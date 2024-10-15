:- module(polyhedra_new,_,[assertions, dynamic]).

:- use_module(library(sets)).
:- use_module(library(lists)).
:- use_module(library(write)).
:- use_module(library(sort)).
:- use_module(library(terms_vars),
              [
                  varset/2
              ]).
:- use_module(library(terms_check),
              [
                  variant/2
              ]).
:- use_module(engine(basic_props), [list/1]).
:- use_module(library(streams)).

:- use_module(domain(ppl_interface)).
:- include(ciaopp(plai/plai_domain)).
:- dom_def(polyhedra_new, [default]).

:- doc(title,"Polyhedra with constraints representation").
:- doc(author,"Mario").
:- doc(module, "

This domain implements a version of the polyhedra abstract domain
(which is based in PPL).

In this version we handle cosstraints instead of PPL addreses to
represent the abstract substitution. This leads to a cleaner code
easier to maintain (and debug). 
").


:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
:- use_module(engine(runtime_control), [gc/0]). % TODO: why?

:- data ppl_is_init/0.

:- export(polyhedra_initialize/0).
polyhedra_initialize :-
    ( ppl_is_init -> true
    ; gc,ppl_initialize,
      assertz_fact(ppl_is_init)
    ).

:- export(polyhedra_finalize/0).
polyhedra_finalize :- true. % TODO: do nothing (debug)

:- dom_impl(_, init_abstract_domain/1, [noq]).
init_abstract_domain([widen]) :- 
    push_pp_flag(widen,on).

:- dynamic number_polys/1.
number_polys(0).

polyhedron2asub(Poly,(Cons,Vars)):-
    var(Poly),!,
    length(Vars,Dims),
    ppl_new_NNC_Polyhedron_from_space_dimension(Dims,universe,Poly),
    number_polys(N),
    N1 is N+1,
    retract(number_polys(_)),
    assert(number_polys(N1)),
    ppl_Polyhedron_add_constraints(Poly,Cons).

%% polyhedron2asub(Poly,Cons):-
%%     %% ppl_new_Polyhedron_from_constraints(nnc,Cons,Poly), [DJ] change
%%     ppl_new_NNC_Polyhedron_from_constraints(Cons,Poly),
%%     % ERASE ME
%%     number_polys(N),
%%     N1 is N+1,
%%     %nl,display('ALERT Number of polyhedra in memory > 2 !!!!!!'),nl,
%%     retract(number_polys(_)),
%%     assert(number_polys(N1)).	
%%     %%% END ERASE ME

polyhedra_delete_Polyhedron(Poly):-
    ppl_delete_Polyhedron(Poly),
    number_polys(N),
    N1 is N-1,
    retract(number_polys(_)),
    assert(number_polys(N1)).

ppl_Constraint_is_empty(ASub1):-
    polyhedra_initialize,
    polyhedron2asub(Poly1,ASub1),
    (ppl_Polyhedron_is_empty(Poly1)->
        polyhedra_delete_Polyhedron(Poly1),
        polyhedra_finalize;
            
            polyhedra_delete_Polyhedron(Poly1),
            polyhedra_finalize,!,
            fail
	).

ppl_Constraint_equals_Constraint(ASub1,ASub2):-
    polyhedra_initialize,
    polyhedron2asub(Poly1,ASub1),
    polyhedron2asub(Poly2,ASub2),	
    (ppl_Polyhedron_equals_Polyhedron(Poly1,Poly2) ->
        polyhedra_delete_Polyhedron(Poly1),
        polyhedra_delete_Polyhedron(Poly2),
        polyhedra_finalize;
            
            polyhedra_delete_Polyhedron(Poly1),
	 polyhedra_delete_Polyhedron(Poly2),
	 polyhedra_finalize,!,
	 fail
        ).

% preserve PPL 0,7 semantics: contains(A.B) <=> A contains B
ppl_Constraint_contains_Constraint(ASub1,ASub2):-
    polyhedra_initialize,
    polyhedron2asub(Poly1,ASub1),
    polyhedron2asub(Poly2,ASub2),	
    (ppl_Polyhedron_contains_Polyhedron(Poly1,Poly2) ->
	polyhedra_delete_Polyhedron(Poly1),
	polyhedra_delete_Polyhedron(Poly2),
        polyhedra_finalize;
            
            polyhedra_delete_Polyhedron(Poly1),
            polyhedra_delete_Polyhedron(Poly2),
            polyhedra_finalize,!,	
            fail
        ).
	
ppl_Constraint_poly_hull_assign_and_minimize(ASub1,ASub2,Result):-
    polyhedra_initialize,
    polyhedron2asub(Poly1,ASub1),
    polyhedron2asub(Poly2,ASub2),
    ppl_Polyhedron_poly_hull_assign(Poly1, Poly2),
    %ppl_Polyhedron_poly_hull_assign_and_minimize(Poly1,Poly2),
    ASub1 = (_,Vars),
    ppl_Polyhedron_get_minimized_constraints(Poly1,Const),
    Result = (Const,Vars),
    polyhedra_delete_Polyhedron(Poly1),
    polyhedra_delete_Polyhedron(Poly2),
    polyhedra_finalize.	

ppl_Constraint_intersection_assign_and_minimize(ASub1,ASub2,Result):-
    polyhedra_initialize,
    polyhedron2asub(Poly1,ASub1),
    polyhedron2asub(Poly2,ASub2),
    ppl_Polyhedron_poly_hull_assign(Poly1, Poly2),
    % ppl_Polyhedron_intersection_assign_and_minimize(Poly1,Poly2),
    ASub1 = (_,Vars),
    ppl_Polyhedron_get_minimized_constraints(Poly1,Const),
    Result = (Const,Vars),
    polyhedra_delete_Polyhedron(Poly1),
    polyhedra_delete_Polyhedron(Poly2),
    polyhedra_finalize.	

% Same assumption as PPL again: ASub1 is bigger than ASub2 
ppl_Constraint_BHRZ03_widening_assign(ASub1,ASub2,Result):-	
    polyhedra_initialize,
    polyhedron2asub(Poly1,ASub1),
    polyhedron2asub(Poly2,ASub2),	
    ppl_Polyhedron_BHRZ03_widening_assign(Poly1,Poly2),	
    ASub1 = (_,Vars),
    ppl_Polyhedron_get_minimized_constraints(Poly1,Const),
    Result = (Const,Vars),
    polyhedra_delete_Polyhedron(Poly1),
    polyhedra_delete_Polyhedron(Poly2),
    polyhedra_finalize.	

ppl_Constraint_remove_space_dimensions(ASub,Black_ListN,Result):-
    polyhedra_initialize,
    polyhedron2asub(Poly,ASub),
    ASub = (_Const,Vars),
    ppl_Polyhedron_remove_space_dimensions(Poly,Black_ListN),	
    ppl_Polyhedron_get_minimized_constraints(Poly,New_Const),
    dim2var_varlist(Black_ListN,Vars,Black_List),
    ord_subtract(Vars,Black_List,New_Vars),
    Result = (New_Const,New_Vars),
    polyhedra_delete_Polyhedron(Poly),
    polyhedra_finalize.	

ppl_Constraint_add_constraint(ASub,Constraint,Result):-
    polyhedra_initialize,
    polyhedron2asub(Poly,ASub),
    ppl_Polyhedron_add_constraint(Poly,Constraint),
    ASub = (_,Vars),
    ppl_Polyhedron_get_minimized_constraints(Poly,Const),
    Result = (Const,Vars),
    polyhedra_delete_Polyhedron(Poly),
    polyhedra_finalize.	

ppl_Constraint_add_constraints(ASub,Constraint,Result):-
    polyhedra_initialize,
    polyhedron2asub(Poly,ASub),
    ppl_Polyhedron_add_constraints(Poly,Constraint),
    ASub = (_,Vars),
    ppl_Polyhedron_get_minimized_constraints(Poly,Const),
    Result = (Const,Vars),
    polyhedra_delete_Polyhedron(Poly),
    polyhedra_finalize.	

ppl_Constraint_relation_with_constraint((Cons, Vars),Constraint,Relation):- %%% **
    polyhedra_initialize,
    polyhedron2asub(Poly,(Cons, Vars)),
    ppl_Polyhedron_relation_with_constraint(Poly,Constraint,Relation),
    polyhedra_delete_Polyhedron(Poly),
    polyhedra_finalize.	

% add space dimensions does not change at all the abstract constraints,
% just the variables get bigger
ppl_Constraint_add_space_dimensions_and_embed(ASub,New_Dims,ASub1):-
    ASub = (Cons,Vars),
    append(Vars,New_Dims,New_Vars),
    ASub1 = (Cons,New_Vars).


%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT SORT
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom'):-!.
abs_sort(ASub,ASub_Sorted):-
    ASub = (Const,Vars),!,
    sort(Vars,Sorted_Vars),
    (Sorted_Vars==Vars ->
        ASub_Sorted = ASub;	    
            dim2var(Const,Vars,Renum_Cons_Sys),
            dim2var(Renum_Cons_Sys,Sorted_Vars,Cons_Sys2),
            ASub_Sorted = (Cons_Sys2,Sorted_Vars)
	).
abs_sort(X,X).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT IDENTICAL
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
:- dom_impl(_, identical_abstract/2, [noq]).
identical_abstract('$bottom','$bottom'):-!.
identical_abstract(ASub1,_ASub2):-
    ppl_Constraint_is_empty(ASub1),!.
identical_abstract(ASub1,ASub2):-
    ASub1 = (_Const1,Vars1),
    ASub2 = (_Const2,Vars2),
    Vars1 == Vars2,
    ppl_Constraint_equals_Constraint(ASub1,ASub2).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                            WIDENINGs
%   Disabling of widening cannot be done here but in domains.pl
%
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
:- dom_impl(_, widencall/3, [noq]).
% widening requires Dim0 = Dim1
widencall('$bottom',ASub2,ASub2):-!.
widencall(ASub1,'$bottom',ASub1):-!.
widencall(ASub1,ASub2,New_ASub):- 
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2),
    widencall_(New_ASub1,New_ASub2,New_ASub).

	
% ASub1 is more recent than ASub0, thus matching the usual order
% for widenings
widencall_(ASub0,ASub1,ASub0):- 
    ppl_Constraint_contains_Constraint(ASub0,ASub1),!.

widencall_(ASub0,ASub1,ASub_Widen):- 
    ppl_Constraint_poly_hull_assign_and_minimize(ASub0,ASub1,ASub_Hull),
    ppl_Constraint_BHRZ03_widening_assign(ASub_Hull,ASub0,ASub_Widen).

:- dom_impl(_, needs/1, [noq]).
needs(widen).

:- dom_impl(_, widen/3, [noq]).
widen(Prime0,Prime1,New_Prime):- 
    widencall(Prime0,Prime1,New_Prime).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT LESS OR EQUAL
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal(ASub1,ASub2):-
    ppl_Constraint_contains_Constraint(ASub1,ASub2).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT LUB
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
:- dom_impl(_, compute_lub/2, [noq]).
compute_lub('$bottom','$bottom').
compute_lub([ASub1],ASub1).
compute_lub([E1,E2|Rest],Lub):-
    compute_lub_el(E1,E2,PartialLub),
    compute_lub([PartialLub|Rest],Lub).

compute_lub_el(ASub1,'$bottom',ASub1):- !.
compute_lub_el('$bottom',ASub2,ASub2):- !.
compute_lub_el(ASub1,ASub2,Lub):-
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2),
    ppl_Constraint_poly_hull_assign_and_minimize(New_ASub1,New_ASub2,Lub),
    !.
compute_lub_el(_ASub1,_ASub2,'$bottom').


%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT GLB
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
:- dom_impl(_, glb/3, [noq]).

glb(('$bottom',_),_ASub2,'$bottom'):- !.	
glb(_ASub1,('$bottom',_),'$bottom'):- !.	
glb(ASub1,ASub2,Glb):-
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2),
    ppl_Constraint_intersection_assign_and_minimize(New_ASub1,New_ASub2,Glb),
    !.
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(_, project/5, [noq]).
:- export(project_/3).
project(_Sg,Vars,_HvFv_u,ASub,Proj) :-
    project_(ASub, Vars, Proj).
    
project_('$bottom',_,'$bottom'):- !.
project_(ASub,Vars_Proj,Proj):-
    ASub = (_Const,Vars),
    ord_subtract(Vars,Vars_Proj,Black_List),
    dim2var_varlist(Black_List,Vars,Black_ListN),
    ppl_Constraint_remove_space_dimensions(ASub,Black_ListN,Proj).



%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %REMOVE ME
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% get_invalid_dimensions([],_Dim,_Vars,Black_List,Black_List):-!.
%% get_invalid_dimensions([Var|Rest_Var],Dim,Vars,Black_List,Black_ListF):-
%%     ord_member(Var,Vars),!,
%%     Dim1 is Dim + 1,
%%     get_invalid_dimensions(Rest_Var,Dim1,Vars,Black_List,Black_ListF).
%% get_invalid_dimensions([_Var|Rest_Var],Dim,Vars,Black_List,Black_ListF):-
%%     Black_List1 = ['$VAR'(Dim)|Black_List],
%%     Dim1 is Dim + 1,
%%     get_invalid_dimensions(Rest_Var,Dim1,Vars,Black_List1,Black_ListF).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Extend
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
:- dom_impl(_, extend/5, [noq]).
extend(_Sg,Prime,Sv,Call,Success):-
    extend_(Prime, Sv, Call, Success).

extend_('$bottom',_Sv,_Call,'$bottom').
extend_(Prime,Sv,Call,Success):- 
    polyhedra_merge(Call,Prime,Sv,Success).


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                    ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
    call_to_entry_(Sv,Sg,Hv,Head,Fv,Proj,Entry,ExtraInfo).

call_to_entry_(_Sv,Sg,Hv,Head,Fv,Proj,Entry,ExtraInfo):-
    ord_union(Hv,Fv,HvFv),
    polyhedra_add_dimensions(Proj,HvFv,Temp1),
    polyhedra_simplify_equations(Sg,Head,Binds),
    abs_gunify(Temp1,Binds,Upd_Proj,_NewBinds),
    project_(Upd_Proj,HvFv,Entry),
    ExtraInfo = (Upd_Proj,HvFv).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom'):-
    !.
exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo = (Upd_Proj,HvFv),
    polyhedra_merge(Upd_Proj,Exit,HvFv,Tmp),
    project_(Tmp,Sv,Prime).


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------
:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    call_to_success_fact_(Sg,Hv,Head,Sv,Call,Proj,Prime,Succ).

call_to_success_fact_(Sg,Hv,Head,Sv,Call,Proj,Prime,Succ):-
    polyhedra_add_dimensions(Proj,Hv,Temp1),
    polyhedra_simplify_equations(Sg,Head,Binds),
    abs_gunify(Temp1,Binds,Entry,_NewBinds),
    project_(Entry,Sv,Prime),
    extend_(Prime,Sv,Call,Succ).


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                Unknow & Empty Entry,Unknow Call                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Vars,Entry):- 
    polyhedra_get_empty_Asub(Empty),
    polyhedra_add_dimensions(Empty,Vars,Entry).

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(_Sg, Vars,Entry):- 
    unknown_entry(_Sg, Vars,Entry).


% The unknown call might only impose more constraints on Vars, so Call is
% a valid approximation for Succ, even for those dimensions that could be
% instantiated as non-numeric values in the unknown call
:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg, Call,_Vars,Succ):-
    Succ = Call.



%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                          Special Builtin
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(_, special_builtin/5, [noq]). 
special_builtin(SgKey,Sg,_,Type,Condvars):- 
    special_builtin_(SgKey,Sg,Type,Condvars).

special_builtin_('=/2',=(X,Y),unification,Condvars):-
    Condvars = (X,Y).	
special_builtin_('is/2',is(X,Y),constraint,Condvars):-
    Condvars = '='(X,Y).	
special_builtin_('=</2',Sg,constraint,Condvars):-
    Condvars = Sg.	
special_builtin_('>=/2',Sg,constraint,Condvars):-
    Condvars = Sg.	
special_builtin_('</2',Sg,constraint,Condvars):-
    Condvars = Sg.	
special_builtin_('>/2',Sg,constraint,Condvars):-
    Condvars = Sg.	
special_builtin_('true/0',_,unchanged,_).
special_builtin_('read:read/1',_,unchanged,_).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                          Success Builtin
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
	
% We only pay attention to the subset [=,<,>,>=,=<] if they relate linear
% equations.
:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(Type,Sv,Condv, _HvFv_u, Call,New_Succ):-
    success_builtin_(Type,Sv,Condv,Call,Succ),
    (ppl_Constraint_is_empty(Succ) ->
        New_Succ = '$bottom';
            New_Succ = Succ
	).

success_builtin_(unchanged,_,_,Call,Succ):-
    Call = Succ.
success_builtin_(unification,_Sv,Condv,Call,Succ):-
    Condv = (Term1,Term2),
    polyhedra_simplify_equations(Term1,Term2,Binds),
    abs_gunify(Call,Binds,Succ,_NewBinds).
success_builtin_(constraint,_Sv,Condv,Call,Succ):-
    Call = (_Const,Vars),
    dim2var_constraint(Condv,Vars,Condv_As_PPL_Cons),!,
    ppl_Constraint_add_constraint(Call,Condv_As_PPL_Cons,Succ).
success_builtin_(constraint,_Sv,_Condv,Call,Succ):-
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%
    %%%%%%%%% Remove all variables implied
    Call = Succ.

%------------------------------------------------------------------------%
%                       Call to Success Builtin
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin(_SgKey,_Sh,_Sv,Call,_Proj,Succ):-
    Call = Succ.

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%            Assertion(I/O) related Functions                            %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface(Cons_Sys,Qv,New_ASub,_Sg,_MaybeCallASub):-
    input_user_interface_(Cons_Sys,Qv,New_ASub).

input_user_interface_(Cons_Sys,Qv,New_ASub):-
    ASub = ([],Qv),
    input2builtin(Cons_Sys,ASub,New_ASub).

input2builtin([],ASub,ASub).
input2builtin([=(A,B)|Rest_Cons],ASub,New_ASub):- !,
    success_builtin_(unification,_,(A,B),ASub,ASub1),
    input2builtin(Rest_Cons,ASub1,New_ASub).
% it can only be < ,>, >=, =< as filtered by constraint/1
input2builtin([In_Equality|Rest_Cons],ASub,New_ASub):-
    success_builtin_(constraint,_,In_Equality,ASub,ASub1),
    input2builtin(Rest_Cons,ASub1,New_ASub).

polyhedra_input_interface(constraint(Cons_Sys),perfect,Old_Cons_Sys,New_Cons_Sys):-
    append(Old_Cons_Sys,Cons_Sys,New_Cons_Sys). 

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native(ASub,_Qv,_OutFlag,Output,[]):-
    asub_to_native_(ASub,_Qv,Output).


asub_to_native_('$bottom',_Qv,'$bottom').
asub_to_native_(ASub,_Qv,[Output]):-
    ASub = (Const,Vars),
    dim2var(Const,Vars,Named_Cons_Sys),
    Output = constraint(Named_Cons_Sys).


%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%            Intermediate Functions                                      %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

print_absu('$bottom') :- 
    display('No solution'),!.
print_absu(Const,Vars) :-
    length(Vars,Dims),
    display('Dims: '),write(Dims),nl,
    display('Cons: '),write(Const),nl,
    display('Vars: '),display(Vars),nl.

print_poly(Address):-
    polyhedra_initialize,
    %ppl_Polyhedron_get_minimized_constraints('$address'(Address),Const),
    ppl_Polyhedron_get_minimized_constraints(Address,Const),
    polyhedra_finalize,
    print_absu(Const,[whatever_vars]).

:- pop_prolog_flag(multi_arity_warnings).


% Dimension Dim  associated with Var
get_dimension(ASub,Var,Dim):-
    ASub = (_Poly,Vars),!,
    my_nth(Vars,Var,Dim,not_instantiate).
get_dimension(Vars,Var,Dim):-
    list(Vars),
    var(Dim),!,
    my_nth(Vars,Var,Dim,not_instantiate).
get_dimension(Vars,Var,Dim):-
    ground(Dim),
    my_nth(Vars,Var,Dim,instantiate).


my_nth(Vars,Var,Dim,Flag):-
    my_nth_(0,Vars,Var,Dim,Flag).
my_nth_(N,[Var|_Rest],Pattern,N,not_instantiate):-
    Var==Pattern,!.
my_nth_(N,[Pattern|_Rest],Pattern,N,instantiate):-!.
my_nth_(N,[_Var|Rest],Pattern,Dim,Flag):-
    N1 is N+1,
    my_nth_(N1,Rest,Pattern,Dim,Flag).

polyhedra_get_empty_Asub(ASub_Empty):-
    ASub_Empty = ([],[]). 

polyhedra_add_dimensions(ASub,New_Dims,New_ASub):-
    ppl_Constraint_add_space_dimensions_and_embed(ASub,New_Dims,New_ASub).


match_dimensions(ASub1,ASub2,ASub1,ASub2):-
    ASub1 = (_Const1,Vars1),
    ASub2 = (_Const2,Vars2),
    Vars1 == Vars2,!.
match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2):-
    ASub1 = (_Const1,Vars1),
    ASub2 = (_Const2,Vars2),
    ord_intersection(Vars1,Vars2,Vars),
    project_(ASub1,Vars,New_ASub1),
    project_(ASub2,Vars,New_ASub2).


% ASub2 contains more recent information about the variables so its used
% as reference
polyhedra_merge(Old_ASub,New_ASub,Init_Vars_New,Merge):-
    Old_ASub=(_,Vars_Old),
    polyhedra_merge_vars(Vars_Old,Init_Vars_New,New_ASub,Tmp1),
	polyhedra_merge_poly(Old_ASub,Tmp1,Merge).

% mix the set of variables of both substitutions	
polyhedra_merge_vars([],_HvFv,Exit,Sorted_Exit):-
    abs_sort(Exit,Sorted_Exit).
polyhedra_merge_vars([Var|Rest_Vars],HvFv,Exit,Sorted_Exit):-
    ord_member(Var,HvFv),!,
    Exit=(Const_Exit,Vars_Exit),
    match_vars(Var,Vars_Exit,New_Vars_Exit),
    New_Exit=(Const_Exit,New_Vars_Exit),
    polyhedra_merge_vars(Rest_Vars,HvFv,New_Exit,Sorted_Exit).
polyhedra_merge_vars([Var|Rest_Vars],HvFv,Exit,Sorted_Exit):-
    polyhedra_add_dimensions(Exit,[Var],New_Exit),
    polyhedra_merge_vars(Rest_Vars,HvFv,New_Exit,Sorted_Exit).

match_vars(_Synonym,[],[]).
match_vars(Synonym,[Var|Rest_Vars],New_Varset):-
    Synonym == Var,!,
    New_Varset = [Var|Rest_Vars].
match_vars(Sinonym,[Var|Rest_Vars],New_Varset):-
    New_Varset = [Var|Rest_New_Varset],
    match_vars(Sinonym,Rest_Vars,Rest_New_Varset).


polyhedra_merge_poly(ASub1,ASub2,ASub_Merge):-
    ASub2=(_Const2,Vars2),
    project_(ASub1,Vars2,New_ASub1),
    New_ASub1=(Const1,Vars2),
    ppl_Constraint_add_constraints(ASub2,Const1,ASub_Merge).	

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                     Standard Peel Equations
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
polyhedra_simplify_equations(Term1,Term2,Binds):-
    polyhedra_free_peel(Term1,Term2,Binds,[]).

polyhedra_free_peel(Term1,Term2,Binds,Rest) :-
    var(Term1), !,
    varset(Term2,List),
    Binds = [(Term1,Term2,List)|Rest].
polyhedra_free_peel(Term1,Term2,Binds,Rest) :-
    var(Term2), !,
    varset(Term1,List),
    Binds = [(Term2,Term1,List)|Rest].
polyhedra_free_peel(Term1,Term2,Binds,Rest) :-
    Term1 == Term2, !,
    Binds = Rest.
polyhedra_free_peel(Term1,Term2,Binds,Rest) :- 
    functor(Term1,F,N),
    functor(Term2,F,N),
    polyhedra_free_peel_args(0,N,Term1,Term2,Binds,Rest).

polyhedra_free_peel_args(N,N,_,_,Binds,Rest) :- !,
    Binds = Rest.
polyhedra_free_peel_args(N1,N,Term1,Term2,Binds,Rest) :-
    N2 is N1 + 1,
    arg(N2,Term1,A1),
    arg(N2,Term2,A2),
    polyhedra_free_peel(A1,A2,Binds,Rest1),
    polyhedra_free_peel_args(N2,N,Term1,Term2,Rest1,Rest).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                     ABSTRACT UNIFICATION
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

abs_gunify(Proj,Binds,NewProj,NewBinds):-
    ab_unify(Binds,Proj,Proj1,Binds1),
    fixpoint_gunify(Proj,Binds,Proj1,Binds1,NewProj,NewBinds).

fixpoint_gunify(Proj,Binds,Proj1,Binds1,NewProj,NewBinds):-
    Proj == Proj1,
    Binds == Binds1,!,
    NewProj = Proj1,
    NewBinds = Binds1.
fixpoint_gunify(_,_,Proj1,Binds1,NewProj,NewBinds):-
    abs_gunify(Proj1,Binds1,NewProj,NewBinds).

ab_unify([],Proj,Proj,[]).
ab_unify([(X,Y,_Tv)|Binds],Proj,New_Proj,NewBinds):-
    var(X),
    var(Y),!,
    ab_unify_variables(X,Y,Proj,Proj1),
    ab_unify(Binds,Proj1,New_Proj,NewBinds).
ab_unify([(X,Term,[])|Binds],Proj,New_Proj,NewBinds):-
    var(X),
    ground(Term),
    number(Term),!,
    dim2var_var(X,Proj,Named_X),
    ppl_Constraint_add_constraint(Proj,Named_X = Term,Proj1),
    ab_unify(Binds,Proj1,New_Proj,NewBinds).
ab_unify([(X,Term,[])|Binds],Proj,New_Proj,NewBinds):-
    var(X),
    ground(Term),
    polyhedra_remove_nonint_dims(Proj,X,Proj1),!,
    ab_unify(Binds,Proj1,New_Proj,NewBinds).
ab_unify([(X,Term,[])|Binds],Proj,New_Proj,NewBinds):-
    var(X),
    ground(Term),!,
    ab_unify(Binds,Proj,New_Proj,NewBinds).
ab_unify([_Bind|Binds],Proj,NewProj,NewBinds):-
    ab_unify(Binds,Proj,NewProj,NewBinds).

ab_unify_variables(X,Y,Proj,Folded_Proj):-
    dim2var_var(Y,Proj,Named_Y),
    dim2var_var(X,Proj,Named_X),!, 
    ppl_Constraint_add_constraint(Proj,Named_X = Named_Y,Folded_Proj).
ab_unify_variables(X,_Y,Proj,New_Proj):-
    polyhedra_remove_nonint_dims(Proj,X,New_Proj),!.
ab_unify_variables(_X,Y,Proj,New_Proj):-
    polyhedra_remove_nonint_dims(Proj,Y,New_Proj).


polyhedra_remove_nonint_dims(ASub,Invalid_Dim,New_ASub):-
    ASub = (_Const,Vars),
    polyhedra_find_nonint_dims(ASub,Invalid_Dim,Invalid_Dims),
    dim2var_varlist(Invalid_Dims,Vars,Named_Invalid_Dims),
    sort(Named_Invalid_Dims,Sorted_Invalid_Dims),
    ord_subtract(Vars,Sorted_Invalid_Dims,Valid_Dims),
    project_(ASub,Valid_Dims,New_ASub).

polyhedra_find_nonint_dims(ASub,Start,Invalid_Dims):-
    ASub = (Const,Vars),
    dim2var_var(Start,Vars,Num_Start),
    dim2var_varlist(Vars,Vars,Num_Vars),
    dim2var_varlist([Start|Vars],[Start|Vars], AllVars),
    find_nonint_dims([Num_Start],Const,AllVars,Num_Vars,Num_Vars,Invalid_Dims).

find_nonint_dims([],_Const,_AllVars,_Vars,_Vars,[]).
find_nonint_dims([Dim|Rest_Dim],Const,AllVars,[],Vars,[Dim|Rest_Result]):-
    find_nonint_dims(Rest_Dim,Const,AllVars,Vars,Vars,Rest_Result).
find_nonint_dims([Dim|Rest_Dim],Const,AllVars,[Var|Rest_Vars],Vars,Result):-
    Dim \== Var,
    ppl_Constraint_relation_with_constraint((Const, AllVars),=(Dim,Var),Relation),
    member(is_included,Relation),
    append([Dim|Rest_Dim],[Var],Dims_Not_Int),
    ord_subtract(Vars,[Var],New_Vars),
    find_nonint_dims(Dims_Not_Int,Const,AllVars,Rest_Vars,New_Vars,Result).
find_nonint_dims([Dim|Rest_Dim],Const,AllVars,[_|Rest_Vars],Vars,Result):-
    find_nonint_dims([Dim|Rest_Dim],Const,AllVars,Rest_Vars,Vars,Result).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                     CONSTRAINT MANIPULATION/ TYPE CHECKER
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

dim2var_var(Var,Vars_Or_ASub,Renamed_Var):-
    var(Var),!,
    get_dimension(Vars_Or_ASub,Var,Dim_Var),
    Renamed_Var = '$VAR'(Dim_Var).
dim2var_var(Var,Vars,Name_Var):-
    ground(Var),
    Var='$VAR'(Dim),!,
    get_dimension(Vars,Name_Var,Dim).

dim2var_varlist([],_Vars,[]).
dim2var_varlist([Var|Rest_Var],Vars,[Ren_Var|Rest_Ren_Var]):-
    dim2var_var(Var,Vars,Ren_Var),
    dim2var_varlist(Rest_Var,Vars,Rest_Ren_Var).

dim2var_coefficient(Coeff):-
    ground(Coeff),
    int(Coeff).

:- push_prolog_flag(multi_arity_warnings,off).
:- push_prolog_flag(discontiguous_warnings,off).

dim2var_lin_expr(PPL_Var,Vars,PPL_Dim):-dim2var_var(PPL_Var,Vars,PPL_Dim),!.
dim2var_lin_expr(Coeff,_Vars,Coeff):-dim2var_coefficient(Coeff).
dim2var_lin_expr(+(Lin_Expr),Vars,+(New_Lin_Expr)):-
    dim2var_lin_expr(Lin_Expr,Vars,New_Lin_Expr).
dim2var_lin_expr(-(Lin_Expr),Vars,-(New_Lin_Expr)):-
    dim2var_lin_expr(Lin_Expr,Vars,New_Lin_Expr).
dim2var_lin_expr(+(Lin_Expr1,Lin_Expr2),Vars,+(New_Lin_Expr1,New_Lin_Expr2)):-
    dim2var_lin_expr(Lin_Expr1,Vars,New_Lin_Expr1),
    dim2var_lin_expr(Lin_Expr2,Vars,New_Lin_Expr2).
dim2var_lin_expr(-(Lin_Expr1,Lin_Expr2),Vars,-(New_Lin_Expr1,New_Lin_Expr2)):-
    dim2var_lin_expr(Lin_Expr1,Vars,New_Lin_Expr1),
    dim2var_lin_expr(Lin_Expr2,Vars,New_Lin_Expr2).
dim2var_lin_expr(*(Coeff,Lin_Expr),Vars,*(Coeff,New_Lin_Expr)):-
    dim2var_coefficient(Coeff),
    dim2var_lin_expr(Lin_Expr,Vars,New_Lin_Expr).
dim2var_lin_expr(*(Lin_Expr,Coeff),Vars,*(Coeff,New_Lin_Expr)):-
    dim2var_coefficient(Coeff),
    dim2var_lin_expr(Lin_Expr,Vars,New_Lin_Expr).

:- pop_prolog_flag(discontiguous_warnings).
:- pop_prolog_flag(multi_arity_warnings).

dim2var_constraint(=(Lin_Expr1,Lin_Expr2),Vars,=(Lin_Expr21,Lin_Expr22)):-
    dim2var_lin_expr(Lin_Expr1,Vars,Lin_Expr21),
    dim2var_lin_expr(Lin_Expr2,Vars,Lin_Expr22).
dim2var_constraint(=<(Lin_Expr1,Lin_Expr2),Vars,=<(Lin_Expr21,Lin_Expr22)):-
    dim2var_lin_expr(Lin_Expr1,Vars,Lin_Expr21),
    dim2var_lin_expr(Lin_Expr2,Vars,Lin_Expr22).
dim2var_constraint(>=(Lin_Expr1,Lin_Expr2),Vars,>=(Lin_Expr21,Lin_Expr22)):-
    dim2var_lin_expr(Lin_Expr1,Vars,Lin_Expr21),
    dim2var_lin_expr(Lin_Expr2,Vars,Lin_Expr22).
dim2var_constraint(<(Lin_Expr1,Lin_Expr2),Vars,<(Lin_Expr21,Lin_Expr22)):-
    dim2var_lin_expr(Lin_Expr1,Vars,Lin_Expr21),
    dim2var_lin_expr(Lin_Expr2,Vars,Lin_Expr22).
dim2var_constraint(>(Lin_Expr1,Lin_Expr2),Vars,>(Lin_Expr21,Lin_Expr22)):-
    dim2var_lin_expr(Lin_Expr1,Vars,Lin_Expr21),
    dim2var_lin_expr(Lin_Expr2,Vars,Lin_Expr22).

dim2var_constraint_system([],_Vars,[]).
dim2var_constraint_system([Cons|Rest],Vars,[New_Cons|Rest_New_Cons]):-
    dim2var_constraint(Cons,Vars,New_Cons),!,
    dim2var_constraint_system(Rest,Vars,Rest_New_Cons ).
dim2var_constraint_system([_Cons|Rest],Vars,Rest_New_Cons):-
    dim2var_constraint_system(Rest,Vars,Rest_New_Cons ).

dim2var(Cons_Sys,Vars,Renamed_Cons_Sys):-
    dim2var_constraint_system(Cons_Sys,Vars,Renamed_Cons_Sys).

