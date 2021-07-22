:- module(polyhedra,[],[datafacts]).

:- use_module(library(sets)).
:- use_module(library(lists)).
:- use_module(library(streams)).
:- use_module(library(write)).
:- use_module(library(sort)).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(basic_props), [list/1]). % TODO: review this use

:- use_module(domain(ppl_interface)).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(polyhedra, [default]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: WARNING
% This domain causes severe memory leaks because of the use of pointers
% (PPL_Polyhedra) to objects not cleaned during garbage collection BUT
% is not restricted to the 100Megs limit so it works for more cases than  
% a version using prolog terms. 
% Check /home/mario/research/PPL/polyhedra_new.pl for that alternative
% version
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: move dim2var to a API-friendly version
% TODO: Process ALL builtins
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% TODO: names 'initialize'/'finalize' may be misleading
%% OLD
%% polyhedra_initialize:-
%       gc,ppl_initialize.
% polyhedra_finalize:-
%       ppl_finalize,gc.

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

%-------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(polyhedra, init_abstract_domain/1, [noq]).
init_abstract_domain([widen]) :- 
    push_pp_flag(widen,on).

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom'):-!.
abs_sort(ASub1,ASub2):-
    polyhedra_initialize,
    polyhedra_sort_(ASub1,ASub2),
    polyhedra_finalize.

polyhedra_sort_(ASub,ASub_Sorted):-
    ASub = (Poly,Vars),!,
    sort(Vars,Sorted_Vars),
    ( Sorted_Vars==Vars ->
        ASub_Sorted = ASub
    ; ppl_Polyhedron_get_minimized_constraints(Poly,Cons_Sys),
      dim2var(Cons_Sys,Vars,Renum_Cons_Sys),
      dim2var(Renum_Cons_Sys,Sorted_Vars,Cons_Sys2),
      ppl_Polyhedron_space_dimension(Poly,Dims),
      ppl_new_NNC_Polyhedron_from_space_dimension(Dims,universe,New_Poly),
      ppl_Polyhedron_add_constraints(New_Poly,Cons_Sys2),
      ASub_Sorted = (New_Poly,Sorted_Vars)
    ).
polyhedra_sort_(X,X).

:- dom_impl(polyhedra, eliminate_equivalent/2, [noq]).
eliminate_equivalent(ASub1,ASub2):-
    abs_sort(ASub1,ASub2).

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, identical_abstract/2, [noq]).
identical_abstract('$bottom','$bottom'):-!.
identical_abstract(ASub1,ASub2):-
    polyhedra_initialize,
    identical_abstract_(ASub1,ASub2),     
    polyhedra_finalize.

identical_abstract_(ASub1,_ASub2):-
    ASub1 = (Poly1,_Vars1),
    ppl_Polyhedron_is_empty(Poly1),!.
identical_abstract_(ASub1,ASub2):-
    ASub1 = (Poly1,Vars1),
    ASub2 = (Poly2,Vars2),
    Vars1 == Vars2,
    ppl_Polyhedron_equals_Polyhedron(Poly1,Poly2).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                            WIDENINGs
%   Disabling of widening cannot be done here but in domains.pl
%
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%

% widening requires Dim0 = Dim1
:- dom_impl(polyhedra, widencall/3, [noq]).
widencall('$bottom',ASub2,ASub2):-!.
widencall(ASub1,'$bottom',ASub1):-!.
widencall(ASub1,ASub2,New_ASub):- 
    polyhedra_initialize,
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2),
    New_ASub1 = (Poly1,Vars),
    New_ASub2 = (Poly2,Vars),
    widencall_(Poly1,Poly2,Poly_Widen),           
    New_ASub = (Poly_Widen,Vars),
    polyhedra_finalize.
    
% Poly1 is more recent than Poly0, thus matching the usual order
% for widenings
% Remember (PPL 0.7 bug) that contains(A,B)=true if B<=A -> A contains B
widencall_(Poly0,Poly1,Poly_Widen):- 
    ppl_Polyhedron_contains_Polyhedron(Poly0,Poly1),!,
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly0,New_Poly),
    Poly_Widen = New_Poly.
widencall_(Poly0,Poly1,Poly_Widen):- 
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly0,New_Poly),
    % TODO: call minimize after assign
    ppl_Polyhedron_poly_hull_assign(New_Poly,Poly1),
    %ppl_Polyhedron_poly_hull_assign_and_minimize(New_Poly,Poly1),
    ppl_Polyhedron_BHRZ03_widening_assign(New_Poly,Poly0),  
    Poly_Widen = New_Poly.

:- dom_impl(polyhedra, needs/1, [noq]).
needs(widen).

:- dom_impl(polyhedra, widen/3, [noq]).
widen(Prime0,Prime1,New_Prime):- 
    widencall(Prime0,Prime1,New_Prime).

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, less_or_equal/2, [noq]).
less_or_equal(ASub1,ASub2):-
    polyhedra_initialize,
    ASub1 = (Poly1,Vars),
    ASub2 = (Poly2,Vars),
    ppl_Polyhedron_contains_Polyhedron(Poly2,Poly1), % TODO: WAS IT REVERSED?!?!?!?!
    polyhedra_finalize.

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, compute_lub/2, [noq]).
compute_lub(ASubList,Lub):-
    polyhedra_initialize,
    compute_lub_(ASubList,Lub),
    polyhedra_finalize.

compute_lub_('$bottom','$bottom').
compute_lub_([ASub1],ASub1).
compute_lub_([E1,E2|Rest],Lub):-
    compute_lub_el(E1,E2,PartialLub),
    compute_lub_([PartialLub|Rest],Lub).

compute_lub_el(ASub1,'$bottom',ASub1):- !.
compute_lub_el('$bottom',ASub2,ASub2):- !.
compute_lub_el(ASub1,ASub2,Lub):-
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2),
    New_ASub1 = (Poly1,Vars),
    New_ASub2 = (Poly2,Vars),
    % TODO: call minimize after assign
    ppl_Polyhedron_poly_hull_assign(Poly1,Poly2),!,
    Lub = (Poly1,Vars).
compute_lub_el(_ASub1,_ASub2,'$bottom').

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, glb/3, [noq]).
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb(ASub1,ASub2,Glb):-
    polyhedra_initialize,
    glb_(ASub1,ASub2,Glb),
    polyhedra_finalize.

glb_(('$bottom',_),_ASub2,'$bottom'):- !.     
glb_(_ASub1,('$bottom',_),'$bottom'):- !.     
glb_(ASub1,ASub2,Glb):-
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2),
    New_ASub1 = (Poly1,Vars),
    New_ASub2 = (Poly2,Vars),
    % TODO: call minimize after assign
    ppl_Polyhedron_intersection_assign(Poly1,Poly2),!,
    Glb = (Poly1,Vars).

%------------------------------------------------------------------------%
:- dom_impl(polyhedra, project/5, [noq]).
project(_Sg,Vars,_HvFv_u,ASub,Proj):-
    polyhedra_initialize,
    project_(ASub,Vars,Proj),
    polyhedra_finalize.

project_('$bottom',_,'$bottom'):- !.
project_(ASub,Vars,Proj):-
    ASub = (Poly,Poly_Vars),
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly,Poly_Proj),
    project_on_dimensions(Poly_Proj,0,Poly_Vars,Vars),
    Proj = (Poly_Proj,Vars).

project_on_dimensions(_Poly,_Dim,[],_Vars):-!.
project_on_dimensions( Poly,Dim,[Var|Rest_Var],Vars):-
    ord_member(Var,Vars),!,
    Dim1 is Dim + 1,
    project_on_dimensions(Poly,Dim1,Rest_Var,Vars).
project_on_dimensions( Poly,Dim,[_Var|Rest_Var],Vars):-
    ppl_Polyhedron_remove_space_dimensions(Poly,['$VAR'(Dim)]),
    project_on_dimensions(Poly,Dim,Rest_Var,Vars).

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, extend/5, [noq]).
extend(_Sg,Prime,Sv,Call,Success):-
    polyhedra_initialize,
    extend_(Prime,Sv,Call,Success),
    polyhedra_finalize.

extend_('$bottom',_Sv,_Call,'$bottom').
extend_(Prime,Sv,Call,Success):- 
    polyhedra_merge(Call,Prime,Sv,Success).

%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
    polyhedra_initialize,
    call_to_entry_(Sv,Sg,Hv,Head,Fv,Proj,Entry,ExtraInfo),
    polyhedra_finalize.

call_to_entry_(_Sv,Sg,Hv,Head,Fv,Proj,Entry,ExtraInfo):-
    Proj=(Poly1,Vars),
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly1,Poly2),
    Temp1=(Poly2,Vars),
    ord_union(Hv,Fv,HvFv),
    polyhedra_add_dimensions(Temp1,HvFv,Temp2),
    polyhedra_simplify_equations(Sg,Head,Binds),
    abs_gunify(Temp2,Binds,Upd_Proj,_NewBinds),
    project_(Upd_Proj,HvFv,Entry),
    ExtraInfo = (Upd_Proj,HvFv).

%-------------------------------------------------------------------------
:- dom_impl(polyhedra, exit_to_prime/7, [noq]).
exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    polyhedra_initialize,
    exit_to_prime_(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime),
    polyhedra_finalize.

exit_to_prime_(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom'):-
    !.
exit_to_prime_(_Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo = (Upd_Proj,HvFv),
    polyhedra_merge(Upd_Proj,Exit,HvFv,Tmp),
    project_(Tmp,Sv,Prime),
    polyhedra_delete_polyhedron(Tmp).

%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------
:- dom_impl(polyhedra, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    polyhedra_initialize,
    call_to_success_fact_(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ),
    polyhedra_finalize.

call_to_success_fact_(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    Proj = (Poly1,Vars),
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly1,Poly2),
    New_Proj = (Poly2,Vars),
    polyhedra_add_dimensions(New_Proj,Hv,Temp1),
    polyhedra_simplify_equations(Sg,Head,Binds),
    abs_gunify(Temp1,Binds,Entry,_NewBinds),
    project_(Entry,Sv,Prime),
    extend_(Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                Unknow & Empty Entry,Unknow Call                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(polyhedra, unknown_entry/3, [noq]).
unknown_entry(_Sg,Vars,Entry):- 
    polyhedra_initialize,
    polyhedra_get_empty_Asub(Empty),
    polyhedra_add_dimensions(Empty,Vars,Entry),
    polyhedra_finalize.

:- dom_impl(polyhedra, empty_entry/3, [noq]).
empty_entry(Sg,Vars,Entry):- 
    polyhedra_initialize,
    unknown_entry(Sg,Vars,Entry),
    polyhedra_finalize.

% The unknown call might only impose more constraints on Vars, so Call is
% a valid approximation for Succ, even for those dimensions that could be
% instantiated as non-numeric values in the unknown call
:- dom_impl(polyhedra, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,Call,Succ):-
    polyhedra_initialize,
    Succ = Call,
    polyhedra_finalize.

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                          Special Builtin
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(polyhedra, special_builtin/5, [noq]).
special_builtin('=/2',=(X,Y),_,unification,Condvars):-
    Condvars = (X,Y).       
special_builtin('is/2',is(X,Y),_,constraint,Condvars):-
    Condvars = '='(X,Y).    
special_builtin('=</2',Sg,_,constraint,Condvars):-
    Condvars = Sg.  
special_builtin('>=/2',Sg,_,constraint,Condvars):-
    Condvars = Sg.  
special_builtin('</2',Sg,_,constraint,Condvars):-
    Condvars = Sg.  
special_builtin('>/2',Sg,_,constraint,Condvars):-
    Condvars = Sg.  
special_builtin('true/0',_,_,unchanged,_).
special_builtin('read:read/1',_,_,unchanged,_).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                          Success Builtin
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
    
% We only pay attention to the subset [=,<,>,>=,=<] if they relate linear
% equations.
:- dom_impl(polyhedra, success_builtin/6, [noq]).
success_builtin(Type,Sv,Condv,_HvFv_u,Call,New_Succ):-
    polyhedra_initialize,
    success_builtin0(Type,Sv,Condv,Call,New_Succ),
    polyhedra_finalize.

success_builtin0(Type,Sv,Condv,Call,New_Succ):-
    success_builtin_(Type,Sv,Condv,Call,Succ),
    Succ = (Poly,_Vars),
    (ppl_Polyhedron_is_empty(Poly) ->
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
    Call = (Poly1,Vars),
    dim2var_constraint(Condv,Vars,Condv_As_PPL_Cons),!,
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly1,Poly2),
    ppl_Polyhedron_add_constraint(Poly2,Condv_As_PPL_Cons),
    Succ = (Poly2,Vars).
success_builtin_(constraint,_Sv,_Condv,Call,Succ):-
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%
    %%%%%%%%% Remove all variables implied
    Call = Succ.

%------------------------------------------------------------------------%
%                       Call to Success Builtin
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- dom_impl(polyhedra, call_to_success_builtin/6, [noq]).
call_to_success_builtin(SgKey,Sh,Sv,Call,Proj,Succ):-
    polyhedra_initialize,
    call_to_success_builtin_(SgKey,Sh,Sv,Call,Proj,Succ),
    polyhedra_finalize.

call_to_success_builtin_(_SgKey,_Sh,_Sv,Call,_Proj,Succ):-
    Call = Succ.

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%            Assertion(I/O) related Functions                            %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

:- dom_impl(polyhedra, input_user_interface/5, [noq]).
input_user_interface(Cons_Sys,Qv,New_ASub,_Sg,_MaybeCallASub):-
    polyhedra_initialize,
    length(Qv,Dims),
    ppl_new_NNC_Polyhedron_from_space_dimension(Dims,universe,Poly),
    ASub = (Poly,Qv),
    input2builtin(Cons_Sys,ASub,New_ASub),
    polyhedra_finalize.

input2builtin([],ASub,ASub).
input2builtin([=(A,B)|Rest_Cons],ASub,New_ASub):- !,
    success_builtin0(unification,_,(A,B),ASub,ASub1),
    input2builtin(Rest_Cons,ASub1,New_ASub).
% it can only be < ,>, >=, =< as filtered by constraint/1
input2builtin([In_Equality|Rest_Cons],ASub,New_ASub):-
    success_builtin0(constraint,_,In_Equality,ASub,ASub1),
    input2builtin(Rest_Cons,ASub1,New_ASub).
    
:- dom_impl(polyhedra, input_interface/4, [noq]).
input_interface(InputUser,_Kind,Old_Cons_Sys,New_Cons_sys):-
    polyhedra_initialize,
    input_interface_(InputUser,_Kind,Old_Cons_Sys,New_Cons_sys),
    polyhedra_finalize.

input_interface_(constraint(Cons_Sys),perfect,Old_Cons_Sys,New_Cons_Sys):-
    append(Old_Cons_Sys,Cons_Sys,New_Cons_Sys). 

:- dom_impl(polyhedra, asub_to_native/5, [noq]).
asub_to_native('$bottom',_Qv,_OutFlag,'$bottom',[]) :- !.
asub_to_native(ASub1,_Qv,_OutFlag,[Output],[]):-
    polyhedra_initialize,
    ASub1 = (Poly,Vars),
    ppl_Polyhedron_get_minimized_constraints(Poly,Cons_Sys),
    dim2var(Cons_Sys,Vars,Named_Cons_Sys),
    ( Named_Cons_Sys = [] -> % Just 'true'
        % NOTE: this is a special case needed to avoid confusing
        % the assertion normalizer (which believes that any
        % property with no reference to predicate argument
        % variables is abridged syntax)
        Output = true
    ; Output = constraint(Named_Cons_Sys)
    ),
    polyhedra_finalize.


%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%            Intermediate Functions                                      %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

print_absu('$bottom') :- 
    display('No solution'),!.
print_absu((Poly,Vars)) :-
    ppl_Polyhedron_get_minimized_constraints(Poly,Poly_Cons),!,     
    ppl_Polyhedron_space_dimension(Poly,Dims),
    display('Dims: '),write(Dims),nl,
    display('Cons: '),write(Poly_Cons),nl,
    display('Vars: '),display(Vars),nl.
print_absu(Poly):-
    print_absu(('$address'(Poly),whatever_vars)).

:- pop_prolog_flag(multi_arity_warnings).


% Dimension Dim  associated with Var
get_dimension(ASub,Var,Dim):-
    ASub = (_Poly,Vars),!,
    my_nth(Vars,Var,Dim,not_instantiate).
get_dimension(Vars,Var,Dim):-
    list(Vars), % TODO: make sure it really checks?
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
    ppl_new_NNC_Polyhedron_from_space_dimension(0,universe,Poly),
    ASub_Empty = (Poly,[]). 
 

polyhedra_delete_polyhedron((Poly,_Vars)):-
    ppl_delete_Polyhedron(Poly),!.
polyhedra_delete_polyhedron(Poly):-
    ppl_delete_Polyhedron(Poly).


:- push_prolog_flag(multi_arity_warnings,off).

polyhedra_add_dimension((Poly,Vars),Added_Vars,(Poly,New_Vars)):-
    ppl_Polyhedron_add_space_dimensions_and_embed(Poly,1),
    append(Vars,[Added_Vars],New_Vars).
polyhedra_add_dimensions((Poly,Vars),New_Dims,(Poly,New_Vars)):-
    length(New_Dims,No_New_Dims),
    ppl_Polyhedron_add_space_dimensions_and_embed(Poly,No_New_Dims),
    append(Vars,New_Dims,New_Vars).

:- pop_prolog_flag(multi_arity_warnings).


match_dimensions(ASub1,ASub2,ASub1,ASub2):-
    ASub1 = (_Poly1,Vars1),
    ASub2 = (_Poly2,Vars2),
    Vars1 == Vars2,!.
match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2):-
    ASub1 = (_Poly1,Vars1),
    ASub2 = (_Poly2,Vars2),
    ord_intersection(Vars1,Vars2,Vars),
    project_(ASub1,Vars,New_ASub1),
    project_(ASub2,Vars,New_ASub2).

% This is complicated; comment!
polyhedra_merge(Old_ASub,New_ASub,Init_Vars_New,Merge):-
    Old_ASub= (Poly_Old,Vars_Old),
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly_Old,Poly_Old2),
    Old_ASub2 = (Poly_Old2,Vars_Old),       
    New_ASub=(Poly,Vars),
    ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(Poly,Poly2),
    New_ASub2 = (Poly2,Vars),
    polyhedra_merge_vars(Vars_Old,Init_Vars_New,New_ASub2,Merge),
    polyhedra_merge_poly(Old_ASub2,Merge).

% merge according to ASub2 the (renumbered) constraints of both 
% ASub2 contains more recent information about the variables so its used
% as reference
polyhedra_merge_poly(ASub1,ASub2):-
    ASub2=( Poly2,Vars2),
    project_(ASub1,Vars2,New_ASub1),
    New_ASub1=(Poly1,Vars2),
    ppl_Polyhedron_get_minimized_constraints(Poly1,Cons_Sys1),      
    ppl_Polyhedron_add_constraints(Poly2,Cons_Sys1).        

    
% mix the set of variables of both substitutions        
polyhedra_merge_vars([],_HvFv,Exit,Sorted_Exit):-
    polyhedra_sort_(Exit,Sorted_Exit).
polyhedra_merge_vars([Var|Rest_Vars],HvFv,Exit,Sorted_Exit):-
    ord_member(Var,HvFv),!,
    Exit=(Poly_Exit,Vars_Exit),
    match_vars(Var,Vars_Exit,New_Vars_Exit),
    New_Exit=(Poly_Exit,New_Vars_Exit),
    polyhedra_merge_vars(Rest_Vars,HvFv,New_Exit,Sorted_Exit).
polyhedra_merge_vars([Var|Rest_Vars],HvFv,Exit,Sorted_Exit):-
    polyhedra_add_dimension(Exit,Var,New_Exit),
    polyhedra_merge_vars(Rest_Vars,HvFv,New_Exit,Sorted_Exit).

match_vars(_Synonym,[],[]).
match_vars(Synonym,[Var|Rest_Vars],New_Varset):-
    Synonym == Var,!,
    New_Varset = [Var|Rest_Vars].
match_vars(Sinonym,[Var|Rest_Vars],New_Varset):-
    New_Varset = [Var|Rest_New_Varset],
    match_vars(Sinonym,Rest_Vars,Rest_New_Varset).


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
% ABSTRACT UNIFICATION

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
    Proj = (Poly,_Vars),
    var(X),
    ground(Term),
    number(Term),!,
    dim2var_var(X,Proj,Named_X),
    ppl_Polyhedron_add_constraint(Poly,Named_X = Term),     
    ab_unify(Binds,Proj,New_Proj,NewBinds).
ab_unify([(X,Term,[])|Binds],Proj,New_Proj,NewBinds):-
    var(X),
    ground(Term),
    polyhedra_remove_nonint_dims(Proj,X,Proj1),!,
    ab_unify(Binds,Proj1,New_Proj,NewBinds).
ab_unify([(X,Term,[])|Binds],Proj,New_Proj,NewBinds):-
    var(X),
    ground(Term),!,
    ab_unify(Binds,Proj,New_Proj,NewBinds).
ab_unify([_Bind|Binds],Proj,Proj,NewBinds):-
    ab_unify(Binds,Proj,Proj,NewBinds).

ab_unify_variables(X,Y,Proj,Folded_Proj):-
    dim2var_var(Y,Proj,Named_Y),
    dim2var_var(X,Proj,Named_X),!,
    Proj = (Poly,_Vars),
    ppl_Polyhedron_add_constraint(Poly,Named_X = Named_Y),
    Folded_Proj = Proj. 
ab_unify_variables(X,_Y,Proj,New_Proj):-
    polyhedra_remove_nonint_dims(Proj,X,New_Proj),!.
ab_unify_variables(_X,Y,Proj,New_Proj):-
    polyhedra_remove_nonint_dims(Proj,Y,New_Proj).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

polyhedra_remove_nonint_dims(ASub,Invalid_Dim,New_ASub):-
    ASub = (_Poly,Vars),
    polyhedra_find_nonint_dims(ASub,Invalid_Dim,Invalid_Dims),
    dim2var_list_var(Invalid_Dims,Vars,Named_Invalid_Dims),
    sort(Named_Invalid_Dims,Sorted_Invalid_Dims),
    ord_subtract(Vars,Sorted_Invalid_Dims,Valid_Dims),
    project_(ASub,Valid_Dims,New_ASub).

polyhedra_find_nonint_dims(ASub,Start,Invalid_Dims):-
    ASub = (Poly,Vars),
    dim2var_var(Start,Vars,Num_Start),
    dim2var_list_var(Vars,Vars,Num_Vars),
    find_nonint_dims([Num_Start],Poly,Num_Vars,Num_Vars,Invalid_Dims).

find_nonint_dims([],_Poly,_Vars,_Vars,[]).
find_nonint_dims([Dim|Rest_Dim],Poly,[],Vars,[Dim|Rest_Result]):-
    find_nonint_dims(Rest_Dim,Poly,Vars,Vars,Rest_Result).
find_nonint_dims([Dim|Rest_Dim],Poly,[Var|Rest_Vars],Vars,Result):-
    Dim \== Var,
    ppl_Polyhedron_relation_with_constraint(Poly,=(Dim,Var),Relation),
    member(is_included,Relation),
    append([Dim|Rest_Dim],[Var],Dims_Not_Int),
    ord_subtract(Vars,[Var],New_Vars),
    find_nonint_dims(Dims_Not_Int,Poly,Rest_Vars,New_Vars,Result).
find_nonint_dims([Dim|Rest_Dim],Poly,[_|Rest_Vars],Vars,Result):-
    find_nonint_dims([Dim|Rest_Dim],Poly,Rest_Vars,Vars,Result).

%-------------------------------------------------------------------------
% CONSTRAINT MANIPULATION/ TYPE CHECKER

dim2var_var(Var,Vars_Or_ASub,Renamed_Var):-
    var(Var),!,
    get_dimension(Vars_Or_ASub,Var,Dim_Var),
    Renamed_Var = '$VAR'(Dim_Var).
dim2var_var(Var,Vars,Name_Var):-
    ground(Var),
    Var='$VAR'(Dim),!,
    get_dimension(Vars,Name_Var,Dim).
dim2var_list_var([],_Vars,[]).
dim2var_list_var([Var|Rest_Var],Vars,[Ren_Var|Rest_Ren_Var]):-
    dim2var_var(Var,Vars,Ren_Var),
    dim2var_list_var(Rest_Var,Vars,Rest_Ren_Var).
    
dim2var_coefficient(Coeff):-
    integer(Coeff).

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

% ===========================================================================
% (Tests)

% TODO: move to polyhedra.test.pl module (reduce space) and turn into unit tests

% %:- export(test_extend/0).
% test_extend:-
%     polyhedra_initialize,
%     % call
%     %ppl_new_Polyhedron_from_space_dimension(nnc,6,universe,Poly1),
%     ppl_new_NNC_Polyhedron_from_space_dimension(6,universe,Poly1),
%     ppl_Polyhedron_add_constraints(Poly1,
%     ['$VAR'(5)=<3*'$VAR'(1),'$VAR'(5)=<4*'$VAR'(2),'$VAR'(5)>2*'$VAR'(4)]),
%     Vars_Call = [[_1,_2],[_3],[_4],[_5,_6,_7,_8],[_9],[_10]],
%     ASub_Call = (Poly1,Vars_Call),
%     % prime
%     ppl_new_NNC_Polyhedron_from_space_dimension(2,universe,Poly2),
%     Vars_Prime = [[_3,_4,_9],[_5,_6,_7,_8]],
%     ASub_Prime = (Poly2,Vars_Prime),
% 
%     Sv = [_1,_2,_3,_4,_5,_6,_7,_8,_9],
%     extend(not_provided_Sg,ASub_Prime,Sv,ASub_Call,ASub_Success),
%     print_absu(ASub_Success),
%     polyhedra_finalize.
% 
% %:- export(test_polyhedra_exit_to_prime/0).
% test_polyhedra_exit_to_prime:-
%     polyhedra_initialize,
%     % proj
%     ppl_new_NNC_Polyhedron_from_space_dimension(5,universe,Poly1),
%     ppl_Polyhedron_add_constraints(Poly1,['$VAR'(2)>'$VAR'(0)]),
%     Upd_Proj = (Poly1,[[_Sv1],[_Sv2,_Hv1],[_Sv3,_Sv4,_Hv2],[_Sv5],[_Fv1]]),
%     %exit
%     ppl_new_NNC_Polyhedron_from_space_dimension(1,universe,Poly2),
%     ppl_Polyhedron_add_constraints(Poly2,
%                                   ['$VAR'(0)=7]),
%     Exit = (Poly2,[[_Hv1,_Hv2]]),
%     Hv =   [_Hv1,_Hv2],
%     Sv=    [_Sv1,_Sv2,_Sv3,_Sv4,_Sv5],
%     ord_union(Hv,[_Fv1],HvFv),
%     ExtraInfo = (Upd_Proj,HvFv),
%     exit_to_prime(_Sg,Hv,_Head,Sv,Exit,ExtraInfo,Prime),
%     print_absu(Prime),
%     polyhedra_finalize.
% 
% test2(0).
% test2(X):-
%     test_polyhedra_exit_to_prime,
%     X1 is X-1,
%     test2(X1).
% 
% %:- export(test_polyhedra_call_to_success_fact/0).
% test_polyhedra_call_to_success_fact:-
%     polyhedra_initialize,
%     Sv1 = '$VAR'(0),
%     ppl_new_NNC_Polyhedron_from_space_dimension(3,universe,Poly1),
%     ppl_Polyhedron_add_constraint(Poly1,Sv1 >= 0),
%     ASub1 = (Poly1,[[_Sv1],[_Sv2],[_Sv3]]),
%     Sg = p(_Sv1,7),
%     Sv = [_Sv1],
%     Hv = [_Hv1],
%     Head = p(4,_Hv1),
%     Call=ASub1,
%     project(not_provided_Sg,Sv,not_provided_HvFv_u,Call,Proj),
%     %
%     call_to_entry(_Sv,Sg,Hv,Head,not_provided,[_Fv1],Proj,Entry,EI), % TODO: add some ClauseKey?
%     Entry = Exit,
%     exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,EI,Prime),
%     extend(not_provided_Sg,Prime,Sv,Call,Succ1), % TODO: use extend_??? (otherwise ppl is deinitialized in the middle)
%     call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_Prime,Succ2), % TODO: add some ClauseKey?
%     identical_abstract(Succ1,Succ2),
%     polyhedra_finalize.
% 
% %:- export(test_polyhedra_remove_nonint_dims/0).
% test_polyhedra_remove_nonint_dims:-
%     polyhedra_initialize,
%     ppl_new_NNC_Polyhedron_from_space_dimension(6,universe,Poly1),
%     ppl_Polyhedron_add_constraints(Poly1,
%           ['$VAR'(3)='$VAR'(1),'$VAR'(2)='$VAR'(1),'$VAR'(5)=<'$VAR'(0)] ),
%     ASub = (Poly1,[[_1],[_2],[_3],[_4],[_5],[_6]]), 
%     polyhedra_remove_nonint_dims(ASub,_3,New_ASub), 
%     print_absu(New_ASub),
%     polyhedra_finalize.
% 
% %:- export(test_ab_unify/0).
% test_ab_unify:-
%     polyhedra_initialize,
%     ppl_new_NNC_Polyhedron_from_space_dimension(6,universe,Poly1),
%     ppl_Polyhedron_add_constraints(Poly1,
%         ['$VAR'(3) =< 3 *'$VAR'(1),'$VAR'(2) ='$VAR'(3)+'$VAR'(4)]),
%     ASub1 = (Poly1,[[_1,_4],[_3,_5],[_7],[_8],[_9,_11],[_Hv1]]),
%     polyhedra_simplify_equations((_1,_3,_7,_9),(a,5,_Hv1,_Hv1),Binds),
%     abs_gunify(ASub1,Binds,ASub2,_New_Binds),
%     print_absu(ASub2),
%     polyhedra_finalize.
