:- module(deftypes,[
	gen_graph/0,
	build_defined_types_lattice/0,
	pre_build_defined_types_lattice/1,
	load_lib_deftypes/1,
	deftypes_call_to_entry/7,
	deftypes_exit_to_prime/7,
	deftypes_project/3,
	deftypes_compute_lub/2,
	deftypes_compute_lub_el/3,
%	deftypes_sort/2,
	deftypes_extend/4,
	deftypes_less_or_equal/2,
	deftypes_glb/3,
	deftypes_unknown_call/3,
	deftypes_unknown_entry/2,
	deftypes_empty_entry/2,
	deftypes_call_to_success_fact/8,
%	deftypes_special_builtin/4,
%	deftypes_success_builtin/5,
	deftypes_call_to_success_builtin/6,
	deftypes_input_interface/4,
	deftypes_asub_to_native/3,
	deftypes_output_interface/2,
	deftypes_input_user_interface/3,
	deftypes_collect_abstypes/3,
	deftypes_rename_abs/4,
	deftypes_identical_abstract/2,
	deftypes_widen/3,
	deftypes_widencall/3,
	approx_as_defined/2,
	deftypes_contains_parameters/1,
	absu/1
%	is_interesting_type/1
%	deftypes_concret/3
	%
%	concret/4,
%	normalize_type_asub/2,
%	revert_types/4,
%	shortening_el/2
	     ],
	     [assertions,regtypes,basicmodes,datafacts]).


:- doc(title,"Defined Types Abstract Domain (based on termsd.pl)").
:- doc(author, "Pawel Pietrzak").


:- doc(module,"

This module implements the abstract operations in the flavour of other
CiaoPP type domains, with the difference that only library types, user-defined
types and instances of parametric rules are in the domain. 
An abstrat sustitution is list of Var:Type elements, where Var is a 
variable and Type is a pure type term @cite{Dart-Zobel}. 

").

:- use_module(ciaopp(p_unit), [new_internal_predicate/3]).
% type operations from Pedro's library
:- use_module(typeslib(typeslib), 
	[
	    assert_param_type_instance/2,
	    compound_pure_type_term/4,
	    dz_type_included/2,
	    equiv_types/2,
	    insert_rule/2,
	    internally_defined_type_symbol/2,
	    new_type_symbol/1,
	    param_type_symbol_renaming/2,
	    pure_type_term/1,
	    recorda_required_types/1,
	    set_top_type/1,
	    type_escape_term_list/2,
	    type_intersection_2/3,
	    type_symbol/1,
	    get_preprocessing_unit_types/1,
	    paramtypedef/2,
	    assert_param_type_rule_instance/2,
	    param_matching_mode/1,
	    equivalent_to_top_type/1,
	    get_compatible_types/4,
	    belongs_to_type/2,
	    prlb/2,
	    get_type_definition/2,
	    non_parametric_type_rule_symbol_def/3,
	    parametric_type_rule_symbol_def/3,
	    assert_and_propagate_type_equivalence/2,
	    par_rule_type_symbol/1,
	    non_par_rule_type_symbol/1,
	    contains_type_param/1
	]).
:- use_module(typeslib(regtype_basic_lattice), 
	[ native_type_symbol/1, 
	  type_parameter/1,
	  base_type_symbol/1]).
:- use_module(typeslib(type_support), [ins_without_dup/2, find_list_entry/3]).
:- use_module(ciaopp(p_unit/aux_filenames), [is_library/1]).
%:- reexport(typeslib(typeslib),[insert_rule/2]). % delete

:- use_module(domain(termsd), [precondition_builtin/2, 	postcondition_builtin/4]).

:- use_module(engine(internals), [module_concat/3]).
:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(library(lists), [member/2]).
:- use_module(library(terms_vars), 
	[
	  varset/2
	]).
:- use_module(library(terms_check), 
	[
	  variant/2
	]).
:- use_module(library(lists), 
	[
	    append/3,
	    select/3
	]).
:- use_module(library(sets), 
	[ 
	    merge/3,
	    ord_subtract/3,
	    ord_member/2,
	    insert/3
	]).
:- use_module(library(sort), 
	[
	    sort/2
	]).

:- use_module(engine(io_basic)).

:- use_module(ciaopp(p_unit/itf_db), [current_itf/3, preloaded_module/2]).
:- use_module(library(assoc), [get_assoc/3]).
:- use_module(library(aggregates), [findall/3]).

:- regtype absu(A) # "@var{A} is an abstract substitution".

absu('$bottom').
absu([]).
absu([Elem|Absu]):- 
	absu_elem(Elem),
	absu(Absu).

:- regtype absu_elem(E) # "@var{E} is a single substitution".

absu_elem(Var:Type):-
	var(Var),
	pure_type_term(Type).

deftypes_input_interface(ground(X),perfect,Acc,[gnd(X)|Acc]).
deftypes_input_interface(regtype(T),perfect,Acc,[T|Acc]):-
        functor(T,_,1),!,
        may_be_var(Acc).
deftypes_input_interface(regtype(T),perfect,Acc,[NonPT|Acc]):-
        functor(T,_,2),!,
        arg(1,T,V),
        assert_param_type_instance(T,NonPType),
        functor(NonPT,NonPType,1),
        arg(1,NonPT,V),
        may_be_var(Acc).
% PP: TO BE FIXED:
deftypes_input_interface(member(X,L),perfect,Acc,[P|Acc]):-
	type_escape_term_list(L,Def),
        new_type_symbol(T),
	insert_rule(T,Def),
	P =.. [T,X].


may_be_var([]):- !.
may_be_var(_Acc).

	

%------------------------------------------------------------------%
:- pred deftypes_compute_lub(+ListASub,-Lub): list(absu) * absu # 
" It computes the least upper bound of a set of abstract
substitutions.  For each two abstract substitutions @var{ASub1} and
@var{ASub2} in @var{ListASub}, obtaining the lub is foreach X:Type1 in
@var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion is in Lub, and
TypeUnion is the deterministic union of Type1 an Type2.  ".

deftypes_compute_lub([ASub1,ASub2|Rest],Lub):-
	deftypes_compute_lub_el(ASub1,ASub2,ASub3),
	deftypes_compute_lub([ASub3|Rest],Lub).
deftypes_compute_lub([ASub],ASub).

%------------------------------------------------------------------%

deftypes_compute_lub_el('$bottom',ASub,ASub):- !.
deftypes_compute_lub_el(ASub,'$bottom',ASub):- !.
deftypes_compute_lub_el(ASub1,ASub2,ASub3):-
	ASub1 == ASub2, !,
	ASub3 = ASub2.
deftypes_compute_lub_el(ASub1,ASub2,ASub3):-
	deftypes_lub0(ASub1,ASub2,ASub3),!.

deftypes_lub0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
	X==Y,
%	type_union(T1,T2,T3,[]),
	types_lub(T1,T2,T3),
	deftypes_lub0(ASub1,ASub2,ASub3).
deftypes_lub0([],[],[]).



%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%--------------------------WIDENING----------------------------------%
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
% normalize_type_asub(Prime,Prime). % needed for plai framework

deftypes_widencall(_Prime0,Prime1,Prime1).
%deftypes_widencall(Prime0,Prime1,NewPrime):-
%	deftypes_widen(Prime0,Prime1,NewPrime).
%	display(terms_widencall),nl,
%	terms_compute_lub_el(Prime0,Prime1,Prime),
%	shortening(Prime,NewPrime).


:- pred deftypes_widen(+Prime0,+Prime1,-NewPrime):
absu * absu * absu #
"
Induction step on the abstract substitution of a fixpoint.
@var{Prime0} corresponds to non-recursive and @var{Prime1} to
recursive clauses.  @var{NewPrime} is the result of apply one widening
operation to the least upper bound of the formers.  Widening
operations implemented are ``shortening'' and ``restricted shortening''
@cite{gallagher-types-iclp94,Saglam-Gallagher-95} .  ".


deftypes_widen(Prime0,Prime1,NewPrime):-
 	deftypes_compute_lub_el(Prime0,Prime1,NewPrime).

%------------------------------------------------------------------%
:- pred deftypes_call_to_entry(+Sg,+Hv,+Head,+Fv,+Proj,-Entry,-ExtraInfo):  callable * list * 
callable * list * absu * absu * extrainfo # 
"
It obtains the abstract substitution @var{Entry} which results from
adding the abstraction of the @var{Sg} = @var{Head} to @var{Proj},
later projecting the resulting substitution onto @var{Hv}.
 This is done as follows: 
@begin{itemize} 
@item If @var{Sg} and @var{Head} are identical up to renaming it is just  
 renaming @var{Proj} and adding the @var{Fv} 
@item Otherwise, it will 
 @begin{itemize} 
 @item obtain the abstract substitution from unifying @var{Sg} and @var{Head} calling ``unify_term_and_type_term'' 
 @item add to this abstract substituion the variables in Fv as term type. 
 @end{itemize} 
@end{itemize} 

The meaning of the variables is
@begin{itemize}
@item @var{Sg} is the subgoal being analysed. 
@item @var{Head} is the Head of the clause being analysed. 
@item @var{Fv} is a list of free variables in the body of the clause being considered. 
@item @var{Proj} is the abstract substitution @var{Call} projected onto @var{Sv}. 
@item @var{Entry} is the Abstract entry substitution (i.e. the abstract subtitution obtained after the abstract unification of @var{Sg} and @var{Head} projected onto @var{Hv} + @var{Fv}). 
@item @var{ExtraInfo}is a flag ``yes'' when no unification is required, i.e.,  
Entry=Proj upto names of vars. and ignoring Fv. It is ``no''
 if unification fails. 
@end{itemize}
".

deftypes_call_to_entry(Sg,_,Head,Fv,Proj,Entry,Flag):- 
	variant(Sg,Head), !,
	Flag = yes,
	copy_term((Sg,Proj),(NewTerm,NewProj_u)),
	Head = NewTerm,
	terms_sort(NewProj_u,NewProj),
	variables_are_variable_type(Fv,Free),
	merge(Free,NewProj,Entry).
deftypes_call_to_entry(Sg,Hv,Head,Fv,Proj,Entry,dummy):-
	unify_term_and_type_term(Head,Hv,Sg,Proj,TmpEntry), !,
	variables_are_variable_type(Fv,Tmp),
	merge(Tmp,TmpEntry,Entry).
deftypes_call_to_entry(_Sg,_Hv,_Head,_Fv,_Proj,'$bottom',no).

:- regtype extrainfo/1.

extrainfo(yes).
extrainfo(no).

:- pred variables_are_variable_type(+Fv,-ASub): list * absu # 
"at the moment it assigns the value top_type to the variables in @var{Fv}
 but in the future it must assign the value ``var''".


variables_are_variable_type(Fv,ASub):-
	variables_are_top_type(Fv,ASub).


%------------------------------------------------------------------%
:- pred deftypes_exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime): list
* list * callable * callable * absu * extrainfo * absu # 
"
It computes the prime abstract substitution @var{Prime}, i.e.  the result of 
 going from the abstract substitution over the head variables @var{Exit}, to
 the abstract substitution over the variables in the subgoal. It will:
 @begin{itemize}
@item If @var{Exit} is '$bottom', @var{Prime} will be also '$bottom'.               
@item If @var{ExtraInfo} = yes (@var{Head} and @var{Sg} identical up to renaming) it is just 
renaming Exit                                            %
@item  Otherwise: it will 
 @begin{itemize}                                                        
  @item projects @var{Exit} onto @var{Hv} obtaining @var{BPrime}. 
  @item obtain the abstract substitution from unifying @var{Sg} and @var{Head} calling 
         ``unify_term_and_type_term'' 
 @end{itemize}
@end{itemize}
".

deftypes_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
	Prime = '$bottom'.
deftypes_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
	deftypes_project(Hv,Exit,BPrime),
	copy_term((Head,BPrime),(NewTerm,NewPrime)),
	Sg = NewTerm,
	terms_sort(NewPrime,Prime).	
deftypes_exit_to_prime(Sg,Hv,Head,Sv,Exit,_ExtraInfo,Prime):- 
	deftypes_project(Hv,Exit,BPrime),
	unify_term_and_type_term(Sg,Sv,Head,BPrime,Prime).
deftypes_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').


:- pred unify_term_and_type_term(+Term1,+Tv,+Term2,+ASub,-NewASub): callable * list * 
callable * absu * absu # 
"it unifies the term @var{Term1} to the type term @var{Term2}
obtaining the the abstract substitution TypeAss which is sorted and
projeted on @var{Tv}".



unify_term_and_type_term(Term1,Tv,Term2,ASub,NewASub):-
	copy_term((Term2,ASub),(TypeTerm,ASub0)),
	TypeTerm =.. [_|Types],
	Term1 =.. [_|Args],
	type_escape_term_list(Types,EscTypes),
	apply(ASub0),
	deftypes:generate_a_type_assigment(EscTypes,Args,TypeAss),
	( 
	    member(_:bot,TypeAss) -> fail
	;
	    terms_sort(TypeAss,ASub1),
	    deftypes_project(Tv,ASub1,NASub),
	    normal_asub(NASub,NewASub)
	).

normal_asub([],[]).
normal_asub([X:Type|ASub],[X:NType|NASub]):-
	normalize(Type,NType),
	normal_asub(ASub,NASub).

normalize(Type,NType):-
	nonvar(Type),
	(
	    number(Type);
	    Type = [] ;
	    Type = [_|_];
	    Type = ^(_) 
	),!,
        new_type_symbol(NType0),
	insert_rule(NType0,[Type]),
	approx_as_defined(NType0,NType).
%	remove_rule(NType0).

normalize(Type,NType):-
	approx_as_defined(Type,NType).

:- pred apply(+ASub): absu # 
"it unifies the variables in the abstract
substitution @var{ASub} to his respective values".

apply([Term:Term|ASub]):-
	apply(ASub).
apply([]).

generate_a_type_assigment(Type_List, Term_List, TypeAss):- 
      varset(Term_List, Term_Vars),     
      get_var_types_by_unification(Type_List, Term_List, Types),
      intersec_types_2(Term_Vars, Types, [], TypeAss).

get_var_types_by_unification([], [], _Types):-
   !.
get_var_types_by_unification([Type|Type_List], [Term|Term_List], Types):-
   compute_type(Term, Type, Types),
   get_var_types_by_unification(Type_List, Term_List, Types).

compute_type(Term, Type, Types):-
    equivalent_to_top_type(Type), 
    % top_type(Type), 
    !, 
    insert_top_type(Term, Types).
compute_type(Term, Type, Types):-
    var(Term), 
    !, 
    insert_type(Types, Term, Type).
compute_type(Term, Type, _Types):-
    atomic(Term), 
    !, 
    belongs_to_type(Term, Type).

compute_type(Term, Type, Types):-    
    nonvar(Term), 
    functor(Term, F, A), 
    get_compatible_types(F/A, Type, [], CompTypes),
    \+ (CompTypes = []),
    ( there_are_only_one_compa_type(CompTypes, CompTerm) -> 
%    ( CompTypes = [CompTerm] -> 
        compute_args_type(A, Term, CompTerm, Types)
        ;
        insert_top_type(Term, Types)).

there_are_only_one_compa_type(CompTypes, CompTerm):-
  CompTypes = [CType],
  compound_pure_type_term(CType, CompTerm, _Name, _Arity).


compute_args_type(A, _Term, _CompType, _Types):-
   A =:= 0, !.
compute_args_type(A, Term, CompType, Types):-
   A > 0, 
   arg(A, Term, Term_Arg),
   arg(A, CompType, Type_Arg), 
   compute_type(Term_Arg, Type_Arg, Types),
   A1 is A - 1, 
   compute_args_type(A1, Term, CompType, Types).


insert_type(NVarList, Var, NVar):- 
	insert_list_entry(NVarList, Var, vt(Var, VList)),
	ins_without_dup(VList, NVar). % or possibly do glb right here

insert_list_entry(VT, Var, Entry) :- 
	var(VT), !,
	Entry = vt(Var, _),
	VT = [Entry|_].
insert_list_entry(VT, Var, Entry) :- 
	nonvar(VT),
	VT = [E|_],
	E = vt(EVar, _),
        EVar == Var, !,
        Entry = E.
insert_list_entry(VT, Var, Entry) :- 
	nonvar(VT),
	VT = [E|S],
        E = vt(EVar, _),
	EVar \== Var,
	insert_list_entry(S, Var, Entry).


insert_top_type(Term, Types):-
	varset(Term,TVs),
	set_top_type(TopType),
	insert_top_forall(TVs,TopType,Types).

insert_top_forall([V|Vs],TopType,Types) :-
	insert_type(Types,V,TopType),
	insert_top_forall(Vs,TopType,Types).
insert_top_forall([],_,_).

% Variables which do not have type are assigned the top type.
intersec_types_2([], _Var_Types, OTypeAss, OTypeAss):-
   !.
intersec_types_2([Var|List], Var_Types, ITypeAss, OTypeAss):-
   find_list_entry(Var_Types, Var, Entry),
   (var(Entry) -> Types = _
                  ;
                  Entry = vt(_, Types)),
   set_top_type(Top),
   intersec_type_list_2(Types, Top, LType),
   intersec_types_2(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).

intersec_type_list_2(Type_List, Type, Type):-
   var(Type_List), 
   !.
intersec_type_list_2(Type_List, InType, OutType):-
   nonvar(Type_List),
   Type_List = [Type|List],
   type_intersection_2(InType, Type, Intersec),
   intersec_type_list_2(List, Intersec, OutType).



%------------------------------------------------------------------%
:- pred deftypes_project(+Vars,+Asub,-Proj): list * absu * absu # 
"@var{Proj} is the result of eliminating from @var{Asub} all
@var{X}:@var{Value} such that @var{X} is not in @var{Vars}".

deftypes_project(_,'$bottom',Proj):- 
	Proj = '$bottom'.
deftypes_project(Vars,ASub,Proj) :- 
	deftypes_project_aux(Vars,ASub,Proj).

deftypes_project_aux([],_,Proj):- !,
	Proj = [].
deftypes_project_aux(_,[],Proj):- !,
	Proj = [].
deftypes_project_aux([Head1|Tail1],[Head2:Type|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	deftypes_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

deftypes_project_aux_(=,_,Tail1,HeadType,Tail2,[HeadType|Proj]) :-
	deftypes_project_aux(Tail1,Tail2,Proj).
deftypes_project_aux_(>,Head1,Tail1,_,[Head2:Type|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	deftypes_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).



%------------------------------------------------------------------%
:- pred terms_sort(+Asub,-Asub_s): absu * absu
# 
"It sorts the set of @var{X}:@var{Type} in @var{Asub} ontaining @var{Asub_s}".

terms_sort('$bottom','$bottom'):- !.
terms_sort(ASub,ASub_s):- sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- pred deftypes_extend(+Prime,+Sv,+Call,-Succ): absu * list * absu * absu # 
"
If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
 @var{Succ} is computed updating the values of @var{Call} with those
 in @var{Prime}".

deftypes_extend('$bottom',_Sv,_Call,'$bottom'):- !.
deftypes_extend(Prime,Sv,Call,Succ):-
	subtract_keys(Call,Sv,RestCall),
	merge(RestCall,Prime,Succ).



subtract_keys([K:_|Xs],Ks,Dict):-
	ord_member(K,Ks), !,
	subtract_keys(Xs,Ks,Dict).
subtract_keys([X|Xs],Ks,[X|Dict]):-
	subtract_keys(Xs,Ks,Dict).
subtract_keys([],_Ks,[]).


%------------------------------------------------------------------%
:- pred deftypes_less_or_equal(+ASub0,+ASub1): absu * absu # 
"Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
it's assumed the two abstract substitutions are defined on the same variables".


deftypes_less_or_equal('$bottom',_ASub):- !.
deftypes_less_or_equal(ASub1,ASub2):-
	ASub1 == ASub2, !.
deftypes_less_or_equal(ASub1,ASub2):-
	deftypes_less_or_equal0(ASub1,ASub2).

deftypes_less_or_equal0([X:T1|ASub1],[Y:T2|ASub2]):-
	X==Y,
%	dz_type_included(T1,T2),
	def_subtype(T1,T2),
	deftypes_less_or_equal0(ASub1,ASub2).
deftypes_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- pred deftypes_glb(+ASub0,+ASub1,-Glb): absu * absu * absu # 
"@var{Glb} is the great lower bound of @var{ASub0} and @var{ASub1}".


deftypes_glb('$bottom',_ASub,'$bottom'):- !.
deftypes_glb(_ASub,'$bottom','$bottom'):- !.
deftypes_glb(ASub1,ASub2,ASub3):-
	ASub1 == ASub2, !,
	ASub3 = ASub2.
deftypes_glb(ASub1,ASub2,ASub3):-
	deftypes_glb0(ASub1,ASub2,ASub3), !.
deftypes_glb(_ASub1,_ASub2,'$bottom').



deftypes_glb0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
	X==Y,
	types_glb(T1,T2,T3),!,
	T3 \== bot,
	deftypes_glb0(ASub1,ASub2,ASub3).
deftypes_glb0([],[],[]).



%------------------------------------------------------------------%
:- pred deftypes_unknown_entry(+Qv,-Call): list * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to   
 Call. In this domain the top value is X:term forall X in the set of variables".

deftypes_unknown_entry(Vars,ASub):-
	variables_are_top_type(Vars,ASub).

:- pred deftypes_empty_entry(+Vars,-Entry): list * absu # "Gives the
""empty"" value in this domain for a given set of variables
@var{Vars}, resulting in the abstract substitution @var{Entry}. I.e.,
obtains the abstraction of a substitution in which all variables
@var{Vars} are unbound: free and unaliased. In this domain the empty
value is giving the variable type to each variable".

deftypes_empty_entry(Vars,ASub):-
	variables_are_variable_type(Vars,ASub).


%------------------------------------------------------------------%
:- pred deftypes_unknown_call(+Call,+Vars,-Succ): absu * list * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to
 @var{Call}".

deftypes_unknown_call(Call,Vars,Succ):-
	substitution(Call,CallVars,_),
	ord_subtract(Vars,CallVars,TopVars),
	variables_are_top_type(TopVars,ASub),
	merge(Call,ASub,Succ).
	
substitution([],[],[]).
substitution([X:T|TypeAss],[X|Vars],[T|ListTypes]):-
	substitution(TypeAss,Vars,ListTypes).

:- pred variables_are_top_type(+Fv,-ASub): list * absu # 
"it assigns the value top_type to the variables in @var{Fv}
and return the abstract substitution @var{ASub} ".

variables_are_top_type([V|Fv],[V:Type|ASub]):-
	set_top_type(Type),
	variables_are_top_type(Fv,ASub).
variables_are_top_type([],[]).



%------------------------------------------------------------------%
:- pred deftypes_call_to_success_fact(+Sg,+Hv,+Head,+Sv,+Call,+Proj,-Prime,-Succ): callable * 
list * callable * list * absu * absu * absu * absu # 
"Specialized version of call_to_entry + exit_to_prime + extend for facts".

deftypes_call_to_success_fact(Sg,Hv,Head,Sv,Call,Proj,Prime,Succ):-
	deftypes_call_to_entry(Sg,Hv,Head,[],Proj,Entry,ExtraInfo),
	deftypes_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
	deftypes_extend(Prime,Sv,Call,Succ).




%------------------------------------------------------------------------%
%			    USER INTERFACE
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% deftypes_input_user_interface(+InputUser,+Qv,-ASub)                       %
% Obtains the abstract substitution ASub from user supplied information. %
%------------------------------------------------------------------------%

deftypes_input_user_interface(InputUser,Qv,ASub):-
        obtain_Asub_user(InputUser,ASub0),
	sort(ASub0,ASub_s),
	reduce_same_var(ASub_s,ASub1),
	substitution(ASub1,Vars,_),
	ord_subtract(Qv,Vars,TopV),
	variables_are_top_type(TopV,ASub2),
	sort(ASub2,ASub3),
	merge(ASub1,ASub3,ASub).

obtain_Asub_user([],[]):- !.
obtain_Asub_user([User|InputUser],[X:T|ASub]):-
	functor(User,T,_),
	arg(1,User,X),
	obtain_Asub_user(InputUser,ASub).

reduce_same_var([X:T|ASub],NewASub):-
	reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var([],[]).

reduce_same_var_([Y:TY|ASub],X,TX,NewASub):-
	reduce_same_var__(Y,TY,X,TX,ASub,NewASub).
reduce_same_var_([],X,T,[X:T]).

reduce_same_var__(Y,TY,X,TX,ASub,NewASub):-
	X == Y, !,
%	type_intersection_2(TY,TX,T),
	types_glb(TY,TX,T),
	reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var__(Y,TY,X,TX,ASub,[X:TX|NewASub]):-
	reduce_same_var_(ASub,Y,TY,NewASub).


% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
% 	Type=..[T,X],
% 	inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).


%------------------------------------------------------------------------%
% deftypes_asub_to_native(+ASub,+Flag,-OutputUser)                          %
% Transforms abstract substitution ASub to user friendly format.         %
%------------------------------------------------------------------------%


deftypes_asub_to_native(ASub,Flag,OutputUser):-
	deftypes_asub_to_native0(ASub,OutputUser1),
	equiv_types(OutputUser1,OutputUser2),
	revert_types(OutputUser2,OutputUser,Symbols,[]),
	recorda_required_types_(Flag,Symbols).

deftypes_asub_to_native0([X:T|ASub],[Type|OutputUser]):-
	revert_type(T,X,Type),
	deftypes_asub_to_native0(ASub,OutputUser).
deftypes_asub_to_native0([],[]).

revert_type(T,X,Type):-
	type_symbol(T), !,
	functor(Type,T,1),
	arg(1,Type,X).

%	Type=..[T,X].
revert_type(T,X,(X=T)).      

revert_types([Type|OutputUser],[NType|NOutputUser],Symbols,Rest):-
	( 
	    Type = (_X = T) ->
	    symbols_of(T,Symbols,Rest1),
	    NType = Type
	;
	    functor(Type,S,AS),
	    arg(1,Type,X),
	    ( 
		param_type_symbol_renaming(PT,S) ->
		PT=..[N|Args],
		% parametric are not created: so not required
		% Symbols = [PT|Rest1],
		%pp% Symbols = Rest1,
		append(Args,Rest1,Symbols),
		NType=..[N,X|Args]
	    ;
		( 
		    internally_defined_type_symbol(S,AS) ->
		    Symbols = [S|Rest1],
		    new_internal_predicate(S,AS,NewS),
		    Type=..[S|Args],
		    NType=..[NewS|Args]
		;
		    Symbols = Rest1,
		    NType=Type
		)
	    )
	),
	revert_types(OutputUser,NOutputUser,Rest1,Rest).
revert_types([],[],S,S).

symbols_of(T,Symbols,Rest):-
	compound_pure_type_term(T,Term,_Name,Arity),!,
	symbols_of0(Arity,Term,Symbols,Rest).
symbols_of(T,[T|Rest],Rest).

symbols_of0(0,_Term,S,S).
symbols_of0(N,Term,Symbols,Rest):-
	arg(N,Term,T),
	symbols_of(T,Symbols,Rest1),
	N1 is N - 1,
	symbols_of0(N1,Term,Rest1,Rest).

recorda_required_types_(no,_Symbols).
recorda_required_types_(yes,Symbols):-
	recorda_required_types(Symbols).

%------------------------------------------------------------------------%
% deftypes_output_interface(+ASub,-Output)                                  %
% Transforms abstract substitution ASub to a more readible but still     %
% close to internal format.                                              %
%------------------------------------------------------------------------%

deftypes_output_interface(ASub,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

deftypes_collect_abstypes([],Types,Types).
deftypes_collect_abstypes([_:Type|Abs],Types0,Types):-
	insert(Types0,Type,Types1),
	deftypes_collect_abstypes(Abs,Types1,Types).

deftypes_rename_abs([],_,_,[]).
deftypes_rename_abs([C|Call],Types,Names,[RenC|RenCall]):-
	C = Var:Type,
	RenC = Var:RenType,
	get_value_(Types,Type,RenType),
%	new_type_name(RenName),
%	insert_type_name(RenName,[],0),
	deftypes_rename_abs(Call,Types,Names,RenCall).

get_value_(Rens,Type,RenType):-
	assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%

deftypes_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
deftypes_identical_abstract(ASub1,ASub2):-
	deftypes_identical_abstract0(ASub1,ASub2).

deftypes_identical_abstract0([X:Type0|ASub0],[Y:Type1|ASub1]):-
	X==Y,
        def_equivalent_types(Type0,Type1),
	deftypes_identical_abstract0(ASub0,ASub1).
deftypes_identical_abstract0([],[]).


def_equivalent_types(T0,T1) :-
 	T0 == T1,!.
def_equivalent_types(T0,T1) :-
	( def_equiv_types(T0,T1) ; def_equiv_types(T1,T0) ),!.
def_equivalent_types(T0,T1) :-
	def_subtype(T0,T1),
	def_subtype(T1,T0).
%% ---------------------------------------------------------------------------

deftypes_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
	deftypes_call_to_success_fact(p(X,Y),[W],p(W,W),Sv,Call,Proj,_Prime,Succ).

deftypes_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
	(
	    precondition_builtin(Key,Sg) ->
	    postcondition_builtin(Key,Bg,Bv,Exit),
	    deftypes_exit_to_prime(Sg,Bv,Bg,Sv,Exit,no,Prime1),
	    deftypes_glb(Proj,Prime1,Prime),
	    deftypes_extend(Prime,Sv,Call,Succ)
	;
	    Succ = '$bottom'
	).

%% ---------------------------------------------------------------------------
:- use_module(library(read), [read/2]).

load_lib_deftypes(Stream):-
	repeat,
	read(Stream,Fact),
	(
	    Fact = end_of_file ->
	    true
	;
	    assertz_fact(Fact),
	    fail
	).
	
%% ---------------------------------------------------------------------------


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preloading defined types lattice
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

pre_build_defined_types_lattice(_) :-
	build_defined_types_lattice,
	fail.
pre_build_defined_types_lattice(S) :-
	nl(S),
	pgm_def_equiv_types(A,B),
	displayq(S,lib_def_equiv_types(A,B)),
	display(S,'.'),nl(S),
	fail.
pre_build_defined_types_lattice(S) :-
	nl(S),
	pgm_def_subtype_basic(A,B),
	displayq(S,lib_def_subtype_basic(A,B)),
	display(S,'.'),nl(S),
	fail.
pre_build_defined_types_lattice(S) :-
	nl(S),
	pgm_param_type_hook(A,B,C),
	displayq(S,lib_param_type_hook(A,B,C)),
	display(S,'.'),nl(S),
	fail.
pre_build_defined_types_lattice(S) :-
	nl(S),
	pgm_functor_types(A,B,C),
	displayq(S,lib_functor_types(A,B,C)),
	display(S,'.'),nl(S),
	fail.
pre_build_defined_types_lattice(_).
	
build_defined_types_lattice :-
	retractall_fact(pgm_def_subtype_basic(_,_)),
	retractall_fact(pgm_def_equiv_types(_,_)),
	retractall_fact(pgm_param_type_hook(_,_,_)),
	retractall_fact(pgm_functor_types(_,_,_)),
	get_preprocessing_unit_types(Types),
	keep_interesting_types(Types,[],ITypes),
	build_lattice(ITypes).

keep_interesting_types([],Ts,Ts).
keep_interesting_types([T|Ts],ITs1,Out) :-
	( is_interesting_type(T,build) ->
	  ITs = [T|ITs1]
	; ITs = ITs1
	),
	keep_interesting_types(Ts,ITs,Out).

is_interesting_type(term,_) :-!.
is_interesting_type(bot,_) :-!.
is_interesting_type(T,_) :-
	base_type_symbol(T),!.
is_interesting_type(T,Mode) :-
	( param_type_symbol_renaming(Head,T)
	; param_type_symbol_renaming(T,_), Head = T
	),!,
	param_type_hook(Head,[V|_],_),
	is_interesting_type(V,Mode).
is_interesting_type(T,Mode) :-
	atom(T),
	module_split(T,M,_),
	interesting_module(M,Mode).

interesting_module(M,build) :-
	preloaded_module(M,_Base),!,fail.
interesting_module(basic_props,_).
interesting_module(arithmetic,_).
interesting_module(assertions_props,_).
interesting_module(term_typing,_).
interesting_module(Module,_) :- 
	current_itf(defines_module,Module,Base),
	\+ is_library(Base).

:- data lib_def_equiv_types/2.
:- data lib_def_subtype_basic/2.
:- data lib_param_type_hook/3.
:- data lib_functor_types/3. 

:- data pgm_def_equiv_types/2.
:- data pgm_def_subtype_basic/2.
:- data pgm_param_type_hook/3.
:- data pgm_functor_types/3. 

def_subtype_basic(T1,T2) :-
	pgm_def_subtype_basic(T1,T2).
def_subtype_basic(T1,T2) :-
	lib_def_subtype_basic(T1,T2).

def_equiv_types(T1,T2) :-
	pgm_def_equiv_types(T1,T2).
def_equiv_types(T1,T2) :-
	lib_def_equiv_types(T1,T2).

param_type_hook(A,B,C) :-
	pgm_param_type_hook(A,B,C).
param_type_hook(A,B,C) :-
	lib_param_type_hook(A,B,C).

%% functor_types(F,Ts,B) :-
%% 	( pgm_functor_types(F,Ts1,B); Ts1 = [] ),
%% 	( lib_functor_types(F,Ts2,B); Ts2 = [] ),  
%% 	append(Ts1,Ts2,Ts).  

% build the basic graph, can be improved 
build_lattice(Ts0) :-
	add_paramdefs(ParamDefs),
	append(ParamDefs,Ts0,Ts05),
	del_equivalent([term|Ts05],Ts), % sort of chapuza
	select(T0,Ts,Ts1),
	select(T1,Ts1,Ts2),
	T1 \= bot,
	dz_type_included(T0,T1), 
	\+ ( member(T2,Ts2), dz_type_included(T2,T1), dz_type_included(T0,T2)),
	assertz_fact(pgm_def_subtype_basic(T0,T1)),
	fail.
build_lattice(_) :-
	def_subtype_basic(T,_),
	\+ def_subtype_basic(_,T),
	T \= bot,
	assertz_fact(pgm_def_subtype_basic(bot,T)),
	fail.
build_lattice(Types) :-
	create_defined_types_filters_x(Types).

%remove_irrelevant_params([T|Ts],Out) :-
%	( param_to_remove(T) ->
%	  Out = Out1
%	; Out = [T|Out1]
%	),
%	remove_irrelevant_params(Ts,Out1).
%remove_irrelevant_params([],[]).

%param_to_remove(P) :-
%	param_type_symbol_renaming(Head,P),
%	param_type_hook(Head,Vs,_),
%	\+ keep_interesting_types(Vs,Vs).

create_defined_types_filters_x([]).
create_defined_types_filters_x([T|Ts]) :-
	prlb(T,Fs),
	add_to_each_functor(Fs,T),
	create_defined_types_filters_x(Ts).

add_to_each_functor([],_).
add_to_each_functor([F|Fs],T) :-
	( retract_fact(pgm_functor_types(F,Ts,_)) ->
	  append(Ts,[T],Ts1)
	; Ts1 = [T]
	),
	( native_type_symbol(F) ->
	  M = basic
	; M = rule
	),
	assertz_fact(pgm_functor_types(F,Ts1,M)),
	add_to_each_functor(Fs,T).


add_paramdefs(ParamDefs) :-
	findall(P,add_one_paramdef(P),ParamDefs).

add_one_paramdef(ParSymb) :-
	paramtypedef(Head,_),
	varset(Head,HVs),
        copy_term(Head,CHead),
	varset(CHead,CHVs),
	ground_params_to_top(CHVs),
	assert_param_type_rule_instance(CHead,ParSymb),
	assertz_fact(pgm_param_type_hook(Head,HVs,ParSymb)).
	
ground_params_to_top([]).
ground_params_to_top([term|Ps]) :-
	ground_params_to_top(Ps).

del_equivalent([],[]).
del_equivalent([T|Ts],[T|NoEq]) :-
	del_eq(T,Ts,Ts1),
	del_equivalent(Ts1,NoEq).

del_eq(_T,[],[]).
del_eq(T,[T1|Ts],NoEq) :-
	( dz_type_included(T,T1), dz_type_included(T1,T) ->
	  assertz_fact(pgm_def_equiv_types(T,T1)),
	  NoEq = NoEq1
	; NoEq = [T1|NoEq1]
	),
	del_eq(T,Ts,NoEq1).


get_param_head(TypeSymb,Head) :-
	( atom(TypeSymb) ->
	  get_canonical_type(TypeSymb,Can),
	  param_type_symbol_renaming(Head,Can)
	; Head = TypeSymb
	).


def_subtype(T1,T2) :-
 	contains_type_param(T2),
 	param_matching_mode(on),!,
	dz_type_included(T1,T2).
def_subtype(_,term) :-!.
def_subtype(bot,_) :-!.
% both parametric types
def_subtype(T1,T2) :-
	get_param_head(T1,Par1),
	get_param_head(T2,Par2),!,
	param_type_hook(Par1,Vs1,PT),
	param_type_hook(Par2,Vs2,PT), % same param rule?
	def_subtype_all(Vs1,Vs2).
% first one parametric
def_subtype(T1,T2) :-
	param_type_symbol_renaming(Par1,T1),
	\+ def_subtype_basic(T1,_),
	\+ def_subtype_basic(_,T1), !, % not in the lattice
	param_type_hook(Par1,_,PT),
	def_subtype(PT,T2).
def_subtype(T1,T2) :-
	get_canonical_type(T1,CT1),
	get_canonical_type(T2,CT2),
	def_subtype_x(CT1,CT2),!.

def_subtype_all([],[]).
def_subtype_all([T1|Ts1],[T2|Ts2]) :-
	def_subtype(T1,T2),
	def_subtype_all(Ts1,Ts2).


get_canonical_type(T,CT) :-
	def_equiv_types(CT,T),!.
get_canonical_type(T,CT) :-
	base_type_symbol(T),
	module_concat(basic_props,T,CT),!.
% not quite right...
get_canonical_type(T,CT) :-
	\+ is_interesting_type(T,canonical),
	\+ internally_defined_type_symbol(T,1),
	T \= ^(_),
	T \= [],
	T \= [_|_],
	\+ number(T),
	!,
	CT = term.
get_canonical_type(T,T).

def_subtype_x(T,T) :-!.
def_subtype_x(T1,T2) :-
	def_subtype_basic(T1,T2),!.
def_subtype_x(T1,T2) :-
	def_subtype_basic(T1,T3),
	def_subtype(T3,T2).

% GLB is not quite safe...
% keep the old version for the time being...
types_glb(TY,TX,T) :-
	type_intersection_2(TY,TX,T_tmp),
	approx_as_defined(T_tmp,T),!.


gen_subtype(T,T).
gen_subtype(T,Sub) :-
	def_subtype_basic(Sub1,T),
	gen_subtype(Sub1,Sub).

types_lub(_,term,term):-!.
types_lub(term,_,term):-!.
% not quite complete yet...
types_lub(T1,T2,LUB) :-
	def_subtype(T1,T2),
	def_subtype(T2,T1),
	!, 
	( T1 @> T2 -> LUB = T2; LUB = T1). 
types_lub(T1,T2,LUB) :-
	( def_subtype(T1,T2), LUB=T2
	; def_subtype(T2,T1), LUB=T1
	),
	!.
types_lub(T1,T2,T3) :-
	get_param_head(T1,Par1),
	get_param_head(T2,Par2),
	param_type_hook(Par1,Vs1,PT),
	param_type_hook(Par2,Vs2,PT), % same param rule?
	!,
	lub_all(Vs1,Vs2,VsLUB),
	param_type_hook(ParLUB,VsLUB,PT),
	assert_param_type_rule_instance(ParLUB,T3).
types_lub(T1,T2,LUB) :-
	get_canonical_type(T1,CT1),
	gen_suptype(CT1,Sup1),
	def_subtype(T2,Sup1),!,
	LUB = Sup1.
types_lub(_T1,_T2, term).


lub_all([],[],[]).
lub_all([T1|Ts1],[T2|Ts2],[T3|Ts3]) :-
	types_lub(T1,T2,T3),
	lub_all(Ts1,Ts2,Ts3).

gen_suptype(T,T).
gen_suptype(T,Sup) :-
	def_subtype_basic(T,Sup1),
	gen_suptype(Sup1,Sup).
gen_suptype(T,S) :-
	get_param_head(T,Par),
	param_type_hook(Par,[V|_],PT),
	gen_subtype(V,SupV),
	param_type_hook(S0,[SupV|_],PT),
	add_param_rule_if_needed(S0,S).
	

add_param_rule_if_needed(T,T1) :-
	atom(T),!,
	T1 = T.
add_param_rule_if_needed(T,PT) :-
	param_type_symbol_renaming(T,PT),!.
add_param_rule_if_needed(T,PT) :-
	assert_param_type_rule_instance(T,PT).

% defined types  "widening" starts here
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

approx_as_defined(Type,ApproxType):-
	get_canonical_type(Type,CT),
	( CT == term ; def_subtype_basic(CT,_) ),% def_subtype_basic(_,CT) ),
	!,
	ApproxType = Type.
approx_as_defined(Type,ApproxType):-
 	type_parameter(Type),
 	param_matching_mode(on),!,
 	ApproxType = Type.
approx_as_defined(Type,ParType):-
 	match_one_rule_as_parametric(Type,ParType),!.
approx_as_defined(Type,ApproxType):-
	get_canonical_type('basic_props:term',MinSoFar),
	find_min_in_lattice(Type,MinSoFar,ApproxType),!.


find_min_in_lattice(Type,MinSoFar,Min) :-
	def_subtype_basic(New,MinSoFar),
	dz_type_included(Type,New),!,
	find_min_in_lattice(Type,New,Min).
find_min_in_lattice(_,Min,Min).


match_one_rule_as_parametric(Type, NewType):-
	param_type_symbol_renaming(_,Type),
	!,
	NewType = Type.
match_one_rule_as_parametric(Type, NtypSymbol1):-
	get_type_definition(Type,Def),
	TypeDef = typedef(Type,Def),
	paramtypedef(Head,Body), 
	ParRule = paramtypedef(Head,Body), 
        copy_term(ParRule, Rule),
        non_parametric_type_rule_symbol_def(TypeDef, NTypeSymbol, NDefin),
        parametric_type_rule_symbol_def(Rule, PTypeSymbol, PDefin),
%        order_type_defin(PDefin, OrPDefin), !, 
        match_defin(NDefin, PDefin, PDefin), 
        ground(PTypeSymbol),
        assert_param_type_rule_instance(PTypeSymbol, Cand),
        dz_type_included(NTypeSymbol, Cand),
	!,
        assert_and_propagate_type_equivalence(NTypeSymbol, Cand),
	check_max_depth(Cand,3,NtypSymbol1).


match_defin([], RestPDefin, PDefin) :-
	RestPDefin \= PDefin, % some parts of the parametric rule have
                              % been matched
	varset(RestPDefin,FreeParams),
	bind_to_bot(FreeParams).
match_defin([NType|NDefin], PDefin, OrigPDefin):-
        match_with_some_type(PDefin, NType, RestPDefin),
        match_defin(NDefin, RestPDefin, OrigPDefin).

match_with_some_type([PType|PDefin], NType, PDefin):-
        type_match(NType, PType), !.
match_with_some_type([PType|PDefin], NType, [PType|RestPDefin]):-
        match_with_some_type(PDefin, NType, RestPDefin).

%:- use_module(typeslib(typeslib)).

type_match(NType, PType):-
    var(PType),
    approx_as_defined(NType,DefType),
    !,
    PType = DefType.
type_match(NType, PType):- 
    NType == PType,
    !.
type_match(NType, PType):-
   compound_pure_type_term(NType, NComp, Name, Arity),
   compound_pure_type_term(PType, PComp, Name, Arity), % PType is not a variable.
   !,
   compound_type_match(Arity, NComp, PComp).
type_match(_NType, PType):-
%   non_par_rule_type_symbol(NType),
   par_rule_type_symbol(PType), !.
type_match(NType, PType):-
   non_par_rule_type_symbol(NType),
   non_par_rule_type_symbol(PType).


compound_type_match(0, _NComp, _PComp):-!.
compound_type_match(ArgNum, NComp, PComp):-
       ArgNum > 0, 
       arg(ArgNum, NComp, NArg),
       arg(ArgNum, PComp, PArg),
       type_match(NArg, PArg),
       NArgNum is ArgNum - 1,
       compound_type_match(NArgNum, NComp, PComp).

bind_to_bot([]).
bind_to_bot([bot|Ps]):-
	bind_to_bot(Ps).

check_max_depth(_,0,term).
check_max_depth(PType,Depth,NewType) :-
	param_type_symbol_renaming(Def,PType),!,
	Def =.. [NDef,NextType|Rest],
	Depth1 is Depth - 1,
	check_max_depth(NextType,Depth1,NewNextType),
	( NewNextType \= NextType ->
	  NewDef =.. [NDef,NewNextType|Rest],
	  assert_param_type_rule_instance(NewDef, NewType)
	; NewType = PType
	).
check_max_depth(Type,_,Type).


deftypes_contains_parameters([_:T|Subs]) :-
	( contains_type_param(T),!
	; deftypes_contains_parameters(Subs)
	).


% a facility to output the type lattice in the DOT format

:- use_module(engine(stream_basic)).
:- use_module(library(format), [format/3]).

gen_graph :-
	open('type_graph.dot',write,Out),
	gen_gr(Out).

gen_gr(Out) :-
	format(Out,"digraph G {\nordering = out;\n",[]),
	def_subtype_basic(A,B),
	format(Out,"\"~w\" -> \"~w\"\n ",[B,A]),
	fail.
gen_gr(Out) :-
	format(Out,"}\n",[]),
	close(Out).


