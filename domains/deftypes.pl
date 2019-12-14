:- module(deftypes, [], [assertions,regtypes,basicmodes,datafacts]).

:- doc(title,"Defined Types Abstract Domain (based on termsd.pl)").
:- doc(author, "Pawel Pietrzak").

:- doc(module,"This module implements the abstract operations in the
   flavour of other CiaoPP type domains, with the difference that only
   library types, user-defined types and instances of parametric rules
   are in the domain.  An abstract sustitution is list of Var:Type
   elements, where Var is a variable and Type is a pure type term
   @cite{Dart-Zobel}.").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(deftypes).
:- dom_impl(deftypes, init_abstract_domain/1).
:- dom_impl(deftypes, call_to_entry/9).
:- dom_impl(deftypes, exit_to_prime/7).
:- dom_impl(deftypes, project/5).
:- dom_impl(deftypes, widencall/3).
:- dom_impl(deftypes, widen/3).
:- dom_impl(deftypes, compute_lub/2).
:- dom_impl(deftypes, identical_abstract/2).
:- dom_impl(deftypes, abs_sort/2).
:- dom_impl(deftypes, extend/5).
:- dom_impl(deftypes, less_or_equal/2).
:- dom_impl(deftypes, glb/3).
:- dom_impl(deftypes, call_to_success_fact/9).
:- dom_impl(deftypes, special_builtin/5).
:- dom_impl(deftypes, success_builtin/6).
:- dom_impl(deftypes, call_to_success_builtin/6).
:- dom_impl(deftypes, input_interface/4).
:- dom_impl(deftypes, input_user_interface/5).
:- dom_impl(deftypes, asub_to_native/5).
:- dom_impl(deftypes, concrete/3).
:- dom_impl(deftypes, unknown_call/4).
:- dom_impl(deftypes, unknown_entry/3).
:- dom_impl(deftypes, empty_entry/3).
:- dom_impl(deftypes, collect_abstypes_abs/3).
:- dom_impl(deftypes, rename_abstypes_abs/3).
:- dom_impl(deftypes, contains_parameters/1).

% ---------------------------------------------------------------------------

:- use_module(domain(termsd), [
    substitution/3,
    variables_are_top_type/2,
    terms_special_builtin/5,
    terms_success_builtin/6,
    terms_concrete/3,
    terms_unknown_call/4]).
:- use_module(domain(termsd), [recorda_required_types/2]).

:- use_module(ciaopp(p_unit), [new_internal_predicate/3]).

:- use_module(typeslib(typeslib_deftypes)).
% type operations from Pedro's library
:- use_module(typeslib(typeslib), 
    [
        param_type_symbol_renaming/2,
        assert_param_type_instance/2,
        internally_defined_type_symbol/2,
        compound_pure_type_term/4,
        equiv_types/2,
        insert_rule/2,
        new_type_symbol/1,
        set_top_type/1,
        type_escape_term_list/2,
        type_intersection_2/3,
        type_symbol/1,
        equivalent_to_top_type/1,
        get_compatible_types/4,
        belongs_to_type/2,
        contains_type_param/1,
        pure_type_term/1
    ]).
:- use_module(typeslib(type_support), [ins_without_dup/2, find_list_entry/3]).

:- use_module(library(lists), [append/3, member/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3, ord_member/2, insert/3]).
:- use_module(library(sort), [sort/2]).

% ---------------------------------------------------------------------------

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

% ---------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
deftypes_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

%% ---------------------------------------------------------------------------

:- use_module(domain(termsd), [
    precondition_builtin/2,
    postcondition_builtin/4]).

:- export(deftypes_call_to_success_builtin/6).
deftypes_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
    deftypes_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?

deftypes_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    ( precondition_builtin(Key,Sg) ->
        postcondition_builtin(Key,Bg,Bv,Exit),
        deftypes_exit_to_prime(Sg,Bv,Bg,Sv,Exit,no,Prime1),
        deftypes_glb(Proj,Prime1,Prime),
        deftypes_extend(Sg,Prime,Sv,Call,Succ)
    ;
        Succ = '$bottom'
    ).

:- export(deftypes_input_interface/4).
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

:- export(deftypes_special_builtin/5).
deftypes_special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :-
    terms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

:- export(deftypes_success_builtin/6).
deftypes_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ):-
    terms_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).

:- export(deftypes_concrete/3).
deftypes_concrete(Var,ASub,List) :-
    terms_concrete(Var,ASub,List).

:- export(deftypes_unknown_call/4).
deftypes_unknown_call(Sg,Vars,Call,Succ) :-
    terms_unknown_call(Sg,Vars,Call,Succ).

%------------------------------------------------------------------%
:- export(deftypes_compute_lub/2).
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
%       type_union(T1,T2,T3,[]),
    types_lub(T1,T2,T3),
    deftypes_lub0(ASub1,ASub2,ASub3).
deftypes_lub0([],[],[]).

% ---------------------------------------------------------------------------
% Widening

% normalize_type_asub(Prime,Prime). % needed for plai framework

:- export(deftypes_widencall/3).
deftypes_widencall(_Prime0,Prime1,Prime1).
%deftypes_widencall(Prime0,Prime1,NewPrime):-
%       deftypes_widen(Prime0,Prime1,NewPrime).
%       display(terms_widencall),nl,
%       terms_compute_lub_el(Prime0,Prime1,Prime),
%       shortening(Prime,NewPrime).

:- export(deftypes_widen/3).
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
:- export(deftypes_call_to_entry/9).
:- pred deftypes_call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo): 
   term * callable * list * callable * term * list * absu * absu * extrainfo # 
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

deftypes_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
    variant(Sg,Head), !,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    deftypes_abs_sort(NewProj_u,NewProj),
    variables_are_variable_type(Fv,Free),
    merge(Free,NewProj,Entry).
deftypes_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,dummy):-
    unify_term_and_type_term(Head,Hv,Sg,Proj,TmpEntry), !,
    variables_are_variable_type(Fv,Tmp),
    merge(Tmp,TmpEntry,Entry).
deftypes_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- regtype extrainfo/1.

extrainfo(yes).
extrainfo(no).

:- pred variables_are_variable_type(+Fv,-ASub): list * absu # 
"at the moment it assigns the value top_type to the variables in @var{Fv}
 but in the future it must assign the value ``var''".

variables_are_variable_type(Fv,ASub):-
    variables_are_top_type(Fv,ASub).

%------------------------------------------------------------------%
:- export(deftypes_exit_to_prime/7).
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
    deftypes_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    deftypes_abs_sort(NewPrime,Prime). 
deftypes_exit_to_prime(Sg,Hv,Head,Sv,Exit,_ExtraInfo,Prime):- 
    deftypes_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
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
        deftypes_abs_sort(TypeAss,ASub1),
        deftypes_project(not_provided_Sg,Tv,not_provided_HvFv_u,ASub1,NASub),
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
%       remove_rule(NType0).

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
:- export(deftypes_project/5).
:- pred deftypes_project(+Sg,+Vars,+HvFv_u,+Asub,-Proj): term * list * list * absu * absu # 
"@var{Proj} is the result of eliminating from @var{Asub} all
@var{X}:@var{Value} such that @var{X} is not in @var{Vars}".

deftypes_project(_,_,_,'$bottom',Proj):- !,
    Proj = '$bottom'.
deftypes_project(_Sg,Vars,_HvFv_u,ASub,Proj) :- 
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
:- export(deftypes_abs_sort/2).
:- pred deftypes_abs_sort(+Asub,-Asub_s): absu * absu
# 
"It sorts the set of @var{X}:@var{Type} in @var{Asub} ontaining @var{Asub_s}".

deftypes_abs_sort('$bottom','$bottom'):- !.
deftypes_abs_sort(ASub,ASub_s):- sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- export(deftypes_extend/5).
:- pred deftypes_extend(+Sg,+Prime,+Sv,+Call,-Succ): term * absu * list * absu * absu # 
"
If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
 @var{Succ} is computed updating the values of @var{Call} with those
 in @var{Prime}".

deftypes_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
deftypes_extend(_Sg,Prime,Sv,Call,Succ):-
    subtract_keys(Call,Sv,RestCall),
    merge(RestCall,Prime,Succ).

subtract_keys([K:_|Xs],Ks,Dict):-
    ord_member(K,Ks), !,
    subtract_keys(Xs,Ks,Dict).
subtract_keys([X|Xs],Ks,[X|Dict]):-
    subtract_keys(Xs,Ks,Dict).
subtract_keys([],_Ks,[]).

%------------------------------------------------------------------%
:- export(deftypes_less_or_equal/2).
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
%       dz_type_included(T1,T2),
    def_subtype(T1,T2),
    deftypes_less_or_equal0(ASub1,ASub2).
deftypes_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- export(deftypes_glb/3).
:- pred deftypes_glb(+ASub0,+ASub1,-Glb): absu * absu * absu # 
"@var{Glb} is the great lower bound of @var{ASub0} and @var{ASub1}".

deftypes_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
deftypes_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
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
:- export(deftypes_unknown_entry/3).
:- pred deftypes_unknown_entry(+Sg,+Qv,-Call): callable * list * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to   
 Call. In this domain the top value is X:term forall X in the set of variables".

% deftypes_unknown_entry(Sg,Qv,Call) :- terms_unknown_entry(Sg,Qv,Call).
deftypes_unknown_entry(_Sg,Vars,ASub):-
    variables_are_top_type(Vars,ASub).

:- export(deftypes_empty_entry/3).
:- pred deftypes_empty_entry(+Sg,+Vars,-Entry): callable * list * absu # "Gives the
\"empty\" value in this domain for a given set of variables
@var{Vars}, resulting in the abstract substitution @var{Entry}. I.e.,
obtains the abstraction of a substitution in which all variables
@var{Vars} are unbound: free and unaliased. In this domain the empty
value is giving the variable type to each variable".

% deftypes_empty_entry(Sg,Qv,Call) :- terms_empty_entry(Sg,Qv,Call).
deftypes_empty_entry(_Sg,Vars,ASub):-
    variables_are_variable_type(Vars,ASub).

%------------------------------------------------------------------%
:- export(deftypes_call_to_success_fact/9).
:- pred deftypes_call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ): callable * 
list * callable * term * list * absu * absu * absu * absu # 
"Specialized version of call_to_entry + exit_to_prime + extend for facts".

deftypes_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    deftypes_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
    deftypes_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
    deftypes_extend(Sg,Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%
%                           USER INTERFACE
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% deftypes_input_user_interface(+InputUser,+Qv,-ASub,+Sg,+MaybeCallASub) %
% Obtains the abstract substitution ASub from user supplied information. %
%------------------------------------------------------------------------%

:- export(deftypes_input_user_interface/5).
deftypes_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
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
%       type_intersection_2(TY,TX,T),
    types_glb(TY,TX,T),
    reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var__(Y,TY,X,TX,ASub,[X:TX|NewASub]):-
    reduce_same_var_(ASub,Y,TY,NewASub).

% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
%       Type=..[T,X],
%       inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).

%------------------------------------------------------------------------%
% deftypes_asub_to_native(+ASub,+Qv,+Flag,-OutputUser,-Comps)            %
% Transforms abstract substitution ASub to user friendly format.         %
%------------------------------------------------------------------------%

:- export(deftypes_asub_to_native/5).
deftypes_asub_to_native(ASub,_Qv,Flag,OutputUser,[]):-
    deftypes_asub_to_native0(ASub,OutputUser1),
    equiv_types(OutputUser1,OutputUser2), % TODO: use def_equiv_types? (JFMC)
    revert_types(OutputUser2,OutputUser,Symbols,[]),
    recorda_required_types(Flag,Symbols).

deftypes_asub_to_native0([X:T|ASub],[Type|OutputUser]):-
    revert_type(T,X,Type),
    deftypes_asub_to_native0(ASub,OutputUser).
deftypes_asub_to_native0([],[]).

revert_type(T,X,Type):-
    type_symbol(T), !,
    functor(Type,T,1),
    arg(1,Type,X).
%       Type=..[T,X].
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

%------------------------------------------------------------------------%

:- use_module(library(assoc), [get_assoc/3]).

:- export(deftypes_collect_abstypes_abs/3).
deftypes_collect_abstypes_abs([],Types,Types).
deftypes_collect_abstypes_abs([_:Type|Abs],Types0,Types):-
    insert(Types0,Type,Types1),
    deftypes_collect_abstypes_abs(Abs,Types1,Types).

:- export(deftypes_rename_abstypes_abs/3).
% TODO: duplicated
% deftypes_rename_abstypes_abs(ASub,Dict,RenASub) :- terms_rename_abstypes_abs(ASub,Dict,RenASub).
deftypes_rename_abstypes_abs([],_,[]).
deftypes_rename_abstypes_abs([C|Call],Dict,[RenC|RenCall]):-
    Dict = (Types,_),
    C = Var:Type,
    RenC = Var:RenType,
    get_value_(Types,Type,RenType),
%       new_type_name(RenName),
%       insert_type_name(RenName,[],0),
    deftypes_rename_abstypes_abs(Call,Dict,RenCall).

get_value_(Rens,Type,RenType):-
    assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%

:- export(deftypes_identical_abstract/2).
deftypes_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
deftypes_identical_abstract(ASub1,ASub2):-
    deftypes_identical_abstract0(ASub1,ASub2).

deftypes_identical_abstract0([X:Type0|ASub0],[Y:Type1|ASub1]):-
    X==Y,
    def_equivalent_types(Type0,Type1),
    deftypes_identical_abstract0(ASub0,ASub1).
deftypes_identical_abstract0([],[]).

% ---------------------------------------------------------------------------

:- export(deftypes_contains_parameters/1).
deftypes_contains_parameters([_:T|Subs]) :-
    ( contains_type_param(T),!
    ; deftypes_contains_parameters(Subs)
    ).

