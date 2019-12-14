:- module(ptypes,[],[assertions,regtypes,basicmodes]).

:- doc(title, "Types Abstract Domain").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").

:- doc(module,"This module implements the topological clash widening
   operator for types domain.").

:- use_module(library(lists), [member/2]).
:- use_module(library(sort), [sort/2]).

:- use_module(domain(termsd)).
:- use_module(typeslib(typeslib), [
        compound_pure_type_term/4,
        construct_compound_pure_type_term/2,
        dz_type_included/2,
        em_defined_type_symbol/2,
        insert_rule/2,
        new_type_symbol/1,
        unfold_type_union/3
    ]).

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(ptypes).
:- dom_impl(ptypes, init_abstract_domain/1).
:- dom_impl(ptypes, call_to_entry/9).
:- dom_impl(ptypes, exit_to_prime/7).
:- dom_impl(ptypes, widencall/3).
:- dom_impl(ptypes, widen/3).
:- dom_impl(ptypes, compute_lub/2).
:- dom_impl(ptypes, identical_abstract/2).
:- dom_impl(ptypes, abs_sort/2).
:- dom_impl(ptypes, extend/5).
:- dom_impl(ptypes, less_or_equal/2).
:- dom_impl(ptypes, glb/3).
:- dom_impl(ptypes, call_to_success_fact/9).
:- dom_impl(ptypes, special_builtin/5).
:- dom_impl(ptypes, success_builtin/6).
:- dom_impl(ptypes, call_to_success_builtin/6).
:- dom_impl(ptypes, input_interface/4).
:- dom_impl(ptypes, input_user_interface/5).
:- dom_impl(ptypes, asub_to_native/5).
:- dom_impl(ptypes, concrete/3).
:- dom_impl(ptypes, unknown_call/4).
:- dom_impl(ptypes, unknown_entry/3).
:- dom_impl(ptypes, empty_entry/3).
:- dom_impl(ptypes, collect_abstypes_abs/3).
% :- dom_impl(ptypes, rename_abstypes_abs/3). % TODO: missing, why?

:- export(ptypes_init_abstract_domain/1).
ptypes_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

:- export(ptypes_call_to_entry/9).
ptypes_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- terms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).

:- export(ptypes_exit_to_prime/7).
ptypes_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- terms_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).

:- export(ptypes_compute_lub/2).
ptypes_compute_lub(ListASub,LubASub) :- terms_compute_lub(ListASub,LubASub).

:- export(ptypes_identical_abstract/2).
ptypes_identical_abstract(ASub1,ASub2) :- terms_identical_abstract(ASub1,ASub2).

:- export(ptypes_abs_sort/2).
ptypes_abs_sort(ASub,ASub_s) :- terms_abs_sort(ASub,ASub_s).

:- export(ptypes_extend/5).
ptypes_extend(Sg,Prime,Sv,Call,Succ) :- terms_extend(Sg,Prime,Sv,Call,Succ).

:- export(ptypes_less_or_equal/2).
ptypes_less_or_equal(ASub0,ASub1) :- terms_less_or_equal(ASub0,ASub1).

:- export(ptypes_glb/3).
ptypes_glb(ASub0,ASub1,ASub) :- terms_glb(ASub0,ASub1,ASub).

:- export(ptypes_call_to_success_fact/9).
ptypes_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- terms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).

:- export(ptypes_special_builtin/5).
ptypes_special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :- terms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

:- export(ptypes_success_builtin/6).
ptypes_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ):- terms_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).

:- export(ptypes_call_to_success_builtin/6).
ptypes_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ) :- terms_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).

:- export(ptypes_input_interface/4).
ptypes_input_interface(InputUser,Kind,Struct0,Struct1) :- terms_input_interface(InputUser,Kind,Struct0,Struct1).

:- export(ptypes_input_user_interface/5).
ptypes_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub) :- terms_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).

:- export(ptypes_asub_to_native/5).
ptypes_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps) :- terms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).

:- export(ptypes_concrete/3).
ptypes_concrete(Var,ASub,List) :- terms_concrete(Var,ASub,List).

:- export(ptypes_unknown_call/4).
ptypes_unknown_call(Sg,Vars,Call,Succ) :- terms_unknown_call(Sg,Vars,Call,Succ).

:- export(ptypes_unknown_entry/3).
ptypes_unknown_entry(Sg,Qv,Call) :- terms_unknown_entry(Sg,Qv,Call).

:- export(ptypes_empty_entry/3).
ptypes_empty_entry(Sg,Qv,Call) :- terms_empty_entry(Sg,Qv,Call).

:- export(ptypes_collect_abstypes_abs/3).
ptypes_collect_abstypes_abs(ASub,Types0,Types) :- terms_collect_abstypes_abs(ASub,Types0,Types).

:- export(ptypes_widencall/3).
ptypes_widencall(Prime0,Prime1,Result):-
    (
        terms_less_or_equal(Prime1,Prime0) ->
        Result = Prime0
    ;
        terms_compute_lub_el(Prime0,Prime1,Prime),
        henten(Prime0,Prime,Prime2),
        ( 
            terms_identical_abstract(Prime2,Prime) ->
            Result = Prime1
        ;
            Result = Prime2
        )
    ).

:- export(ptypes_widen/3).
ptypes_widen(Prime0,Prime1,NewPrime):-
    terms_compute_lub_el(Prime0,Prime1,Prime),
    henten(Prime0,Prime,NewPrime).

henten('$bottom','$bottom','$bottom').
henten('$bottom',Prime,Prime).
henten([],[],[]).
henten([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
    hentenwid(T1,T2,T,[],[],no),
    henten(Prime0,Prime,NewPrime).

samepf([],[]).
samepf([T|Def],[T2|Def2]):-
    samefunctor(T,T2),!,
    samepf(Def,Def2).

samefunctor(T,T).
samefunctor(T,T2):-
    compound_pure_type_term(T,_Term,F,A),!,
    compound_pure_type_term(T2,_Term2,F,A).
    
hentenancestor(T2,Seen,NT):-
    member((T,NT),Seen),
    dz_type_included(T2,T).
    
hentendef([],[],[],_,_,_).
hentendef([T1|Def1],[T2|Def],[T|NewDef],Seen,Prev,Flag):-
    hentenwid(T1,T2,T,Seen,Prev,Flag),
    hentendef(Def1,Def,NewDef,Seen,Prev,Flag).

hentenwid_arg(0,_Term1,_Term2,_NewTerm,_Seen,_Prev,_Flag).
hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag):-
    arg(A,Term2,Arg2),
    arg(A,Term1,Arg1),
    hentenwid(Arg1,Arg2,NewArg,Seen,Prev,Flag),     
    arg(A,NewTerm,NewArg),
    A1 is A - 1,
    hentenwid_arg(A1,Term1,Term2,NewTerm,Seen,Prev,Flag).

hentenwid(T1,T2,T,Seen,Prev,Flag):-
    em_defined_type_symbol(T2,Def),!,
    (
        member((T2,T),Seen) -> true
    ;
        (
            (
                em_defined_type_symbol(T1,Def1) ->
                NewPrev = [T1|Prev],
                (
                    (Flag == yes;member(T1,Prev)) ->
                     NewFlag = yes
                ;
                    NewFlag = Flag
                )
            ;
                NewPrev = Prev,
                Def1 = [T1],
                NewFlag = Flag
            ),
            (
                (samepf(Def,Def1),NewFlag = no) ->
                 new_type_symbol(NT),
                 hentendef(Def1,Def,NewDef,[(T2,NT)|Seen],NewPrev,NewFlag),
                 (
                     Def == NewDef ->
                     T = T2
                 ;
                     T = NT,
                     unfold_type_union(T,NewDef,NewDef_u),
                     sort(NewDef_u,NewDef_u_s),
                     insert_rule(T,NewDef_u_s)
                 )
            ;
                (
                    hentenancestor(T2,Seen,T) ->
                    true
                ;
                    T = T2
                )
            )
        )
    ).

hentenwid(T1,T2,T,Seen,Prev,Flag):-
    compound_pure_type_term(T2,Term2,F,A),!,
    compound_pure_type_term(T1,Term1,F,A),
    functor(NewTerm,F,A),
    hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag),
    construct_compound_pure_type_term(NewTerm,T).

hentenwid(_T1,T2,T2,_Seen,_Prev,_Flag). 
