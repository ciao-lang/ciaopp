:- module(ptypes,[],[assertions,regtypes,basicmodes]).

:- doc(title, "ptypes: types with topological class widening (abstract domain)").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").
:- doc(author, "Ciao Development Team").

:- doc(module,"This module implements a types domain (based on
   @tt{termsd.pl}) using the topological clash widening operator
   (@pred{hentenwid/3}).").

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
:- use_module(domain(termsd)).
:- use_module(typeslib(typeslib), [hentenwid/3]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(ptypes).

:- dom_impl(ptypes, init_abstract_domain/1).
:- export(ptypes_init_abstract_domain/1).
ptypes_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

:- dom_impl(ptypes, call_to_entry/9).
:- export(ptypes_call_to_entry/9).
ptypes_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- terms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).

:- dom_impl(ptypes, exit_to_prime/7).
:- export(ptypes_exit_to_prime/7).
ptypes_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- terms_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).

:- dom_impl(ptypes, compute_lub/2).
:- export(ptypes_compute_lub/2).
ptypes_compute_lub(ListASub,LubASub) :- terms_compute_lub(ListASub,LubASub).

:- dom_impl(ptypes, identical_abstract/2).
:- export(ptypes_identical_abstract/2).
ptypes_identical_abstract(ASub1,ASub2) :- terms_identical_abstract(ASub1,ASub2).

:- dom_impl(ptypes, abs_sort/2).
:- export(ptypes_abs_sort/2).
ptypes_abs_sort(ASub,ASub_s) :- terms_abs_sort(ASub,ASub_s).

:- dom_impl(ptypes, extend/5).
:- export(ptypes_extend/5).
ptypes_extend(Sg,Prime,Sv,Call,Succ) :- terms_extend(Sg,Prime,Sv,Call,Succ).

:- dom_impl(ptypes, less_or_equal/2).
:- export(ptypes_less_or_equal/2).
ptypes_less_or_equal(ASub0,ASub1) :- terms_less_or_equal(ASub0,ASub1).

:- dom_impl(ptypes, glb/3).
:- export(ptypes_glb/3).
ptypes_glb(ASub0,ASub1,ASub) :- terms_glb(ASub0,ASub1,ASub).

:- dom_impl(ptypes, call_to_success_fact/9).
:- export(ptypes_call_to_success_fact/9).
ptypes_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- terms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).

:- dom_impl(ptypes, special_builtin/5).
:- export(ptypes_special_builtin/5).
ptypes_special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :- terms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

:- dom_impl(ptypes, success_builtin/6).
:- export(ptypes_success_builtin/6).
ptypes_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ):- terms_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).

:- dom_impl(ptypes, call_to_success_builtin/6).
:- export(ptypes_call_to_success_builtin/6).
ptypes_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ) :- terms_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).

:- dom_impl(ptypes, input_interface/4).
:- export(ptypes_input_interface/4).
ptypes_input_interface(InputUser,Kind,Struct0,Struct1) :- terms_input_interface(InputUser,Kind,Struct0,Struct1).

:- dom_impl(ptypes, input_user_interface/5).
:- export(ptypes_input_user_interface/5).
ptypes_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub) :- terms_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).

:- dom_impl(ptypes, asub_to_native/5).
:- export(ptypes_asub_to_native/5).
ptypes_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps) :- terms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).

:- dom_impl(ptypes, concrete/3).
:- export(ptypes_concrete/3).
ptypes_concrete(Var,ASub,List) :- terms_concrete(Var,ASub,List).

:- dom_impl(ptypes, unknown_call/4).
:- export(ptypes_unknown_call/4).
ptypes_unknown_call(Sg,Vars,Call,Succ) :- terms_unknown_call(Sg,Vars,Call,Succ).

:- dom_impl(ptypes, unknown_entry/3).
:- export(ptypes_unknown_entry/3).
ptypes_unknown_entry(Sg,Qv,Call) :- terms_unknown_entry(Sg,Qv,Call).

:- dom_impl(ptypes, empty_entry/3).
:- export(ptypes_empty_entry/3).
ptypes_empty_entry(Sg,Qv,Call) :- terms_empty_entry(Sg,Qv,Call).

:- dom_impl(ptypes, collect_abstypes_abs/3).
:- export(ptypes_collect_abstypes_abs/3).
ptypes_collect_abstypes_abs(ASub,Types0,Types) :- terms_collect_abstypes_abs(ASub,Types0,Types).

:- dom_impl(ptypes, widencall/3).
:- export(ptypes_widencall/3).
ptypes_widencall(Prime0,Prime1,Result):-
    ( terms_less_or_equal(Prime1,Prime0) ->
        Result = Prime0
    ; terms_compute_lub_el(Prime0,Prime1,Prime),
      henten(Prime0,Prime,Prime2),
      ( terms_identical_abstract(Prime2,Prime) ->
          Result = Prime1
      ; Result = Prime2
      )
    ).

:- dom_impl(ptypes, needs/1).
:- export(ptypes_needs/1).
ptypes_needs(X) :-
    terms_needs(X).

:- dom_impl(ptypes, widen/3).
:- export(ptypes_widen/3).
ptypes_widen(Prime0,Prime1,NewPrime):-
    terms_compute_lub_el(Prime0,Prime1,Prime),
    henten(Prime0,Prime,NewPrime).

henten('$bottom','$bottom','$bottom') :- !.
henten('$bottom',Prime,Prime).
henten([],[],[]).
henten([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
    hentenwid(T1,T2,T),
    henten(Prime0,Prime,NewPrime).

% :- dom_impl(ptypes, rename_abstypes_abs/3). % TODO: missing, why?
