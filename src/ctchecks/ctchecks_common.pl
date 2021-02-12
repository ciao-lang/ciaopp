:- module(ctchecks_common,
    [
        abs_execute/7,
        pp_abs_execute_with_info/5,
        get_info/4
    ],
    [assertions, regtypes]).

:- use_module(library(messages), [error_message/3]).
:- use_module(library(formulae), [list_to_conj/2, conj_to_list/2]).

:- use_module(ciaopp(infer),       [get_memo_lub/5]).
:- use_module(ciaopp(infer/infer_dom),   [abs_execute_with_info/4]).
:- use_module(spec(abs_exec_ops), [adapt_info_to_assrt_head/6]).
:- use_module(ciaopp(plai/domains),      [abs_sort/3]).

abs_execute(none, _Head, Calls, _Goal, _Vars, _Info , Calls) :- !.
abs_execute(Domain, Head, Calls, Goal, Vars, Info, NCalls) :-
    list(Calls), !,
%       PP: seems to peel off prefixes from native types, making them 
%       not working in abs_execute/4, and nothing more. Commented out
%       to_native_props(Calls, NativeCalls),   
    Calls = NativeCalls,
    list_to_conj(NativeCalls, ConjNativeCalls),
    adapt_info_to_assrt_head(Domain, Goal, Vars, Info, Head, NewInfo),
    pp_abs_execute_with_info(ConjNativeCalls,Domain,Head,NewInfo,NCalls).
abs_execute(Domain, Head, Calls, Goal, Vars, Info, NCalls) :-
    adapt_info_to_assrt_head(Domain, Goal, Vars, Info, Head, NewInfo),
    abs_sort(Domain, NewInfo, NewInfo_o),
    pp_abs_execute_with_info(Calls,Domain,Head, NewInfo_o, NCalls).

pp_abs_execute_with_info(ExpL, AbsInt,Goal,Info,NewExp):-
    ExpL = [_|_],!,
    list_to_conj(ExpL, Exp),
    pp_abs_execute_with_info(Exp, AbsInt,Goal,Info,NewExp).
pp_abs_execute_with_info((Exp1,Exp2), AbsInt,Goal,Info,NewExp):-
    !,
    pp_abs_execute_with_info(Exp1,AbsInt,Goal,Info,NewExp1),
    ( NewExp1 == fail ->
        NewExp = fail
    ;
        pp_abs_execute_with_info(Exp2,AbsInt,Goal,Info,NewExp2),
        compose_conj(NewExp1,NewExp2,NewExp)
   ).
pp_abs_execute_with_info((Exp1L;Exp2L), AbsInt,Goal,Info,NewExp):-
    !,
%       list_to_conj(Exp1L, Exp1),
    pp_abs_execute_with_info(Exp1L,AbsInt,Goal,Info,NewExp1),
    ( NewExp1 == true ->
        NewExp = true
    ;
%           list_to_conj(Exp2L,Exp2),
        pp_abs_execute_with_info(Exp2L,AbsInt,Goal,Info,NewExp2),
        synt_compose_disj(NewExp1,NewExp2,NewExp)
   ).
pp_abs_execute_with_info(Prop, AbsInt, _Goal,Info, E) :-   
    abs_execute_with_info(AbsInt, Info, Prop, E),
    !.
pp_abs_execute_with_info(Prop,_AbsInt,_Goal,_Info,Prop) :-
    error_message(error, "INTERNAL ERROR: pp_abs_execute_with_info: " ||
                          "cannot execute abs: ~w", [Prop]).

compose_conj(true , Exp2, Exp2) :- !.
compose_conj(Exp1 , true, Exp1) :- !.
compose_conj(_Exp1, fail, fail) :- !.
compose_conj(Exp1 , Exp2, (Exp1,Exp2)).

synt_compose_disj(fail, Exp2, Exp2) :- !.
synt_compose_disj(_Exp, true, true) :- !.
synt_compose_disj(Exp1, fail, Exp1) :- !.
synt_compose_disj(Exp1, Exp2, (Exp1L;Exp2L)) :-
    conj_to_list(Exp1, Exp1L),
    conj_to_list(Exp2, Exp2L).

%% :- use_module(library(format)).
get_info(none, _K, _Vars, none) :- !.
get_info(_, unkown_id, _Vars, none) :- !.
get_info(Types, K, Vars, TypesInfo) :-
%       format("Key: ~w   Vars: ~w  Types: ~w", [K,Vars,Types]),
    get_memo_lub(K,Vars,Types,yes,TypesInfo),
    !.
%       format("  TypesInfo: ~w~n", [TypesInfo]).
get_info(_,_,_Vars,([],[])).
%       format("  TypesInfo (forced): ~w~n", [ ([],[]) ]).

% %  PP: Probably not needed any more

% to_native_props([], []).
% to_native_props([A|As], [B|Bs]) :-
%       my_native_prop(A, B),
%       to_native_props(As, Bs).

% my_native_prop(I, O2) :-
%       prop_to_native(I, O),
% %     (current_itf(visible,I,_), ! ;
% %         current_itf(visible,O,_) 
% %    ),
%       (O = regtype(O2) -> true ; O = O2),
%       !.

% my_native_prop(I, I).
