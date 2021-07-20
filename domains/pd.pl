:- module(pd, [], [assertions,regtypes,basicmodes]).

:- doc(title, "PD domain").
:- doc(module, "This abstract domain is the domain with one value,
   top. PD stands for Partial Deduction.").

:- use_module(domain(sharefree), [shfr_special_builtin/5]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(pd, [default]).

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,Proj,Proj,_ExtraInfo).

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,Exit,_ExtraInfo,Exit).

:- dom_impl(_, project/5, [noq]).
project(_,_Vars,_,ASub,ASub).

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub(_ListAsub,top).

%% compute_lub([ASub1,ASub2|Rest],Lub) :-
%%      lub(ASub1,ASub2,ASub3),
%%      compute_lub([ASub3|Rest],Lub).
%% compute_lub([ASub],ASub).
%% 
%% lub('$bottom','$bottom',ALub):-!,
%%      ALub = '$bottom'.
%% lub(_ASub1,_ASub2,top).

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort(ASub,ASub).

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,Prime,_Sv,_Call,Prime).

%% extend('$bottom',_Hv,_Call,Succ):- !,
%%      Succ = '$bottom'.
%% extend(_Prime,_Hv,_Call,Succ):- !,
%%      Succ = top.

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal(_,_).

:- dom_impl(_, glb/3, [noq]).
% TODO: why is '$bottom' handled here? This domain should always return top
glb('$bottom',_ASub1,ASub) :- !, ASub = '$bottom'.
glb(_ASub0,'$bottom',ASub) :- !, ASub = '$bottom'.
glb(_,_,top).

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,Call,_Proj,Call,Call).

:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin(_SgKey,_Sg,_Sv,Call,_Proj,Call).

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface(_InputUser,_Qv,top,_Sg,_MaybeCallASub).

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native(_ASub,_Qv,_OutFlag,[true],[]).

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,Call,Call).

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,_Qv,top).

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(_Sg,_Qv,top).

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :-
    shfr_special_builtin(SgKey,Sg,Subgoal,Type,Condvars), !. % TODO: why?
special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
    very_special_builtin(Key).

very_special_builtin('=/2').
very_special_builtin('\==/2').

:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(_unchanged,_,_,_,Lda,Lda).
