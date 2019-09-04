:- module(pd, [], [assertions,regtypes,basicmodes]).

:- doc(module, "This abstract domain is the domain with one value,
   top. PD stands for Partial Deduction.").

:- use_module(domain(share), [shfr_special_builtin/4]).

:- export(pd_call_to_entry/9).
pd_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,Proj,Proj,_ExtraInfo).

:- export(pd_exit_to_prime/7).
pd_exit_to_prime(_Sg,_Hv,_Head,_Sv,Exit,_ExtraInfo,Exit).

:- export(pd_project/5).
pd_project(_,_Vars,_,ASub,ASub).

:- export(pd_compute_lub/2).
pd_compute_lub(_ListAsub,top).

:- export(pd_sort/2).
pd_sort(ASub,ASub).

:- export(pd_extend/5).
pd_extend(_Sg,Prime,_Sv,_Call,Prime).

%% pd_extend('$bottom',_Hv,_Call,Succ):- !,
%% 	Succ = '$bottom'.
%% pd_extend(_Prime,_Hv,_Call,Succ):- !,
%% 	Succ = top.

:- export(pd_less_or_equal/2).
pd_less_or_equal(_,_).

:- export(pd_glb/3).
pd_glb('$bottom',_ASub1,ASub) :- !, ASub = '$bottom'.
pd_glb(_ASub0,'$bottom',ASub) :- !, ASub = '$bottom'.
pd_glb(_,_,top).

:- export(pd_call_to_success_fact/9).
pd_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,Call,_Proj,Call,Call).

:- export(pd_call_to_success_builtin/6).
pd_call_to_success_builtin(_SgKey,_Sg,_Sv,Call,_Proj,Call).

:- export(pd_input_user_interface/5).
pd_input_user_interface(_InputUser,_Qv,top,_Sg,_MaybeCallASub).

:- export(pd_asub_to_native/5).
pd_asub_to_native(_ASub,_Qv,_OutFlag,[true],[]).

:- export(pd_unknown_call/4).
pd_unknown_call(_Sg,_Vars,Call,Call).

:- export(pd_unknown_entry/3).
pd_unknown_entry(_Sg,_Qv,'top').

:- export(pd_empty_entry/3).
pd_empty_entry(_Sg,_Qv,'top').

%% 
%% pd_compute_lub([ASub1,ASub2|Rest],Lub) :-
%% 	pd_lub(ASub1,ASub2,ASub3),
%% 	pd_compute_lub([ASub3|Rest],Lub).
%% pd_compute_lub([ASub],ASub).
%% 
%% pd_lub('$bottom','$bottom',ALub):-!,
%% 	ALub = '$bottom'.
%% pd_lub(_ASub1,_ASub2,top).

:- export(pd_special_builtin/5).
pd_special_builtin(SgKey,Sg,_Subgoal,Type,Condvars) :-
	shfr_special_builtin(SgKey,Sg,Type,Condvars), !. % TODO: why?
pd_special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
	pd_very_special_builtin(Key).

pd_very_special_builtin('=/2').
pd_very_special_builtin('\==/2').

:- export(pd_success_builtin/6).
pd_success_builtin(_unchanged,_,_,_,Lda,Lda).
