:- module(pd,[
%% 	pd_call_to_entry/8,
%% 	pd_exit_to_prime/7,
%% 	pd_project/3,
%% 	pd_extend/4,
%% 	pd_compute_lub/2,
%% 	pd_glb/3,
%% 	pd_less_or_equal/2,
%% 	%pd_compute_lub_el/3,
%% 	%pd_extend_free/3,
%% 	pd_sort/2,
	%% 	pd_call_to_success_fact/8,
	pd_special_builtin/4,
 	pd_success_builtin/5
%% 	pd_call_to_success_builtin/6,
%% 	pd_input_interface/4,
%% 	pd_input_user_interface/3,
%% 	pd_asub_to_native/3,
%% 	%pd_output_interface/2,
%% 	pd_unknown_call/3,
%% 	pd_unknown_entry/2,
%% 	pd_empty_entry/2
	     ],
	     [assertions,regtypes,basicmodes
	     ]).

:- use_module(domain(share), 
	[ shfr_special_builtin/4 ]).

%% pd_extend('$bottom',_Hv,_Call,Succ):- !,
%% 	Succ = '$bottom'.
%% pd_extend(_Prime,_Hv,_Call,Succ):- !,
%% 	Succ = top.
%% 
%% pd_compute_lub([ASub1,ASub2|Rest],Lub) :-
%% 	pd_lub(ASub1,ASub2,ASub3),
%% 	pd_compute_lub([ASub3|Rest],Lub).
%% pd_compute_lub([ASub],ASub).
%% 
%% pd_lub('$bottom','$bottom',ALub):-!,
%% 	ALub = '$bottom'.
%% pd_lub(_ASub1,_ASub2,top).

pd_special_builtin(A,B,C,D):-
	shfr_special_builtin(A,B,C,D).

pd_special_builtin(Key,_Sg,special(Key),[]):-
	pd_very_special_builtin(Key).

pd_very_special_builtin('=/2').
pd_very_special_builtin('\==/2').

pd_success_builtin(_unchanged,_,_,Lda,Lda).
