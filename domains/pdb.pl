:- module(pdb,[
%% 	pdb_call_to_entry/8,
%% 	pdb_exit_to_prime/7,
%% 	pdb_project/3,
 	pdb_extend/4,
 	pdb_compute_lub/2,
%% 	pdb_glb/3,
 	pdb_less_or_equal/2,
%% 	%pdb_compute_lub_el/3,
%% 	%pdb_extend_free/3,
%% 	pdb_sort/2,
	%% 	pdb_call_to_success_fact/8,
	pdb_special_builtin/4,
 	pdb_success_builtin/5,
%% 	pdb_call_to_success_builtin/6,
%% 	pdb_input_interface/4,
%% 	pdb_input_user_interface/3,
 	pdb_asub_to_native/3
%% 	%pdb_output_interface/2,
%% 	pdb_unknown_call/3,
%% 	pdb_unknown_entry/2,
%% 	pdb_empty_entry/2
	     ],
	     [assertions,regtypes,basicmodes
	     ]).

:- doc(module, "This abstract domain is the domain with only two
   values, top and bottom. This simple improvement over the @tt{pd}
   domain provides improvements, both in specialization time and
   quality of the specialized program if abstract specialization is
   then performed. PDB stands for Partial Deduction + Bottom.").

:- use_module(domain(share), 
	[ shfr_special_builtin/4 ]).

pdb_extend('$bottom',_Hv,_Call,Succ):- !,
	Succ = '$bottom'.
pdb_extend(_Prime,_Hv,_Call,Succ):- 
	Succ = top.

pdb_compute_lub([ASub1,ASub2|Rest],Lub) :-
	pdb_lub(ASub1,ASub2,ASub3),
	pdb_compute_lub([ASub3|Rest],Lub).
pdb_compute_lub([ASub],ASub).

pdb_lub('$bottom','$bottom',ALub):-!,
	ALub = '$bottom'.
pdb_lub(_ASub1,_ASub2,top).

pdb_less_or_equal('$bottom',_).
pdb_less_or_equal(top,top).

pdb_special_builtin(A,B,C,D):-
	shfr_special_builtin(A,B,C,D).

pdb_special_builtin(Key,_Sg,special(Key),[]):-
	pdb_very_special_builtin(Key).

pdb_very_special_builtin('=/2').
pdb_very_special_builtin('\==/2').

pdb_success_builtin(_unchanged,_,_,Lda,Lda).

pdb_asub_to_native('$bottom',_Qv,_ASub_user):- !, fail.
pdb_asub_to_native(_Succ,_Qv,[true]).
