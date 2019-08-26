:- module(pdb,[],[assertions,regtypes,basicmodes]).

:- doc(module, "This abstract domain is the domain with only two
   values, top and bottom. This simple improvement over the @tt{pd}
   domain provides improvements, both in specialization time and
   quality of the specialized program if abstract specialization is
   then performed. PDB stands for Partial Deduction + Bottom.").

:- use_module(domain(share), [shfr_special_builtin/4]).

:- export(pdb_call_to_entry/9).
pdb_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,Proj,Proj,_ExtraInfo).

:- export(pdb_exit_to_prime/7).
pdb_exit_to_prime(_Sg,_Hv,_Head,_Sv,Exit,_ExtraInfo,Exit).

:- export(pdb_project/5).
pdb_project(_,_Vars,_,ASub,ASub).

:- export(pdb_sort/2).
pdb_sort(ASub,ASub).

:- export(pdb_glb/3).
pdb_glb('$bottom',_ASub1,ASub) :- !, ASub = '$bottom'.
pdb_glb(_ASub0,'$bottom',ASub) :- !, ASub = '$bottom'.
pdb_glb(_,_,top).

:- export(pdb_call_to_success_fact/9).
pdb_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,Call,_Proj,Call,Call).

:- export(pdb_call_to_success_builtin/6).
pdb_call_to_success_builtin(_SgKey,_Sg,_Sv,Call,_Proj,Call).

:- export(pdb_input_user_interface/5).
pdb_input_user_interface(_InputUser,_Qv,top,_Sg,_MaybeCallASub).

:- export(pdb_unknown_call/4).
pdb_unknown_call(_Sg,_Vars,Call,Call).

:- export(pdb_unknown_entry/3).
pdb_unknown_entry(_Sg,_Qv,'top').

:- export(pdb_empty_entry/2).
pdb_empty_entry(_Qv,'top').

:- export(pdb_extend/5).
pdb_extend(_Sg,'$bottom',_Hv,_Call,Succ):- !,
	Succ = '$bottom'.
pdb_extend(_Sg,_Prime,_Hv,_Call,Succ):- 
	Succ = top.

:- export(pdb_compute_lub/2).
pdb_compute_lub([ASub1,ASub2|Rest],Lub) :-
	pdb_lub(ASub1,ASub2,ASub3),
	pdb_compute_lub([ASub3|Rest],Lub).
pdb_compute_lub([ASub],ASub).

pdb_lub('$bottom','$bottom',ALub):-!,
	ALub = '$bottom'.
pdb_lub(_ASub1,_ASub2,top).

:- export(pdb_less_or_equal/2).
pdb_less_or_equal('$bottom',_).
pdb_less_or_equal(top,top).

:- export(pdb_special_builtin/5).
pdb_special_builtin(SgKey,Sg,_Subgoal,Type,Condvars) :-
	shfr_special_builtin(SgKey,Sg,Type,Condvars), !. % TODO: why?
pdb_special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
	pdb_very_special_builtin(Key).

pdb_very_special_builtin('=/2').
pdb_very_special_builtin('\==/2').

:- export(pdb_success_builtin/6).
pdb_success_builtin(_unchanged,_,_,_,Lda,Lda).

:- export(pdb_asub_to_native/5).
pdb_asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
pdb_asub_to_native(_Succ,_Qv,_OutFlag,[true],[]).
