:- module(pdb,[],[assertions,regtypes,basicmodes]).

:- doc(title, "PD domain with bottom").
:- doc(module, "This abstract domain is the domain with only two
   values, top and bottom. This simple improvement over the @tt{pd}
   domain provides improvements, both in specialization time and
   quality of the specialized program if abstract specialization is
   then performed. PDB stands for Partial Deduction + Bottom.").

:- use_module(domain(sharefree), [shfr_special_builtin/5]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(pdb, [default]).

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,Proj,Proj,_ExtraInfo).

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,Exit,_ExtraInfo,Exit).

:- dom_impl(_, project/5, [noq]).
project(_,_Vars,_,ASub,ASub).

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort(ASub,ASub).

:- dom_impl(_, glb/3, [noq]).
glb('$bottom',_ASub1,ASub) :- !, ASub = '$bottom'.
glb(_ASub0,'$bottom',ASub) :- !, ASub = '$bottom'.
glb(_,_,top).

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,Call,_Proj,Call,Call).

:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin(_SgKey,_Sg,_Sv,Call,_Proj,Call).

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface(_InputUser,_Qv,top,_Sg,_MaybeCallASub).

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,Call,Call).

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,_Qv,top).

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(_Sg,_Qv,top).

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Hv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,_Hv,_Call,Succ):- 
    Succ = top.

% TODO: optimize for other domains
:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([top|_],Lub) :- !,
    Lub = top.
compute_lub([_|Rest],Lub) :- !,
    compute_lub(Rest,Lub).
compute_lub(_,'$bottom').

% TODO: not connected
pdb_lub('$bottom','$bottom',ALub):-!,
    ALub = '$bottom'.
pdb_lub(_ASub1,_ASub2,top).

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal('$bottom',_).
less_or_equal(top,top).

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :-
    shfr_special_builtin(SgKey,Sg,Subgoal,Type,Condvars), !. % TODO: why?
special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
    very_special_builtin(Key).

very_special_builtin('=/2').
very_special_builtin('\==/2').

:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(bottom,_,_,_,_,'$bottom') :- !.
success_builtin(_unchanged,_,_,_,Lda,Lda).

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
asub_to_native(_Succ,_Qv,_OutFlag,[true],[]).
