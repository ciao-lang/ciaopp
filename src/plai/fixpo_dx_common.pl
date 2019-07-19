:- include(.(fixpo_dx_check_common)).

%------------------------------------------------------------------------
:- pred entry_to_exit(+Body,+Key,+Call,-Exit,+Vars_u,+AbsInt,+NewN)
        : (atm(Key), list(Vars_u), atm(AbsInt)) + not_fails
 #"Traverses the body of a clause (first argument) obtaining the Exit for
   a given Entry (represented by Call, since it is both the Entry of the
   clause and the Call for the first subgoal).".
entry_to_exit((Sg,Rest),K,Call,Exit,Vars_u,AbsInt,NewN):- !,
	debug('.'),
	body_succ(Call,Sg,Succ,Vars_u,AbsInt,K,NewN,_Id),
	entry_to_exit(Rest,K,Succ,Exit,Vars_u,AbsInt,NewN).
entry_to_exit(true,_,Call,Call,_,_,_):- !,
	debug('.').
entry_to_exit(g(_,[],'$built'(_,true,_),'true/0',true),Key,Call,Call,Vars_u,AbsInt,NewN):- !,
 	debug('.'),
 	decide_memo(AbsInt,Key,NewN,no,Vars_u,Call).
entry_to_exit(Sg,Key,Call,Exit,Vars_u,AbsInt,NewN):- 
	debug('.'),
	body_succ(Call,Sg,Exit,Vars_u,AbsInt,Key,NewN,_Id),
	decide_memo(AbsInt,Key,NewN,no,Vars_u,Exit),!.
