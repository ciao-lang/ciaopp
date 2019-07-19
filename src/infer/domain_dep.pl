
do_compute_lub(AbsInt,SubstList,Subst):-
	( AbsInt = fr ; AbsInt = fd ), !,
	compute_lub_general(AbsInt,SubstList,Subst).
do_compute_lub(AbsInt,SubstList,Subst):-
	there_is_delay, !,
	del_compute_lub(SubstList,AbsInt,Subst).
do_compute_lub(AbsInt,SubstList,Subst):-
	compute_lub_(AbsInt,SubstList,Subst).

compute_lub_(_AbsInt,[],'$bottom'):- !.
compute_lub_(AbsInt,SubstList,Subst):-
	compute_lub(AbsInt,SubstList,Subst).

join_if_needed(fd,Proj,Prime,Sv,Join):- !,
	fd_extend(Prime,Sv,Proj,Join).
join_if_needed(fr,Proj,Prime,Sv,Join):- !,
	fr_extend(Prime,Sv,Proj,Join).
join_if_needed(_,_,Prime,_,Prime).

free_vars_in_asub(depth,Vars,Info,FVars):- !,
	varset(Info,AllVars),
	ord_subtract(AllVars,Vars,FVars).
free_vars_in_asub(sha,Vars,Info,FVars):- !,
	varset(Info,AllVars),
	ord_subtract(AllVars,Vars,FVars).
free_vars_in_asub(_AbsInt,_Vars,_Info,[]).
