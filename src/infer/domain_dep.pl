%% %% VD general version of lub used for printing the output
%% :- export(compute_lub_general/3).
%% compute_lub_general(frdef,ListASub,LubASub) :- !, frdef_compute_lub_general(ListASub,LubASub).
%% compute_lub_general(def,ListASub,LubASub) :- !, def_compute_lub(ListASub,LubASub).
%% compute_lub_general(aeq,ListASub,LubASub) :- !, aeq_compute_lub(ListASub,LubASub).
%%
%% frdef_compute_lub_general(ListASub,ListASub).
%%
%% :- export(do_compute_lub/3).

%% do_compute_lub(AbsInt,SubstList,Subst) :- AbsInt = frdef, !, compute_lub_general(AbsInt,SubstList,Subst).

%:- compilation_fact(dummy_lub_uas).

:- if(defined(dummy_lub_uas)).
do_compute_lub(AbsInt,SubstList,Subst):-
    ( AbsInt = fr ; AbsInt = frdef ), !,
    % TODO: compute_lub_general not available here! see CiaoPP 0.7 
    compute_lub_general(AbsInt,SubstList,Subst).
:- endif.
do_compute_lub(AbsInt,SubstList,Subst):-
    there_is_delay, !,
    del_compute_lub(SubstList,AbsInt,Subst).
do_compute_lub(AbsInt,SubstList,Subst):-
    compute_lub_(AbsInt,SubstList,Subst).

:- if(defined(dummy_lub_uas)).
compute_lub_general(_,_,_). % TODO: simplify? remove? (was in pool.pl)
fake_frdef_extend(_,_,_,_). % TODO: simplify? remove? (was in pool.pl)
fake_fr_extend(_,_,_,_). % TODO: simplify? remove? (was in pool.pl)
:- endif.

compute_lub_(_AbsInt,[],'$bottom'):- !.
compute_lub_(AbsInt,SubstList,Subst):-
    compute_lub(AbsInt,SubstList,Subst).

:- if(defined(dummy_lub_uas)).
join_if_needed(frdef,Proj,Prime,_Sg,Sv,Join):- !,
    % TODO: use fd_extend here! see CiaoPP 0.7 
    fake_frdef_extend(Prime,Sv,Proj,Join).
join_if_needed(fr,Proj,Prime,_Sg,Sv,Join):- !,
    % TODO: use fr_extend here! see CiaoPP 0.7 
    fake_fr_extend(Prime,Sv,Proj,Join).
:- endif.
join_if_needed(_,_,Prime,_,_,Prime).

free_vars_in_asub(depthk,Vars,Info,FVars):- !,
    varset(Info,AllVars),
    ord_subtract(AllVars,Vars,FVars).
free_vars_in_asub(sha,Vars,Info,FVars):- !,
    varset(Info,AllVars),
    ord_subtract(AllVars,Vars,FVars).
free_vars_in_asub(_AbsInt,_Vars,_Info,[]).
