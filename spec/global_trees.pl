:- use_module(library(lists), [member/2]).
:- use_module(ciaopp(plai/plai_db), [complete/7, complete_parent/2]).

previous_atom(Key,AbsInt,_Id,OldSg,OldProj,OldId):-
	current_pp_flag(global_trees,off),!,
	current_fact(spec_def_for(Key,OldSg,_NSv,OldProj,AbsInt,OldId,_NF,_A)).
previous_atom(Key,AbsInt,Id,OldSg,OldProj,OldId):-
	global_ancestor(Id,Key,AbsInt,OldId),
	current_fact(spec_def_for(Key,OldSg,_NSv,OldProj,AbsInt,OldId,_NF,_A)).

parent(Id,Key,AbsInt,OldId):-
	current_fact(complete(Key,AbsInt,_,_,_,Id,Fs)),
	member((_,PrevId),Fs),
	spec_wrt(PrevId,AbsInt,OldId).
parent(Id,_Key,AbsInt,OldId):-
	current_fact(complete_parent(Id,[(_,PrevId)])),
	spec_wrt(PrevId,AbsInt,OldId).

global_ancestor(Id,Key,AbsInt,OldId):-
	parent(Id,Key,AbsInt,OldId),
	OldId \== Id.
global_ancestor(Id,Key,AbsInt,OldId):-
	parent(Id,Key,AbsInt,TmpId),
	TmpId \== Id,
	global_ancestor(TmpId,_NKey,AbsInt,OldId),
	OldId \== Id.

