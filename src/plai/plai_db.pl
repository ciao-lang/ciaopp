:- module(plai_db,
	[ complete/7, lub_complete/6, 
	  memo_call/5, memo_table/6, memo_lub/5, pragma/5,complete_parent/2,
	 cleanup_plai_db/1],
	[assertions, datafacts,regtypes,isomodes]).

:- use_module(ciaopp(plai/transform), [cleanup_trans_clauses/0]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3, decode_litkey/5,
        predkey/1, litkey/1]). % Props

:- doc(bug,"The cleanup does not work when in debugging mode!!!").

:- doc(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents),
	"The predicate @var{SgKey} has a variant success pattern 
	  @code{(Sg,Proj,Prime)} on the domain @var{AbsInt}. The and-or
	  graph node is @var{Id}, and is called from the program points
	  in list @var{Parents}.").
:- data complete/7.
:- pred complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents)
        => predkey * atm * term * term * list(term) * int * parents_complete.

:- prop parents_complete/1.
parents_complete([]). % only if the complete is temporary
parents_complete([(K,Id)|Ps]) :-
        litkey(K),
        int(Id),
        parents_complete(Ps).

:- data complete_key/3.
% to cache results

:- doc(lub_complete(SgKey,AbsInt,Lub,Sg,Proj,Prime),
	"The predicate @var{SgKey} has in all variants success pattern 
	  @code{(Sg,Proj,Prime)} on the domain @var{AbsInt}. 
          If @var{Lub} is yes, @var{Proj} and @var{Prime} are substitutions, 
	  if @var{Lub} is no, they are lists of substitutions.").
:- data lub_complete/6.

:- doc(memo_table(LitKey,AbsInt,Id,Child,Vars_u,Call),
	"Before calling the goal at program point @var{PointKey}, 
	  there is a variant in which
	  @var{Call} on the domain @var{AbsInt} holds upon the program
	  clause variables @var{Vars_u}. These variables need be sorted
	  conveniently so that @var{Call} makes sense. The and-or graph
	  node that causes this is @var{Id} and the call originated to
	  the goal at this program point generates and-or graph node
	  @var{Child}.").
:- data memo_table/6.
:- pred memo_table(LitKey,AbsInt,Id,Child,Vars_u,Call)
        => litkey * atm * int * int * term * list(term).

:- data memo_call/5.

:- doc(memo_lub(PointKey,AbsInt,Lub,Vars_u,Call),
	"Before calling the goal at program point @var{PointKey}, 
	  in all variants
	  @var{Call} on the domain @var{AbsInt} holds upon the program
	  clause variables @var{Vars_u}. If @var{Lub} is yes, @var{Call}
	  is a substitution, if If @var{Lub} is no, @var{Call}
	  is a list of substitutions.").
:- data memo_lub/5.

:- doc(complete_parent(Id,Parents), "Used to keep the trace of the
	parents in the and-or graph for the di fixpoint. The parents
	are used to choose previous aproximations to apply the
	widening operators on calls The and-or graph node is @var{Id},
	and @var{Parents} is a list of couples of graph node and
	program points.").
:- data complete_parent/2.

%% ?????????????????
:- data pragma/5.

% To annotate when a call (litkey) is invalid because it violates a (trust) call
% assertion
:- export(invalid_call/6). % for dump incanal
:- data invalid_call/6.

:- export(raw_success/6). % for dump incanal
:- data raw_success/6.
% raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime)

:- doc(cleanup_plai_db(AbsInt),"Erases all data in this module for
	the analysis domain @var{AbsInt}.").
cleanup_plai_db(AbsInt):-
	retractall_fact(complete(_,AbsInt,_,_,_,_,_)),
	retractall_fact(lub_complete(_,AbsInt,_,_,_,_)),
	retractall_fact(memo_lub(_,AbsInt,_,_,_)),
	retractall_fact(memo_table(_,AbsInt,_,_,_,_)),
	retractall_fact(memo_call(_,AbsInt,_,_,_)),
	retractall_fact(complete_parent(_,_)),
	retractall_fact(pragma(_,_,_,_,_)),
	retractall_fact(complete_key(_,_,_)),
  retractall_fact(invalid_call(_,AbsInt,_,_,_,_)),
  retractall_fact(raw_success(_,AbsInt,_,_,_,_)),
	cleanup_trans_clauses.

:- export(get_parent_key/4).
% This predicate exists because of the way meta_calls are represented
% differently in the memo_table and the completes
:- pred get_parent_key(LitKey,Id,AbsInt,CKey)
        => litkey * int * atm * predkey
	#"@var{CKey} is the key that corresponds to @var{Id}, it may
      not correspong to the decoding LitKey because of how meta_calls
      are indexed in the fixpoints".
get_parent_key(LitKey,Id,AbsInt,CKey) :-
	decode_litkey(LitKey,F,A,_,_),
	get_predkey(F,A,SgKey),
	( complete(SgKey,AbsInt,_,_,_,Id,_) ->
	    CKey = SgKey
	;
	    ( complete_key(Id,AbsInt,CKey),
	      complete(CKey,AbsInt,_,_,_,Id,_)
	    ->
	        true
	    ;
		( complete(CKey,AbsInt,_,_,_,Id,_) -> true ; fail),
		assertz_fact(complete_key(Id,AbsInt,CKey))
	    )
	), !.

:- export(get_complete/8).
% complete + (!) to avoid unnecessary choicepoints
:- pred get_complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps,Ref)
        : (predkey(SgKey), atm(Id)).
get_complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents,Ref) :-
        current_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents),Ref), !.

:- export(get_memo_table/7).
% complete + (!) to avoid unnecessary choicepoints
:- pred get_memo_table(LitKey,AbsInt,Id,Child,Vars,Call,Ref)
        : (predkey(SgKey), atm(Id)).
get_memo_table(LitKey,AbsInt,Id,Child,Vars,Call,Ref) :-
        current_fact(memo_table(LitKey,AbsInt,Id,Child,Vars,Call), Ref), !.

:- export(add_parent_complete/5).
:- pred add_parent_complete(+SgKey,+AbsInt,+Id,+PId,+LitKey).
add_parent_complete(SgKey,AbsInt,Id,PId,LitKey) :-
        retract_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps)), !, % unique
        merge_parents([(LitKey,PId)],Ps,NPs),
        asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,NPs)).

:- export(del_parent_complete/6).
:- pred del_parent_complete(+SgKey,+AbsInt,+Id,+PId,+LitKey,-NPs).
del_parent_complete(SgKey,AbsInt,Id,PId,LitKey,NPs) :-
        retract_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps)), !, % unique
        del_parent(Ps,LitKey,PId,NPs),
        asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,NPs)).

:- export(patch_parents/6).
:- meta_predicate patch_parents(?,fact,?,?,?,?).
patch_parents(_Ref,_Memo,K,C,_Ps,Fs):-
	member((K,C),Fs), !. % TODO: bad complexity
patch_parents(Ref,Memo,K,C,Ps,Fs):-
	erase(Ref),
	Ps=[(K,C)|Fs],
	asserta_fact(Memo).

:- export(merge_parents/3).
merge_parents([],Ps2,Ps2).
merge_parents([P|Ps1],Ps2,Ps3) :-
        member(P,Ps2), !, % TODO: bad complexity, 
        merge_parents(Ps1,Ps2,Ps3).
merge_parents([P|Ps1],Ps2,[P|Ps3]) :-
        merge_parents(Ps1,Ps2,Ps3).

:- export(del_parent/4).
del_parent([],_,_,[]).
del_parent([(K,C)|Parents],K,C,NParents):-!,
 	del_parent(Parents,K,C,NParents).
del_parent([P|Parents],K,C,[P|NParents]):-
 	del_parent(Parents,K,C,NParents).

% ----------------------------------------------------------------------
:- doc(section, "Operations for invalid calls").

:- export(add_invalid_call/6).
add_invalid_call(SgKey,AbsInt,LitKey,N,Sg,Proj) :-
        invalid_call(SgKey,AbsInt,LitKey,N,Sg,Proj), !.
add_invalid_call(SgKey,AbsInt,LitKey,N,Sg,Proj) :-
        assertz_fact(invalid_call(SgKey,AbsInt,LitKey,N,Sg,Proj)).

% TODO: retract this when a complete is removed!!
:- export(store_raw_success/6).
store_raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime) :-
        ( retract_fact(raw_success(ClKey,AbsInt,Id,_,_,_)) -> true ; true ),
          % Id is unique
          assertz_fact(raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime)).

:- export(get_raw_success/6).
:- pred get_raw_success(+ClKey,+AbsInt,+Id,Sg,Proj,Prime).
get_raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime) :-
        raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime), !.

:- doc(section, "Types").

:- export(plai_db_id/1).
:- regtype plai_db_id/1.
plai_db_id(no).
plai_db_id(X) :-
        int(X).
