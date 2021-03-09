:- module(plai_db,
    [ complete/7, lub_complete/6, 
      memo_call/5, memo_table/6, memo_lub/5, pragma/5,complete_parent/2,
     cleanup_plai_db/1],
    [assertions, datafacts,regtypes,isomodes,nativeprops]).

:- use_module(ciaopp(plai/transform), [cleanup_trans_clauses/0, trans_clause/3]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3, decode_litkey/5,
    predkey/1, litkey/1]). % Props

:- doc(bug,"The cleanup does not work in debugging mode!!!").

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
    parents in the and-or graph for the dd/di fixpoints. The parents
    are used to choose previous aproximations to apply the
    widening operators on calls The and-or graph node is @var{Id},
    and @var{Parents} is a list of couples of graph node and
    program points.").
:- data complete_parent/2.

%% ?????????????????
:- data pragma/5.

% To annotate when a call (litkey) is invalid because it violates a (trust) call
% assertion
:- export(invalid_call/6). % for incanal assrts
:- data invalid_call/6.

:- export(raw_success/6). % for incanal
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
:- pred get_complete(SgKey,AbsInt,?Sg,?Proj,?Prime,+Id,?Ps,Ref)
    : (predkey(SgKey), atm(AbsInt), plai_db_id(Id)) + is_det.
get_complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents,Ref) :-
    current_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents),Ref), !.

:- export(get_memo_table/7).
% memo_table + (!) to avoid unnecessary choicepoints
:- pred get_memo_table(+LitKey,+AbsInt,+Id,Child,Vars,Call,Ref)
    : (litkey(LitKey), atm(AbsInt), plai_db_id(Id)).
get_memo_table(LitKey,AbsInt,Id,Child,Vars,Call,Ref) :-
    current_fact(memo_table(LitKey,AbsInt,Id,Child,Vars,Call), Ref), !.

:- export(get_raw_success/7).
% raw_success + (!) to avoid unnecessary choicepoints
:- pred get_raw_success(+ClKey,+AbsInt,+Id,Sg,Proj,Prime,Ref)
   : (litkey(ClKey), atm(AbsInt), plai_db_id(Id))
   => (nonvar(Sg), nonvar(Proj), nonvar(Prime), nonvar(Ref)).
get_raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime,Ref) :-
    current_fact(raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime), Ref), !.

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
:- pred patch_parents(+Ref,+Memo,+Key,+Id,?NewFs,+Fs)
   : list(Fs) 
   % => (list(NewFs) ; var(NewFs))  % TODO: mixing regtype and inst
   + not_fails.
patch_parents(_Ref,_Memo,K,C,_NewFs,Fs):- % not unifying NewFs if alredy in the list
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(section, "Modifying completes.").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%% Change the Id of a complete %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TODO: This is a pain...
:- export(update_complete_id/4).
update_complete_id(SgKey,AbsInt,Id,NId) :-
    retract_fact(complete(SgKey, AbsInt, Sg, Proj, Prime, Id, Ps)), !,
    asserta_fact(complete(SgKey, AbsInt, Sg, Proj, Prime, NId, Ps)),
    update_extra_info_complete(Id, NId, AbsInt).
%        retract_fact(complete_id_key_(Id, AbsInt, _)), !, % update indexing
%        assertz_fact(complete_id_key_(NId,AbsInt,SgKey)).

% TODO: this predicate should be in plai_db, there should be some way to plug
% removing auxiliary information that is kept for the completes (e.g., info
% related to assertions, widenings, etc)
update_extra_info_complete(Id, NId, AbsInt) :-
    update_complete_parent(Id,NId),
    ( % failure-driven loop
        memo_table_id_key(Id, AbsInt, MKey), % (for indexing)
        % update all the arcs of the call that depends on that memo_table entry
        retract_fact(memo_table(MKey, AbsInt, Id, Child, Vars, Proj)),
          asserta_fact(memo_table(MKey, AbsInt, Id, Child, Vars, Proj)),
          update_raw_success(MKey,AbsInt,Id,NId),
          fail
    ; true
    ).

update_complete_parent(Id,NId) :-
    retract_fact(complete_parent(Id,F)), !,
    asserta_fact(complete_parent(NId,F)).
update_complete_parent(_,_).

update_raw_success(ClKey, AbsInt, Id,NId) :-
    retract_fact(raw_success(ClKey,AbsInt,Id,A,B,C)), !,
    asserta_fact(raw_success(ClKey,AbsInt,NId,A,B,C)).
update_raw_success(_, _, _,_).

%%%%%%%%%%%%%%%%% Delete a complete %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- export(delete_complete/3).
:- pred delete_complete(+SgKey,+AbsInt,+Id) : atm * atm * plai_db_id
   #"Deletes the information of the complete with @var{Id}. This predicate does
    not delete recursively following its parents.".
delete_complete(SgKey,AbsInt,Id) :-
    retract_fact(complete(SgKey, AbsInt, _, _, _, Id, _)), !,
    remove_extra_info_complete(SgKey,Id,AbsInt).

% TODO: this predicate should be in plai_db, there should be some way to plug
% removing auxiliary information that is kept for the completes (e.g., info
% related to assertions, widenings, etc)
:- export(remove_extra_info_complete/3).
remove_extra_info_complete(PredKey,Id,AbsInt) :-
    remove_complete_parent(Id),
    ( % failure-driven loop
      trans_clause(PredKey, _, clause(_, _, ClKey, _)),
        delete_plai_db_one_clause(PredKey,ClKey,Id,AbsInt),
        fail
    ;   true
    ).

:- export(delete_plai_db_one_clause/4).
:- pred delete_plai_db_one_clause(+PredKey,+ClKey,+Id,+AbsInt)
   : atm * atm * plai_db_id * atm
   #"Removes from plai_db the information relative to the clause @var{ClKey} of
    complete @var{Id} for the domain @var{AbsInt}".
delete_plai_db_one_clause(PredKey,ClKey,Id,AbsInt) :-
    trans_clause(PredKey, _, clause(_, _, ClKey, Body)), !,
    remove_raw_success(ClKey, AbsInt, Id),
    ( get_memo_table(ClKey,AbsInt,Id,no,_,_,_) -> % (**) see below
        erase_previous_memo_tables_and_parents(Body,AbsInt,ClKey,Id),
        erase_previous_memo_lubs(Body,ClKey)
    ;  true ).
% IG: retract also auxiliary completes (Id = no) created from this one
% IG: not necessary, they are not created (see add_complete_builtin in fixpo_ops.pl)
% ( % failure-driven loop
%   current_fact(complete(_BKey,AbsInt,_,_,_,no,Ps), Ref),
%       member((_,Id), Ps), % TODO: performance!
%       erase(Ref),
%       fail
% ; true ),

% (**) this check was added because of '!' being used as key for the
% memo_tables. The problem is that when several clauses have a '!' but one of
% them does not have an analysis, e.g., because it didn't unify with the query,
% if we don't make this check, and the cut is the first literal of a clause, one
% entry of the memo_table will be removed for a clause that has no analysis.
% Later, when the info of the clause where the actual '!' was analyzed is
% attempted to be removed, it fails because it was already removed, and the
% remaining of the clause info is not removed. To this end, we are checking if
% the analysis of a clause was finished by checking if there is a memo_table for
% the last program point of the clause, i.e., the one that has as key, the ClKey

remove_complete_parent(Id) :-
    retract_fact(complete_parent(Id,_)), !.
remove_complete_parent(_).

:- pred remove_raw_success(+ClKey, +AbsInt, +Id) + (not_fails, is_det).
remove_raw_success(ClKey, AbsInt, Id) :-
    retract_fact(raw_success(ClKey,AbsInt,Id,_,_,_)), !.
remove_raw_success(_, _, _).

:- export(complete_key_from_id/3).
complete_key_from_id(Id, AbsInt, Key) :-
    complete_id_key(Id, AbsInt, Key0), % (for indexing)
    % complete(Key, AbsInt, _, _, _, Id, _), % slower (no indexing)
    !,
    Key = Key0.

%--------------------------------------------------------------------------
:- export(erase_previous_memo_tables_and_parents/4).
:- pred erase_previous_memo_tables_and_parents(+Body,+AbsInt,+ClKey,+Id)
    #"We use @var{Body} to erase all the memo_tables and all the pointers in
      the dependency graph that are not longer valid".
erase_previous_memo_tables_and_parents(true,_,_,_):-!. % deprecated
erase_previous_memo_tables_and_parents((G,Goals),AbsInt,ClKey,Id):-
    erase_previous_memo_table_and_parents_one_goal(G,AbsInt,ClKey,Id), !,
    erase_previous_memo_tables_and_parents(Goals,AbsInt,ClKey,Id).
erase_previous_memo_tables_and_parents(G,AbsInt,ClKey,Id):-
    erase_previous_memo_table_and_parents_one_goal(G,AbsInt,ClKey,Id), !,
    erase_last_memo_table(AbsInt,ClKey,Id).
erase_previous_memo_tables_and_parents(_,_,_,_). %nothing had been recorded

erase_previous_memo_table_and_parents_one_goal(g(Key,_,Info,SgKey,Sg),AbsInt,ClKey,Id) :-
    get_memo_table(Key,AbsInt,Id,Son,_,_Info,Ref),
    erase(Ref),
    ( Info = '$meta'(_,LGoals,_) ->
        listbody_to_body(LGoals,MetaGoals),
        erase_previous_memo_tables_and_parents(MetaGoals,AbsInt,ClKey,Id)
    ;   true
    ),
    Goal = (SgKey,Info,Sg),
    erase_previous_parents_info(Son,Goal,AbsInt,Key,Id).

:- export(erase_last_memo_table/3).
:- pred erase_last_memo_table(+AbsInt,+ClKey,+Id) + not_fails.
erase_last_memo_table(AbsInt,ClKey,Id):-
    get_memo_table(ClKey,AbsInt,Id,no,_,_,Ref2), !,
    erase(Ref2).
erase_last_memo_table(_,_,_). %maybe we have not written it yet

:- export(erase_previous_memo_lubs/2).
:- pred erase_previous_memo_lubs(+Body, +ClKey) 
    # "This predicate traverses @var{Body} and removes the existing 
       memo_lubs. When @var{Body} is finished, we also remove the 
       memo-lub for the end of the clause using @var{ClKey}.".
erase_previous_memo_lubs(true,_):- !.
erase_previous_memo_lubs((Goal,Goals),K):-
    Goal = g(_Id, _Vars, _Info, Key, _),
    retract_fact(memo_lub(Key, _, _, _, _)), !,
    erase_previous_memo_lubs(Goals,K).
erase_previous_memo_lubs(Goal,K):-
    Goal = g(_Id, _Vars, _Info, Key, _),
    retract_fact(memo_lub(Key, _, _, _, _)), !,
    erase_last_memo_lub(K).
erase_previous_memo_lubs(_,_). %nothing had been recorded

erase_last_memo_lub(K):-
    retract_fact(memo_lub(K, _, _, _, _)), !.
erase_last_memo_lub(_). %maybe we have not written it yet

%------------------------------------------------------------------------
:- pred erase_previous_parents_info(+Id,+Goal,+AbsInt,+Key,+NewN)
    #"@var{Id} is the node identifier of the complete that has this
    @var{Goal} in its list of parents. If Id is no then nothing needs to be
    done (it is a builtin)".
:- export(erase_previous_parents_info/5).
erase_previous_parents_info(no,_,_,_,_):- !.
% Cut has a no?
erase_previous_parents_info(Id,Goal,AbsInt,Key,NewN):-
    erase_prev_parents(Goal, Key,AbsInt,NewN,Id).

% IG % TODO: UNIFY
% IG % TODO: Goal has now a different shape
erase_prev_parents(('$meta',_,Call),K,AbsInt,NewN,Id):-
    functor(Call,_,1),!,
    arg(1,Call,NGoal),
    erase_prev_parents(NGoal,K,AbsInt,NewN,Id).
erase_prev_parents(('$meta',_,Call),K,AbsInt,NewN,Id):-
    functor(Call,_,3),!,
    arg(2,Call,NGoal),
    erase_prev_parents(NGoal,K,AbsInt,NewN,Id).
erase_prev_parents((GKey,_,_),K,AbsInt,NewN,Id):- !, % TODO: old notation
    erase_prev_parents(GKey,K,AbsInt,NewN,Id).
erase_prev_parents(GKey,K,AbsInt,NewN,Id):-
    atom(GKey),
    current_fact(complete(GKey,AbsInt,A1,A2,A3,Id,Parents),Ref),!,
    % TODO: possibly more retracts of complete_parent are needed
    ( retract_fact(complete_parent(Id,K)) -> true ; true), % Used for widening
    del_parent(Parents,K,NewN,NewParents),
    erase(Ref),
    asserta_fact(complete(GKey,AbsInt,A1,A2,A3,Id,NewParents)).
%% erase_prev_parents((GKey,_,_),K,_AbsInt,NewN,Id):-
 %%     current_fact(approx(GKey,A1,A2,A3,Id,Parents),Ref),!,
 %%     del_parent(Parents,K,NewN,NewParents),
 %%     erase(Ref),
 %%     asserta_fact(approx(GKey,A1,A2,A3,Id,NewParents)).
 %% erase_prev_parents((GKey,_,_),K,_AbsInt,NewN,Id):-
 %%     current_fact(fixpoint(GKey,A1,A2,A3,Id,Parents),Ref),!,
 %%     del_parent(Parents,K,NewN,NewParents),
 %%     erase(Ref),
 %%     asserta_fact(fixpoint(GKey,A1,A2,A3,Id,NewParents)).
erase_prev_parents(_,_,_,_,_).

listbody_to_body([X],(X)) :- !.
listbody_to_body([X|Xs],(X,Goals)) :-
    listbody_to_body(Xs,Goals).


:- doc(section, "Reverse indexes for plai_db").
%
% *IMPORTANT NOTE*: THESE INDEXES NEED TO BE MAINTAINED MANUALLY USING
% init_rev_idx/1 and clean_rev_idx/1.

% ---- begin hack: construct reverse indices for better indexing ----
% TODO: merge with complete and memo_table updates (if it works)
:- data complete_id_key_/3.
:- data memo_table_id_key_/3.
:- export(init_rev_idx/1). % for inc assertions
init_rev_idx(AbsInt) :-
    clean_rev_idx(AbsInt),
    ( complete(Key, AbsInt, _Sg, _Proj, _Prime, Id, _Parents),
        \+ Id = no,
        assertz_fact(complete_id_key_(Id,AbsInt,Key)),
        fail
    ; true
    ),
    ( memo_table(MKey, AbsInt, Id, _Child, _Sg, _Proj),
        assertz_fact(memo_table_id_key_(Id,AbsInt,MKey)),
        fail
    ; true
    ).
:- export(clean_rev_idx/1). % for inc assertions
clean_rev_idx(AbsInt) :-
    retractall_fact(complete_id_key_(_,AbsInt,_)),
    retractall_fact(memo_table_id_key_(_,AbsInt,_)).

% IG: ensure that the deletion does not fail even if the indexes are not created
:- export(complete_id_key/3). % for inc assertions
complete_id_key(A, B, C) :-
    complete_id_key_(A, B, C), !.
complete_id_key(_, _, _).

:- export(memo_table_id_key/3). % for inc assertions ( % TODO: not necessary )
memo_table_id_key(_, _, _) :-
    \+ memo_table_id_key_(_, _, _), !.
memo_table_id_key(A, B, C) :-
    memo_table_id_key_(A, B, C).

% ---- end hack: construct reverse indices for better indexing ----


% ----------------------------------------------------------------------
:- doc(section, "Operations for invalid calls").

:- export(add_invalid_call/6).
:- pred add_invalid_call(+SgKey,+AbsInt,+LitKey,+Id,+Sg,+Proj).
add_invalid_call(SgKey,AbsInt,LitKey,Id,Sg,Proj) :-
    invalid_call(SgKey,AbsInt,LitKey,Id,Sg,Proj), !.
add_invalid_call(SgKey,AbsInt,LitKey,Id,Sg,Proj) :-
    assertz_fact(invalid_call(SgKey,AbsInt,LitKey,Id,Sg,Proj)).

:- export(store_raw_success/6).
:- pred store_raw_success(+ClKey,+AbsInt,+Id,+Sg,+Proj,+LPrime).
store_raw_success(ClKey,AbsInt,Id,Sg,Proj,LPrime) :-
    ( retract_fact(raw_success(ClKey,AbsInt,Id,_,_,_)) -> true ; true ),
    % Id is unique
    assertz_fact(raw_success(ClKey,AbsInt,Id,Sg,Proj,LPrime)).

:- export(get_raw_success/6).
:- pred get_raw_success(+ClKey,+AbsInt,+Id,Sg,Proj,LPrime)
   => list(LPrime).
get_raw_success(ClKey,AbsInt,Id,Sg,Proj,LPrime) :-
    raw_success(ClKey,AbsInt,Id,Sg,Proj,LPrime), !.

:- doc(section, "Types").

:- export(plai_db_id/1).
:- regtype plai_db_id/1.
plai_db_id(no).
plai_db_id(X) :-
    int(X).
