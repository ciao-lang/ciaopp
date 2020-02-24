:- module(incanal_deletion,
    [ remove_clauses_and_related_info_collect_preds/4,
      bottom_up_delete_completes_preds/4,
      bottom_up_delete_complete/5
    ],
    [assertions, isomodes, nativeprops, datafacts]).

:- doc(title, "Update plai_db after clause deletion (incremental analysis)").

:- doc(author, "Isabel Garcia-Contreras (ported from ciaopp-0.8)").

:- doc(module, "This module contains predicates for removing completes
and related memo_table data from analysis necessary for recomputing
correctly analysis after removing clauses or modifying the answers of
the analysis.").

:- use_module(ciaopp(plai/tarjan), [get_recursivity_class/3]).

:- use_module(ciaopp(p_unit/program_keys),
    [decode_clkey/4, decode_litkey/5, get_predkey/3, decode_predkey/3]).
:- use_module(ciaopp(plai/domains), [abs_sort/3]).

:- use_module(library(sort), [sort/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(messages)).
:- use_module(library(lists), [member/2, append/3]).

:- use_module(ciaopp(plai/plai_db), [memo_lub/5, complete/7, memo_table/6,
    get_complete/8,delete_complete/3, delete_plai_db_one_clause/4, del_parent/4]).
:- use_module(ciaopp(plai/transform), [trans_clause/3, remove_trans_clause/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- pred remove_clauses_and_related_info_collect_preds(+Clids, +AbsInt, -Preds,-Keys)
    + not_fails
    #"@var{Cls} is a set of clauses which has have been eliminated from the
    program. Thus, they must be deleted from the database of clauses used by the
    analyzer. In addition to the clause, we delete all the memo_tables and
    memo_lubs for the clauses. In @var{Preds} and @var{Keys} we collect the
    name,arity and keys of predicates for which clauses have been deleted. This
    will later be used for updating the SCCs.".
remove_clauses_and_related_info_collect_preds([], _, [], []).
remove_clauses_and_related_info_collect_preds([Clid|Clids], AbsInt, [F/A|Preds],[Key|Keys]):-
    decode_clkey(Clid, F, A, _),
    get_predkey(F,A,Key),
    %%      delete_recursivity_if_necessary(RFlag,Key),
    ( % failure-driven loop
      complete(Key, AbsInt, _, _, _, Id, _),
        delete_plai_db_one_clause(Key,Clid,Id,AbsInt),
        fail
    ;   true
    ),
    remove_trans_clause(Key, Clid),
    remove_clauses_and_related_info_collect_preds(Clids, AbsInt, Preds, Keys).

% ----------------------------------------------------------------------
:- pred bottom_up_delete_completes_preds(+Keys,SCCs,+AbsInt,-ExtCompletes) + not_fails
    # "@var{Keys} is the list of keys of predicates for which clauses
    have been deleted. The completes for such predicates may no longer
    be accurate enough. Thus we collect the external calls in @var{ExtCompletes} and
    erase the corresponding completes from the analysis database.".
bottom_up_delete_completes_preds(Keys, SCCs, AbsInt, ExtCompletes):-
    ( % failure-driven loop
      member(Key, Keys),
        decode_predkey(Key,N,A),
        get_recursivity_class(N/A,SCCs,SCC),
        bottom_up_delete_completes_pred_(Key,SCC,AbsInt),
        fail
    ;
        get_cached_external_calls(ExtCompletes0),
        remove_non_ext_calls(ExtCompletes0,ExtCompletes)
    ).

remove_non_ext_calls(ExtCompletes0,ExtCompletes) :-
    collect_complete_ids(ExtCompletes0,Ids),
    remove_ids_from_parents(ExtCompletes0, Ids, ExtCompletes).

collect_complete_ids([],[]). % an Id cannot be twice in this list
collect_complete_ids([comp(_,_,_,Id,_)|Cs],[Id|Ids]) :-
    collect_complete_ids(Cs,Ids).

remove_ids_from_parents([], _, []).
remove_ids_from_parents([C|Cs0], Ids, [comp(Sg,Proj,LPrime,Id,Fs)|Cs]) :-
    C = comp(Sg,Proj,LPrime,Id,Fs0),
    del_parents(Ids,Fs0,Fs),
    remove_ids_from_parents(Cs0, Ids, Cs).

del_parents([],Fs,Fs).
del_parents([Id|Ids],Fs0,Fs) :-
    del_parent(Fs0,_K,Id,Fs1), % K is not necessary, Id is unique
    del_parents(Ids,Fs1,Fs).

% Exported predicate,
:- pred bottom_up_delete_complete(+SgKey, +Id, +SCC, +AbsInt,-ExtCompletes) + not_fails.
bottom_up_delete_complete(Key, Id, SCC, AbsInt, ExtCompletes) :-
    get_complete(Key, AbsInt, Sg, Proj, Prime, Id, Fs, _), !,
    retractall_fact(external_call(_,_,_,_,_,_)),
    bottom_up_delete_complete_(Key, Id, Sg, Proj, Prime, Fs, SCC, AbsInt),
    get_cached_external_calls(ExtCompletes).
bottom_up_delete_complete(_Key, _Id, _SCC, _AbsInt, []).

bottom_up_delete_complete_(Key, Id, Sg, Proj, LPrime, Fs, SCC, AbsInt) :-
    delete_complete(Key,AbsInt,Id),
    bottom_up_follow_parents_SCC_complete(Key,Sg,Proj,LPrime,Id,Fs,SCC,AbsInt).

%%%%%%%%%%%%%%%% BEGIN New bottom_up_delete_mark %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- data external_call/6.
% external_call(Key,Sg,Proj,LPrime,Id,External).

add_external_call(Key,_Sg,_Proj,_LPrime,Id,_External,_AbsInt) :-
    external_call(Key,_,_,_,Id,_), !.
add_external_call(Key,Sg,Proj_u,LPrime,Id,External,AbsInt) :-
    abs_sort(AbsInt,Proj_u,Proj),
    assertz_fact(external_call(Key,Sg,Proj,LPrime,Id,External)).

get_cached_external_calls(Comps) :-
    findall(comp(Sg,Proj,LPrime,Id,External), retract_fact(external_call(_SgKey,Sg,Proj,LPrime,Id,External)), Comps).

:- data old_complete/6. % no AbsInt
% old_complete(Key,Sg,Proj,LPrime,Id,Fs).

get_old_completes(Key,AbsInt) :-
    retractall_fact(old_complete(Key,_,_,_,_,_)),
    complete(Key, AbsInt, Sg, Proj, LPrime, Id, Fs),
    assertz_fact(old_complete(Key, Sg, Proj, LPrime, Id, Fs)),
    fail.
get_old_completes(_,_).

bottom_up_delete_completes_pred_(Key, SCC, AbsInt) :-
    get_old_completes(Key,AbsInt),
    ( % failure-driven loop
      old_complete(Key,  Sg, Proj, LPrime, Id, Fs), % bc completes are removed
        bottom_up_follow_parents_SCC_complete(Key,Sg,Proj,LPrime,Id,Fs,SCC,AbsInt),
        delete_complete(Key,AbsInt,Id),
        fail
    ; true
    ).

bottom_up_follow_parents_SCC_complete(Key,Sg,Proj,LPrime,Id,Fs,SCC,AbsInt) :-
    external_calls(Fs,External,Internal,SCC),
    (External \= [] ->
        add_external_call(Key,Sg,Proj,LPrime,Id,External,AbsInt)
    ; true
    ),
    sort(Internal,Internal_s), % to eliminate duplicates
    eliminate_self_recursive(Internal_s,Id,Inter),
    ( % failure-driven loop
      member((PKey,PId),Inter),
        get_complete(PKey,AbsInt,PSg,PProj,PLPrime,PId,PFs,_), % this can fail (already processed)
        bottom_up_delete_complete_(PKey,PId,PSg,PProj,PLPrime,PFs,SCC,AbsInt),
        fail
    ; true
    ).

%%%%%%%%%%%%%%%%% END New bottom_up_delete_mark %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%% BEGIN Old bottom_up_delete_mark %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% bottom_up_delete_completes_pred(Key, Completes, SCC, AbsInt):-
%%     findall(comp(Sg, Proj, LPrime, Id, Fs), % Old comp table in the paper
%%             complete(Key, AbsInt, Sg, Proj, LPrime, Id, Fs),
%%             AllCompletes),
%%     bottom_up_mark_list_completes(AllCompletes, Completes, SCC, AbsInt),
%%     ( % failure-driven loop
%%       % TODO: replace this predicate by a failure-driven loop when we have
%%       % checked that doing so with bottom_up_mark_list_completes is safe
%%       member(comp(_, _, _, Id, _), AllCompletes),
%%         delete_complete(Key,AbsInt,Id),
%%         fail
%%     ; true
%%     ).

%% % IG: change name by filter external completes??
%% :- pred bottom_up_mark_list_completes(+Completes, -ExtCompletes, +SCCs, +AbsInt)
%%     # "We filter out from @var{Completes} those which are not seen from
%%        outside the SCC for the corresponding predicate. The result is
%%        given in @var{ExtCompletes}.".
%% bottom_up_mark_list_completes([], [], _, _).
%% bottom_up_mark_list_completes([comp(Sg, Proj_u, LPrime, Id, Fs)|Comps], ExtCompletes,
%%                               SCC, AbsInt):-
%%     external_calls(Fs,External,Internal,SCC),
%%     (External \= [] ->
%%         abs_sort(AbsInt,Proj_u,Proj),
%%         ExtCompletes = [comp(Sg,Proj,LPrime,Id,External)|MoreCompletes]
%%     ;
%%         ExtCompletes = MoreCompletes),
%%     sort(Internal,Internal_s),
%%     eliminate_self_recursive(Internal_s,Id,Inter),
%%     bottom_up_delete_recursively_mark_parents(Inter,Comp,SCC,AbsInt),
%%     append(Comp,NewComp,MoreCompletes),
%%     bottom_up_mark_list_completes(Comps,NewComp,SCC,AbsInt).

%% :- pred bottom_up_delete_recursively_mark_parents(+Inter,-Comp,+SCCs,+AbsInt).
%% bottom_up_delete_recursively_mark_parents([],[],_,_).
%% bottom_up_delete_recursively_mark_parents([(Key,Id)|Fs],Comp,SCC,AbsInt):-
%%     bottom_up_delete_complete(Key,Id,SCC,AbsInt,Complete),
%%     append(Complete,MoreComp,Comp),
%%     bottom_up_delete_recursively_mark_parents(Fs,MoreComp,SCC,AbsInt).

%%%%%%%%%%%%%%%%% END Old bottom_up_delete_mark %%%%%%%%%%%%%%%%%%%%%%%%%%%%%

external_calls([],[],[],_).
external_calls([(Lit,Id)|Fs],External,Internal,SCC):-
    decode_litkey(Lit,N,A,_,_), % IG leaves choicepoint
    get_predkey(N,A,Key),
    member(N/A,SCC),!,
    Internal = [(Key,Id)|More_Internal],
    External = More_External,
    external_calls(Fs,More_External,More_Internal,SCC).
external_calls([(Lit,Id)|Fs],[(Lit,Id)|More_External],Internal,SCC):-
    external_calls(Fs,More_External,Internal,SCC).

eliminate_self_recursive([],_Id,[]).
eliminate_self_recursive([(F,Id1)|Parents],Id,NewParents):-
    (Id = Id1 ->
        NewParents = MoreParents
    ;
        NewParents = [(F,Id1)|MoreParents]),
    eliminate_self_recursive(Parents,Id,MoreParents).
