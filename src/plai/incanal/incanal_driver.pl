:- module(incanal_driver,
    [init_empty_inc_analysis/0,
     init_file_inc_analysis/3,
     td_add_clauses/2,
     td_delete_clauses/2,
     bu_delete_clauses/2
    ],
    [assertions, isomodes, datafacts, nativeprops]).

:- include(incanal_options). % tracing and rtchecks compilation options

:- doc(title, "Incremental analysis (low level)").
:- doc(author, "Isabel Garcia-Contreras (ported from ciaopp-0.8)").

:- doc(module, "This module contains the basic operations for adding
    or removing clauses to ciaopp (currently working for fixpoint
    dd) and perform an incremental reanalysis.

The posible actions are:
@begin{itemize}

@item Initialize ciaopp for incremental analysis (see
@pred{init_empty_inc_analysis}), for clauses to be added/removed from, they
should be implemented in a file passed to this predicate.

@item Add clauses to analysis (see @pred{td_add_clauses/2}). Adds
    clauses and performs top down reanalysis.

@item Remove clauses from analysis, following a top down strategy (see
@pred{td_delete_clauses/2}). Removes clauses and performs top down
reanalysis.

@item Remove clauses from analysis, following a bottom up strategy
(see @pred{bu_delete_clauses/2}). Removes clauses and reanalyzes
according to the strategy defined.

@end{itemize}").

% ciao libraries
:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(aggregates)).
:- use_module(library(lists), [member/2, append/3, union/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sort)). % to remove duplicates

% plai
:- use_module(ciaopp(plai/fixpo_dd)).
:- use_module(ciaopp(plai/fixpo_ops), [each_abs_sort/3, each_extend/6, each_less_or_equal/3]).
:- use_module(ciaopp(plai/transform), [trans_clause/3, cleanup_trans_clauses/0, determine_r_flag/3]).
:- use_module(ciaopp(plai/domains), [identical_proj/5, init_abstract_domain/2,
                                     abs_sort/3, identical_abstract/3, compute_lub/3]).
:- use_module(ciaopp(plai/tarjan), [recursive_class/2, get_recursivity_class/3]).
:- use_module(ciaopp(p_unit/program_keys)).
:- use_module(ciaopp(plai/plai_db)).
:- use_module(ciaopp(plai), [topdown_analysis/3, mod_topdown_analysis/3, entry_point/5]).
:- use_module(ciaopp(plai/intermod_entry), [get_entry_info/3]).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7]).

%%% ciaopp
:- use_module(ciaopp(frontend_driver), [module/1]).
:- use_module(ciaopp(analyze_driver), [clean_analysis_info/0, assert_domain/1]).
:- use_module(ciaopp(preprocess_flags),
        [current_pp_flag/2, set_pp_flag/2,typeanalysis/1]).
:- use_module(ciaopp(analysis_stats)).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

%%% p_unit
:- use_module(ciaopp(p_unit), [program/2]).
:- use_module(ciaopp(p_unit/p_dump), [clean_all_ciaopp_db/0]).
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3, cleanup_clause_db/0]).
:- use_module(ciaopp(p_unit/assrt_db), [cleanup_assrt_db/0]).
:- use_module(ciaopp(p_unit/auxinfo_dump),
    [restore_auxiliary_info/2, imp_auxiliary_info/4]).
:- use_module(ciaopp(p_unit/p_abs), [curr_mod_entry/4, typedb/2]).

%%% incanal
:- use_module(ciaopp(plai/incanal/tarjan_inc)).
:- use_module(ciaopp(plai/incanal/plai_db_comparator)).
:- use_module(ciaopp(plai/incanal/incanal_deletion)). % low level deletion functionality
:- use_module(ciaopp(plai/incanal/incanal_db)).

% ----------------------------------------------------------------------
:- doc(section, "Initialization predicates").

:- doc(init_empty_inc_analysis/0, "Initializes ciaopp for incremental
analysis. @bf{Removes all previous analysis info}.").
init_empty_inc_analysis :-
    cleanup_trans_clauses, % asserted clauses in traverse_clauses
    clean_analysis_info,
    clean_incremental_db,
    cleanup_clause_db,
    cleanup_assrt_db, % removes only program assertions (not cached lib assertions)
    clean_all_ciaopp_db,
    retractall_fact(changed_complete_id(_,_,_)),
    retractall_fact(changed_complete(_,_,_,_,_)).

:- pred init_file_inc_analysis(Files, Cls, Ds) : list(Files)
   #"Initializes incremental analysis with a file.".
init_file_inc_analysis(Files, Cls, Ds) :-
    init_empty_inc_analysis,
    read_file(Files, Cls, Ds),
    init_clkeys.

read_file(AbsoluteName,Cls, Ds) :-
    module(AbsoluteName),
    program(Cls,Ds).

sources_from_clkeys([], [], []).
sources_from_clkeys([ClKey|ClKeys], [Cl:ClKey|Cls], [D|Ds]) :-
    source_clause(ClKey, Cl, D), !,
    sources_from_clkeys(ClKeys, Cls, Ds).

%---------------------------------------------------------------------
:- doc(section, "Top-down clause addition").

:- pred td_add_clauses(ClKeys, AbsInt) : list * atm + (not_fails, is_det)
   #"Adds a list of already processed clauses, expressed with their clause id
    (@var{ClKeys}) to the code database and updates the analysis of abstract
    domain @var{AbsInt} with them.".
td_add_clauses([], _) :- !.
td_add_clauses(ClKeys, AbsInt) :-
    pplog(incremental_high, ['{[incanal] Adding clauses', ClKeys, '}']),
    sources_from_clkeys(ClKeys, Cls, Ds),
    pplog(incremental_high, ['{[incanal] Added clauses to db', ClKeys, '}']),
    inc_plai_add(Cls, Ds, dd, AbsInt, _).

% the clause (that may have been transformed into more than one) needs to be
% reanalized (in fact is the first time it is going to be analyzed). We
% start from the beginning. We use the artificial key P/A/C/0
td_mark_add_clauses([], _).
td_mark_add_clauses([clause(_Head,_Body):ClKey|Clauses], AbsInt) :-
    decode_clkey(ClKey, P, A, C), !, % TODO: IG leaves choicepoint
    get_predkey(P,A,Key),
    get_litkey(P,A,C,0,LitKey),
    td_mark_add_complete(Key,LitKey,P/A/C/0, AbsInt), % module before
    td_mark_add_clauses(Clauses, AbsInt).

td_mark_add_complete(Key,LitKey,Literal, AbsInt) :-
    current_fact(complete(Key,AbsInt,_,_,_,Id,Parents)),
    add_change(Id,LitKey,Literal,Parents, AbsInt),
    fail.
td_mark_add_complete(_, _, _, _).

% ----------------------------------------------------------------------
:- doc(section, "Top-down clause deletion").

:- pred td_delete_clauses(ClKeys, AbsInt) : list * atm + (not_fails, is_det)
   #"Removes clauses with ids of list @var{ClKeys} for abstract domain
   @var{AbsInt} from analysis using top-down deletion strategy and performs a
   reanalysis.".
td_delete_clauses([], _) :- !.
td_delete_clauses(ClKeys, AbsInt) :-
    pplog(incremental_high, ['{[incanal] Td deleting clauses', ClKeys, '}']),
    stat(preproc, del_preprocess_clauses(ClKeys, AbsInt, Keys)),
    init_rev_idx(AbsInt), % TODO: !!!
    stat(td_delete, td_rec_delete_completes(Keys, AbsInt)),
    clean_rev_idx(AbsInt), % TODO: !!!
    pplog(incremental_high, ['{[incanal] Td deleted clauses', ClKeys, '}']),
    run_inc_fixpoint(AbsInt).

td_rec_delete_completes([], _).
td_rec_delete_completes([Key|Keys], AbsInt) :-
    findall(Id, complete(Key, AbsInt, _, _, _, Id, _), Ids),
    td_rec_delete_completes_(Ids, Key, AbsInt), !,
    td_rec_delete_completes(Keys, AbsInt).
td_rec_delete_completes([_|Keys], AbsInt) :-
    td_rec_delete_completes(Keys, AbsInt).

td_rec_delete_completes_([], _, _).
td_rec_delete_completes_([Id|Ids], Key, AbsInt) :-
    td_rec_delete_complete(Id, Key, AbsInt), !,
    td_rec_delete_completes_(Ids, Key, AbsInt).
td_rec_delete_completes_([_|Ids], Key, AbsInt) :-
    td_rec_delete_completes_(Ids, Key, AbsInt).

:- export(td_rec_delete_complete/3).
:- pred td_rec_delete_complete(+Id, ?Key, +AbsInt)
   : (plai_db_id(Id), atm(AbsInt)) + not_fails
   #"This predicate removes the complete with @var{Id} in domain @var{AbsInt} and
    all its dependent information".
td_rec_delete_complete(no, _Key, _) :- !.
td_rec_delete_complete(Id, Key, AbsInt) :- % pass Key
    % complete_id_key(Id, AbsInt, Key), % (for indexing) % this should work
    get_complete(Key,AbsInt,_,_,_,Id,Parents,_),
    findall((MKey,Child), complete_child(Id, AbsInt, MKey,Child), Children),
    % IG: this findall is done for termination, delete_complete removes the memo_table
    delete_complete(Key, AbsInt, Id),
    td_rec_delete_memo_table(Children,AbsInt),
    remove_memo_table_depends_complete(Parents, AbsInt, Id).
td_rec_delete_complete(_,_,_).

complete_child(Id,AbsInt,MKey,Child) :-
    memo_table_id_key(Id, AbsInt, MKey),
    memo_table(MKey, AbsInt, Id, Child, _Vars, _Proj),
    \+ Child = no. %%% do not collect memo_table for builtins

td_rec_delete_memo_table(Ids,AbsInt) :-
    ( % failure-driven loop
      member((MKey,Id), Ids),
        complete_key_from_id(Child, AbsInt, PKey),
        erase_rec_prev_parents(PKey, MKey, AbsInt, Id, Child),
        fail
    ; true ).

remove_memo_table_depends_complete([], _, _).
remove_memo_table_depends_complete([(PKey, _Id)|Parents], AbsInt, Id) :-
    is_entrykey(PKey), !,
    remove_memo_table_depends_complete(Parents, AbsInt, Id).
remove_memo_table_depends_complete([(LitKey, PId)|Parents], AbsInt, Id) :-
    ( get_parent_key(LitKey,PId,AbsInt,Key) -> % get_parent_key may fail if the complete was already removed
        td_rec_delete_complete(PId, Key, AbsInt) 
    ; true
    ),
    remove_memo_table_depends_complete(Parents, AbsInt, Id).

erase_rec_prev_parents(GKey,K,AbsInt,NewN,Id):-
    atom(GKey), !,
    del_parent_complete(GKey,AbsInt,Id,K,NewN,NewParents),
    decide_delete_complete(NewParents,GKey),
    td_rec_delete_complete(Id, GKey, AbsInt). % TODO:!!
erase_rec_prev_parents(_,_,_,_,_).

decide_delete_complete([], _) :- !. % The complete has no more parents
decide_delete_complete(NewParents, GKey) :-
    decode_predkey(GKey, P, A),
    recursive_class(P/A, Class),
    all_parents_same_rec_class(NewParents, Class).

% [IG]
% We remove the complete if all its parents belong to the same
% recursive class.  The recursive class is an over-approximation of
% the actual dinamic call graph that is stored in the memo_table.  The
% use of the static recursive classes for deciding wether there are
% cycles in the complete parents may cause deletions that were not
% necessary (i.e., for example the parents could be in the same rec
% class but with a call pattern comming from a different call).
all_parents_same_rec_class([], _Class).
all_parents_same_rec_class([(LitKey, _)|Ps], Class) :-
    decode_litkey(LitKey, P, A, _C, _L),
    member(P/A, Class), !,
    all_parents_same_rec_class(Ps, Class).

:- data useful/1.
:- pred useless(+Id) : plai_db_id. % only to check, do not generate.
useless(no) :- !, fail.
useless(0) :- !, fail. % query Id is never useless
useless(Id) :-
    \+ useful(Id), !.

:- export(remove_useless_completes/1).
:- pred remove_useless_completes(+AbsInt) + not_fails
   #"Remove completes which have no parents and would not be necessary during
    the reanalysis. Completes with empty parents would be (recursively) deleted.".
remove_useless_completes(AbsInt) :-
    deleted_comp, !,
    retractall_fact(useful(_)),
    init_rev_idx(AbsInt), % TODO: !!!
    retractall_fact(useful(_)),
    ( % failure-driven loop
      analysis_entry(SgKey,AbsInt,Sg,Proj),
        mark_useful_complete(SgKey,AbsInt,Sg,Proj),
        fail
    ; true),
    remove_useless_from_plai_db(AbsInt),
    clean_rev_idx(AbsInt). % TODO: !!!
remove_useless_completes(_AbsInt).

:- export(module_has_entries/1).
module_has_entries(AbsInt) :-
    analysis_entry(_,AbsInt,_,_), !.

analysis_entry(SgKey,AbsInt,Sg,Proj) :-
    \+ using_modular_driver, !,
    entry_point(AbsInt,Sg,_Sv,Proj,_Name),
    predkey_from_sg(Sg, SgKey).
analysis_entry(SgKey,AbsInt,Sg,Proj) :-
    using_modular_driver,
    ( curr_mod_entry(SgKey, AbsInt, Sg, Proj) ;
        get_entry_info(AbsInt, Sg, Proj), %% entries not yet added to registry
        predkey_from_sg(Sg, SgKey)
    ).

:- pred mark_useful_complete(+SgKey,+AbsInt,+Sg,+Proj) + (is_det, not_fails).
mark_useful_complete(SgKey,AbsInt,Sg,Proj) :-
    complete(SgKey, AbsInt, Sg1, Proj1, _E, Id, Fs), % creating choicepoints
    \+ Fs = [], %% completes with empty parents are never useful
    check_same_calls(AbsInt, Sg, Proj, Sg1, Proj1), !,
    mark_useful_sons(Id, AbsInt).
mark_useful_complete(_SgKey,_AbsInt,_Sg,_Proj).

:- pred mark_useful_sons(+Id, +AbsInt) + not_fails.
mark_useful_sons(no, _AbsInt) :- !. % special case (auxiliary completes have Id = no)
mark_useful_sons(Id, _AbsInt) :-
    useful(Id), !. % do nothing if already visited
mark_useful_sons(Id, AbsInt) :-
    assertz_fact(useful(Id)),
    ( % failure-driven loop
      memo_table_id_key(Id, AbsInt, MKey),
        memo_table(MKey, AbsInt, Id, Child, _, _),
        mark_useful_sons(Child, AbsInt),
        fail
    ; true
    ).

remove_useless_from_plai_db(AbsInt) :-
    current_fact(complete(SgKey, AbsInt, Sg, Proj, LPrime, Id, Fs), Ref),
    ( useless(Id) ->
        delete_complete(SgKey,AbsInt,Id)
    ; (Id = no, Fs = []) -> % Auxiliary complete, remove for now
        erase(Ref)
    ;
        update_parents(Fs, NFs, Updated),
        \+ var(Updated),
        erase(Ref),
        assertz_fact(complete(SgKey, AbsInt, Sg, Proj, LPrime, Id, NFs))
    ),
    fail.
remove_useless_from_plai_db(_).

update_parents([], [], _).
update_parents([(_,Id)|Fs], NFs, yes) :-
    useless(Id), !,
    update_parents(Fs, NFs, _).
update_parents([F|Fs], [F|NFs], X) :-
    update_parents(Fs, NFs, X).

% ----------------------------------------------------------------------
% for preprocessing when deleting
del_preprocess_clauses(ClKeys, AbsInt, Keys) :-
    remove_clauses_and_related_info_collect_preds(ClKeys, AbsInt, Preds_u,Keys),
    sort(Preds_u,Preds), % no repetitions
    rearrange_tarjan_after_deletion(Preds).

% ----------------------------------------------------------------------
:- doc(section, "Bottom-up clause deletion").

:- pred bu_delete_clauses(ClKeys, AbsInt) : list * atm + (not_fails, is_det)
    #"Removes clauses @var{Cls} for abstract domain @var{AbsInt}
      from analysis using the bottom up deletion strategy and
      performs a reanalysis.".
bu_delete_clauses([], _) :- !.
bu_delete_clauses(ClKeys, AbsInt) :-
    pplog(incremental_high, ['{[incanal] BU deleting clauses', ClKeys, '}']),
    retractall_fact('$change_list'(_,_,_)),
    stat(preproc, del_preprocess_clauses(ClKeys, AbsInt,PredKeys)),
    tarjan_data(SCCs),
    ( current_pp_flag(del_strategy,bottom_up) ->
        stat(bu_delete, bottom_up_delete_completes_preds(PredKeys,SCCs,AbsInt,ExtCompletes))
    ;
        stat(bu_delete, bu_update_delete_clauses_plai_db(PredKeys,SCCs,AbsInt,ExtCompletes))
    ),
    pplog(incremental_high, ['{[incanal] BU deleted clauses', ClKeys, '}']),
    stat(fixp, run_bu_del_fixp(ExtCompletes,AbsInt,SCCs)),
    set_fact(deleted_comp),
    remove_useless_completes(AbsInt). % Do not call this if no dependencies changed

:- pred run_bu_del_fixp(+Completes,+AbsInt,+SCCs) + (not_fails, is_det).
run_bu_del_fixp(Completes,AbsInt,SCCs) :-
    analyze_external_calls(Completes,AbsInt,New_answers),
    bottom_up_reanalyze_SCC(Completes,New_answers,AbsInt,SCCs).

:- pred bottom_up_reanalyze_SCC(+Completes,+New_answers,+AbsInt,+SCCs)
   : list * list(list) * atm * list(list)
   + (not_fails, is_det).
bottom_up_reanalyze_SCC(Completes,New_answers,AbsInt,SCCs) :-
    % IG: get the list of answers that changed
    only_different(Completes,New_answers,Differ,AbsInt),
    bottom_up_reanalyze_another_level(Differ,AbsInt,SCCs).

:- pred only_different/4 : list * list(list) * var * atm
   => list * list(list) * list * atm + (not_fails, is_det).
%% IG: sort here also by topological order?
only_different([],[],[],_) :- !.
only_different([comp(_,_,_,O_Prime_u,_,Fs)|Comps],[N_Prime_u|N_Primes],Differ,AbsInt):-
    each_abs_sort(O_Prime_u,AbsInt,O_Prime),
    each_abs_sort(N_Prime_u,AbsInt,N_Prime),
    ( check_same_success_sorted(O_Prime,AbsInt,N_Prime) ->
        Differ = N_differ
    ;
        Differ = [Fs|N_differ]
    ),
    only_different(Comps,N_Primes,N_differ,AbsInt).

:- pred bottom_up_reanalyze_another_level/3 + (not_fails, is_det).
bottom_up_reanalyze_another_level([], _, _) :- !.
bottom_up_reanalyze_another_level(Fss, AbsInt, SCCs) :-
    ( current_pp_flag(del_strategy, bottom_up) -> % TODO: do not do this each iteration
        b_up_mark_prev_parents(Fss, NewCompletes, AbsInt, SCCs) % merge Fss by SCC?
    ; % del_strategy -> bottom_up_cls
        b_up_process_parents(Fss, AbsInt, SCCs, NewCompletes),
        process_change_list
    ),
    analyze_external_calls(NewCompletes, AbsInt, New_answers), !,
    bottom_up_reanalyze_SCC(NewCompletes, New_answers, AbsInt, SCCs).

% In the bottom_up_cls strategy, the predicate `add_change_scc` of the dd
% fixpoint is used to mark to recompute all the predicates in the strongly
% connected component. For precision, the clauses need to be computed from the
% begining, not just the literals that form the SCC. `process_change_list`
% processes the `$change_list` predicate to force the fixpoint to start from the
% literal '0', ie., the beginning of the clause. This works because we have
% previously erased the information in the `memo_table`.
process_change_list :-
    findall('$change_list'(Id,SgKey,ChL),
            retract_fact('$change_list'(Id,SgKey,ChL)),
            Changes),
    ( % failure-driven loop
      member('$change_list'(Id,SgKey,ChL0), Changes),
        process_change_list_(ChL0,ChL),
        pplog(incremental_high, ['changed ', SgKey, ' ', Id, '\n', ChL0, '\n', ChL,'\n']),
        assertz_fact('$change_list'(Id,SgKey,ChL)),
        fail
    ; true ).

% putting 0 we force the recomputation of the whole clause, this may be optimized
process_change_list_([],[]).
process_change_list_([(_,N/A/C/_)|ChL0],[(_,N/A/C/0)|ChL]) :-
    process_change_list_(ChL0,ChL).

:- pred b_up_mark_prev_parents(+Fss, -Completes, +AbsInt, +SCCs)
   : ( list(list,Fss), atm(AbsInt), list(list,SCCs) )
   => list(Completes) + (not_fails, is_det).
b_up_mark_prev_parents([], [], _, _).
b_up_mark_prev_parents([Fs|Fss], TCompletes, AbsInt, SCCs) :-
    b_up_prev_literal(Fs, Completes, AbsInt, SCCs),
    append(Completes, MoreCompletes, TCompletes),
    b_up_mark_prev_parents(Fss, MoreCompletes, AbsInt, SCCs).

b_up_prev_literal([],[],_,_).
b_up_prev_literal([(Lit,Id)|Fs],Completes,AbsInt,SCCs):-
    decode_litkey(Lit,N,A,_,_), !,
    get_recursivity_class(N/A,SCCs,SCC),
    get_predkey(N,A,Key),
    bottom_up_delete_complete(Key,Id,SCC,AbsInt,CompletesSCC),
    append(CompletesSCC,MoreCompletes,Completes),
    b_up_prev_literal(Fs,MoreCompletes,AbsInt,SCCs).
b_up_prev_literal([(ClKey, _)|Fs],Completes,AbsInt,SCCs) :-
    is_entrykey(ClKey), !,
    b_up_prev_literal(Fs,Completes,AbsInt,SCCs).

b_up_process_parents(Fss, AbsInt, SCCs, NewCompletes) :-
    % 1.- Use mark_parents_change_list to populate '$change_list' with the
    %     clauses of the completes of the SCC
    mark_parents_scc(Fss,AbsInt,SCCs),
    % 2.- Remove from plai_db the memo_table of the clauses in '$change_list'
    % 3.- Collect the completes
    findall(comp(SgKey,Sg,Proj,Prime,Id,Fs),
            update_marked_complete(SgKey,AbsInt,SCCs,Sg,Proj,Prime,Id,Fs),
            NewCompletes).

:- pred update_marked_complete(?SgKey,+AbsInt,+SCCs,?Sg,-Proj,-Prime,-Id,-ExtFs)
   => ( nonvar(Proj), nonvar(Prime), plai_db_id(Id), list(ExtFs))
   % used for backtracking (may_be_nondet)
   #"Removes from plai_db the info related to clauses that were marked to be
    potentially un precise. After this a temporary value for the complete is
    computed based on the success of each of non-affected (necessarily
    non-recursive) clauses.".
update_marked_complete(SgKey,AbsInt,SCCs,Sg,Proj,Prime,Id,ExtFs) :-
    ( % bactracking here allowed
        '$change_list'(Id,SgKey,LitKeys),  % no duplicated Ids
        remove_plai_db_clauses(LitKeys,SgKey,AbsInt,Id)
    ;
        retract_fact(changed_complete_id(Id,SgKey,_)), % (*)
        \+ '$change_list'(Id,SgKey,_)
    ),
    get_complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Fs,Ref), erase(Ref),
    functor(Sg,F,A),
    get_recursivity_class(F/A,SCCs,SCC),
    external_calls(Fs,ExtFs,_IntFs,SCC),
    recompute_complete_from_raw_successes(SgKey,Id,AbsInt,Sg,NewTempPrime),
    assertz_fact(complete(SgKey,AbsInt,Sg,Proj,NewTempPrime,Id,[])).
%% (*) covers when a clause is removed and the predicate does not contain
%% recursive clauses, and therefore they were not marked while add_change_scc

:- pred remove_plai_db_clauses(+,+,+,+) + not_fails.
remove_plai_db_clauses([],_,_,_).
remove_plai_db_clauses([(_,F/A/Cl/_)|LitKeys],SgKey,AbsInt,Id) :-
    get_clkey(F,A,Cl,ClKey),
    ( delete_plai_db_one_clause(SgKey,ClKey,Id,AbsInt) -> true ; true ), % may be already deleted
    remove_plai_db_clauses(LitKeys,SgKey,AbsInt,Id).

mark_parents_scc([],_,_).
mark_parents_scc([Fs|Fss], AbsInt, SCCs) :-
    mark_parent_scc(Fs,AbsInt,SCCs), % adds '$change_list'(C,NewList),
    mark_parents_scc(Fss, AbsInt, SCCs).

mark_parent_scc([],_,_).
mark_parent_scc([(Lit,Id)|Fs],AbsInt,SCCs):-
    decode_litkey(Lit,N,A,_,_), !,
    get_recursivity_class(N/A,SCCs,Class),
    mark_parents_change_list_scc([(Lit,Id)], Class, AbsInt),
    mark_parent_scc(Fs,AbsInt,SCCs).
mark_parent_scc([(ClKey, _)|Fs],AbsInt,SCCs) :-
    is_entrykey(ClKey), !,
    mark_parent_scc(Fs,AbsInt,SCCs).

:- pred analyze_external_calls(+Comps,+AbsInt,-Answers)
   : (list(Comps), atm(AbsInt))
   => list(list,Answers) + not_fails.
analyze_external_calls([],_,[]).
analyze_external_calls([comp(SgKey,Sg,Proj,_,Id,Fs)|Comps],AbsInt,[Answer|Answers]):-
    varset(Sg,Sv),
    ( current_pp_flag(del_strategy, bottom_up) ->
        functor(Sg,P,A),
        rec_preds(Ps),
        determine_r_flag(Ps, P/A,RFlag),
        bu_del_call_to_succ(RFlag,SgKey,Proj,Proj,Sg,Sv,AbsInt,Answer,Fs,Id)
    ; % del_strategy = bottom_up_cls
        bu_update_call_to_succ(SgKey,Proj,Sg,Sv,AbsInt,Answer,Fs,Id)
    ),
    % remove_useless_completes(AbsInt), % we postpone this until we are finished
    analyze_external_calls(Comps,AbsInt,Answers).

:- pred bu_del_call_to_succ(+RFlag,+SgKey,+Call,+Proj,+Sg,+Sv,+AbsInt,-Succ,+ExtFs,+Id)
   => list(Succ) + (not_fails, is_det)
    #"This predicate is a modification of predicate @pred{call_to_success/11}
     defined in an analysis algorithms. The main differences are that rather
     than adding one element to the list of clauses for the complete, we add the
     list of external calls previously computed for the complete.".
bu_del_call_to_succ(nr,SgKey,Call,Proj,Sg,Sv,AbsInt,Prime,ExtFs,Id) :-
    fixpoint_trace('[incanal] bu non-recursive initiated',Id,N,SgKey,Sg,Proj,Clauses),
    proj_to_prime_nr(SgKey, Sg, Sv, Call, Proj, AbsInt, SgKey, Prime, Id), !, % TODO: remove '!'?
    fixpoint_trace('[incanal] bu non-recursive completed',Id,N,SgKey,Sg,Prime,Clauses),
    asserta_fact(complete(SgKey, AbsInt, Sg,Proj,Prime,Id,ExtFs)).
bu_del_call_to_succ(r,SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,ExtFs,Id) :-
    % proj_to_prime_r processes the non recursive clauses of a recursive predicate
    proj_to_prime_r(SgKey, Sg, Sv, Call, Proj, AbsInt, TempPrime, Id), !,
    asserta_fact(complete(SgKey, AbsInt, Sg,Proj,TempPrime,Id,[])),
    bagof(X, X^(trans_clause(SgKey, r, X)),Clauses),
    fixpoint_trace('[incanal] bu fixpoint started',Id,N,SgKey,Sg,Proj,Clauses),
    compute(Clauses,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id),
    ( retract_fact('$change_list'(Id,SgKey,ChL)) ->
        fixpoint_compute_change(ChL,SgKey,Sg,Sv,Proj,AbsInt,Prime,NPrime,Id)
    ;
        NPrime = Prime
    ),
    retract_fact(complete(SgKey,AbsInt,A,B,C,Id,SCCFs)), !,
    union(ExtFs,SCCFs,Fs),
    asserta_fact(complete(SgKey,AbsInt,A,B,C,Id,Fs)),
    Succ = NPrime,
    fixpoint_trace('[incanal] bu fixpoint completed',Id,N,SgKey,Sg,NPrime,Clauses).

%% bu_del_call_to_succ_for reusing data from the non affected clauses
:- pred bu_update_call_to_succ(+SgKey,+Proj,+Sg,+Sv,+AbsInt,-Succ,+ExtFs,+Id)
   : (atm(SgKey), list(Sv), atm(AbsInt), list(ExtFs), plai_db_id(Id))
   => list(Succ) + (not_fails, is_det).
bu_update_call_to_succ(SgKey,_Proj,Sg,Sv,AbsInt,Succ,ExtFs,Id) :-
    get_complete(SgKey,AbsInt,Sg,Proj,Prime1,Id,_,_),
    each_abs_sort(Prime1,AbsInt,TempPrime),
    abs_sort(AbsInt, Proj, Proj_s),
    ( retract_fact('$change_list'(Id, SgKey, ChL)) ->
        fixpoint_trace('[incanal] bu fixpoint started',Id,_,SgKey,Sg,Proj_s,_),
        fixpoint_compute_change(ChL,SgKey,Sg,Sv,Proj_s,AbsInt,TempPrime,NPrime,Id)
    ;
        NPrime = TempPrime
    ),
    Succ = NPrime,
    retract_fact(complete(SgKey,AbsInt,A,B,C,Id,SCCFs)), !,
    union(ExtFs,SCCFs,Fs),
    asserta_fact(complete(SgKey,AbsInt,A,B,C,Id,Fs)),
    % each_extend(Sg,Prime,AbsInt,Sv,Proj,Succ),
    fixpoint_trace('[incanal] bu fixpoint completed',Id,_,SgKey,Sg,Succ,_).

%-------------------------------------------------------------------
:- doc(section, "Predicates for running the fixpoint.").

:- export(run_inc_fixpoint/1).
:- pred run_inc_fixpoint(+AbsInt) + (not_fails, is_det)
   #"This predicate runs fixpoint for abstract domain @var{AbsInt}. It
   should to be run after adding information from registry files in
   intermodular analysis.".
run_inc_fixpoint(AbsInt) :-
    rec_preds(Ps),
    set_pp_flag(widen, on),
    inc_query(dd, AbsInt, Ps), !. % analyzing leaves choicepoints

% Here we start the top-down incremental analysis. It is the
% same as abs_interpret, but we do not reset fixpoint_id to 0 as that
% may be dangerous (two different completes may get the same number)

inc_plai_add(Cls,Ds,Fixp,AbsInt,_):-
    % initialization
    init_abstract_domain(AbsInt,_Flags),
    do_inc_plai_add(Cls, Ds, Fixp, AbsInt, _, _).

do_inc_plai_add(Cls, Ds, dd, AbsInt, _, _) :-
    %add_packages_if_needed(AbsInt), % IG: output only
    stat(preproc, inc_add_source_clauses(Cls, Ds, AbsInt)),
    % update the recursivity after new clauses
    stat(td_add, td_mark_add_clauses(Cls, AbsInt)),
    run_inc_fixpoint(AbsInt).

inc_query(dd, AbsInt, Ps) :-
    init_abstract_domain(AbsInt, _Flags), % IG flags is an output var? % fast
    call_inc_fixpoint(dd,AbsInt,Ps), !,
    set_fact(deleted_comp).
inc_query(Fixp, _, _) :-
    ( Fixp = dd ->
        message(error, ['Incremental analysis failed'])
    ;
        message(warning, ['Incremental analysis works only for fixpoint dd'])
    ).

call_inc_fixpoint(Fixp,AbsInt,Ps) :-
    assert_domain(AbsInt),
    using_modular_driver, !,
    stat(fixp, mod_topdown_analysis(AbsInt, Fixp, Ps)).
call_inc_fixpoint(Fixp,AbsInt,Ps) :-
    stat(fixp, topdown_analysis(Fixp, AbsInt, Ps)).

using_modular_driver :-
    \+ current_pp_flag(intermod, off).

% --------------------------------------------------
:- doc(section, "Modular analysis predicates").

:- export(incrementally_update_analysis/2).
:- pred incrementally_update_analysis(+Mod, +AbsInt) + (not_fails, is_det)
   #"@var{Mod} is the module that will be reanalyzed after updating its external
    completes. To be called in modular analysis, no following analysis needed.
    This is a top-down strategy update".
incrementally_update_analysis(Mod, AbsInt) :-
    get_external_completes(Mod, AbsInt, Comps),
    \+ Comps = [], !,
    init_rev_idx(AbsInt), % TODO: !!!
    update_imported_completes(Comps, Mod, AbsInt),
    clean_rev_idx(AbsInt),
    ( \+ current_pp_flag(del_strategy, top_down) ->
        tarjan_data(SCCs),
        findall(comp(SgKey,Sg,Proj,Prime,Id,Fs),
                bu_changed_complete(SgKey,Sg,AbsInt,Proj,Prime,Id,Fs),
                Completes),
        pplog(incremental_high, ['bu change completes: ', Completes, '\n']),
        get_new_answers(Completes, AbsInt, NewAnswers),
        pplog(incremental_high, ['bu new answers: ', NewAnswers, '\n']),
        bottom_up_reanalyze_SCC(Completes, NewAnswers,AbsInt, SCCs),
        set_fact(deleted_comp)
    ; true
    ).
incrementally_update_analysis(_, _).

bu_changed_complete(SgKey,Sg,AbsInt,Proj,Prime,Id,Fs) :-
    retract_fact(changed_complete_id(Id,SgKey,AbsInt)),
    get_complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Fs,_).

get_new_answers([], _, []).
get_new_answers([comp(SgKey,Sg,_Proj,_Prime,Id,_Fs)|Cs], AbsInt, [NewPrime|NPs]) :-
    retract_fact(changed_complete(Id,SgKey,AbsInt,Sg,NewPrime)), !,
    get_complete(SgKey,AbsInt,Sg,Proj,_OldPrime,Id,Fs,Ref), erase(Ref),
    asserta_fact(complete(SgKey,AbsInt,Sg,Proj,NewPrime,Id,Fs)),
    get_new_answers(Cs, AbsInt, NPs).

:- use_module(ciaopp(raw_printer)).

% Added for changes in completes during modular analysis
:- export(process_external_complete_change/6).
:- pred process_external_complete_change(+AbsInt,+NewPrime,+SgKey,+Sg,+Id,+Proj)
    : (atm(AbsInt), list(NewPrime), atm(SgKey), plai_db_id(Id)) + not_fails
#"This predicate updates analysis information given a complete that
has changed externally. Typically this is used for updating completes
that are outdated as a consequence of modular analysis (the analysis
of a module was improved). The complete that has change has key
@var{SgKey} and id @var{Id}. The new answer for the complete is
@var{NewPrime} and refers to domain @var{AbsInt}.

Changes in answers are updated as follows:

@begin{itemize}

@item If the new answer is more general than the previous one, the update is
as simple as replacing the answer in the complete and adding an
event.

@item If the new answer is more specific or incompatible, the
information that depends on it has to be deleted and recomputed. We
are removing the information with a top-down deletion strategy,
although a bottom-up deletion strategy could more efficient. The
fixpoint has to be runned after this deletion.

@end{itemize}
    ".
process_external_complete_change(AbsInt,NewPrime,SgKey,Sg,Id,Proj):-
    get_complete(SgKey,AbsInt,Sg,_,OldPrime,Id,Fs,Ref),
    each_abs_sort(OldPrime, AbsInt, OldPrime_s),
    each_abs_sort(NewPrime, AbsInt, NewPrime_s),
    ( each_less_or_equal(OldPrime_s, AbsInt, NewPrime_s) ->
        erase(Ref),
        asserta_fact(complete(SgKey,AbsInt,Sg,Proj,NewPrime_s,Id,Fs)),
        td_mark_parents_change_list(Fs,AbsInt)
    ; \+ current_pp_flag(del_strategy, bottom_up_cls) ->
        td_rec_delete_complete(Id, SgKey, AbsInt)
    ;
        mark_bu_rec_update_complete(Id, SgKey, AbsInt, Sg, NewPrime_s)
    ).
process_external_complete_change(_,_,_,_,_,_).
% This case means that the complete was removed earlier

get_external_completes(Mod, AbsInt, Cs) :-
    findall((EMod, C), external_updated_complete(Mod, AbsInt, C, EMod), Cs).

:- pred external_updated_complete(Module, AbsInt, C, ExtMod) #"@var{C}
    is a complete of a predicate which is not defined in
    @var{Module}.".
external_updated_complete(Module, AbsInt, C, M) :-
    complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents),
    decode_predkey(SgKey, P, _),
    module_split(P, M, _),
    Module \= M,
    \+ Id = no,
    C = complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents).

:- pred update_imported_completes/3 + not_fails.
update_imported_completes([], _, _).
update_imported_completes([(ImpMod, C)|Cs], CMod, AbsInt) :-
    filter_comps_mod(Cs, ImpMod, NCs, RestCs),
    apply_changes_imported_mod([C|NCs], CMod, ImpMod),
    update_imported_completes(RestCs, CMod, AbsInt).

:- pred filter_comps_mod/4 + not_fails.
filter_comps_mod([], _, [], []).
filter_comps_mod([(Mod, C)|Cs], Mod, [C|NCs], RestCs) :- !,
    filter_comps_mod(Cs, Mod, NCs, RestCs).
filter_comps_mod([Comp|Cs], Mod, NCs, [Comp|RestCs]) :-
    filter_comps_mod(Cs, Mod, NCs, RestCs).

:- pred apply_changes_imported_mod/3 + not_fails.
apply_changes_imported_mod(Comps, CMod, Mod) :-
    restore_auxinfo_mod(Mod, Dict), % restore module types
    findall((SgKey, Reg), get_changed_registry(SgKey, CMod, Mod, Reg), ChRegs),
    decide_apply_changed_registries(ChRegs, Mod, Comps, Dict).

:- pred decide_apply_changed_registries/4 + not_fails.
decide_apply_changed_registries([], _, _, _).
decide_apply_changed_registries([(SgKey,ChReg)|ChRegs], Mod, Comps, Dict) :-
    ChReg = regdata(_,AbsInt,Sg,RegProj,RegPrime,_,_,_,_),
    ( typeanalysis(AbsInt) -> % TODO: Importing should be a domain action % TODO: use knows_of/2 (JFMC)
	      imp_auxiliary_info(AbsInt, Dict, [RegProj,RegPrime],[Proj,Prime])
    ;
        Proj = RegProj, Prime = RegPrime
    ),
    abs_sort(AbsInt, Proj, Proj_s),
    abs_sort(AbsInt, Prime, Prime_s),
    apply_changes_imported_comps(Comps,SgKey,Sg,Proj_s,Prime_s),
    decide_apply_changed_registries(ChRegs, Mod, Comps, Dict).

:- data deleted_comp/0. % This flags is set to avoid computing the reachable
                        % completes if no completes were removed (all are
                        % reachable)

:- pred apply_changes_imported_comps/5 + (not_fails, is_det).
apply_changes_imported_comps([],_,_,_,_).
apply_changes_imported_comps([Comp|_],SgKey,Sg,ImpProj,ImpPrime) :-
    Comp = complete(SgKey,AbsInt,Sg1,Proj1,OldPrime_u,Id,_),
    identical_proj(AbsInt,Sg,ImpProj,Sg1,Proj1), !,
    CNPrime = [ImpPrime],
    % IG this [ImpPrime] list is because registries do not store success
    % patterns as lists (multivariant is not considered for intermod)
    each_abs_sort(OldPrime_u, AbsInt, OldPrime),
    ( check_same_success_sorted(OldPrime, AbsInt, CNPrime) ->
        true
    ;
        process_external_complete_change(AbsInt, CNPrime, SgKey,Sg1,Id,Proj1),
        ( each_less_or_equal(CNPrime, AbsInt, OldPrime) -> set_fact(deleted_comp) ; true )
    ).
apply_changes_imported_comps([_|Comps], SgKey, Sg, ImpProj, ImpPrime) :-
    apply_changes_imported_comps(Comps, SgKey, Sg, ImpProj, ImpPrime).

restore_auxinfo_mod(Mod, Dict) :-
    set_fact(restore_module(Mod)),
    restore_auxiliary_info(current_typedb,Dict).

:- data restore_module/1.

% TODO: merge with p_abs:current_typedb/1
current_typedb(TypeDef):-
    current_fact(restore_module(Module)),
    current_fact(typedb(Module,TypeDef)).

% ----------------------------------------------------------------------
:- doc(section, "Bottom-up update analysis").

:- data changed_complete_id/3.
:- data changed_complete/5.
% TODO: store it sorted?
:- pred mark_bu_rec_update_complete(+Id, +SgKey, +AbsInt, +Sg, +NewPrime)
   : plai_db_id * atm * atm * term * list + (not_fails, is_det).
mark_bu_rec_update_complete(Id, SgKey, AbsInt, Sg, NewPrime) :-
    ( \+ changed_complete_id(Id,_,_) ->
        assertz_fact(changed_complete_id(Id,SgKey,AbsInt)),
        assertz_fact(changed_complete(Id,SgKey,AbsInt,Sg,NewPrime))
    ; true
    ).

:- data new_prime/2.

:- pred recompute_complete_from_raw_successes(+PredKey,+Id,+AbsInt,Sg,-NewPrime)
   => list(NewPrime) + (not_fails, is_det).
recompute_complete_from_raw_successes(PredKey,Id,AbsInt,Sg,[NewPrime]) :-
    set_fact(new_prime(Sg,'$bottom')),
    ( % failure-driven loop
      trans_clause(PredKey, _, clause(_,_,ClKey,_)),
      % In practice, only no rec cls will be reused, as raw_success of recs are deleted in add_change_scc
        get_raw_success(ClKey,AbsInt,Id,Sg,_Proj,[RPrime],_), % allowed to fail (cl needs to be recomputed)
        \+ RPrime = '$bottom', % do not call domain operation if '$bottom'
        new_prime(Sg,NewPrime0),
        compute_lub(AbsInt, [NewPrime0, RPrime], NewPrime),
        set_fact(new_prime(Sg,NewPrime)),
        fail
    ; new_prime(Sg, NewPrime)
    ).

%%%%%% new predicate for deleting only the necessary clauses
%%% the clauses were already deleted from the clause database
:- pred bu_update_delete_clauses_plai_db(+Preds,SCCs,+AbsInt,-Completes) + not_fails
   #"@var{ClKeys} is the list of clauses to be deleted, @var{Completes} is the
   list of completes that need to be recomputed.".
bu_update_delete_clauses_plai_db(Preds, SCCs, AbsInt, Completes):-
    ( % failure-driven loop
      member(SgKey, Preds),  %% The clause_db (transform.pl) has already been updated
      ( % failure-driven loop
        complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents),
          ( % failure-driven loop
            trans_clause(SgKey, r, clause(_,_,ClKey,_)), %% filter non-recursive, not needed to analyze
              decode_clkey(ClKey,P,A,Cl),
              get_recursivity_class(N/A,SCCs,SCC),
              get_litkey(N,A,Cl,0,LitKey),
              add_change_scc(Id,LitKey,P/A/Cl/0,Parents,SCC,AbsInt),
              fail
          ;   assertz_fact(changed_complete_id(Id,SgKey,AbsInt))
          ),
          fail % backtrack completes
      ;
          fail % backtrack all changed predicates and force failure for findall
      )
    ;
        findall(comp(SgKey,Sg,Proj,Prime,Id,Fs),
                update_marked_complete(SgKey,AbsInt,SCCs,Sg,Proj,Prime,Id,Fs),
                Completes),
        process_change_list
    ).
