:- module(incanal_driver,
    [init_empty_inc_analysis/0,
     init_file_inc_analysis/3,
     cl_from_clid/2,
     td_add_clauses/2,
     td_delete_clauses/2,
     bu_delete_clauses/2
    ],
    [assertions, isomodes, datafacts, nativeprops]).

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

:- use_module(ciaopp(plai/fixpo_dd), [add_change/5, add_external_complete_change/6,
    '$change_list'/2, proj_to_prime/9, proj_to_prime_r/8, proj_to_prime_nr/9,
    compute/9, fixpoint_compute_change/9]).
:- use_module(ciaopp(plai/transform), [trans_clause/3, cleanup_trans_clauses/0, determine_r_flag/3]).
:- use_module(ciaopp(plai/domains), [identical_proj/5, init_abstract_domain/2,
                                     abs_sort/3, identical_abstract/3, less_or_equal/3]).
:- use_module(ciaopp(plai/tarjan), [recursive_class/2, get_recursivity_class/3]).
:- use_module(ciaopp(p_unit/program_keys),
    [decode_clkey/4, decode_litkey/5, decode_predkey/3, get_predkey/3,
     predkey_from_sg/2, is_entrykey/1, get_litkey/5]).

%%%%% IG NEW CIAOPP IMPORTS %%%%%
:- use_module(ciaopp(frontend_driver), [module/1]).
:- use_module(ciaopp(analyze_driver), [clean_analysis_info/0, assert_domain/1]).
:- use_module(ciaopp(preprocess_flags),
        [current_pp_flag/2, set_pp_flag/2,typeanalysis/1]).

:- use_module(ciaopp(p_unit), [program/2]).
:- use_module(ciaopp(p_unit/p_dump), [clean_all_ciaopp_db/0]).
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3, cleanup_clause_db/0]).
:- use_module(ciaopp(p_unit/assrt_db), [cleanup_assrt_db/0]).

:- use_module(ciaopp(plai/plai_db)).
:- use_module(ciaopp(plai), [topdown_analysis/3, mod_topdown_analysis/3, entry_point/5]).

:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(engine(messages_basic), [message/2]).

% IG old lib imports
:- use_module(library(aggregates)).
:- use_module(library(lists), [member/2, append/3, difference/3,union/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sort)).

:- use_module(ciaopp(plai/intermod_entry), [get_entry_info/3]).

:- use_module(ciaopp(plai/incanal/tarjan_inc),
    [inc_add_source_clauses/3, tarjan_data/1, rec_preds/1,
     rearrange_tarjan_after_deletion/1]).
:- use_module(ciaopp(plai/incanal/plai_db_comparator),
    [check_same_success/3, check_same_calls/5]).
:- use_module(ciaopp(plai/incanal/incanal_deletion)). % low level deletion functionality
:- use_module(ciaopp(plai/incanal/incanal_db), [init_clids/0,
    clean_incremental_db/0, get_changed_registry/4]).
:- use_module(ciaopp(p_unit/auxinfo_dump),
    [restore_auxiliary_info/2, imp_auxiliary_info/4]).

:- use_module(ciaopp(analysis_stats)).

:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7]).
:- use_package(.(notrace)). % inhibits the tracing

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
    clean_all_ciaopp_db.

:- pred init_file_inc_analysis(Files, Cls, Ds) : list(Files)
    #"Initializes incremental analysis with a file.".
init_file_inc_analysis(Files, Cls, Ds) :-
    init_empty_inc_analysis,
    read_file(Files, Cls, Ds),
    init_clids.

read_file(AbsoluteName,Cls, Ds) :-
    module(AbsoluteName),
    program(Cls,Ds).

:- pred cl_from_clid(+Clid, -Cl) : atm(Clid)
    #"Gets the processed clause @var{Cl} associated with clause id @var{Clid}.".
cl_from_clid(Clid, Cl) :-
    trans_clause(SgKey, RFlag, clause(Head, Vars_u, Clid, Body)),
    Cl = clause(SgKey,RFlag,Head,Vars_u,Clid,Body).

source_from_clid(Clid, Cl, D) :-
    source_clause(Clid, Cl, D).

sources_from_clids([], [], []).
sources_from_clids([Clid|Clids], [Cl:Clid|Cls], [D|Ds]) :-
    source_from_clid(Clid, Cl, D),
    sources_from_clids(Clids, Cls, Ds).

%---------------------------------------------------------------------
:- doc(section, "Incremental addition").

:- pred td_add_clauses(Clids, AbsInt) : list * atm #"Adds a list of
    already processed clauses, expressed with their clause id
    (@var{Clids}) to the code database and updates the analysis of
    abstract domain @var{AbsInt} with them.".
td_add_clauses([], _) :- !.
td_add_clauses(Clids, AbsInt) :-
    fixpoint_trace('[incanal] adding clauses',Clids,_,_,_,_,Clids),
    sources_from_clids(Clids, Cls, Ds),
    fixpoint_trace('[incanal] added clauses',Clids,_,_,_,_,Clids),
    inc_plai_add(Cls, Ds, dd, AbsInt, _).

% the clause (that may have been transformed into more than one) needs to be
% reanalized (in fact is the first time it is going to be analyzed). We
% start from the beginning. We use the artificial key P/A/C/0
td_mark_add_clauses([], _).
td_mark_add_clauses([clause(_Head,_Body):Clid|Clauses], AbsInt) :-
    decode_clkey(Clid, P, A, C), !, % TODO: IG leaves choicepoint
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
:- doc(section, "Top down deletion").

:- pred td_delete_clauses(Clids, AbsInt) : list * atm
    #"Removes clauses with ids of list @var{Clids} for abstract
      domain @var{AbsInt} from analysis using top-down deletion
 strategy and performs a reanalysis.".
td_delete_clauses([], _) :- !.
td_delete_clauses(Clids, AbsInt) :-
    fixpoint_trace('[incanal] td deleting clauses',Clids,_,_,_,_,Clids),
    stat(preproc, del_preprocess_clauses(Clids, AbsInt, Keys)),
    init_rev_idx(AbsInt), % TODO: !!!
    stat(td_delete, td_rec_delete_completes(Keys, AbsInt)),
    clean_rev_idx(AbsInt), % TODO: !!!
    fixpoint_trace('[incanal] td deleted clauses',Clids,_,_,_,_,Clids),
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
    %       complete_id_key(Id, AbsInt, Key), % (for indexing) % this should work
    get_complete(Key,AbsInt,_,_,_,Id,Parents,_),
    findall((MKey,Child), complete_child(Id, AbsInt, MKey,Child), Children),
    % IG: this findall is done for termination, delete_complete removes the memo_table
    delete_complete(Key, AbsInt, Id),
    td_rec_delete_memo_table(Children,AbsInt),
    remove_memo_table_depends_complete(Parents, AbsInt, Id).
td_rec_delete_complete(_,_,_).

complete_child(Id,AbsInt,MKey,Child) :-
    memo_table_id_key(Id, AbsInt, MKey),
    memo_table(MKey, AbsInt, Id, Child, _Vars, _Proj).

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
    decide_delete_complete(GKey,NewParents),
    td_rec_delete_complete(Id, GKey, AbsInt). % TODO:!!
erase_rec_prev_parents(_,_,_,_,_).

:- export(decide_delete_complete/2).
decide_delete_complete(_, []) :- !. % The complete has no more parents
decide_delete_complete(GKey, NewParents) :-
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
:- pred useless(+Id). % only to check, do not generate.
useless(no) :- !, fail.
useless(0) :- !, fail. % query Id is never useless
useless(Id) :-
    \+ useful(Id), !.

% TODO: review for non-modular driver
:- pred remove_useless_completes(+AbsInt) + not_fails.
remove_useless_completes(AbsInt) :-
    init_rev_idx(AbsInt), % TODO: !!!
    retractall_fact(useful(_)),
    ( % failure-driven loop
      analysis_entry(SgKey,AbsInt,Sg,Proj),
        mark_useful_complete(SgKey,AbsInt,Sg,Proj),
        fail
    ; true),
    remove_useless_tuples(AbsInt),
    clean_rev_idx(AbsInt). % TODO: !!!

analysis_entry(SgKey,AbsInt,Sg,Proj) :-
    ( using_modular_driver -> % TODO: review monolithic driver
        ( entry_point(AbsInt,Sg,_Sv,Proj,_Name)
        ; curr_mod_entry(SgKey, AbsInt, Sg, Proj) )
    ;
        get_entry_info(AbsInt,Sg,Proj),
        predkey_from_sg(Sg, SgKey)
    ).

:- pred mark_useful_complete(+SgKey,+AbsInt,+Sg,+Proj) + not_fails.
mark_useful_complete(SgKey,AbsInt,Sg,Proj) :-
      complete(SgKey, AbsInt, Sg1, Proj1, _E, Id, _Fs), % creating choicepoints
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

remove_useless_tuples(AbsInt) :-
    current_fact(complete(SgKey, AbsInt, Sg, Proj, Prime, Id, Fs), Ref),
    ( useless(Id) ->
      delete_complete(SgKey,AbsInt,Id)
    ; (Id = no, Fs = []) -> % Auxiliary complete, remove for now
        erase(Ref)
    ;
        update_parents(Fs, NFs, Updated),
        \+ var(Updated),
        erase(Ref),
        assertz_fact(complete(SgKey, AbsInt, Sg, Proj, Prime, Id, NFs))
    ),
    fail.
remove_useless_tuples(_).

update_parents([], [], _).
update_parents([(_,Id)|Fs], NFs, yes) :-
    useless(Id), !,
    update_parents(Fs, NFs, _).
update_parents([F|Fs], [F|NFs], X) :-
    update_parents(Fs, NFs, X).
% IG END NEW CODE

% ----------------------------------------------------------------------
% for preprocessing when deleting
del_preprocess_clauses(Clids, AbsInt, Keys) :-
    remove_clauses_and_related_info_collect_preds(Clids, AbsInt, Preds_u,Keys),
    sort(Preds_u,Preds), % no repetitions
    rearrange_tarjan_after_deletion(Preds).

:- doc(section, "Bottom-up down deletion").

:- pred bu_delete_clauses(Clids, AbsInt) : list * atm + not_fails
    #"Removes clauses @var{Cls} for abstract domain @var{AbsInt}
      from analysis using the bottom up deletion strategy and
      performs a reanalysis.".
bu_delete_clauses([], _) :- !.
bu_delete_clauses(Clids, AbsInt) :-
    fixpoint_trace('[incanal] bu deleting clauses',Clids,_,_,_,_,Clids),
    set_pp_flag(widen, on), % TODO: replace by push?
    retractall_fact('$change_list'(_,_)),
    stat(preproc, del_preprocess_clauses(Clids, AbsInt,Keys)),
    tarjan_data(SCCs),
    stat(bu_delete, bottom_up_delete_completes_preds(Keys,SCCs,AbsInt,ExtCompletes)),
    %% display(bottom_up_delete_completes_preds(Keys,SCCs,AbsInt,ExtCompletes)), nl,
    fixpoint_trace('[incanal] bu deleted clauses',Clids,_,_,_,_,Clids),
    stat(fixp, run_bu_del_fixp(ExtCompletes,AbsInt,SCCs)),
    remove_useless_completes(AbsInt). % Do not call this if nothing was removed

:- pred run_bu_del_fixp/3 + not_fails.
run_bu_del_fixp(Completes,AbsInt,SCCs) :-
    analyze_external_calls(Completes,New_answers,AbsInt),
    bottom_up_reanalyze_SCC(Completes,New_answers,AbsInt,SCCs).

% IG: removing the 'useless' completes, i.e., completes which have no
% parents would not be necessary if during the reanalysis, completes
% with empty parents would be (recursively) deleted.

:- pred bottom_up_reanalyze_SCC/4 + not_fails.
bottom_up_reanalyze_SCC(Completes,New_answers,AbsInt,SCCs) :-
    % IG: get the list of answers that changed
    only_different(Completes,New_answers,Differ,AbsInt),
    bottom_up_reanalyze_another_level(Differ,AbsInt,SCCs), !.

:- pred only_different/4 + not_fails.
only_different([],[],[],_) :- !.
only_different(Comps1,[N_Prime|N_Primes],Differ,AbsInt):-
    Comps1 = [comp(_,_,O_Prime,_,Fs)|Comps],
    ( check_same_success(AbsInt,O_Prime,N_Prime) ->
        Differ = N_differ
    ;
        Differ = [Fs|N_differ]),
    only_different(Comps,N_Primes,N_differ,AbsInt).

:- pred bottom_up_reanalyze_another_level/3 + not_fails.
bottom_up_reanalyze_another_level([], _, _) :- !.
bottom_up_reanalyze_another_level(Fss, AbsInt, SCCs) :-
    b_up_mark_prev_parents(Fss, NewCompletes, AbsInt, SCCs),
    analyze_external_calls(NewCompletes, New_answers, AbsInt), !,
    bottom_up_reanalyze_SCC(NewCompletes, New_answers, AbsInt, SCCs).

:- pred b_up_mark_prev_parents/4 + not_fails.
b_up_mark_prev_parents([], [], _, _).
b_up_mark_prev_parents([Fs|Fss], Completes, AbsInt, SCCs) :-
    b_up_prev_literal(Fs, Complete, AbsInt, SCCs),
    append(Complete, MoreCompletes, Completes),
    b_up_mark_prev_parents(Fss, MoreCompletes, AbsInt, SCCs).

b_up_prev_literal([],[],_,_).
b_up_prev_literal([(Clid, _)|Fs],Completes,AbsInt,SCCs) :-
    is_entrykey(Clid), !,
    b_up_prev_literal(Fs,Completes,AbsInt,SCCs).
b_up_prev_literal([(Lit,Id)|Fs],Completes,AbsInt,SCCs):-
    decode_litkey(Lit,N,A,_,_),
    get_recursivity_class(N/A,SCCs,SCC),
    get_predkey(N,A,Key),
    bottom_up_delete_complete(Key,Id,SCC,AbsInt,Complete),
    append(Complete,MoreCompletes,Completes),
    b_up_prev_literal(Fs,MoreCompletes,AbsInt,SCCs).

:- pred analyze_external_calls(+Comps,-Answers,+AbsInt) + not_fails.
analyze_external_calls([],[],_).
analyze_external_calls([comp(Sg,Proj,_,Id,Fs)|Comps],[Answer|Answers],AbsInt):-
    functor(Sg,P,A),
    rec_preds(Ps),
    determine_r_flag(Ps, P/A,RFlag),
    varset(Sg,Sv),
    get_predkey(P,A,SgKey),
    bu_del_call_to_succ(RFlag,SgKey,Proj,Proj,Sg,Sv,AbsInt,Answer,Fs,Id), % Call=Proj
    % remove_useless_completes(AbsInt), % should we postpone this until we are finished?
    analyze_external_calls(Comps,Answers,AbsInt).

:- pred bu_del_call_to_succ(+RFlag,+SgKey,+Call,+Proj,+Sg,+Sv,+AbsInt,-Succ,+Fs,+Id) + not_fails
    #"This predicate is a modification of predicate @pred{call_to_success/11}
     defined in an analysis algorithms. The main differences are that rather
     than adding one element to the list of clauses for the complete, we add the
     list of external calls previously computed for the complete.".
bu_del_call_to_succ(nr,SgKey,Call,Proj,Sg,Sv,AbsInt,Prime,Fs,Id) :-
    proj_to_prime_nr(SgKey, Sg, Sv, Call, Proj, AbsInt, SgKey, Prime, Id), !, % TODO: remove '!'?
    asserta_fact(complete(SgKey, AbsInt, Sg,Proj,Prime,Id,Fs)).
bu_del_call_to_succ(r,SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,Fs,Id) :-
    fixpoint_trace('[incanal] bu fixpoint started',Id,N,SgKey,Sg,Proj,Clauses),
    % proj_to_prime_r processes the non recursive clauses of a recursive predicate
    proj_to_prime_r(SgKey, Sg, Sv, Call, Proj, AbsInt, TempPrime, Id),
    asserta_fact(complete(SgKey, AbsInt, Sg,Proj,TempPrime,Id,[])),
    % IG: asserting a complete with no parents!
    bagof(X, X^(trans_clause(SgKey, r, X)),Clauses), % IG old, moved to the first line
    compute(Clauses,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id),
    ( current_fact('$change_list'(Id,ChList), Ref2) ->
       erase(Ref2),
       fixpoint_compute_change(ChList,SgKey,Sg,Sv,Proj,AbsInt,Prime,NPrime,Id)
    ;
        NPrime = Prime
    ),
    retract_fact(complete(SgKey,AbsInt,A,B,C,Id,Fs2)),
    union(Fs,Fs2,Fs3),
    asserta_fact(complete(SgKey,AbsInt,A,B,C,Id,Fs3)),
    Succ = NPrime,
    fixpoint_trace('[incanal] bu fixpoint completed',Id,N,SgKey,Sg,Proj,Clauses).

%-------------------------------------------------------------------
:- doc(section, "Predicates for running the fixpoint.").

:- export(run_inc_fixpoint/1).
:- pred run_inc_fixpoint(AbsInt) #"This predicate runs fixpoint for
    abstract domain @var{AbsInt}. It is thought to be runned after
    adding information from registry files in intermodular analysis.".
run_inc_fixpoint(AbsInt) :-
    rec_preds(Ps),
    set_pp_flag(widen, on),
    inc_query(dd, AbsInt, Ps), !. % analyzing leaves choicepoints

%  Here we start the top-down incremental analysis. It is the
% same as abs_interpret, but we do not reset fixpoint_id to 0 as that
% may be dangerous (two different completes may get the same number)

inc_plai_add(Cls,Ds,Fixp,AbsInt,_):-
    % initialization
    init_abstract_domain(AbsInt,_Flags),
    do_inc_plai_add(Cls, Ds, Fixp, AbsInt, _, _).

do_inc_plai_add(Cls, Ds, dd, AbsInt, _, _) :-
    %add_packages_if_needed(AbsInt), % TODO: IG: This is for output only
    stat(preproc, inc_add_source_clauses(Cls, Ds, AbsInt)),
    % update the recursivity after new clauses
    stat(td_add, td_mark_add_clauses(Cls, AbsInt)),
    run_inc_fixpoint(AbsInt).

inc_query(dd, AbsInt, Ps) :-
    init_abstract_domain(AbsInt, _Flags), % IG flags is an output var? % fast
    call_inc_fixpoint(dd,AbsInt,Ps), !,
    remove_useless_completes(AbsInt).
inc_query(Fixp, _, _) :-
    ( Fixp = dd ->
        message(error, ['Analysis failed'])
    ;
        message(warning, ['incremental analysis works only for fixpoint dd'])
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
:- pred incrementally_update_analysis(Mod, AbsInt) #" @var{Mod} is the module
    that will be reanalyzed after updating its external
    completes. To be called in modular analysis, no following
    analysis needed. This is a top-down strategy update".
incrementally_update_analysis(Mod, AbsInt) :-
    get_external_completes(Mod, AbsInt, Comps),
    init_rev_idx(AbsInt), % TODO: !!!
    retractall_fact(deleted_comp),
    update_imported_completes(Comps, Mod, AbsInt),
    clean_rev_idx(AbsInt),
    ( deleted_comp -> % optimization to avoid traversing all the graph if no
                      % completes were removed
        remove_useless_completes(AbsInt)
    ;
        true
    ).

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
    ( typeanalysis(AbsInt) -> % TODO: generalize % Importing should be a domain action % TODO: use knows_of/2 (JFMC)
	      imp_auxiliary_info(AbsInt, Dict, [RegProj,RegPrime],[Proj,Prime])
    ;
        Proj = RegProj, Prime = RegPrime
    ),
    abs_sort(AbsInt, Proj, Proj_s),
    apply_changes_imported_comps(Comps,SgKey,Sg,Proj_s,Prime,_RestComps),
    decide_apply_changed_registries(ChRegs, Mod, Comps, Dict).

:- data deleted_comp/0. % This flags is set to avoid computing the reachable
                        % completes if no completes were removed (all are
                        % reachable)

:- pred apply_changes_imported_comps/6 + not_fails.
apply_changes_imported_comps([],_,_,_,_,[]).
apply_changes_imported_comps([Comp|Comps],SgKey,Sg,ImpProj,ImpPrime,Comps) :-
    Comp = complete(SgKey,AbsInt,Sg,Proj,OldPrime,Id,_),
    abs_sort(AbsInt, Proj, Proj_s),
    identical_proj(AbsInt,Sg,ImpProj,Sg,Proj_s), !,
    CNPrime = [ImpPrime],
    % IG this [ImpPrime] list is because registries do not store success
    % patterns as lists (multivariant is not considered for intermod?)
    ( check_same_success(AbsInt, OldPrime, CNPrime) -> % this predicate sorts the abs subs
        true
    ;
        add_external_complete_change(AbsInt, CNPrime, SgKey,Sg,Id,Proj),
        ( each_less_or_equal(AbsInt, CNPrime, OldPrime) -> set_fact(deleted_comp) ; true )
    ).
apply_changes_imported_comps([Comp|Comps], SgKey, Sg, ImpProj, ImpPrime, [Comp|NComps]) :-
    apply_changes_imported_comps(Comps, SgKey, Sg, ImpProj, ImpPrime, NComps).

% TODO: duplicated from fixpo_dd
each_less_or_equal(_, [], []) :- !.
each_less_or_equal(AbsInt, [S1|S1s], [S2|S2s]) :-
    abs_sort(AbsInt,S1,S1_s),
    abs_sort(AbsInt,S2,S2_s),
    less_or_equal(AbsInt, S1_s, S2_s),
    each_less_or_equal(AbsInt, S1s, S2s).

restore_auxinfo_mod(Mod, Dict) :-
    set_fact(restore_module(Mod)),
    restore_auxiliary_info(current_typedb,Dict).

:- use_module(ciaopp(p_unit/p_abs), [curr_mod_entry/4, typedb/2]).

:- data restore_module/1.

% TODO: merge with p_abs:current_typedb/1
current_typedb(TypeDef):-
    current_fact(restore_module(Module)),
    current_fact(typedb(Module,TypeDef)).
