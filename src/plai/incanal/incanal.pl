:- module(incanal, [
    incremental_module/1,
    incremental_module/2,
    incremental_analyze/1,
    incremental_analyze/2,
    reset_incremental_analysis_info/0
    ], [assertions, regtypes, datafacts, nativeprops]).

:- doc(title, "Incremental analysis (high level)").

:- doc(stability, devel).

:- doc(module, "This module implements a high level interface of
incremental analysis (see @lib{incanal_driver} for the low level interface).

@section{Usage}

@bf{Important:} For using incremental analysis some ciaopp flags have to be set:

@begin{verbatim}
?- set_pp_flag(fixpoint, dd),
   set_pp_flag(incremental, on).
@end{verbatim}

@begin{enumerate}

@item (Re)Load a list of modules to be analyzed with
@pred{incremental_module/1} (or @pred{incremental_module/2} to get
statistics). It can be done several times before reanalyzing.

@item (Re)Analyze the code with @pred{incremental_analyze/1} (or
@pred{incremental_analyze/2} to get statistics). Internally, the
changes will be automatically incrementally applied.

This predicate depends on the ciaopp flag @code{del_strategy} for
incremental deletion.

@end{enumerate}

@begin{note}
@bf{Note:} If a module is not present in the reloading list, it is
assumed that it has been removed from analysis so all modules must be
in the input list although they may have not changed.
@end{note}

@begin{alert}
@bf{Tip (under construction!!):} If you want to quickly display the
information inferred by the analyzer between analyses you can:
@end{alert}

@begin{verbatim}
?- use_module(ciaopp(raw_printer)).
?- show_analysis.
@end{verbatim}

@section{Example}

Example of incremental analysis for file @tt{foo.pl}

@begin{verbatim}
:- module(foo, [p/1], []).

p(1).
p(3).
@end{verbatim}

Incremental analysis from Ciao toplevel:

@begin{verbatim}
?- use_module(ciaopp(plai/incanal)), use_module(ciaopp(preprocess_flags)).

yes
?- % incremental flags
   set_pp_flag(fixpoint, dd),
   set_pp_flag(incremental, on).

yes
?- incremental_module(foo, T).

T = [time(317.96,[])] ?

yes
?- incremental_analyze(eterms, T).

T = [proc_diff(0.244),add(2.281),delete(0.001)] ?

yes
% reload changes:
?- incremental_module(foo, T).

T = [time(299.822,[])] ?

yes
?- incremental_analyze(eterms, T).
{Incrementally analyzed with dd for eterms }

T = [proc_diff(0.314),add(2.148),delete(2.797)] ?

yes
@end{verbatim}

@section{Side effects}

As a result of the incremental analysis, auxiliary files are generated
for each analyzed module:

@begin{itemize}
@item When loaded a module: @tt{File.itf}.
@item When analyzed a module: @tt{File.dump}.
@end{itemize}

They are used to detect if changes were made in a module. To reset the
incremental analysis these files have to be removed.

@begin{alert}
@bf{WARNING}: There might be problems with clause locators because Ids
generated when transforming the code can be modified.
@end{alert}
    ").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(bug, "Call compiler to avoid reloading a source that did not change.").
% This checking could be controlled by a flag

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(diff), [diff/4, patch/3]).
:- use_module(library(pathnames), [path_basename/2]).

:- use_module(ciaopp(frontend_driver), [module/2]).
:- use_module(ciaopp(analyze_driver), [clean_analysis_info/0]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2, set_pp_flag/2]).
:- use_module(ciaopp(p_unit/clause_db), [cleanup_clause_db/0]).
:- use_module(ciaopp(plai/fixpo_dd), ['$change_list'/2]).
:- use_module(typeslib(typeslib), [cleanup_types/0]).

% incanal
:- use_module(ciaopp(plai/incanal/incanal_driver)).
:- use_module(ciaopp(plai/incanal/incanal_db)).
:- use_module(ciaopp(plai/incanal/incanal_persistent_db)).
:- use_module(ciaopp(plai/incanal/tarjan_inc), [inc_add_source_clauses/3]).
:- use_module(ciaopp(plai/apply_assertions_inc)).

:- use_module(ciaopp(analysis_stats),
    [stat/2, gather_stats/2, pretty_print_stats/1]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- pred reset_incremental_analysis_info/0 #"Resets incremental and regular ciaopp
    internal data structures.".
reset_incremental_analysis_info :-
    clean_incremental_db,
    reset_persistent_db,
    analyze_driver:clean_analysis_info,
  cleanup_applied_assertions_inc(_).

:- data last_diff_key/1.
:- data last_diff_cl/2.
:- data last_diff_as/2.

:- pred incremental_module(Files) : list + not_fails #"Loads and transforms the
    code of @var{Files} to the ciaopp code database, computing the
    differences with the code previously present".
incremental_module(Files) :-
    incremental_module(Files, _).

:- pred incremental_module(Files, Stats) : list(Files) => list(Stats) + not_fails
    #"Same as @pred{incremental_module/1} but returns runtime
     statistics in @var{Stats}.".
incremental_module(Files, Stats) :-
    incremental_module_(Files, S1),
    gather_stats(module, S2),
    append(S1, S2, Stats).

incremental_module_(Files, Stats) :-
    update_modules(Files, Stats),
    set_loaded_mods(Files).

% Like simple_module/2 but extract list of changes on program clauses
% (rather than modifying the clause db)
% assuming that type definitions do not change
% TODO: Possible missing type definitions
update_modules(Files, Stats) :- % Reload files (keeps prev analysis)
    clean_analysis_info,
    cleanup_types,
    simple_module(Files, Stats),
    get_current_clauses(NCls),
    get_current_assertions(NAssrts),
    top_level_of_files(Files, Top),
    set_loaded_module(Top),
    ( has_dump(Top, _) ->
        init_empty_inc_analysis,
        load_persistent_if_needed(Top,Files), % restore previous analysis
        get_current_clauses(OldCls),
        get_current_assertions(OldAssrts),
        save_clause_db
    ;
    OldCls = [],
    OldAssrts = []
    ),
    stat(comp_diff, preds_diff(OldCls, NCls, Diff)),
    stat(comp_diff_as, assrts_diff(OldAssrts, NAssrts, ADiff)),
    set_last_diff(Diff,ADiff).

% This is done with assert/retract of several data facts because we do
% not want to assert huge terms (because of limitations of the number
% of variables that a fact can contain in Ciao).
set_last_diff(Diff,ADiff) :-
    retractall_fact(last_diff_key(_)),
    retractall_fact(last_diff_cl(_,_)),
  retractall_fact(last_diff_as(_,_)),
    ( member(diff(Key,Cls),Diff),
        assertz_fact(last_diff_key(Key)),
        ( member(Cl, Cls),
            assertz_fact(last_diff_cl(Key, Cl)),
      fail
        ; true
        ),
        fail
    ; true
    ),
  ( member(diff(Key,As),ADiff),
      add_change_predkey(Key),
        ( member(A, As),
            assertz_fact(last_diff_as(Key,A)),
      fail
        ; true
        ),
        fail
    ; true
    ).

get_last_diff(ClDiff,ADiff) :-
    findall(K, last_diff_key(K), Keys),
    get_last_diff_keys_cl(Keys, ClDiff),
  get_last_diff_keys_as(Keys, ADiff).

get_last_diff_keys_cl([], []).
get_last_diff_keys_cl([Key|Keys], [diff(Key, Cls)|Diffs]) :-
    findall(Cl, last_diff_cl(Key, Cl), Cls),
    Cls \= [], !,
    get_last_diff_keys_cl(Keys, Diffs).
get_last_diff_keys_cl([_|Keys], Diffs) :-
    get_last_diff_keys_cl(Keys, Diffs).

get_last_diff_keys_as([], []).
get_last_diff_keys_as([Key|Keys], [diff(Key, As)|Diffs]) :-
    findall(A, last_diff_as(Key, A), As),
    As \= [], !,
    get_last_diff_keys_as(Keys, Diffs).
get_last_diff_keys_as([_|Keys],Diffs) :-
    get_last_diff_keys_as(Keys, Diffs).

simple_module(Files, Stats) :-
    init_empty_inc_analysis,
    set_pp_flag(incremental, off),
    module(Files, Stats),     % regular non-incremental module
    set_pp_flag(incremental, on).

:- data incremental_load_mode/1. % TODO: move to preprocess_flags ?
incremental_load_mode(clean).

:- export(config_incremental_load/1).
:- pred config_incremental_load(X) : load_config.
config_incremental_load(X) :-
    set_fact(incremental_load_mode(X)).
% By default load cleans all previous information, loads the modules,
% restores the previous persistent info for those modules

:- regtype load_config/1.
load_config(clean).
load_config(keep).

:- pred preds_diff(Cls1, Cls2, Diff) #"Calculates the differences of clauses for
    each predicate separately".
preds_diff([], [], []) :- !.
preds_diff([], Cls2, [diff(new_preds, Cls2)]). % New preds (all additions)
preds_diff([Cl|Cls1], Cls2, TotalDiff) :-
    Cl = (_Clid, clause(H, _B), _Dic),
    functor(H, F, A),
    all_clauses_pred(Cls1, F/A, PredCls1, NCls1),
    all_clauses_pred(Cls2, F/A, PredCls2, NCls2),
    clauses_diff([Cl|PredCls1], PredCls2, PredDiff),
    ( PredDiff = [] ->
        TotalDiff = RestDiff
    ;
        TotalDiff = [diff(F/A,PredDiff)|RestDiff]
    ),
    preds_diff(NCls1, NCls2, RestDiff).

clauses_diff(Cls1, Cls2, Diff) :-
    diff(Cls1, Cls2, same_clause, Diff).

all_clauses_pred([], _/_, [], []).
all_clauses_pred([Cl|Cls], F/A, PredCls, NCls) :-
    Cl = (_Clid, clause(H, _), _),
    ( functor(H, F, A) ->
        PredCls = [Cl|PredCls1],
        NCls = NCls1
    ;
        PredCls = PredCls1,
        NCls = [Cl|NCls1]
    ),
    all_clauses_pred(Cls, F/A, PredCls1, NCls1).

:- use_module(ciaopp(p_unit/assrt_db), [pgm_assertion_read/9]).

:- pred assrts_diff(Assrts1, Assrts2, Diff) #"Computes the differences of
    assertions for each predicate separately".
assrts_diff([], [], []) :- !.
assrts_diff([], Assrts, [diff(new_preds, Assrts)]). % New preds (all additions)
assrts_diff([A|As1], As2, Diff) :-
    A = pgm_assertion_read(Goal,_M,_Status,_Type,_Body,_,_,_,_),
    functor(Goal, F, N),
    all_assertions_pred(As1, F/N, PredAs1, NAs1),
    all_assertions_pred(As2, F/N, PredAs2, NAs2),
    assertions_diff([A|PredAs1], PredAs2, PredADiff),
    ( PredADiff = [] ->
        Diff = RestDiff
    ;
        Diff = [diff(F/N,PredADiff)|RestDiff]
    ),
    assrts_diff(NAs1, NAs2, RestDiff).

assertions_diff(As1, As2, Diff) :-
    diff(As1, As2, same_assertion, Diff).

% comparing syntactically
same_assertion(A1,A2) :-
    \+ \+ same_assertion_(A1,A2).

same_assertion_(A1,A2) :-
    A1 = pgm_assertion_read(Goal,M,Status,Type,Body,_,_,_,_),
    A2 = pgm_assertion_read(Goal,M,Status,Type,Body,_,_,_,_).

:- export(all_assertions_pred/4).
all_assertions_pred([], _/_, [], []).
all_assertions_pred([A|As], F/N, PredAs, NAs) :-
    A = pgm_assertion_read(Goal,_,_,_,_,_,_,_,_),
    ( functor(Goal, F, N) ->
        PredAs = [A|PredAs1],
        NAs = NAs1
    ;
        PredAs = PredAs1,
        NAs = [A|NAs1]
    ),
    all_assertions_pred(As, F/N, PredAs1, NAs1).

% TODO: change by PredKey?
add_change_pred(Key,Change) :-
    add_change_predkey(Key),
    assertz_fact(last_diff_cl(Key, Change)).

add_change_predkey(Key) :-
    last_diff_key(Key), !.
add_change_predkey(Key) :-
    assertz_fact(last_diff_key(Key)).

% ----------------------------------------------------------------------
:- doc(section, "Incremental analysis").

:- pred incremental_analyze(AbsInt) : atm(AbsInt) #"Applies @var{Diff}
    to the current analysis by performing all deletions according
    to the deletion strategy set the ciaopp flag (@tt{top_down} or
    @tt{bottom_up}), reanalyzing and adding all clauses and assertions after.".
incremental_analyze(AbsInt) :-
    incremental_analyze(AbsInt, _).

:- pred incremental_analyze(AbsInt, Stats) : atm(AbsInt) => list(Stats) + not_fails
    #"Same as @pred{incremental_analyze/1} but returns runtime
     statistics in @var{Stats}. Statistics are divided in:

     @begin{itemize}
     @item @tt{proc_diff}: Time needed to apply the differences to the
           incremental database.
     @item @tt{add}: Time needed for performing the addition of clauses.
     @item @tt{delete}: Time needed for performing the deletion of clauses
           according to the selected deletion strategy.
     @end{itemize}".
incremental_analyze(AbsInt, Stats) :-
    stat(proc_diff, process_diff(ProcDiff,ADiff)),
    extract_cl_diff_info(ProcDiff, Additions, Deletions),
    loaded_mods(Context),
    restore_change_list(Context),
    restore_fixpoint_id(Context), % fixpoint id necessary for updating assertions
    stat(proc_assrts,update_all_assertions_analysis(ADiff,AbsInt)),
    modular_actions(AbsInt),
    % Updating LAT needs to be here or otherwise it would overwrite the computation made by bu_delete_clauses
    ( current_pp_flag(del_strategy, top_down) ->
        td_delete_clauses(Deletions, AbsInt)
    ;
        bu_delete_clauses(Deletions, AbsInt)
    ),
    td_add_clauses(Additions, AbsInt),
    analysis_actions(AbsInt, Additions, Deletions), % run fixpo if not done before on delete or add
    store_current_fixpoint_id(Context),
    message(inform, ['{Incrementally analyzed with dd for ', ~~(AbsInt), ' }']),
    save_persistent_analysis,
    store_change_list(Context),
    gather_stats(analysis, Stats),
    pretty_print_stats(Stats). % TODO: show in a nicer way

:- data local_change_list/3.
store_change_list(Context) :-
    retractall_fact(local_change_list(Context, _, _)),
    ( % failure-driven loop
        '$change_list'(A, B),
        assertz_fact(local_change_list(Context, A, B)),
        fail
    ; true).
restore_change_list(Context) :-
    retractall_fact('$change_list'(_, _)),
    ( % failure-driven loop
        local_change_list(Context, A, B),
        assertz_fact('$change_list'(A, B)),
        fail
    ; true).

:- pred analysis_actions(AbsInt, Adds, Dels) #"These actions are needed because
    intermodular analysis changes the state of the completes
between incremental reanalysis.".
% TODO: review this predicate for changes only in assertions monolithic
analysis_actions(AbsInt, [], _) :-
    \+ current_pp_flag(intermod, off),
    % find a better way for detecting monolithic
    current_pp_flag(del_strategy, bottom_up), !,
    % This is needed for bottom_up because new entries that were not considered can be added
    run_inc_fixpoint(AbsInt).  % This also adds the entries to the GAT
analysis_actions(AbsInt, [], []) :- % run fixpoint if there were no changes
    \+ current_pp_flag(intermod, off), !,
    run_inc_fixpoint(AbsInt).
analysis_actions(_, _, _) :- !. % do not run fixpoint if it is not modular

modular_actions(AbsInt) :-
    \+ current_pp_flag(intermod, off),
    loaded_mods([ModPath]), !, % only one module was loaded => it is modular
    % TODO: improve this checking
    path_basename(ModPath,Mod),
    stat(upd_lat, incrementally_update_analysis(Mod, AbsInt)).
modular_actions(_).

process_diff(ClProcDiff,ADiff) :- 
    get_last_diff(ClDiff, ADiff), % assertions do not need processing (no conflicting ids)
    apply_diff_cl(ClDiff, ClProcDiff),
    apply_diff_as(ADiff),
    cleanup_clause_db,
    restore_clause_db.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

apply_diff_cl([], []).
apply_diff_cl([diff(new_preds, Cls)|Diffs], [diff(new_preds, Cls)|NDiff]) :- !,
    % only additions
    add_new_preds(Cls),
    apply_diff_cl(Diffs, NDiff).
apply_diff_cl([diff(F/A, PredDiff)|Diffs], [diff(F/A, NDiff1)|NDiff]) :-
    apply_diff_pred(F/A, PredDiff, NDiff1),
    apply_diff_cl(Diffs, NDiff).

:- pred apply_diff_pred(F/A, DiffList, ProcDiff) : list(DiffList) => list(ProcDiff)
    #"Asserts based on the change list @var{DiffList},
    @var{ProcDiff} is the diff after it has been processed,
    i.e. conficting ids have been solved".
apply_diff_pred(_, [], []) :- !.
apply_diff_pred(F/A, Diff, NDiff) :-
    remove_clauses_pred(F/A, Cls), % retracts those clauses
    change_diff_ids(Diff, NDiff),
    patch(Cls, NDiff, NewCls),
    add_all_clauses(NewCls).

change_diff_ids([], []).
change_diff_ids([ins(P, Cl)|Diff], [ins(P, NCl)|NDiff]) :- !,
    change_id_clause(Cl, NCl),
    change_diff_ids(Diff, NDiff).
change_diff_ids([D|Diff], [D|NDiff]) :-
    change_diff_ids(Diff, NDiff).

extract_cl_diff_info([], [], []) :- !.
extract_cl_diff_info([diff(new_preds, Ad)|Diffs], Additions, Ds) :- !,
    extract_diff_new_pred_info(Ad, Clids),
    append(Clids, As, Additions),
    extract_cl_diff_info(Diffs, As, Ds).
extract_cl_diff_info([diff(_Pred, L)|Diffs], Additions, Deletions) :-
    extract_cl_diff_info_pred(L, Add, Del),
    append(Add, As, Additions),
    append(Del, Ds, Deletions),
    extract_cl_diff_info(Diffs, As, Ds).

extract_diff_new_pred_info([], []).
extract_diff_new_pred_info([(Clid, _, _)|Cls], [Clid|Clids]) :-
    extract_diff_new_pred_info(Cls, Clids).

extract_cl_diff_info_pred([], [], []).
extract_cl_diff_info_pred([ins(_, (Clid, _, _))|Diff], [Clid|Add], Del) :- !,
    extract_cl_diff_info_pred(Diff, Add, Del).
extract_cl_diff_info_pred([del(_, (Clid, _, _))|Diff], Add, [Clid|Del]) :-
    extract_cl_diff_info_pred(Diff, Add, Del).

% ------------------------------------------------------------
:- doc(section, "Processing changes in assertions").

apply_diff_as(As) :-
    ( member(diff(new_preds,Assrts), As) ->
      ( member(A,Assrts),
          add_assertion_source_db(A),
          fail
      ;  true
      )
      ; true
    ),
    ( % failure-driven loop
      member(diff(_Pred,Assrts1), As),
        ( % failure-driven loop
          member(E, Assrts1),
            ( E = ins(_, A) -> 
                add_assertion_source_db(A)
            ; E = del(_, A) ->
                del_assertion_source_db(A)
            ),
            fail
        ; true
        ),
        fail
    ; true
    ).

update_all_assertions_analysis([],_).
update_all_assertions_analysis([diff(new_preds, Assrts)|Diffs],AbsInt) :- !,
    split_new_preds(Assrts, SAssrts),
    update_all_assertions_analysis(SAssrts,AbsInt),
    update_all_assertions_analysis(Diffs,AbsInt).
update_all_assertions_analysis([diff(Pred, Assrts)|Diffs],AbsInt) :-
    update_assertions_pred(Pred, AbsInt, Assrts),
    update_all_assertions_analysis(Diffs,AbsInt).

split_new_preds([],[]).
split_new_preds([A|As], [diff(F/N,Assrts)|APreds]) :-
    A = pgm_assertion_read(Goal,_M,_Status,_Type,_Body,_,_,_,_),
    functor(Goal, F, N),
    all_assertions_pred([A|As], F/N, PredAssrts, NAs),
    format_insert(PredAssrts, Assrts),
    split_new_preds(NAs, APreds).

format_insert([], []).
format_insert([A|As], [ins(_,A)|IAs]) :-
    format_insert(As, IAs).

% ----------------------------------------------------------------------
:- doc(section, "Predicates for comparison in diff algorithm").
% TODO: move?

:- pred same_clause(+Cl1, +Cl2) #"This predicate succeeds if @var{Cl1}
    and @var{Cl2} are the same clause, if a variable is renamed,
    the clauses are considered the same.".
same_clause(Cl1, Cl2) :-
    Cl1 = (_Cl1id, clause(H1, B1), dic(_Vs1, _VsNames1)),
    % Diff in names does not affect
    Cl2 = (_Cl2id, clause(H2, B2), dic(_Vs2, _VsNames2)),
    same_head(H1, H2, HVars),
    same_body(B1, B2, HVars, _BVars).

% This predicate performs like variant but removing clids
:- pred same_head(+OH, +NH, -LCorresponds) #"@var{LCorresponds} is the
    list of pairs of variables that correspond between the two heads.".
same_head(OH, NH, LCorresponds) :-
    equivalent_term_list([OH], [NH], [], LCorresponds).

equivalent_term_list([], [], Vars, Vars).
equivalent_term_list([T1|LT1], [T2|LT2], Vars, NVars) :-
    var(T1), var(T2), !,
    ( appeared(T1, Vars) -> 
        T1 == T2,      % It was previously unified
        equivalent_term_list(LT1, LT2, Vars, NVars)
    ;
        T1 = T2,
        equivalent_term_list(LT1, LT2, [T1|Vars], NVars)
    ).
equivalent_term_list([T1|LT1], [T2|LT2], Vars, NVars) :- % They have a struct
    nonvar(T1), nonvar(T2), !,
    T1 =.. [H|T1Args],
    T2 =.. [H|T2Args],
    equivalent_term_list(T1Args, T2Args, Vars, Vars1),
    equivalent_term_list(LT1, LT2, Vars1, NVars).

appeared(V, [V1|_]) :- % member cannot be used because it unifies
    V == V1, !.
appeared(V, [_|L]) :-
    appeared(V, L).

:- pred same_body(+B1, +B2, +LCorr, -NCorr) #"".
same_body((!), (!), Vars, Vars) :- !.
same_body(Lit1:_Id, Lit2:_NId, Vars, NVars) :- !,
    equivalent_term_list([Lit1], [Lit2], Vars, NVars).
same_body((Lit1:_Id, B1), (Lit2:_NId, B2), Vars, NVars) :- !,
    equivalent_term_list([Lit1], [Lit2], Vars, Vars1),
    same_body(B1, B2, Vars1, NVars).
same_body((!, B1), (!, B2), Vars, NVars) :-
    same_body(B1, B2, Vars, NVars).

% ----------------------------------------------------------------------
%
% Code for testing adding/removing clauses in incremental tarjan
% (source transformations, without analysis)
%
% :- use_module(ciaopp(plain/incanal/incanal_driver), [sources_from_clids/3]).
% % for testing adding in tarjan
% :- export(inc_update_source_db/1).
%
% :- pred inc_update_source_db(AbsInt) : atm #"This predicates updates
%       only the source code db with a previously calculated diff, but
%       does not perform any analysis.".
% inc_update_source_db(AbsInt) :-
%       process_diff(ProcDiff),
%       extract_cl_diff_info(ProcDiff, Clids, _),
%       sources_from_clids(Clids, Cls, Ds),
%       inc_add_source_clauses(Cls, Ds, AbsInt),
%       save_persistent_analysis.
