:- module(p_dump,[dump/1,restore/1,restore/2,show_dump/1],[assertions, regtypes, datafacts]).

:- doc(module, "This module contains the machinery for dumping the
    current analysis information to disk and for later restoring
    such information from disk. This has many applications since
    writing the analysis results to disk and later restoring them
    should hopefully be more efficient than reanalizing the module
    from scratch. The information saved to disk can be more or
    less detailed. Sometimes we may be interested in saving only
    part of the information since the missing part can be
    recomputed afterwards. Conceptually, the analysis information
    can be split into three components, the answer table
    (completes), the program point info (memo_table) and the
    dependency table (parent pointers). Note that the last two can
    be efficiently recomputed from the first one, since a fixpoint
    is guaranteed to be found in only one iteration. (to be continued)").

:- use_module(library(conc_aggregates), [findall/3]).
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(messages), [show_message/3]).
:- use_module(library(fastrw), [fast_write/1, fast_read/1]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(library(hiordlib), [maplist/2]).

:- use_module(ciaopp(p_unit/auxinfo_dump)).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

% ---------------------------------------------------------------------------
% Program and analysis database

:- use_module(ciaopp(infer/infer_db), [domain/1, inferred/3]).
:- use_module(ciaopp(plai/plai_db),
    [complete/7, memo_table/6, memo_lub/5, lub_complete/6,
     complete_parent/2, invalid_call/6, raw_success/6]).
:- use_module(ciaopp(plai/fixpo_ops), [iter/1]).

%% --------------------------------------------------------------------

% clauses
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3, cleanup_clause_db/0]).
:- use_module(ciaopp(plai/transform), [trans_clause_/6]).

% assertions
:- use_module(ciaopp(p_unit/assrt_db), [pgm_assertion_read/9]).
:- use_module(ciaopp(plai/apply_assertions),
    [call_asr/5, success_asr/6]). % assertions translated to some domain

% incanal
:- use_module(ciaopp(plai/tarjan), [recursive_classes/1]).
:- use_module(ciaopp(plai/incanal/tarjan_inc),
    [rec/1, vertexes/1, predicates/1, rec_preds/1, tarjan_data/1]).
:- use_module(ciaopp(plai/fixpo_dd), ['$change_list'/2]).
:- use_module(ciaopp(plai/incanal/incanal_db), [update_inc_clid/1, fixpoint_id_/2]).

% TODO: make add_to_db multifile and split in the modules in which
% they are stored

:- export(add_to_db/1).
% plai db
:- pred add_to_db(X) #"Adds any fact to the ciaopp db".
add_to_db(complete(A, B, C, D, E, F, G)) :- !,
    assertz_fact(complete(A, B, C, D, E, F, G)).
add_to_db(memo_table(A, B, C, D, E, F)) :- !,
    assertz_fact(memo_table(A, B, C, D, E, F)).
add_to_db(memo_lub(A, B, C, D, E)) :- !,
    assertz_fact(memo_lub(A, B, C, D, E)).
add_to_db(lub_complete(A, B, C, D, E, F)) :- !,
    assertz_fact(lub_complete(A, B, C, D, E, F)).
add_to_db(complete_parent(A, B)) :- !,
    assertz_fact(complete_parent(A, B)).
add_to_db(invalid_call(A, B, C, D, E, F)) :- !,
    assertz_fact(invalid_call(A, B, C, D, E, F)).
add_to_db(raw_success(A, B, C, D, E, F)) :- !,
    assertz_fact(raw_success(A, B, C, D, E, F)).
add_to_db(domain(A)) :- !,
    assertz_fact(domain(A)).
add_to_db(inferred(A, B, C)) :- !,
    assertz_fact(inferred(A, B, C)).
add_to_db(iter(A)) :- !,  % not necessary?
    assertz_fact(iter(A)).
% source db
add_to_db(source_clause(A, B, C)) :- !,
    assertz_fact(source_clause(A, B, C)).
add_to_db(trans_clause_(A, B, C, D, E, F)) :- !,
    assertz_fact(trans_clause_(A, B, C, D, E, F)).
% Incremental data
add_to_db(rec(A)) :- !,
    assertz_fact(rec(A)).
add_to_db(fixpoint_id_(C,I)) :- !,
    assertz_fact(fixpoint_id_(C,I)).
add_to_db(recursive_classes(A)) :- !,
    assertz_fact(recursive_classes(A)).
add_to_db(vertexes(A)) :- !,
    assertz_fact(vertexes(A)).
add_to_db(tarjan_data(A)) :- !,
    assertz_fact(tarjan_data(A)).
add_to_db(predicates(A)) :- !,
    assertz_fact(predicates(A)).
add_to_db(pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)) :- !,
    assertz_fact(pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)).
add_to_db(call_asr(SgKey, Sg, Status, AbsInt, Call)) :- !,
    assertz_fact(call_asr(SgKey, Sg, Status, AbsInt, Call)).
add_to_db(success_asr(SgKey, Sg, Status, AbsInt, Call,Succ)) :- !,
    assertz_fact(success_asr(SgKey, Sg, Status, AbsInt, Call,Succ)).
add_to_db(X) :-
    show_message(error, "NOT DEFINED IN DUMP ~w\n", [X]),
    fail.

% ---------------------------------------------------------------------------
:- export(dump_dir/1).
:- data dump_dir/1.

:- pred dump(Module, Opts) : (atm(Module), list(Opts))
# "Writes on disk all information related to @var{Module}, so it can
   be restored to continue analysing this module.".
dump(File) :-
    dump(File, []).

:- export(dump/2).
dump(File, Opts):-
    current_pp_flag(dump_pred, PredF),
    current_pp_flag(dump_ext, ExtF),
    current_pp_flag(dump_pp, PPF),
    acc_aux_info_before_write(ExtF, PredF, PPF),
    open(File,write,Stream),
    current_output(O),
    set_output(Stream),
    %
    dump_auxiliary_info(fast_write),
    fast_write(end_of_auxiliary_info),
    ToDump = [plai_db|Xs],
    ( member(incremental, Opts) ->
        Xs = [trans_clause_db, source_clause_db, inc_db, plai_db_extra, assertions]
    ; Xs = []
    ),
    dump_ciaopp_db_data(ToDump, PredF, PPF),
    close(Stream),
    set_output(O).

acc_aux_info_before_write(ExtF, PredF, PPF) :-
    ( % faiure-driven loop
      ( complete(A,B,C,D,E,F,G), Cl = complete(A,B,C,D,E,F,G)
      ; memo_table(A,B,C,D,E,F), Cl = memo_table(A,B,C,D,E,F)
      ),
        data_acc_aux_info(Cl, ExtF, PredF, PPF),
        fail
    ; true ).

data_acc_aux_info(complete(_,_,_,_,_,_,_), _, off, _) :- !.
data_acc_aux_info(memo_table(_,_,_,_,_,_), _, _, off) :- !.
data_acc_aux_info(Cl, ExtF, _, _) :-
    Cl = complete(_,A2,_,A4,A5,ID,_), !,
    ( ExtF = int ->
        (ID \== no),
        acc_auxiliary_info(A2,[A4|A5])
    ;
        acc_auxiliary_info(A2,[A4|A5]),
        ( ExtF = iter ->
            iter(A5)
        ; true
        )
    ).
data_acc_aux_info(Cl, ExtF, _, _) :-
    Cl = memo_table(_,M2,M3,ID,_,M6), !,
    acc_auxiliary_info(M2,M6),
    ( ExtF = int ->
        \+ (ID == no)
    ;
        ( ExtF = iter  ->
            iter(M3)
        ; true )
    ).
data_acc_aux_info(_, _, _, _).

process_before_write(complete(_,_,_,_,_,_), off, _, 'ignored') :- !.
process_before_write(Cl, nodep, _, NCl) :-
    Cl = complete(_,_,_,_,_,_,_), !,
    eliminate_deps_comp(Cl, NCl).
process_before_write(memo_table(_,_,_,_,_), _, off, 'ignored') :- !.
process_before_write(Cl, _, nodep, NCl) :-
    Cl = memo_table(_,_,_,_,_), !,
    eliminate_deps_memo(Cl, NCl).
process_before_write(Cl, _, _, Cl).

eliminate_deps_comp(complete(A1,A2,A3,A4,A5,A6,_), complete(A1,A2,A3,A4,A5,A6,v)).

eliminate_deps_memo(memo_table(M1,M2,M3,M4,_,_), memo_table(M1,M2,M3,M4,v,v)).

:- multifile dump_flags_list/2.
dump_flags_list(dump, [dump_pred ,dump_pp ,dump_ext]).

%% --------------------------------------------------------------------
:- pred restore(Module,Info) :: module * list
   # "Restores from disk analysis information related to
      @var{Module}. It is like call to restore_with_flag( File ,
      current ). @var{Info} returns the time required for this
      process.".
restore(File, [time(T1,[])]):-
    pp_statistics(runtime,_),
    restore_with_flag( File , current ),
    pp_statistics(runtime,[_,T1]),
    pplog(dump, ['{restored analysis in ',~~(T1), ' msec.}']).

:- pred restore(Module) :: module
# "Restores from disk analysis information related to @var{Module}. It
is like call to restore( File , current )".
restore(File):-
    restore(File, _).

:- pred restore_with_flag(Module,Flag) :: module * atom
    # "Restores from disk analysis information related to
       @var{Module}.  Depending on Flag, which can take the values
       @tt{current} and @tt{prev}, it restores disk analysis
       information into complete or complete_prev respectively".
restore_with_flag(File, F) :-
    open(File,read,Stream),
    current_input(O),
    set_input(Stream),
    restore_auxiliary_info(restore_aux, Dict),
    ( fast_read(T)  ->
        read_all_terms(T, Dict, F)
    ; true
    ),
    close(Stream),
    set_input(O).

% backtrackable and failing at end:
restore_aux(X):-
    repeat,
      ( fast_read(X)
      -> true
       ; !, 
         fail
      ).

% TODO: This should be generic
read_all_terms(end_of_file, _Dict, _Flag) :- !.
read_all_terms(end_of_auxiliary_info, Dict, Flag) :-
    fast_read(X),!,
    read_all_terms(X, Dict, Flag).
read_all_terms(T0, Dict, Flag) :-
    process_after_read(T0, T_to_check, Dict),
    ( Flag == current ->
        T = T_to_check
    ;
        T_to_check =.. [T_Func|T_Args],
        rename_pred(T_Func, T_New),
        T =.. [T_New|T_Args]
    ),
    add_to_db(T),
    fast_read(X),!,
    read_all_terms(X, Dict, Flag).
% if fast read fails, we have to finish.
read_all_terms(_, _, _).

rename_pred(complete, complete_prev). 
rename_pred(memo_table, memo_table_prev). 

process_after_read(complete(A1,A2,A3,A4,A5,A6,A7), T, Dict) :- !,
    T = complete(A1,A2,A3,Proj,Primes,A6,A7),
    imp_auxiliary_info(A2,Dict,[A4|A5],[Proj|Primes]).
process_after_read(memo_table(M1,M2,M3,M4,v,v), T, _Dict) :- !,
    T = memo_table(M1,M2,M3,M4,v,v).
process_after_read(memo_table(M1,M2,M3,M4,M5,M6), T, Dict) :- !,
    T = memo_table(M1,M2,M3,M4,M5,Call),
    imp_auxiliary_info(M2,Dict,M6,Call).
process_after_read(T, T, _) :-
    T = source_clause(Clid, _, _), !,
    update_inc_clid(Clid).
process_after_read(T, T, _Dict).

%% --------------------------------------------------------------------

show_dump(File) :-
    open(File,read,Stream),
    current_input(O),
    set_input(Stream),
    read_and_show,
    close(Stream),
    set_input(O).

read_and_show :-
    fast_read(T),
    display(T), nl, nl,
    read_and_show.
read_and_show.

:- regtype module/1.

module(X) :- atm(X).

:- export(clean_all_ciaopp_db/0).
:- doc(clean_all_ciaopp_db/0, "Cleans all ciaopp databases").
clean_all_ciaopp_db :-
    ( % failure-driven loop
      clean_ciaopp_db(_),
        fail
    ; true).

% TODO: This predicate should be a multifile
:- export(clean_ciaopp_db/1).
:- pred clean_ciaopp_db(X) : atm(X)
    #"Cleans all the data related to @var{X}.".
clean_ciaopp_db(plai_db) :-
    retractall_fact(domain(_)),
    retractall_fact(complete(_,_,_,_,_,_,_)),
    retractall_fact(inferred(_,_,_)),
    retractall_fact(memo_table(_,_,_,_,_,_)).
clean_ciaopp_db(plai_db_extra) :-
    retractall_fact(memo_lub(_,_,_,_,_)),
    retractall_fact(lub_complete(_,_,_,_,_,_)),
    retractall_fact(complete_parent(_,_)),
    retractall_fact(invalid_call(_,_,_,_,_,_)),
    retractall_fact(raw_success(_,_,_,_,_,_)).
clean_ciaopp_db(source_clause_db) :-
    retractall_fact(source_clause(_,_,_)).
clean_ciaopp_db(trans_clause_db) :-
    retractall_fact(trans_clause_(_,_,_,_,_,_)).
clean_ciaopp_db(inc_db) :-
    retractall_fact(vertexes(_)),
    retractall_fact(recursive_classes(_)),
    retractall_fact(tarjan_data(_)),
    retractall_fact(predicates(_)),
    retractall_fact(rec(_)),
    retractall_fact(fixpoint_id_(_,_)).
clean_ciaopp_db(assertions) :-
    retractall_fact(pgm_assertion_read(_,_,_,_,_,_,_,_,_)),
    retractall_fact(call_asr(_,_,_,_,_)),
    retractall_fact(success_asr(_,_,_,_,_,_)).

dump_ciaopp_db_data(DBs, PredF, PPF) :-
    ( % failure-driven loop
      member(DB, DBs),
      ( get_data(DB, Cl),
          process_before_write(Cl, PredF, PPF, NCl),
          \+ NCl = 'ignored',
          fast_write(Cl), fail
      ; true
      ),
      fail
    ; true).

:- export(get_data/2).
:- pred get_data(DB, Data) :: atm(DB)
    #"This predicate enumerates the data in a database @var{DB}.".
%%%%%% plai db %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_data(plai_db, Cl) :-
    current_fact(domain(A)),
    Cl = domain(A).
get_data(plai_db, Cl) :-
    current_fact(complete(A, B, C, D, E, F, G)),
    Cl = complete(A, B, C, D, E, F, G).
get_data(plai_db, Cl) :-
    current_fact(inferred(A, B, C)),
    Cl = inferred(A, B, C).
get_data(plai_db, Cl) :-
    current_fact(memo_table(A, B, C, D, E, F)),
    Cl = memo_table(A, B, C, D, E, F).
%%%%%% source_clause db %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_data(source_clause_db, Cl) :-
    current_fact(source_clause(A, B, C)),
    Cl = source_clause(A, B, C).
%%%%%% trans clause db %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_data(trans_clause_db, Cl) :-
    current_fact(trans_clause_(A, B, C, D, E, F)),
    Cl = trans_clause_(A, B, C, D, E, F).
%%%%%% incremental db %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_data(inc_db, Cl) :-
    current_fact(recursive_classes(A)),
    Cl = recursive_classes(A).
get_data(inc_db, Cl) :-
    current_fact(vertexes(A)),
    Cl = vertexes(A).
get_data(inc_db, Cl) :-
    current_fact(tarjan_data(A)),
    Cl = tarjan_data(A).
get_data(inc_db, Cl) :-
    current_fact(predicates(A)),
    Cl = predicates(A).
get_data(inc_db, Cl) :-
    current_fact(rec(A)),
    Cl = rec(A).
get_data(inc_db, Cl) :-
    current_fact(fixpoint_id_(C,I)),
    Cl = fixpoint_id_(C,I).
%%%%%% plai db extra %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_data(plai_db_extra, Cl) :-
    current_fact(memo_lub(A, B, C, D, E)),
    Cl = memo_lub(A, B, C, D, E).
get_data(plai_db_extra, Cl) :-
    current_fact(lub_complete(A, B, C, D, E, F)),
    Cl = lub_complete(A, B, C, D, E, F).
get_data(plai_db_extra, Cl) :-
    current_fact(complete_parent(A, B)),
    Cl = complete_parent(A, B).
get_data(plai_db_extra, Cl) :-
    current_fact(invalid_call(A, B, C, D, E, F)),
    Cl = invalid_call(A, B, C, D, E, F).
get_data(plai_db_extra, Cl) :-
    current_fact(raw_success(A, B, C, D, E, F)),
    Cl = raw_success(A, B, C, D, E, F).
%%%%%% assertions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_data(assertions, Cl) :-
    current_fact(pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)),
    Cl = pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE).
get_data(assertions, Cl) :-
    current_fact(call_asr(SgKey, Sg, Status, AbsInt, Call)),
    Cl = call_asr(SgKey, Sg, Status, AbsInt, Call).
get_data(assertions, Cl) :-
    current_fact(success_asr(SgKey, Sg, Status, AbsInt, Call,Succ)),
    Cl = success_asr(SgKey, Sg, Status, AbsInt, Call,Succ).
