:- module(ciaopp_worker, [start_worker/1], [assertions, modes, regtypes, datafacts]).

:- doc(title, "Worker for CiaoPP batch processing").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, " 
This module implements an execution mode for CiaoPP as a worker for
@apl{ciaopp-batch} (using @lib{ciaopp_batch(db_analysis)} for
communication).

Note that this tool has to be used with an external timeout because
the analysis of some modules could require too much memory or time to
be performed. It must be used with @ref{Analysis management
predicates}.

@section{Generated data}

@begin{itemize} 

@item Analysis information: For each module abstract analysis
  information is stored in a @tt{.dump} file generated in the same
  location. This information and can be restored later.

@item Run-time statistics: Statistics of time and memory used are
  stored in as a term in a @tt{.err} file in the same location as the
  original module. This file contains also the output of the analyzer.

@item Status of the analysis: For each module, information of load and
  analysis success is stored in @tt{data/task_status.pl}.

  This allows also the script to be incremental, i.e., it does not
  repeat ciaopp analysis for a module if it has already been done.

  If the the user wants the tool to redo an analysis for all files,
  @tt{task_status.pl} has to be removed before starting.

@item @tt{last_analyzed_file.pl}: This file contains the file that is
  being analyzed.

@end{itemize}
").

:- use_module(library(lists), [append/3]).
:- use_module(library(system), [mktemp_in_tmp/2, get_pid/1]).
:- use_module(library(system_extra), [del_file_nofail/1]).
:- use_module(library(port_reify), [once_port_reify/2]).
:- use_module(library(io_alias_redirection), [set_stream/3]).
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(stream_utils), [file_to_string/2]).
:- use_module(library(read), [read/2]).

:- use_module(ciaopp(frontend_driver), [module/2,ensure_libcache_loaded/0]).
:- use_module(ciaopp(analyze_driver), [analyze/2]).
:- use_module(ciaopp(preprocess_flags), [set_pp_flag/2]).
:- use_module(ciaopp(p_dump), [dump/2]).

:- use_module(ciaopp_batch(ciaopp_batch_aux)).

% TODO: This should be taken from the Flags variable
:- include(ciaopp_batch(analyze_opts)).
:- use_module(ciaopp_batch(tasks_db)).

% ---------------------------------------------------------------------------
% (analysis database)

:- use_module(ciaopp_batch(db_analysis)).

% ---------------------------------------------------------------------------

:- doc(section, "Predicates for launching ciaopp_worker as an application").

:- data worker_ID/1.
:- data priority_file/1.

start_worker(LogID) :- !,
    set_fact(worker_ID(LogID)),
    init_tmp_db(LogID),
    % set_pp_flag(use_libcache, on), % (enabled by default)
    ensure_libcache_loaded,
    treat_all.

% ---------------------------------------------------------------------------
:- pred treat_all
    #"Analyzes with priority module files in @var{Files}
    then modules in DB are analyzed.".
treat_all:-
    update_task_status, % not needed ?
    add_priority_tasks,
    analyze_files.

add_priority_tasks :-
    repeat,
    ( read(user_input, X), \+ X = end_of_file ->
        X = treat(File,Mod,AbsInt,Flags),
        assertz_fact(priority_file(treat(File,Mod,AbsInt,Flags))),
        fail
    ; !
    ).

analyze_files :-
    ( retract_fact(priority_file(treat(File,Mod,AbsInt,Flags))) ->
        true
    ;
        pop_task(File,Mod,AbsInt,Flags)
    ),
    worker_ID(ID),
    set_current_task(ID, treat(File, Mod, AbsInt, Flags)),
    analyze_single_file(pl(File,Mod), AbsInt, Flags),
    fail.
analyze_files :-
    display('All modules analyzed'), nl.

:- pred analyze_single_file(Module, AbsInt, Flags) : term * atom * term
    #"Analyzes @var{ModName} in @var{FilePath} and outputs the analysis
     status in @var{StatusStream}. Generates a file in @var{FilePath} 
    directory with the output of the analysis and run-time statistics and
    a file with a dump of the analysis.".
analyze_single_file(pl(FilePath, ModName), AbsInt, Flags) :-
    find_set_pp_flags,
    load_and_diagnose(FilePath, LSt, LDiag),
    display(load_and_diagnose(FilePath, LSt, LDiag)), nl,
    ( LSt = ok ->
        ( task_status(ModName, _, module, Flags, ok) -> true
        ; add_task_status(ModName, FilePath, module, Flags, ok)
        ),
        analyze_and_diagnose(AbsInt, Flags, St, ADiag),
        ( \+ St = ok ->
             add_task_status(ModName, FilePath, AbsInt, Flags, err)
        ;
            dump_file(FilePath, ModName, AbsInt, DumpFilePath),
            dump(DumpFilePath, [incremental]),
            ( task_status(ModName, _, AbsInt, Flags, ok) -> true
            ; add_task_status(ModName, FilePath, AbsInt, Flags, ok)
            )
        )
    ;
        add_task_status(ModName, FilePath, module, Flags, err),
        ADiag = diagnosis(AbsInt, skip, "", "", "")
    ),
    Diagnosis = [LDiag, ADiag],
    report_mod_info(FilePath, ModName, Diagnosis).

:- pred load_and_diagnose(+FilePath, -Status, -D).
load_and_diagnose(FilePath, Status, D) :-
    logged_once_port_reify(module(FilePath, LInfo), MPort, LOutStr, LErrStr),
    ( (\+ MPort = success ; string_contained("ERROR", LErrStr)) ->
      Status = err ; Status = ok),
    ( var(LInfo) -> LInfo = 0 ; true ),
    D = diagnosis(module, Status, LInfo, LOutStr, LErrStr).

:- pred analyze_and_diagnose(+AbsInt, +Flags, -Status, -D)
    #"Requires the module to be loaded before.".
analyze_and_diagnose(AbsInt, _Flags, Status, D) :-
    logged_once_port_reify(analyze(AbsInt, AInfo), APort, AOutStr, AErrStr),
    ( (\+ APort = success ; string_contained("ERROR", AErrStr)) ->
      Status = err ; Status = ok),
    % TODO: Remove when analyze never fails
    ( var(AInfo) -> AInfo = 0 ; true ),
    D = diagnosis(AbsInt, Status, AInfo, AOutStr, AErrStr).

% TODO: move somewhere else?
:- export(logged_once_port_reify/4).
:- pred logged_once_port_reify(Goal, Port, OutString, ErrString)
    => (string(OutString), string(ErrString))
    #"Executes @var{Goal}, @var{Port} is the state when the
      predicate finishes (true, fail). Its stdout and stderr are
      stored in @var{OutString} and @var{ErrString} respectively.".
:- meta_predicate logged_once_port_reify(goal, ?, ?, ?).
logged_once_port_reify(Goal, Port, OutString, ErrString) :-
    mktemp_in_tmp('outtextXXXXXX', OutN),
    mktemp_in_tmp('outerrXXXXXX', ErrN),
    open(OutN, write, OutS),
    open(ErrN, write, ErrS),
    current_output(OutS0),
    set_output(OutS),
    set_stream(user_error, ErrS, ErrS0),
    once_port_reify(Goal, Port0),
    set_output(OutS0),
    set_stream(user_error, ErrS0, _),
    close(OutS),
    close(ErrS),
    file_to_string(OutN, OutString),
    file_to_string(ErrN, ErrString),
    del_file_nofail(OutN),
    del_file_nofail(ErrN),
    Port = Port0.

:- doc(doinclude, task_status/1).
:- regtype task_status(Status) #"Type of analysis status.".
task_status(ok).
task_status(err).
task_status(skip).
