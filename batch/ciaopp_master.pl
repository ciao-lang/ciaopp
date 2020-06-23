:- module(ciaopp_master, [main/1], [assertions, hiord, datafacts]).

:- doc(module, "This programs analyzes modules read in the form of terms from
the standard input.

This program should not be used directly, it should be used through
@tt{ciaopp_batch}.

@bf{Workflow}:
This program uses workers to launch ciaopp analysis. It controls the analysis
time of each worker with a timeout.").

:- use_module(library(process),
    [process_call/3, process_kill/1, process_join/1, process/1]).
:- use_module(library(system), [pause/1]).
:- use_module(library(pathnames), [path_concat/3, path_basename/2]).
:- use_module(library(concurrency)).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(source_tree), [current_file_find/3]).
:- use_module(library(read), [read/2]).
:- use_module(library(messages),
    [simple_message/2, simple_message/1, note_message/1]).

:- use_module(ciaobld(config_common), [cmd_path/4]).

:- use_module(ciaopp_batch(db_analysis)).
:- use_module(ciaopp_batch(tasks_db)).
:- use_module(ciaopp_batch(ciaopp_batch_aux)).

:- pred timeout(T) :: int #"Time limit for performing tasks. The default timeout
    is 30 seconds.".
timeout(30).
:- data timeout/1.

set_timeout(X) :-
    atom_number(X, T),
    T > 0,
    set_fact(timeout(T)).

:- data workers/1.
workers(1).
set_workers(X) :-
    atom_number(X, N),
    N > 0,
    set_fact(workers(N)).

:- pred main(Config) : list
    #"Analyzes @var{Files} with ciaopp using @mod{main_analysis}".
main([T, N]) :- !,
    set_timeout(T),
    set_workers(N),
    tasks_db:clean_db, % clean previous work
    do_analysis,
    tasks_db:clean_db.
main(_) :-
    help_msg(M),
    simple_message(M).

worker_msg_file(ID, F) :-
    db_data_dir(D),
    atom_concat(ID, 'ciaopp_worker.log', FN),
    path_concat(D, FN, F).

:- export(server_file/1).
server_file(X) :-
    db_data_dir(D),
    path_concat(D, 'ciaopp_worker_pid.lock', X).

do_analysis :-
    init_analysis_db,
    process_paths_to_analyze, % Add (if necessary) modules to the tasks db
    ( analysis_task(_,_,_,_)  -> % there are modules to analyze
        simple_message("Start analysis"),
        % timer that send tick events
        start_timer(add_event('1', tick)), % TODO: add one timer for each worker
        display_event('Timer started', ""),
        set_fact(next_worker('1', [])),
        start_analysis_loop
    ;
        true
    ).

:- data next_worker/2.

start_analysis_loop :-
    % launch analysis process
    next_worker(ID, Mods),
    ( ( analysis_task(_,_,_,_)
      ; Mods = [_|_]) -> % there are modules to analyze
        !,
        launch_worker(ID, Mods),
        call_in_eventloop(process_event, start_analysis_loop)
    ;
        true
    ).

% Call ciaopp in worker mode
launch_worker(ID, Work) :-
    cmd_path(ciaopp, plexe, 'ciaopp', B),
    set_task_time(ID, none, 0),
    worker_msg_file(ID, MF),
    eng_process_call(B, ['--worker', ID], [stdin(terms(Work)),stdout(file(MF))], batch_finished(ID), AProc),
    set_control_process(ID, AProc).

% Called when ciaopp_batch finishes
batch_finished(ID) :-  % executed in a thread (not main)
    add_event(ID, joined).

display_control_event(Event, Msg) :-
    atom_codes(A, Msg),
    simple_message("[C] ~w ~w ", [Event, A]).

:- data last_task_time/3.
:- pred last_task_time(IDa, Mod, Time).

set_task_time(IDa, Mod, Time) :-
    ( last_task_time(IDa, _, _) ->
        retract_fact(last_task_time(IDa, _, _))
    ;
        true),
    assertz_fact(last_task_time(IDa, Mod, Time)).

:- pred control_process(ID, P) => atm * process.
:- data control_process/2.

set_control_process(ID, P) :-
    ( control_process(ID, _) ->
        retract_fact(control_process(ID, _))
    ; true
    ),
    assertz_fact(control_process(ID, P)).

process_event(Cont) :-
    ( retract_fact_nb(control_event(ID, joined)) -> % non-blocking
        % it needs to be checked first because if retract is made it will
        % wait until such event is asserted.
%            get_event(ID, joined),
        Event = joined
    ; get_event(ID, Event)
    ),
    simple_message("Next event ~w ~w", [Event, ID]),
    process_event_(Event, ID, Cont).

process_event_(tick, ID, Cont) :-
    last_task_time(ID, _Task, T),
    timeout(T0), T0 < T, !,
    display_event('Timeout', ""),
    control_process(ID, Process),
    catch(process_kill(Process), _E, note_message("Attempt to kill a joined process")),
    % The process may already have finished
    % TODO: We need process_join with timeout (wait join for an amount of time)
    display_event('Kill signal sent', ""),
    Cont = next_event.
process_event_(tick, ID, Cont) :-
    last_task_time(ID, LTask, N),
    current_task_proc(ID, Task),
    Task = treat(_,Mod,_,_),
    ( LTask = Task ->
      N1 is N + 1,
      set_task_time(ID, Task, N1),
      simple_message("[M] Waiting for ~w ~w second(s).", [Mod, N])
    ;
        simple_message("[M] Analyzing ~w.", [Mod]),
        set_task_time(ID, Task, 0)
    ),
    Cont = next_event.
process_event_(joined, ID, Cont) :-
    % TODO: annotate when the process was sent the kill message
    last_task_time(ID, Task, T),
    timeout(T0), T > T0, !,
    ( redo_analysis(ID, Task) -> % worker ID repeated the analysis
        % add analysis error to db
        Task = treat(FilePath, ModName, AbsInt, Flags),
        add_task_status(ModName, FilePath, AbsInt, Flags, err),
        set_last_error(ModName, FilePath, AbsInt),
        retract_fact(redo_analysis(ID, Task)),
        set_fact(next_worker(ID, []))
    ;
        asserta_fact(redo_analysis(ID, Task)),
        % launch_process analyzing this failed module
        simple_message("Next worker ~w ~q", [ID, Task]),
        set_fact(next_worker(ID, [Task]))
    ),      
    set_task_time(ID, none, 0),
    Cont = restart_loop.
process_event_(joined, ID, Cont) :-
    display_event(ID, "Analysis finished"),
    stop_timer,
    Cont = finish_loop.

display_event(EventAtm, Msg) :-
    atom_codes(A, Msg),
    simple_message("[M] ~w ~w", [EventAtm, A]).

% ---------------------------------------------------------------------------

help_msg("Usage: ./ciaopp_master <timeout(s)> <n_workers>

where each path is a module or a directory containing modules to be
analyzed.").

% ---------------------------------------------------------------------------
:- doc(section, "Concurrent timer").
% TODO: customize pause time

:- concurrent stop_timer_flag/0.

:- meta_predicate start_timer(goal).
start_timer(G) :-
    eng_call(timer_loop(G), create, create).

stop_timer :-
    set_fact(stop_timer_flag). % stop timer

:- meta_predicate timer_loop(goal).
timer_loop(G) :-
    display_control_event('Starting timer', ""),
    timer_loop_(G).

:- meta_predicate timer_loop_(goal).
timer_loop_(G) :-
    ( stop_timer_flag ->
        true
    ;
        pause(1),
        G,
        timer_loop_(G)
    ).

% ---------------------------------------------------------------------------
:- doc(section, "Concurrent-based process call").

% TODO: This should be equivalent to:
%   eng_call((process_call(...), OnJoin), ..., ...)
% but here the process call is performed from the parent thread.
% Is there any reason to do it?

% Do process call on a separate thread, run OnJoin code when the process finishes
:- meta_predicate eng_process_call(?, ?, ?, goal, ?).
eng_process_call(Path, Args, Opts, OnJoin, AProc) :-
    % Launch on background
     process_call(Path, Args, [background(AProc)|Opts]),
     % Wait on a thread
     eng_call(eng_process_join_(AProc, OnJoin), create, create).

:- meta_predicate eng_process_join_(?, goal).
eng_process_join_(Process, OnJoin) :-
    ( catch(process_join(Process),_,true) -> true ; true ),
    % process_join fails if the process did not end correctly
    call(OnJoin).

% ---------------------------------------------------------------------------
:- doc(section, "Process concurrent events").
% TODO: Find the right abstraction, move to its own library and document

:- pred control_event(ID, Event) => atm * term.
:- concurrent control_event/2.

:- meta_predicate call_in_eventloop(pred(1), goal).
call_in_eventloop(ProcessEvent, Restart) :-
    ( % (Get events on backtracking)
        ProcessEvent(Cont),
        ( Cont = next_event ->
            fail % process next event
        ; Cont = restart_loop ->
            !, % cut to stop reading events
      % restart loop
      Restart
        ; Cont = finish_loop ->
            !, % cut to stop reading events
      true
        ; throw(bug_unknown_cont(Cont))
        )
    ; throw(bug_no_finish_event)
    ).

%:- pred get_event(-Event) :: term.
get_event(ID, Event) :-
    retract_fact(control_event(ID, Event)). % read

%:- pred add_event(+Event) :: term.
add_event(ID, Event) :-
    assertz_fact(control_event(ID, Event)).

% --------------------------------------------------------------------------------
:- doc(section, "Analysis logic").

:- doc(treat(Path,Module,AbsInt,Flags), "Contains the @var{Module} to be analyzed
and its absolute @var{Path}, the abstract domain (@var{AbsInt}) and the CiaoPP configuration of
the analysis (@var{Flags})").
:- data treat/4.

:- export(process_paths_to_analyze/0).
process_paths_to_analyze :-
    retractall_fact(treat(_,_,_,_)),
    repeat,
    ( read(user_input, X), \+ X = end_of_file ->
      X = w(Path, AbsInt, Flags),
        files_from_path(Path, Files),
        assert_files(Files, AbsInt, Flags),
        fail
    ; !,
      add_analysis_tasks
    ).

files_from_path(FilePath, Fs) :-
    ( atom_concat(Base, '.pl', FilePath) ->
        path_basename(Base, Module),
        Fs = [pl(FilePath,Module)]
    ;
        findall(pl(File, ModName), (current_file_find([proj(compilable), srctype(module)], FilePath, File), get_mod_name_from_file(File, ModName)), Fs)
    ).

assert_files([], _, _).
assert_files([pl(File, M)|Fs], AbsInt, Flags) :-
    assertz_fact(treat(File, M, AbsInt, Flags)),
    assert_files(Fs, AbsInt, Flags).

add_analysis_tasks :-
    findall(treat(AbsFile, Module, AbsInt, Flags), to_analyze(AbsFile, Module, AbsInt, Flags), Mods),
    add_tasks(Mods).

:- data redo_analysis/2.
:- pred redo_analysis(Worker, Task)
    #"Repeat an analysis @var{Task} in @var{Worker}".

% ---------------------- MODULE STATES ---------------------------- %

:- pred to_analyze(ModulePath, Module, AbsInt, Flags)
    #"A @var{Module} is to_analyze in this context if it has not been 
      already loaded and analyzed for abstract domain @var{AbsInt}.".
to_analyze(ModulePath, Module, AbsInt, Flags) :-
    treat(ModulePath, Module, AbsInt, Flags),
    \+ task_status(Module, ModulePath, module, Flags, ok),
    \+ task_status(Module, ModulePath, module, Flags, err),
    \+ task_status(Module, ModulePath, AbsInt, Flags, ok),
    \+ task_status(Module, ModulePath, AbsInt, Flags, err).

:- export(clean_dbs/0).
clean_dbs :-
    db_analysis:clean_db,
    tasks_db:clean_db.
