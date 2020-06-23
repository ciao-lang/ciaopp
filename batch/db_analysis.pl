:- module(db_analysis, [], [assertions, persdb, datafacts]).

:- doc(title, "Database for ciaopp_batch process").
:- doc(author, "Isabel Garcia-Contreras").
:- doc(module, "This module manages the analysis database for ciaopp_batch.").

:- use_module(ciaopp_batch(ciaopp_batch_aux), [newer/2, dump_file/4, make_dir_nofail/1]).

:- use_module(library(system), [file_exists/1, touch/1, directory_files/2]).
:- use_module(engine(stream_basic)).
:- use_module(library(terms_io), [file_to_terms/2]).
:- use_module(library(system_extra), [del_file_nofail/1]).
:- use_module(library(read), [read/2]).
:- use_module(library(pathnames), [path_split/3, path_concat/3]).
:- use_module(library(write), [portray_clause/2]).

% ---------------------------------------------------------------------------
:- include(cache_persdb_dir).

persdb_keyword(ciaopp_batch__localdb).
persdb_data(task_status_/5).

persdb_dir(Dir) :- db_data_dir(Dir).

:- persistent(task_status_/5, ciaopp_batch__localdb).

:- export(add_task_status/5).
:- pred add_task_status(ModName, ModPath, Action, Flags, Status)
    : atm * atm * atm * term * atm
    #"Adds ciaopp action status for @var{ModName} located in @var{ModPath}".
add_task_status(ModName, ModPath, Action, Flags, Status) :-
    update_localdb,
    assertz_fact(task_status_(ModName, ModPath, Action, Flags, Status)),
    update_persdb.

:- export(task_status/5).
:- pred task_status(ModName, ModPath, Action, Flags, Status)
    ::  atm * atm * atm * term * atm
    #"@var{Status} is the information of how @var{ModName} located in
    @var{ModPath} was analyzed".
task_status(ModName, ModPath, Action, Flags, Status) :-
    update_localdb,
    task_status_(ModName, ModPath, Action, Flags, Status).

:- export(update_task_status/0).
:- pred update_task_status/0 #"Updates the data with the last analysis information".
update_task_status :-
    update_localdb.

:- export(last_file_log/2). % This log is different for each worker
:- pred last_file_log(ID, F) : atm(ID) => atm(F)
    #"@var{F} is the associated file log to @var{ID}".
last_file_log(ID, F) :-
    db_tmp_dir(D),
    atom_concat(worker_log_, ID, File),
    path_concat(D, File, F).

% ---------------------------------------------------------------------------
:- export(init_analysis_db/0).
:- pred init_analysis_db/0 #"Initializes analysis database".
init_analysis_db :-
    db_data_dir(D),
    make_dir_nofail(D),
    initialize_db.

:- export(init_tmp_db/1).
:- pred init_tmp_db(ID) : atm #"Initializes a temporal DB for @var{ID}.".
init_tmp_db(ID) :-
    db_tmp_dir(D),  
    make_dir_nofail(D),
    last_file_log(ID, F),
    touch(F).

:- export(clean_db/0).
:- pred clean_db/0 #"Clears all analysis data.".
clean_db :-
    clean_tmp_db,
    update_localdb,
    retractall_fact(task_status_(_, _, _, _, _)),
    update_persdb.

:- export(clean_tmp_db/0).
:- pred clean_tmp_db/0 #"Removes all temporal databases.".
clean_tmp_db :-
    db_tmp_dir(D),
    file_exists(D), !,
    directory_files(D, Fs),
    delete_files(Fs, D).
clean_tmp_db.

delete_files([],_).
delete_files([F|Fs],D) :-
    path_concat(D,F,Path),
    del_file_nofail(Path),
    delete_files(Fs,D).

% ---------------------------------------------------------------------------
:- export(set_current_task/2).
:- pred set_current_task(ID, Task)
    #"Writes in a file that @var{Module} is currently being analyzed.".
set_current_task(ID, Task) :-
    last_file_log(ID, File),
    open(File, write, S),
    portray_clause(S, (last_treated(Task))), % AbsInt included
    flush_output(S),
    close(S).

:- export(current_task_proc/2).
:- pred current_task_proc(ID, -Task) #"@var{Module} is the module being analyzed by @apl{batch_analyze} currenlty".
current_task_proc(ID, Task) :-
    last_file_log(ID, CF),
    ( file_exists(CF) ->
        file_to_terms(CF, T),
        ( T = [last_treated(Task)|_]->
            true
        ;
            Task = treat(none, none,_,_) % TODO: fix this
        )
    ;
        Task = treat(none, none,_,_) % TODO: fix this
    ).

:- export(set_last_error/3).
:- pred set_last_error(ModName, FilePath, AbsInt)
    #"Appends to the error file of @var{FilePath} that the analysis for
    domain @var{AbsInt} of the last module (@var{Module}) had a timeout.".
set_last_error(ModName, FilePath, AbsInt) :-
    open_err_file(FilePath, ModName, SEF),
    portray_clause(SEF, diagnosis(module, ok, "", "", "")),
    portray_clause(SEF, diagnosis(AbsInt, err, timeout, "", "Timeout")),
    flush_output(SEF), % necessary?
    close(SEF).

:- doc(section, "Update analysis DB").

:- export(update_tasks_analysis_status/0).
:- pred update_tasks_analysis_status/0
    #"Updates the task_status db to remove modules which are not
     updated, i.e., their @tt{.dump} file is older than their
     @tt{.pl} file.

     For modules which could not be analyze, no information is updated".
update_tasks_analysis_status :-
    update_localdb,
    task_status(ModName, ModPath, AbsInt, _, St),
    ( St = ok ->
         dump_file(ModPath, ModName, AbsInt, DumpFile),
         ( newer(ModPath, DumpFile) ->
             % TODO: We should check also imports(m)
             retract_fact(task_status(ModName, _, AbsInt, _, _))
         )
    ),
    fail.
update_tasks_analysis_status :-
    update_persdb. % store changes

:- doc(section, "Analysis statistics").

:- export(report_mod_info/3).
:- pred report_mod_info(FilePath, ModName, LDiag)
    #"Stores in a file with extension @tt{.err} @var{Info} about @var{ModName}".
report_mod_info(FilePath, ModName, LDiag) :-
    error_file(FilePath, ModName, FileName),
    open(FileName, append, SErr),
    ( % failure-driven loop
      member(L, LDiag),
        portray_clause(SErr, L),
        fail
    ; true),
      flush_output(SErr),
      close(SErr).

open_err_file(FilePath, ModName, SErr) :-
    error_file(FilePath, ModName, FileName),
    open(FileName, append, SErr).

:- pred error_file(FilePath, Module, ErrFile) : atm * atm * var
    #"Given a @var{FilePath} and @var{Module} name, generates its 
      associated @var{ErrFile}".
error_file(FilePath, ModName, ErrFile) :-
    path_split(FilePath, Path, _),
    atom_concat(ModName, '.err', Err),
    path_concat(Path, Err, ErrFile).        

:- use_module(library(persdb/datadir), [ensure_datadir/2]).

:- export(db_data_dir/1).
:- pred db_data_dir(F) #"@var{F} is the location of data in this bundle".
db_data_dir(Dir) :-
    ensure_datadir('ciaopp_batch_data', Dir).

db_tmp_dir(Dir) :-
    db_data_dir(Dir0),
    path_concat(Dir0, 'tmp', Dir).

%%% old predicate
:- use_module(library(format), [format/2]).
show_module_status_info(Module, AbsInt, Flags) :-
    ( task_status(Module, _, module, Flags, ok) ->
        Loaded = 'OK'
    ;
        ( task_status(Module, _, module, Flags, err) ->
            Loaded = 'ERR'
        ;
            Loaded = 'UNKNOWN'
        )
    ),
    ( task_status(Module, _, AbsInt, Flags, ok) ->
        Analyzed = 'OK'
    ;
        ( task_status(Module, _, AbsInt, Flags, err) ->
            Analyzed = 'ERR'
        ;
            Analyzed = 'UNKNOWN'
        )
    ),
    format('~w~t~w~t~w~n', [Module,Loaded,Analyzed]).
