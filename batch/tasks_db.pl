:- module(tasks_db, [], [assertions, persdb, datafacts]).

:- doc(module, "This handles the data base of modules to be analyzed.
   Currently it is implemented with persistent predicates").

:- use_module(ciaopp_batch(db_analysis), [db_data_dir/1]).
:- use_module(library(format)).

% (use a persistent db local to this bundle)
:- include(cache_persdb_dir).

persdb_keyword(ciaopp_batch__localdb).
persdb_data(task_queue_/4).

persdb_dir(Dir) :- db_data_dir(Dir).

:- persistent(task_queue_/4, ciaopp_batch__localdb).

% TODO: Flags should be a regtype defined for
:- export(add_task/1).
:- pred add_task(Mod)
    #"Add a task to analyze with abtract domain @var{AbsInt} and CiaoPP configuration @var{Flags}".
add_task(treat(File, Mod, AbsInt, Flags)) :-
    update_localdb,
    assertz_fact(task_queue_(File, Mod, AbsInt, Flags)),
    update_persdb.

:- export(add_tasks/1).
:- pred add_tasks(Tasks) : list(Tasks)
    #"The same as @pred{add_task/3} but for a list of tasks (for
     efficiency)".
add_tasks(Tasks) :-
    update_localdb,
    add_tasks_(Tasks),
    update_persdb.

add_tasks_([]).
add_tasks_([treat(File, Mod, AbsInt, Flags)|Ms]) :-
    assertz_fact(task_queue_(File,Mod,AbsInt, Flags)),
    add_tasks_(Ms).

:- export(pop_task/4).
:- pred pop_task(File,Mod, AbsInt, Flags) #"Remove a task to analyze".
pop_task(File, Mod, AbsInt, Flags) :-
    update_localdb,
    retract_fact(task_queue_(File, Mod, AbsInt, Flags)),
    update_persdb.

:- export(analysis_task/4).
:- pred analysis_task(File,Mod,AbsInt,Flags)
    #"Checks a task to analyze, this predicate does not modify the DB".
analysis_task(File, Mod, AbsInt, Flags) :-
    update_localdb, !, % TODO: make_persistent leaves choice point
    task_queue_(File, Mod, AbsInt, Flags).

:- export(clean_db/0).
:- pred clean_db/0 #"Empties the database.".
clean_db :-
    update_localdb,
    retractall_fact(task_queue_(_,_,_,_)),
    update_persdb.

:- export(init_tasks_db/0).
:- pred clean_db/0 #"Initializes the database.".
init_tasks_db :-
    initialize_db.
