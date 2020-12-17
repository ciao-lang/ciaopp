:- module(incanal_persistent_db, [], [assertions, regtypes, datafacts]).

:- doc(title, "Persistent database for incremental analysis").

:- use_module(library(system), [file_exists/1]).
:- use_module(library(system_extra), [del_file_nofail/1]).
:- use_module(library(pathnames), [path_split/3, path_splitext/3, path_concat/3]).

:- use_module(ciaopp(p_unit/p_dump), [dump/2, restore/2]).
:- use_module(ciaopp(analysis_stats), [add_stat/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

:- doc(module, "This module handles the maintenance of the persistent
database needed for resuming a stopped incremental analysis.").

% TODO: when we analyze a modular program in a monolithic way, we
% store one dump (only for the top-level module containing all the
% analysis info)

:- data loaded_module/1.

:- export(set_loaded_module/1).
set_loaded_module(X) :-
    set_fact(loaded_module(X)).

:- export(reset_persistent_db/0).
:- doc(reset_persistent_db/0, "Removes previous persistent data of an
incremental analysis.").
reset_persistent_db :-
    loaded_module(X),
    dump_file(X, D),
    del_file_nofail(D).

:- export(load_persistent_if_needed/2).
:- pred load_persistent_if_needed(Top,Fs) : atm * list
    #"Restores the persistent analysis of tiles in list @var{Fs}
     if it existed and the flag @tt{inc_persistent} is on.".
load_persistent_if_needed(Top,_Fs) :-
    \+ current_pp_flag(intermod, off),
    current_pp_flag(module_loading, all), !, % monolithic with modular driver 
    restore_dump_files([Top]).
load_persistent_if_needed(_Top,Fs0) :-
    ( atom(Fs0) -> Fs = [Fs0] ; Fs = Fs0),
    restore_dump_files(Fs).

% TODO: Predicate for defining top-level module (to reuse also in intermod)
:- export(top_level_of_files/2).
top_level_of_files([TopLevel|_], TopLevel) :- !.
top_level_of_files(TopLevel, TopLevel) :-
    atom(TopLevel).

restore_dump_files([]).
restore_dump_files([F|Fs]) :-
    restore_dump_file(F),
    restore_dump_files(Fs).

restore_dump_file(File) :- 
    ( has_dump(File, DFile) ->
        pplog(incremental_high, ['{Restoring ', DFile, '}\n']),
        restore(DFile, [time(T1,[])]), % this restores counters
        add_stat(restore, T1)
    ; true).

:- export(has_dump/2).
has_dump(File, DFile) :-
    dump_file(File, DFile),
    file_exists(DFile).

:- data inc_persistent/1. % Flag for persistent analysis.
inc_persistent(on). % ON by default

:- export(set_inc_persistent/1).
:- pred set_inc_persistent(St) : inc_persistent_status #"This flags
    controls the storage of persistent information after the
    analysis.".
set_inc_persistent(St) :-
    set_fact(inc_persistent(St)).

:- export(inc_persistent_status/1).
:- regtype inc_persistent_status(St) #"@var{St} Defines whether the analysis
    should be stored persistently.".
:- doc(inc_persistent_status(X), "@var{X} can be:
    @begin{itemize}
    @item @tt{on}: Analysis information will be stored in the same
    location as the analyzed code (as dump files). This is usefull
    when analysis scheduling involves loading and unloading
    modules. To perform an analysis from scratch, these files have
    to be manually removed.
    @item @tt{off}: No information is stored.
    @end{itemize}").
inc_persistent_status(on).
inc_persistent_status(off).

:- export(save_persistent_analysis/0).
:- pred save_persistent_analysis #"Makes incremental analysis
    persistent by saving it to disk.".
save_persistent_analysis :-
    inc_persistent(on), !,
    loaded_module(File),
    dump_file(File, DFile),
    pplog(incremental_high, ['{Analysis stored in: ', DFile, '}\n']),
    dump(DFile, [incremental]).

:- export(clean_persistent_analysis/0).
:- pred clean_persistent_analysis #"Removes the persistent incremental analysis
   from disk.".
clean_persistent_analysis :-
    inc_persistent(on), !,
    loaded_module(File),
    dump_file(File, DFile),
    pplog(incremental_high, ['{Analysis stored in: ', DFile, '}\n']),
    del_file_nofail(DFile).

% ----------------------------------------------------------------------
% TODO: copied from ciaopp_batch and adapted
dump_file(FilePath, DumpFile) :-
    path_split(FilePath, Path, Mod),
    ( path_splitext(Mod, ModName, '.pl') -> true ; ModName = Mod ),
    % TODO: temporary extension for easy finding/cleaning
    atom_concat(ModName, '.dump_inc', Dump),
    current_pp_flag(incanal_dump_dir, Dir),
    ( Dir = '$default' ->
        path_concat(Path, Dump, DumpFile)
    ;
        path_concat(Dir, Dump, DumpFile)
    ).
