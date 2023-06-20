:- module(ciaopp_batch_aux, [dump_file/4, string_contained/2, get_mod_name_from_file/2], [assertions]).

:- use_module(library(pathnames), [path_split/3, path_concat/3]).
:- use_module(library(system), [modif_time0/2, file_exists/1, make_directory/1]).
:- use_module(library(lists), [append/3]).

:- doc(title, "Auxiliary predicates").

:- doc(module, "Auxiliary predicates for ciaopp batch").

:- pred dump_file(FilePath, Module, AbsInt, DumpFile) : atm * atm * atm * var
    #"Given a @var{FilePath} and @var{Module} name, generates its
      associated @var{DumpFile}".
dump_file(FilePath, Module, AbsInt, DumpFile) :-
    path_split(FilePath, Path, _),
    atom_concat(Module, '_', Dump0),
    % TODO: see frontend_driver:get_output_path/2
    atom_concat(Dump0, AbsInt, Dump1),
    atom_concat(Dump1, '.dump', Dump),
    path_concat(Path, Dump, DumpFile).

:- pred string_contained(L1, L2) : string * string
    #"@var{L1} is a sublist of @var{L2}.".
string_contained(X, String) :-
    append(X, _, X2),
    append(_, X2, String), !.

% TODO: get module name from module done well
:- pred get_mod_name_from_file(FilePath, ModName)
    #"@var{ModName} is the name of the module located in @var{FilePath}.".
get_mod_name_from_file(ModPath, ModName) :-
    path_split(ModPath, _, Mod),
    atom_concat(ModName, '.pl', Mod), !.

% TODO: implemented somewhere else?
:- export(newer/2).
:- pred newer(FileA, FileB) : atom * atom
    #"@var{FileA} was modified later than @var{FileB}.".
newer(FileA, FileB) :-
    modif_time0(FileA, TA),
    modif_time0(FileB, TB),
    TA > TB.

:- pred make_dir_nofail(X) : atm #"Creates @var{X} if it does not exist already".
:- export(make_dir_nofail/1).
make_dir_nofail(X) :-
    ( file_exists(X) -> true
    ;  make_directory(X)).
