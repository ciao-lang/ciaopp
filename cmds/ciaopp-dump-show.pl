:- module(_, [main/1], [assertions, datafacts, fsyntax]).

:- use_module(ciaopp(p_unit/p_dump), [show_dump/1]).
:- use_module(ciaopp(raw_printer), [show_registry_info/0]).
:- use_module(ciaopp(test_aux/compare_dump), [not_hidden_directory_files/2]).
:- use_module(library(pathnames), [path_splitext/3, path_concat/3]).
:- use_module(library(system), [file_property/2]).
:- use_module(ciaopp(plai/intermod_punit), [ensure_registry_file/3]).

main([Path]) :-
    ( file_property(Path, type(regular)) ->
        show_dump(Path)
    ;
        not_hidden_directory_files(Path, Fs),
        ( % failure-driven loop
          member(F, Fs),
            path_splitext(F, Module, '.reg'),
            ensure_registry_file(Module, ~path_concat(Path, Module), high),
            fail
        ; true),
        show_registry_info
    ).