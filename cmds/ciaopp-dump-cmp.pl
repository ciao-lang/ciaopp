:- module(_, [main/1], [assertions, hiord, datafacts]).

:- doc(title, "A semantic dump comparator").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(stability, devel).

:- doc(summary, "This command compares semantically analysis results.").

:- doc(module, "This command compares semantically the results of an
analysis of two given paths. The paths can be either files or
directories. If the paths are directories, each of the files in one directory
will be compared with the files in the other directory with the same
name.

Currently, only the files with extension @tt{.dump}, @tt{.reg} or
@tt{.inc_reg} will be checked, the rest will be omitted.

@subsection{Usage}

@begin{verbatim}
$ ciaopp-dump-cmp <base_path> <test_path> <domain>
@end{verbatim}
").

:- use_module(library(format), [format/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(messages), [error_message/2,show_message/2]).
:- use_module(library(system), [file_exists/1, file_property/2]).
:- use_module(library(pathnames), [path_concat/3, path_split/3]).
:- use_module(library(sort), [sort/2]).

%:- use_module(ciaopp_tests(benchs/incanal/ciaopp_bench_manager), [directory_dir/3]).
:- use_module(ciaopp(test_aux/compare_dump)).

main([Path1, Path2, AbsInt]) :- !,
    ( file_exists(Path1) ->
      ( file_exists(Path2) ->
          main_([Path1, Path2, AbsInt]),
          ( halt_(Halt) -> true ; Halt = 0 )
      ;
          error_message("File not found: ~w~n", [Path2]),
          Halt=1
      )
    ;
        error_message("File not found: ~w~n", [Path1]),
        Halt=1
    ),
    halt(Halt).
main(_) :-
    show_message(simple,"Usage: ciaopp-dump-cmp <base_path> <test_path> <domain>~n"),
    halt(1).

main_([Dir1, Dir2, AbsInt]) :-
    file_property(Dir1,type(directory)), !,
    evaluate_results(Dir1, Dir2, AbsInt).
main_([F1, F2, AbsInt]) :- !,
    file_property(F1, type(regular)),
    compare_one_dump(F1,F2,AbsInt).

:- data halt_/1.

:- pred evaluate_results(Path1, Path2, AbsInt) : atm * atm * atm.
evaluate_results(Path1, Path2, AbsInt) :-
    set_fact(checking_domain(AbsInt)), % TODO: should be written in the dump
    ( file_property(Path1, type(regular)) ->
        compare_files(Path1, Path2, AbsInt)
    ;
        compare_dirs(Path1, Path2, AbsInt)
    ).

compare_files(F1, F2, AbsInt) :-
    path_split(F1, Dir1, File1),
    path_split(F2, Dir2, File2),
    dumpfile_checker_loop([File1], [File2], Dir1, Dir2, AbsInt).

compare_dirs(Dir1, Dir2, AbsInt) :-
    not_hidden_directory_files(Dir1, Fs1),
    not_hidden_directory_files(Dir2, Fs2),
    dumpfile_checker_loop(Fs1, Fs2, Dir1, Dir2, AbsInt).

compare_one_dump(F1,F2,AbsInt) :-
    compare_dumps_auto_detect_db(F1, F2, db1, db2, AbsInt,Diff),
    ( Diff = [] ->
        % format(user_error, 'EQUIVALENT', [])
        true
    ;
        format(user_error, 'Checking ~w \n vs. ~w~n', [F1,F2]),
        print_diff(Diff, DSumm),
        format(user_error, '\n', []),
        ( DSumm = [] -> true ; set_fact(halt_(1))) % store number of errors?
    ).

dumpfile_checker_loop([], _, _, _, _).
dumpfile_checker_loop([F1|Fs1], [F1|Fs2], Dir1, Dir2, AbsInt) :- !,
    path_concat(Dir1, F1, DF1),
    path_concat(Dir2, F1, DF2),
    compare_one_dump(DF1,DF2,AbsInt),
    dumpfile_checker_loop(Fs1, Fs2, Dir1, Dir2, AbsInt).
dumpfile_checker_loop([F1|Fs1], [F2|Fs2], Dir1, Dir2, AbsInt) :-
    F1 < F2, !,
    format(user_error, 'Skipping ~w ~w ...~n', [Dir1, F1]),
    dumpfile_checker_loop(Fs1, [F2|Fs2], Dir1, Dir2,  AbsInt).
dumpfile_checker_loop(Fs1, [F2|Fs2], Dir1, Dir2, AbsInt) :-
    format(user_error, 'Skipping ~w ~w ...~n', [Dir2, F2]),
    dumpfile_checker_loop(Fs1, Fs2, Dir1, Dir2, AbsInt).
