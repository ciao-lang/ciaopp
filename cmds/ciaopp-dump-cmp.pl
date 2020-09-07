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
:- use_module(library(messages), [error_message/2,show_message/2]).
:- use_module(library(system), [file_exists/1, file_property/2]).
:- use_module(library(pathnames), [path_concat/3, path_split/3]).
:- use_module(library(sort), [sort/2]).

:- use_module(ciaopp(test_aux/compare_dump)).

main(Args) :-
    parse_options(Args,Seq,Mis,[Path1, Path2, AbsInt]), !,
    ( file_exists(Path1) ->
      ( file_exists(Path2) ->
          main_(Seq,Mis,Path1, Path2, AbsInt),
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
:- export(parse_options/4).
parse_options([P1,P2,AI],_,_,[P1,P2,AI]) :- !.
parse_options(['--sequence'|Paths],seq,Mis,Rest) :- !,
    parse_options(Paths,_,Mis,Rest).
parse_options(['--no-missing'|Paths],Seq,nomis,Rest) :- !,
    parse_options(Paths,Seq,_,Rest).
parse_options([O|_],_,_,_) :- !,
    error_message("Unrecognized option ~w~n", [O]), fail.

main_(Seq,Mis,P1, P2, AbsInt) :-
    set_fact(checking_domain(AbsInt)),
    ( nonvar(Mis) -> set_fact(missing) ; true),
    ( (nonvar(Seq), Seq = seq) ->
        evaluate_results(P1, P2, AbsInt)
    ;
        compare_one_analysis(P1,P2,AbsInt)
    ).

:- data halt_/1.
:- data missing/0.

:- pred evaluate_results(Path1, Path2, AbsInt) : atm * atm * atm.
evaluate_results(Path1, Path2, AbsInt) :-
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

compare_one_analysis(F1,F2,AbsInt) :-
    compare_dumps_auto_detect_db(F1, F2, db1, db2, AbsInt,Diff),
    ( Diff = [] -> % equivalent
        true
    ;
        format(user_error, 'Checking ~w \n vs. ~w~n', [F1,F2]),
        checking_domain(AbsInt), format(user_error, '~w~n', [AbsInt]),
        ( missing ->
            print_diff(Diff,skip_miss,DSumm)
        ;
            print_diff(Diff,skip_none,DSumm)
        ),
        format(user_error, '\n', []),
        ( DSumm = [] -> true ; set_fact(halt_(1))) % store number of errors?
    ).

skip_miss(abs_diff(_,_,_,_,_,not_in(_))).

skip_none(_) :- fail.

dumpfile_checker_loop([], _, _, _, _).
dumpfile_checker_loop([F1|Fs1], [F1|Fs2], Dir1, Dir2, AbsInt) :- !,
    path_concat(Dir1, F1, DF1),
    path_concat(Dir2, F1, DF2),
    compare_one_analysis(DF1,DF2,AbsInt),
    dumpfile_checker_loop(Fs1, Fs2, Dir1, Dir2, AbsInt).
dumpfile_checker_loop([F1|Fs1], [F2|Fs2], Dir1, Dir2, AbsInt) :-
    F1 < F2, !,
    format(user_error, 'Skipping ~w ~w ...~n', [Dir1, F1]),
    dumpfile_checker_loop(Fs1, [F2|Fs2], Dir1, Dir2,  AbsInt).
dumpfile_checker_loop(Fs1, [F2|Fs2], Dir1, Dir2, AbsInt) :-
    format(user_error, 'Skipping ~w ~w ...~n', [Dir2, F2]),
    dumpfile_checker_loop(Fs1, Fs2, Dir1, Dir2, AbsInt).
