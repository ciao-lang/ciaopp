:- module(_, [main/1], [assertions]).

:- doc(title,"Display information about CiaoPP files").

:- doc(author,"Isabel Garcia-Contreras").
:- doc(stability, devel).

:- use_module(library(format)).

:- use_module('ciaopp-dump-show').
:- use_module('ciaopp-dump-cmp').
:- use_module('ciaopp-dump-fmt').
:- use_module('ciaopp-dump-stats').
:- use_module('ciaopp-dump-syntactic').
:- use_module('ciaopp-dump-report').
:- use_module('ciaopp-dump-ctcheck').

:- doc(module, "This program outputs information about CiaoPP files.

   @section{Usage}

   @begin{verbatim}
@includefact{usage_text/1}
   @end{verbatim}
").

usage_text("ciaopp-dump <action> [<opts>] <files>

where the possible options are:

  -h
     Print this information

  show <path>
     Print info of the dump file or registry directory located in <path>.

  cmp <path1> <path2> <domain>
     Compares the analysis results of path1 and path2.
     May be directories or .dump files.

  fmt <filename>[.dump]
     Outputs the analysis result in dot format.

  ctcheck <modulename>.pl <filename>[.dump] <domain>
     Checks assertions agains the analysis in <filename>.dump with <domain>.

  report reach <file>[.dump]
     Deadcode and failure report of a CiaoPP analysis dumped with the
     incremental option, and analyzed with the pp_flag fact_info=on.

  stats [--print-header] <filenames>[.dump]
     Counts simple characteristics of analysis in the files.

     --print-header: prints the names of the characteristics displayed

  syntactic [--print-header] <filenames>[.pl]
     Counts simple syntactic characteristics of the source in the files.

     --print-header: prints the names of the characteristics displayed
").

main(['-h']) :- !,
    usage_text(T),
    format(user_output,"Usage: ~s~n",[T]).
main(['show',Path]) :- !,
    'ciaopp-dump-show':main([Path]).
main(['fmt'|Args]) :- !,
    'ciaopp-dump-fmt':main(Args).
main(['cmp'|Args]) :- !,
    'ciaopp-dump-cmp':main(Args).
main(['stats'|Args]) :- !,
    'ciaopp-dump-stats':main(Args).
main(['syntactic'|Args]) :- !,
    'ciaopp-dump-syntactic':main(Args).
main(['report', 'reach'|Args]) :- !,
    'ciaopp-dump-report':main(Args).
main(['ctcheck'|Args]) :- !,
    'ciaopp-dump-ctcheck':main(Args).
main(_) :-
    format(user_error, "Wrong arguments. Run '-h' to show help",[]).
