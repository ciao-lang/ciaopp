:- module(_, [main/1], [assertions]).

:- doc(title, "CiaoPP batch processing").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "
This is the command line interface for the batch analysis
@lib{ciaopp_batch(ciaopp_batch)} library.

@bf{Usage:} @tt{ciaopp-batch AbsInt [Paths]}

@bf{Analyze a list of directories:}
@begin{verbatim}
?- use_module(ciaopp_batch(ciaopp_batch)).
?- analysis_start([Dir1, Dir2], []).
@end{verbatim}

To see more options see page @ref{Analysis management predicates}.

@bf{Generate a report of an analyzed directory:}

The following command generates a directory @tt{allure-results} in the directory
from which the command is run. The diretory will contain an @tt{xml} file for each of
the domains that the directory was analyzed for.

@begin{verbatim}
$ ciaopp_batch_report Dir
@end{verbatim}

@bf{Visualize a report:}

The analysis report in xml can be processed with the allure tool. Once the tool
is installed, visualize the results by running in the same directory as the results were generated
@begin{verbatim}
$ allure serve
@end{verbatim}
").

:- use_module(ciaopp_batch(ciaopp_batch)).
:- use_module(ciaopp_batch(db_analysis)).
:- use_module(library(format)).

main(Args) :-
    process_opts(Args,Paths,Opts), !,
    analysis_start(Paths, Opts).
main(_) :-
    format('Usage: ciaopp-batch [-t T --inc=no|module|clause] <Domain> <Path> [Paths]~n',[]).

process_opts(Args0,Paths,Opts) :-
    ( member('--inc=module', Args0) ->
        Args = Args0
    ;
        Args = ['--inc=no'|Args0] % "non incremental" by default
    ),
    process_opts_(Args,Paths,Opts).

process_opts_([],[],[]).
process_opts_(['-t',NA|Args], Paths, [timeout(N)|Opts]) :- !,
    atom_number(NA,N),
    process_opts(Args,Paths,Opts).
process_opts_([I|Args], Paths, Opts) :-
    ( I = '--inc=no' ->
        Opts = [no_incremental|Opts0]
    ; I = '--inc=clause' ->
        format('WARNING: Clause-level inc not implemented in ciaopp-batch~n', []),
        Opts = Opts0
    ; I = '--inc=module',
        Opts = Opts0
    ), !,
    process_opts_(Args,Paths,Opts0).
process_opts_([AbsInt|Paths],Paths,[analysis([AbsInt])]).
