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
:- use_module(library(format)).

main([AbsInt|Paths]) :-
    Paths = [_|_], !,
    analysis_start(Paths, [analysis([AbsInt])]).
main(_) :-
    format('Usage: ciaopp-batch <Domain> <Path> [Paths]~n',[]).
