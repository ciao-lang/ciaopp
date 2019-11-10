% TODO: publish ciaopp_batch?

:- doc(version(1*3+0,2019/11/3,11:16*23+'CEST'), "
   @begin{itemize}
   @item New functionality:
     @begin{itemize}
     @item Backported (and improved) incremental analysis (incanal)
       from CiaoPP 0.8.
     @item Integrated incremental and modular analysis (@tt{pp_flag
       incremental=on})
     @item Integrated modular analysis in the general analysis driver.
     @item Added analysis using run-time semantics of assertions to
       the @tt{dd} fixpoint (@tt{pp_flag} @tt{old_trusts=off}).
     @item Fixes in meta-calls (work in progress).
     @item Modularized domains, now they use the aidomain package
       (work in progress).
     @item Added generic, non relational domain with simpler domain operations.
     @item New flag value: restrict modular analysis to the modules of
       a bundle (@tt{pp_flag} @tt{punit_boundary=bundle}).
     @end{itemize}
   @item Performance improvements:
     @begin{itemize}
     @item Added hook to cache library assertions.
     @item Added flag to load modules faster by preloading ciao libraries.
     @item Fixed many dangling choicepoints across all modules.
     @item Fixed performance issues in modular analysis.
     @item Fixed bug of metacalls inside a recursion (@tt{dd} fixpoint).
     @end{itemize}
   @item User interface and documentation:
     @begin{itemize}
     @item Rearranged manual.
     @item Created web interface for demos (see @tt{ciaopp_online} bundle).
     @item Added a high level interface for intermental analisis (incanal).
     @end{itemize}
   @item Benchmarks, internal testing, and debugging:
     @begin{itemize}
     @item Tests/benchmarks moved to a separate bundle (ciaopp_tests).
     @item Added tests for gitlab CI (continuous integration).
     @item Some fixes in the davinci interface.
     @item Fixed (documentation) assertions. CiaoPP can be run with
       the package rtchecks.
     @item Added analysis_stats.pl to unify statistics collecting.
     @item ciaopp-dump-cmp: new command to compare two ciaopp analaysis dumps.
     @item ciaopp-dump-fmt: new command that outputs the analysis in dot format.
     @item New flag value: Raw analysis printer (@tt{pp_flag}
       @tt{output_lang=raw}).
     @item Added @tt{pp_flag} to trace fixpoints.
     @end{itemize}
   @item Other bug fixes, cleanups, refactoring, etc.:
     @begin{itemize}
     @item Removed @tt{api} (now using @tt{p_unit}).
     @item Fixed maintaining @tt{plai_db} for complete operations
     @item Fixed classifying mistakenly recursive predicates as non
       recursive (meta predicates).
     @item Fixed issue with reexported predicates in p_unit.
     @item Fixed problem with meta_predicates that did not have any
       meta argument.
     @item Added @tt{free/1} to @tt{sharefree_clique} domain.
     @item Replaced @tt{runtime_control:statistics/2} by
       @tt{analysis_stats:pp_statistics/2}.
     @item Using @tt{p_unit/program_keys.pl} for the keys of ciaopp.
     @end{itemize}
   @end{itemize}
").

:- doc(version(1*2+0,2006/01/03,11:16*23+'CEST'),
	"New version").

:- doc(version(1*0+0,2001/11/07,19:05*57+'CET'),
	"New version").
