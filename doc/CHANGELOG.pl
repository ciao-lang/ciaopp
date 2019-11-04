:- doc(version(1*3+0,2019/11/3,11:16*23+'CEST'),
	"% TODO: publish ciaopp_batch?
@section{Functionality}
        @begin{itemize}
      @item Ported incremental analysis of ciaopp 0.8.
      @item Added a high level interface for incanal.
      @item Integrated incremental and modular analysis (pp_flag incremental=on)
      @item Split tests in a bundle (ciaopp_tests).
      @item ciaopp-dump-cmp: new command to compare two ciaopp analaysis dumps.
      @item ciaopp-dump-fmt: new command that outputs the analysis in dot format.
      @item New flag value: Raw analysis printer (pp_flag output_lang=raw).
      @item Added analysis using run-time semantics of assertions to the dd fixpoint (pp_flag old_trusts=off).
      @item Fixes in meta_calls.
      @item Added hook to cache library assertions.
      @item Added pp flag to trace fixpoints.
      @item Added generic, non relational domain with simpler domain operations.
      @item Modularized domains now they use the aidomain package.
      @item Integrated modular analysis in the general analysis driver.
      @item New flag value: restrict modular analysis to the modules of a bundle (pp_flag punit_boundary=bundle).
      @item Added flag to load modules faster by preloading ciao libraries.
        @end{itemize}

@section{Performance}
        @begin{itemize}
     @item Fixed dangling choicepoints across all modules.
     @item Removed api (now using p_unit).
     @item Fixed performance issues in modular analysis.
     @item Fixed bug of metacalls inside a recursion (fixpo dd).
        @end{itemize}

@section{Other}
        @begin{itemize}
     @item Created web interface for demos.
     @item Rearranged manual.
     @item Created tests for gitlab.
     @item Fixed maintaining plai_db for complete operations
     @item Some fixes in the davinci interface.
     @item Using p_unit/program_keys.pl for the keys of ciaopp.
     @item Fixed (documentation) assertions. CiaoPP can be run with the package rtchecks.
     @item Added analysis_stats.pl to unify statistics collecting.
        @end{itemize}

@section{Minor}
        @begin{itemize}
     @item Fixed classifying mistakenly recursive predicates as non recursive (meta predicates).
     @item Fixed issue with reexported predicates in p_unit.
     @item Fixed problem with meta_predicates that did not have any meta argument.
     @item Added 'free/1' to sharefree_clique domain.
     @item Replaced runtime_control:statistics/2 by analysis_stats:pp_statistics/2.
        @end{itemize}
      ").

:- doc(version(1*2+0,2006/01/03,11:16*23+'CEST'),
	"New version").

:- doc(version(1*0+0,2001/11/07,19:05*57+'CET'),
	"New version").
