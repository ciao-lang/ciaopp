:- doc(version(1*4+0,2020/11/18,6:18*07+'CET'), "
   @begin{itemize}
   @item General changes and new features:
     @begin{itemize}
     @item LLVM-based frontend improved and moved to its own bundle (see
       @tt{ciaopp_llvm} bundle).
     @item Split @tt{typeslib} as a separate bundle.
     @item Allow heads of entry assertions to be non-normalized.
     @item Adapted to new hiord.
     @item [new] Command @tt{ciaopp-dump}, which performs several
       actions over a ciaopp analysis dump: it subsumes the old
       @tt{ciaopp-dump-cmp} and @tt{ciaopp-dump-cmp} commands. New
       options for: showing the contents of a dump file, a code
       reachability report, static, offline checks of assertions using
       a dump file, and general statistics for the analysis results.
     @item [new] Added @tt{-op Suffix} option to ciaopp command-line (useful for flycheck).
     @item [new] Warning if no entries were found
     @item [new] Unified messages, now controlled by @tt{ciaopp_log.pl}
     @item [new] @tt{ciaopp-batch} command to run ciaopp on many files and with timeouts.
     @item [new] Modular (non-incremental) analysis with types (shortening).
     @item [new] Bottom-up incremental update of fixpoint (at literal level).
     @item [new] Modular (non-incremental) analysis with types (shortening).
     @end{itemize}
   
   @item Domains:
     @begin{itemize}
     @item Implemented domains using (a special) trait package.
     @item Added @tt{needs/2} operation.
     @item Renamed @tt{abstypes_abs} to @tt{auxinfo_asub}.
     @item eterms: @tt{member/2}, @tt{=/2} as native properties (for assertions).
     @item pdb:
       @begin{itemize}
       @item Optimize @tt{pdb_compute_lub}: top if any @tt{ASub} is top.
       @item Use @tt{fail} literals.
       @end{itemize}
     @item sharing: fixed @tt{free/1} handlers
     @item shfr: fixes in handlers of @tt{==/2}, @tt{=/2},
       @tt{'\\\\=='/2}, @tt{'\\\\='/2}, @tt{free/1} (native version of
       @tt{var/1})
     @end{itemize}
   
   @item Fixpoints:
     @begin{itemize}
     @item Split compilation options (@tt{debug}, @tt{trace},
       @tt{rtchecks}) in common file @tt{fixpoint_options.pl}
     @item Improved tracing of clauses
     @item Refactored fixpoints to make them easier to merge
     @end{itemize}

   @item Fixpoint @tt{dd}:
     @begin{itemize}
     @item [fix] Reuse a complete with the same head but different vars order
     @item [performance] Using get_memo_table because Id+Key is unique
     @item [fix] Case in which a literal is not reachable
     @item Improved documentation
     @end{itemize}
   
   @item Analysis of higher-order code:
     @begin{itemize}
     @item [new] Flag for automatic generation of entries of meta
       calls.
     @item [fix] @tt{call/N} was not being detected as meta predicate
       (and flattened when possible).
     @item [new] @tt{\\\\+} not treated as meta, flatten calls known at
       compile time.
     @end{itemize}

   @item Flags and options menu:
     @begin{itemize}
     @item [new] Flag to remove useless (unreachable) completes after fixpo.
     @item @tt{punit_boundary}: change default value to bundle.
     @item Included @tt{incanal} flag, changed @tt{ext_policy} in menu
       (same as @tt{pp_flag}).
     @item Improved options menu (added and simplified dependencies,
       simplified text, grouped actions, better documentation).
     @end{itemize}
   @end{itemize}
").

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
