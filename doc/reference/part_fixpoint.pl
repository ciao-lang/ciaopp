:- module(_, [], [assertions]).

:- doc(filetype, part).

:- doc(title, "Available fixpoints").

:- doc(module, "

@subsection{Analysis with PLAI}

Most of the analyses of CiaoPP are performed with the PLAI (Programming in
Logic with Abstract Interpretation) framework @cite{plai-tr}. 
This framework is based on the computation of a fixed point 
for the information being inferred. Such a fixed point computation is governed 
by flag @tt{fixpoint}, whose values are:

@begin{itemize}
 @item @tt{plai} for the classical fixed point computation @cite{mcctr-ai};
 @item @tt{dd} for an incremental fixed point computation 
       @cite{incanal-toplas};
 @item @tt{di} for the @em{depth independent} fixed point algorithm of
       @cite{inc-fixp-sas};
 @item @tt{check_di} .
@end{itemize}

@subsection{Inter-modular analysis}

In @concept{inter-modular analysis} CiaoPP takes into account the results
of analyzing a module when other modules in the same program are analyzed.
Thus, it collects analysis results (success patterns) for calls to predicates
in other modules to improve the analysis of a given module. It also collects
calls (call patterns) that are issued by the given module to other modules to 
reconsider them during analysis of such other modules.

Such flow of analysis information between modules while being analyzed can
be performed when analyzing one single module. The information flow then
affects only the modules imported by it. New call patterns will be taken
into account when/if it is the turn for such imported modules to be analyzed.
Improved success patterns will only be reused when/if the importing module is
reanalyzed. However, CiaoPP can also iterate continuously over the set of
modules of a given program, transferring the information from one module to
others, and deciding which modules to analyze at which moment. This will be
done until an inter-modular fixed point is reached in the analysis of the
whole program (whereas analysis is performed one-module-at-a-time, anyway).

Inter-modular analysis is enabled with flag @tt{intermod}. During inter-modular
analysis there are several possible choices for selecting success patterns
and call patterns. For example, when a success pattern is required for a given
call pattern to an imported predicate, and there exist several that could
be used, but none of them fit exactly with the given call pattern. Also, if,
in that same case, there are no success patterns that fit (in which case
CiaoPP has to make an @em{initial guess}). Finally, when there are new
call patterns to a given module obtained during analysis of the modules that
import it, which of them to use as entry points should be decided. All
these features are governed by the following flags:

@begin{itemize}
 @item @tt{intermod} to activate inter-modular analysis.
       @begin{itemize}
	@item @tt{off} disables inter-modular analysis.
	               This is the default value.
	@item @tt{on} enables inter-modular analysis.
	@item @tt{auto} allows the analysis of a modular program,
	      using @tt{intermod:auto_analyze/2-3} with the main
	      module of the program, iterating through the module
	      graph until an inter-modular fixed point is
	      reached. This value is set automatically by CiaoPP, and
	      it should not be set by the user.
	@end{itemize}

 @item @tt{success_policy} to obtain success information for given call
       patterns to imported predicates.
       @begin{itemize} 
        @item @tt{best} selects the success pattern which corresponds
	      to the best over-approximation of the sought call pattern; if
	      there are several non-comparable best over-approximations,
	      one of them is chosen randomly.
	@item @tt{first} selects the first success pattern which corresponds
	      to a call pattern which is an
	      over-approximation of the sought call pattern.
	@item @tt{all} computes the greatest lower bound of the
	      success patterns that correspond to over-approximating
	      call patterns.
	@item @tt{top} selects @tt{Top} (no information) as answer pattern 
              for any call pattern.
	@item @tt{botfirst} selects the first success pattern which
	      corresponds to a call pattern which is an
	      under-approximation of the sought call pattern.
        @item @tt{botbest} selects the success pattern which corresponds
	      to the best under-approximation of the sought call pattern; if
	      there are several non-comparable best under-approximations,
	      one of them is chosen randomly.
	@item @tt{botall} computes the least upper bound of the
	      success patterns that correspond to under-approximating
	      call patterns.
	@item @tt{bottom} selects @tt{Bottom} (failure) as answer pattern 
	      for any call pattern. 
	@end{itemize}

 @item @tt{initial_guess} to obtain an initial guess for the success pattern
       corresponding to a call pattern to an imported predicate when there is 
       none that fully matches.
       @begin{itemize}
	@item @tt{botfirst} selects the success pattern already
	      computed corresponding to the first call pattern which is an
	      under-approximation of the given call pattern.
	@item @tt{botbest} selects the success pattern corresponding
	      to the call pattern which best under-approximates the
	      given call pattern (if there are several, non-comparable
	      call patterns, one of them is selected randomly).
	@item @tt{botall} computes the least upper bound of the
	      success patterns that correspond to under-approximating
	      call patterns.
	@item @tt{bottom} selects @tt{Bottom} as initial guess for any call
	      pattern. 
       @end{itemize}

 @item @tt{entry_policy} to obtain entry call patterns for exported predicates.
       @begin{itemize}
        @item @tt{all} selects all entry call patterns for the current
	      module which have not been analyzed yet, either from
	      entry assertions found in the source code, or from the
	      analysis of other modules that import the current
	      module. 
	@item @tt{top_level} is only meaningful during @tt{auto} inter-modular 
              analysis, and it is set automatically by CiaoPP. If the current
	      module is the top-level module (the main module of the
	      modular program being analyzed), the entry policy
	      behaves like @tt{all}. In any other case, it selects
	      entry call patterns for the current module from the
	      analysis of other modules that import it, ignoring entry
	      assertions found in the source code.
	@item @tt{force} forces the analysis of all entries of the
	      module (from both the module source code and calling modules),
	      even if they have been already analyzed.
	@item @tt{force_assrt} forces the analysis of all entries
	      coming from the module source code, but does not analyze
	      entries relative to calling modules, even if they need
	      to be (re)analyzed.
	@end{itemize}

@item @tt{punit_boundary} to indicate which modules must be also analyzed
        when a modular user program is analyzed.
       @begin{itemize}
        @item @tt{off} disables the analysis of any Ciao system library.
        @item @tt{on} enables the analysis of all Ciao system libraries.
        @item @tt{no_engine} enables the analysis of Ciao system
        libraries which are not engine libraries.
        @item @tt{bundle} limits the modular analysis to the modules within the
        bundle of the entry module.
       @end{itemize}

 @item @tt{use_check_assrt} to indicate that check assertions for
       imported predicates will be used as trust assertions.  This is
       specially interesting when performing intermodular compile-time
       checking.
       @begin{itemize}

        @item @tt{off} disables the use of check assertions as trust
              assertions for imported predicates.
        @item @tt{on} enables the use of check assertions as trust 
              assertions.
       @end{itemize}
@end{itemize}

").