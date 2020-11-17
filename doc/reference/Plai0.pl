:- use_package([assertions]).

:- doc(filetype, documentation).

:- doc(title,"PLAI- Abstract Interpretation-based Analysis").

:- doc(module,"
Abstract interpretation based analysis in PLAI is implemented in a parametric
fashion: there are four available fixpoint computation algorithms for the
analysis which can be used with several abstract domains.

The (basic) organization of the code is as follows:

 @image{plai}

Module @lib{plai} is in charge of interfacing with the rest of CiaoPP.
Modules @lib{tarjan}, @lib{normalize}, and @lib{transform} support the 
preprocessing needed for analysis: identify strongly connected components,
normalize the program (if required), and assert it in a format suitable
for analysis, respectively. Module @lib{plai\_db} stores the final
results of analysis. Module @lib{trust} handles the assertions used
during analysis and module @lib{domains} interfaces to the domain-dependent
operations.

Module @lib{fixpo\_plai} implements the classical top-down fixpoint
algorithm of PLAI. In the figure, it represents several other fixpoint
algorithms available, namely: @lib{fixpo\_del} for delay analysis, and
@lib{fixpo\_dd} and @lib{fixpo\_di} for incremental analysis. Module
@lib{re\_analysis} supports the recovery of analysis information after
transformation of the source program.

Modules @lib{trace\_fixp} and @lib{view\_fixp} implement tracing of the
analysis procedure, including a graphic visualization of the and-or graph
being constructed during analysis. ").
%jcf%Module @lib{abs\_graph} allows the
%jcf%visualization of this graph after analysis is finished.
%jcf%").
