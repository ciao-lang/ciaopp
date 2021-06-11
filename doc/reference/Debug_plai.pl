:- use_package(assertions).

:- doc(filetype, documentation).

:- doc(title, "Debugging PLAI analyses").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "This module is intended for debugging fixpoints and abstract
domains. The debugging modes are sorted by difficulty and knowledge required
by the programmer.

General comments. To discard errors related with not cleaning properly internal
databases it is better not to debug in the ciao/ciaopp toplevel, but rather use
the ciaopp command line if possible.

@section{Debug raw analysis result}

Output the analysis result without postprocessing. This is using internal clause
representation of ciaopp and internal representation of the abstract domain. For
this, simply set the flag @tt{output_lang} to @tt{raw}.

For every @bf{reachable} program point there is one or more @tt{true}
annotations, one for every inferred call pattern. In the body, annotations with
the same number correspond to the execution of the abstract call with that
number. A raw assertion will appear with the same id for such abstract call and
success.

Note that this option is specially useful when developing a new abstract domain.
If the predicates @pred{asub_to_info/5}, @pred{asub_to_native/6}, etc are not
defined, no useful information appears in the usual.

@section{Inspect analysis graphs}

Dump the analysis graph in some <file>:
@begin{verbatim}
ciaopp ?- use_module(ciaopp(p_unit/p_dump)).
ciaopp ?- dump(<file>).
@end{verbatim}

Use the command @tt{ciaopp-dump} to inspect:
@begin{verbatim}
$ ciaopp-dump show <file>
     # Print info of the dump <file>.
$ ciaopp-dump fmt <file>
     # Outputs the analysis result in dot format.
$ dot -Tpdf <file>.dot -o <file>.pdf
     # Generates a graph in pdf of the dot analysis format.
@end{verbatim}

@section{Trace fixpoint operations}

Output steps to reach fixpoint. It is useful to combine this option with the raw
output, as it shows the steps to generate the graphs using the same numbers for
ids.

In file @tt{src/plai/fixpoint_options.pl}, uncomment @tt{:- use_package(.(notrace)).}, and recompile:
@begin{verbatim}
$ ciao build --bin ciaopp
@end{verbatim}

@begin{alert}
A clean may be necessary, due to some undetected changes in incremental
compilation of programs with included files.
@begin{verbatim}
$ ciao clean ciaopp
@end{verbatim}
@end{alert}

Then set flag @tt{trace_fixp} to @tt{trace} in the @tt{ciaopp} toplevel or
activate it in the command line:
@begin{verbatim}
$ ciaopp -A <file> -ftrace_fixp=trace
@end{verbatim}

Additionally, if the flag @tt{timestamp_trace} is set to @tt{on} (can only be
set in the @tt{ciaopp} toplevel) a timestamp is printed when tracing. This can
help finding perfomance issues.

@section{Activate run-time checks}

Go to any module, add @tt{:- use_package(rtchecks).} and recompile by
@begin{verbatim}
$ ciao build --bin ciaopp
@end{verbatim}

Modules recommended:
@begin{itemize}
@item Generic domain interface @tt{src/plai/domains.pl}.
@item Any specific domain.
of @tt{src/domains/*} (check that it has assertions!).
@item Fixpoints: @tt{src/plai/fixpoint_options.pl}.
@item Generic fixpoint operations: @tt{src/plai/fixpo_ops.pl}.
@item Modular analysis: @tt{src/plai/intermod_options.pl}.
@item Incremental analysis: @tt{src/plai/incanal/incanal_options.pl}.
@item Assertions during fixpoint: @tt{src/plai/apply_assertions.pl}/@tt{src/plai/apply_assertions_old.pl}.
@end{itemize}


@begin{alert} In @tt{domains.pl} the assertions were written by looking only at
some domains, not all of them. It could happen that they are too restrictive. If
you find that an assertion does not hold in run-time, please open an issue.
@end{alert}

@section{Debug fixpoint step by step}

For this, it is recommended to deactivate run-time checks, as the debugger shows
also the code for RT checking.

Write @tt{:- use_package(debug).} in @tt{src/plai/fixpoint_options.pl} and
recompile:

@begin{verbatim}
$ ciao build --bin ciaopp
@end{verbatim}

In an emacs shell buffer do @tt{M-x ciao-inferior-mode}. Then execute the ciaopp
command to debug

@begin{verbatim}
$ ciaopp -A <file>
@end{verbatim}

@section{Access PLAI databases directly}

@begin{verbatim}
ciaopp ?- use_module(ciaopp(plai/plai_db)).
ciaopp ?- complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents).
ciaopp ?- memo_table(LitKey,AbsInt,Id,Child,Vars_u,Call).
@end{verbatim}

 ").