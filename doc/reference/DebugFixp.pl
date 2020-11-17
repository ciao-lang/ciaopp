:- use_package(assertions).

:- doc(filetype, part).

:- doc(title,"Debugging the fixpoint operations").

:- doc(module,
"This component is in charge of tracing the fixpoint operations to ease debugging.

@bf{Make sure that the fixpoint that you want to trace is not
importing package notrace (If this is the case, nothing will be shown).}

The fixpoint can be traced in several forms: graphical (with daVinci
graph viewer) or ascii, using @pred{trace_fixp/1}.

@section{Example of visualization}

Note that daVinci executable has to be accesible in the path for Ciao.

@begin{verbatim}
?- trace_fixp(view).     % This will open a uDraw(Graph) window

?- module(PathToModule). % load the module to analyze (located in PathToModule)

?- analyze(AbsInt).      % Analyze for abstract domain AbsInt
% The process will appear in the uDraw(Graph) window.

?- trace_fixp(no).       % Stop the tracing
@end{verbatim}

@begin{alert}
The implementation may not support all features of CiaoPP.

E.g. in the actions: @tt{?- analyze(AbsInt), analyze(AbsInt).} the
second analysis will fail (only if the tracing is on).

@end{alert}


@section{uDraw(Graph) extended features}

A menu is generated in uDraw(Graph) (Edit) that allows to execute the
analysis in a syncronous and asynchronous way (see Edit->Mode) to
swich options.

If the synchronous option is on, once the analysis has started, the
visualization (and the fixpoint) will do one operation each step. The
next step will be performed only if command Edit->'One step ahead' is executed.

").
