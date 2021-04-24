:- module(_, [], [assertions]).

:- doc(filetype, documentation).

:- doc(title, "CiaoPP Quick Tutorial").

:- doc(author, "Isabel Garcia-Contreras").


:- doc(module, "

Quick guide to using @apl{CiaoPP}.

In this tutorial we assume that CiaoPP has been installed (see
@ref{Installation} for more information).

For more information see the @ref{Advanced Tutorial on Program
Development and Optimization using the CiaoPP Program Processor}.

In this tutorial we want to quickly illustrate the kind of static processing
that @apl{CiaoPP} can perform.

@section{Analyzing}

Let us analyze this implementation of the append predicate:

@includecode{tut_examples/app}

Automatic analysis can be performed by using the direct acces button in the
emacs interface @image{Figs/quick-ciaoanalysis}{33}{30}.

By default, CiaoPP analyzes programs with a type domain (@ref{eterms}) and a
sharing/freeness domain (@ref{shfr}):

@image{Figs/quick-analyze-after}{636}{751}

The inferred information is expressed with (@tt{true}) assertions (for a more
extensive tutorial of the assertion language see @ref{Using assertions for
preprocessing programs}).

@tt{true} represents abstractions of the behavior of the program inferred by the
analyzer. In this case it was inferred:

@begin{verbatim}
:- true pred app(A,B,C) % (1)
     : ( list(A), list(B), term(C) )
    => ( list(A), list(B), list(C) ).

:- true pred app(A,B,C) % (2)
     : mshare([[A],[A,B],[A,B,C],[A,C],[B],[B,C],[C]])
    => mshare([[A,B,C],[A,C],[B,C]]).
@end{verbatim}

Assertion (1) contains types information and encodes @em{predicate @tt{app/3} is
called with @var{A} and @var{B} as @tt{lists} and if it succeeds, @var{C} will
be a @tt{list}}.

Assertion (2) contains information about how variables are shared. It was
inferred that when @tt{app(A,B,C)} is called arguments @var{A}, @var{B}, and
@var{C} may be shared and if it succeeds they also will be shared, sice @var{C}
is the concatenation of @var{A} and @var{B}.

@section{Assertion Checking}

Let us add an assertion with properties that we want to prove about the
execution of the program.

@includecode{tut_examples/app_assrt_false}

This assertion is stating that if the predicate is called with a @var{A} and
@var{B} @tt{list}, if it succeeds @var{C} will be a free variable. We can check
this assertion by clicking the @image{Figs/quick-ciaoasr}{33}{30} icon in the emacs
interface:

@image{Figs/quick-false-assertion}{636}{751}

Of course this assertion does not hold and we get a message saying so.

Assertion checking can also be reported within the source code by typing
\"@tt{output.}\" in the @apl{CiaoPP} top-level and open the file (@tt{C-c C-v}).
This feature is experimental:

@image{Figs/quick-false-assertion-full}{636}{751}

This assertion was wrong so we correct it with:
@begin{verbatim}
:- pred app(A,B,C) : (list(A), list(B)) => list(C).
@end{verbatim}
 
and run the analysis again. In this case we get no error messages and, as before,
results can also be reported in the source file:

@image{Figs/quick-checked-assertion}{636}{751}

@section{Program Optimization}

The following program naively implements a predicate that duplicates the first
element of a list.

@includecode{tut_examples/dup_first}

@apl{CiaoPP} can automatically optimize sources by using the @image{Figs/quick-ciaopt}{33}{30} button:

@image{Figs/quick-optimization}{636}{751}

@section{Advanced Preprocessing}

@apl{CiaoPP} has several parameters for each of the main actions. For more
information, see the @ref{Advanced Tutorial on Program Development and
Optimization using the CiaoPP Program Processor}.

").
