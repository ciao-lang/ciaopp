:- module(_, [], [assertions]).

:- doc(filetype, documentation).

:- doc(title, "CiaoPP at a glance").

:- doc(author, "Isabel Garcia-Contreras").
:- doc(author, "Daniela Ferreiro").

:- doc(module, "

The purpose of this document is to quickly illustrate some of the
kinds of static processing that @apl{CiaoPP} can perform. Note that
this is not intended to be a tutorial, for that please follow @ref{A
Gentle Introduction to Static Verification and Bug Finding with
CiaoPP} or @ref{Program Development using the CiaoPP Program
Processor}.

@section{Setup}

In order to follow these examples you need to either:

@begin{itemize}

@item Install @apl{Ciao} on your computer, including the development
      environment (see the Ciao manual or web site for more
      information). This includes @apl{CiaoPP} (and @apl{LPdoc}). You
      can then access @apl{CiaoPP} from the different IDEs (Emacs,
      VSC), as well as and from the command line.

@item Run @apl{CiaoPP} directly on your browser through the @apl{Ciao}
      playground. To this end, load the examples into the playground
      by pressing the @key{↗} button (``Load in playground''), and
      then @apl{CiaoPP} can be run clicking the @key{More...} button
      and selecting @key{Analyze and check assertions}.

@end{itemize}

The instructions below use the Emacs interface but the steps can also
be performed in the playground version and other interfaces.

@section{Analyzing}
 
Let us analyze this implementation of the append predicate:

```ciao_runnable
:- module(_, [app/3], [assertions]).

:- pred app(A,B,C) : (list(A), list(B)) => var(C).

app([],Y,Y).
app([X|Xs], Ys, [X|Zs]) :- 
    app(Xs,Ys,Zs).
```

Automatic analysis can be performed by using the direct access button in the
Emacs interface @image{Figs/quick-ciaoanalysis}{33}{30}.

By default, @apl{CiaoPP} analyzes programs with a type domain (@tt{eterms}) and a
sharing/freeness (modes) domain (@tt{shfr}). We can open the file with the
inferred information by typing @tt{C-c C-v}.

The inferred information is expressed with (@tt{true}) assertions (for
a more extensive tutorial of the assertion language see @em{Using
assertions for preprocessing programs} in the @apl{CiaoPP}
manual). Assertion marked as @tt{true} contain safe approximations
(safe abstractions) of the behavior of the program that were inferred
by the analyzer. In this case @apl{CiaoPP} inferred:

@exfilter{app_assrt_false.pl}{A,filter=tpred}

The first assertion contains type information and expresses the fact
that @em{predicate @tt{app/3} is called (@tt{:} field) with @var{A}
and @var{B} bound to @tt{lists} and, if it succeeds (@tt{=>} field),
then @var{C} will be a @tt{list}}.

The second assertion contains information about how variables are shared. It was
inferred that when @tt{app(A,B,C)} is called arguments @var{A}, @var{B}, and
@var{C} may be shared and if it succeeds they also will be shared, sice @var{C}
is the concatenation of @var{A} and @var{B}.
 
@section{Assertion Checking}

In the example above, we have also added an assertion with properties that we want
to prove about the execution of the program.

```ciao
:- pred app(A,B,C) : (list(A), list(B)) => var(C).
```
 
This assertion is stating that if predicate @pred{append/3} is called with @var{A} and
@var{B} bound to @tt{list}s, then, if the call succeeds, @var{C} will be a free variable.
This is not true in general of course. We can check
this assertion by clicking the @image{Figs/quick-ciaoasr}{33}{30} icon in the Emacs
interface and we obtain: 

@exfilter{app_assrt_false.pl}{V,filter=warn_error}

Since this assertion does not hold we get a message saying so.

Assertion checking can also be reported within the source code.  If we
open the output file the @apl{CiaoPP} produces (@tt{C-c C-v}), we see
that the analyzer proves the assertion that we had included false:

@exfilter{app_assrt_false.pl}{V,output=on,filter=check_pred}

So we correct it with:

```ciao
:- pred app(A,B,C) : (list(A), list(B)) => list(C).
```
 
and run the analysis again. In this case we get no error messages and, as before,
results can also be reported in the source file:

@exfilter{app.pl}{V,output=on,filter=check_pred}

@section{Program Optimization}

The following program naively implements a predicate that duplicates the first
element of a list.

```ciao_runnable
:- module(_, [dup_first/2], []).

dup_first([X|Xs], Zs) :-
    app([X], [X|Xs], Zs).

app([],Y,Y).
app([X|Xs], Ys, [X|Zs]) :-
    app(Xs,Ys,Zs). 
```

@apl{CiaoPP} can automatically optimize sources by using the @image{Figs/quick-ciaopt}{33}{30} button:
  
@exfilter{dup_first.pl}{O,filter=all}

@section{Advanced Preprocessing}

@apl{CiaoPP} has several parameters for each of the main actions. For more
information, see the @ref{Program Development using the CiaoPP Program Processor}.

").
