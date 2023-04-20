:- module(_, [], [assertions]).

:- doc(filetype, documentation).

:- doc(title, "CiaoPP at a glance").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "

In this document we assume that @apl{CiaoPP} has been installed (see
@ref{Installation} for more information) or you have access to @apl{CiaoPP}
through your browser. The examples can be loaded
into a separate playground by pressing the ↗ button (``Load in playground''),
then @apl{CiaoPP} can be run clicking the @key{More...} button and
@key{Analyze and check assertions}. 

Here we want to quickly illustrate the kind of static processing
that @apl{CiaoPP} can perform. Note that this isn’t intended to be a tutorial,
for a full tutorial you can check
@ref{A Gentle Introduction to Static Verification and Bug Finding with CiaoPP}
or @ref{Program Development using the CiaoPP Program Processor}.

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
emacs interface @image{Figs/quick-ciaoanalysis}{33}{30}.

By default, @apl{CiaoPP} analyzes programs with a type domain (@tt{eterms}) and a
sharing/freeness domain (@tt{shfr}). We can open the file with the
inferred information (@tt{C-c C-v}).

The inferred information is expressed with (@tt{true}) assertions (for a more
extensive tutorial of the assertion language see @ref{Using assertions for
preprocessing programs}).

@tt{true} represents abstractions of the behavior of the program inferred by the
analyzer. In this case it was inferred:

@exfilter{app_assrt_false.pl}{A,filter=tpred}

The first assertion contains types information and encodes @em{predicate @tt{app/3} is
called with @var{A} and @var{B} as @tt{lists} and if it succeeds, @var{C} will
be a @tt{list}}.

The second one contains information about how variables are shared. It was
inferred that when @tt{app(A,B,C)} is called arguments @var{A}, @var{B}, and
@var{C} may be shared and if it succeeds they also will be shared, sice @var{C}
is the concatenation of @var{A} and @var{B}.
 
@section{Assertion Checking}

In the example above, we have also add an assertion with properties that we want
to prove about the execution of the program.

```ciao
:- pred app(A,B,C) : (list(A), list(B)) => var(C).
```
 
This assertion is stating that if the predicate is called with a @var{A} and
@var{B} @tt{list}, if it succeeds @var{C} will be a free variable. We can check
this assertion by clicking the @image{Figs/quick-ciaoasr}{33}{30} icon in the emacs
interface:

@exfilter{app_assrt_false.pl}{V,filter=warn_error}

Of course this assertion does not hold and we get a message saying so.

Assertion checking can also be reported within the source code,
if we open the file (@tt{C-c C-v}), we can see that the analyzer does not
verify the assertion that we had included:

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