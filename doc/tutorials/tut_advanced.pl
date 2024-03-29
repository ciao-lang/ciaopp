:- module(_, [], [assertions]).

:- doc(filetype, documentation).

:- doc(title, "Program Development using the
   CiaoPP Program Processor").

:- doc(author, "The Ciao Development Team").

%%% Uncomment for the large version of this tutorial
%:- compilation_fact(full_tutorial).
 
:- if(defined(full_tutorial)).  
% TODO: Review summary (think about what we want to say about parallelization)
:- doc(summary,
"We present in a tutorial fashion @apl{ciaopp}, the preprocessor of the Ciao
multi-paradigm programming system, which implements a novel program
development framework which uses abstract interpretation as a
fundamental tool. The framework uses
    @comment{modular, incremental} abstract
interpretation to obtain information about the program. This
information is used to validate programs, to detect bugs with respect
to partial specifications written using assertions (in the program
itself and/or in system libraries), to generate and simplify run-time
tests, and to perform high-level program transformations such as
multiple abstract specialization, parallelization, and resource usage
control, all in a provably correct way. In the case of validation and
debugging, the assertions can refer to a variety of program points
such as procedure entry, procedure exit, points within procedures, or
global computations.  The system can reason with much richer
information than, for example, traditional types. This includes data
structure shape (including pointer sharing), bounds on data structure
sizes, and other operational variable instantiation properties, as
well as procedure-level properties such as determinacy, termination,
non-failure, and bounds on resource consumption (time or space cost).").

:- endif.

:- if(defined(full_tutorial)).
%%% IG: I think this is good for selling but it does not belong in the tutorial
%%% maybe put a link to this description?
:- doc(module, "
 We describe in a tutorial fashion @apl{ciaopp}, an implementation of a novel
programming framework which uses extensively abstract interpretation
as a fundamental tool in the program development process.  The
framework uses modular, incremental abstract interpretation to obtain
information about the program, which is then used to validate
programs, to detect bugs with respect to partial specifications
written using assertions (in the program itself and/or in system
libraries), to generate run-time tests for properties which cannot be
checked completely at compile-time and simplify them, and to perform
high-level program transformations such as multiple abstract
specialization, parallelization, and resource usage control, all in a
provably correct way.

@apl{ciaopp} is the preprocessor of the @apl{ciao} program development
system @cite{ciao-reference-manual-tr}. @apl{ciao} is a multi-paradigm
programming system, allowing programming in logic, constraint, and
functional styles (as well as a particular form of object-oriented
programming).  At the heart of Ciao is an efficient logic
programming-based kernel language. This allows the use of the very
large body of approximation domains, inference techniques, and tools
for abstract interpretation-based semantic analysis which have been
developed to a powerful and mature level in this area (see, e.g.,
@cite{ai-jlp,LeCharlier94:toplas,gallagher-types-iclp94,full-prolog-esop96,anconsall-acm,ciaopp-iclp99-tut,ciaopp-sas03-journal-scp}
and their references). These techniques and systems can approximate at
compile-time, always safely, and with a significant degree of
precision, a wide range of properties which is much richer than, for
example, traditional types.  This includes data structure shape
(including pointer sharing), independence, storage reuse, bounds on
data structure sizes and other operational variable instantiation
properties, as well as procedure-level properties such as determinacy,
termination, non-failure, and bounds on resource consumption (time or
space cost). ").
:- endif. 

%   By design, @apl{ciaopp} is a generic tool that can be easily customized
%   to different
%   programming systems and dialects and allows the integration of
%   additional analyses in a simple way. As a particularly interesting
%   example, the preprocessor has been adapted for use with the CHIP
%   @tt{clpfd} system. This has resulted in CHIPRE, a preprocessor for CHIP
%   which has been shown to detect non-trivial programming errors in
%   CHIP programs.
%   More information on the CHIPRE system and an example of a debugging
%   session with it can be found in @cite{preproc-disciplbook}.


:- doc(module, "
@apl{CiaoPP} is a standalone preprocessor to the standard clause-level
compiler. It performs source-to-source transformations. The input to
@apl{CiaoPP} are logic programs (optionally with assertions and syntactic
extensions). The output are @em{error/warning messages} plus the
@em{transformed logic program}, with
results of @bf{analysis} (as assertions),
results of @bf{static checking of assertions},
@bf{assertion run-time checking code}, and
@bf{optimizations} (specialization, parallelization, etc.).

This tutorial is organized as follows:

@begin{itemize}
@item @ref{Getting Started} gives the ''getting started'' basics.
@item @ref{Static Analysis and Program Assertions} shows how @apl{CiaoPP}
performs program analysis.
@item @ref{Program Debugging and Assertion Checking} does the same for 
program debugging and validation.
@comment{
@item @ref{Source Program Optimization} presents @apl{CiaoPP} at work for program
transformation and optimization.
}
@end{itemize}

@section{Getting Started}

In order to follow these examples you need to either:

@begin{itemize}

@item Install @apl{Ciao} on your computer, including the development
      environment (see the @em{Ciao installation instructions} for
      more information). This includes @apl{CiaoPP} (and
      @apl{LPdoc}). You can then access @apl{CiaoPP} from the Emacs or
      VSC interfaces, or from the command line.  

@item Run @apl{CiaoPP} directly on your browser through the @apl{Ciao}
      playground. To this end, load the examples into the playground
      by pressing the @key{↗} button (''Load in playground''), and
      then @apl{CiaoPP} can be run by clicking the @key{More...}
      button and selecting @key{Analyze and check assertions}.

@end{itemize}

However, to follow this tutorial we recommend local installation,
since some of the advanced features may not be yet included in the
playground.  The instructions below use the Emacs interface.

A @apl{CiaoPP}  session consists in the preprocessing of a file. The session is
governed by a @bf{menu}, where you can choose the kind of preprocessing you want to
be done to your file among several analyses and program transformations
available. This tutorial shows how to customize the preprocessing but some
predefined preprocessing options are described in @ref{CiaoPP at a glance}.

Clicking on the icon @image{Figs/button-options-new}{38}{34}
in the buffer containing the file to be preprocessed displays the menu, which
will look (depending on the options available in the current @apl{CiaoPP} 
version) something like the ''Preprocessor Option Browser'' shown in:

@image{Figs/naive-menu-new}{650}{375}

Except for the first line, which refers to selecting levels of customization.
You can select @bf{analysis} and @bf{assertion checking}
 (@tt{analyze_check}) or
@bf{program optimization} (@tt{optimize}), and you can later combine the four kinds
of preprocessing. The relevant options for the @tt{action} selected are
then shown, together with the relevant flags.

A description of the values for each option will be given as it is
used in the corresponding section of this tutorial.

@section{Static Analysis and Program Assertions}

The fundamental functionality behind @apl{CiaoPP} is static global program
analysis, based on abstract interpretation. For this task @apl{CiaoPP} uses the
PLAI abstract interpreter @cite{ai-jlp,effofai-toplas}.

@comment{including extensions
for, e.g., incrementality @cite{incanal-toplas,inc-fixp-sas}, modularity
@cite{full-prolog-esop96,ciao-modules-analspec-entcs,modular-anal-lopstr},
analysis of constraints @cite{anconsall-acm-short}, and analysis of concurrency
@cite{delay-popl}.}

The system infers information
on variable-level properties such as @bf{moded types, definiteness,
freeness, independence, and grounding dependencies}: essentially,
precise data structure shape and pointer sharing. It can also infer
@bf{bounds on data structure sizes}, as well as procedure-level properties
such as @bf{determinacy, termination, non-failure, and bounds on resource
consumption} (time or space cost). @apl{CiaoPP} implements several techniques
for dealing with ''difficult'' language features (such as
side-effects, meta-programming, higher-order, etc.)  and as a result
can for example deal safely with arbitrary ISO-Prolog
programs @cite{full-prolog-esop96}. A unified language of assertions
@cite{full-prolog-esop96,assert-lang-disciplbook} is used to express
the results of analysis, to provide input to the analyzer
of program specifications for debugging and validation, as
well as the results of the comparisons performed against the
specifications.

@subsection{Static Analysis Basics}

Consider the program defining a module which exports the @tt{qsort} predicate:

```ciao_runnable
:- module(_, [qsort/2], [assertions]).

:- pred qsort(A,B) : (list(num, A), var(B)).

qsort([],[]).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg),
    qsort(Sm,SmS), qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2):-
    X =< F, partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]):-
    X > F, partition(Y,F,Y1,Y2).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).
```

We have added a @tt{pred} assertion for the exported predicate
@tt{qsort} expressing that it should be called with its first argument
bound to a list of numbers.

Note the use of builtin properties (i.e., defined in modules which are
loaded by default, such as @tt{var}, @tt{num}, @tt{list}, etc.).  Note
also that @bf{properties natively understood by different analysis
domains can be combined} in the same assertion.

The @bf{sharing and freeness} analysis abstract domain computes
@bf{freeness, independence, and grounding dependencies} between
program variables.

It is performed by selecting the menu option @tt{Aliasing-Mode}:

@image{Figs/analysis-shfr-new}{600}{375}

The output of the analysis is performed via @em{assertions} (see
section @em{Using assertions for preprocessing programs}
in the @apl{CiaoPP} manual for a detailed description). In this
case three assertions appear:
 
@exfilter{qsort.pl}{A,types=none,modes=shfr,filter=tpred}
 
These @em{assertions} express, for example, that the third and fourth arguments
of @tt{partition} have ''output mode'': @bf{when @tt{partition} is called
(@tt{:}) @var{Y1} and @var{Y2} are free unaliased variables} and they are
@bf{ground on success (@tt{=>})}. Also, @tt{append} is used in a mode in which
the first and second argument are input (i.e., ground on call). 
").

%%%%% IG: Old from modular example
% and imports predicates @tt{geq} and @tt{lt} from module
% @tt{compare}. During the analysis of this program, CiaoPP will take advantage
% of the fact that the only predicate that can be called from outside is the
% @em{exported} predicate @tt{qsort}. This allows CiaoPP to infer more precise
% information than if it had to consider that all predicates may be called in any
% possible way (as would be true had this been a simple \"user\" file instead of a
% module). Also, assume that the @tt{compare} module has already been analyzed.
% This allows CiaoPP to be more efficient and/or precise, since it will use the
% information obtained for @tt{geq} and @tt{lt} during analysis of @tt{compare}
% instead of either (re-)analyzing @tt{compare} or assuming topmost substitutions
% for them. Assuming that @tt{geq} and @tt{lt} have a similar binding behavior
% as the standard comparison predicates, a mode and independence analysis
% (\"sharing+freeness\" @cite{freeness-iclp91}) of the module using CiaoPP yields
% the following results:@footnote{In the \"sharing+freeness\" domain @tt{var}
% denotes variables that do not point yet to any data structure, @tt{mshare}
% denotes pointer sharing patterns between variables. Derived properties
% @tt{ground} and @tt{indep} denote respectively variables which point to
% data structures which contain no pointers, and pairs of variables which point to
% data structures which do not share any pointers.}

:- doc(module, "
@subsection{Type Analysis}

@apl{CiaoPP} can infer @bf{(parametric) types} for programs both at the predicate
level and at the literal level
@cite{gallagher-types-iclp94,set-based-absint-padl,eterms-sas02}. Different type
domains can be selected with the menu option @code{Shape-Type} Analysis. As
shown in the following screenshot:

@image{Figs/analysis-eterms-new}{600}{375}

At the predicate level the inferred information is:

@exfilter{qsort.pl}{A,types=eterms,modes=none,filter=tpred}

where @tt{term} is any term and prop @tt{list} and @tt{list1} are defined
in @tt{library(lists)} as:
```ciao
:- regtype list(T,L) #\"@var{L} is a list of @var{T}'s.\".
:- meta_predicate list(pred(1),?).
list(_T,[]).
list(T,[X|L]) :- T(X), list(T,L).

:- regtype list1(T,X) # \"@var{X} is a list of @var{Y}s of at least one element.\".
:- meta_predicate list1(pred(1),?).
list1(T,[X|R]) :- T(X), list(T,R).
```

@subsection{Non-failure and Determinacy Analysis:}

@apl{CiaoPP} includes a @bf{non-failure} analysis, based on
@cite{non-failure-iclp97} and @cite{nfplai-flops04}, which can detect procedures
and goals that can be @bf{guaranteed not to fail}, i.e., to produce at least one
solution or not terminate. It also can detect predicates that are
@bf{''covered''}, i.e., such that for any input (included in the calling type of
the predicate), there is at least one clause whose ''test'' (head unification
and body builtins) succeeds. @apl{CiaoPP} also includes a @bf{determinacy} analysis
based on @cite{determ-lopstr04}, which can detect predicates which produce at
most one solution, or predicates whose clause tests are mutually exclusive, even
if they are not deterministic (because they call other predicates that can
produce more than one solution). Programs can be analyzed with this kind of
domains by selecting to perform @code{Non-Failure} Analysis with domain
@code{nf}:
 
@image{Figs/analysis-nf-new}{600}{375}
 
Analyzing qsort with the @code{nf} domain will produce (among others) the
following assertion:

@exfilter{qsort.pl}{A,ana_nf=nf,name=qsort,filter=tpred_plus}

The @tt{+} field in @tt{pred} assertions can contain a conjunction of global
properties of the @em{computation} of the predicate. @tt{not_fails} states
that if the precondition is met, the @bf{predicate will never fail}.

").

:- doc(module, "
@subsection{Size, Resources, and Termination Analysis}
 
@apl{CiaoPP} can also
infer lower and upper bounds on the sizes of terms and the computational
cost of predicates @cite{low-bou-sas94,low-bounds-ilps97}.  The cost
bounds are expressed as functions on the sizes of the input arguments
and yield the number of resolution steps. Various measures are used
for the ''size'' of an input, such as list-length, term-size,
term-depth, integer-value, etc.
Note that obtaining a non-infinite upper bound on cost also implies
proving @bf{termination} of the predicate.

Our resource analysis is @bf{parametric on the resources}, therefore a package
defining the resource to be used has to be imported in the module, in this case
we use the default package that infers information about computation al steps.
This is done by replacing the first line by:

```ciao
:- module(qsort, [qsort/2], [assertions,predefres(res_steps)]).
```

Also, to be able to infer lower bounds a non-failure and determinacy analysis
has to be performed:

@image{Figs/analysis-resources-new}{600}{375}

As an example, the following assertions are part of the output of 
the upper bounds analysis:

@exfilter{qsort2.pl}{A,ana_nf=nfdet,ana_cost=resources,name=qsort,assertion=[cost,ub],filter=tpred_plus}

@exfilter{qsort2.pl}{A,ana_nf=nfdet,ana_cost=resources,name=append,assertion=[cost,ub],filter=tpred_plus}

For example, the second assertion is inferring @bf{on success
@tt{size(ub,length,B,length(X)+length(A))}}, which means that @bf{an (upper) bound}
on the size of the third argument of @tt{append/3} is the @bf{sum of the sizes
of the first and second arguments}. The inferred @bf{upper bound on
computational steps} (@tt{+ cost(ub,steps,length(_A)+1)}) is @bf{the length of
the first argument} of @tt{append/3}.

The following is the output of the lower-bounds analysis:

@exfilter{qsort2.pl}{A,ana_nf=nfdet,ana_cost=resources,name=qsort,assertion=[cost,lb],filter=tpred_plus}

@exfilter{qsort2.pl}{A,ana_nf=nfdet,ana_cost=resources,name=append,assertion=[cost,lb],filter=tpred_plus} 

The lower-bounds analysis uses information from the non-failure
analysis, without which a trivial lower bound of 0 would be derived.

In this case it is inferred that on success the lower bound of the third
argument of append is @bf{size(lb,length,_B,length(X)+length(_A))} (the same as the
upper bound!), and the @bf{upper bound on computational steps} @tt{+
cost(lb,steps,0)}, which represents the case in which the first list to
concatenate is empty.

").  
  
:- doc(module, "
@subsection{Decidability, Approximations, and Safety}

As a final note on the analyses, it should be pointed out that since most of the
@bf{inferred properties are in general undecidable at compile-time}, the
inference technique used, abstract interpretation, @bf{is necessarily
@em{approximate}}, i.e., possibly imprecise. On the other hand, such
approximations are also always @bf{guaranteed to be safe}, in the sense that (modulo
bugs, of course) they are @bf{never @em{incorrect}}: the properties stated in
inferred assertions do always hold of the program.

@section{Program Debugging and Assertion Checking}
@apl{CiaoPP} is also capable of static assertion checking, and
debugging using the ideas outlined so far. To this end, it implements
the framework described in @cite{prog-glob-an,preproc-disciplbook}
which involves several of the tools which comprise @apl{CiaoPP}.
The following figure depicts the overall
architecture.

@image{Figs/ciaopp-framework}

Hexagons represent the different tools involved and arrows indicate
the communication paths among them.

Program verification and detection of errors is first @bf{performed at compile-time
by inferring properties of the program via abstract interpretation-based static
analysis} and comparing this information against (partial) specifications written
in terms of assertions (see @cite{ciaopp-sas03-journal-scp} for a detailed
description of the sufficient conditions used for achieving this @apl{CiaoPP}
functionality).

The @bf{static checking} is @bf{provably @em{safe}} in the sense
that @bf{all errors flagged are definite violations of the specifications}.

@subsection{Assertions and Properties}

As introduced before, @bf{assertions are a means of specifying @em{properties}} which
are (or should be) true of a given predicate, predicate argument, and/or
@em{program point}. See section @em{Using assertions for preprocessing programs}
in the @apl{CiaoPP} manual for a more detailed description of the concepts that we
briefly introduce now.

They are of the form @code{:- [Status] Scope Head : Pre => Post + Comp.}, where
@var{Status} is a qualifier of the meaning of the assertion, @var{Scope}
describes where the assertion is applied, @var{Head} is a normalized atom, and
@var{Pre}, @var{Post}, and @var{Comp} are conjunctions of @bf{properties}.

So far we have seen assertions with @var{Status} @bf{@tt{true}}, which mean that
they express the @bf{behavior inferred by the analyzer}. This status can only
appear in the output of the analyzer (i.e. the user should not use it).

@begin{itemize}

@item @bf{@tt{check}}: (input and output status) @bf{default} status (i.e., if
no status is specified), expresses properties that the user wants @bf{ensured to
hold at run-time}, i.e., that the analyzer should prove (or else generate run-time checks for). 
@item @bf{@tt{trust}}: (input status) the assertion represents an @bf{actual
behavior} of the predicate that @bf{the analyzer may not be able to infer
automatically}.
@item @bf{@tt{checked}}: (output status) the assertion was @bf{proved to hold
statically} by the analyzer.
@item @bf{@tt{false}}: (output status) the assertion was @bf{proved not to hold
statically} by the analyzer.

@end{itemize}

@comment{% IG: trust assertions are not working.
Assertions can also be used to provide information to the analyzer in
order to increase its precision or to describe predicates which have
not been coded yet during program development.  These assertions have
a @tt{trust} prefix @cite{full-prolog-esop96}.  For example, if we
commented out the @tt{use_module/2} declaration in
Figure @ref{fig:qsort}, 
we could describe the mode of the (now
missing) @tt{geq} and @tt{lt} predicates to the analyzer for example
as follows:
```ciao
:- trust pred geq(X,Y) => ( ground(X), ground(Y) ).
:- trust pred lt(X,Y)  => ( ground(X), ground(Y) ).
```

The same approach can be used if the predicates are written in, e.g.,
an external language such as, e.g., C or Java. Finally, assertions
with a @tt{check} prefix 
are the ones used to specify the @em{ intended} semantics of the
program, which can then be used in debugging and/or validation, 
as we will see later in this section.
Interestingly, this
very general concept of assertions is also particularly useful for
generating documentation automatically (see @cite{lpdoc-cl2000} for a
description of their use by the Ciao auto-documenter).
}

    ").

:- if(defined(full_tutorial)).
:- doc(module, "
@subsection{Scope of assertions}

Assertions refer to certain program points. The @tt{true pred}
assertions above specify in a combined way properties of both the
entry (i.e., upon calling) and exit (i.e., upon success) points of
@em{all calls} to the predicate. It is also possible to express
properties which hold at points between clause literals. As an example
of this, the following
is a fragment of the output produced by CiaoPP for the program in
Figure @ref{fig:qsort} when information is requested at this level:

```ciao
qsort([X|L],R) :-
  true((ground(X),ground(L),var(R),var(L1),var(L2),var(R2), ...
  partition(L,X,L1,L2),
  true((ground(X),ground(L),ground(L1),ground(L2),var(R),var(R2), ...
  qsort(L2,R2), ...
```
 ").
:- endif.


:- doc(module, "

In @apl{CiaoPP} @bf{properties are predicates}, which may be @bf{builtin or user defined}.
For example, the property @tt{var} used in the above examples is the standard
builtin predicate to check for a free variable. The same applies to @tt{ground}
and @tt{mshare}. The properties used by an analysis in its output (such as
@tt{var}, @tt{ground}, and @tt{mshare} for the previous mode analysis) are said
to be @em{native} for that particular analysis. The system requires that
properties be marked as such with a @tt{prop} declaration which must be visible
to the module in which the property is used.

@comment{In addition, properties which are
to be used in run-time checking (see later) should be defined by a (logic)
program or system builtin, and also visible.}

Properties declared and/or @bf{defined}
in a module can be @bf{exported} as any other predicate. For example:
```ciao
:- prop list/1.
list([]).
list([_|L]) :- list(L).
```
or, using the functional syntax package, more compactly as:
```ciao
:- prop list/1. list := [] | [_|list].
```

defines the property @tt{list}. A list is an instance of a very useful class of
user-defined properties called @em{regular types}
@cite{yardeni87,Dart-Zobel,gallagher-types-iclp94,set-based-absint-padl,eterms-sas02},
which herein are simply a syntactically restricted class of logic programs. We
can mark this fact by stating @tt{:- regtype list/1.} instead of @tt{:-
prop list/1.} (this can be done automatically). The definition above can be
included in a user program or, alternatively, it can be imported from a system
library, e.g.: @tt{:- use_module(library(lists),[list/1]).}

@subsection{Using analysis information for debugging}

The idea of using analysis information
for debugging comes naturally after observing analysis @bf{outputs for
erroneous programs}.  Consider this buggy implementation of @tt{qsort}:

```ciao_runnable
:- module(qsort, [qsort/2], [assertions]).

:- pred qsort(A,B) : (list(num, A), var(B)).

qsort([],[]).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg),
    qsort(Sm,SmS), qsort(Lg,LgS),
    append(SmS,[x|LgS],Result).  % <-- 'x' should be X (variable)

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2):-
    X =< F, partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]):-
    X > F, partition(Y,F,Y1,Y2).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).
```

The result of regular type analysis for this program includes the
following code:

@exfilter{bugqsort.pl}{A,types=eterms,name=qsort,modes=none,filter=tpred}

@comment{
```ciao
:- true pred qsort(A,B)
     : ( list(num,A), term(B) )
    => ( list(num,A), list(^(x),B) ).
```
}
where @bf{@tt{list(^x,B)} means ''B is a list of atoms @tt{x}.''}. The information
inferred does not seem compatible with a correct definition of @tt{qsort}, which
clearly points to a bug in the program.

@subsection{Static Checking of Assertions in System Libraries}

In addition to manual inspection of the analyzer output, @apl{CiaoPP} includes a
number of automated facilities to help in the debugging task. For example,
@apl{CiaoPP} can @bf{find incompatibilities} between the ways in which library
predicates are called and their intended mode of use, expressed in the form of
assertions in the libraries themselves. Also, the preprocessor can @bf{detect
inconsistencies in the program} and @bf{check the assertions} present in other
modules used by the program.


Consider a different implementation of @tt{qsort}, also with bugs:

```ciao_runnable
:- module(_, [qsort/2], [assertions]).

:- pred qsort(A,B) : (list(num, A), var(B)).

qsort([X|L],R) :-
    partition(L,L1,X,L2),         % <-- swapped second and third arguments
    qsort(L2,R2), qsort(L1,R1),
    append(R2,[X|R1],R).
qsort([],[]).

partition([],_B,[],[]).
partition([e|R],C,[E|Left1],Right):-  % <-- 'e' should be E (variable)
    E < C, !, partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]):-
    E >= C, partition(R,C,Left,Right1).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).
```

By default, the option @em{Static assertion checking} is set to @em{on},
which means that the system will @bf{automatically detect the analyses to be
performed} in order to check the program, depending on the information available
in the program assertions (in the example in the pred assertion informs how the
predicate @tt{qsort/2} will be called using types and modes information only).

Using the default options, and running @apl{CiaoPP}, we obtain the following
messages (and the system highlights the line
which produces the first of them), as shown:

@exfilter{bugqsort2.pl}{V,filter=warn_error}

First and the last two messages warn that all @bf{calls to @tt{partition} and @tt{>=/2} will
fail}, something normally not intended (e.g., in our case). The error message
indicates @bf{a wrong call to a builtin predicate}, which is an obvious error. This
error has been detected by comparing the mode information obtained by global
analysis, which at the corresponding program point indicates that the second
argument to the call to @tt{>=/2} is a variable, with the assertion:

```ciao
:- check calls B>=A
   : ( nonvar(B), nonvar(A), arithexpression(B), arithexpression(A) ).
```

which is present in the default builtins module, and which implies that the two
arguments to @tt{>=/2} should be ground when this arithmetic predicate is
called. The message signals a compile-time, or @em{abstract}, incorrectness
symptom @cite{aadebug97-informal}, indicating that the program does not satisfy
the specification given (that of the builtin predicates, in this case). Checking
the indicated call to @tt{partition} and inspecting its arguments we detect that
in the definition of @tt{qsort}, @tt{partition} is called with the second and
third arguments in reversed order -- @bf{the correct call is
@tt{partition(L,X,L1,L2)}}.

After correcting this bug, we proceed to perform another round of
compile-time checking, which continues producing the following message:

@exfilter{bugqsort3.pl}{V,filter=warn_error}

This time the error is in the second clause of @tt{partition}.
Checking this clause we see that in the first argument of the head
there is an @tt{e} which should be @tt{E} instead.
Compile-time checking of the program with this bug corrected does not
produce any further warning or error messages.
").  
  
:- doc(module, "
@comment{
Consider a different implementation of @tt{qsort}, also with bugs:

We run compile-time error checking and selecting type and mode analysis for our
tentative @tt{qsort} program, by selecting the action @em{check_assertions}.


By default, the option @em{Perform Compile-Time Checks} is set to @em{auto},
which means that the system will @bf{automatically detect the analyses to be
performed} in order to check the program, depending on the information available
in the program assertions (in the example in The entry assertion informs how the
predicate @tt{qsort/2} will be called using types and modes information only).


Using the default options, and setting @em{Report Non-Verified Assrts} to
@em{error}, we obtain the following messages (and the system highlights the line
which produces the first of them, as shown:

```ciao-inferior
WARNING (preproc_errors): (lns 5-8) goal qsort2:partition(L,L1,X,L2) at literal 1 does not succeed!

WARNING (ctchecks_messages): (lns 11-12) the head of clause 'qsort2:partition/4/2' is incompatible with its call type
     Head:      qsort2:partition([e|R],C,[E|Left1],Right)
     Call Type: qsort2:partition(basic_props:list(num),term,num,term)

WARNING (preproc_errors): (lns 13-14) goal arithmetic:>=(E,C) at literal 1 does not succeed!
```

First and last messages warn that all @bf{calls to @tt{partition} and @tt{>=/2} will
fail}, something normally not intended (e.g., in our case). The error message
indicates @bf{a wrong call to a builtin predicate}, which is an obvious error. This
error has been detected by comparing the mode information obtained by global
analysis, which at the corresponding program point indicates that the second
argument to the call to @tt{>=/2} is a variable, with the assertion:

```ciao-inferior
:- check calls A>=B : (ground(A), ground(B)).
```

which is present in the default builtins module, and which implies that the two
arguments to @tt{>=/2} should be ground when this arithmetic predicate is
called. The message signals a compile-time, or @em{abstract}, incorrectness
symptom @cite{aadebug97-informal}, indicating that the program does not satisfy
the specification given (that of the builtin predicates, in this case). Checking
the indicated call to @tt{partition} and inspecting its arguments we detect that
in the definition of @tt{qsort}, @tt{partition} is called with the second and
third arguments in reversed order -- @bf{the correct call is
@tt{partition(L,X,L1,L2)}}.

After correcting this bug, we proceed to perform another round of
compile-time checking, which continues producing the following message:
```ciao-inferior
WARNING (ctchecks_messages): (lns 11-12) the head of clause 'qsort2:partition/4/2' is incompatible with its call type
     Head:      qsort2:partition([e|R],C,[E|Left1],Right)
     Call Type: qsort2:partition(basic_props:list(num),term,num,term)
```
This time the error is in the second clause of @tt{partition}.
Checking this clause we see that in the first argument of the head
there is an @tt{e} which should be @tt{E} instead.
Compile-time checking of the program with this bug corrected does not
produce any further warning or error messages.
}
").  
  
:- doc(module, "
@subsection{Static Checking of User Assertions and Program Validation}

Though, as seen above, it is often possible to detect error without
adding assertions to user programs, if the program is not correct, the
more assertions are present in the program the more likely it is for
errors to be automatically detected. Thus, for those parts of the
program which are potentially buggy or for parts whose correctness is
crucial, the programmer may decide to invest more time in writing
assertions than for other parts of the program which are more
stable. In order to be more confident about our program, we add to it
the following @tt{check} assertions (the @tt{check} prefix is assumed
when no prefix is given, as in the example shown):

```ciao
:- pred qsort(A,B) : (list(num, A), var(B)).

qsort([X|L],R) :-
    partition(L,L1,X,L2),
    qsort(L2,R2), qsort(L1,R1),
    append(R2,[x|R1],R).
qsort([],[]).

partition([],_B,[],[]).
partition([E|R],C,[E|Left1],Right):-
    E < C, !, partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]):-
    E >= C, partition(R,C,Left,Right1).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).

:- calls   qsort(A,B)         : list(num, A).                     % A1
:- success qsort(A,B)         => (ground(B), sorted_num_list(B)). % A2
:- calls   partition(A,B,C,D) : (ground(A), ground(B)).           % A3
:- success partition(A,B,C,D) => (list(num, C),ground(D)).        % A4
:- calls   append(A,B,C)      : (list(num,A),list(num,B)).        % A5
:- comp    partition/4        + not_fails.                        % A6
:- comp    partition/4        + is_det.                           % A7
:- comp    partition(A,B,C,D) + terminates.                       % A8

:- prop sorted_num_list/1.
sorted_num_list([]).
sorted_num_list([X]):- number(X).
sorted_num_list([X,Y|Z]):-
    number(X), number(Y), X=<Y, sorted_num_list([Y|Z]).
```
where we also use a new property, @tt{sorted_num_list}, defined in the module
itself. These assertions provide a partial specification of the program. They
can be seen as integrity constraints: if their properties do not hold at the
corresponding program points (procedure call, procedure exit, etc.), the program
is incorrect. @tt{Calls} assertions specify properties of all calls to a
predicate, while @tt{success} assertions specify properties of exit points for
all calls to a predicate. Properties of successes can be restricted to apply
only to calls satisfying certain properties upon entry by adding a @tt{:}
field to @tt{success} assertions. Finally, @tt{Comp} assertions specify
@em{global} properties of the execution of a predicate. These include complex
properties such as determinacy or termination and are in general not amenable to
run-time checking. They can also be restricted to a subset of the calls using
@tt{:}. More details on the assertion language can be found in
@cite{assert-lang-disciplbook}.

@apl{CiaoPP} can perform compile-time checking of the assertions above, by
comparing them with the assertions inferred by analysis 
(see
@cite{ciaopp-sas03-journal-scp,aadebug97-informal,assrt-theoret-framework-lopstr99} for 
details), producing as output the following assertions: 

@exfilter{bugqsort_assertions.pl}{V,output=on,simplify_checks=on,filter=check_pred} 

In order to produce this output, the @apl{CiaoPP} 
menu must be set to the same options as those used 
for checking assertions in
system libraries.
Since the @em{on} mode has been used for the option @em{Static assertion checking},
@apl{CiaoPP} has automatically detected that the
program must be analyzed not only for types and modes domains, but
also to check non-failure, determinism, and upper-bound cost.
Note that a number of initial assertions have been marked as
@tt{checked}, i.e., they have been @em{validated}. If all
assertions had been moved to this @tt{checked} status, the program
would have been @em{verified}. In these cases @apl{CiaoPP} is capable of
generating certificates which can be checked efficiently for, e.g.,
mobile code applications @cite{cocv04-ai-safety}.  However, in our case
assertion @tt{A5} has not been verified.  This indicates a
violation of the specification given, which is also flagged by @apl{CiaoPP}
as follows:

@exfilter{bugqsort_assertions.pl}{V,simplify_checks=on,filter=warnings} 

The error is now in the call @tt{append(R2,[x|R1],R)} in
@tt{qsort}
(@tt{x} instead of @tt{X}).
Assertions @tt{A1},
@tt{A3}, @tt{A4}, @tt{A6}, @tt{A7}, and @tt{A8} have been
detected to hold.
Note that though the predicate @tt{partition} may fail in general, in
the context of the current program it can be proved not to fail
(assertion @tt{A6}).
However, it was not possible to prove statically assertion also @tt{A2},
which has remained with @tt{check} status.
Note also that @tt{A2}
has been simplified, and this is because the mode analysis has
determined that on success the second argument of @tt{qsort} is
ground, and thus this does not have to be checked at run-time.  On the
other hand the analyses used in our session (types, modes,
non-failure, determinism, and upper-bound cost analysis) do not
provide enough information to prove that the output of @tt{qsort} is
a @em{sorted} list of numbers, since this is not a native property of
the analyses being used. While this property could be captured by
including a more refined domain (such as constrained types), it is
interesting to see what happens with the analyses selected for the
example.

@footnote{Note that while property @tt{sorted_num_list}
  cannot be proved with only (over approximations) of mode and regular
  type information, it may be possible to prove that it does @em{not}
  hold (an example of how properties which are not natively understood
  by the analysis can also be useful for detecting bugs at
  compile-time): while the regular type analysis cannot capture
  perfectly the property @tt{sorted_num_list}, it can still
  approximate it (by analyzing the definition) as @tt{list(num, B)}.
  If type analysis for the program were to generate a type for @tt{B}
  not compatible with @tt{list(num, B)}, then a definite error
  symptom would be detected.}

").

:- if(defined(full_tutorial)).

:- doc(module, "
@subsection{Dynamic Debugging with Run-time Checks}
Assuming that we stay with the analyses selected previously, the following step
in the development process is to compile the program obtained above with the
''generate run-time checks'' option. @apl{ciaopp} will then introduce run-time
tests in the program for those @tt{calls} and @tt{success} assertions which have
not been proved nor disproved during compile-time (see again
Figure @ref{fig:chiprewhere}). In our case, the program with run-time checks
will call the definition of @tt{sorted_num_list} at the appropriate times. In
the current implementation of @apl{ciaopp} we obtain the following code for
predicate @tt{qsort} (the code for @tt{partition} and @tt{append} remain the
same as there is no other assertion left to check):
```ciao
qsort(A,B) :-
    new_qsort(A,B),
    postc([ qsort(C,D) : true => sorted(D) ], qsort(A,B)).
```
```ciao
new_qsort([X|L],R) :-
    partition(L,X,L1,L2),
    qsort(L2,R2), qsort(L1,R1),
    append(R2,[X|R1],R).
new_qsort([],[]).
```
where @tt{postc} is the library predicate in charge of checking
postconditions of predicates.  If we now run the program with run-time
checks in order to sort, say, the list @tt{[1,2]}, the Ciao system
generates the following error message:
```ciao-inferior
?- qsort([1,2],L).
ERROR: for Goal qsort([1,2],[2,1])
Precondition: true  holds, but 
Postcondition: sorted_num_list([2,1]) does not.
```
```ciao-inferior
L = [2,1] ? 
```
Clearly, there is a problem with @tt{qsort}, since @tt{[2,1]} is not
the result of ordering @tt{[1,2]} in ascending order. This is a (now,
run-time, or @em{ concrete}) incorrectness symptom, which can be used
as the starting point of diagnosis. The result of such diagnosis
should indicate that the call to @tt{append} (where @tt{R1} and
@tt{R2} have been swapped) is the cause of the error and that the
right definition of predicate @tt{qsort} is the one in
Figure @ref{fig:qsortnomod}. 
").
:- endif.

:- doc(module, "
@subsection{Performance Debugging and Validation:}

@apl{CiaoPP} allows stating assertions about the efficiency of the program. This
is done by stating @bf{lower and/or upper bounds on the computational cost} of
predicates (given in number of execution steps). Consider for example the naive
reverse program:

```ciao
:- module(_, [nrev/2], [assertions,predefres(res_steps)]).

:- use_module(library(assertions/native_props)).

:- pred nrev(A,B) : (ground(A), list(A), var(B)).
%:- check comp nrev(A,B) + steps_ub(length(A)+1).     % (1) false
%:- check comp nrev(A,B) + steps_o(length(A)).        % (2) false
%:- check comp nrev(A,B) + steps_o(exp(length(A),2)). % (3) checked

nrev([],[]).
nrev([H|L],R) :-
    nrev(L,R1),
    append(R1,[H],R).

append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]):- append(Xs,Ys,Zs).
```

Suppose that the programmer thinks that @bf{the cost of @tt{nrev} is
given by a linear function on the size (list-length) of its first
argument}, maybe because he has not taken into account the cost of the
@tt{append} call, and adds the assertion: 

```ciao_runnable
:- module(_, [nrev/2], [assertions]).

:- use_module(library(assertions/native_props)).

:- pred nrev(A,B) : (ground(A), list(A), var(B)).
%! \\begin{focus}
:- check comp nrev(A,B) + steps_ub(length(A)+1).   

nrev([],[]).
nrev([H|L],R) :-
    nrev(L,R1),
    append(R1,[H],R).

append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]):- append(Xs,Ys,Zs).
%! \\end{focus}
```

Since @tt{append} is linear, it causes @tt{nrev} to be quadratic. @apl{CiaoPP}
can be used to inform the programmer about this false idea about the cost of
@tt{nrev}. 

As before, we set the option @tt{Action} to @tt{analyze_check}
in the menu. We get the following error message:

@exfilter{nrev.pl}{V,asr_not_stat_eval=warning,ctchecks_intervals=off,filter=errors}
 
This message states that @bf{@tt{nrev}} will take @bf{at least
@tt{0.5*(length(A))^2 + 1.5*length(A) + 1} resolution steps} (which is the
cost analysis output), while the @bf{assertion requires that it take at most
@tt{length(A)+1}} resolution steps. The cost function in the user-provided
assertion is compared with the lower-bound cost assertion inferred by analysis.
This allows detecting the inconsistency and proving that the program does not
satisfy the efficiency requirements imposed. Upper-bound cost assertions can
also be proved to hold, i.e., can be @tt{checked}, by using upper-bound cost
analysis rather than lower-bound cost analysis. In such case, it holds when the
upper-bound computed by analysis is lower or equal than the upper-bound stated
by the user in the assertion. The converse holds for lower-bound cost
assertions.

@apl{CiaoPP} can also verify or falsify cost assertions expressing @bf{worst
case computational complexity orders} (this is specially useful if the
programmer does not want or does not know which particular cost
function should be checked). For example, suppose now that the
programmer adds the following ''check'' assertion:

```ciao
:- check comp nrev(A,B) + steps_o(length(A)).
```
In this case, we get the following error message:

@exfilter{nrev2.pl}{V,asr_not_stat_eval=warning,ctchecks_intervals=off,filter=errors}

This message states that @tt{nrev} will take at least @tt{0.5*(length(A))^2 +
1.5*length(A) + 1} resolution steps (which is the cost analysis output, as in
the previous example), while the assertion requires that the worst case cost of
@tt{nrev} be linear on @tt{length(A)} (the size of the input argument).

If the programmer adds now the following ''check'' assertion:

```ciao
:- check comp nrev(A,B) + steps_o(exp(length(A),2)).
```

which states that the worst case cost of @tt{nrev} is quadratic, i.e.
is in @math{O(n^{2})}, where @math{n} is the length of the first list
(represented as @tt{length(A)}). Then the assertion is validated and
the following ''checked'' assertion is included in the output produced
by @apl{CiaoPP}:

@exfilter{nrev3.pl}{V,output=on,asr_not_stat_eval=warning,ctchecks_intervals=off,filter=check_pred}


@apl{CiaoPP} can certify programs with resource consumption assurances
@cite{tutorial-europar04}.
").

:- if(defined(full_tutorial)).
:- doc(module, "
@subsection{Abstraction-Carrying Code}

Extended options for certificate generation:
@image{Figs/debugging-acc1}

Menu options for certificate checking:
@image{Figs/debugging-acc2}

Certificate checked by @apl{ciaopp}.
@begin{alert}
TODO: This does not work
@end{alert}
@image{Figs/debugging-acc3}

@apl{ciaopp} also allows to generate program certificates based on
abstract interpretation, in order to provide the basis for
abstraction-carrying code.

Let us consider again a program for the naive reversal of a list, in
this case using functional notation, part of the @apl{ciao} system. We
have added a set of assertions which specify the intended safety
policy. The idea is that, if the assertions can be verified, then we
know that the safety policy is entailed from them and the program. The
program code is as follows:

```ciao
:- module(_, [nrev/2], [assertions,functions,regtypes,nativeprops]).
:- fun_eval(arith(false)).
:- entry nrev/2 : {list, ground} * var.

:- check pred nrev(A,B)  : list(A) => list(B).  
:- check comp nrev(_,_)  + ( not_fails, is_det ).
:- check comp nrev(A,_)  + steps_o( exp(length(A),2) ).  

nrev( [] )    := [] .
nrev( [H|L] ) := ~conc( ~nrev(L),[H] ).

:- check comp conc(_,_,_) + ( terminates, is_det ).
:- check comp conc(A,_,_) + steps_o(length(A)).

conc( [],   L ) := L.
conc( [H|L], K ) := [ H | ~conc(L,K) ]. 
```

For generating the certificate, the menu @em{check_assertions} will
be used.  Since the certificate will require specific values for some
advanced options, the expert menu must be used, selecting @tt{expert}
for the @tt{Select Menu Level} option.  The complete set of values
are shown in Figure @ref{fig:debugging-acc1}.

The results of analysis show that the above assertions have been
proved and hence the intended safety policy holds:

```ciao
:- checked comp nrev(_1,_2)
     + ( not_fails, is_det ).

:- checked comp nrev(A,_1)
     + steps_o(exp(length(A),2)).

:- checked calls nrev(A,B)
     : list(A).

:- checked success nrev(A,B)
     : list(A)
    => list(B).

:- checked comp conc(_1,_2,_3)
     + ( terminates, is_det ).

:- checked comp conc(A,_1,_2)
     + steps_o(length(A)).
```

The consumer will receive the untrusted code and the certificate
package generated with the options in Figure @ref{fig:debugging-acc1}.
It proceeds to check that the certificate is valid for the program and
that the safety policy is entailed from it. To do this, we select the
option @em{check_certificate} from the Action Group, as shown in
Figure @ref{fig:debugging-acc2}. It can be seen in
Figure @ref{fig:debugging-acc3} that with this option @apl{ciaopp}
successfully validates the certificate and assertions. Hence, the
program can be trusted by this consumer.

").

:- endif.


:- if(defined(full_tutorial)).

% TODO: review intro (some things may not work).
:- doc(module, "
@section{Source Program Optimization}
We first turn our attention to the program optimizations that are available in
@apl{ciaopp}. These include abstract specialization, multiple program
specialization, integration of abstract interpretation and partial evaluation,
and parallelization (including granularity control). All of them are performed
as source to source transformations of the program. In most of them static
analysis is instrumental, or, at least, beneficial (See Section @ref{Static
Analysis and Program Assertions} for a tutorial on program analysis with
@apl{ciaopp}).

@subsection{Abstract Specialization}

@note{How do we perform this? Is it implemented?}
  
Program specialization optimizes programs for known values
(substitutions) of the input. It is often the case that the set of
possible input values is unknown, or this set is infinite. However, a
form of specialization can still be performed in such cases by means
of abstract interpretation, specialization then being with respect to
abstract values, rather than concrete ones.  
Such abstract values represent 
a (possibly infinite) set of concrete values.
For example, consider the following definition of the property @tt{
  sorted_num_list/1}:

```ciao
:- prop sorted_num_list/1.
sorted_num_list([]).
sorted_num_list([X]):- number(X).
sorted_num_list([X,Y|Z]):- 
    number(X), number(Y), X=<Y, sorted_num_list([Y|Z]).
```
and assume that regular type analysis infers that @tt{sorted_num_list/1} will
always be called with its argument bound to a list of integers. Abstract
specialization can use this information to optimize the code into:
```ciao
sorted_num_list([]).
sorted_num_list([_]).
sorted_num_list([X,Y|Z]):- X=<Y, sorted_num_list([Y|Z]).
```
which is clearly more efficient because no @tt{number}
tests are executed. The optimization above is based on abstractly
executing the @tt{number} literals to the value @tt{true}, as
discussed in @cite{ciaopp-sas03-journal-scp}.

@subsection{Multiple Specialization}

Sometimes a procedure has different uses within a program, i.e. it is
called from different places in the program with different (abstract)
input values.  In principle, (abstract) program specialization is then
allowable only if the optimization is applicable to all uses of the
predicate. However, it is possible that in several different uses the
input values allow different and incompatible optimizations and then
none of them can take place.  In @apl{ciaopp} this problem is overcome by
means of \"multiple abstract specialization\" where different versions
of the predicate are generated for each use.  Each version is then
optimized for the particular subset of input values with which it is
to be used.  The abstract multiple specialization technique used in
@apl{ciaopp} @cite{spec-jlp} has the advantage that it can be incorporated
with little or no modification of some existing abstract interpreters,
provided they are @em{multivariant}.

This specialization can be used for example to improve automatic
parallelization) in those cases where run-time tests are included in
the resulting program (see Section @ref{Parallelization} for a
tutorial on parallelization). In such cases, a good number of run-time
tests may be eliminated and invariants extracted automatically from
loops, resulting generally in lower overheads and in several cases in
increased speedups. We consider automatic parallelization of a program
for matrix multiplication using the same analysis and parallelization
algorithms as the @tt{ qsort} example used in
Section @ref{Parallelization}.

").

:- endif.

:- if(defined(full_tutorial)).

% TODO: not sure how we perform this.
:- doc(module, "
This program is automatically parallelized without tests if we provide
the analyzer (by means of an @tt{entry} declaration) with accurate
information on the expected modes of use of the program. However, in
the interesting case in which the user does not provide such
declaration, the code generated contains a large number of run-time
tests. We include below the code for predicate @tt{multiply} which 
multiplies a matrix by a vector:
```ciao
multiply([],_,[]).
multiply([V0|Rest],V1,[Result|Others]) :-
    (ground(V1),
     indep([[V0,Rest],[V0,Others],[Rest,Result],[Result,Others]]) ->
       vmul(V0,V1,Result) & multiply(Rest,V1,Others) 
    ;  vmul(V0,V1,Result), multiply(Rest,V1,Others)).
```
Four independence tests and one groundness test have
to be executed prior to executing in parallel the calls in the body of
the recursive clause of @tt{multiply} (these tests essentially check
that the arrays do not contain pointers that point in such a way that
would make the @tt{vmul} and @tt{multiply} calls be dependent). 
However, abstract multiple
specialization generates four versions of the predicate @tt{ multiply}
which correspond to the different ways this predicate may be called
(basically, depending on whether the tests succeed or not). Of these
four variants, the most optimized one is:
```ciao
multiply3([],_,[]).
multiply3([V0|Rest],V1,[Result|Others]) :-
    (indep([[Result,Others]]) ->
       vmul(V0,V1,Result) & multiply3(Rest,V1,Others)
    ;  vmul(V0,V1,Result), multiply3(Rest,V1,Others)).
```
where the groundness test and three out of the four independence tests
have been eliminated. 
Note also that the recursive calls to @tt{multiply} use the optimized
version @tt{multiply3}. Thus, execution of matrix multiplication with
the expected mode (the only one which will succeed in Prolog) 
will be quickly directed to the optimized versions of the predicates
and iterate on them. This is because the specializer has been able to
detect this optimization as an invariant of the loop. The complete
code for this example can be found in @cite{spec-jlp}. 
The multiple specialization implemented incorporates a minimization
algorithm which keeps in the final program as few versions as possible
while not losing opportunities for optimization.  For example, eight
versions of predicate @tt{vmul} (for vector multiplication) would be
generated if no minimizations were performed. However, as multiple
versions do not allow further optimization, only one version is
present in the final program.
").

:- endif.

%%%%% TODO: [IG] currently not working
:- if(defined(full_tutorial)).
:- doc(module, "
@subsection{Basic Partial Evaluation}

The main purpose of @em{partial evaluation} (see @cite{pevalbook93}
for a general text on the area) is to specialize a given program
w.r.t. part of its input data---hence it is also known as
@em{program specialization}.  Essentially, partial evaluators are
non-standard interpreters which evaluate expressions while enough
information is available and residualize them (i.e. leave them in the
resulting program) otherwise.  The partial evaluation of logic
programs is usually known as @em{partial deduction}
@cite{Lloyd:jlp91,gallagher:pepm93}.  Informally, the partial
deduction algorithm proceeds as follows. Given an input program and a
set of atoms, the first step consists in applying an @em{unfolding
  rule} to compute finite (possibly incomplete) SLD trees for these
atoms. This step returns a set of @em{resultants} (or residual
rules), i.e., a program, associated to the root-to-leaf derivations of
these trees.  Then, an @em{abstraction operator} is applied to
properly add the atoms in the right-hand sides of resultants to the
set of atoms to be partially evaluated. The abstraction phase yields a
new set of atoms, some of which may in turn need further evaluation
and, thus, the process is iteratively repeated while new atoms are
introduced.

We show a simple example where Partial Evaluation is used to
specialize a program w.r.t. known input data. In this case, the entry
declaration states that calls to append will be performed with a list
starting by the prefix @tt{[1,2,3]} always.  The user program will
look as follows:

```ciao
:- module(app, [append/3], [assertions] ).
:- entry append([1,2,3|L],L1,Cs).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).
```

The default options for @tt{optimization} can be used to successfully
specialize the program (Figure @ref{fig:optimization-pe1} shows the
default optimization menu). 

@image{Figs/optimization-pe1}

The following resulting partially evaluated program has specialized
the third argument by propagating the first three known values. There
is an auxiliary predicate @tt{append_2} used to concatenate the remaining
elements of the first and second lists.

```ciao
:- module( _app, [append/3], [assertions] ).
:- entry append([1,2,3|L],L1,Cs).

append([1,2,3],A,[1,2,3|A]).
append([1,2,3,B|C],A,[1,2,3,B|D]) :-
    append_2(D,A,C) .

append_2(A,A,[]).
append_2([B|D],A,[B|C]) :-
    append_2(D,A,C) .
```

    ").
:- endif.

:- if(defined(full_tutorial)).
:- doc(module, "
@subsection{Nonleftmost Unfolding in Partial Evaluation of Prolog Programs}

@begin{alert}
TODO: Broken - @tt{auto_interface} error (required atom, found number)
@end{alert}

It is well-known that @em{non-leftmost} unfolding is essential in
partial evaluation in some cases for the satisfactory propagation of
static information (see, e.g., @cite{LeuschelBruynooghe:TPLP02}).  Let
us describe this feature by means of the following program, which
implements an exponentiation procedure with accumulating parameter:

```ciao
:- module(exponential_ac,[exp/3],[assertions]).
:- entry exp(Base,3,_) : int(Base).

exp(Base,Exp,Res):- 
       exp_ac(Exp,Base,1,Res). 
    
exp_ac(0,_,Res,Res). 
exp_ac(Exp,Base,Tmp,Res):- 
    Exp > 0, 
    Exp1 is Exp - 1, 
    NTmp is Tmp * Base, 
    exp_ac(Exp1,Base,NTmp,Res). 
```

The default options for partial evaluation produce the following
non-optimal residual program where only leftmost unfolding have been
used: 

```ciao
:- module( _exponential_ac, [exp/3], [assertions] ).
:- entry exp(Base,3,_1) : int(Base).

exp(A,3,B) :-
    C is 1*A,
    exp_ac_1(B,C,A).

exp_ac_1(C,B,A) :-
    D is B*A,
    exp_ac_2(C,D,A).

exp_ac_2(C,B,A) :-
    C is B*A. 
```

where the calls to the builtin \"is\" cannot be executed and hence they
have been residualized. This prevents the atoms to the right of the
calls to \"is\" from being unfolded and intermediate rules have to be
created.

In order to improve the specialization some specific options of the
system must be set.  We proceed by first selecting the @tt{expert}
mode of the optimization menu (by toggling the second option of the
menu in Figure @ref{fig:optimization-pe1}).  An overview of the
selected options is depicted in Figure @ref{fig:optimization-pe2}.
The computation rule @tt{no_sideff_jb} allows us to jump over the
residual builtins as long as nonlefmost unfolding is \"safe\"
@cite{nonleftmost-lopstr05} --in the sense that calls to builtins are
pure and hence the runtime behavior of the specialized program is
preserved.  We also select the option @tt{mono} for abstract
specialization so that a post-processing of unfolding is carried out.

@image{Figs/optimization-pe2}

The resulting specialized program is further improved:
```ciao
:- module( _exponential_ac, [exp/3], [assertions] ).

:- entry exp(Base,3,_1) : int(Base).

exp(A,3,B) :-
    C is 1*A,
    D is C*A,
    B is D*A. 
```
").

:- endif.

%%%% TODO: Not working
:- if(defined(full_tutorial)).
:- doc(module, "
@subsection{Integration of Abstract Interpretation and Partial Evaluation:}


Abstract multiple specialization, abstract interpretation, and partial
evaluation techniques are integrated into @apl{ciaopp} and their
relationship is exploited in order to achieve greater levels of
optimizations than those obtained by using these techniques alone.

Abstract specialization exploits the information obtained by
multivariant abstract interpretation where
information about values of variables is propagated by simulating
program execution and performing fixpoint computations for recursive
calls. In contrast, traditional partial evaluators (mainly) use
unfolding for both propagating values of variables and transforming
the program. It is known that abstract interpretation is a better
technique for propagating success values than unfolding.  However, the
program transformations induced by unfolding may lead to important
optimizations which are not directly achievable in the existing
frameworks for multiple specialization based on abstract
interpretation. Herein, we illustrate the @apl{ciaopp}'s specialization
framework @cite{ai-with-specs-wlpe05} which integrates the better
information propagation of abstract interpretation with the powerful
program transformations performed by partial evaluation.  We will use
the challenge program of Figure @ref{fig:peanoarithm}.

A simple Peano's arithmetic program:
@includecode{code/peano}

It is a simple @apl{ciao} program which uses Peano's arithmetic. The @tt{entry}
declaration is used to inform that all calls to the only exported predicate
(i.e., @tt{main/2}) will always be of the form @tt{main(s(s(s(N))),R)} with
@tt{N} a natural number in Peano's representation and @tt{R} a variable. The
predicate @tt{main/2} performs two calls to predicate @tt{formula/2}. A call
@tt{formula(X,W)} performs mode tests @tt{ground(X)} and @tt{var(W)} on its
input arguments and returns @math{W=(X-2)\\times 2}. Predicate @tt{two/1}
returns @tt{s(s(0))}, i.e., the natural number 2. A call @tt{minus(A,B,C)}
returns @math{C=A-B}. However, if the result becomes a negative number, @math{C}
is left as a free variable. This indicates that the result is not valid. In
turn, a call @tt{twice(A,B)} returns @math{B=A\times 2}. Prior to computing the
result, this predicate checks whether @math{A} is valid, i.e., not a variable,
and simply returns a variable otherwise.

Figure @ref{fig:optimization-aipe1} shows the extended option values
needed in the @tt{optimization} menu to produce the specialized code
shown in Figure @ref{fig:peano-code-optim-aipe1} using integrated
abstract interpretation and partial evaluation (rules are renamed
apart).

Extended menu options for integration of abstract interpretation and partial
    evaluation.
@image{Figs/optimization-aipe1}

Optimized Peano's arithmetic program with abstract
    interpretation and partial evaluation integrated:
```ciao
:- module( _example_sd, [main/2], [assertions, regtypes, nativeprops] ).

:- entry main(N,R): ( gt_two_nat(N), var(R) ).

main(s(s(s(B))),A) :-
    tw_1(B,C),
    formula_1(A,C).

tw_1(0,0).
tw_1(s(A),s(s(B))) :-
    tw_1(A,B).

formula_1(0,0).
formula_1(s(s(B)),s(A)) :-
    tw_1(A,B).
```

We can see that calls to predicates @tt{ground/1} and
@tt{var/1} in predicate @tt{formula/2} have been removed.  For
this, we need to select the @tt{shfr} abstract domain in the menu.  The
abstract information obtained from (groundness and freeness) analysis
states that such calls will definitely succeed for initial queries
satisfying the @tt{entry} declaration (and thus, can be replaced
by @em{true}). Also, the code for predicates @tt{twice/2} and
@tt{tw/2} has been merged into one predicate: @tt{tw_1/2}.
This is also because the inferred abstract information states that the
call to @tt{ground/1} in predicate @tt{twice/2} will
definitely succeed (and thus can be removed).  Also, the call to
predicate @tt{var/1} in the first clause of predicate
@tt{twice/2} will always fail (and thus, this clause can be
removed).
These optimizations can be selected in @apl{ciaopp} by choosing the option
value @tt{spec} for @tt{Select Optimize} and the option value
@tt{all} for @tt{Abstract Spec Definitions} in the menu (See
Figure @ref{fig:optimization-aipe1}). These points illustrate
hence the benefits of @em{exploiting abstract information in order
  to abstractly execute certain atoms which may, in turn, allow
  unfolding of other atoms}.

However, the use of an abstract domain which captures groundness and
freeness information will in general not be sufficient to determine
that, in the second execution of @tt{formula/2} in predicate
@tt{main/2}, the tests @tt{ground(X)} and @tt{var(W)} will
also succeed. The reason is that, on success of
@tt{minus(T,X,X2)}, @var{X2} cannot be guaranteed to be ground
since @tt{minus/3} succeeds with a free variable in its third
argument position. It can be observed, however, that for all calls to
@tt{minus/3} in the executions described by the @tt{entry}
declaration, the third clause for @tt{minus/3} is useless. It will
never contribute to a success of @tt{minus/3} since such predicate
is always called with a value greater than zero in its first
argument. Unfolding can make this explicit by fully unfolding calls to
@tt{minus/3} since they are sufficiently instantiated, and as a
result, the \"dangerous\" third clause is disregarded.  This unfolding
allows concluding that in our particular context all calls to
@tt{minus/3} succeed with a ground third argument. This can be
selected in @apl{ciaopp} by choosing the values for @tt{local} and
@tt{global} control within the optimization menu shown in
Figure @ref{fig:optimization-aipe1}. This illustrates the
importance of @em{performing unfolding steps in order to prune away
  useless branches, and that this will result in improved success
  information}.
").


:- doc(module, "
@subsection{Parallelization}
@begin{cartouche}
It works
@end{cartouche}
An example of a non-trivial program optimization performed using
abstract interpretation in @apl{ciaopp}is program
parallelization @cite{effofai-toplas}. It is also performed as a
source-to-source transformation, in which the input program is @em{
  annotated} with parallel expressions.  The parallelization
algorithms, or annotators @cite{annotators-jlp}, exploit parallelism
under certain @em{independence} conditions, which allow guaranteeing
interesting correctness and no-slowdown properties for the
parallelized programs @cite{sinsi-jlp,consind-toplas}. This process
is complicated by the presence of shared variables and pointers among
data structures at run-time.

Consider the following program :

@includecode{code/qsort_par}

A possible parallelization is: 

```ciao
qsort([X|L],R) :-
    partition(L,X,L1,L2),
    ( indep([[L1,L2]]) -> qsort(L2,R2) & qsort(L1,R1)
                        ; qsort(L2,R2), qsort(L1,R1) ),
    append(R1,[X|R2],R).
```
which indicates that, provided that @tt{L1} and @tt{L2} do not have
variables in common (at execution time), then the recursive calls to
@tt{qsort} can be run in parallel.

@image{Figs/optimization-parallelization2}

Given the information inferred by the abstract interpreter using,
e.g., the mode and independence analysis (see
Section @ref{Static Analysis and Program Assertions}), which determines that @tt{L1} and
@tt{L2} are ground after @tt{partition} (and therefore do not share
variables), the independence test and the conditional can be
simplified via abstract executability and the annotator yields
instead:
```ciao
qsort([X|L],R) :-
    partition(L,X,L1,L2),
    qsort(L2,R2) & qsort(L1,R1),
    append(R1,[X|R2],R).
```
which is much more efficient since it has no run-time test. This test
simplification process is described in detail in @cite{effofai-toplas}
where the impact of abstract interpretation in the effectiveness of
the resulting parallel expressions is also studied.  The selected menu
options needed to produce this output are depicted in
Figure @ref{fig:optimization-parallelization}.

Menu options for parallelization with analysis information:
@image{Figs/optimization-parallelization}

The tests in the above example aim at @em{strict} independent
and-parallelism. However, the annotators are parameterized on the
notion of independence. Different tests can be used for different
independence notions: non-strict independence @cite{nsicond-sas94}, 
constraint-based independence @cite{consind-toplas}, etc.

Moreover, all forms of and-parallelism in logic programs can be seen as
independent and-parallelism, provided the definition of independence is applied
at the appropriate granularity level.
@footnote{For example, stream
and-parallelism can be seen as independent and-parallelism if the independence
of ''bindings'' rather than goals is considered.}

    ").
:- endif.

:- if(defined(full_tutorial)).
:- doc(module, "
@subsection{Resource and Granularity Control:}

@begin{alert}
TODO: This seems to hangs
@end{alert}

Another application of the information produced by the @apl{ciaopp} analyzers,
in this case cost analysis, is to perform combined compile--time/run--time
resource control. An example of this is task granularity
control @cite{granularity-jsc-short} of parallelized code. Such parallel code
can be the output of the process mentioned above or code parallelized manually.

In general, this run-time granularity control process involves computing sizes
of terms involved in granularity control, evaluating cost functions, and
comparing the result with a threshold @footnote{This threshold can be determined
experimentally for each parallel system, by taking the average value resulting
from several runs.} to decide for parallel or sequential execution.
Optimizations to this general process include cost function simplification and
improved term size computation, both of which are illustrated in the following
example.

Consider again the qsort program in Figure @ref{fig:qsortnomod}. We use
@apl{ciaopp} to perform a transformation for granularity control. An overview
of the selected menu options to achieve this is depicted in Figure
@ref{fig:optimization-granularity}.

@image{Figs/optimization-granularity}

In the resulting optimized code, @apl{ciaopp} adds a clause:
@tt{qsort(_1,_2) :- g_qsort(_1,_2).}
(to preserve the original entry point) and produces 
@tt{g_qsort/2}, the version of @tt{qsort/2} that performs
granularity control (@tt{s_qsort/2} is the sequential version):
```ciao
g_qsort([X|L],R) :-
    partition_o3_4(L,X,L1,L2,_1,_2),
    ( _2>7 -> (_1>7 -> g_qsort(L2,R2) & g_qsort(L1,R1)
                     ; g_qsort(L2,R2), s_qsort(L1,R1))
            ; (_1>7 -> s_qsort(L2,R2), g_qsort(L1,R1)
                     ; s_qsort(L2,R2), s_qsort(L1,R1))),
    append(R1,[X|R2],R).
g_qsort([],[]).
```

Note that if the lengths of the two input lists to the qsort program
are greater than a threshold (a list length of 7 in this case) then
versions which continue performing granularity control are executed in
parallel. Otherwise, the two recursive calls are executed
sequentially. The executed version of each of such calls depends on
its grain size: if the length of its input list is not greater than
the threshold then a sequential version which does not perform
granularity control is executed. This is based on the detection of a
recursive invariant: in subsequent recursions this goal will not
produce tasks with input sizes greater than the threshold, and thus,
for all of them, execution should be performed sequentially and,
obviously, no granularity control is needed.
  
In general, the evaluation of the condition to decide which predicate
versions are executed will require the computation of cost functions
and a comparison with a cost threshold (measured in units of
computation). However, in this example a test simplification has been
performed, so that the input size is simply compared against a size
threshold, and thus the cost function for qsort does not need to be
evaluated.@footnote{This size threshold will obviously be different if
  the cost function is.}
Predicate @tt{partition_o3_4/6}:
```ciao
partition_o3_4([],_B,[],[],0,0).
partition_o3_4([E|R],C,[E|Left1],Right,_1,_2) :-
    E<C, partition_o3_4(R,C,Left1,Right,_3,_2), _1 is _3+1.
partition_o3_4([E|R],C,Left,[E|Right1],_1,_2) :-
    E>=C, partition_o3_4(R,C,Left,Right1,_1,_3), _2 is _3+1.
```

is the transformed version of @tt{ partition/4}, which \"on the fly\"
computes the sizes of its third and fourth arguments (the
automatically generated variables @tt{_1} and @tt{_2} represent
these sizes respectively) @cite{termsize-iclp95}.
").

:- endif.
