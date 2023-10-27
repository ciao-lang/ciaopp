:- module(_, [], [assertions]).

:- doc(filetype, documentation).

:- doc(title, "Examples of types, modes, and resources in CiaoPP").

:- doc(author, "The Ciao Development Team").

:- doc(module, "
The @em{Ciao assertions model} involves the combination of a rich 
assertion language, allowing a very general class of (possibly
undecidable) properties,  and a novel methodology for dealing with such
assertions. This methodology is based on making a best effort to infer and check assertions 
statically, using rigorous static analysis tools based on
@em{safe approximations}, in particular via abstract interpretation.
This implies accepting that complete verification or error detection 
may not always be possible and run-time checks may be needed.
This approach allows dealing in a uniform way with a wide variety of properties
which includes types, but also, e.g., rich modes, determinacy,
non-failure, sharing/aliasing, term linearity, cost
etc., while at the same time allowing assertions to be @em{optional}.

The @apl{Ciao} model and language design also allows for a smooth
integration with testing. Moreover, as (parts of) tests that can be verified at
compile time are eliminated, some tests can be passed without ever running them.
Finally, the model supports naturally assertion-based test case generation.


In the following we illustrate these aspects of the @apl{Ciao} assertions
model through examples run on the system.
While there are several ways to use the system, 
the idea is to have installed @apl{Ciao} on your computer, including the development
environment (see @ref{Installation} for more information). This
includes @apl{CiaoPP}. You can then access
@apl{CiaoPP} from the Emacs interface or the command line. 
The examples can be also followed by running @apl{CiaoPP} directly on your browser
through the @apl{Ciao} playground. To this end, load the examples into the playground
by pressing the @key{↗} button (''Load in playground''), and
then @apl{CiaoPP} can be run clicking the @key{More...} button
and selecting @key{Analyze and check assertions}. Or, you can also
interact with the code boxes (you will identify them by a question mark (?)
in the right top corner), and by clicking the question mark you would be
able to run @apl{CiaoPP} and see fragments of the analysis output.

@bf{A first example.}
Consider the classic implementation of quick-sort:

```ciao_runnable
%! \\begin{code}
:- module(_,[qsort/2],[assertions,nativeprops,modes]).

% With no information on the calls to qsort/2, 
% the analyzer warns that it cannot ensure that 
% the calls to =</2 and >/2 will not generate a 
% run-time error.

qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
%! \\end{code}
%! \\begin{opts}
V,assertion=[assertion],filter=warn_error
%! \\end{opts}
```
    
If no other information is provided, the exported predicate
@tt{qsort/2} can be called with arbitrarily instantiated terms as
arguments (e.g., with a list of variables). This implies that the 
library predicates @tt{=</2} and @tt{>/2} in @tt{partition/4} can also
be called with arbitrary terms and thus run-time errors are possible,
since @tt{=</2} and  @tt{>/2} require their arguments to be bound to arithmetic
expressions when called. Even though there are no assertions in the program
itself, the system is able to warn that it cannot verify that the
calls to @tt{=</2} and @tt{>/2} will not generate a run-time
error (by clicking the question mark (?)
in the right top corner, you can run @apl{CiaoPP} and see the messages).
This is the result of a modular global analysis and a
comparison of the information inferred for the program points before
the calls to @tt{=</2} and @tt{>/2} with the assertions that
express the calling restrictions for @tt{=</2} and
@tt{>/2}. Such assertions live in the libraries that provide
these standard predicates.  Further details can be obtained
by reading the messages.

We can add an assertion for the exported predicate @tt{qsort/2}
expressing that it should be called with its first argument bound to a list of numbers:

```ciao_runnable
%! \\begin{code}
:- module(_,[qsort/2],[assertions,nativeprops,modes]).

% Adding information on how the exported predicate should 
% be called the system can infer that =</2 and >/2 will be 
% called correctly, and no warnings are flagged.

:- pred qsort(+list(num),_).

qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
%! \\end{code}
%! \\begin{opts}
V,assertion=[assertion],filter=all_message
%! \\end{opts}
```

Assuming this ''entry'' information, the @apl{Ciao} system can verify that all
the calls to @tt{=</2} and @tt{>/2} are now correct (with
their arguments bound to numbers in this case), and thus no warnings
are displayed.
Note that in practice this assertion may not be necessary since this information
could be obtained from the analysis of the caller(s) to this module.
 
Let us now add more assertions to the program, stating properties that
we want checked: 
```ciao_runnable
:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes]).

% qsort/2 with some assertions.
% The system verifes the assertions and also that 
% the =</2 and >/2 are called correctly and will not 
% generate any run-time errors.  
% Try also generating the documentation for this file!

% If qsort/2 is called with a list of numbers, it will
% return a list of numbers and at most one solution.
:- pred qsort(+list(num),-list(num)) + semidet.
 
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

% partition/4 is called with a list of numbers and a
% number it returns two lists of numbers, one solution,
% and will never fail. 
:- pred partition(+list(num),+num,-list(num),-list(num)) + det.

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

% append/3 is called with two lists of numbers, will
% return a list of numbers, and at most one solution.
:- pred append(+list(num),+list(num),-list(num)) + semidet.

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
```
For example, the assertion for predicate @tt{partition/4} (line 23):
```ciao
:- pred partition(+list(num),+num,-list(num),-list(num)) + det.
```
expresses, using @lib{modes}, that the first  argument should be bound to a list of numbers,
and the second to a number, and that, for any terminating call meeting this call pattern:
a) if the call succeeds, then the third and fourth arguments will be bound
to lists of numbers; and
b) the call is deterministic, i.e., it will produce one solution exactly, property @tt{det}
in the @tt{+} field, which is inferred in @apl{CiaoPP} as the
conjunction of two properties: 1) the call does not (finitely) fail
(property @tt{not_fails}) and 2) the call will produce one solution at most (property
@tt{is\_det}). Similarly, the assertion for @tt{qsort/2}:
```ciao
:- pred qsort(+list(num),-list(num)) + semidet.
```
expresses the expected calling pattern, and that the call can have at most one answer,
property @tt{semidet}.


In the Ciao assertion model, modes are @em{macros} that serve as a
shorthand for assertions, in particular @em{predicate-level
assertions}. These are in general of the form:

@code{:- [Status] pred Head : Pre => Post + Comp.}

where @var{Head} denotes the predicate that the assertion applies to, and @var{Pre} and
@var{Post} are conjunctions of @em{state property} literals.
@var{Pre} expresses properties that hold when  @var{Head} is called. @var{Post} 
states properties that hold if @var{Head} is called in a state compatible
with @var{Pre} and the call succeeds.
@var{Comp} describes properties of the whole computation such as
determinism, non-failure, resource usage, termination, etc.,
also for calls that meet @var{Pre}. In particular, the modes for @tt{qsort/2} in
the last example are expanded by the @tt{modes} package 
(see module declaration in the above examples) to:
```ciao
:- pred qsort(X,Y) : list(num,X) => list(num,Y) + semidet.
```

All the assertions in the last example indeed get verified by @apl{CiaoPP}, which is shown in
the output:

@exfilter{qsort_assrt_det.pl}{V,ana_det=nfdet,output=on,filter=check_pred}  

In the next example, the assertions are written as machine readable comments enabled by the @tt{doccomments}
package. Such comments can contain embedded assertions, which are
also verified.  Here we use again modes and determinacy. This format is familiar to
Prolog programmers and compatible with any Prolog system without
having to define any operators for the assertion syntax. If we run the example,
we can see that, as before, the assertions get verified by @apl{CiaoPP}:

```ciao_runnable
%! \\begin{code}
:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes,doccomments]).

% Describing predicates with modes/assertions in doccommmments syntax
% (which also get veryfied by the sustem). Try also generating the 
% documentation for this file!

%! qsort(+list(num),-list(num)): 
%  Y is X sorted.
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

%! partition(+list(num),+num,-list(num),-list(num)): 
%  Partitions a list into two lists, greater and
%  smaller than second argument. 
partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

%! append(+list(num),+list(num),-list(num)): 
append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
%! \\end{code}
%! \\begin{opts}
V,ana_det=nfdet,output=on,filter=check_pred
%! \\end{opts}
```

Imagine that we replace @tt{=</2} with
@tt{</2} in the second clause of @tt{partition/4},

```ciao_runnable
%! \\begin{code}
:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes]).

% qsort/2 with some assertions.
% If we have </2 and >/2 in partition the system warns 
% that partition/4 is not guaranteed to not fail.

:- pred qsort(+list(num),-list(num)) + semidet.
 
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

:- pred partition(+list(num),+num,-list(num),-list(num)) + det.

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X < F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

:- pred append(+list(num),+list(num),-list(num)) + semidet.

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
%! \\end{code}
%! \\begin{opts}
V,ana_det=nfdet,filter=warn_error
%! \\end{opts}
```

@apl{CiaoPP} warns that this predicate may fail.
This is because the case where @tt{X=F} is not ''covered'' by the
''tests'' of @tt{partition/4}.
Conversely, if we replace @tt{>/2} with @tt{>=/2} in the
second clause of the original definition of @tt{partition/4},

```ciao_runnable
%! \\begin{code}
:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes]).

% qsort/2 with some assertions.
% If we have =</2 and >=/2 in partition the system warns 
% that both partition/4 and qsort/2 may not be deterministic.

:- pred qsort(+list(num),-list(num)) + semidet.
 
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

:- pred partition(+list(num),+num,-list(num),-list(num)) + det.

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X >= F,
    partition(Y,F,Y1,Y2).

:- pred append(+list(num),+list(num),-list(num)) + semidet.

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
%! \\end{code}
%! \\begin{opts}
V,ana_det=nfdet,filter=warn_error
%! \\end{opts}
```
the system warns that the predicate may not be deterministic.
This is because the analyzer infers that not all the clauses of
@tt{partition/4} are pairwise mutually exclusive (in particular
the second and third clauses are not), and thus, multiple solutions
may be obtained.

@bf{Defining properties.}
The reader may be wondering at this point where the properties that
are used in assertions (such as @tt{list(num)}) come from. As
mentioned before, such properties are typically written in Prolog and
its extensions; and they can also be built-in and/or defined and 
imported from system libraries or in user code. Visibility is
controlled by the module system as for any other predicate. 

```ciao_runnable
%! \\begin{focus}
:- module(_,[color/1,colorlist/1,sorted/1],[assertions,regtypes,clpq]).

% Defining some types and properties which can then be used 
% in assertions.

:- regtype color/1.
color(red).
color(green).
color(blue).

:- regtype colorlist/1.
colorlist([]).
colorlist([H|T]) :- color(H), colorlist(T).

:- prop sorted/1.
sorted([]).
sorted([_]).
sorted([X,Y|T]) :- X .>=. Y, sorted([Y|T]).
%! \\end{focus}
``` 
    
The above example shows some examples of definitions of properties. 
Two of them are marked as @em{regular types} 
(@tt{regtype} directive): @tt{color/1}, defined as
the set of values @{@tt{red}, @tt{green}, @tt{blue}@}, and
@tt{colorlist/1}, representing the infinite set of
lists whose elements are of @tt{color} type. The third property is
not a regular type, but an arbitrary property 
(@tt{prop} directive), representing the infinite set of lists
of numeric elements in descending order.
Marking predicates as properties allows them to be used in assertions,
but they remain regular predicates, and can be called as any other,
and also used as run-time tests, to generate examples (test cases),
etc. For example: 
```ciao_runnable
?- colorlist(X).
```
or, we can select breadth-first execution (useful here for fair generation) by adding
the package @tt{srt/fall}.
```ciao
:- module(_,[color/1,colorlist/1,sorted/1],[assertions,regtypes,clpq,sr/bfall]).
``` 

The next example shows the same properties as the last example but written
using functional notation. The definitions are equivalent, functional syntax being
just syntactic sugar.
```ciao
:- module(_,[colorlist/1,sorted/1,color/1],[assertions,regtypes,fsyntax]).

% Defining some types and properties (using functiomal syntax)
% which can then be used in assertions. 

:- regtype color/1.
color := red | green | blue.

:- regtype colorlist/1.
colorlist := [] | [~color|~colorlist].

:- prop sorted/1.
sorted := [] | [_].
sorted([X,Y|T]) :- X .>=. Y, sorted([Y|T]).
```


In the following example we add some simple definitions for @tt{p/1} and @tt{q/1}:
```ciao_runnable
%! \\begin{code}
:- module(_,[p/1,colorlist/1,sorted/1,color/1],[assertions,regtypes,fsyntax]).

% Defining some types and properties (using functiomal syntax)
% which are then used in two simple assertions. The system
% detects that property sorted is incompatible with the success
% tyoe of p/1.

:- pred p(X) => sorted(X).
p(X) :- q(X).

:- pred q(X) => color(X).
q(M) :- M = red.

:- regtype color/1.
color := red | green | blue.

:- regtype colorlist/1.
colorlist := [] | [~color|~colorlist].

:- prop sorted/1.
sorted := [] | [_].
sorted([X,Y|T]) :- X >= Y, sorted([Y|T]).
%! \\end{code}
%! \\begin{opts}
V,output=on,filter=check_pred
%! \\end{opts}
``` 
    
and a @tt{pred} assertion for @tt{q/1}, meaning ''in all calls @tt{q(X)} that succeed,
@tt{X} is @em{instantiated} on success to a term of @tt{color} type''.
This is verified by @apl{CiaoPP}. We have also added an assertion for @tt{p/1}
meaning ''in all calls @tt{p(X)} that succeed, @tt{X} gets instantiated to a
term meeting the @tt{sorted} property.'' 
@apl{CiaoPP} detects that such assertion is false and shows the reason
the analyzer (with the @tt{eterms} abstract domain @tt{eterms}) infers that
on success @tt{X} gets bound to @tt{red}, expressed as the automatically inferred regular
type @tt{rt27/1}, and @apl{CiaoPP} finds that @tt{rt27(X)} and
@tt{sorted(X)} are incompatible (empty intersection of the set of
terms they represent):

@exfilter{incompatible_type_f_error.pl}{V,filter=warn_error}

In the program,
```ciao
:- module(_,[p/1,colorlist/1,sorted/1,color/1],[assertions,regtypes,fsyntax]).

% Defining some types and properties (using functiomal syntax)
% which are then used in two simple assertions. With default domain
% sorted/1 is not proved and will generate a run-time check and 
% optionally initiate assertion-based test generation.

:- pred p(X) => sorted(X).
p(X) :- q(X).

:- pred q(X) => list(X).
q(M) :- M = [_,_,_].

:- regtype color/1.
color := red | green | blue.

:- regtype colorlist/1.
colorlist := [] | [~color|~colorlist].

:- prop sorted/1.
sorted := [] | [_].
sorted([X,Y|T]) :- X >= Y, sorted([Y|T]).
```
we have changed the definition of incompatibility, and now @apl{CiaoPP} simply warns
that it cannot verify the assertion for @tt{p/1}:

@exfilter{incompatible_type_f_fixed.pl}{V,filter=warn_error}

The success type @tt{rt27(X)} inferred for @tt{p/1} (lists of three 
arbitrary terms) and @tt{sorted(X)} are now compatible, and thus no error is flagged.
However, @tt{rt27(X)} does not imply @tt{sorted(X)} for all @tt{X}'s, and thus
@tt{sorted(X)} is not verified (with the default set of abstract domains). 
In this case, the system will (optionally)
introduce a run-time check so that @tt{sorted(X)} is tested when
@tt{p/1} is called. Furthermore, the system can run unit tests or
generate test cases (in this case arbitrary terms) automatically to
exercise such run-time tests.

@bf{An example with more complex properties.}
To follow this part of the tutorial we recommend to have installed @apl{CiaoPP} as many of the advanced
features are not yet included in the playground. An example with more complex properties (also
using the functional syntax package) is shown here:

```ciao
:- module(_, [nrev/2], [assertions,fsyntax,nativeprops]).

% Naive reverse with some complex assertions.
% The system flags a (cost) error reminding us that 
% nrev/2 is quadratic, not linear. 
% (Requires cost-related domains.)

:- pred nrev(A,B) : (list(num,A), var(B)) => list(B) 
   + ( det, terminates, steps_o( length(A) ) ).

nrev( [] )    := [].
nrev( [H|L] ) := ~conc( ~nrev(L),[H] ). 


:- pred conc(A,B,C) + ( det, terminates, steps_o(length(A))).

conc( [],    L ) := L. 
conc( [H|L], K ) := [ H | ~conc(L,K) ].
``` 
It includes a user-provided assertion stating (among other properties) that
the cost of @tt{nrev/2} in resolution steps, for calls to @tt{nrev(A, B)} with @tt{A}
a ground list and @tt{B} a free variable,  should be linear 
in the length of the (input) argument @tt{A}
($O($@tt{length(A)}$)$, property @tt{steps_o(length(A))} in the 
@tt{+} field. @apl{CiaoPP} can infer that this is false:
 
@exfilter{revf_n_o_det_error.pl}{V,output=on,filter=check_pred}

If we continue to examine the output of @apl{CiaoPP} we can see this other assertion:

@exfilter{revf_n_o_det_error.pl}{V,output=on,name=nrev,assertion=[steps_lb],filter=tpred_plus}

The assertion explains that the stated worst case asymptotic
complexity is incompatible with the quadratic lower bound cost 
inferred by the analyzer (in fact: @math{\\frac{1}{2} \ length{(A)}^2 + \\frac{3}{2} \ length(A) + 1},
see the @tt{steps_lb} property). If we change the assertion to specify a quadratic upper bound:
```ciao
:- pred nrev(A,B) : (list(num,A), var(B)) => list(B) 
   + ( det, terminates, steps_o( exp(length(A), 2) ) ).
```
it is now proven:

@exfilter{revf_n_o_det_verified.pl}{V,output=on,filter=check_pred}

Now we have changed the assertion for @tt{conc/3} from complexity order (@tt{_o})
to a concrete upper bound (@tt{_ub}), and the system detects the error:

@exfilter{revf_n_ub_det_error.pl}{V,output=on,filter=check_pred}

@tt{length(A)} is not a correct upper bound because, as shown in the message,
it is incompatible with the lower bound @tt{length(A) + 1} inferred by the analyzer:

@exfilter{revf_n_ub_det_error.pl}{V,output=on,name=conc,assertion=[steps_lb],filter=tpred_plus}

If we change the upper bound to @tt{length(A) + 1}, then the assertion is verified. 

@exfilter{revf_n_ub_det_verified.pl}{V,output=on,filter=check_pred}

").
