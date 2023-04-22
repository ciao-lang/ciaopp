:- use_package([assertions]).

:- doc(filetype, documentation).

:- doc(title, "A Gentle Introduction to Static Verification and Bug Finding with CiaoPP").

:- doc(author, "Daniela Ferreiro").
:- doc(author, "Jose F. Morales (minor)").

:- doc(module," 
This is a tutorial to illustrate step-by-step the development of a
program for a given specification, using the @apl{Ciao} language of
assertions, which allows the user to describe predicates and
properties. Our aim is to show how to use @apl{CiaoPP} to prove
@em{statically} whether these assertions hold and/or detect bugs. The
tutorial also provides an introduction to the dynamic checking aspects
of @apl{CiaoPP}. Although the solution of the different exercises is
provided in this tutorial, try to think first about the answer on your
own, and experiment!

Consider the following specification (taken from the Prolog
programming contest at ICLP'95, Portland, USA):

@begin{cartouche}
@bf{Specification. }@em{Write a predicate @pred{powers/3}, which is
called with a list of non-negative numbers as first argument, a
non-negative number @var{N} as second argument, and a free third
argument. Such a call must succeed exactly once and unify the third
argument with the list that contains the smallest @var{N} integers (in
ascending order) that are a non-negative power of one of the elements
of the first argument.}
@end{cartouche}

In the next section we will show a complete fully working @ref{Initial
implementation}. If you wish, you can skip directly to this solution
and run some queries before start specifying properties @ref{Using
assertions}.

@include{interactive_usage.lpdoc}

@section{Defining modules and exports}
@cindex{module, exports}
We will start with the module declaration:
```ciao
:- module(powers,[powers/3],[assertions])
```
This module declaration states that the name of the module is
@tt{powers}, that it exports a predicate @pred{powers/3}, and that it
uses the @lib{assertions} package. Note that the module @lib{powers}
will define other predicates, such as @pred{remove_power/3} (the
program can be found below). These other predicates are internal to
the module, i.e., they cannot be seen or used in other modules. One of
the reasons why we export only the predicate @pred{powers/3} is that
during the analysis of this program, @apl{CiaoPP} can assume that
external calls are only to this predicate. This fact will allow
@apl{CiaoPP} to produce more accurate information about the program
since analysis then does not have to consider all the possible ways
other predicates inside the module may be called, and only those that
can actually occur in the module.

@section{Writing powers/3} 

Once we have defined the module we start writing the predicate
@pred{powers/3}. We can sketch the main idea of our approach with a
motivating example. Consider the following query:

```ciao
?- powers([2,3,5],7,Powers).
```

We start by constructing the list of pairs \\[(2,2),(3,3),(5,5)\\],
which is sorted and which has no two pairs with the same first
component. The implementation of this predicate can be as follows:

```ciao_runnable
:- module(_, _, [assertions]).
%! \\begin{focus}
create_pairs([],[]).
create_pairs([X|R],[(X,X)|S]) :- create_pairs(R,S).
%! \\end{focus}
``` 

In each pair @tt{(P,F)}, @var{P} is the smallest power of @var{F} that
is not in the solution list yet.  So, the first component of the first
element of the pair-list is the next element in the output we are
constructing.  We remove this pair, compute the next power of @var{F}
(i.e., @var{P}\\*@var{F}) and insert the pair @tt{(P*F,F)} into the
pair-list, respecting the invariants.  We start by writing
@pred{remove_power/3}, which takes a number as first argument, and a
list of pairs as second argument, and returns as its third argument
another pair-list consisting of the second argument minus the pair
@tt{(P,F)} with @var{P} the first argument.

```ciao_runnable
:- module(_, _, [assertions]).
%! \\begin{focus}
remove_power(_,[],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= Power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).
%! \\end{focus}
```

We also define @pred{sorted_insert/3}:

```ciao_runnable
:- module(_, _, [assertions]).
%! \\begin{focus}
sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]) :- X =< X1, !.
sorted_insert([P|L1], X, [P|L]) :- sorted_insert(L1, X, L).
%! \\end{focus}
```

This predicate compares the value of the item to be inserted (the
second argument) with the head of the list. If it is less than this
value, then the new pair must be inserted just before this head,
otherwise the pair is inserted into the new tail. 

@subsection{Initial implementation}
Using the information we have seen so far we would have the following
implementation (there is a brief explanation of each predicate):

```ciao_runnable
:- module(_,[powers/3],[assertions]).

%! \\begin{focus}
% powers(X,N,P): P is the sorted list that contains the smallest N integers
% that are a non-negative power of one of the elements of the list X.

powers([],_,[]).
powers(Factors,N,Powers) :-
    quicksort(Factors, SFactors),
    create_pairs(SFactors,Pairs),
    first_powers(N,Pairs,Powers).

% quicksort(Xs,Ys): Performs a quicksort of a list Xs and returns the result
% in Ys.

quicksort(Xs,Ys) :- qsort(Xs,Ys,[]).

qsort([],DL,DL).

qsort([X|Xs],Head,Tail) :-
    partition(Xs,X,L,R),
    qsort(L,Head,[X|QR]),
    qsort(R,QR,Tail).

partition([],_,[],[]).
partition([X|Xs],Pv,[X|L],R) :- X =< Pv, !, partition(Xs,Pv,L,R). 
partition([X|Xs],Pv,L,[X|R]) :- X > Pv, partition(Xs,Pv,L,R).


% create_pairs(F,P): F is a list and P is sorted list of pairs. Each  
% element of P has the form (X,X), where X is a element of F.

create_pairs([],[]).
create_pairs([X|R],[(X,X)|S]) :- create_pairs(R,S).


% first_powers(N,L,R): R is a sorted list with N non-negative numbers.

first_powers(N,[(Power,Factor)|PFs],[Power|Powers]) :-
    N > 0, !,
    N1 is N-1,
    remove_power(Power,PFs,PFs1),
    Power1 is Power*Factor,
    sorted_insert(PFs1,(Power1,Factor),PFs2),
    first_powers(N1,PFs2,Powers).
first_powers(0,_,[]).


% remove_powers(P,L,R): R is the sorted list of pairs obtained by removing
% from the list L.

remove_power(_,[],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= Power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).


% sorted_insert(L,P,R): R is the sorted list of pairs obtained by adding
% to the list L the pair P.

sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]) :- X =< X1, !.
sorted_insert([P|L1], X, [P|L]) :- sorted_insert(L1, X, L).
%! \\end{focus}
```

Below are some examples queries to the @pred{powers/3} predicate (make
sure that the code box above is marked with a @em{green check mark}):
  
```ciao_runnable
?- powers([3,5,4],17,Powers).
```
```ciao_runnable
?- powers([2,9999999,9999998],20,Powers).
```
```ciao_runnable
?- powers([2,4],6,Powers).
```

@begin{cartouche}
@bf{Exercise 1 (Understanding the predicate). }@em{What is the answer of this query?}
```ciao_runnable
?- powers([4,2],6,Powers). 
```
@em{@bf{Hint:} Remember that Powers contains the smallest N integers (in ascending order)}
@end{cartouche}

@subsection{Analysis of our the initial implementation}

Let us analyze this implementation of the @pred{powers/3}
predicate. The @apl{Ciao} system includes a large number of domains
that can be used in this program and has strategies for selecting
between them. But, by default, @apl{CiaoPP} analyzes programs with a
types domain (the regular types domain @tt{eterms}) and a modes domain
(the sharing/freeness domain @tt{shfr}). We will be working mainly
with these two. The following are the results (it is not necessary to
look too carefully at these results yet):
 
@exfilter{power_without_assertions.pl}{V,filter=warnings}  

These warnings are stating that there are a number of assertions that
cannot be shown to hold. In particular, the analysis is saying that it
is not possible to ensure that the calls that the program makes to
predicates such as @pred{>=/2}, @pred{</2}, @pred{>/2}, @pred{is/2},
and @pred{=</2} respect the corresponding preconditions or @em{calling
modes}, which generally require the arguments to be bound to
arithmetic expressions when called. The interesting thing to note here
is that we did not have to include any assertions in our code. The
warning messages stem from the assertions (specifications) that
provide the pre-conditions and post-conditions for such library
predicates in the @apl{Ciao} system libraries. Thus, a first
observation is that it is possible to identify potential bugs even
without actually adding assertions to programs. However, in general,
if the program is incorrect, the more assertions are present in the
program, the more likely errors will be detected automatically. Thus,
we may choose to dedicate more time to writing assertions for those
parts of the program that seem to be possibly buggy or whose
correctness is important.

In particular, in view of the warnings above, it seems useful to be
able to ensure that all these library predicates will always be called
properly within our module and thus be more confident about our
program. We can work towards this objective by providing some
information regarding how the exported predicate, @pred{powers/3},
will be called from outside the module.

@section{Using assertions}

For example, from the problem specification we know that the second
argument should always be a number. In order to be able to state such
properties of predicates we will have to use the assertion language,
in particular (as we have just seen), @tt{pred} assertions which are
used to describe a particular predicate. Such assertions use the
following syntax: @cindex{assertions}

```ciao
:- pred Pred [:Precond] [=> Postcond] [+ CompProp] .
```
Such an assertion indicates that in any call to @var{Pred}, if
@var{Precond} holds in the calling state and the computation of the
call succeeds, then @var{Postcond} also holds in the success state. As
we will see later, @var{Precond} and @var{Postcond} are conjunctions
of @em{state properties}. @var{CompProp} refers to a sequence of
states and we refer to the properties that appear there as properties
of the computation. Examples are determinacy, non-failure, or cost.

So, we can start by adding the following @tt{pred} assertion to state
that when @pred{powers/3} is called the second argument is bound to a
number, using the built-in property @pred{num/1}:

```ciao
:- pred powers(A,B,C) : num(B).
```

We then proceed to run @apl{CiaoPP} again: 

@exfilter{power_without_assertions1.pl}{V,filter=warnings}  

As we can see, @apl{CiaoPP} continues producing some warning messages but they are now fewer.

@section{Regular types and other properties} 
@cindex{regular type, types, properties}
We have seen before how certain types can be used as @em{properties}
to describe predicates. In @apl{CiaoPP} we can define new regular
types using @decl{regtype} declarations. In general, properties (such
as these types) are normal predicates, but which meet certain
conditions (e.g., termination) and are marked as such via @tt{prop/1}
or @tt{regtype/1} declarations). Other properties like @tt{num/1},
@tt{var/1}, or @tt{not_fails} are builtins, defined in libraries. See
@ref{Declaring regular types} in the @apl{CiaoPP} manual for more
details on (regular) types, as well as other details about properties
in @apl{Ciao}). For example, our specification states that the first
argument is a list of numbers.  This property is available in the
@apl{Ciao} libraries, however, we choose to declare it ourselves. So
we represent the set of \"lists of numbers\" by the regular type
@tt{list_num}, defined as follows:

@comment{TODO: need include code with explicit language}
@includecode{code/regtypes1.pl}

The problem specification also tells us that the first argument is a
list of numbers and that @pred{powers/3} returns another number list
of numbers (for now, we will not put other restrictions such as being
a list of non-negative numbers). I.e., combining with the previous
information, we need to ensure that for any call to predicate
@pred{powers/3} with the first argument bound to a list of numbers,
the second argument bound to a number, and the third one unbound, if
the call succeeds, then the third argument will also be bound to a
list of numbers.

@begin{cartouche}
@bf{Exercise 2 (Solved). }@em{What assertion would we need to add?}
```ciao_runnable
%! \\begin{code}
:- pred powers(A,B,C) : (?, ?, ?) => (?) .   
%! \\end{code}
%! \\begin{opts}
solution=equal
%! \\end{opts}  
%! \\begin{solution}
:- pred powers(A,B,C) : (list_num(A), num(B), var(C)) => (list_num(C)).
%! \\end{solution}
```
@end{cartouche}

If we now take a look into the file generated by @apl{CiaoPP} we will
find that there are no warnings, i.e., @apl{CiaoPP} can now prove that
all calls to library predicates are correct and will not raise any
errors at run time (we will return to this topic later). Furthermore,
we will find in the output the following assertion:

@exfilter{power_without_assertions3.pl}{V,output=on,comments=on,filter=check_pred}

This means that the assertion that we have included has been marked as
checked, i.e., it has been validated, proving that indeed the third
argument of @pred{powers/3} will be bound to a list on success.

If we take a look again into the file generated by @apl{CiaoPP} we will find these assertions:  

@exfilter{power_without_assertions3.pl}{A,absdomain=types,name=remove_power,filter=tpred}

@exfilter{power_without_assertions3.pl}{A,absdomain=modes,name=remove_power,filter=tpred}

The sharing and freeness analysis abstract domain computes freeness,
independence, and grounding dependencies between program
variables. The second assertion expresses that the third argument is a
free variable while the first and second arguments are input values
(i.e., ground on call) when @pred{remove_power/3} is called (:). Upon
success, all three arguments will get instantiated. On the other hand,
the first assertion expresses that, if @pred{remove_power(N, A, B)} is
called with a number @var{N}, a pair-list of numbers in @var{A} and
any term in @var{B}, then @var{B} will on exit be a pair-list of
numbers. Therefore, we need a regular type @tt{list_pair} which
defines a list of pairs @tt{(X,Y)}. If we continue to examine the
output of @apl{CiaoPP} we can see this other assertion:

@exfilter{power_without_assertions3.pl}{A,absdomain=types,name=sorted_insert,filter=tpred}

@exfilter{power_without_assertions3.pl}{A,filter=regtype} 

Where we find new types, inferred by @apl{CiaoPP}.  The analyzer thus
tells us about types that represent the data that the program builds,
and we can use these definitions back in the source file to enhance
the specification. In our case, the second regular type is defining
the pairs, so we can copy it into the source file, giving it a
meaningful name for clarity, as follows:

@includecode{code/regtypes2.pl}

(Note that we can also use parametric types here, but we use a simple type for simplicity.)
Once we have defined these regular types, we can write more precise assertions:

@begin{cartouche}
@bf{Exercise 3. }@em{What assertion would we need to add?}
```ciao_runnable
%! \\begin{code}
:- pred remove_power(A,B,C) : (?, ?, ?) => (?) .     
%! \\end{code}
%! \\begin{opts}
solution=equal
%! \\end{opts}  
%! \\begin{solution}
:- pred remove_power(A,B,C) : (num(A), list_pair(B), var(C)) => list_pair(C).
%! \\end{solution}
```
@begin{note}
@em{@bf{Hint:} @pred{remove_power/3} is called in this program with
the first parameter being a number, the second argument being of type
@tt{list_pair} (i.e., bound to a list of pairs) and one variable. And
on success the third argument is bound to a @tt{list-pair}.}
@end{note}
@end{cartouche}

@begin{cartouche}
@bf{Exercise 4. }@em{What assertion would we need to add?}
```ciao_runnable
%! \\begin{code}
:- pred sorted_insert(A,B,C) : (?, ?, ?) => (?) .   
%! \\end{code}
%! \\begin{opts}
solution=equal
%! \\end{opts} 
%! \\begin{solution}
:- pred sorted_insert(A,B,C) : (list_pair(A), num_pair(B), var(C)) => list_pair1(C).
%! \\end{solution}
```
@begin{note}
@em{@bf{Hint:} @pred{sorted_insert/3} is called in this program with
the first parameter being of type @tt{list_pair} (i.e., bound to a
pair-list), the second argument being of type @tt{num_pair} ( i.e.,
bound to a pair of numbers) and one variable. And on success the third
argument is bound to a non-empty list-pair.}
@end{note}
@end{cartouche}

Using the information we have seen so far we would have the following
implementation:
 
```ciao_runnable
:- module(_,[powers/3],[assertions, regtypes, nativeprops]).

%! \\begin{focus}
:- regtype list_num(X) .
list_num([]).
list_num([X|T]) :-
    num(X),
    list_num(T).

% powers(X,N,P): P is the sorted list that contains the smallest N integers
% that are a non-negative power of one of the elements of the list X.
:- pred powers(A,B,C) : (list_num(A), num(B), var(C)) => (list_num(C)).

powers([],_,[]).
powers(Factors,N,Powers) :-
    quicksort(Factors, SFactors),
    create_pairs(SFactors,Pairs),
    first_powers(N,Pairs,Powers).

%! quicksort(Xs,Ys): Performs a quicksort of a list `Xs` and returns the
% result in Ys`.

quicksort(Xs,Ys) :- qsort(Xs,Ys,[]).

qsort([],DL,DL).

qsort([X|Xs],Head,Tail) :-
    partition(Xs,X,L,R),
    qsort(L,Head,[X|QR]),
    qsort(R,QR,Tail).

partition([],_,[],[]).
partition([X|Xs],Pv,[X|L],R) :- X =< Pv, !, partition(Xs,Pv,L,R). 
partition([X|Xs],Pv,L,[X|R]) :- X > Pv, partition(Xs,Pv,L,R).


%! create_pairs(F,P): `F` is a list and `P` is sorted list of pairs.
%  Each element of `P` has the form `(X,X)`, where `X` is a element of `F`.

create_pairs([],[]).
create_pairs([X|R],[(X,X)|S]) :- create_pairs(R,S).


:- regtype num_pair(P) .
num_pair((X, Y)):- num(X), num(Y).

:- regtype list_pair(L).
list_pair([]).
list_pair([X|Xs]):-
    num_pair(X),
    list_pair(Xs).

:- regtype list_pair1(L).
list_pair1([X|Xs]):-
   num_pair(X),
   list_pair(Xs).


%! first_powers(N,L,R): `R` is a sorted list with `N` non-negative numbers.
%  \includedef{first_powers/3}

:- pred first_powers(A,B,C) : (num(A), list_pair(B),var(C)) => (list_num(C)) .

first_powers(N,[(Power,Factor)|PFs],[Power|Powers]) :-
    N > 0, !,
    N1 is N-1,
    remove_power(Power,PFs,PFs1),
    Power1 is Power*Factor,
    sorted_insert(PFs1,(Power1,Factor),PFs2),
    first_powers(N1,PFs2,Powers).
first_powers(0,_,[]).


%! remove_powers(P,L,R): `R` is the sorted list of pairs obtained by removing from the list `L`
%  the pair (`P`,_).

:- pred remove_power(A,B,C) : (num(A), list_pair(B), var(C)) => list_pair(C) .

remove_power(_, [], []).
remove_power(Power, [(Power1, Factor)|RestOut], [(Power1, Factor)|RestOut]) :-
    Power =\= Power1, !.
remove_power(Power, [_|RestPFsIn], PFsOut) :-
    remove_power(Power, RestPFsIn, PFsOut).


%! sorted_insert(L,P,R): `R` is the sorted list of pairs obtained by adding to the list `L`
%  the pair `P`.

:- pred sorted_insert(A,B,C) : (list_pair(A), num_pair(B), var(C)) => list_pair1(C) .

sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]):- X =< X1, !.
sorted_insert([X1|L1], X, [X1|L]):- sorted_insert(L1, X, L).
%! \\end{focus}
```
 
@section{Bugs detected by CiaoPP}
@cindex{bugs, debugging}
In the sections above we have included assertions to describe some
properties that we require to hold of our program. But we also
mentioned that @apl{CiaoPP} can identify errors without these
assertions. So imagine we make some modifications to the predicate
@pred{remove_power/3} defined above:

@includecode{code/remove_power_bug1.pl}

If we now run @apl{CiaoPP} it produces the following output: 

@exfilter{remove_power_bug1.pl}{V,filter=warn_error} 

As we can see, different messages appear. In this section, we will explain one by one what each of these messages indicates, and how we can handle them:

@begin{itemize}
@item @bf{Singleton variable}: The first message is a warning message
which indicates that there are singleton variables. We know that the
singleton variables are those which appear only one time in a
clause. As mistyping a variable is a common mistake, for this reason,
@apl{CiaoPP} outputs a warning message indicating if a variable is
used only once (such warnings would also be emitted by the compiler).

@begin{cartouche}
@bf{Exercise 5 (Detecting Bugs). }@em{What variable do you need to change? (Only change the incorrect variable.)}
```ciao_runnable
:- module(_,[remove_power/3],[assertions]).
%! \\begin{code}
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut1).  
%! \\end{code}
%! \\begin{opts} 
solution=errors,message=singleton
%! \\end{opts}
%! \\begin{solution}
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).  

% In our case, we type PFsOut1 instead of PFsOut.
%! \\end{solution}
```
@end{cartouche}

@item @bf{No base case}: The fact that a predicate always fails is not
sufficient to conclude that there is a bug in the program. However, in
most cases this is actually a bug, as is the case in this program.
Predicate @pred{remove_power/3} is called recursively but has no base
case, this means it will either loop or fail. So, we add the following
base case and fix the error:

@includecode{code/remove_power_bug3.pl}

We now obtain the following messages:

@exfilter{remove_power_bug3.pl}{V,filter=warn_error}

@item @bf{Arity}: We have forgotten a parameter in the base case of
the recursive predicate @pred{remove_power/3}. Then, @apl{CiaoPP}
detects that two predicates: @pred{remove_power/2} and
@pred{remove_power/3} are defined, so it is possible that we have
forgotten or added an argument in one of them (these warnings are also
detected by the compiler and can also be turned off when using
multi-arity predicates).

@begin{cartouche}
@bf{Exercise 6 (Detecting Bugs). }@em{What is the correct base case?}
```ciao_runnable
%! \\begin{code}
:- module(_,[remove_power/3],[assertions]).

remove_power([],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).  
%! \\end{code}
%! \\begin{opts}
solution=errors,message=arity
%! \\end{opts}
%! \\begin{solution}
:- module(_,[remove_power/3],[assertions]).

remove_power(_,[],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).
%! \\end{solution}
```
@end{cartouche}

We run again @apl{CiaoPP}: 
@exfilter{remove_power_bug4.pl}{V,filter=errors}

@item @bf{Static Checking of Assertions in System Libraries}: As
mentioned before, @apl{CiaoPP} can find incompatibilities between the
ways in which library predicates are called.  In our example
@pred{=\\\\=/2} is a library predicate so suppose that incidentally a
bug was introduced in the second clause of @pred{remove_power/3}, and
instead of writing @var{Power1} we write @var{power1} (It is a bug
since variables always begin with a capital letter).  @apl{CiaoPP}
tells us that the @lib{arithmetic} library in @apl{Ciao} contains an
assertion of the form:
```ciao
:- check calls A=\\=B : ( nonvar(A), nonvar(B), arithexpression(A), arithexpression(B) ).
```
which requires the second argument of @pred{=\\\\=/2} to be an
arithmetic expression (which is a regular type also defined in the
arithmetic library) that contains no variables.  Moreover, the
@tt{eterms} analysis indicates us that in our program @var{A} is any
term and @var{B} is an auxiliary regular type which was created by
@apl{CiaoPP} to represent the term @tt{power1}.
 
@begin{cartouche}
@bf{Exercise 7 (Detecting Bugs). }@em{Although we have seen the
predicate without bugs, try to write it again without any error.}
```ciao_runnable
:- module(_,[remove_power/3],[assertions, regtypes, nativeprops]).

:- regtype list_num(X).
list_num([]).
list_num([X|T]) :-
      num(X), list_num(T).

:- regtype list_num1(X).  
list_num1([X|T]) :-
    num(X),
    list_num(T).

:- regtype num_pair(P).
num_pair((X, Y)) :- num(X), num(Y).

:- regtype list_pair(L). 
list_pair([]).
list_pair([X|Xs]) :-
    num_pair(X),
    list_pair(Xs).

:- regtype list_pair1(L).
list_pair1([X|Xs]) :-
   num_pair(X),
   list_pair(Xs).
%! \\begin{code}
:- pred remove_power(A,B,C) : (num(A), list_pair(B), var(C)) => list_pair(C).

remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut1).
%! \\end{code}
%! \\begin{opts}
solution=errors
%! \\end{opts}
%! \\begin{solution}
:- pred remove_power(A,B,C) : (num(A), list_pair(B), var(C)) => list_pair(C).

remove_power(_, [], []).
remove_power(Power, [(Power1, Factor)|RestOut], [(Power1, Factor)|RestOut]) :-
    Power =\\= Power1, !.
remove_power(Power, [_|RestPFsIn], PFsOut) :- 
    remove_power(Power, RestPFsIn, PFsOut).
%! \\end{solution}
```
@end{cartouche}
@end{itemize} 
  
@section{Nonfailure+Determinism Domain}
@cindex{determinism, non-failure, nf, det, nfdet}

So far we have only worked with the two most used abstract domains:
@tt{shfr} and @tt{eterms}. However, @apl{CiaoPP} has a wide variety of
abstract domains to perform analysis with.  In this section, we will
analyze the example with @tt{nfdet} analysis. The @tt{nfdet} combined
domain carries nonfailure (@tt{nf}) and determinism (@tt{det})
information, i.e., the analysis will be able to detect procedures that
can be guaranteed not to fail (produce at least one solution) and to
detect predicates which are deterministic (produce at most one
solution).

@subsection{Categories}

The following lattice diagram summarizes several determinacy and nonfailure properties inferred by the @tt{nf} and @tt{det} domains:

@begin{verbatim}
          nondet [0,inf] 
          /        \\
         /          \\
     semidet [0,1]  multi [1,inf]
        /       \\     / 
       /         \\   /      
    fails [0,0]   det [1,1]  
            \\      /
             \\    /
          bottom (non reachable)
@end{verbatim}

@begin{itemize}
@item @tt{semidet} = 0 or 1 solutions
@item @tt{multi} = 1 or more solutions
@item @tt{det} = 1 solution
@item @tt{fails} = 0 solutions
@end{itemize}
 
@subsection{Example: sorted_insert/3} 

In order to see these analyses in action, assume that our predicate
@pred{sorted_insert/3} is defined without the cut. If we analyze the
program with this modification:

@begin{cartouche}
@bf{Exercise 8 (Making predicates deterministic). }@em{Modify the predicate to make it deterministic:}
```ciao_runnable
:- module(_, [sorted_insert/3], [assertions,regtypes]).

:- regtype num_pair(P).
num_pair((X, Y)) :- num(X), num(Y).

:- regtype list_pair(L).
list_pair([]).
list_pair([X|Xs]) :-
    num_pair(X),
    list_pair(Xs).

:- regtype list_pair1(L).
list_pair1([X|Xs]) :-
   num_pair(X),
   list_pair(Xs).
%! \\begin{code}
:- pred sorted_insert(A,B,C) : (list_pair(A), num_pair(B), var(C)) => list_pair1(C).

sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]) :- X =< X1.
sorted_insert([P|L1], X, [P|L]) :- sorted_insert(L1, X, L).
%! \\end{code}
%! \\begin{opts}
A,ana_det=nfdet,name=sorted_insert,filter=tpred_plus
%! \\end{opts}
```
@end{cartouche}

the output includes the following assertions:

@exfilter{sorted_insert_multi.pl}{V,comments=on,output=on,filter=check_pred} 

Thus, we can see that the analyzer does verify the assertion that we
had included. However, we can also see these other assertions:

@exfilter{sorted_insert_multi.pl}{A,ana_det=nfdet,name=sorted_insert,filter=tpred_plus}

As we mentioned before, the @tt{+} field in @tt{pred} assertions
describes properties of the computation of the predicate (such as
determinism or non-failure). According to the diagram shown before,
@tt{multi} states that there is at least one solution but may have
more. Also, @tt{covered} means that for any input there is at least
one clause whose succeeds and @tt{possibly_not_mut_exclusive} denotes
that mutual exclusion is not ensured. This is because when the first
argument is a non-empty list both the second and third clauses will
succeed. When reasoning about determinacy, it is a necessary condition
(but not sufficient) that clauses of the predicate be pairwise
mutually exclusive, i.e., that only one clause will produce solutions.
In order to solve this, we can add either the complementary @tt{X >
X1} condition in the third clause or the cut in the second
clause. Obviously, for any particular call only one of the clauses
@tt{X =< X1} or @tt{X > X1} will succeed. Adding one of these two
options and analyzing the program again we can see that the predicate
is deterministic (modifying the previous example you can observe this
behavior).  @section{Dynamic Bug Finding with CiaoPP's Testing
Facilities} @cindex{testing, tests, unit test}

The specification throughout our program so far is that the predicate
@pred{powers/3} is called with a list of numbers as first argument, a
number @var{N} as second argument, and a free variable in the third
argument. However, the original specification states that the numbers
are actually non-negative integers. It also states that the list
produced on success in the third argument is also a list of
non-negative integers, and, furthermore, that this list is in
ascending order (i.e., sorted in ascending order).

We can specify all this by first defining new properties as follows
(we use @tt{nnegint} from the @apl{Ciao} libraries):
@includecode{code/regtypes_int.pl}

@tt{list_nnegint/1} checks if the argument is a list of non-negative
integers, @tt{sorted/1} checks if the argument is a sorted list. Other
properties like @tt{var/1} or @tt{not_fails} are builtins, defined in
libraries. These properties are important because they will be used by
@apl{CiaoTest} as generators for test cases. Then including them in
our program together with the following assertion:

```ciao
:- pred powers(A,B,C) : (list_nnegint(A), nnegint(B), var(C)) => (list_nnegint(C), sorted(C)) + not_fails.
```

and running @apl{CiaoPP} we will see that this assertion cannot be
proved nor disproved statically with the standard @apl{CiaoPP}
domains:

@exfilter{powers.pl}{V,output=on,filter=check_pred}

This is because there is no abstract domain that covers properly the
@tt{sorted/1} property. This is something that can occur specially
with user-defined properties. In these cases @apl{CiaoPP} will
generate @em{run-time} checks for the properties that have not been
verified statically in such assertions.  Such runtime checks will
raise an error if the assertion is violated, albeit at run time. Thus,
they at least ensure that execution paths that violate the assertions
are captured during execution.

Since letting errors be raised after deployment is less desirable, a
step that can be taken in order to deal with non-verified assertions
is to generate test cases to try to find a counterexample, i.e., an
input for which an error is raised by the run-time tests.  This can be
done either manually, by adding @tt{test} assertions (unit tests), to
the program, or using the provisions that @apl{CiaoPP} offers for
@em{automatically} generating test cases from the call fields of
assertions. This process works as follows:

Consider this buggy implementation of @tt{quicksort/2} in @tt{powers/3}:
```ciao_runnable 
:- module(_,[powers/3],[assertions,nativeprops]).

:- prop list_nnegint(X) + regtype  .  
list_nnegint([]).
list_nnegint([X|T]) :- 
    nnegint(X), list_nnegint(T).

:- prop sorted(Xs).

sorted([]).
sorted([_]).
sorted([X,Y|Ns]) :-
	X =< Y,
	sorted([Y|Ns]).

%! \\begin{focus}

:- pred powers(A,B,C) : (list_nnegint(A), nnegint(B), var(C)) => (list_nnegint(C), sorted(C) ) + not_fails.

:- test powers(A,B,C) : (A = [3,4,5], B = 17) => (C = [3,4,5,9,16,25,27,64,81,125,243,256,625,729,1024,2187,3125]) + not_fails.
:- test powers(A,B,C) : (A = [2,9999999,9999998], B = 20) => (C = [2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576]) + not_fails.
:- test powers(A,B,C) : (A = [2,4], B = 6) => (C = [2,4,8,16,32,64]) + not_fails.

powers([],_,[]).
powers(Factors,N,Powers) :-
    quicksort(Factors, SFactors),
    create_pairs(SFactors,Pairs),
    first_powers(N,Pairs,Powers).

% qsort with a slight mistake: it may fail when there are repeated numbers in the list
quicksort(Xs,Ys) :- qsort(Xs,Ys,[]).

qsort([],DL,DL).

qsort([X|Xs],Head,Tail) :-
    partition(Xs,X,L,R),
    qsort(L,Head,[X|QR]),
    qsort(R,QR,Tail).

partition([],_,[],[]).
partition([X|Xs],Pv,[X|L],R) :- X < Pv, !, partition(Xs,Pv,L,R). % (1) should be >= (or =< below)
partition([X|Xs],Pv,L,[X|R]) :- X > Pv, partition(Xs,Pv,L,R).
%! \\end{focus}

create_pairs([],[]).
create_pairs([X|R],[(X,X)|S]) :- create_pairs(R,S).


first_powers(N,[(Power,Factor)|PFs],[Power|Powers]) :-
    N > 0, !,
    N1 is N-1,
    remove_power(Power,PFs,PFs1),
    Power1 is Power*Factor,
    sorted_insert(PFs1,(Power1,Factor),PFs2),
    first_powers(N1,PFs2,Powers).
first_powers(0,_,[]).e
 
remove_power(_,[],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\\= Power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).

sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]) :- X =< X1, !.
sorted_insert([P|L1], X, [P|L]) :- sorted_insert(L1, X, L).
```

This predicate sorts a given list of integers from lowest to
highest. However, we have introduced an intentional bug @tt{(1 in the
listing)} that causes the program to fail when a list with repeated
elements is given.

After the @tt{pred} assertion we can see three test assertions that
the user has included to check the behavior of the predicate. They
cover the examples given in the problem statement.

@subsection{Setting up CiaoPP flags}
  
In order to carry out the operations described above (running unit
tests and test generation) automatically we need to activate a few
flags in CiaoPP's menu.  Under the @tt{Test assertions} category, we
will find the @tt{Run test assertions (run_utests)} and @tt{Generate
tests from check assertions (test_gen)} flags that we need to turn on:

@image{Figs/ciaopp-flag-menu}{650}{375} 

Now, when we tell @apl{CiaoPP} to perform assertion checking, it will
first run the usual static analysis and checking of assertions, then
it will run all unit tests present in the program. If at least one of
them fails, then random test generation is skipped. However, if all
unit tests pass, test generation is performed as a last step to try to
find test cases that make the assertions fail, hence revealing faults
in our code.

@subsection{Running unit tests}

After assertion checking, @apl{CiaoTest} runs all unit tests present
in the program:

@exfilter{power_testing.pl}{V,output=on,testing=on,filter=test}

In this case all tests passed without errors, so random test generation is performed.

@subsection{Generating Tests}

@apl{CiaoTest} will read the assertions left to be checked and
generate goals for that predicate satisfying the assertion
precondition and execute them to either check that the assertion holds
for those cases or find errors.  Lets see what @apl{CiaoTest} did:

@exfilter{power_testing.pl}{V,testing=on,test_gen=on,filter=errors}

By default @apl{CiaoTest} generates 100 cases for each assertion, or
stops before if it finds one case that does not meet the assertion
post-condition. Keep in mind that the generation is random, so do not
expect to get the same results if you try this yourself, in fact, it
may very well be that none of the test cases generated makes the
program fail, so it is recommended to run @apl{CiaoTest} a couple
times or increase the number of cases to be generated using the
@tt{num_test_cases} option in CiaoPP's flags menu. For that same
reason, it is also important to note that of course even if
@apl{CiaoTest} does not find any cases that violate the assertion, one
cannot affirm that the assertion is true.

The failed test cases that we got are valid calls to @tt{powers/3}
that did not comply with the post-condition, in particular, they
violated the computational properties field, since they where required
to not fail. Thus, they are counter-examples that prove that the
remaining part of the assertion does not hold. Now we are aware that
the predicate is not behaving as it should. If we look at the input
lists that violate the assertion, it is not too difficult too realize
that there are repeated elements in them, and that this may be the
source of our problems.

If it is not apparent where the bug is through observation, a good
next step would be to debug the predicate in the interactive source
debugger calling it with the counter-examples that @apl{CiaoTest}
generated for us and look for the point in which the error occurs.

If we take a look into CiaoPP's output file now, we will see that some
of the assertions left to be checked after static analysis have been
proven false by the counter-examples found via test generation:

@exfilter{power_testing.pl}{V,output=on,testing=on,test_gen=on,filter=check_pred}
In the computation properties field of the assertions that have been
marked as false, we can see a new property @tt{by/1} that is used to
indicate the source of the failure. In our case, that source is the
failed test cases, which are represented by @tt{texec} declarations,
each identified by a different @tt{id/1}, which is what appears in the
@tt{by/1} field.

In this section we showed how given a buggy program we can follow a
simple methodology to help us spot those bugs. @apl{CiaoPP}'s
analyzers and verifiers offer us the static analysis tools to check
part of the assertions and then we can ask it to use @apl{CiaoTest} to
check the remaining unchecked assertions by running the unit tests
present in the program and with assertion-based random test
generation. Depending on the properties involved, this procedure can
often be fully automatic, just needing setting the relevant flags. If
failing test cases are found they can be excellent starting points for
more classical debugging.  Other possible approaches include
implementing a new abstract domain for a specific property (i.e., in
this case a new domain that infers if a list is sorted or not) or
proving the property by hand or with an automatic theorem prover.
These solutions are more powerful than testing, in the sense that they
can potentially verify that there are no errors in the program, while
testing can find bugs but cannot verify that there are none, but they
are also more involved.
").
