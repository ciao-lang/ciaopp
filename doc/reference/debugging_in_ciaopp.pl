:- module(debugging_in_ciaopp,[],[assertions]).

:- doc(filetype, documentation).

:- doc(title,"Using assertions for preprocessing programs").

:- doc(author,"Francisco Bueno").

:- doc(summary,"The aim of this document is to serve as a
  guideline for programmers in the use of the Ciao Program
  Precompiler. This document explains the use of assertions to
  describe the specification of a program and the role of other
  assertion-related declarations so that the program can be statically
  debugged with the Ciao Program Precompiler and programming
  environment.").

:- doc(module,"

This chapter explains the use of assertions to specify a program
behaviour and properties expected to hold of the program. It also
clarifies the role of assertion-related declarations so that a program 
can be statically preprocessed with CiaoPP.

CiaoPP starts a preprocessing session from a piece of code, annotated
with assertions. The code can
be either a complete self-contained program or part of a larger
program (e.g., a module, or a user file which is only partial). The
assertions annotating the code describe some properties which the
programmer requires to hold of the program.
Assertions are used also to
describe to the static analyzer some properties of the interface of the
code being
preprocessed at a given session with other parts of the program that
code belongs to.  In addition, assertions can be used to provide
information to the static analyzer, in order to guide it, and also to
control specialization and other program transformations.

This chapter explains the use of assertions in describing to CiaoPP: 
(1) the program specification, (2) the program interface, and (3) additional 
information that might help static preprocessing of the program.

In the following, the Ciao assertion language is briefly
described and heavily used. In @ref{The Ciao assertion language}, a
complete reference description of assertions is provided. More
detailed explanations of the language can be found in
@cite{assert-lang-disciplbook}.

This chapter also introduces and uses properties, and among them (regular)
types. See @ref{Basic data types and properties}, for a concrete reference
of (some of) the Ciao properties.
See @ref{Declaring regular types}, for a presentation of the Ciao type
language and an explanation on how you can write your own properties and 
types.

Most of the predicates used below which are not defined belong to the 
@index{ISO-Prolog} standard @cite{iso-prolog}. The builtin
(or primitive) constraints used have also become more or less de-facto
standard.  For detailed descriptions of particular constraint logic
programming builtins refer for example to the CHIP @cite{chip-manual},
PrologIV @cite{prologiv-manual}, and Ciao @cite{ciao-manual-1.10} 
manuals.

@section{Assertions}

Predicate assertions can be used to declare properties of the
execution states at the time of calling a predicate and upon predicate
success. Also, properties of the computation of the calls to a
predicate can be declared.

Assertions may be qualified by keywords @tt{check} or
@tt{trust}. Assertions qualified with the former---or not
qualifed---are known as check assertions; those qualified with the
latter are known as trust assertions. Check assertions state the
programmer's intention about the program and are used by the debugger
to check for program inconsistencies. On the contrary, trust assertions are
``trusted'' by CiaoPP tools.

@begin{cartouche}
@begin{itemize}
@item{} The specification of a program is made of all check
  assertions for the program predicates.
@end{itemize}
@end{cartouche}

@subsection{Properties of success states}

They are similar in nature to the @em{postconditions} used in program
verification. They can be expressed in our assertion language using
the basic assertion:
@begin{verbatim}
:- success Goal => Postcond.
@end{verbatim}

This assertion should be interpreted as, ``for any call of the
form @tt{Goal} which succeeds, on success @tt{Postcond} should also
hold'' . 

Note that, in contrast to other programming paradigms, calls
to a predicate may either succeed or fail.  The postcondition stated
in a @tt{success} assertion only refers to successful executions.

@subsection{Restricting assertions to a subset of calls}

Sometimes we are interested in properties which refer not to all
invocations of a predicate, but rather to a subset of them. With this
aim we allow the addition of preconditions (@tt{Precond}) to predicate
assertions as follows: `@tt{Goal} @tt{:} @tt{Precond}'.

For example, @tt{success} assertions can be restricted and we obtain
an assertion of the form:
@begin{verbatim}
:- success Goal : Precond => Postcond.
@end{verbatim}
which should be interpreted as, ``for any call of the
form @tt{Goal} for which @tt{Precond} holds, if the call succeeds then
on success @tt{Postcond} should also hold''. 

@subsection{Properties of call states}

It is also possible to use assertions to describe properties about the
calls for a predicate which may appear at run-time. An assertion of
the form:
@begin{verbatim}
:- calls Goal : Cond.
@end{verbatim}
must be interpreted as, ``all calls of the form @tt{Goal} should
satisfy @tt{Cond}''. 

@subsection{Properties of the computation}

Many other properties which refer to the computation of the
predicate (rather than the input-output behaviour) are not
easily expressible using @tt{calls} and @tt{success} predicate
assertions only. Examples of properties of the computation which we
may be interested in are: non-failure, termination, determinacy,
non-suspension, etc. 

This sort of properties are expressed by an assertion of the form:
@begin{verbatim}
:- comp Goal : Precond + Comp-prop.
@end{verbatim}
which must be interpreted as, ``for any call of the form @tt{Goal} for
which @tt{Precond} holds, @tt{Comp-prop} should
also hold for the computation of @tt{Goal}''. 
Again, the field `@tt{:} @tt{Precond}' is optional. 

@subsection{Compound assertions}

In order to facilitate the writing of assertions, a compound predicate
assertion can be used as syntactic sugar for the above mentioned basic
assertions. Each compound assertion is translated into one or several
basic assertions, depending on how many of the fields in the compound
assertion are given. The compound assertion is as follows.
@begin{verbatim}
:- pred Pred : Precond => Postcond + Comp-prop.
@end{verbatim}

Each such compound assertion corresponds to: a @tt{success} assertion
of the form:
@begin{verbatim}
:- success Pred : Precond => Postcond.
@end{verbatim}
if the @tt{pred} assertion has a @tt{=>} field (and a @tt{:} field).
It also corresponds to a @tt{comp} assertion of the form:
@begin{verbatim}
:- comp Pred : Precond + Comp-prop.
@end{verbatim}
if the @tt{pred} assertion has a @tt{+} field (and a @tt{:} field).

All compound assertions given for the same predicate correspond to a 
single @tt{calls} assertion. This @tt{calls} assertion states as 
properties of the
calls to the predicate a disjunction of the properties stated by the
different compound assertions in their @tt{:} field. Thus, it is of the form:
@begin{verbatim}
:- calls Pred : ( Precond1 ; ... ; Precondn ).
@end{verbatim}
for all the @tt{Precondi} in the @tt{:} fields of (all) the different
@tt{pred} assertions.

Note that when compound assertions are used, @tt{calls} assertions are
always implicitly generated.  If you do not want the @tt{calls}
assertion to be generated (for example because the set of assertions
available does not cover all possible uses of the predicate) basic
@tt{success} or @tt{comp} assertions rather than compound
(@tt{pred}) assertions should be used.

@subsection{Examples of compound assertions}
Consider the classical qsort program for sorting lists.
We can use the following assertion in order to require that
the output of procedure @tt{qsort} be a list:
@begin{verbatim}
:- success qsort(A,B) => list(B).
@end{verbatim}
Alternatively, we may require that if @tt{qsort} is called with a
list in the first argument position and the call succeeds, then on
success the second argument position should also be a list. This is
declared as follows:
@begin{verbatim}
:- success qsort(A,B) : list(A) => list(B).
@end{verbatim}
The difference with respect to the previous assertion is that @tt{B}
is only expected to be a list on success of predicate @tt{qsort/2} if
@tt{A} was a list at the call.

In addition, we may also require that in all calls to predicate
 @tt{qsort} the first argument should be a list.  The following
 assertion will do:
@begin{verbatim}
:- calls qsort(A,B) : list(A).
@end{verbatim}

The @tt{qsort} procedure should be able to sort all lists. Thus, we
also require that all calls to it that have a list in the first
argument and a variable in the second argument do not fail:
@begin{verbatim} 
:- comp qsort(A,B) : (list(A) , var(B)) + does_not_fail.
@end{verbatim}

Instead of the above basic assertions, the following compound one could
be given:
@begin{verbatim} 
:- pred qsort(A,B) : (list(A) , var(B)) => list(B) + does_not_fail.
@end{verbatim}
which will be equivalent to:
@begin{verbatim}
:- calls qsort(A,B) : (list(A), var(B)).
:- success qsort(A,B) : (list(A), var(B)) => list(B).
:- comp qsort(A,B) : (list(A) , var(B)) + does_not_fail.
@end{verbatim}

This will not allow to call @tt{qsort} with anything else than a
variable as second argument. If this use of @tt{qsort} is expected,
one should have added the assertion:
@begin{verbatim} 
:- pred qsort(A,B) : list(A) => list(B).
@end{verbatim}
which, together with the above one, will imply:
@begin{verbatim}
:- calls qsort(A,B) : ((list(A), var(B)) ; list(A)).
@end{verbatim}
Then it is only required that @tt{A} be a list.

@section{Properties}

Whereas each kind of assertion indicates @em{when}, i.e., in which
states or sequences of states, to check the given
properties, the properties themselves define @em{what} to check.
Properties are used to say things such as ``X is a
list of integers,'' ``Y is ground,'' ``p(X) does not fail,'' etc. and
in Ciao they are logic predicates, in the sense that the
evaluation of each property either succeeds or fails. The failure or
success of properties typically needs to be determined at the time
when the assertions in which they appear are checked.  Assertions can be
checked both at compile-time by CiaoPP and at run-time by Ciao itself
(after the instrumentation of the program by CiaoPP).
In this section 
we will concentrate exclusively on run-time checking.

A property may be a predefined predicate in the language (such as 
@tt{integer(X)}) or constraint (such as @tt{X>5}). Properties may include
extra-logical predicates such as @tt{var(X)}). Also, expressions built
using conjunctions of properties,@footnote{Although disjunctions are also 
  supported, we restrict our attention to only conjunctions.}
or, in principle, any predicate defined
by the user, using the full underlying (C)LP language.  As an example,
consider defining the predicate @tt{sorted(B)} and using it as a
postcondition to check that a more involved sorting algorithm such as
@tt{qsort(A,B)} produces correct results.

While user-defined properties allow for properties that are as
general as allowed by the full source language syntax, some
limitations are useful in practice. Essentially, the
behaviour of the program should not change in a fundamental way depending on
whether the run-time tests are being performed or not. For example,
turning on run-time
checking should not introduce non-termination in a program which
terminates without run-time checking. To this end, it is required that the
user ensure that the execution of properties terminate for any
possible initial state.  Also, checking a property should not change
the answers computed by the program or produce unexpected
side-effects.  Regarding computed answers, in principle properties are
not allowed to further instantiate their arguments or add new
constraints.
Regarding side-effects, it is required that the code
defining the property does not perform input/output, add/delete
clauses, etc. which may interfere with the program behaviour.  It is
the user's responsibility to only use predicates meeting these
conditions as properties. 
The user is required
to identify in a special way the predicates which he or she has
determined to be legal properties. This is done by means of a
declaration of the form 
@begin{verbatim}
:- prop Spec.
@end{verbatim}
where @tt{Spec} is a predicate specification in the form
 @tt{PredName}/@tt{Arity}.

Given the classes of assertions presented previously, there are two
fundamental classes of properties. The properties used in the
@tt{Cond} of calls assertions, @tt{Postcond} of success
assertions, and @tt{Precond} of success and comp
assertions refer to a particular execution state and we refer to them
as @em{properties of execution states}. The properties used in the
@tt{Comp-prop} part of comp assertions refer to a sequence of
states and we refer to them as @em{properties of computations}.

Basic properties, including instantiation and compatibility state
properties, types, and properties of computations (all discussed 
in @ref{Declaring regular types})
are documented in @ref{Basic data types and properties}.

@comment{include{writing_props}}


@section{Preprocessing units}

The preprocessing unit is the piece of code that is made available to
CiaoPP at a given preprocessing session. Normally, this is a file, but
not all the code of a program is necessarily contained in one single
file: in order to statically manipulate the code in a file, CiaoPP needs
to know the interactions of this code with other pieces of the
program---probably scattered over other files---, as well as what the
user's interaction  with the code will be upon execution. This is also
done through the use of assertions. 

If the preprocessing unit is self-contained the only interaction of its
code (apart from calling the builtin predicates of the language) is
with the user.
The user's interaction with the program consists in querying the
program. The predicates that may be directly queried by the user are
entry points to the preprocessing unit.

Entry points can be declared in two ways: using a module declaration
specifying the entry points, or using one entry declaration 
for each entry point. If entry declarations are used,
instead of, or in addition to, the module declaration, they can also
state properties which will hold at the time the predicate is called.

However, if the preprocessing unit is not self-contained, but only part of
a larger program, then other interactions may occur.
The interactions of the preprocessing unit include: the user's queries,
calls from other parts of the program to the unit code, calls
to the unit code from unit code which does not appear explicitely in the
unit text, and calls from the unit code to other parts of the program.

First, other parts of the program can call predicates defined
in the preprocessing unit. CiaoPP needs to know this information.
It must be declared by specifying additional entry points, together with
those corresponding to the user's queries.

Second, the preprocessing unit itself may contain meta-calls which
may call any unspecified predicate. All predicates that may be called
in such a way should be declared also as entry points. 
Additional entry points also occur when there are predicates defined
in the preprocessing unit which can be dynamically modified. In this case
the code dynamically added can contain new predicate calls. These calls
should be declared also as entry points.

Note that @em{all} entry points to the preprocessing unit should be
declared: entry points including query calls that the user may issue
to the program, or another part of the program can issue to the unit,
but also @em{dynamic calls}: goals that may be run within the unit
which do not appear explicitely in the unit text, i.e., from
meta-predicates or from dynamic clauses which may be asserted during
execution.
In all cases, @em{entry} declarations are used to declare entry
points.@footnote{When the language supports a module system, entry
  points are implicitely declared by the exported predicates. In this
  case entry declarations are only used for local predicates if there
  are dynamic calls.}

Third, the unit code may call predicates defined in other parts of the
program. The code defining such predicates is termed @em{foreign
  code}, since it is foreign to the preprocessing unit. It is important
that CiaoPP knows information about how calls to foreign code
will succeed (if they succeed), in order to improve its accuracy.
This can be done using @em{trust} declarations.

Also, trust declarations can be used to provide the preprocessor with extra 
information. They can be used to describe calls to predicates defined
within the preprocessing unit, in addition to those describing foreign code.
This can improve the information available to the preprocessor and thus
help it in its task. Trust declarations state properties
that the programmer knows to hold of the program.
@comment{
%% One example of the use of trust declarations is in describing
%% predicates not defined in the preprocessing unit itself, which includes
%% foreign code and the language builtins.
}

The builtin predicates is one particular case of predicates the
definitions of which are never contained in the program itself.
Therefore, preprocessing units never contain code to define
the builtins that they use.
However, the Ciao Program Precompiler makes no assumptions
on the underlying language (except that it is constraint logic
programming). Thus, all information on the behaviour of the language
builtins should be made available to it by means of
assertions (although this does not concern the application programmer
who is going to preprocess a unit, rather it concerns the system
programmer when installing the Ciao Program Precompiler
@comment{ --see @ref{Describing builtins by means of assertions}}
). 

The rest of this document summarizes how assertions can be used 
to declare the preprocessing unit interactions. It shows the use of entry 
and trust declarations in preprocessing programs
with CiaoPP.@footnote{This manual concentrates on one
  particular use of the declarations for solving problems related to
  compile-time program analysis. However, there are other possible
  solutions. For a complete discussion of these
  see @cite{full-prolog-esop96}.}

@section{Foreign code}

A program preprocessing unit may make use of predicates defined in other
parts of the program. Such predicates are foreign to the preprocessing
unit, i.e., their code is not in the unit itself. In this case, CiaoPP
needs to know which is the effect that such predicates may
cause on the execution of the predicates defined in the unit. For this
purpose, trust declarations are used.

Foreign code includes predicates defined in other modules which are
used by the preprocessing unit, predicates defined in other files which do
not form part of the preprocessing unit but which are called by it,
builtin predicates@footnote{However, builtin predicates are usually
  taken care of by the system programmer, and the preprocessor, once
  installed, already ``knows'' them.}
used by the code in the preprocessing unit, and code 
written in a foreign language which will be linked with the program.
All foreign calls (except to builtin predicates) need to be
declared.@footnote{However, if the language supports a module system,
  and the preprocessor is used in modular analysis operation mode, trust
  declarations are imported from other modules and do not need to be
  declared in the preprocessing unit.}

@begin{cartouche}
@begin{itemize}
@item{} The effect of calls to foreign predicates may be declared
@comment{(in the unit the predicates are defined)}
  by using trust declarations for such predicates.
@end{itemize}
@end{cartouche}

@cindex{trust assertions}
Trust declarations have the following form:
@begin{verbatim}
:- trust success Goal : ( Prop, ..., Prop )
                 => ( Prop, ..., Prop ).
@end{verbatim}
where @tt{Goal} is an atom of the foreign predicate, with
all arguments single distinct variables, and @tt{Prop} is an atom
which declares a property of one (or several) of the goal variables.

The first list of properties states the information at the time of
calling the goal and the second one at the time of success of the
goal. Thus, such a trust assertion declares that for any call to the
predicate where the properties in the first list hold, those of the
second will also hold upon success of the call.

Simplified versions of trust assertions can also be used, much the
same as with entry declarations. See @ref{Assertions}.

Trust declarations are a means to provide the preprocessor
with extra information about the program states. This
information is guaranteed to hold, and for this reason the preprocessor
@em{trusts} it. Therefore, it should be used with great care, since
if it is wrong the precompilation of your program will possibly be wrong.

@subsection{Examples of trust assertions}
The following annotations describe the behavior of the
predicate @tt{p/2} for two possible call patterns:
@begin{verbatim}
:- trust success p/2 : def * free => def * def.
:- trust success p/2 : free * def => free * def.
@end{verbatim}
This would allow performing the analysis even if the code for @tt{p/2} is not present.
@comment{
%%  provided that the calls to @tt{p/2} that appear
%% in the program conform to one of
%% the two call patterns above.  
}
In that case
the corresponding success information in the annotation can be
used (``trusted'') as success substitution.

In addition, trust declarations can be used to improve the results of
compile-time program analysis when they are imprecise. This may
improve the accuracy of the debugging, possibly allowing it to find
more bugs.

@section{Dynamic predicates}

Predicate definitions can be augmented, reduced, and modified during
program execution. This is done through the database manipulation
builtins, which include @tt{assert}, @tt{retract}, 
@tt{abolish}, and @tt{clause}.  These builtins (with the exception
of @tt{clause}) dynamically manipulate the program itself by adding
to or removing clauses from it. Predicates that can be affected by
such builtins are called dynamic predicates.

There are at least two possible classes of dynamic predicates which
behave differently from the point of view of static manipulation.
First, clauses can be asserted and/or
retracted to maintain an information database that the program
uses. In this case, usually only facts are asserted. Second, full
clauses can be asserted for predicates which are also called within
the program.

The first class of dynamic predicates are declared by data
declarations. The second class by dynamic declarations. The form of
both declarations is as follows:
@cindex{data declaration}
@cindex{dynamic declaration}
@begin{verbatim}
:- data Spec, ..., Spec.
:- dynamic Spec, ..., Spec.
@end{verbatim}
where @tt{Spec} is a predicate specification in the form
 @tt{PredName}/@tt{Arity}.

@begin{cartouche}
@begin{itemize}
@item Dynamic predicates which are called must be declared by
  using a dynamic declaration.
@end{itemize}
@end{cartouche}

Of course, the preprocessor cannot know of the effect that dynamic clauses 
added to the definition of a predicate may cause in the execution of that
predicate. However, this effect can be described to the preprocessor by
adding trust declarations for the dynamic predicates.

@begin{cartouche}
@begin{itemize}
@item{} The effect of calls to predicates which are dynamically modified
may be declared by using trust declarations for such predicates.
@end{itemize}
@end{cartouche}

@section{Entry points}

In a preprocessing session (at least) one entry point to the preprocessing
unit is required. It plays a role during preprocessing similar to that of the
query that is given to the program to run. Several entry points may be given.
Entry points are given to the preprocessor by means of entry or module
declarations.

If the preprocessing unit is a module, only the exported predicates can be
queried. If the preprocessing unit is not a module, all of its predicates
can be queried: all the unit predicates may be entry points to it. 
Entry declarations can then be used by the programmer to specify additional
information about the properties that hold of the arguments of a
predicate call when that predicate is queried.

Note that if the unit is not a module all of its predicates are
considered entry points to the preprocessor. However, if the unit
incorporates some entry declarations the preprocessor will act as if the
predicates declared were the only entry 
points (the preprocessing session being valid for a particular use of the
unit code---that specified by the entry declarations given).

@begin{cartouche}
@begin{itemize}
@item{} All predicates that can be queried by the user and all
  predicates that can be called
  from parts of the program which do not explicitely appear in the
  preprocessing unit 
  should (but need not)
  be declared as entry points by using entry declarations.
@end{itemize}
@end{cartouche}

The entry declaration has the following form:
@cindex{entry declaration}
@begin{verbatim}
:- entry Goal : ( Prop, ..., Prop ).
@end{verbatim}

where @tt{Goal} is an atom of the predicate that may be called, with
all arguments single distinct variables, and @tt{Prop} is an atom
which declares a property of one (or several) of the goal variables.
The list of properties is optional.

There are alternative formats in which the properties can be given: as
the arguments of @tt{Goal} itself, or as keywords of the declaration.
For a complete reference of the syntax of assertions, see
@ref{Assertions}. 

@subsection{Examples of entry declarations}
Consider the following program:
@begin{verbatim}
append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).
@end{verbatim}

It may be called in a classical way with the first two arguments bound
to lists, and the third argument a free variable. This can be
annotated in any of the following three ways:
@begin{verbatim}
:- entry append(X,Y,Z) : ( list(X), list(Y), var(Z) ).
:- entry append/3 : list * list * var.
:- entry append(list,list,var).
@end{verbatim}

Assume you have the following program:
@begin{verbatim}
p(X,Y):- q(X,Y,Z).
q(X,Y,Z):- X = f(Y,Z), Y + Z = 3.
@end{verbatim}
Assume that @tt{p/2} is the only entry point. If you include the
following declaration: 
@begin{verbatim}
:- entry p/2.
@end{verbatim}
or, equivalently,
@begin{verbatim}
:- entry p(X,Y).
@end{verbatim}
the code will be preprocessed as if goal @tt{p(X,Y)} was called with the
most general call pattern (i.e., as if @tt{X} and @tt{Y} may have
any two values, or no value at all---the variables being free).

However, if you know that @tt{p/2} will always be called with the 
first argument uniquely defined and the second unconstrained, you can
then provide more accurate information by introducing one of the
following declarations:
@begin{verbatim}
:- entry p(X,Y) : ( def(X), free(Y) ).
:- entry p(def,free).
@end{verbatim}

Now assume that @tt{p/2} will always be called with the first
argument bound to the compound term @tt{f(A,B)} where @tt{A} is
definite and @tt{B} is unconstrained, and the second argument of
@tt{p/2} is unconstrained. The entry declaration for this call
pattern is: 
@begin{verbatim}
:- entry p(X,Y) : ( X=f(A,B), def(A), free(B), free(Y) ).
@end{verbatim}

If both call patterns are possible, the most accurate approach is to
include both entry declarations in the preprocessing unit. The preprocessor
will then analyze the program for each declaration. Another
alternative is to include an entry declaration which approximates both
call patterns, such as one of the following two:
@begin{verbatim}
:- entry p(X,Y) : free(Y).
:- entry p(X,free).
@end{verbatim}
which state that @tt{Y} is known to be free, but nothing is known of
@tt{X} (since it may or may not be definite).

@section{Modules}

Modules provide for encapsulation of code, in such a way that
(some) predicates defined in a module can be used by other parts of
the program (possibly other modules), but other (auxiliary) predicates
can not. The predicates that can be used are exported by the module
defining them and imported by the module(s) which use(s) them.
Thus, modules provide for a natural declaration of the allowed entry
points to a piece of a program.

@cindex{module declaration}
A module is identified by a module declaration at the beginning of the
file defining that module.
The module declaration has the following form:
@begin{verbatim}
:- module(Name, [ Spec,...,Spec ] ).
@end{verbatim}
where the module is named @tt{Name} and it exports the predicates in
the different @tt{Spec}'s.

Note that such a module declaration is equivalent, for the purpose of
static preprocessing, to as many entry declarations of the form: 
@begin{verbatim}
:- entry Spec.
@end{verbatim}
as there are exported @tt{Spec}'s.


@section{Dynamic calls}

In addition to entry points there are other calls that may occur from
within a piece of code which do not explicitely appear in the code
itself. Among these are metacalls, callbacks, and calls from clauses
which are asserted during program execution.

Metacalls are literals which call one of their arguments at run-time,
converting at the time of the call a term into a goal. Predicates in
this class are not only @tt{call}, but also @tt{bagof}, 
@tt{findall}, @tt{setof}, negation by failure, and @tt{once} (single 
solution).

Metacalls may be static, and this kind of calls need not be
declared. A static metacall is, for example, @tt{once(p(X))}, where
the predicate being called is statically identifiable (since it
appears in the code). On the other hand, metacalls of the form
@tt{call(Y)} are dynamic, since the predicate being called will only
be determined at runtime.@footnote{However, sometimes analysis
  techniques can be used to transform dynamic metacalls into static
  ones.} 

@comment{
%% Note that identifying a metacall to be static relies on the knowledge
%% of which of the arguments hold the metaterm: for this we need the
%% metapredicate declaration ...
}

Callbacks are also metacalls. A callback occurs when a piece of a
program uses a different program module (or object) in such a way that
it provides to that module the call that it should issue upon return.
Callbacks, much the same as metacalls, can be either dynamic or
static. Only the predicates of the preprocessing unit which can be
dynamically called-back need be declared.

Clauses that are asserted during program execution correspond to code
which is dynamically created; thus, the preprocessor cannot be aware of
such code during a (compile-time) preprocessing session. The calls that
may appear from the body of a clause which is dynamically created and
asserted are also dynamic calls.

@begin{cartouche}
@begin{itemize}
@item{} All dynamic calls must be declared by using entry
  declarations for the predicates that can be called in a dynamic
  way.
@end{itemize}
@end{cartouche}

@subsection{Examples of dynamic calls}
Consider a program where you use the @tt{bagof} predicate to collect
all solutions to a goal, and the program call looks like:
@begin{verbatim}
p(X,...) :- ..., bagof(P,X,L), ...
@end{verbatim}
However, you know that, upon execution, only the predicates @tt{p/2}
and @tt{q/3} will be called by @tt{bagof}, i.e., @tt{X} will
only be bound to terms with functors @tt{p/2} and @tt{q/3}.
Moreover, such terms will have all of their arguments constrained to
definite values. This information should be given to the preprocessor
using the declarations:
@begin{verbatim}
:- entry p(def,def).
:- entry q(def,def,def).
@end{verbatim}

Assume you have a graphics library predicate
@tt{menu\_create/5} which creates a graphic menu. The call must
specify, among other things, the name of the menu, the menu items, and
the menu handler, i.e., a predicate which 
should be called upon the selection of a menu item.
The predicate is used as:
@begin{verbatim}
top :- ..., menu_create(Menu,0,Items,Callback,[]), ...
@end{verbatim}
but the program is coded so that there are only two menu handlers:
@tt{app\_menu/2} and @tt{edit\_menu/2}. The first one handles menu
items of the type @tt{app\_item} and the second one items of the
type @tt{edit\_item}. This should be declared with:
@begin{verbatim}
:- entry app_menu(gnd,app_item).
:- entry edit_menu(gnd,edit_item).
@end{verbatim}

Let a program have a dynamic predicate @tt{dyn\_calls/1} to which the
program asserts clauses, such that these clauses do only have in their
bodies calls to predicates @tt{p/2} and @tt{q/3}. This should be
declared with:
@begin{verbatim}
:- entry p/2.
:- entry q/3.
@end{verbatim}
Moreover, if the programmer knows that every call to
@tt{dyn\_calls/1} which can appear in the program is such that upon
its execution the calls to @tt{p/2} and @tt{q/3} have all of their
arguments constrained to definite values, then the two entry
declarations at the beginning of the examples may be used.

@section{An overview}

To process programs with the Ciao Program Precompiler
the following guidelines might be useful:
@begin{enumerate}
@item Add 
@begin{verbatim}
:- use_package(assertions).
@end{verbatim}
 to your program.
@item Declare your specification of the program using calls, success,
  comp, or pred assertions.
@item Use entry declarations to declare all entry points to your
  program.
@item The preprocessor will notify you during the session of
  certain program points where a meta-call appears that may call
  unknown (at compile-time) predicates.

  Add entry declarations for all the predicates that may be
  dynamically called at such program points.
@item Use data or dynamic declarations to declare all predicates that
  may be dynamically modified. 
@item Add entry declarations for the dynamic calls that may occur from
  the code that the program may dynamically assert.
@item Optionally, you can interact with the preprocessor using trust
  assertions. 

  For example, the preprocessor will notify you during the session of
  certain program points where a call appears to an
  unknown (at compile-time) predicate.

  Add trust declarations for such predicates.
@end{enumerate}

").

