:- module(_, [], [assertions, regtypes, nativeprops, modes]).

:- doc(title, "Implementing a simple (non relational-)Abstract Domain in CiaoPP").

:- doc(module, "

In this tutorial we show how a (non relational-)Abstract Domain is
implemented in CiaoPP. Since these domains are usually simpler, less
operations are usually needed and their implementation in closer to
their mathematical definition.

All the non-relation abstract domains generated with this interface
are assumed to be @tt{'$bottom'} or a list of elements of the form
@var{X/Val} where @var{X} is a program variable and @var{Val} an
abstract value. In the later case, all the variables in the program
appear in the abstraction.

As running example we will use the @em{Sign} abstract domain, it abstracts
whether a variable is:

@begin{itemize}
@item a negative number (that we represent with the abstract value '-'), or
@item a non-negative number (represented by 'nng'), or 
@item a positive number (represented by '+'), or 
@item zero (represented by 0).
@end{itemize}

@section{Lattice definition and lattice operations}

First we need to define our lattice. The lattice structure is given by its
the order relation, in our case the Sign lattice is the following:

@begin{verbatim}
               T
               |
              / \\
             /   \\
            /     \\
        non-neg    \\
         /  \\      |
        /    \\     |
       +     0     -
        \\    |    /
         \\   |   /
          \\  |  /
           \\ | /
             ⊥
@end{verbatim}

where T denotes the top-most element ('$top') and B the bottom-most
element ('$bot').  Now, we have to define the following predicates:

@subsubsection{@var{less_or_equal_el(+Elem1, +Elem2)}} 

The predicate @tt{less_or_equal_el/2} implements the order relation of
the lattice. It has to receive two lattice elements and can fail.

In this case, given two elements of the lattice @math{X,Y}, @math{X @leq Y} iff: 
@begin{itemize}
@item @math{X} and @math{Y} are the same element, or
@item @math{Y} is non-negative and @math{X} is positive or zero, or
@item @math{Y} is the topmost element, or
@item @math{X} is the bottom element
@end{itemize}

The following predicate captures this behaviour

```ciao
less_or_equal_el(X, X).
less_or_equal_el(+, nng).
less_or_equal_el(0, nng).
less_or_equal_el(_, '$top').
less_or_equal_el('$bot', _).
```
@subsubsection{@var{lub_el(+Elem1, +Elem2, -Lub)}} 

The predicate @tt{lub_el/3} captures, given two elements of the
lattice, their @em{least upper bound}. This predicate receives two
elements and should succeed providing a third element which is the
least upper bound of those elements or an over-approximation.

By inspecting the lattice, we can define the predicate:

```ciao
lub_el(X, X, X) :- !.
lub_el(+, 0, nng) :- !.
lub_el(0, +, nng) :- !.
lub_el(nng, +, nng) :- !.
lub_el(nng, 0, nng) :- !. 
lub_el(+, nng, nng) :- !.
lub_el(0, nng, nng) :- !.
lub_el('$bot', X, X) :- !.
lub_el(X, '$bot', X) :- !.
lub_el(_, _, '$top') :- !.
```
@subsubsection{@var{glb_el(+Elem1, +Elem2, -Glb)}} 

In a similar fashion, we have to define the predicate @tt{glb_el/3}
capturing the @em{greatest lower bound} of two elements of the
lattice. Notice that the greatest lower bound will allow us to define
the abstract more general unifier of two elements of the lattice.

```ciao
glb_el(X, X, X) :- !.
glb_el('$top', X, X) :- !.
glb_el(X, '$top', X) :- !.
glb_el(nng, +, +) :- !.
glb_el(nng, 0, 0) :- !.
glb_el(+, nng, +) :- !.
glb_el(0, nng, 0) :- !.
glb_el(_, _, '$bot') :- !.
```


@subsubsection{@var{widen_el(+Elem1, +Elem2, -Widen)}} 

Finally, is common to define a widen operator to accelerate the
convergence of the fixpoint. In this case, we can simply use the least upper
bound.

```ciao
widen_el(El1, El2, Widen) :- lub_el(El1, El2, Widen). 
```

@section{Abstraction operations}

Now that we have described the lattice and its operations, we need to
define the operations required to abstract the concrete elements. 


@subsubsection{@var{abstract_term(+Term, +Call, -AbsTerm)}}

The predicate @tt{abstract_term/3} is the closest to the abstract
function @math{@alpha}. In our example, such a function would be
defined as follows:

@begin{itemize}
@item a(0) = 0
@item a(X) = + if X > 0
@item a(X) = - if X < 0
@item a(X+Y) = a(X) a(+) a(Y)
@end{itemize}

where the abstract version of the addition (a(+)) is given by the
table:

@begin{verbatim}
|------+-----+-----+-----+-----+-----+-----|
| a(+) | top | nng |  +  |  0  |  -  | bot |
|------+-----+-----+-----+-----+-----+-----|
| top  | top | top | top | top | top | bot |
| nng  | top | nng |  +  | nng | top | bot |
|  +   | top |  +  |  +  |  +  | top | bot |
|  0   | top | nng |  +  |  0  |  -  | bot |
|  -   | top | top | top |  -  |  -  | bot |
| bot  | bot | bot | bot | bot | bot | bot |
|------+-----+-----+-----+-----+-----+-----|
@end{verbatim}

The implementation of the predicate @tt{abstract_term/3} is in fact
very similar as the mathematical definition. If the term is a variable
we invoke the @tt{current_value/3} predicate and get the abstract
value stored in the abstraction for that variable.  If the term is a
number we just check whether is positive, negative, or zero. Finally,
for the case of it being an arithmetical expression we define the
auxiliary predicate @tt{abs_op/4} which computes the table shown above
(and also the corresponding tables for the subtraction and the
product.

```ciao
abstract_term(X, ASub, Value) :-
    var(X), !, current_value(ASub, X, Value). 
abstract_term(0, _, 0).
abstract_term(N, _, Abs) :-
    number(N), !,
    (N > 0 -> Abs = +
    ;
        Abs = -).
abstract_term(+(X, Y), ASub, AbsTerm) :-
    abstract_term(X, ASub, AbsVX),
    abstract_term(Y, ASub, AbsVY), 
    abs_op(+, AbsVX, AbsVY, AbsTerm).
abstract_term(-(X, Y), ASub, AbsTerm) :-
    abstract_term(X, ASub, AbsVX),
    abstract_term(Y, ASub, AbsVY), 
    abs_op(-, AbsVX, AbsVY, AbsTerm).
abstract_term(*(X, Y), ASub, AbsTerm) :-
    abstract_term(X, ASub, AbsVX),
    abstract_term(Y, ASub, AbsVY), 
    abs_op(*, AbsVX, AbsVY, AbsTerm).
abstract_term(_, _, '$top').

abs_op(_, '$bot', _, X) :- !, X = '$bot'.
abs_op(_, _, '$bot', X) :- !, X = '$bot'.
abs_op(_, '$top', _, X) :- !, X = '$top'.
abs_op(_, _, '$top', X) :- !, X = '$top'.
%
abs_op(+, nng,  nng   ,X) :- !, X = nng.
abs_op(+, nng,  +     ,X) :- !, X = + .
abs_op(+, nng,  0     ,X) :- !, X = nng.
abs_op(+, nng,  -     ,X) :- !, X = '$top'.
%
abs_op(+,  + ,  nng   ,X) :- !, X = + .
abs_op(+,  + ,   +    ,X) :- !, X = + .
abs_op(+,  + ,   0    ,X) :- !, X = + .
abs_op(+,  + ,   -    ,X) :- !, X = '$top'.
%
abs_op(+,  0 ,  nng   ,X) :- !, X = nng.
abs_op(+,  0 ,   +    ,X) :- !, X = + .
abs_op(+,  0 ,   0    ,X) :- !, X = 0.
abs_op(+,  0 ,   -    ,X) :- !, X = - .
%
abs_op(+,  - ,  nng   ,X) :- !, X = '$top'.
abs_op(+,  - ,   +    ,X) :- !, X = '$top'.
abs_op(+,  - ,   0    ,X) :- !, X = - .
abs_op(+,  - ,   -    ,X) :- !, X = - .
%
abs_op(*, nng, nng, X) :- !, X = nng.
abs_op(*, nng, +,   X) :- !, X = nng.
abs_op(*, nng, 0,   X) :- !, X = 0.
%
abs_op(*, +, nng, X) :- !, X = nng.
abs_op(*, +, +,   X) :- !, X = + .
abs_op(*, +, 0,   X) :- !, X = 0.
abs_op(*, +, -,   X) :- !, X = - .
%
abs_op(*, 0, nng, X) :- !, X = 0.
abs_op(*, 0, -,   X) :- !, X = 0.
abs_op(*, 0, +,   X) :- !, X = 0.
abs_op(*, 0, 0,   X) :- !, X = 0.
%
abs_op(*, -, 0, X) :- !, X = 0.
abs_op(*, -, -, X) :- !, X = + .
abs_op(*, -, +, X) :- !, X = - .
%
abs_op(-, -, +, X) :- !, X = - .
abs_op(-, -, 0, X) :- !, X = - .
abs_op(-, 0, -, X) :- !, X = + .
abs_op(-, +, -, X) :- !, X = + .
%
abs_op(_, _, _, X) :- !, X = '$top'.
```

The previous defined predicate will allow the framework to abstract
the unification. However, in many cases programs do not only contain
unifications. In this case, for example, we may want to abstract
arithmetical expressions. The following predicates,
@tt{known_builtin/1} and @tt{abstract_literal/4}, are defined for this task.

@subsubsection{@var{known_builtin(+Sg_key)}}

This flag allow the analyzer to know with literals our domain can
abstract. By default, the analyzer will consider that is analyzing a
pure program, i.e., only unifications and predicate calls are present.
However, we may want to predefine the abstraction for some known
predicates or, as in this case, capture arithmetical expressions. To
do so, we include the 'is/2' key as a known_builtin. 

```ciao
known_builtin('is/2') :- !.
```
@subsubsection{@var{abstract_literal(+Key, +Lit, +Call, -Succ)}}

Now that we have added the special literals that we want our domain to
abstract we need to define @em{how} to abstract them. To this end we
use the @tt{abstract_literal/4} literal. This literal receives the
@var{Key} of the literal as provided to the @tt{known_builtin/1}
predicate, the literal that we aim to abstract, @var{Lit}, and the
current abstract state, @var{Call} and returns an updated abstraction.
Notice that, in this case, is possible that some literals change the
abstract value of multiple variables or even send the full abstraction
to bottom if an error is detected.


```ciao
abstract_literal('is/2', is(X, Y), Call, Succ) :-
    abstract_term(X, Call, ValX),
    abstract_term(Y, Call, ValY),
    glb_el(ValX, ValY, Glb),
    replace_value(Call, X, Glb, Succ).
```

However, if in a program appears something like @tt{X > 0} we may want
out domain to abstract @tt{X} to '+', or to raise an error if @tt{X}
is already abstracted to other value.  Thus, we can extend our domain
by adding also descriptions to manage other builtin.

```ciao
known_builtin('>/2') :- !.
known_builtin('</2') :- !.
known_builtin('>=/2') :- !.
known_builtin('=</2') :- !.

abstract_literal('=</2', =<(X, Y), Call, Succ) :-
    abstract_term(Y, Call, ValY), 
    abstract_term(X, Call, ValX), 
    abstract_order_rel(ValX, ValY, X, Y, '=</2', Call, Succ).
abstract_literal('</2', <(X, Y), Call, Succ) :-
    abstract_term(Y, Call, ValY), 
    abstract_term(X, Call, ValX), 
    abstract_order_rel(ValX, ValY, X, Y, '</2', Call, Succ).
abstract_literal('>/2', >(X, Y), Call, Succ) :-
    abstract_literal('</2', <(Y,X), Call, Succ).
abstract_literal('>=/2', >=(X, Y), Call, Succ) :-
    abstract_literal('=</2', =<(Y,X), Call, Succ).

abstract_order_rel('$top','$top',_,_,_,Call, Succ):-
    !, Succ = Call.
abstract_order_rel(ValX, ValY, _X, _Y, Ord, Call, Succ) :-
    ValX \= '$top',
    ValY \= '$top', !,
    (check_order_rel(Ord, ValX, ValY) -> Succ = Call
    ;
        Succ  = '$bottom').
abstract_order_rel(ValX,ValY,_X,Y,Ord,Call,Succ) :- 
    ValX \= '$top',
    ValY = '$top',!,
    plain_ord(Ord,POrd), 
    abstract_from_order_lft(POrd, ValX, NValY), % I known left_val
    replace_value(Call, Y, NValY, Succ).
abstract_order_rel(ValX,ValY,X,_Y,Ord,Call,Succ) :- 
    ValX = '$top',
    ValY \= '$top',!,
    plain_ord(Ord, POrd), 
    abstract_from_order_rgt(POrd, ValY, NValX), % I known right_val
    replace_value(Call, X, NValX, Succ).

plain_ord('=</2', '</2').
plain_ord('>=/2', '>/2').
plain_ord(X, X).

abstract_from_order_lft('</2', 0, +) :- !.
abstract_from_order_lft('</2', +, +) :- !.
abstract_from_order_lft('</2', _, '$top') :- !.
abstract_from_order_lft('>/2', 0, -) :- !.
abstract_from_order_lft('>/2', -, -) :- !.
abstract_from_order_lft('>/2', _, '$top') :- !.

abstract_from_order_rgt('</2', 0, -) :- !.
abstract_from_order_rgt('</2', -, -) :- !.
abstract_from_order_rgt('</2', _, '$top') :- !.
abstract_from_order_rgt('>/2', 0, +) :- !.
abstract_from_order_rgt('>/2', +, +) :- !.
abstract_from_order_rgt('>/2', _, '$top') :- !.

check_order_rel('</2', 0, +).
check_order_rel('</2', -, +).
check_order_rel('</2', -, 0).
check_order_rel('</2', -, nng).
check_order_rel('>/2', X,Y) :- check_order_rel('</2', Y,X).
check_order_rel('=</2',X,Y) :- check_order_rel('</2', X,Y).
check_order_rel('>=/2',X,Y) :- check_order_rel('>/2', X,Y).
```

@section{Other Auxiliary Predicates and Input-Output Operations}

Finally, a number of extra predicates can be defined. Among those, the
following are predefined but may need to be redefined.

@subsubsection{@var{needs(+Option)}}

Succeeds if the domains needs and operation @var{Op} for termination
or correctness. The supported operations are: 

@begin{enumerate}
@item @tt{widen} : whether widening is necessary for termination,
@item @tt{clauses_lub} : whether the lub must be performed over the
      abstract substitution split by clase,
@item @tt{aux_info} :whether the information in the abstract
      substitutions is not complete and an external solver may be
      needed,currently only used when outputting the analysis in a
      @tt{.dump} file.
@end{enumerate} 
by default it is assumed that nothing is needed.

@subsubsection{@var{asub_to_native(+ASub,+Qv,+OutFlag,-NativeStat,-NativeComp}}

@var{NativeStat} and @var{NativeComp} are the list of native (state
and computational, resp.) properties that are the concretization of
abstract substitution @var{ASub} on variables @var{Qv} for the
domain. These are later translated to the properties which are visible
in the preprocessing unit.

@subsubsection{@var{input_interface(+Prop, +Kind, ?Struct0, -Struct1)}}
    @var{Prop} is a native property that is relevant to domain
      (i.e., the domain knows how to fully --@var{+Kind}=perfect-- or
      approximately --@var{-Kind}=approx-- abstract it) and
      @var{Struct1} is a (domain defined) structure resulting of
      adding the (domain dependent) information conveyed by @var{Prop}
      to structure @var{Struct0}. This way, the properties relevant to
      a domain are being accumulated.

@subsubsection{@var{input_user_interface(+Struct, +Qv, -ASub, +Sg, ?MaybeCallASub)}}
    @var{ASub} is the abstraction of the information collected in
     @var{Struct} (a domain defined structure) on variables
     @var{Qv}.


These predicates are predefined as follows:

```ciao
needs(_) :- fail. %% Assume nothing is needed

asub_to_native(ASub, _, _, [ASub], []). %% Output the internal representation

input_interface(_Prop, _Kind, _Struct0, _Struct1) :- fail. 

input_user_interface(Struct, Qv, ASub, _, _) :- topmost(Qv, Struct, ASub).

```
").






