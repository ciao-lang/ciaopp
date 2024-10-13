:- module(_, [], [assertions, regtypes, nativeprops, modes]).

:- doc(title, "Implementing a Polyhedra analysis in CiaoPP").

:- doc(module, "


In this tutorial we show how to implement a relational Abstract Domain
in CiaoPP. We implement a Polyhedra analysis to abstract numerical relations. 

In order to keep this tutorial simple, we will not discuss technical
details about how to represent polyhedra nor how to implement some
complex operations. To ease the development of this domains we use an
already implemented library in the Ciao system: the @tt{poly_clpq} library
which implements a number of operations to manipulate (rational,
closed) polyhedra based on CLP(Q) operations. Concretely we will use
the @tt{project/3}, @tt{convexhull/3}, @tt{simplify/2}, and
@tt{contains/2} predicates. The two first predicates are based on the
paper:

 @begin{verbatim} \"Computing convex hulls with a linear
solver\", Florence Benoy, Andy King, Frédéric Mesnard.  TPLP 5(1-2):
259-271 (2005).  @end{verbatim}

We begin by describing the abstraction and some operations to manipulate it:


@section{Operations over the Abstract Substitution}

Since we aim to abstract a rather complex property a substitution-like
abstraction pairing variables with values would not be very useful. 
Instead of that, we define our abstraction as a pair @tt{(Ctrs, Vars)} such that:
@begin{itemize}
@item @tt{Ctrs} is a set of closed constraints defining a polyhedron and, 
@item @tt{Vars} is the set of variables over which the polyhedron is defined.
@end{itemize}

Notice that all the variables appearing in @tt{Ctrs} must appear in
@tt{Vars}. Moreover, carrying @tt{Vars} we are also inferring a type
property, only numerical variables can be in @tt{Vars}.

Finally, given a polyhedron @tt{([], [X])} we can infer that @tt{X} is
a numerical variable over which nothing else is known.

Now that we have defined how our abstraction looks like we can
implement the first predicate that CiaoPP requires:

@subsubsection{@var{asub(+ASub)}}
The predicate @tt{asub/1} is used to define the regtype @tt{asub/1}. 
In our case is defined as follows:
```ciao

asub('$bottom'):-!.       
asub(([], _)) :- !.
asub((Ctr, Vs)) :-
    varset(Ctr, CtrVs),
    ord_subset(CtrVs, Vs), !,
    valid_ctrs(Ctr).

valid_ctrs([]).
valid_ctrs([>=(_, _)|Cs]) :-
    valid_ctrs(Cs).
valid_ctrs([=(_, _)|Cs]) :-
    valid_ctrs(Cs).
valid_ctrs([=<(_, _)|Cs]) :-
    valid_ctrs(Cs).
```

@subsubsection{@var{project(+Vars, +ASub, -Proj)}}

The predicate @tt{project/3} projects the information captured by
@var{ASub} over the set of variables @tt{Vars}. Luckily, the library
@tt{poly_clpq} already defines a project predicate which keeps the
constraints related with the given set of variables. However, the
obtained polyhedron may not be minimal (and we want to keep the
minimal representation). Because of that, we also invoke the
@tt{simplify_poly/2} predicate which yields a reduced polyhedron.

```ciao
project(_, '$bottom', '$bottom').
project(Vs, (Ctrs, CVs), Proj) :-
    ord_intersection(Vs, CVs, Vs_pr),
    poly_clpq:project(Vs_pr, Ctrs, Ctr_pr),
    simplify_poly((Ctr_pr, Vs_pr), Proj).
```

@subsubsection{@var{augment(+Vars, +ASub, -ASub_aug)}}

The predicate @tt{augment/3} increases the abstraction with the
variables in @var{Vars}. This variables are @em{free, fresh
variables}. Because of that, we know that they are not numerical at
this analysis point. Thus the predicate has to unify @var{ASub} with
@var{ASub_aug}.

```ciao
augment(_Vars, Poly, Poly) :- !.  %% They are free fresh vars so they are not in the polyhedron (yet)
```

@subsubsection{@var{extend(+Sv, +Prime, +Call, -Success)}} 

The @tt{extend/4} operation is used to update the information that
exists at call-time @var{Call} with the inferred information
@var{Prime}. In this case, we can just merge the constraints at
call-time whith the \"prime\" constraints and then simplify the
resulting constraint store.


```ciao
extend(_Sv,'$bottom',_Call,'$bottom').
extend(_Sv, Prime, Call,Success):-
    Prime = (Poly_pr, Vars_pr),
    Call  = (Poly_cl, Vars_cl),
    ord_union(Poly_pr, Poly_cl, Poly_mr), %% Merge Poly
    ord_union(Vars_pr, Vars_cl, Vars_mr), %% Merge Vars
    simplify_poly((Poly_mr, Vars_mr), Success).
```

Now that we have defined the operations required by CiaoPP to operate
over the abstraction, we turn our attention to define the operations
over the lattice:

@section{Operations over the Lattice}

@subsubsection{@var{less_or_equal(+ASub1, +ASub2)}}

The @tt{less_or_equal/2} predicate succeeds if the abstraction
@var{ASub1} is less or equal than @var{ASub2}. In this case we use the
@tt{contains/2} predicate to check whether @var{ASub2} contains
@var{ASub1}.

```ciao

less_or_equal('$bottom', _) :- !.
less_or_equal((Poly1, Vars), (Poly2, Vars)) :-
    poly_clpq:contains(Poly2, Poly1), !.
```

@subsubsection{@var{lub(+ASub1, +ASub2, -Lub)} and @var{widen(+ASub1, +ASub2, -Widen)}}

The predicate @tt{lub/3} is used to compute the @em{least upper bound}
of two abstractions. Thus, given two polyhedrons, their convexhull is
a safe candidate for least upper bound. Before, computing the
convexhull we invoke the predicate @tt{match_dimensions/4} which will
keep both abstractions defined over the variables appearing in both polyhedra.

The predicate @tt{widen/3} is used to acelerate the computation of the fixpoint. Many different widens can be defined for a polyhedra domain. That is outside of the scope of this tutorial, thus we use @tt{lub/3}.

```ciao

lub(ASub1,'$bottom',ASub1):- !.
lub('$bottom',ASub2,ASub2):- !.
lub(ASub1,ASub2,Lub):-
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2), 
    New_ASub1 = (Poly1,Vars),
    New_ASub2 = (Poly2,Vars),
    poly_clpq:convhull(Poly1, Poly2, Poly_h),!,
    Lub = (Poly_h,Vars).
lub(_ASub1,_ASub2,'$top').
    
widen(L1, L2, W) :-
    lub(L1, L2, W).  

match_dimensions(ASub1,ASub2,ASub1,ASub2):-
    ASub1 = (_Poly1,Vars1),
    ASub2 = (_Poly2,Vars2),
    Vars1 == Vars2,!.
match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2):-
    ASub1 = (_Poly1,Vars1),
    ASub2 = (_Poly2,Vars2),
    ord_intersection(Vars1,Vars2,Vars),
    polyhedra_clpq:project(Vars, ASub1,New_ASub1),
    polyhedra_clpq:project(Vars,ASub2,New_ASub2).


```

@section{Abstracting operations} 

Now that we have described the lattice and the abstract representation used, we describe how the elements of the concrete program are abstracted.

@subsubsection{@var{topmost(+Vars, +MaybeCall, -TopAbs)}}

The predicate @tt{topmost/3} is used to compute an abstraction such that nothing is known about the variables in @var{Vars}. We have to consider the case in which @var{MaybeCall} unifies with an atom @tt{not_provided}, that means that a top-most abstraction over the variables in @var{Vars} has to be defined.
```ciao

topmost(_, not_provided, ([],[])).
topmost(_, Poly, Poly) :- !.
```


@subsubsection{@var{amgu(+Var, +Term, +Call, -Succ)}}
The predicate @tt{amgu/4} computes the @em{abstract most general unifier} for the unification @var{Var=Term} given the current abstracted information @var{Call}. Hence, @var{Succ} is the result of update @var{Call} with such an information.
Is important to note that @var{Var} is indeed a variable so cases are only need to be considered about @var{Term}.

For our polyhedra domain, defining @tt{amgu/4} is pretty straightforward:

```ciao
amgu(Var, Term, Poly1, Poly2) :-
    number(Term), !,
    poly_add_constraint(Poly1, Var=Term, Poly2).
amgu(Var, Term, Poly1, Poly2) :-
    var(Term), !,
    poly_add_constraint(Poly1, Var=Term, Poly2).
amgu(_, _, Poly1, Poly1). 


poly_add_constraint('$bottom', _, '$bottom').
poly_add_constraint((Poly, Vars), Const, NASub) :-
    varset(Const, ConstVars), sort(ConstVars, ConstVars_s),
    Poly_add = [Const|Poly], 
    ord_union(Vars, ConstVars_s, Vars_add),
    simplify_poly((Poly_add, Vars_add), NASub).
```

@subsubsection{@var{known_builtin(+Sg_Key)}}

This flag allow the analyzer to know whith literals our domain can
abstract. By default, the analyzer will consider that is analyzing a
pure program, i.e., only unifications and predicate calls are present.
However, we may want to predefine the abstraction for some known
predicates or, as in this case, capture arithmetical expressions.

```ciao

known_builtin('is/2').
known_builtin('>/2').
known_builtin('>=/2').
known_builtin('</2').
known_builtin('=</2').
```

@subsubsection{@var{abstract_literal(+Sg_key, +Sg, +Call, -Succ)}}

Now that we have declared which builtins our domain knows how to
handle we have to describe their abstraction. The predicate
@tt{abstract_literal/4} implements how to abstract a literal
(@var{Sg}) which has a known @var{Sg_key} key.
In our case we can add the new constraints to the polyhedron in @var{Call} and then simplify it to obtain the success abstraction @var{Succ}.

```ciao

abstract_literal('is/2', is(X, Y), Poly_call, Poly_succ) :- 
    %% Once again, we are keeping it simple
    poly_add_constraint(Poly_call, X=Y, Poly_succ).
abstract_literal('>=/2', >=(X, Y), Poly_call, Poly_succ) :-
    poly_add_constraint(Poly_call, >=(X,Y), Poly_succ).
abstract_literal('>/2', >(X, Y), Poly_call, Poly_succ) :-
    abstract_literal('>=/2', '>='(X, Y+1),Poly_call, Poly_succ).
abstract_literal('=</2', =<(X, Y), Poly_call, Poly_succ) :-
    abstract_literal('>=/2', '>='(Y,X),Poly_call, Poly_succ).
abstract_literal('</2', <(X, Y), Poly_call, Poly_succ) :-
    abstract_literal('>/2', '>'(Y,X), Poly_call, Poly_succ).
```

@section{Other Auxiliary Predicates and Input-Output Operations}

Finally, a number of extra predicates can be defined. Among those, the
following are predefined but may need to be redefined.

@subsubsection{@var{needs(+Option)}}

Succeeds if the domains needs an operation @var{+Option} for termination
or correctness. The supported operations are: 

@begin{enumerate}
@item @tt{widen} : whether widening is necessary for termination,
@item @tt{clauses_lub} : whether the lub must be performed over the
      abstract substitution split by clase,
@item @tt{aux_info} :whether the information in the abstract
      substitutions is not complete and an external solver may be
      needed,currently only used when outputing the analysis in a
      @tt{.dump} file.
@end{enumerate} 
by default it is assumed that nothing is needed. However, we will set widen as needed in this case.

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

```ciao
needs(widen) :- !.

asub_to_native(ASub, _, _, [ASub], []).

input_interface(_Prop, _Kind, _Struct0, _Struct1) :- fail.

input_user_interface(Struct, Qv, ASub, _, _) :- topmost(Qv, Struct, ASub).
```
").