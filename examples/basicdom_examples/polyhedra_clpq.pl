:- module(_, [], [assertions, regtypes, nativeprops, modes]).
:- include(dominterf(basicdom_base)).
:- dom_def(_, [default]).
:- doc(section, " Operations over the Abstract Substitutions").


:- doc(module, "
   This file implements a Polyhedra Abstract Domain using the library @tt{poly_clpq}.
   That library implements a convex hull and projection based on the paper:

   @begin{verbatim}
   \"Computing convex hulls with a linear solver\", Florence Benoy,
   Andy King, Frédéric Mesnard.  TPLP 5(1-2): 259-271 (2005).
   @end{verbatim}
 
@section{Overview}       


The library we are going to use is guaranteed to work for closed
polyhedra (i.e. only non-strict inequalities are allowed).

Our abstraction is a pair @tt{(Constr, Vs)} where @tt{Constr} is a
list of (close)-constraints and @tt{Vs} a list containing the
variables over which the polyhedron is defined. Notice that, @tt{([],
[X, Y])} denotes the top-most polyhedron defined over @tt{X} and @tt{Y}

").
:- use_module(library(poly_clpq), [project/3, simplify/2, contains/2, convhull/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sets), [ord_subset/2, ord_intersection/3, ord_union/3]).
:- use_module(library(sort), [sort/2]).
              
:- export(asub/1).
:- regtype asub(L)
  # "This regular type defines that @var{L} is an abstraction.
     ".
asub('$bottom') :- !.
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
%:- impl_defined(asub/1).

:- export(project/3).
:- push_prolog_flag(multi_arity_warnings, off).
:- pred project(+Vs, +L, -Prj) : (asub(L), asub(Prj)) + not_fails
  # "Succeeds if @var{Prj} is an abstraction containing all the
     information in @var{L} restricted to the variables in @var{Vs}".
project(_, '$bottom', '$bottom').
project(Vs, (Ctrs, CVs), Proj) :-
    ord_intersection(Vs, CVs, Vs_pr),
    poly_clpq:project(Vs_pr, Ctrs, Ctr_pr),
    simplify_poly((Ctr_pr, Vs_pr), Proj).
%:- impl_defined(project/3).
:- pop_prolog_flag(multi_arity_warnings).

:- export(augment/3).
:- pred augment(+Vars, +L1, -L2) : (asub(L1), asub(L2)) + not_fails
   # "Succeeds if @var{L2}, is the result of adding to the abstraction
      @var{L1} the top information about the set of free variables
      @var{Vars}.

      - Notice that @var{Vars} and dom(L1) are disjoint sets.
      - Also notice that the elements in @var{Vars} are @emph{free}
        variables.".
%:- impl_defined(augment/3).
augment(_Vars, Poly, Poly) :- !.  %% They are free fresh vars so they are not in the polyhedron (yet)

:- push_prolog_flag(multi_arity_warnings, off).   
:- export(extend/4).
:- pred extend(+Sv, +Prime, +Call, -Succ) : (asub(Prime), asub(Call), asub(Succ)) + not_fails 
   # "@var{Succ} is the result of updating @var{Call} with the
      information in @var{Prime}. @var{Prime} is defined over @var{Sv}
      and @var{Sv} is a subset of the domain of @var{Call}. @var{Call}
      and @var{Succ} have the same domain.".
%:- impl_defined(extend/4).
extend(_Sv,'$bottom',_Call,'$bottom').
extend(_Sv, Prime, Call,Success):-
    Prime = (Poly_pr, Vars_pr),
    Call  = (Poly_cl, Vars_cl),
    ord_union(Poly_pr, Poly_cl, Poly_mr), %% Merge Poly
    ord_union(Vars_pr, Vars_cl, Vars_mr), %% Merge Vars
    simplify_poly((Poly_mr, Vars_mr), Success).
:- pop_prolog_flag(multi_arity_warnings).

:- doc(section, "Lattice Operations").

:- export(less_or_equal/2).
:- pred less_or_equal(+L1, +L2) : (asub(L1), asub(L2))
   # "Succeeds if the abstraction @var{L1} is less or equal than
      @var{L2} with the order relation of the lattice.".
less_or_equal('$bottom', _) :- !.
less_or_equal((Poly1, Vars), (Poly2, Vars)) :-
    poly_clpq:contains(Poly2, Poly1), !.


:- export(lub/3).
:- pred lub(+L1, +L2, -LUB) : (asub(L1), asub(Ln2), asub(LUB)) + not_fails
   # "@var{LUB} is the least upper bound of @var{L1} and
      @var{L2} (or a safe approximation). @var{L1} and @var{L2} are
      defined over the same variables.".

lub(ASub1,'$bottom',ASub1):- !.
lub('$bottom',ASub2,ASub2):- !.
lub(ASub1,ASub2,Lub):-
    match_dimensions(ASub1,ASub2,New_ASub1,New_ASub2), 
    New_ASub1 = (Poly1,Vars),
    New_ASub2 = (Poly2,Vars),
    poly_clpq:convhull(Poly1, Poly2, Poly_h),!,
    Lub = (Poly_h,Vars).
lub(_ASub1,_ASub2,'$top').
    
:- export(widen/3).
:- pred widen(+L1, +L2, -WD) : (asub(L1), asub(L2), asub(WD)) + not_fails
   # "@var{WD} is the widen of @var{L1} and @var{L2} (or a
      safe approximation). By default, @tt{lub/3} is used.".
widen(L1, L2, W) :-
    lub(L1, L2, W). 
%% widen(Poly1, Poly2, W) :-
%%     match_dimensions(Poly1, Poly2, Poly1_new, Poly2_new),
%%     Poly1_new = (Ctrs1, Vars),
%%     Poly2_new = (Ctrs2, Vars),
%%     poly_clpq:widen(Ctrs1, Ctrs2, Ctrs_w),
%%     W = (Ctrs_w, Vars).


:- impl_defined(amgu/4).
:- pred amgu(+Var,+Term, +L1, -L2) : (var(Var), term(Term), asub(L1), asub(L2)) + not_fails
   # "Computes the abstract most general unifier of the variable
      @var{Var} with the term @var{Term} with the information
      abstracted in @var{L1}. The domain of @var{L1} contains
      @var{Var} and @tt{vars}(@var{Term}).".
amgu(Var, Term, Poly1, Poly2) :-
    number(Term), !,
    poly_add_constraint(Poly1, Var=Term, Poly2).
amgu(Var, Term, Poly1, Poly2) :-
    var(Term), !,
    poly_add_constraint(Poly1, Var=Term, Poly2).
amgu(_, _, Poly1, Poly1). %% I don't do anything
%%% But I could check if any var in Poly1 bcs that would mean a error!    


:- export(topmost/3).
:- pred topmost(+Vars, +L1, -L2) : (asub(L1), asub(L2)) + not_fails
   # "@var{L2}, is the result of adding to @var{L1} the
      top-most information of the variables in @var{Vars}. Notice that
      @var{Vars} is a subset of @dom(L1). If @var{L1} is not provided,
      then the topmost abstraction for the variables in @var{Vars} is
      generated.".
topmost(_, not_provided, ([],[])).
topmost(_, Poly, Poly) :- !.
%:- impl_defined(topmost/3).


:- export(known_builtin/1).
:- pred known_builtin(+Sg_key) 
   # "Succeeds if the domain can abstract @var{Sg_key}. For example,
      if the domain can abstract arithmetical operations
      @tt{known_builtin('is/2')} should succeed.".
%:- impl_defined(known_builtin/1).
known_builtin('is/2').
known_builtin('>/2').
known_builtin('>=/2').
known_builtin('</2').
known_builtin('=</2').

:- export(abstract_literal/4).

:- pred abstract_literal(+Sg_key, +Sg, +Call, -Succ) : (asub(Call), asub(Succ))
   # "@var{Succ} is the @em{abstraction} that results of abstracting
      the literal @var{Literal} provided the information in the
      abstraction @var{Call}. If the domain does not know how to
      abstract such literal, the predicate has to fail.".
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

%:- impl_defined(abstract_literal/4).

:- doc(section, "Assertions/Input-Output Operations").

:- export(needs/1).
:- pred needs(+Op)
   # "Succeeds if the domains needs and operation @var{Op} for
      termination or correctness. The supported operations are:
      @begin{enumerate} 
      @item @tt{widen} : whether widening is necessary for
            termination,
      @item @tt{clauses_lub} : whether the lub must be performed over
            the abstract substitution split by clase, 
      @item @tt{aux_info} :whether the information in the abstract
            substitutions is not complete and an external solver may
            be needed,currently only used when outputing the analysis
            in a @tt{.dump} file.
      @end{enumerate}
      by defect it is assumed that nothing is needed.".
%needs(_) :- fail.
needs(widen) :- !.

:- export(asub_to_native/5).
:- pred asub_to_native(+ASub,+Qv,+OutFlag,-NativeStat,-NativeComp) + not_fails
   # "@var{NativeStat} and @var{NativeComp} are the list of native
      (state and computational, resp.) properties that are the
      concretization of abstract substitution @var{ASub} on variables
      @var{Qv} for the domain. These are later translated to the
      properties which are visible in the preprocessing unit.".
asub_to_native(ASub, _, _, [ASub], []).

:- export(input_interface/4).
:- pred input_interface(+Prop, +Kind, +Struct0, -Struct1)
   # "@var{Prop} is a native property that is relevant to domain
      (i.e., the domain knows how to fully --@var{+Kind}=perfect-- or
      approximately --@var{-Kind}=approx-- abstract it) and
      @var{Struct1} is a (domain defined) structure resulting of
      adding the (domain dependent) information conveyed by @var{Prop}
      to structure @var{Struct0}. This way, the properties relevant to
      a domain are being accumulated.".
input_interface(_Prop, _Kind, _Struct0, _Struct1) :- fail.

:- export(input_user_interface/5).
:- pred input_user_interface(+Struct, +Qv, -ASub, +Sg, +MaybeCallASub)
   # "@var{ASub} is the abstraction of the information collected in
     @var{Struct} (a domain defined structure) on variables
     @var{Qv}.".
input_user_interface(Struct, Qv, ASub, _, _) :- topmost(Qv, Struct, ASub).



%%% Auxiliary predicates

simplify_poly('$bottom', '$bottom').
simplify_poly(ASub, NASub_s) :-
    abs_sort(ASub, (Poly_s, Vars)),
    simplify(Poly_s, PolyS),
    (
        PolyS == [], Poly_s \== [] 
        -> NASub = '$bottom' %% If the simpl. is empty and it was not
                             %% empty before, then some unconsistent
                             %% constraint was there!
        ;
            NASub = (PolyS, Vars)
        ),
    abs_sort(NASub, NASub_s).

:- use_module(library(lists), [reverse/2]).
simplify(A,B) :-
    reverse(A, A_),
    convhull(A_,A_,B0),!,
    B=B0. 
simplify(_,[]). % convhull fails if empty

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


poly_add_constraint('$bottom', _, '$bottom').
poly_add_constraint((Poly, Vars), Const, NASub) :-
    varset(Const, ConstVars), sort(ConstVars, ConstVars_s),
    Poly_add = [Const|Poly], 
%    merge(Poly, [Const], Poly_add),
    ord_union(Vars, ConstVars_s, Vars_add),
    simplify_poly((Poly_add, Vars_add), NASub).