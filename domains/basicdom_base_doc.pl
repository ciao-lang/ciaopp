%# begin-rel
%! # Name your domain
%
%  This file presents the basic predicates that have be implemented in
%  order to define a non-relational abstract domain in CiaoPP.  When
%  defining each operation, fill the gaps indicated in the
%  @tt{throw(implement(P/N)))} bodies.

%! ## Operations over the Abstract Substitutions.

:- export(asub/1).
:- regtype asub(L)
   # "This regular type defines that @var{L} is an abstraction.".
asub(_) :-
    throw(asub/1).

:- export(project/3).
:- pred project(+Vs, +L, -Prj) : (asub(L), asub(Prj)) + not_fails
  # "Succeeds if @var{Prj} is an abstraction containing all the
     information in @var{L} restricted to the variables in @var{Vs}"
project(_,_,_) :-
    throw(project/3).

:- export(augment/3).
:- pred augment(+Vars, +L1, -L2) : (asub(L1), asub(L2)) + not_fails
   # "Succeeds if @var{L2}, is the result of adding to the abstraction
      @var{L1} the top information about the set of free variables
      @var{Vars}.

      - Notice that @var{Vars} and dom(L1) are disjoint sets.
      - Also notice that the elements in @var{Vars} are @emph{free}
        variables.".
augment(_, _, _) :-
    throw(augment/3).

:- export(extend/4).
:- pred extend(+Sv, +Prime, +Call, -Succ) : (asub(Prime), asub(Call), asub(Succ)) + not_fails 
   # "@var{Succ} is the result of updating @var{Call} with the
      information in @var{Prime}. @var{Prime} is defined over @var{Sv}
      and @var{Sv} is a subset of the domain of @var{Call}. @var{Call}
      and @var{Succ} have the same domain.".
extend(_, _, _, _) :-
    throw(extend/4).

%! ## Lattice Operations

:- export(less_or_equal/2).
:- pred less_or_equal(+L1, +L2) : (asub(L1), asub(L2))
   # "Succeeds if the abstraction @var{L1} is lower or equal than
      @var{L2} with the order relation of the lattice.".
less_or_equal(_, _) :-
    throw(less_or_equal/2).
    
:- export(lub/3).
:- pred lub(+L1, +L2, -LUB) : (asub(L1), asub(Ln2), asub(LUB)) + not_fails
   # "@var{LUB} is the least upper bound of @var{L1} and
      @var{L2} (or a safe approximation). @var{L1} and @var{L2} are
      defined over the same variables.".
lub(_,_,_) :-
    throw(lub/3).

:- export(widen/3).
:- pred widen(+L1, +L2, -WD) : (asub(L1), asub(L2), asub(WD)) + not_fails
   # "@var{WD} is the widen of @var{L1} and @var{L2} (or a
      safe approximation). By default, @tt{lub/3} is used.".
widen(L1, L2, W) :- lub(L1, L2, W). 

:- impl_defined(amgu/4).
:- pred amgu(+Var,+Term, +L1, -L2) : (var(Var), term(Term), asub(L1), asub(L2)) + not_fails
   # "Computes the abstract most general unifier of the variable
      @var{Var} with the term @var{Term} with the information
      abstracted in @var{L1}. The domain of @var{L1} contains
      @var{Var} and @tt{vars}(@var{Term}).".
amgu(_,_,_,_) :-
    throw(amgu/4).

:- export(topmost/3).
:- pred topmost(+Vars, +L1, -L2) : (asub(L1), asub(L2)) + not_fails
   # "@var{L2}, is the result of adding to @var{L1} the
      top-most information of the variables in @var{Vars}. Notice that
      @var{Vars} is a subset of @dom(L1). If @var{L1} is not provided,
      then the topmost abstraction for the variables in @var{Vars} is
      generated.".
topmost(_,_,_) :-
    throw(topmost/3).
%# end-rel

%# begin-common
:- export(known_builtin/1).
:- pred known_builtin(+Sg_key) 
   # "Succeeds if the domain can abstract @var{Sg_key}. For example,
      if the domain can abstract arithmetical operations
      @tt{known_builtin('is/2')} should succeed.".
know_builtin(_) :-
    throw(known_builtin/1).

:- export(abstract_literal/4).
:- pred abstract_literal(+Sg_key, +Sg, +Call, -Succ) : (asub(Call), asub(Succ))
   # "@var{Succ} is the @em{abstraction} that results of abstracting
      the literal @var{Literal} provided the information in the
      abstraction @var{Call}. If the domain does not know how to
      abstract such literal, the predicate has to fail.".
abstract_literal(_,_,_,_) :-
    throw(abstract_literal/4).

%! ## Assertions/Input-Output Operations

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
needs(_) :- fail.

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
%# end-common
