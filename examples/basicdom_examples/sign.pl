:- module(_, [], [assertions, regtypes, nativeprops, modes]).
:- include(dominterf(basicdom_nonrel_base)).
:- dom_def(_, [default]).

%! \title Simple Sign Domain

%! ## Lattice operations

:- export(less_or_equal_el/2).
:- pred less_or_equal_el(+Elem1, +Elem2)
   # "Succeeds if element @var{Elem1} is lower or equal than
      @var{Elem2} with the order relation of the lattice.".
%:- impl_defined(less_or_equal_el/2).
less_or_equal_el(X, X) :- !.
less_or_equal_el(+, nng) :- !.
less_or_equal_el(0, nng) :- !.
less_or_equal_el(_, '$top'):- !.
less_or_equal_el('$bot', _) :- !.

:- export(lub_el/3). 
:- pred lub_el(+El1, +El2, -Lub) + not_fails
   # "Succeeds if @var{Lub} is the least upper bound (or a safe
      over-approximation) of elements @var{El1} and @var{El2}".
%:- impl_defined(lub_el/3). 
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

:- export(widen_el/3).
:- pred widen_el(+El1, +El2, -Widen) + not_fails
   # "Succeeds if @var{Widen} is the result of applying the widen
      operator (or a safe over-approximation) to the elements
      @var{El1} and @var{El2}. By defect, @tt{lub_el} is used.".
widen_el(El1, El2, Widen) :- lub_el(El1, El2, Widen). 

:- export(glb_el/3).
:- pred glb_el(+El1, +El2, -Glb) + not_fails
   # "Succeeds if @var{Glb} is the greatest lower bound of elements
      @var{El1} and @var{El2}".
%:- impl_defined(glb_el/3).
glb_el(X, X, X) :- !.
glb_el('$top', X, X) :- !.
glb_el(X, '$top', X) :- !.
glb_el(nng, +, +) :- !.
glb_el(nng, 0, 0) :- !.
glb_el(+, nng, +) :- !.
glb_el(0, nng, 0) :- !.
glb_el(_, _, '$bot') :- !.

:- doc(subtitle, "Abstraction operations").

:- export(abstract_term/3).
:- pred abstract_term(Term, +ASub, -AbsTerm) + not_fails
   # "Succeeds if @var{AbsTerm} is the result of abstracting the
      concrete value @var{Term}, provided the current abstract state
      @var{ASub}.".
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


%%% Auxiliary
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

:- export(known_builtin/1).
:- pred known_builtin(+Sg_key) 
   # "Succeeds if the domain can abstract @var{Sg_key}. For example,
      if the domain can abstract arithmetical operations
      @tt{known_builtin('is/2')} should succeed.".
known_builtin('is/2') :- !.
known_builtin('>/2') :- !.
known_builtin('</2') :- !.
known_builtin('>=/2') :- !.
known_builtin('=</2') :- !.

%:- impl_defined(known_builtin/1).

:- export(abstract_literal/4).
:- pred abstract_literal(+Sg_key, +Sg, +Call, -Succ) : (asub(Call), asub(Succ)) 
   # "@var{Succ} is the @em{abstraction} that results from abstracting
      the literal @var{Literal} provided the information in
      abstraction @var{Call}. If the domain does not know how to
      abstract such literal, the predicate has to fail.".

abstract_literal('is/2', is(X, Y), Call, Succ) :-
    abstract_term(X, Call, ValX),
    abstract_term(Y, Call, ValY),
    glb_el(ValX, ValY, Glb),
    replace_value(Call, X, Glb, Succ).
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
    ( check_order_rel(Ord, ValX, ValY) -> Succ = Call
    ; Succ  = '$bottom'
    ).
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
