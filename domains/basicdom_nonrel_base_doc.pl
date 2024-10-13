%# begin-nonrel
%! # Name your domain
%
%  This file presents the basic predicates that have be implemented in
%  order to define a non-relational abstract domain in CiaoPP.  When
%  defining each operation, fill the gaps indicated in the
%  @tt{throw(implement(P/N)))} bodies.  Each predicate presents a
%  brief description of it behaviour, its modes and whether it can
%  fail or not.  Moreover, to define this operation the following
%  auxiliar predicates are provided:
%
%   - replace_value(+ASub, +Var, +Value, -NewASub) replaces the value
%     of @var{Var} in @var{ASub} by @var{Value}.
%
%   - current_value(+ASub, +Var, -Value) succeeds if @var{Value} is
%     the value asociated to the variable @var{Var} in the abstraction
%     @var{ASub}.

%! ## Lattice operations

:- export(less_or_equal_el/2).
:- pred less_or_equal_el(+Elem1, +Elem2)
   # "Succeeds if element @var{Elem1} is lower or equal than
      @var{Elem2} with the order relation of the lattice.".
less_or_equal_el(_, _) :-
    throw(implement(less_or_equal_el/2)).

:- export(lub_el/3). 
:- pred lub_el(+El1, +El2, -Lub) + not_fails
   # "Succeeds if @var{Lub} is the least upper bound (or a safe
      over-approximation) of elements @var{El1} and @var{El2}".
lub_el(_,_,_) :-
    throw(implement(lub_el/2)).

:- export(widen_el/3).
:- pred widen_el(+El1, +El2, -Widen) + not_fails
   # "Succeeds if @var{Widen} is the result of applying the widen
      operator (or a safe over-approximation) to the elements
      @var{El1} and @var{El2}. By defect, @tt{lub_el} is used.".
widen_el(El1, El2, Widen) :-
    % (modify this if needed)
    lub_el(El1, El2, Widen). 

:- export(glb_el/3).
:- pred glb_el(+El1, +El2, -Glb) + not_fails
   # "Succeeds if @var{Glb} is the greatest lower bound of elements
      @var{El1} and @var{El2}".
glb_el(_,_,_) :-
    throw(implement(glb_el/3)).

%! ## Abstraction operations

:- export(abstract_term/3).
:- pred abstract_term(Term, +ASub, -AbsTerm) + not_fails
   # "Succeeds if @var{AbsTerm} is the result of abstracting the
      concrete value @var{Term}, provided the current abstract state
      @var{ASub}.".
%  % (required default case)
% abstract_term(X, ASub, Value) :-
%     var(X), !, current_value(ASub, X, Value). 
abstract_term(_, _, _) :-
    throw(implement(abstract_term/3)).
% abstract_term(_, _, '$top'). % (required default case)

%# end-nonrel
