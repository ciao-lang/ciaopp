:- module(_,[],[hiord]).

% expected an automatic entry for p(1,_).

:- export(main/0).
main :-
    local_goal(p(1,_), _).

:- meta_predicate local_goal(goal, ?).
local_goal(X,1) :-
    call(X).

p(1,2).
bar([],[0]).

q(_).

