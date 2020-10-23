:- module(_,[],[hiord]).

% expected an automatic entry for everything (including local_goal/2!)

:- export(main/0).
main :-
    X = (A = 2),
    local_goal(X, _).

:- meta_predicate local_goal(goal, ?).
local_goal(X,1) :-
    call(X).

p(1,2).
bar([],[0]).

q(_).

