:- module(_,[],[hiord]).

% expected an automatic entry for q/1

:- export(main/0).
main :-
    X = (A = 2),
    local_pred1(X, _).

:- meta_predicate local_pred1(pred(1), ?).
local_pred1(X,A) :-
    call(X,A).

p(1,2).
bar([],[0]).

q(_).
