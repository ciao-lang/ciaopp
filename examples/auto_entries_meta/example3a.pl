:- module(_,[],[hiord]).

% expected an automatic entry for p/2, bar/2, and local_pred2/2

:- export(main/0).
main :-
    X = (A = 2),
    local_pred2(bar, _).

:- meta_predicate local_pred2(pred(2), ?).
local_pred2(X,A) :-
    call(X,A,2).

p(1,2).
bar([],[0]).

q(_).

