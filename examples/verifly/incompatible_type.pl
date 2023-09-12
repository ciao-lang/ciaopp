:- module(_,[p/1],[assertions,regtypes,functional,nativeprops]).

:- pred p(X) => sorted(X) + is_det.

p(X) :-
    q(X).

:- pred q(X) => color(X) + is_det.

q(M) :-
    M = red.

:- regtype color/1.
color := red | green | blue.

:- regtype sorted/1.
sorted := [] | [_].
sorted([X,Y|T]) :-  X>=Y, sorted([Y|T]).

