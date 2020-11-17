:- module(_, [app/3], [assertions]).

:- entry app(A,B,C) : (list(A), list(B)).
:- pred app(A,B,C) : (list(A), list(B)) => list(C).
app([],Y,Y).
app([X|Xs], Ys, [X|Zs]) :-
    app(Xs,Ys,Zs).
