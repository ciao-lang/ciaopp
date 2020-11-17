:- module(app, [app/3], [assertions]).

:- entry app(A,B,C) : (list(A), list(B)).
app([],Y,Y).
app([X|Xs], Ys, [X|Zs]) :-
    app(Xs,Ys,Zs).
