:- module(_, [nrev/2], [assertions]).

:- use_module(library(assertions/native_props)).

:- pred nrev(A,B) : (ground(A), list(A), var(B)).
:- check comp nrev(A,B) + steps_o(exp(length(A),2)).

nrev([],[]).
nrev([H|L],R) :-
    nrev(L,R1),
    append(R1,[H],R).

append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]):- append(Xs,Ys,Zs).


