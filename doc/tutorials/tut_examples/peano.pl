:- module(_,[main/2],[assertions, regtypes]).
:- entry main(N, R) : (gt_two_nat(N), var(R) ).
:- regtype gt_two_nat/1.
gt_two_nat(s(s(s(N)))):- nat(N).

:- regtype nat/1.
nat(0).
nat(s(N)) :- nat(N).

main(In,Out):-
    formula(In,Tmp),
    formula(Tmp,Out),
    nonvar(Out).

formula(X,W):-
    ground(X),
    var(W),
    two(T),
    minus(X,T,X2),
    twice(X2,W).

two(s(s(0))).

minus(X,0,X).
minus(s(Y),s(X),R):- minus(Y,X,R).
minus(0,s(_X),_R).

twice(X,_Y):-  var(X).
twice(X,Y):- ground(X), tw(X,Y).

tw(0,0).
tw(s(X),s(s(NX))):- tw(X,NX). 
