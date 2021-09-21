:- module(_,[qsort/2],[assertions,nativeprops]).

:- pred qsort(X,Y) : (ground(X),list(X),var(Y)) => ground(Y).
qsort(X,Y) :- qsort_(X,Y,T), T=[].

:- pred qsort_(X,Y,Z) : (list(X),var(Y),var(Z),indep(Y,Z)) => ground(X).
qsort_([], Result, Result).
qsort_([First|Rest],ResultB,ResultE) :-
    partition(Rest,First,Sm,Lg), 
    qsort_(Sm,SmB,SmE), 
    qsort_(Lg,LgB,LgE), 
    ResultB=SmB, 
    SmE=[First|LgB], 
    ResultE=LgE.

:- pred partition(L,P,Lg,Sm)
   => (list(Lg), list(Sm), ground(Lg), ground(Sm)).
partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X @=< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X @> F,
    partition(Y,F,Y1,Y2).
