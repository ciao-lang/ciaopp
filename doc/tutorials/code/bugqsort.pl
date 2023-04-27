:- module(qsort, [qsort/2], [assertions]).

:- pred qsort(A,B) : (list(num, A), var(B)).

qsort([],[]).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg),
    qsort(Sm,SmS), qsort(Lg,LgS),
    append(SmS,[x|LgS],Result).  % <-- 'x' should be X (variable)

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2):-
    X =< F, partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]):-
    X > F, partition(Y,F,Y1,Y2).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).