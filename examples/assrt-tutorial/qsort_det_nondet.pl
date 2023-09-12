:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes]).

% qsort/2 with some assertions.
% If we have =</2 and >=/2 in partition, the system warns 
% that both partition/4 and qsort/2 may not be deterministic.

:- pred qsort(+list(num),-list(num)) + semidet.
 
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

:- pred partition(+list(num),+num,-list(num),-list(num)) + det.

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X >= F,
    partition(Y,F,Y1,Y2).

:- pred append(+list(num),+list(num),-list(num)) + semidet.

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
