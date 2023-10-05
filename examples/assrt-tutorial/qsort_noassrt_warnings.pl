:- module(_,[qsort/2],[assertions,nativeprops,modes]).

% With no information on the calls to qsort/2, 
% the analyzer warns that it cannot ensure that 
% the calls to =</2 and >/2 will not generate a 
% run-time error.

qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).

