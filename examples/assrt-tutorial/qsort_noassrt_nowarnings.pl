:- module(_,[qsort/2],[assertions,nativeprops,modes]).

% Adding information on how the exported predicate should 
% be called, the system can infer that =</2 and >/2 will be 
% called correctly, and no warnings are flagged.

:- pred qsort(+list(num),_).

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
