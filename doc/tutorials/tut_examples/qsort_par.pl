:- module(_, [qsort/2], [assertions]).
:- entry qsort(A,B) : (list(num, A), var(B)).

qsort([X|L],R) :-
    partition(L,X,L1,L2),
    qsort(L2,R2), qsort(L1,R1), 
    append(R1,[X|R2],R). 
qsort([],[]).

partition([],_B,[],[]).
partition([E|R],C,[E|Left1],Right):- 
    E < C,  partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]):-
    E > C, partition(R,C,Left,Right1).

append([],Ys,Ys).
append([X|Xs],Ys,[X|Zs]):- append(Xs,Ys,Zs).
