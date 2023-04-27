 :- module(_, [qsort/2], [assertions, regtypes, nativeprops]).

:- regtype list_num(A).
list_num([]).
list_num([A|B]) :- num(A), list_num(B).

:- calls qsort(A,B) : list_num(A).                           % A1
:- success qsort(A,B)  => (list_num(B)).                     % A2
:- calls partition(A,B,C,D) : (ground(A), num(B)).           % A3
:- success partition(A,B,C,D) => (list(num, C), ground(D)).  % A4
:- comp partition/4 + not_fails.                             % A5
:- comp partition/4 + is_det.                                % A6


qsort([],[]).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg),
    qsort(Sm,SmS), qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2):-
    X < F, partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]):-
    X > F, partition(Y,F,Y1,Y2).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).