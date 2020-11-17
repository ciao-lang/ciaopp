:- module(_1,[qsort/2],[assertions,regtypes]).

:- entry qsort(A,B)
     : ( list(num,A), var(B) ).

:- true pred qsort(A,B)
     : ( list(num,A), term(B) )
    => ( list(num,A), list(num,B) ).

qsort([X|L],R) :-
    partition(L,X,L1,L2),
    qsort(L2,R2),
    qsort(L1,R1),
    append(R2,[X|R1],R).
qsort([],[]).

:- true pred partition(_A,_B,Left,Right)
     : ( list(num,_A), num(_B), term(Left), term(Right) )
    => ( list(num,_A), num(_B), list(num,Left), list(num,Right) ).

partition([],_B,[],[]).
partition([e|R],C,[E|Left1],Right) :-
    E<C,
    !,
    partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]) :-
    E>=C,
    partition(R,C,Left,Right1).

:- true pred append(_A,X,_B)
     : ( list(_A,num), rt5(X), term(_B) )
    => ( list(_A,num), rt5(X), rt11(_B) ).

append([],X,X).
append([H|X],Y,[H|Z]) :-
    append(X,Y,Z).


:- regtype rt5/1.

rt5([A]) :-
    num(A).


:- regtype rt11/1.

rt11([A|B]) :-
    num(A),
    list(num,B).


