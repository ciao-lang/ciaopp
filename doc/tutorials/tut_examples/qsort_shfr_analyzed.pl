:- module(_1,[qsort/2],[assertions,nativeprops]).

:- entry qsort(A,B)
     : ( list(num,A), var(B) ).

:- true pred qsort(A,B)
     : ( mshare([[B]]), var(B), ground([A]) )
    => ground([A,B]).

qsort([X|L],R) :-
    partition(L,X,L1,L2),
    qsort(L2,R2),
    qsort(L1,R1),
    append(R2,[X|R1],R).
qsort([],[]).

:- true pred partition(_A,_B,Left,Right)
     : ( mshare([[Left],[Right]]), var(Left), var(Right), ground([_A,_B]) )
    => ground([_A,_B,Left,Right]).

partition([],_B,[],[]).
partition([e|R],C,[E|Left1],Right) :-
    E<C,
    !,
    partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]) :-
    E>=C,
    partition(R,C,Left,Right1).

:- true pred append(_A,X,_B)
     : ( mshare([[_B]]), var(_B), ground([_A,X]) )
    => ground([_A,X,_B]).

append([],X,X).
append([H|X],Y,[H|Z]) :-
    append(X,Y,Z).


