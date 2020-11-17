:- module(_1,[qsort/2],[assertions,regtypes,nativeprops]).

:- entry qsort(A,B)
     : ( list(num,A), var(B) ).

:- true pred qsort(A,B)
     : ( list(num,A), term(B) )
    => ( list(num,A), list(num,B) ).

:- true pred qsort(A,B)
     : ( mshare([[B]]), var(B), ground([A]) )
    => ground([A,B]).

:- true pred qsort(A,B)
     : ( mshare([[B]]), var(B), ground([A]), list(num,A), term(B) )
    => ( ground([A,B]), list(num,A), rt7(B) )
     + ( is_det, mut_exclusive ).

:- true pred qsort(A,B)
     : ( mshare([[B]]), var(B), ground([A]), list(unifier_elem,A), term(B) )
    => ( ground([A,B]), list(unifier_elem,A), list(unifier_elem,B) )
     + ( is_det, mut_exclusive ).

qsort([X|L],R) :-
    partition(L,X,L1,L2),
    qsort(L2,R2),
    qsort(L1,R1),
    append(R2,[X|R1],R).
qsort([],[]).

:- true pred partition(_A,_B,Left,Right)
     : ( list(num,_A), num(_B), term(Left), term(Right) )
    => ( list(num,_A), num(_B), list(unifier_elem,Left), list(num,Right) ).

:- true pred partition(_A,_B,Left,Right)
     : ( mshare([[Left],[Right]]), var(Left), var(Right), ground([_A,_B]) )
    => ground([_A,_B,Left,Right]).

:- true pred partition(_A,_B,Left,Right)
     : ( mshare([[Left],[Right]]), var(Left), var(Right), ground([_A,_B]), list(num,_A), num(_B), term(Left), term(Right) )
    => ( ground([_A,_B,Left,Right]), list(num,_A), num(_B), list(unifier_elem,Left), list(num,Right) )
     + ( is_det, mut_exclusive ).

partition([],_B,[],[]).
partition([e|R],C,[E|Left1],Right) :-
    E<C,
    !,
    partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]) :-
    E>=C,
    partition(R,C,Left,Right1).

:- true pred append(_A,X,_B)
     : ( list(num,_A), rt5(X), term(_B) )
    => ( list(num,_A), rt5(X), rt11(_B) ).

:- true pred append(_A,X,_B)
     : ( mshare([[_B]]), var(_B), ground([_A,X]) )
    => ground([_A,X,_B]).

:- true pred append(_A,[_B|_C],X)
     : ( mshare([[X]]), var(X), ground([_A,_B,_C]), list(unifier_elem,_A), term(X), num(_B), list(unifier_elem,_C) )
    => ( ground([_A,X,_B,_C]), list(unifier_elem,_A), rt5(X), num(_B), list(unifier_elem,_C) )
     + ( is_det, mut_exclusive ).

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


:- regtype rt7/1.

rt7([]).
rt7([A|B]) :-
    num(A),
    list(unifier_elem,B).


