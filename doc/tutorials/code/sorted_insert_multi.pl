:- module(sorted_insert_multi,_,[assertions,regtypes]).

:- regtype num_pair(P)  .
num_pair((X,Y)):- num(X),num(Y).

:- regtype list_pair(L).
list_pair([]).
list_pair([X|Xs]):-
    list_pair(Xs),
   num_pair(X).

:- regtype list_pair1(L).
list_pair1([X|Xs]):-
    list_pair(Xs),
    num_pair(X).

:- pred sorted_insert(A,B,C) : (list_pair(A), num_pair(B), var(C)) => list_pair1(C)  .

sorted_insert([], X, [X]).
sorted_insert([(X1,X2)|Ls], (Y1,Y2), [(Y1,Y2), (X1,X2)|Ls]):- X1 >= Y1 .
sorted_insert([X1|Ls], X, [X1|Rs]):- sorted_insert(Ls,X,Rs).