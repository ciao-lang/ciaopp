:- regtype num_pair(P) .
num_pair((X, Y)):-
    num(X),
    num(Y).

:- regtype list_pair(L) . 
list_pair([]).
list_pair([X|Xs]):-
    num_pair(X),
    list_pair(Xs).

:- regtype list_pair1(L) .
list_pair1([X|Xs]):-
   num_pair(X),
   list_pair(Xs).