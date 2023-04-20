:- prop sorted/1.
sorted([]).
sorted([_]).
sorted([X,Y|Ys]) :-
    X=<Y,
    sorted([Y|Ys]).

:- prop list_nnegint(X) + regtype 
# "Verifies that @var{X} is list of non-negative integers." .  
list_nnegint([]).
list_nnegint([X|T]) :-
    nnegint(X),
    list_nnegint(T).