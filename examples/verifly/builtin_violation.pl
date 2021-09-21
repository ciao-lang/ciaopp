:- module(_,[top/0],[assertions]).

top:-
    input_data(X),
    compute(X,Y),
    show_results(Y).

input_data(a).

compute(X,Y):- 
    X2 is 3,
    X1 is X+X2,  %violates assertion for is/2
    Y is X1+1.

show_results(_X):-
    % ...
    true.
