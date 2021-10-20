:- module(never_succeeds,[top/0],[assertions]).

top:-
    input_data(X),
    compute(X,Y),  
    show_results(Y).

input_data(5).

compute(X,Y):- 
    X1 is X-1,
    compute(X1,Y1),
    Y is Y1*X1.  


show_results(_X):-
    % ...
    true.
