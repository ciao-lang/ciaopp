:- module(_, [main/0], [assertions] ).

main :-
    append([1,2,3|L],L1,Cs).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).
