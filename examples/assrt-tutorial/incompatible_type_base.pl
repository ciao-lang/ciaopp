:- module(_,[color/1,colorlist/1,sorted/1],[assertions,regtypes,clpq]).

% Defining some types and properties which can then be used 
% in assertions.

:- regtype color/1.
color(red).
color(green).
color(blue).

:- regtype colorlist/1.
colorlist([]).
colorlist([H|T]) :- color(H), colorlist(T).

:- prop sorted/1.
sorted([]).
sorted([_]).
sorted([X,Y|T]) :- X .>=. Y, sorted([Y|T]).
