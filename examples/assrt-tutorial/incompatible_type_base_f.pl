:- module(_,[colorlist/1,sorted/1,color/1],[assertions,regtypes,fsyntax,clpq]).

% Defining some types and properties (using functional syntax)
% which can then be used in assertions. 

:- regtype color/1.
color := red | green | blue.

:- regtype colorlist/1.
colorlist := [] | [~color|~colorlist].

:- prop sorted/1.
sorted := [] | [_].
sorted([X,Y|T]) :- X .>=. Y, sorted([Y|T]).
