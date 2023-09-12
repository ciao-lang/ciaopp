:- module(_,[p/1,colorlist/1,sorted/1,color/1],[assertions,regtypes,fsyntax]).

% Defining some types and properties (using functional syntax)
% which are then used in two simple assertions. The system
% detects that property sorted is incompatible with the success
% type of p/1.

:- pred p(X) => sorted(X).
p(X) :- q(X).

:- pred q(X) => color(X).
q(M) :- M = red.

:- regtype color/1.
color := red | green | blue.

:- regtype colorlist/1.
colorlist := [] | [~color|~colorlist].

:- prop sorted/1.
sorted := [] | [_].

sorted([X,Y|T]) :- X >= Y, sorted([Y|T]).
