:- module(_,[p/1,colorlist/1,sorted/1,color/1],[assertions,regtypes,fsyntax]).

% Defining some types and properties (using functiomal syntax)
% which are then used in two simple assertions. With default domain
% sorted/1 is not proved and will generate a run-time check and 
% optionally initiate assertion-based test generation.

:- pred p(X) => sorted(X).
p(X) :- q(X).

:- pred q(X) => list(X).
q(M) :- M = [_,_,_].

:- regtype color/1.
color := red | green | blue.

:- regtype colorlist/1.
colorlist := [] | [~color|~colorlist].

:- prop sorted/1.
sorted := [] | [_].
sorted([X,Y|T]) :- X > Y, sorted([Y|T]).
