:- module(_, [nrev/2], [assertions,fsyntax,nativeprops]).

% Naive reverse with some complex assertions.
% The system flags a (cost) error reminding us that 
% nrev/2 is quadratic, not linear. 
% (Requires cost-related domains.)

:- pred nrev(A,B) : (list(num,A), var(B)) => list(B) 
   + ( det, terminates, steps_o( length(A) ) ).

nrev( [] )    := [].
nrev( [H|L] ) := ~conc( ~nrev(L),[H] ).


:- pred conc(A,B,C) + ( det, terminates, steps_o(length(A))).

conc( [],    L ) := L.
conc( [H|L], K ) := [ H | ~conc(L,K) ].
