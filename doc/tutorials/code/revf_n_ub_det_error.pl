:- module(_, [nrev/2], [assertions,fsyntax,nativeprops]).

% Naive reverse with some complex assertions.
% The system is able to prove them but flags an error 
% since length(A) is not a strict upper bound for conc/3; 
% it is length(A)+1 (cost domains required for the 
% cost-related properties).

:- pred nrev(A,B) : (list(num,A), var(B)) => list(B) 
   + ( det, terminates, steps_o( exp(length(A),2) ) ).

nrev( [] )    := [].
nrev( [H|L] ) := ~conc( ~nrev(L),[H] ).


:- pred conc(A,B,C) + ( det, terminates, steps_ub(length(A))).

conc( [],    L ) := L.
conc( [H|L], K ) := [ H | ~conc(L,K) ].
