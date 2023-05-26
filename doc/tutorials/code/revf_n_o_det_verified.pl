:- module(_, [nrev/2], [assertions,fsyntax,nativeprops]).

:- pred nrev(A,B) : (list(num,A), var(B)) => list(B) 
   + ( det, terminates, steps_o( exp(length(A),2) ) ).

nrev( [] )    := [].
nrev( [H|L] ) := ~conc( ~nrev(L),[H] ).

:- pred conc(A,B,C) + ( det, terminates, steps_o(length(A))).

conc( [],    L ) := L.
conc( [H|L], K ) := [ H | ~conc(L,K) ].
