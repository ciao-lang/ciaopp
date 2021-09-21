:- module(_, [nrev/2], [assertions,fsyntax,nativeprops]).

:- pred nrev(A,B) : {list, ground} * var => list(B) 
   + ( not_fails, is_det, steps_o( length(A) ) ).

nrev( [] )    := [].
nrev( [H|L] ) := ~conc( ~nrev(L),[H] ).


:- pred conc(A,B,C) + ( terminates, non_det, steps_o(length(A)) ).

conc( [],    L ) := L.
conc( [H|L], K ) := [ H | ~conc(L,K) ]. 
