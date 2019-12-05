:- module(_, [canonical/1,
              canonical_pretty/1,
              canonical_each/1,
              melt/2,
              melt1/3,
              melteach/2,
              variable/1], []).

:- use_module(library(write), [numbervars/3, prettyvars/1]).

canonical(T) :-
    numbervars(T,0,_).


canonical_each([]).
canonical_each([X|Xs]) :-
    canonical(X),
    canonical_each(Xs).
    

melt(X,Y) :-
    melt1(X,Y,_Assoclist),
    !.

melt1(X,_,_) :-
    anonVariable(X),
    !.
melt1(X,Y,S) :-
    variable(X),
    !,
    assoc(X,Y,S).
melt1(X,X,_) :-
    atomic(X),
    !.
melt1(X,Y,S) :-
    functor(X,F,N),
    functor(Y,F,N),
    meltargs(1,N,X,Y,S).

meltargs(I,N,_,_,_) :-
    I > N,
    !.
meltargs(I,N,X,Y,S) :-
    arg(I,X,Xi),
    melt1(Xi,Yi,S),
    arg(I,Y,Yi),
    I1 is I+1,
    meltargs(I1,N,X,Y,S).


assoc(X,Y,[assoc(X,Y)|_]) :-
    !.
assoc(X,Y,[_|S]) :-
    assoc(X,Y,S).

variable('$VAR'(N)) :-
    atomic(N).
    
anonVariable('$VAR'('_')).

melteach([],[]).
melteach([X|Xs],[Y|Ys]) :-
    melt(X,Y),
    melteach(Xs,Ys).
    
% CIAO
canonical_pretty(T) :-
    prettyvars(T).

%% % SICS
%% canonical_pretty(T) :-
%%      numbervars(T,0,_).


