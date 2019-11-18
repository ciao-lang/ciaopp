:- module(s_eqs,
    [ apply/1, eqs_ranges/6, 
      free_peel/4, keys_and_values/3, peel/4,
      simplify_equations/3,
      subtract_keys/3
    ],
    [ ]).

:- use_module(library(keys), [key_lookup/4]).
:- use_module(library(sets), [insert/3, merge/3, ord_member/2]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_vars), [varset/2]).

%------------------------------------------------------------------------%
% UNIFICATION EQUATIONS
% Some utilities for handling equations
%------------------------------------------------------------------------%

peel(Term1,Term2,Bindings,Tail):-
    var(Term1), !,
    Bindings = [Term1=Term2|Tail].
peel(Term1,Term2,Bindings,Tail):-
    var(Term2), !,
    Bindings = [Term2=Term1|Tail].
peel(Term1,Term2,Bindings,Tail):- 
    Term1 == Term2, !,
    Bindings = Tail.
peel(Term1,Term2,Bindings,Tail):-
    functor(Term1,F,N),
    functor(Term2,F,N),
    peel_args(Term1,Term2,0,N,Bindings,Tail).

peel_args(_,_,N1,N,Bindings,Tail) :-
    N1 = N, !,
    Bindings = Tail.
peel_args(Term1,Term2,N1,N,Bindings,Tail):-
    N2 is N1 + 1,
    arg(N2,Term1,A1),
    arg(N2,Term2,A2),
    peel(A1,A2,Bindings,MoreBindings),
    peel_args(Term1,Term2,N2,N,MoreBindings,Tail).

%-------------------------------------------------------------------------
% simplify_equations(+,+,-)                                              |
% simplify_equations(Term1,Term2,Binds)                                  |
% It returns in Binds the simplified set of primitive equations obtained |
% from the unification of Term1 and Term2 with the following format:     |
%  (X,Term,Tv) where X is a variable, Term is a term and Tv is the set of|
% variables in Term                                                      |
% COMMENT!!!!!!! is sort(Temp,E) needed??????????                        |
%------------------------------------------------------------------------%
simplify_equations(Term1,Term2,Binds):-
    free_peel(Term1,Term2,Temp,[]),
    sort(Temp,Binds).

free_peel(Term1,Term2,Binds,Rest) :-
    var(Term1), !,
    varset(Term2,List),
    Binds = [(Term1,Term2,List)|Rest].
free_peel(Term1,Term2,Binds,Rest) :-
    var(Term2), !,
    varset(Term1,List),
    Binds = [(Term2,Term1,List)|Rest].
free_peel(Term1,Term2,Binds,Rest) :-
    Term1 == Term2, !,
    Binds = Rest.
free_peel(Term1,Term2,Binds,Rest) :- 
    functor(Term1,F,N),
    functor(Term2,F,N),
    free_peel_args(0,N,Term1,Term2,Binds,Rest).

free_peel_args(N,N,_,_,Binds,Rest) :- !,
    Binds = Rest.
free_peel_args(N1,N,Term1,Term2,Binds,Rest) :-
    N2 is N1 + 1,
    arg(N2,Term1,A1),
    arg(N2,Term2,A2),
    free_peel(A1,A2,Binds,Rest1),
    free_peel_args(N2,N,Term1,Term2,Rest1,Rest).

% ------------------------------------------------------------------------

keys_and_values([K|Ks],[V|Vs],[K=V|ASub]):-
    keys_and_values(Ks,Vs,ASub).
keys_and_values([],[],[]).

subtract_keys([K=_|Xs],Ks,Dict):-
    ord_member(K,Ks), !,
    subtract_keys(Xs,Ks,Dict).
subtract_keys([X|Xs],Ks,[X|Dict]):-
    subtract_keys(Xs,Ks,Dict).
subtract_keys([],_Ks,[]).

apply([X=Term|ASub]):-
    X=Term,
    apply(ASub).
apply([]).

% ------------------------------------------------------------------------

eqs_ranges([X|Dom],Eqs,[Term|Terms],[Vars0|Vars],VarSet0,VarSet):-
    key_lookup(X,Eqs,Term,Eqs0), !,
    varset(Term,Vars0),
    merge(VarSet0,Vars0,VarSet1),
    eqs_ranges(Dom,Eqs0,Terms,Vars,VarSet1,VarSet).
eqs_ranges([_|Dom],Eqs,[Y|Terms],[[Y]|Vars],VarSet0,VarSet):-
    insert(VarSet0,Y,VarSet1),
    eqs_ranges(Dom,Eqs,Terms,Vars,VarSet1,VarSet).
eqs_ranges([],[],[],[],VarSet,VarSet).
