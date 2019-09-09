/*             Copyright (C)2004-2005 UNM-CLIP				*/

:- module(share_amgu_aux,
          [ peel_equations/3,
            sh_peel/3,
            bin_union/3,
	    self/2,
	    star/2,
	    amgu/4,
	    amgu/5
	    ],
         [assertions,isomodes ]).

:- use_module(library(sort), [sort/2]).
:- use_module(library(sets), [ord_union/3]).
:- use_module(library(lsets), [closure_under_union/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(domain(share_amgu_sets), [split_list_of_lists/4]).
:- use_module(domain(share_aux), [append_dl/3]).

%------------------------------------------------------------------------%
% This file implements the amgu for sharing domain defined by Jacobs and |
% Langen and the non-redundant amgu defined by Hill,Bagnara and          |
% Zaffanella and other auxiliary functions.                              |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                                                                        |
%        programmer: J. Navas                                            |
%                                                                        |
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT UNIFICATION                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).
%------------------------------------------------------------------------%
% amgu(+,+,+,+,-)                                                        |
% amgu(X,T,Flag,AMGU,AMGU0)                                              |
% AMGU0 describes the unification x=t (concrete unification) in a state  |
% described by AMGU.                                                     |
% If Flag = star then if performs the "star" amgu                        |
% Otherwise, it performs the amgu the "self-union" amgu                  |   
%------------------------------------------------------------------------%
amgu(X,T,star,ASub,AMGU):-	
	amgu(X,T,ASub,AMGU),!.
amgu(X,T,self,ASub,AMGU):-	
	amgu_s(X,T,ASub,AMGU),!.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   Abstract Unification with STAR                       %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% amgu(+,+,+,-)                                                          |
% amgu(X,T,AMGU,AMGU0)                                                   |
% AMGU0 describes the unification x=t (concrete unification) in a state  |
% described by AMGU.                                                     |
% amgu(x=t,S) = irrel(V_xt,sh) union                                     |
%               bin_union(star(rel(V_x,S)),star(rel(V_t,S)))             |
% GENERAL CASE                                                           |
% Each variable in x can be aliased to any other variable(s) in s        | 
% via an aliasing to a variable in t (and vice versa)                    |
%------------------------------------------------------------------------%
amgu(X,T,ASub,AMGU):-
	sort(T,V_t),
	sort(ASub,SASub),
	ord_union([X],V_t,V_xt), 
	split_list_of_lists([X],SASub,Rel_x,_),
	%simple_message("Rel_x: ~q",[Rel_x]),
	split_list_of_lists(V_t,SASub,Rel_t,_),
	%simple_message("Rel_t: ~q",[Rel_t]),
	split_list_of_lists(V_xt,SASub,_,Irrel_xt),	
	%simple_message("Irrel_xt: ~q",[Irrel_xt]),
	bin_union(Rel_x,Rel_t,BinUnion),
	%simple_message("BinUnion: ~q",[BinUnion]),
	star(BinUnion,BinUnionStar),
	%simple_message("Star: ~q",[BinUnionStar]),
	ord_union(Irrel_xt,BinUnionStar,AMGU).

:- pop_prolog_flag(multi_arity_warnings).
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   Abstract Unification with SELF UNION                 %
%------------------------------------------------------------------------%
% amgu_s(+,+,+,-)                                                        |
% amgu_s(X,T,AMGU,AMGU0)                                                 |
% AMGU0 describes the unification x=t (concrete unification) in a state  |
% described by AMGU.                                                     |
% amgu(x=t,S) = irrel(V_xt,sh) union                                     |
%               bin_union(self(rel(V_x,S)),self(rel(V_t,S)))             |
%------------------------------------------------------------------------%

amgu_s(X,T,ASub,AMGU):-
	sort(T,V_t),
	sort(ASub,SASub),
	ord_union([X],V_t,V_xt),
	split_list_of_lists([X],SASub,Rel_x,_),
	split_list_of_lists(V_t,SASub,Rel_t,_),	
	split_list_of_lists(V_xt,SASub,_,Irrel_xt),	
	self(Rel_x,Star_Rel_x),
	self(Rel_t,Star_Rel_t),
	bin_union(Star_Rel_x,Star_Rel_t,BinUnion),
	ord_union(Irrel_xt,BinUnion,AMGU).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                              BINARY UNION                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% bin_union(+,+,-)                                                       |
% bin_union(S1,S2,S)                                                     |
% Cartesian product using union instead of constructing pairs. S1 and S2 |
% must be sorted lists of lists.                                         |
% bin(sh1,sh2) = {S1 union S2 | S1 in sh1, S2 in sh2}                    |
% S is a sorted list of lists                                            |
%------------------------------------------------------------------------%

:- use_module(library(lsets), [sort_list_of_lists/2]).

% bin_union([],_,[]).
% bin_union([H|T],L2,L):-
% %	sort(H,H1),
% 	bin_union_(L2,H,SL),
% 	bin_union(T,L2,RL),
% 	ord_union(RL,SL,L).

% bin_union_([],_,[]).
% bin_union_([S|Ss],E,BUnion ):-
% %	sort(H,H0),
% 	ord_union(S,E,Union),
% 	bin_union_(Ss,E,Res),
% 	ord_union(Res,[Union],BUnion).

bin_union(Ss1,Ss2,BinUnion):-
	bin_union0(Ss1,Ss2,[],BinUnion_u),
	sort_list_of_lists(BinUnion_u,BinUnion).

%% tail-recursion version
bin_union0([],_,Res,Res).
bin_union0([X|Xs],Ss,Acc,Res):-
	bin_union_(Ss,X,Acc,NAcc),
	bin_union0(Xs,Ss,NAcc,Res).

%% tail-recursion version
bin_union_([],_,Res,Res).
bin_union_([S|Ss],E,Acc,Res ):-
	ord_union(S,E,Union),
	bin_union_(Ss,E,[Union|Acc],Res).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      SELF-BIN  UNION                                   %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% self(+,-)                                                              |
% self(S1,S)                                                             |
% Version of binary union of sharing is non-redundant w.r.t. pair-sharing|
% sel_bin(sh) = bin(sh,sh)                                               |
%------------------------------------------------------------------------%
self(Sh,Sh0):- bin_union(Sh,Sh,Sh0).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      STAR UNION (CLOSURE UNDER UNION)                  % 
%------------------------------------------------------------------------%
% star(+,-)                                                              |  
% star(Xss,Star)                                                         |
% Star is the closure under union of Xss                                 |
% bin(sh1,sh2) = {S1 union S2 | S1 in sh1, S2 in sh2}                    |
% Star is a sorted list of lists                                         |
%------------------------------------------------------------------------%

star(Sh,Star):-closure_under_union(Sh,Star).

%------------------------------------------------------------------------%
%                            ABSTRACT Peel Equations                     %
%------------------------------------------------------------------------%
% peel_equations(+,+,-)                                                  %
% peel_equations(Term1,Term2,Eqs)                                        %
% Eqs is a list of pairs x-t                                             %
% PLAI version                                                           %
%------------------------------------------------------------------------%

peel_equations(Term1,Term2,Equs) :-
	sh_peel(Term1,Term2,Temp-[]),
	sort(Temp,Equs). % remove duplicates
  
sh_peel(Term1,Term2,Binds) :-
	var(Term1),!,
	sh_peel_var(Term1,Term2,Binds).
sh_peel(Term1,Term2,Binds) :-
	var(Term2),!,
	varset(Term1,List),
	Binds = [(Term2,List)|X]-X.
sh_peel(Term1,Term2,Binds) :- 
	Term1 == Term2, !,
	Binds = X-X.
sh_peel(Term1,Term2,Binds) :-
	functor(Term1,F,N),
	functor(Term2,F,N),
	sh_peel_args(Term1,Term2,0,N,Binds).

sh_peel_var(Term1,Term2,Binds):-
	var(Term2),!,
	Binds = [(Term1,[Term2])|X]-X.
sh_peel_var(Term1,Term2,Binds):-
	varset(Term2,List),
	Binds = [(Term1,List)|X]-X.

sh_peel_args(_,_,N1,N,Binds) :-
	N1 = N, !,
	Binds = X-X.
sh_peel_args(Term1,Term2,N1,N,Binds) :-
	N2 is N1 + 1,
	arg(N2,Term1,A1),
	arg(N2,Term2,A2),
	sh_peel(A1,A2,Bind1),
	sh_peel_args(Term1,Term2,N2,N,Bind2),
	append_dl(Bind1,Bind2,Binds).
