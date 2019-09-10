:- module(sharefree_amgu_aux,
	  [ sharefree_amgu_iterate/3,
	    amgu_non_star/5,
	    peel_equations_frl/3,
	    map_freeness_list/3,
	    unmap_freeness_list/2,
	    filter_freeness_with_call/3,
	    shfr_update_freeness/4,
	    update_freeness/4,
	    share_with/3,
	    lin/2
          ],
	  [assertions, isomodes]).

:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the amgu for sharing+Freeness domain defined by   |
% Jacobs&Langen and Muthukumar&Hermenegildo and other auxiliary functions|
%------------------------------------------------------------------------%

:- use_module(library(lists), [length/2]). 
:- use_module(library(sort), [sort/2]).
:- use_module(domain(s_grshfr), [member_value_freeness/3]).
:- use_module(library(sets),
	[ord_member/2, ord_subtract/3, ord_union/3, ord_subset/2, ord_intersection/3]).
:- use_module(library(lsets), [merge_list_of_lists/2]).
:- use_module(domain(share_amgu_sets), [split_list_of_lists/4]).	
:- use_module(library(terms_vars), [varset/2, varsbag/3]).
:- use_module(domain(share_amgu_aux)).
:- use_module(domain(share_aux), [append_dl/3]).

%------------------------------------------------------------------------%
% sharefree_amgu_iterate(+,+,-)                                          %
%------------------------------------------------------------------------%
sharefree_amgu_iterate([],ASub,ASub).
sharefree_amgu_iterate([(X,(Ts,Type,L))|Eqs],ASub,ASub2):-	
     amgu_shfr(X,(Ts,Type,L),ASub,ASub1),
     sharefree_amgu_iterate(Eqs,ASub1, ASub2).

%------------------------------------------------------------------------%
%                      ABSTRACT UNIFICATION                              %
%------------------------------------------------------------------------%
% amgu_shfr(+,+,+,-)                                                     |
% amgu_shfr(X,(T,Type,L),(Sh,f),SHF')                                    | 
% Amgu describes the unification X=T (concrete unification) in a state   |
% described by S. Type describes T is v or t and L, l or nl              |
% SHF' = (Sh',f') where:                                                 |
% Sh' =  \rel(Sh_xt) U Sh_x \bin Sh_t   if x in f or t in f (*)          |
%        \rel(Sh_xt) U Sh_x \bin Sh_t*  if x \notin f or t \notin f      |     
%                                          but t \subseteq f and lin(t)  |
%        amgu(X,T,Sh)                      otherwise                     |
%                                                                        |
% f'  =  f             if x in f, t in f                                 |
%     |  f \ (U rel_x) if x in f, t not in f                             |  
%     |  f \ (U rel_t) if x not in f, t in f                             |  
%     |  f \ (U rel_x) U (U rel_t) if x not in f, t not in f             |
%                                                                        |
% t is linear iff                                                        |
%   1. for all y in t: [t]_y=1 and                                       |
%   2. for all y in t: t in F  and                                       |
%   3. for all y in t, z in t, y\neq z: sh_y /\ sh_z = \emptyset         |
%------------------------------------------------------------------------%
% Implementation issues: The update of freeneess component consists of   |
%  (1) remove variables (keeps track of only free variables)             |
%  (2) call update_freeness (keeps track of ground and non-free)         |
%------------------------------------------------------------------------%
% (*) Note that "if x in f or t in f" means that |x|=|t|=1. Thus, if x   |
% or t are free and since |x|=|t|=1, x and t are linear, the application |
% of star union is not necessary.                                        | 
%------------------------------------------------------------------------%
amgu_shfr(X,(T,Type,Lin),(Sh,F),(Sh0,F0)):-
     member_value_freeness(F,Free_Vars0,f),
     sort(Free_Vars0,Free_Vars),
     amgu_shfr_(X,(T,Type,Lin),(Sh,Free_Vars),(Sh0,F0)).
%------------------------------------------------------------------------%

amgu_shfr_(X,(T,Type,_),(Sh,F),(Sh0,F0)):-
     ord_member(X,F),!,       
%% sharing
     % CASE 1: x or t is free 
     amgu_non_star(non_star,X,T,Sh,Sh0),
%% freeness
     ( ((Type == v), T = [T1], ord_member(T1,F)) ->
	% x in f, t in f (1)
        F1 = F
     ;  % x in f, t not in f (2)  
	update_freeness([X],Sh,F,F1) 
     ),     
     map_freeness_list(F1,f,F0).
amgu_shfr_(X,([T],v,_),(Sh,F),(Sh0,F0)):-
     ord_member(T,F),!,
%% sharing
     % CASE 1: x or t is free 
     amgu_non_star(non_star,X,[T],Sh,Sh0),
%% freeness
     % CASE 3: x not in f, t in f	
     update_freeness([T],Sh,F,F1),
     map_freeness_list(F1,f,F0).
amgu_shfr_(X,(T,_,l),(Sh,F),(Sh0,F0)):-
%% sharing
     % CASE 2: x not in f, t not in f but t is linear
     alin_f(T,Sh,F),!, 
     amgu_non_star(star_t,X,T,Sh,Sh0),
%% freeness
     % CASE 4: x not in f, t not in f	
     ord_union([X],T,X_union_T),
     update_freeness(X_union_T,Sh,F,F1),
     map_freeness_list(F1,f,F0).
amgu_shfr_(X,(T,_,_),(Sh,F),(Sh0,F0)):-
%% sharing
     % CASE 3: otherwise	
     amgu(X,T,star,Sh,Sh0),
%% freeness
     % CASE 4: x not in f, t not in f	
     ord_union([X],T,X_union_T),
     update_freeness(X_union_T,Sh,F,F1),
     map_freeness_list(F1,f,F0).

% alin(T) iff t \subseteq f and lin(t)
alin_f(T,Sh,F):-
     sort(T,Ts),
     ord_subset(Ts,F),!,
     lin(Sh,Ts).
%------------------------------------------------------------------------%
% lin(+,+)                                                               |
% lin(Sh,t) iff for all s \in sh_t, |s /\ t| = 1                         |
%------------------------------------------------------------------------%
lin(Sh,V_t):-
	split_list_of_lists(V_t,Sh,Sh_t,_),     
	lin_(Sh_t,V_t).

lin_([],_).
lin_([S|Sh_t],V_t):-
	ord_intersection(S,V_t,[_]),
	lin_(Sh_t,V_t).
	
% Returns only free variables (f)
update_freeness(Vars,Sh,F,F0):-
     share_with(Vars,Sh,Rel_Vars),
     ord_subtract(F,Rel_Vars,F0).

share_with([],_,[]).  % TODO: missing cut
share_with(Vars,Sh,Rel_Vars):- 
     split_list_of_lists(Vars,Sh,Rel,_),
     merge_list_of_lists(Rel,Rel_Vars0),!,
     (Rel_Vars0 = [] ->
      Rel_Vars = Vars
     ;Rel_Vars = Rel_Vars0).	 

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%           Abstract Unification NON STAR                                %  
%------------------------------------------------------------------------%
% amgu_non_star(+,+,+,+,-)                                               |
% amgu_non_star(Flag,X,T,AMGU,AMGU0)                                     |
% AMGU0 describes the unification x=t (concrete unification) in a state  |
% described by AMGU.                                                     |
% if Flag = star_x then                                                  |
%       amgu(x=t,S) = \rel(V_xt,sh) U (sh_x* \bin sh_t)                  |
% else                                                                   |
%    if Flag = star_t then                                               |
%       amgu(x=t,S) = \rel(V_xt,sh) U (sh_x \bin sh_t*)                  |
%    else  * non_star *                                                  | 
%       amgu(x=t,S) = \rel(V_xt,sh) U (sh_x \bin sh_t)                   |
%    endif                                                               |
% endif                                                                  |
%------------------------------------------------------------------------%
amgu_non_star(Flag,X,T,ASub,AMGU):-
	sort(T,V_t),
	sort(ASub,SASub),
	ord_union([X],V_t,V_xt),
	split_list_of_lists([X],SASub,Rel0_x,_),
	split_list_of_lists(V_t,SASub,Rel0_t,_),
	split_list_of_lists(V_xt,SASub,_,Irrel_xt),!,
	( Flag == star_x ->
	  star(Rel0_x,Rel_x),
	  Rel_t = Rel0_t
        ;
	  ( Flag == star_t ->
   	    star(Rel0_t,Rel_t),
	    Rel_x = Rel0_x
          ; 
	    % non_star
	    Rel_x = Rel0_x,
	    Rel_t = Rel0_t
          )
        ),
	bin_union(Rel_x,Rel_t,BinUnion),
	ord_union(Irrel_xt,BinUnion,AMGU).
      
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      UPDATE FREENESS                                   % 
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfr_update_freeness(+,+,+,-)                                          |
% shfr_update_freeness(Sh',f',Vars,Newf)                                 |
% NewF = f' U {x/g | x in g'} U {x/nf | x in nf'}                        |
% where:                                                                 |
% - Sh' is the Set-Sharing returned by amgu                              |
% - f' is the list of free variables returned by amgu (only f)           | 
% - Vars are either head vars (call_to_entry) or goal vars               |
%   (exit_to_prime)                                                      | 
% - NewF is the final freeness ({f,nf,g})                                |
%                                                                        |
% nf' = x in F_Call, x not in f', x not in g'                            |
% g'  = Vars \ (Sh)_vars                                                 |
%                                                                        |  
% Note: the variables of the body are free but they are added by         |
% sharefree_amgu_extend_asub/3 (by ortogonality)                         |
%-------------------------------------------------------------------------
shfr_update_freeness(Sh,F,Vars,F1):-
     % ground variables
     merge_list_of_lists(Sh,Sh_Vars),
     ord_subtract(Vars,Sh_Vars,G),
     map_freeness_list(G,g,G0),
     % non-free variables
     unmap_freeness_list(F,UF),
     ord_subtract(Vars,UF,NF0),
     ord_subtract(NF0,G,NF1),
     map_freeness_list(NF1,nf,NF),
     % union of all variables
     ord_union(F,G0,F0),
     ord_union(F0,NF,F1).

% Necessary operations to deal with PLAI domain {f,g,nf}
map_freeness_list([],_,[]).
map_freeness_list([X|T],S,[X/S|Ts]):-
        map_freeness_list(T,S,Ts).

unmap_freeness_list([],[]).
unmap_freeness_list([X/_|T],[X|Ts]):-
        unmap_freeness_list(T,Ts).

%------------------------------------------------------------------------%
% peel_equations_frl(+,+,-)                                              |
% peel_equations_frl(Term1,Term2,Eq)                                     |
%------------------------------------------------------------------------%
% returns a list of pairs (x,(t,T,L)) where                              |
% x is variable                                                          | 
% t is a list of variables                                               |
% T represents whether t is a variable (v) or a functor (t)              |
% L represents whether t is linear (l) or non-lineal (nl). Note that x is|
%   always linear (variable)                                             |
%------------------------------------------------------------------------%
peel_equations_frl(Term1,Term2,Equs) :-
	sh_peel_frl(Term1,Term2,Temp-[]),
	sort(Temp,Equs). 

sh_peel_frl(Term1,Term2,Binds) :-
	var(Term1),!,
	sh_peel_var_frl(Term1,Term2,Binds).
sh_peel_frl(Term1,Term2,Binds) :-
	var(Term2),!,
	varset(Term1,List),
	linear(Term1,L),
	Binds = [(Term2,(List,t,L))|X]-X.
sh_peel_frl(Term1,Term2,Binds) :- 
	Term1 == Term2, !,
	Binds = X-X.
sh_peel_frl(Term1,Term2,Binds) :-
	functor(Term1,F,N),
	functor(Term2,F,N),
	sh_peel_args_frl(Term1,Term2,0,N,Binds).

sh_peel_var_frl(Term1,Term2,Binds):-
	var(Term2),!,
	Binds = [(Term1,([Term2],v,l))|X]-X.
sh_peel_var_frl(Term1,Term2,Binds):-
	varset(Term2,List),
	linear(Term2,L),
	Binds = [(Term1,(List,t,L))|X]-X.
sh_peel_args_frl(_,_,N1,N,Binds) :-
	N1 = N, !,
	Binds = X-X.
sh_peel_args_frl(Term1,Term2,N1,N,Binds) :-
	N2 is N1 + 1,
	arg(N2,Term1,A1),
	arg(N2,Term2,A2),
	sh_peel_frl(A1,A2,Bind1),
	sh_peel_args_frl(Term1,Term2,N2,N,Bind2),
	append_dl(Bind1,Bind2,Binds).

linear(Term,l):-
	linear_(Term),!.
linear(_,nl).

linear_(Term):-
	varsbag(Term,Vars,[]),
	length(Vars,L1),
	sort(Vars,Vars_non_rep),
	length(Vars_non_rep,L2),
	L1 == L2.
	
%------------------------------------------------------------------------%
% filter_freeness_with_call(+,+,-)                                       |
% filter_freeness_with_call(Vars,Freeness,Res)                           |
% Res removes from Vars those variables that are ground.                 |
%------------------------------------------------------------------------%
filter_freeness_with_call(Vars,Freeness_Call,Res):-
     member_value_freeness(Freeness_Call,G_Vars,g),
     filter_freeness_with_call_(Vars,G_Vars,Res).

filter_freeness_with_call_([],_,[]).
filter_freeness_with_call_([X|Xs],G_Vars,Result):-
     ord_member(X,G_Vars),!,
     filter_freeness_with_call_(Xs,G_Vars,Result).
filter_freeness_with_call_([X|Xs],G_Vars,[X|Res]):-
     filter_freeness_with_call_(Xs,G_Vars,Res).



