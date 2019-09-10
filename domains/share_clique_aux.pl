:- module(share_clique_aux,
	[amgu_clique/5,
	 bin_union_w/3,
	 star_w/2,
	 self_w/2,
	 ord_union_w/3,
	 ord_intersection_w/3,
	 rel_w/3,
	 irrel_w/3,
	 amgu_rel_non_rel_info/7,
	 amgu_sharing_part/4,
	 share_clique_normalize/2,
	 share_clique_normalize/4,
	 eliminate_redundancies/2,
% auxiliary predicates for normalization
	 move_clique_to_sharing/4,
	 regularize/2,
	 minimize/3,
	 minimum_cardinality/1,
	 check_threshold/2,
	 longest_candidate/5,
	 smallest_candidate/5,
	 comb/3,
	 update_clique/4,
	 intersect_all/2,
	 number_of_subsets/2,
	 list_if_not_nil/2,	 
% for running benchmarks
	 card_cliques/2,
	 minimize/3,
	 number_of_norma/1,
	 clean_number_of_norma/0
        ],
	[assertions, isomodes]).

:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the amgu for clique-sharing domain defined by     |
% Hill,Bagnara and  Zaffanella and other auxiliary functions.            |
%------------------------------------------------------------------------%

% REMARK: In order to number how many normalization processes have been
% performed, we assert a fact for each one. To take time measurings, we
% recommend you to comment it.

:- use_module(library(sort), [sort/2]).
:- use_module(library(sets), [ord_union/3, ord_subset/2, ord_intersection/3]).
:- use_module(library(lsets),
        [merge_list_of_lists/2, ord_intersect_all/2, sort_list_of_lists/2]).
:- use_module(library(lists), [length/2, select/3]).
:- use_module(domain(sharing_clique), 
 	[share_clique_sort/2,
	 share_clique_widen/4      % amgu&star 
        ]).               
:- use_module(domain(share_amgu_sets), 
	[delete_vars_from_list_of_lists/3,
	 intersection_list_of_lists/3,
	 delete_list_of_lists/3,
	 ord_subset_lists_with_list/2,
	 sublist_list_of_lists/4,
	 nosublist_list_of_lists/3,
	 intersection_lists_with_list/3,
	 split_list_of_lists/4]).
:- use_module(library(aggregates), 
	[bagof/3]).
:- use_module(library(between), 
	[between/3]).
:- use_module(domain(share_amgu_aux)).
:- use_module(library(aggregates), [findall/3]). % for number_of_norma/1

%------------------------------------------------------------------------%
% REMARK:                                                                |
% The normalization process is performed after call2entry and in the     |
% compute_lub. Also, for correctness in identical_abstract and           |
% less_or_equal.                                                         |
%------------------------------------------------------------------------%

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

%------------------------------------------------------------------------%
% Handle of Widening                                                     |
%------------------------------------------------------------------------%
% * Widening or not (off, amgu, plai_op)                                 | 
% - off:  no widening                                                    |
% - plai_op: widening is performed for each PLAI operation (if required) |
% - amgu: widening is performed for each amgu                            |
:- export(widen/1).
widen(X):- current_pp_flag(clique_widen,X).

% * Thresholds. These thresholds are used by the condition of the        |
% widening the simpler widenings only used 'widen_upper_bound'. Some     |
% more complex widenings also use 'widen_lower_bound'.                   |
:- export(widen_upper_bound/1).
widen_upper_bound(X):- current_pp_flag(clique_widen_ub,X).
:- export(widen_lower_bound/1).
widen_lower_bound(X):- current_pp_flag(clique_widen_lb,X).

:- export(type_widening/1).
% * Types of widenings. This clasification was defined by Zaffanella,Hill|
% and Bagnara.                                                           |
% - panic: They are at the top of the scale of widenings and they must be|
% used with very strict guards, only to obey the 'never crash' motto.    |
% - cautious: they're invariant wrt set-sharing representation.          |
% - intermediate: tradeoff between precision and efficiency.             |
% W(cl,sh) = (cl U {Ush},\emptyset)     panic_1                          |
% W(cl,sh) = ({Ucl U Ush},\emptyset)    panic_2                          |
% W(cl,sh) = (cl U sh,\emptyset)        inter_1                          |
% W(cl,sh) = normalize((cl,sh))         cautious                         |
% W((cl,sh),LB) =                       inter_2                          |        
%           1) choose the candidate with the greatest number of subsets  |
%              if not more candidates, end.                              |
%           2) update clique                                             |
%           3) compute (cl'+sh')                                         |
%           4) if (cl'+sh') =< lower_bound, end.                         |
%              otherwise goto 1.                                         |
type_widening(X):- current_pp_flag(clique_widen_type,X).

:- export(type_widening_condition/1).
% * Type of conditions.                                                  |
% - aamgu: the condition is verified after performing the amgu.          |
% - bamgu: an upper bound is computed before performing the amgu in order| 
%   to avoid to compute it. (default)                                    |
type_widening_condition(bamgu). 
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%           ABSTRACT UNIFICATION for CLIQUE-sharing domain (OPERATIONS)  |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% amgu_clique(+,+,+,+,-)                                                 |
% amgu_clique_(X,T,Flag,State,AMGU)                                      |
% If Flag = star then if performs the "star" amgu                        |
% Otherwise, it performs the "self-union" amgu (non-redundant)           |   
%------------------------------------------------------------------------%
amgu_clique(X,T,star,ASub,ASub0):- !,        
	amgu_clique_opt(X,T,ASub,ASub0).
amgu_clique(X,T,self,ASub,ASub0):-           
	amgu_s_clique(X,T,ASub,ASub0).

%------------------------------------------------------------------------%
%                OPTIMIZED UNIFICATION FOR CLIQUE-SHARING                |
%------------------------------------------------------------------------%
% amgu_clique_opt(+,+,+,-)                                               |
% amgu_clique_opt(V_x,X,V_t,State,AMGU)                                  |
% Amgu describes the unification x=t (concrete unification) in a state   |
% described by S                                                         |
% amgu_clique_opt(x=t,(cl,sh)) =                                         |
%   (cl, \sh_xt U (sh_x* bin sh_t*))   if cl_x = cl_t = empty            |
%   (\rel(xt,cl), \sh_xt)              if cl_x = sh_x = empty            |
%                                      or cl_t = sh_t = empty            | 
%   (\rel'(xt,cl) U {U (cl_x U cl_t U sh_x U sh_t)}, \sh_xt)             |
%                                      otherwise                         |
% where \rel'(xt,cl) = {c | c \in cl, c /\ vars(xt) = \emptyset          |
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
:- push_prolog_flag(discontiguous_warnings,off).
amgu_clique_opt(X,T,ASub,AMGU):-           
	widen(amgu),!,
	amgu_clique_opt(X,T,ASub,not,AMGU).
amgu_clique_opt(X,T,(Cl,Sh),NewCall,AMGU):-
	amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),
	                      Irrel_Sh_xt),!,
	( (Cl_x = [], Cl_t = []) ->
	   ( NewCall == not ->
	     ExtraInfo = (Irrel_Sh_xt,Sh_x,Sh_t),
	     share_clique_widen(amgu,(Cl,Sh),ExtraInfo,New_ASub),
	     amgu_clique_opt(X,T,New_ASub,yes,New_AMGU),
	     AMGU = New_AMGU
	   ; 	     
	     amgu_sharing_part(Irrel_Sh_xt,Sh_x,Sh_t,AMGU_sh),
             AMGU = (Cl,AMGU_sh)
	   )           
        ;
	   ( ((Cl_x = [], Sh_x = []) ; (Cl_t = [], Sh_t = [])) -> 
	       delete_vars_from_list_of_lists(V_xt,Cl,Irrel_Cl_xt),
	       AMGU = (Irrel_Cl_xt,Irrel_Sh_xt)
	   ;
	       ord_union(Cl_x,Cl_t,Cl_xt),
	       ord_union(Sh_x,Sh_t,Sh_xt),
	       merge_list_of_lists(Cl_xt,Cl_var),
	       merge_list_of_lists(Sh_xt,Sh_var),
	       ord_union(Cl_var,Sh_var,ClSh_var),
	       list_if_not_nil(ClSh_var,ClSh0_var),
	       split_list_of_lists(V_xt,Cl,_,Irrel_Cl0_xt),
	       ord_union(Irrel_Cl0_xt,ClSh0_var,AMGU_Cl),
	       AMGU = (AMGU_Cl,Irrel_Sh_xt)            
           )
       ).
% \+(widen(amgu))
amgu_clique_opt(X,T,(Cl,Sh),AMGU):- !,     

	amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),Irrel_Sh_xt),!,
	( (Cl_x = [], Cl_t = []) ->
	    amgu_sharing_part(Irrel_Sh_xt,Sh_x,Sh_t,AMGU_sh),
	    AMGU = (Cl,AMGU_sh)
	;
	   ( ((Cl_x = [], Sh_x = []) ; (Cl_t = [], Sh_t = [])) -> 
	     delete_vars_from_list_of_lists(V_xt,Cl,Irrel_Cl_xt),
	     AMGU = (Irrel_Cl_xt,Irrel_Sh_xt)
	   ;
	     ord_union(Cl_x,Cl_t,Cl_xt),
	     ord_union(Sh_x,Sh_t,Sh_xt),
	     merge_list_of_lists(Cl_xt,Cl_var),
	     merge_list_of_lists(Sh_xt,Sh_var),
	     ord_union(Cl_var,Sh_var,ClSh_var),
	     list_if_not_nil(ClSh_var,ClSh0_var),
	     split_list_of_lists(V_xt,Cl,_,Irrel_Cl0_xt),
	     ord_union(Irrel_Cl0_xt,ClSh0_var,AMGU_Cl),
	     AMGU = (AMGU_Cl,Irrel_Sh_xt)            
	   )
	).

:- pop_prolog_flag(discontiguous_warnings).
:- pop_prolog_flag(multi_arity_warnings).

amgu_rel_non_rel_info(X,T,V_xt,ASub,(Cl_x,Sh_x),(Cl_t,Sh_t),Irrel_Sh_xt):-
	sort(T,V_t),
	ord_union([X],T,V_xt),
	share_clique_sort(ASub,(Cl,Sh)),
	split_list_of_lists([X],Cl,Cl_x,_),
	split_list_of_lists(V_t,Cl,Cl_t,_),
	split_list_of_lists([X],Sh,Sh_x,_),
	split_list_of_lists(V_t,Sh,Sh_t,_),
	split_list_of_lists(V_xt,Sh,_,Irrel_Sh_xt).

amgu_sharing_part(Irrel_Sh_xt,Sh_x,Sh_t,AMGU_sh):-
	star(Sh_x,S_Sh_x),
	star(Sh_t,S_Sh_t),
	bin_union(S_Sh_x,S_Sh_t,BinUnion_xt),
	ord_union(Irrel_Sh_xt,BinUnion_xt,AMGU_sh).

%------------------------------------------------------------------------%
%          ABSTRACT UNIFICATION with SELF UNION FOR CLIQUES              | 
%------------------------------------------------------------------------%
% amgu_s_clique_(+,+,+,-)                                                |
% amgu_s_clique(X,V_t,ASub,AMGU)                                         |
% Amgu describes the unification x=t (concrete unification) in a state   |
% described by S.                                                        |
% amgu_s_clique(x=t,(cl,sh)) = irrel_w(xt,shw) U^w                       |
%                    bin^w(sbin^w(rel^w(V_x,shw)),sbin^w(rel^w(V_t,shw)))|
% Note that in this operation, we use Bagnara's definition.              | 
%------------------------------------------------------------------------%
amgu_s_clique(X,T,ASub,AMGU):-           
% Both clique and sharing part are computed together
	sort(T,V_t),
	share_clique_sort(ASub,SASub),
	ord_union([X],V_t,Vxt), 
	irrel_w(Vxt,SASub,Irrel),
	rel_w([X],SASub,Rel_x),
	rel_w(V_t,SASub,Rel_t),
	self_w(Rel_x,Self_Rel_x),
	self_w(Rel_t,Self_Rel_t),
	bin_union_w(Self_Rel_x,Self_Rel_t,SH0),
	ord_union_w(Irrel,SH0,AMGU).
	
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      BINARY UNION FOR CLIQUE SETS                      %
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% bin_union_w(+,+,-)                                                     |
% bin_union_w(SH1,SH2,Cl)                                                |
% bin_union_w((cl1,sh1),(cl2,sh2)) = (bin_union(cl1,cl2) U               |
%                                     bin_union(cl1,sh2) U               |
% 				bin_union(sh1,cl2),bin_union(sh1,sh2))   |
%------------------------------------------------------------------------%
bin_union_w((Cl1,Sh1),(Cl2,Sh2),Bin):-
	bin_union(Cl1,Cl2,Cl3),
	bin_union(Cl1,Sh2,Cl4),
	bin_union(Sh1,Cl2,Cl5),
	ord_union(Cl3,Cl4,Cl6),
	ord_union(Cl5,Cl6,Cl7),
	bin_union(Sh1,Sh2,Sh3),
	Bin = (Cl7,Sh3).
	
%------------------------------------------------------------------------%
%                      STAR UNION FOR CLIQUE SETS                        % 
%------------------------------------------------------------------------%
% star_w(+,-)                                                            |
% star_w(Xss,Star)                                                       |
% Star is the closure under union of Xss                                 |
% NON-OPTIMIZED version                                                  |
% star_w((cl,sh)) = (cl* U bin_union(cl*,sh*),sh*)                       |
% NOTE: Optimized version DOES normalize                                 |
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).
:- push_prolog_flag(discontiguous_warnings,off).


star_w(SH,SH_s):-
	widen(amgu),!,
	star_w(SH,not,SH_s).
star_w(([],Sh),NewCall,SH_s):-!,
	(  NewCall == not ->
	   ExtraInfo = ([],Sh,[[_]]),
	   share_clique_widen(amgu,([],Sh),ExtraInfo,New_ASub),	   
  	   star_w(New_ASub,yes,SH_s)
        ;  
	   star(Sh,Sh_s),
	   SH_s = ([],Sh_s)
        ).
star_w((Cl,Sh),_,SSH):-!,
	merge_list_of_lists(Cl,Cl_Vars),
	merge_list_of_lists(Sh,Sh_Vars),
	ord_union(Cl_Vars,Sh_Vars,Vars),
	list_if_not_nil(Vars,New_Cl),
	SSH = (New_Cl,[]).

% \+(widen(amgu))
star_w(([],[]),([],[])):-!.
star_w((Cl,[]),(S_Cl,[])):-!,
	merge_list_of_lists(Cl,S_Cl0),
	list_if_not_nil(S_Cl0,S_Cl).
star_w(([],Sh),SH):-
	star(Sh,SSh),
	% for correctness (extend)
	 share_clique_normalize(([],SSh),SH).
	%SH= ([],SSh).
star_w((Cl,Sh),SSH):-!,
	merge_list_of_lists(Cl,Cl_Vars),
	merge_list_of_lists(Sh,Sh_Vars),
	ord_union(Cl_Vars,Sh_Vars,Vars),
	list_if_not_nil(Vars,New_Cl),
	SSH = (New_Cl,[]).

:- pop_prolog_flag(discontiguous_warnings).
:- pop_prolog_flag(multi_arity_warnings).

list_if_not_nil([],[]).
list_if_not_nil(X,[X]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      SELF-BIN  UNION FOR CLIQUES                       %
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% self_w(+,-)                                                            |
% self_w(S1,S)                                                           |
% Bagnara's definition                                                   |
% Version of binary union of sharing is non-redundant w.r.t. pair-sharing|
% sel_bin_w((Cl,Sh)) = (Cl^+ U bin_union(Cl,Sh),Sh^+)                    |
%------------------------------------------------------------------------%
self_w((Cl,Sh),(Cl1,Sh0)):- 
	self(Cl,Cl0),
	self(Sh,Sh0),
	bin_union(Cl,Sh,BU),
	ord_union(Cl0,BU,Cl1).

%------------------------------------------------------------------------%
%                        UNION FOR CLIQUE SETS                           % 
%------------------------------------------------------------------------%
% ord_union_w(+,+,-)                                                     |
% ord_union_w(SH1,SH2,SH)                                                |
% ord_union_w((Cl1,Sh1),(Cl2,Sh2)) = (Cl1 U Cl2,Sh1 U Sh2)               |
%------------------------------------------------------------------------%
ord_union_w((Cl1,Sh1),(Cl2,Sh2),(Cl0,Sh0)):-
	ord_union(Sh1,Sh2,Sh0),
	ord_union(Cl1,Cl2,Cl0).

%------------------------------------------------------------------------%
%                 INTERSECTION FOR CLIQUE SETS                           % 
%------------------------------------------------------------------------%
% ord_intersection_w(+,+,-)                                              |
% ord_intersection_w((Cl1,Sh1),(Cl2,Sh2)) = (Cl1 /\^w Cl2, Cl1 /\^w Sh2  |
%                                            U Cl2 /\^w Sh1 U Sh1 /\ Sh2)|
%------------------------------------------------------------------------%
ord_intersection_w((Cl1,Sh1),(Cl2,Sh2),(Cl0,Sh0)):-
	intersection_list_of_lists(Cl1,Cl2,Cl0),
 	intersection_list_of_lists(Cl1,Sh2,Int0),
 	intersection_list_of_lists(Cl2,Sh1,Int1),
	ord_intersection(Sh1,Sh2,Int2),
 	ord_union(Int0,Int1,Int3),
 	ord_union(Int2,Int3,Sh0).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%             RELEVANT AND NON-RELEVANT INFORMATION FOR CLIQUES          %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% rel_w(+,+,-)                                                           |
% rel_w(Vars,SH,Rel)                                                     |
% Rel is the extraction of the relevant component of cl and sh wrt Vars. |
% rel_w(Vars,(cl,sh)) = (rel(V,cl),rel(V,sh))                            |
%------------------------------------------------------------------------%
% irrel_w(+,+,-)                                                         |
% irrel_w(Vars,SH,Irrel)                                                 |
% Irrel is is the exclusion of the irrelevant component of cl and sh wrt |
% Vars.                                                                  |
% Note that a new predicate to compute irrelevant component of cl is     |
% required.                                                              |
% irrel_w'(V,cl) = {C \ V | C in cl} \ empty_set                         |
%------------------------------------------------------------------------%
rel_w(_,'$bottom','$bottom').
rel_w(Vars,(Cl,Sh),(Cl0,Sh0)):- 
 	split_list_of_lists(Vars,Sh,Sh0,_),
 	split_list_of_lists(Vars,Cl,Cl0,_).

irrel_w(_,'$bottom','$bottom').
irrel_w(Vars,(Cl,Sh),(Cl0,Sh0)):-
	split_list_of_lists(Vars,Sh,_,Sh0),
	delete_vars_from_list_of_lists(Vars,Cl,Cl0).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                         NORMALIZE  Cliques                             | 
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% share_clique_normalize(+,+,+,-)                                        |
% share_clique_normalize(SH,T,M,SH1)                                     |
% There are three kind of possible transformations:                      |
% -Regularization: clique which are subset of other cliques              |
% -Minimization: sharing sets that are contained in cliques              |
% -Normalization: sharing sets that are a powerset and so, a clique      |
%   sharing sets with cardinality less than M are not taken into account |
%   so that they are moved to clique part.                               |  
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).
share_clique_normalize(CL,NCL):-
	widen(off),!,
 	minimum_cardinality(M),
 	share_clique_normalize(CL,100,M,NCL).
share_clique_normalize(CL,CL):- !.

%------------------------------------------------------------------------%
% NOTE: This interface should only be used directly by predicates which  |
% need the normalization for either correctness (i.e. extend,            |
% less_or_equal,..) or as a widening.                                    |
%------------------------------------------------------------------------%
share_clique_normalize('$bottom',_,_,'$bottom').
share_clique_normalize((Cl,Sh),T,M,(Cl2,Sh2)):-
	eliminate_redundancies((Cl,Sh),(Cl1,Sh1)),
	normalize((Cl1,Sh1),T,M,(Cl2,Sh2)).
:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
% eliminate_redundancies(+,-)                                            |
% eliminate_redundancies(SH,NewSH)                                       |
% Performs the following process:                                        |
% - regularize                                                           |
% - minimize                                                             |
% - move those clique groups with cardinality 1 to the sharing part      |
% Note that it does not normalize.                                       |
% REMARK: if we use move_clique2sharing qplan doesn't run with           |
% share_clique. Thus, it should only used with freeness                  |
%------------------------------------------------------------------------%
eliminate_redundancies('$bottom','$bottom'):-!.
eliminate_redundancies((Cl,Sh),(Cl2,Sh2)):-!,
	% this reduce # program points
%	move_clique_to_sharing(Cl,Sh,Cl1,Sh1), 
	Cl = Cl1, Sh = Sh1,
	regularize(Cl1,Cl2),                 
	minimize(Sh1,Cl2,Sh2).

%------------------------------------------------------------------------%
% move_clique_to_sharing(+,+,-,-)                                        |
% move_clique_to_sharing(Cl,Sh,NewCl,NewSh)                              |
% Eliminates those clique groups that satisfy a property (e.g. singleton)|
% and moves them to the sharing compoonent.                              |
%------------------------------------------------------------------------%
move_clique_to_sharing(Cl,Sh,NewCl,NewSh):-
	move_clique_to_sharing_(Cl,NewCl,Sh1),
	add_one(Sh1,Sh,NewSh).

move_clique_to_sharing_([],[],[]).
move_clique_to_sharing_([C|Cs],NewCl,[C|Sel1]):-
	one(C),!,
	move_clique_to_sharing_(Cs,NewCl,Sel1).
move_clique_to_sharing_([C|Cs],[C|NewCl],Sel1):-!,
	move_clique_to_sharing_(Cs,NewCl,Sel1).

% move_clique_to_sharing(Cl,Sh,NewCl,NewSh):-
% 	move_clique_to_sharing_(Cl,NewCl,Sh1,Sh2),
% 	add_one(Sh1,Sh,NewSh1),
% 	add_two(Sh2,NewSh1,NewSh).

% move_clique_to_sharing_([],[],[],[]).
% move_clique_to_sharing_([C|Cs],NewCl,[C|Sel1],Sel2):-
% 	one(C),!,
% 	move_clique_to_sharing_(Cs,NewCl,Sel1,Sel2).
% move_clique_to_sharing_([C|Cs],NewCl,Sel1,[C|Sel2]):-
% 	two(C),!,
% 	move_clique_to_sharing_(Cs,NewCl,Sel1,Sel2).
% move_clique_to_sharing_([C|Cs],[C|NewCl],Sel1,Sel2):-!,
% 	move_clique_to_sharing_(Cs,NewCl,Sel1,Sel2).

one([_]):- !.
%two([_,_]):- !.

add_one(Xs,Ys,Zs):-
	ord_union(Xs,Ys,Zs).
% add_two(Xs,Ys,Zs):-
% 	powerset_lists(Xs,Xss,Ys),
% 	sort_list_of_lists(Xss,Zs).

% powerset_2([X,Y],[[X],[X,Y],[Y]]).

% powerset_lists([],Res,Res).
% powerset_lists([X|Xs],NewTemp,Res):-
% 	powerset_2(X,XP),
% 	powerset_lists(Xs,Tem,Res),
% 	ord_union(XP,Tem,NewTemp).

%------------------------------------------------------------------------%
% regularize(+,-)                                                        |
% regularize(Cl,NewCl)= Cl \ {c \in Cl|c is down-redundant for Cl}       |
% Complexity = |Cl|.|Cl|                                                 |
% Removes down-redundant cliques                                         |
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
regularize(Cl,Cl_Reg_s):-	
	neg_length_list_of_lists(Cl,1,Cl_list),
	sort(Cl_list,Cl_list_s), % eliminate duplicates
	regularize(Cl_list_s,[],Cl_Reg),
	sort_list_of_lists(Cl_Reg,Cl_Reg_s).

regularize([],Reg,Reg).
regularize([_-X|Xs],Temp,Reg  ):-
	( set_included_set_of_sets(Temp,X) ->   
	  regularize(Xs,Temp,Reg)
        ;
	  regularize(Xs,[X|Temp],Reg)  
        ). 
:- pop_prolog_flag(multi_arity_warnings).	  

set_included_set_of_sets([],_):- !,fail.
set_included_set_of_sets([X|_],S):-
	ord_subset(S,X),!.
set_included_set_of_sets([_|Xs],S):-
	set_included_set_of_sets(Xs,S).

%------------------------------------------------------------------------%
% minimize(+,-)                                                          |
% minimize(Sh,Cl) = Sh \ {s | s \subseteq cl, cl \in Cl,s \in Sh}        |
% Complexity = |Sh|.|Cl|                                                 |
% Removes sharing groups that are subset of cliques sets                 |  
%------------------------------------------------------------------------%
minimize([],_,[]).
minimize([Sh|Shs],Cl,Sh1):-
	( ord_subset_lists_with_list(Cl,Sh) ->
	  minimize(Shs,Cl,Sh1)
        ;
	  minimize(Shs,Cl,Sh0),	  
	  Sh1 = [Sh|Sh0]
        ).

%------------------------------------------------------------------------%
% normalize(+,+,+,-)                                                     |
% normalize(SH,T,M,SH1)                                                  |
% Moves all sharing sets which contain T% of the clique from the sharing |
% part to the clique part. M is the minimum cardinality                  |
% The complexity is NP-complete (maximal clique in an undirected graph)  |
%------------------------------------------------------------------------%

:- use_package(datafacts).
:- data norma_done/0.

:- push_prolog_flag(multi_arity_warnings,off).
	
% normalize/4: Th is between [0,100]
normalize(SH,T,M,SH1):-
	check_threshold(T,NT),
	normalize(SH,NT,M,SH1,_).

% normalize_/5: Th is between [0.0,1.0]
normalize((Cl,Sh),Th,M,SH1,Continue):-	
	process_candidate((Cl,Sh),Th,M,SH,Continue),!,
	( var(Continue) ->   % It there may be more candidates	  
	    asserta_fact(norma_done),
	    normalize(SH,Th,M,SH1,Continue)
        ; 
	  Continue = not,    % there are not more candidates
          SH1 = (Cl,Sh)
        ).
:- pop_prolog_flag(multi_arity_warnings).

process_candidate((Cl,Sh),Th,M,SH,_):-	
	longest_candidate(Sh,M,CardCand,Cand,Info),
	Info = yes,
	sublist_list_of_lists(Sh,Cand,CardCandSh,CandSh),
	number_sets_in_cliques(Cl,Cand,CardCandCl),
	( is_powerset(CardCand,CardCandSh,CardCandCl,Th) ->
          update_clique(Cand,(Cl,Sh),CandSh,SH)	
	;
          fail % provoke backtraking in order to obtain other candidate
	       % if the previous candidate is not correct
	).
process_candidate(SH,_,_,SH,not).  % there are not more candidates

update_clique(Cand,(Cl,Sh),CandSh,SH):-
	% Removes set-sharing included in the new clique	
        delete_list_of_lists(Sh,CandSh,Sh1),
	% Removes subcliques of the new clique (regularize in the algorithm) 
	nosublist_list_of_lists(Cl,Cand,Cl1), 
	share_clique_sort(([Cand|Cl1],Sh1),SH).

is_powerset(CardCand,CardCandSh,CardCandCl,Threshold):- 
	number_of_subsets(CardCand,CardPws),
	Limit is Threshold * CardPws,
	TotalSubsets is CardCandSh + CardCandCl,
	TotalSubsets >= Limit.

%------------------------------------------------------------------------%
% number_sets_in_cliques(CL,Cand,J)                                      |
% J is the number of subsets which cannot appear in sh because           |
% they are already represented in cl.                                    |
%------------------------------------------------------------------------%
number_sets_in_cliques(CL,Cand,J):-
	intersection_lists_with_list(CL,Cand,I),
	length(I,End),
	compute_inc_exc(I,1,End,plus,0,J).

%------------------------------------------------------------------------%
% Principle of inclusion-exclusion                                       |
% | A_1 U A_2 U...U A_n| =  Sum_1=<i=<p |A_i| -                          |
%  Sum_1=<i_1 =<i_2=<p |A_i1 /\ A_i2|+...+(-1)^p-1 | A_1 /\ A_2 /\...A_n||
%------------------------------------------------------------------------%
compute_inc_exc(_,Start,End,_,J,J):-
	Start > End, !.
compute_inc_exc(I,Start,End,Sig,Acc,J):-
	bagof(S,
	      comb(Start,I,S),
	      Combs),
	intersect_all(Combs,Int),
	sum_cliques(Int,0,Val),
	( Sig = plus ->
	  NSig = minus,
	  NAcc is  Acc + Val
        ;
	  NSig = plus,
	  NAcc is  Acc - Val
        ),
	Next is Start + 1,
	compute_inc_exc(I,Next,End,NSig,NAcc,J).

% comb(L,K,Combs)
% Combs is all possible combinations of the list L taken K at the same time
comb(0,_,[]) :- !.
comb(N,[X|T],[X|Comb]):-N>0,N1 is N-1,comb(N1,T,Comb).
comb(N,[_|T],Comb):-N>0,comb(N,T,Comb).

sum_cliques([],Acc,Acc).
sum_cliques([C|Cs],Acc,Res):-
	card_clique(C,N),
	NAcc is Acc + N,
	sum_cliques(Cs,NAcc,Res).

card_clique(S,N1):-
	length(S,N),!,
	number_of_subsets(N,N1).

number_of_subsets(N,N1):-
	N0 is 2**N,
	N1 is N0 - 1.

intersect_all(Xss,Int):-
	sort_list_of_lists(Xss,Xss1),
	intersect_all_(Xss1,Int).

intersect_all_([],[]).
intersect_all_([Xs|Xss],[Int|Res]):-
	ord_intersect_all(Xs,Int),
	intersect_all_(Xss,Res).

%------------------------------------------------------------------------%
% longest_candidate(S,LB,Card,Max,Info)                                  |
% longest_candidate(+,+,-,-,-)                                           |
% Max is the set with the maximum cardinality Card > LB (lower bound)    |
% of the list of lists                                                   |
% complexity: |Sh| log (|Sh|)
%------------------------------------------------------------------------%
longest_candidate(Sh,LB,Card,Max,Info):-
	neg_length_list_of_lists(Sh,LB,PairList),
	PairList \== [],!,
	Info = yes,
	sort(PairList,PairList_s),
	select(NegCard-Max,PairList_s,_),
	Card is 0 - NegCard.
longest_candidate(_,_,_,_,Info):-
	Info = not.

%------------------------------------------------------------------------%
% smallest_candidate(S,UB,Card,Min,Info)                                 |
% smallest_candidate(+,+,-,-,-)                                          |
%------------------------------------------------------------------------%
smallest_candidate(Sh,LB,Card,Min,Info):-
	pos_length_list_of_lists(Sh,LB,PairList),
	PairList \== [],!,
	Info = yes,
	sort(PairList,PairList_s),
	select(Card-Min,PairList_s,_).
smallest_candidate(_,_,_,_,Info):-
	Info = not.

% complexity: |Sh|
neg_length_list_of_lists([],_,[]).
neg_length_list_of_lists([S|Ss],M,Ss1):-
	length(S,L0),!,
	( L0 >= M ->   
	  L is 0 - L0,
	  neg_length_list_of_lists(Ss,M,R),
	  Ss1= [L-S|R]
	;
	  neg_length_list_of_lists(Ss,M,R),
	  Ss1= R
        ).

pos_length_list_of_lists([],_,[]).
pos_length_list_of_lists([S|Ss],M,Ss1):-
	length(S,L),!,
	( L >= M ->   
	  pos_length_list_of_lists(Ss,M,R),
	  Ss1= [L-S|R]
	;
	  pos_length_list_of_lists(Ss,M,R),
	  Ss1= R
        ).

%------------------------------------------------------------------------%
% minimum_cardinality(+).                                                |
% minimum_cardinality(M)                                                 |
% sharing sets with cardinality less than M are not taken into account   |
% so that they are moved to clique part. (see normalization algorithm)   |  
%------------------------------------------------------------------------%
minimum_cardinality(3).

check_threshold(T,Res):-
	between(0,100,T),
	Res is T /100.
	
% This predicate is used for tests. For this, it is necessary to 
% export it.
 
card_cliques(Cl,J):-
	length(Cl,End),
	compute_inc_exc(Cl,1,End,plus,0,J).

number_of_norma(N):-
	findall(norma_done,norma_done,L),
	length(L,N),
	retractall_fact(norma_done).
clean_number_of_norma:-
	retractall_fact(norma_done).
