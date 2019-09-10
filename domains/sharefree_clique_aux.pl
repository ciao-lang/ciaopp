:- module(sharefree_clique_aux,
	[ sharefree_clique_iterate/3,
	  amgu_clique_ff/4,   %% by obtain_prime_clique_var_var/3
	  sharefree_clique_update_freeness/4 %% by call2entry/8
        ],
	[assertions, isomodes]).

:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the amgu for clique-sharing+Freeness domain       |
% defined by Hill, Bagnara and Zaffanella (for bottom-up analysis and    |
% inferring pair-sharing). This version (for top-down analysis and for   |
% inferring sharing) is defined by J.Navas, F.Bueno and M.Hermenegildo.  |
%------------------------------------------------------------------------%

:- doc(bug,"1. The amgu does not use linearity information").
:- doc(bug,"2. The amgu for supporting linearity information is 
	        implemented but it does not support widening.").

:- use_module(library(sort), [sort/2]).
:- use_module(library(sets), [ord_subtract/3,	ord_member/2, ord_union/3]).
:- use_module(library(lsets), [merge_list_of_lists/2]).
:- use_module(domain(share_amgu_sets),
        [split_list_of_lists/4, delete_vars_from_list_of_lists/3]).
:- use_module(domain(share_amgu_aux), [bin_union/3]).
:- use_module(domain(sharing_clique), [share_clique_widen/4]). % amgu&star 
:- use_module(domain(s_grshfr), [member_value_freeness/3]).
:- use_module(domain(share_clique_aux)).
:- use_module(domain(sharefree_amgu_aux), 
	[map_freeness_list/3, unmap_freeness_list/2]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                            ABSTRACT Iterate                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_iterate(+,+,-)                                        %
% sharefree_clique_iterate(Eqs,ASub0,ASub)                               %
%------------------------------------------------------------------------%
sharefree_clique_iterate([],ASub, ASub).
sharefree_clique_iterate([(X,(Ts,Type,L))|Eqs],ASub, ASub2):-
     amgu_shfr_clique(X,(Ts,Type,L),ASub,ASub1),
     sharefree_clique_iterate(Eqs,ASub1, ASub2).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%               ABSTRACT UNIFICATION CLIQUE-SHARING+FREENESS             |
%------------------------------------------------------------------------%
% amgu_shfr_clique(+,+,+,-)                                              |
% amgu_shfr_clique(X,T,((Cl,Sh),f),SHF')                                 |   
%------------------------------------------------------------------------%
amgu_shfr_clique(X,(T,Type,L),(SH,F),(SH1,F1)):-
     member_value_freeness(F,Free_Vars0,f),
     sort(Free_Vars0,Free_Vars),
     amgu_shfr_clique_(X,(T,Type,L),(SH,Free_Vars),(SH1,F1)).
%------------------------------------------------------------------------%

amgu_shfr_clique_(X,(T,Type,_),(SH,F),(SH0,F0)):-
     ord_member(X,F),!,  
%% sharing
     % CASE 1: x or t is free 
     amgu_clique_ff(X,T,SH,SH0),
%% freeness
     ( ((Type == v), T = [T1], ord_member(T1,F)) ->
	% x in f, t in f (1)
        F1 = F
     ;  % x in f, t not in f (2)  
	update_clique_freeness([X],SH,F,F1) 
     ),     
     map_freeness_list(F1,f,F0).
amgu_shfr_clique_(X,([T],v,_),(SH,F),(SH0,F0)):-
     ord_member(T,F),!,
%% sharing
     % CASE 1: x or t is free 
     amgu_clique_ff(X,[T],SH,SH0),
%% freeness
     % CASE 3: x not in f, t in f	
     update_clique_freeness([T],SH,F,F1),
     map_freeness_list(F1,f,F0).
% amgu_shfr_clique_(X,(T,_,l),(SH,F),(SH0,F0)):-
% %% sharing
%      % CASE 2: x not in f, t not in f but t is linear
%      alin_wf(T,SH,F),!, 
%      amgu_clique_fl(X,T,SH,SH0),
% %% freeness
%      % CASE 4: x not in f, t not in f	
%      ord_union([X],T,X_union_T),
%      update_clique_freeness(X_union_T,SH,F,F1),
%      map_freeness_list(F1,f,F0).
amgu_shfr_clique_(X,(T,_,_),(SH,F),(SH0,F0)):-
%% sharing
     % CASE 3: otherwise	
     %flag_redundant(Flag),!,
     amgu_clique(X,T,star,SH,SH0),
%% freeness
     % CASE 4: x not in f, t not in f	
     ord_union([X],T,X_union_T),
     update_clique_freeness(X_union_T,SH,F,F1),
     map_freeness_list(F1,f,F0).

%% %  alin_wf(T,(Sh,Cl),F) iff t \subseteq F and lin(Sh,T) and lin(Cl,T)
%% alin_wf(T,(Sh,Cl),F):-
%%      sort(T,Ts),
%%      ord_subset(Ts,F),
%%      lin(Sh,Ts),
%%      lin(Cl,Ts).

%------------------------------------------------------------------------%
% amgu_clique_ff(+,+,+,-)                                                |
% amgu_clique_ff(V_x,X,V_t,State,AMGU)                                   |
% x or t free                                                            |
%------------------------------------------------------------------------%
% amgu_clique_ff(x=t,(cl,sh)) =                                          |
% (cl                                                                    |
% , \nrel(xt,sh) U (sh_x \bin sh_t))   if cl_x = cl_t = empty            |
%                                                                        |
% (\nrel(xt,cl)                                                          |
% , \nrel(xt,sh))                      if cl_x = sh_x = empty or         |
%                                         cl_t = sh_t = empty            |
% (\nrel(xt,cl) U                                                        | 
% ((cl_x U sh_x) \bin cl_t) U          otherwise                         |
%  (cl_x \bin sh_t)                                                      |
% , \nrel(xt,sh) U (sh_x \bin sh_t))                                     |
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
:- push_prolog_flag(discontiguous_warnings,off).

amgu_clique_ff(X,T,ASub,AMGU):-           
	widen(amgu),!,
	amgu_clique_ff(X,T,ASub,not,AMGU).  	
amgu_clique_ff(X,T,(Cl,Sh),NewCall,AMGU):-
	amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),
	                      Irrel_Sh_xt),!,
	( (Cl_x = [], Cl_t = []) ->
	   ( NewCall == not ->
	     ExtraInfo = (Irrel_Sh_xt,Sh_x,Sh_t),
	     share_clique_widen(amgu,(Cl,Sh),ExtraInfo,New_ASub),
	     amgu_clique_ff(X,T,New_ASub,yes,New_AMGU),
	     AMGU = New_AMGU
	   ; 
	     bin_union(Sh_x,Sh_t,BinUnion_xt),
	     ord_union(Irrel_Sh_xt,BinUnion_xt,AMGU_sh),
	     AMGU = (Cl,AMGU_sh)
	   )           
        ;
	   ( ((Cl_x = [], Sh_x = []) ; (Cl_t = [], Sh_t = [])) -> 
	       delete_vars_from_list_of_lists(V_xt,Cl,Irrel_Cl_xt),
	       AMGU = (Irrel_Cl_xt,Irrel_Sh_xt)
	   ;
% 	     % if type_widening_condition == bamgu and NewCall == not 
% 	   ( (type_widening_condition(bamgu), NewCall == not) ->
% 	     ExtraInfo = (Irrel_Sh_xt,Sh_x,Sh_t),
% 	     share_clique_widen(amgu,(Cl,Sh),ExtraInfo,New_ASub),
% 	     amgu_clique_ff(X,T,New_ASub,yes,AMGU)
% 	   ; % NewCall == yes or type_widening_condition(aamgu)
	     % clique part  
	     ord_union(Cl_x,Sh_x,ClSh_x),
	     bin_union(ClSh_x,Cl_t,ClSh_x_Cl_t),
	     bin_union(Cl_x,Sh_t,ClSh_xt),
	     ord_union(ClSh_x_Cl_t,ClSh_xt,Rel_Cl),
	     split_list_of_lists(V_xt,Cl,_,Irrel_Cl_xt),
	     ord_union(Irrel_Cl_xt,Rel_Cl,AMGU_Cl),
	     % sharing part  
	     bin_union(Sh_x,Sh_t,Sh_xt),
	     ord_union(Irrel_Sh_xt,Sh_xt,AMGU_Sh),
	     AMGU = (AMGU_Cl,AMGU_Sh)
% 	     ( type_widening_condition(aamgu) ->
% 	       share_clique_widen(amgu,(AMGU_Cl,AMGU_Sh),_,AMGU)
%              ; 
% 	       AMGU = (AMGU_Cl,AMGU_Sh)
%              )
%	   )           
	  %% more efficiency version (but less precise)
% 	  ord_union(Cl_x,Cl_t,Cl_xt),
% 	  ord_union(Sh_x,Sh_t,Sh_xt),
% 	  merge_list_of_lists(Cl_xt,Cl_var),
% 	  merge_list_of_lists(Sh_xt,Sh_var),
% 	  ord_union(Cl_var,Sh_var,ClSh_var),
% 	  list_if_not_nil(ClSh_var,ClSh0_var),
% 	  split_list_of_lists(V_xt,Cl,_,Irrel_Cl0_xt),
% 	  ord_union(Irrel_Cl0_xt,ClSh0_var,AMGU_Cl),
% 	  AMGU = (AMGU_Cl,Irrel_Sh_xt)            

           )
       ).
% widen(off)

amgu_clique_ff(X,T,(Cl,Sh),AMGU):- !,
	amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),
	                      Irrel_Sh_xt),!,
	( (Cl_x = [], Cl_t = []) ->
	    bin_union(Sh_x,Sh_t,BinUnion_xt),
	    ord_union(Irrel_Sh_xt,BinUnion_xt,AMGU_sh),
	    AMGU = (Cl,AMGU_sh)
	;
	   ( ((Cl_x = [], Sh_x = []) ; (Cl_t = [], Sh_t = [])) -> 
	     delete_vars_from_list_of_lists(V_xt,Cl,Irrel_Cl_xt),
	     AMGU = (Irrel_Cl_xt,Irrel_Sh_xt)
	   ;
	     % clique part  
	     ord_union(Cl_x,Sh_x,ClSh_x),
	     bin_union(ClSh_x,Cl_t,ClSh_x_Cl_t),
	     bin_union(Cl_x,Sh_t,ClSh_xt),
	     ord_union(ClSh_x_Cl_t,ClSh_xt,Rel_Cl),
	     split_list_of_lists(V_xt,Cl,_,Irrel_Cl_xt),
	     ord_union(Irrel_Cl_xt,Rel_Cl,AMGU_Cl),
	     % sharing part  
	     bin_union(Sh_x,Sh_t,Sh_xt),
	     ord_union(Irrel_Sh_xt,Sh_xt,AMGU_Sh),
	     AMGU = (AMGU_Cl,AMGU_Sh)
	   )
	).

:- pop_prolog_flag(discontiguous_warnings).
:- pop_prolog_flag(multi_arity_warnings).

%% %------------------------------------------------------------------------%
%% % amgu_clique_fl(+,+,+,-)                                                |
%% % amgu_clique_fl(V_x,X,V_t,State,AMGU)                                   |
%% % t is linear                                                            |
%% %------------------------------------------------------------------------%
%% % amgu_clique_fl(x=t,(cl,sh)) =                                          |
%% %                                                                        |
%% %   (\nrel(xt,cl)) U (cl_x \bin sh_t*),                                  |
%% %    \nrel(xt,sh) U (sh_x \bin sh_t*))            if cl_t = \empty       |
%% %                                                                        |
%% %   (\nrel(xt,cl)) U                                                     |
%% %    ((cl_x U sh_x) \bin {U(cl_t U sh_t)}) U                             |
%% %    (cl_x \bin sh_t*),                                                  |
%% %   \nrel(xt,sh))                                 otherwise              |
%% %------------------------------------------------------------------------%
%% % DOESN'T SUPPORT WIDENING !!!
%% %------------------------------------------------------------------------%
%% amgu_clique_fl(X,T,(Cl,Sh),AMGU):- !,
%% 	amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),
%% 	                     Irrel_Sh_xt),!,
%% 	( Cl_t = [] ->
%% 	  % clique part
%% 	  star(Sh_t,Sh_t_star),
%% 	  bin_union(Cl_x,Sh_t_star,Cl_x_bin_Sh_t_star),
%% 	  split_list_of_lists(V_xt,Cl,_,Irrel_Cl_xt),	  
%% 	  ord_union(Irrel_Cl_xt,Cl_x_bin_Sh_t_star,AMGU_Cl),
%%           % sharing part
%% 	  bin_union(Sh_x,Sh_t_star,Sh_x_bin_Sh_t_star),
%% 	  ord_union(Irrel_Sh_xt,Sh_x_bin_Sh_t_star,AMGU_Sh)
%% 	;
%% 	  % clique part  
%%   	  merge_list_of_lists(Sh_t,USh_t),     
%%   	  merge_list_of_lists(Cl_t,UCl_t),     
%%   	  ord_union(USh_t,UCl_t,UShCl_t),               % {U(cl_t U sh_t)}
%%           ord_union(Cl_x,Sh_x,Cl_x_union_Sh_x),         % (cl_x U sh_x) 
%%           bin_union(Cl_x_union_Sh_x,UShCl_t,Cl0),
%% 	  star(Sh_t,Sh_t_star),
%% 	  bin_union(Cl_x,Sh_t_star,Cl_x_bin_Sh_t_star), % (cl_x \bin sh_t*)
%% 	  ord_union(Cl_x_bin_Sh_t_star,Cl0,AMGU_Cl),
%% 	  % sharing part  
%% 	  AMGU_Sh = Irrel_Sh_xt
%% 	),
%% 	AMGU = (AMGU_Cl,AMGU_Sh).

% Returns only free variables (f)
update_clique_freeness(Vars,SH,F,F0):-
     share_clique_with(Vars,SH,Rel_Vars),
     ord_subtract(F,Rel_Vars,F0).

share_clique_with([],_,[]) :- !.
share_clique_with(Vars,SH,Result):- 
     rel_w(Vars,SH,(Rel_Cl,Rel_Sh)),
     merge_list_of_lists(Rel_Cl,Rel_Vars0),     
     merge_list_of_lists(Rel_Sh,Rel_Vars1),
     ord_union(Rel_Vars0,Rel_Vars1,Rel_Vars),!,
     (Rel_Vars == [] ->
      Result = Vars
     ;Result = Rel_Vars).	       

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      UPDATE FREENESS                                   % 
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_update_freeness(+,+,+,-)                              |
% sharefree_clique_update_freeness(Sh',f',Vars,Newf)                     |
%-------------------------------------------------------------------------
sharefree_clique_update_freeness((Cl,Sh),F,Vars,F1):-
     % ground variables
     merge_list_of_lists(Cl,Cl_Vars),
     merge_list_of_lists(Sh,Sh_Vars),
     ord_union(Cl_Vars,Sh_Vars,SH_Vars),
     ord_subtract(Vars,SH_Vars,G),
     map_freeness_list(G,g,G0),
     % non-free variables
     unmap_freeness_list(F,UF),
     ord_subtract(Vars,UF,NF0),
     ord_subtract(NF0,G,NF1),
     map_freeness_list(NF1,nf,NF),
     % union of all variables
     ord_union(F,G0,F0),
     ord_union(F0,NF,F1).
