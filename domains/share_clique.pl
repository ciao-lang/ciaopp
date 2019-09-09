/*             Copyright (C)2004-2005 UNM-CLIP				*/
:- module(share_clique, [], [assertions, isomodes]).

:- use_module(domain(share_amgu_sets)).
:- use_module(library(lsets), 
	       [sort_list_of_lists/2,
		ord_split_lists_from_list/4,
		merge_list_of_lists/2,
		ord_member_list_of_lists/2
		]).	  
:- use_module(library(sets), 
              [
	       ord_subset/2,
	       ord_subtract/3,
	       ord_union/3,
	       ord_intersection/3,
	       ord_member/2,
	       merge/3,
	       insert/3,
	       ord_intersection_diff/4
	       ]).
:- use_module(library(lists), 
              [delete/3,               
	       append/3,
	       powerset/2
	       ]).
:- use_module(library(sort), 
	      [sort/2]).	

:- include(sharing_clique).
:- include(sharefree_clique).
:- include(sharing_clique_1).
:- include(sharing_clique_def).
:- include(sharefree_clique_def).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

%------------------------------------------------------------------------%
% REMARK:                                                                |
% The normalization process is performed after call2entry and in the     |
% compute_lub. Also, for correctness in identical_abstract and           |
% less_or_equal.                                                         |
%------------------------------------------------------------------------%

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
widen_upper_bound(X):- current_pp_flag(clique_widen_ub,X).
widen_lower_bound(X):- current_pp_flag(clique_widen_lb,X).

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

:- use_module(domain(share_aux), [
	eliminate_couples/4,
	handle_each_indep/4,
	eliminate_if_not_possible/3,
	test_temp/2,
	eliminate_if_not_possible/4]).

:- use_module(domain(share_aux), [append_dl/3]).
