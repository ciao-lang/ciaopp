/*             Copyright (C)2004-2005 UNM-CLIP				*/
:- module(share_clique,
  	[ 	 
%clique+sharing
	  share_clique_call_to_entry/9,
	  share_clique_call_to_success_builtin/6,
	  share_clique_call_to_success_fact/9,
	  share_clique_call_to_prime_fact/6,
	  share_clique_exit_to_prime/7,            
	  share_clique_extend/4,                   
	  share_clique_glb/3,      
	  share_clique_input_user_interface/3,
	  share_clique_input_interface/4,
          share_clique_identical_abstract/2,
          share_clique_eliminate_equivalent/2,
	  share_clique_less_or_equal/2,
	  share_clique_compute_lub/2,
	  share_clique_lub_cl/3,
	  share_clique_asub_to_native/5, 
	  share_clique_project/3,                  
	  share_clique_sort/2,                     
	  share_clique_special_builtin/4,
	  share_clique_success_builtin/5,
	  share_clique_unknown_call/4,
	  share_clique_empty_entry/3,
	  share_clique_unknown_entry/3,
	  share_clique_extend_asub/3,
	  share_clique_widen/4,
	  share_clique_amgu/4,
	  compute_upper_amgu/2, % JN needed by sharedef.pl
%clique+sharing+freeness
	  sharefree_clique_call_to_entry/9,
	  sharefree_clique_call_to_success_builtin/6,
	  sharefree_clique_call_to_success_fact/9,
	  sharefree_clique_call_to_prime_fact/6,
	  sharefree_clique_exit_to_prime/7,            
	  sharefree_clique_extend/4,                   
	  sharefree_clique_glb/3,      
	  sharefree_clique_input_user_interface/3,  
	  sharefree_clique_input_interface/4,  
          sharefree_clique_identical_abstract/2,       
          sharefree_clique_eliminate_equivalent/2,
	  sharefree_clique_less_or_equal/2,     
	  sharefree_clique_compute_lub/2,       
	  sharefree_clique_compute_lub_el/3,
	  sharefree_clique_asub_to_native/5, 
	  sharefree_clique_project/3,                  
	  sharefree_clique_sort/2,                     
	  sharefree_clique_special_builtin/4,
	  sharefree_clique_success_builtin/5,
	  sharefree_clique_unknown_call/4,
	  sharefree_clique_empty_entry/3,
	  sharefree_clique_unknown_entry/3,
	  sharefree_clique_extend_asub/3,
	  sharefree_clique_amgu/4,
%1-clique+sharing
	  share_clique_1_call_to_entry/9,
	  share_clique_1_call_to_success_builtin/6,
	  share_clique_1_call_to_success_fact/9,
	  share_clique_1_exit_to_prime/7,            
	  share_clique_1_extend/4,                   
	  share_clique_1_glb/3,
	  share_clique_1_identical_abstract/2,
	  share_clique_1_less_or_equal/2,
	  share_clique_1_eliminate_equivalent/2,
	  share_clique_1_input_interface/4,  
	  share_clique_1_asub_to_native/5, 
	  share_clique_1_project/3,                  
	  share_clique_1_success_builtin/5,
	  share_clique_1_unknown_call/4,
	  share_clique_1_unknown_entry/3,
	  share_clique_1_compute_lub/2,
	  share_clique_1_lub_cl/3,
%clique-sharing+def
	  share_clique_def_call_to_entry/9,
	  share_clique_def_exit_to_prime/7,
	  share_clique_def_extend/4,
	  share_clique_def_project/3,
	  share_clique_def_sort/2,
	  share_clique_def_glb/3,
	  share_clique_def_identical_abstract/2,
	  share_clique_def_eliminate_equivalent/2,
	  share_clique_def_less_or_equal/2,
	  share_clique_def_call_to_success_fact/9,
	  share_clique_def_compute_lub/2,
	  share_clique_def_lub_cl/3,
	  share_clique_def_input_user_interface/3,
	  share_clique_def_asub_to_native/5,
	  share_clique_def_unknown_call/4,
	  share_clique_def_empty_entry/3,
	  share_clique_def_unknown_entry/3,
	  share_clique_def_special_builtin/4,
	  share_clique_def_compose/2,
%clique-sharing+freeness+def
	  sharefree_clique_def_call_to_entry/9,
	  sharefree_clique_def_exit_to_prime/7,
	  sharefree_clique_def_extend/4,
	  sharefree_clique_def_project/3,
	  sharefree_clique_def_sort/2,
	  sharefree_clique_def_glb/3,
	  sharefree_clique_def_identical_abstract/2,
	  sharefree_clique_def_eliminate_equivalent/2,
	  sharefree_clique_def_less_or_equal/2,
	  sharefree_clique_def_call_to_success_fact/9,
	  sharefree_clique_def_compute_lub/2,
	  sharefree_clique_def_lub_cl/3,
	  sharefree_clique_def_input_user_interface/3,
	  sharefree_clique_def_asub_to_native/5,
	  sharefree_clique_def_unknown_call/4,
	  sharefree_clique_def_empty_entry/3,
	  sharefree_clique_def_unknown_entry/3,
	  sharefree_clique_def_special_builtin/4,
	  sharefree_clique_def_compose/3,
	  unify_asub_if_bottom/2,
% CiaoPP flags 
	  widen/1,
	  type_widening_condition/1
        ],
	[assertions, isomodes]).
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
:- use_module(ciaopp(preprocess_flags), 
	[ current_pp_flag/2]).

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
% * Type of conditions.                                                  |
% - aamgu: the condition is verified after performing the amgu.          |
% - bamgu: an upper bound is computed before performing the amgu in order| 
%   to avoid to compute it. (default)                                    |
type_widening_condition(bamgu). 
%------------------------------------------------------------------------%

% The following predicates are defined in share.pl but they're not
% exported:


if_not_nil([],_,Xs,Xs):- !.
if_not_nil(_,X,[X|Xs],Xs).

list_ground([],[]).
list_ground([X|Xs],[X/g|Rest]):-
	list_ground(Xs,Rest).

%------------------------------------------------------------------------
% eliminate_couples(+,+,+,-)                                             |
% eliminate_couples(Sh,Xs,Ys,NewSh)                                      |
% Eliminates from Sh all SS s.t. both X,Y\in SS for some X\in Xs,Y\in Ys |
% All arguments ordered                                                  |
%------------------------------------------------------------------------

eliminate_couples([],_,_,[]):- !.
eliminate_couples(Sh,Xs,Ys,NewSh) :-
	ord_split_lists_from_list(Xs,Sh,Intersect,Disjunct1),
	ord_split_lists_from_list(Ys,Intersect,_,Disjunct2),
	merge(Disjunct2,Disjunct1,NewSh).

%------------------------------------------------------------------------

handle_each_indep([],_AbsInt,Call,Call).
handle_each_indep([[X,Y]|Rest],AbsInt,Call,Succ):-
	success_builtin(AbsInt,'indep/2',_,p(X,Y),Call,Succ1), !,
	handle_each_indep(Rest,AbsInt,Succ1,Succ).

success_builtin(share,Key,Sv,Vs,Call,Succ):-
	share_success_builtin(Key,Sv,Vs,Call,Succ).
success_builtin(shfr,Key,Sv,Vs,Call,Succ):-
	shfr_success_builtin(Key,Sv,Vs,Call,Succ).
success_builtin(shfrnv,Key,Sv,Vs,Call,Succ):-
	shfrnv_success_builtin(Key,Sv,Vs,Call,Succ).

%-----------------------------------------------------------------------%
% eliminate_if_not_possible(+,+,-)                                      |
% eliminate_if_not_possible(ASub,Vars,More)                             |
% It gives in the third argument each set S in the first argument which |
% has variables in common with Vars but Vars is not a subset of S       |
%-----------------------------------------------------------------------%

eliminate_if_not_possible([],_,X-X).
eliminate_if_not_possible([Z|Rest],Vars,More):-
	ord_intersection(Vars,Z,Term),
	test_temp(Term,Vars), !,
	eliminate_if_not_possible(Rest,Vars,More).
eliminate_if_not_possible([Z|Rest],Vars,[Z|More]-More2):-
	eliminate_if_not_possible(Rest,Vars,More-More2).

test_temp([],_).
test_temp([X|Xs],List):-
	[X|Xs] == List.

%-----------------------------------------------------------------------%
% eliminate_if_not_possible(+,+,+,-)                                    |
% eliminate_if_not_possible(ASub,X,Vars,More)                           |
% It gives as a diff list each set S in ASub s.t. either X appears in S | 
% and no element of Vars appears in S or                                |
% X does not appear but at least on element in Vars appears             |
%-----------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).

eliminate_if_not_possible([],_,_,X-X).
eliminate_if_not_possible([Z|Rest],X,Vars,More):-
	ord_intersection(Vars,Z,V), !,
	test_set(V,X,Z,Rest,Vars,More).
eliminate_if_not_possible([Z|Rest],X,Vars,More):-
	ord_member(X,Z), !,
	eliminate_if_not_possible(Rest,X,Vars,More).
eliminate_if_not_possible([Z|Rest],X,Vars,[Z|More]-More1):-
	eliminate_if_not_possible(Rest,X,Vars,More-More1).
	
:- pop_prolog_flag(multi_arity_warnings).

test_set([],X,Z,Rest,Vars,More):-
	ord_member(X,Z),!,
	More = [Z|Rest1]-Rest2,
	eliminate_if_not_possible(Rest,X,Vars,Rest1-Rest2).
test_set([],X,_,Rest,Vars,More):- !,
	eliminate_if_not_possible(Rest,X,Vars,More).
test_set([_|_],X,Z,Rest,Vars,More):-
	ord_member(X,Z),!,
	eliminate_if_not_possible(Rest,X,Vars,More).
test_set([_|_],X,Z,Rest,Vars,More):- !,
	More = [Z|Rest1]-Rest2,
	eliminate_if_not_possible(Rest,X,Vars,Rest1-Rest2).



