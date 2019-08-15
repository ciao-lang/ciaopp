/*             Copyright (C)2004-2006 UNM-CLIP				*/
:- module(share_amgu,
	    [
%% sharing
		share_amgu_call_to_entry/8,
		share_amgu_call_to_success_builtin/6,
		share_amgu_call_to_success_fact/8,
		share_amgu_call_to_prime_fact/6,
		share_amgu_extend_asub/3,
		share_amgu_extend_two_asub/3,
		share_amgu_exit_to_prime/7,
		share_amgu_special_builtin/4,
		share_amgu_success_builtin/5,
		share_amgu_iterate/4,
		share_amgu/4,
%% sharefree
		sharefree_amgu_call_to_entry/8,
		sharefree_amgu_call_to_success_builtin/6,
		sharefree_amgu_call_to_success_fact/8,
		sharefree_amgu_call_to_prime_fact/6,
		sharefree_amgu_exit_to_prime/7,
		sharefree_amgu_extend_asub/3,
		sharefree_amgu_extend_asub0/3,
		sharefree_amgu_special_builtin/4,
		sharefree_amgu_success_builtin/5,
		sharefree_amgu/4,
%% shfrlin
		shfrlin_call_to_entry/8,
		shfrlin_exit_to_prime/7,
		shfrlin_extend/4,
		shfrlin_extend_asub/3,
		shfrlin_project/3,
		shfrlin_sort/2,
		shfrlin_glb/3,
		shfrlin_call_to_success_fact/8,
		shfrlin_call_to_prime_fact/6,
		shfrlin_special_builtin/4,
		shfrlin_success_builtin/5,
		shfrlin_call_to_success_builtin/6,
		shfrlin_compute_lub/2,
		shfrlin_compute_lub_el/3,
		shfrlin_less_or_equal/2,
		shfrlin_input_user_interface/3,
		shfrlin_input_interface/4,
		shfrlin_asub_to_native/5,
		shfrlin_unknown_call/3,
		shfrlin_unknown_entry/2,
		shfrlin_empty_entry/2,
		shfrlin_amgu/4
	    ],
	    [assertions, isomodes]).

:- use_module(domain(s_grshfr),        [projected_gvars/3]).
:- use_module(library(terms_vars),     [varset/2, varset0/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(domain(share_amgu_sets), [delete_vars_from_list_of_lists/3]).
:- use_module(library(sets)).
:- use_module(library(lsets)).

:- include(sharing_amgu).
:- include(sharefree_amgu).
:- include(shfrlin_amgu).

%-------------------------------------------------------------------------%
% REMARK:                                                                 |
% The builtin ==/2 is not treated because it's not implemented            |
% for the domains sharefree_clique. If you want to use it, comment it out |
% in the files :sharing_amgu and sharefree_amgu.                          |
% The builtins read/2 and length/2 are defined in a simple way. For a     |
% better implementation, comment them.                                    |
%-------------------------------------------------------------------------%

list_ground([],     []).
list_ground([X|Xs], [X/g|Rest]) :-
	list_ground(Xs, Rest).
