:- module(fr_sets,
	[ set_add_el/3,
	  set_boxplus/3,
	  set_compare/3,
	  set_create/2,
	  set_diff/3,
	  set_empty/1,
	  set_eq/2,
	  set_intersect/3,
	  set_is_in/2,
	  set_is_subset/2,
	  set_nondisjoint/2,
	  set_product/3,
	  set_rename/4,
	  set_union/3,
	  set_union_list/2,
	%
	  ss_aconjm/3,
	  ss_add_el/3,
	  ss_addpairs_groups/4,
	  ss_close/2,
	  ss_diff/3,
	  ss_empty/1,
	  ss_identical/2,
	  ss_is_in/2,
	  ss_is_subset/2,
	  ss_lubm/3,
	  ss_make_AlfaFunctor_groups/3,
	  ss_make_pairs/3,
	  ss_make_singl/2,
	  ss_minimise/2,
	  ss_oplusm/3,
	  ss_reduce_min/3,
	  ss_restriction/3,
	  ss_sort/2,
	  ss_split/4,
	  ss_union/3,
	  ss_union_list/2
	],
	[ ] ).

:- use_module(library(lists), [length/2]).
:- use_module(library(sort), [sort/2]).

:- push_prolog_flag(multi_arity_warnings,off).

:- include(domain(fr_os)).
:- include(domain(fr_oss23)).
:- include(domain(kulordsets)).
:- include(domain(kulordsetsext)).

:- pop_prolog_flag(multi_arity_warnings).
