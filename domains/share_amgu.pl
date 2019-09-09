/*             Copyright (C)2004-2006 UNM-CLIP				*/
:- module(share_amgu, [], [assertions, isomodes]).

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

:- use_module(domain(share_aux), [append_dl/3]).
