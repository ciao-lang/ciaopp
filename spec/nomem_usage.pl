:- package(nomem_usage).
% This package allows eliminating calls to update_mem_usage/0,
% thus avoiding the run-time overhead introduced by memory measurements
% if not actually being used.

% TODO: uncertain priority: just disables some decls and goals
:- load_compilation_module(spec(nomem_usage_tr)).
:- add_sentence_trans(nomem_usage_tr:no_mem_usage/2, 9010).
