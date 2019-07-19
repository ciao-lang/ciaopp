:- package(no_debug).
% This package allows eliminating calls to debug/1,
% thus avoiding the run-time overhead introduced by calls to the
% debug/1 predicate

% TODO: uncertain priority: just disables some decls and goals
:- load_compilation_module(spec(no_debug_tr)).
:- add_sentence_trans(no_debug_tr:no_debug/2, 9010).
