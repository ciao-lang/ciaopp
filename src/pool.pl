 
:- module(pool,_,[assertions]).

%% Common predicates that don't go anywhere else...

recorded_internal(_,_,_).

recorda_internal(_,_,_).
recordz_internal(_,_,_).

there_is_delay:- fail.

%% JCF- The following meta_call handling predicates have been implemented
%%      for tr_syntax, but they should be revised before using them
%%      in other parts of Ciaopp.
meta_call(_):- fail.
peel_meta_call(_,_,_,_).
build_meta_call(_,_,_,_).

del_output(_,_,_).
%primes(_).
sum_list_of_lists(_,_,_).

group_calls(_,_,_,_,_,_,_,_).
type_assignments_included(_,_,_,_).
type_assignments_incompatible(_,_,_,_).

del_compute_lub(_,_,_).
output_interface(_,_,_,_,_).

% GPS
no_instantiate_builtin(_).
no_instantiate_builtin_but_change(_).
