 
:- module(pool,[],[assertions]).

% TODO: cleanup

%% Common predicates that don't go anywhere else...
:- export(recorded_internal/3).
recorded_internal(_,_,_).
:- export(recorda_internal/3).
recorda_internal(_,_,_).
:- export(recordz_internal/3).
recordz_internal(_,_,_).

:- export(there_is_delay/0).
there_is_delay:- fail.

%% JCF- The following meta_call handling predicates have been implemented
%%      for tr_syntax, but they should be revised before using them
%%      in other parts of Ciaopp.
:- export(meta_call/1).
meta_call(_):- fail.

:- export(peel_meta_call/4).
peel_meta_call(_,_,_,_).
:- export(build_meta_call/4).
build_meta_call(_,_,_,_).

:- export(del_output/3).
del_output(_,_,_).
%primes(_).
:- export(sum_list_of_lists/3).
sum_list_of_lists(_,_,_).

:- export(group_calls/8).
group_calls(_,_,_,_,_,_,_,_).
:- export(type_assignments_included/4).
type_assignments_included(_,_,_,_).
:- export(type_assignments_incompatible/4).
type_assignments_incompatible(_,_,_,_).

:- export(del_compute_lub/3).
del_compute_lub(_,_,_).
:- export(output_interface/5).
output_interface(_,_,_,_,_).

% GPS
:- export(no_instantiate_builtin/1).
no_instantiate_builtin(_).
:- export(no_instantiate_builtin_but_change/1).
no_instantiate_builtin_but_change(_).
