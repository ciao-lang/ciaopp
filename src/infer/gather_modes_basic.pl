:- module(_, [], [assertions]).

:- use_module(engine(messages_basic), [message/2]).

:- export(get_metric/2).
get_metric(int,      int) :- !.
get_metric(void,     void) :- !.
get_metric(length,   length) :- !.
get_metric(size,     size) :- !.
get_metric(depth, depth) :- !.
get_metric(depth(_), depth) :- !.
get_metric(M,        null) :-
	message(warning, ['The measure ', ~~(M), ' is unknown.']).

:- export(translate_to_modes/2).
translate_to_modes([],[]).
translate_to_modes([I|Is],[M|Ms]):-
	translate_to_mode(I,M),
	translate_to_modes(Is,Ms).

:- export(translate_to_mode/2).
translate_to_mode(y/y,'+') :- !.
translate_to_mode(y/n,'+') :- !. % bug?
translate_to_mode(n/y,'-') :- !.
% TODO: In next clause, if changed 2nd arg. to -, the following benchmarks
% TODO: in (tests/resources/examples) will fail: flat_1, flat_2, flat_3, pqr_2,
% TODO: subst_exp_1, param_1, pqr_cm, partition_1, reverse, rtests, lists_sc,
% TODO: Note that they depend on entry assertions -- EMM
translate_to_mode(n/n,'+'). % Changed (Oct, 14, 2004) -PLG
% translate_to_mode(n/n,'-'). % -PLG

