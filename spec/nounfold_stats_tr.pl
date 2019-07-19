:- module(nounfold_stats_tr,[no_unfold_stats/2],[]).

:- use_package(assertions).

no_unfold_stats((H:-B),(H:-B1)):-
	no_unfold_stats_(B,B1).
%% no_unfold_stats((:- use_module(spec(unfold_stats),_)),[]).
%% no_unfold_stats((:- use_module(spec(unfold_stats))),[]).

no_unfold_stats_(G,G):-
	var(G), !.
no_unfold_stats_((A,B),(A0,B0)):- !,
	no_unfold_stats_(A,A0),
	no_unfold_stats_(B,B0).
no_unfold_stats_((A;B),(A0;B0)):- !,
	no_unfold_stats_(A,A0),
	no_unfold_stats_(B,B0).
no_unfold_stats_((A->B),(A0->B0)):- !,
	no_unfold_stats_(A,A0),
	no_unfold_stats_(B,B0).
no_unfold_stats_(inc_derivation_steps(_),true):- !.
no_unfold_stats_(inc_unfold_evals(_),true):- !.
no_unfold_stats_(G,G).
