:- module(notrace_tr,[no_fixp_trace/2],[assertions]).

no_fixp_trace((H:-B),(H:-B1)):-
	no_fixp_trace_(B,B1).
no_fixp_trace((:- use_module(ciaopp(plai/trace_fixp),_)),[]).
no_fixp_trace((:- use_module(ciaopp(plai/trace_fixp))),[]).

no_fixp_trace_(G,G):-
	var(G), !.
no_fixp_trace_((A,B),(A0,B0)):- !,
	no_fixp_trace_(A,A0),
	no_fixp_trace_(B,B0).
no_fixp_trace_((A;B),(A0;B0)):- !,
	no_fixp_trace_(A,A0),
	no_fixp_trace_(B,B0).
no_fixp_trace_((A->B),(A0->B0)):- !,
	no_fixp_trace_(A,A0),
	no_fixp_trace_(B,B0).
no_fixp_trace_(fixpoint_trace(_,_,_,_,_,_,_),true):- !.
no_fixp_trace_(trace_fixp:cleanup,true):- !.
no_fixp_trace_(G,G).
