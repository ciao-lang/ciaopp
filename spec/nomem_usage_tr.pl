:- module(nomem_usage_tr,[no_mem_usage/2],[]).

:- use_package(assertions).

no_mem_usage((H:-B),(H:-B1)):-
	no_mem_usage_(B,B1).
%% no_mem_usage((:- use_module(spec(mem_usage),_)),[]).
%% no_mem_usage((:- use_module(spec(mem_usage))),[]).

no_mem_usage_(G,G):-
	var(G), !.
no_mem_usage_((A,B),(A0,B0)):- !,
	no_mem_usage_(A,A0),
	no_mem_usage_(B,B0).
no_mem_usage_((A;B),(A0;B0)):- !,
	no_mem_usage_(A,A0),
	no_mem_usage_(B,B0).
no_mem_usage_((A->B),(A0->B0)):- !,
	no_mem_usage_(A,A0),
	no_mem_usage_(B,B0).
no_mem_usage_(update_mem_usage,true):- !.
no_mem_usage_(reset_mem_usage,true):- !.
no_mem_usage_(readjust_max_mem_usage,true):- !.
no_mem_usage_(ask_mem_usage(_,_),true):- !.
no_mem_usage_(G,G).
