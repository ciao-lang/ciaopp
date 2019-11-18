:- module(no_debug_tr,[no_debug/2],[]).

:- use_package(assertions).

no_debug((H:-B),(H:-B1)):-
    no_debug_(B,B1).
%% no_debug((:- use_module(spec(mem_usage),_)),[]).
%% no_debug((:- use_module(spec(mem_usage))),[]).

no_debug_(G,G):-
    var(G), !.
no_debug_((A,B),(A0,B0)):- !,
    no_debug_(A,A0),
    no_debug_(B,B0).
no_debug_((A;B),(A0;B0)):- !,
    no_debug_(A,A0),
    no_debug_(B,B0).
no_debug_((A->B),(A0->B0)):- !,
    no_debug_(A,A0),
    no_debug_(B,B0).
no_debug_(debug(_),true):- !.
no_debug_(G,G).
