:- module(_, [main/1], []).

:- use_module('ciaopp-dump-cmp').
:- use_module('ciaopp-dump-fmt').
:- use_module('ciaopp-dump-stats').
:- use_module('ciaopp-dump-syntactic').

main(['fmt'|Args]) :-
    'ciaopp-dump-fmt':main(Args).

main(['cmp'|Args]) :-
    'ciaopp-dump-cmp':main(Args).

main(['stats'|Args]) :-
    'ciaopp-dump-stats':main(Args).

main(['syntactic'|Args]) :-
    'ciaopp-dump-syntactic':main(Args).