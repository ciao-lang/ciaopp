:- module(nfdet_statistics, [nfdet_statistics/7], [hiord, fsyntax, assertions]).

:- use_module(library(compiler/p_unit), [predicate_names/1]).
:- use_module(library(lists), [member/2, length/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(library(compiler/p_unit/program_keys), [get_predkey/3]).

nfdet_statistics(AbsDomain, S, Total, NF_Preds, Cov_Preds, NF_Variants, Cov_Variants):-
    predicate_names(Pred_Names),
    length(Pred_Names, Total),
    pred_variants(Pred_Names, AbsDomain, S),
    NF_Variants = ~count(~filter(S, some_not_fail)),
    Cov_Variants = ~count(~filter(S, some_covered)),
    NF_Preds = ~count(~filter(S, all_not_fail)),
    Cov_Preds = ~count(~filter(S, all_covered)).

some_not_fail(predinfo(_SgKey, L)) :-
    member(variant(_, not_fails), L). 

some_covered(predinfo(_SgKey, L)) :-
    member(variant(covered, _), L). 

all_not_fail(predinfo(_SgKey, L)) :-
    N = ~count(L), N =\= 0, N = ~count(~filter(L, variant_not_fails)).

all_covered(predinfo(_SgKey, L)) :-
    N = ~count(L), N =\= 0, N = ~count(~filter(L, variant_covered)).

variant_covered(variant(covered, _)).
variant_not_fails(variant(_, not_fails)).

pred_variants([(F/A)|Pred_Names], AbsDomain, [predinfo(SgKey, L)|T]):-
   get_predkey(F,A, SgKey),
   findall(variant(Covered,Fails), 
       (complete(SgKey,AbsDomain,_Sg,_Proj,Prime,_Id,_Parents),
        covfail(Prime,Covered,Fails)),
       L),
   pred_variants(Pred_Names, AbsDomain, T).
pred_variants([], _AbsDomain, []).

covfail([nf(_Types,_Modes,nf(_Tests,Covered,Fails))],Covered,Fails).

count(Xs) := ~length(Xs).

% TODO: use filter/3 from hiordlib (P must be first argument)
:- meta_predicate filter(?, pred(1), ?).
filter([], _P) := [].
filter([X|Xs], P) := [X|~filter(Xs, P)] :- P(X), !.
filter([_|Xs], P) := ~filter(Xs, P).
