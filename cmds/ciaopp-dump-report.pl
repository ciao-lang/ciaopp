:- module(_,[main/1],[assertions]).

:- doc(title, "A reachability report of a dumped CiaoPP analysis").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(module,"
@begin{alert}
The program needs to be analyzed with the pp flag fact_info=on, and dumped with the option 'incremental':

@begin{verbatim}
?- use_module(ciapp(p_unit/p_dump)).
?- dump('file.dump', [incremental]).
@end{verbatim}

@end{alert}").

:- use_module(library(sort)).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(ciaopp(ciaopp)).
:- use_module(ciaopp(plai/plai_db), [get_memo_table/7,complete/7]).
:- use_module(ciaopp(p_unit/p_dump), [restore/1]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).
:- use_module(ciaopp(plai/fixpo_ops), [bottom/1]).

main([DumpFile]) :-
    clean_analysis_info,
    restore(DumpFile),
    ( \+ trans_clause(_,_,_) ->
        format('No clauses found in dump, try dumping it with the incremental option.', [])
    ;
        print_reach_report
    ).
main(_) :-
    format('Usage: ./ciaopp-dump-report file.dump',[]).

% assuming that 
print_reach_report :-
    findall(SgKey, trans_clause(SgKey,_,_), SgKeys_u),
    sort(SgKeys_u, SgKeys), % remove duplicates
    ( % failure-driven loop
      member(SgKey, SgKeys),
        format('~nProcessing ~w:~n', [SgKey]),
        detect_dead_predicate(SgKey),
        ( % failure-driven loop
          trans_clause(SgKey,_,clause(_Head,_Vars_u,ClKey,_Body)),
            ( get_memo_table(ClKey, pdb, _, no, _Vars, ASub, _) ->
                ( bottom(ASub) -> 
                    format('clause ~w always fails or loops~n', [ClKey])
                ;   true )
            ;
                format('clause body of ~w is never executed~n', [ClKey])
            ),
            fail
        ;   true ),
        fail
    ; true
    ).

detect_dead_predicate(SgKey) :-
    findall(comp(Sg, Prime), complete(SgKey, pdb, Sg, _, Prime, _,_), LPrimes),
    process_comps(LPrimes, Fails, Dead),
    ( Fails == yes ->
        format('Pred ~w always fails or loops~n',[SgKey])
    ; true ),
    ( var(Dead) ->
        format('Pred ~w is never executed~n',[SgKey]), !, fail ; true
    ).

% proces_comps if _Fails is var, it means it fails, if _Dead is var, it means it is never called.
process_comps([], _Fails, _Dead).
process_comps([comp(Sg,Prime)|Cs], Fails, Dead) :- % if there is a complete, it is never dead
    Dead = no,
    ( is_bottom(Sg,Prime) -> Fails = yes ; true ),
    process_comps(Cs, Fails, Dead).

% if the head has no vars [] does not imply bottom (like in fixpo_ops)
is_bottom(_Sg,Prime) :- Prime = ['$bottom'].
