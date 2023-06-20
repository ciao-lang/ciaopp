:- module(_,[main/1],[assertions]).

:- doc(title, "A reachability report of a dumped CiaoPP analysis").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(module,"
@begin{alert}
The program needs to be analyzed with the pp flag fact_info=on, and dumped with the option 'incremental':

@begin{verbatim}
?- use_module(ciaopp(p_dump)).
?- dump('file.dump', [incremental]).
@end{verbatim}

@end{alert}").

:- use_module(library(sort)).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(messages), [show_message/4, show_message/3]).

:- use_module(ciaopp(plai/plai_db), [get_memo_table/7,complete/7]).
:- use_module(ciaopp(p_dump), [restore/1]).
:- use_module(ciaopp(p_unit/clause_db), [clause_locator/2]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).
:- use_module(ciaopp(plai/fixpo_ops), [bottom/1]).

main([DumpFile]) :-
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
        % format('~nProcessing ~w:~n', [SgKey]),
        detect_dead_predicate(SgKey),
        ( % failure-driven loop
          trans_clause(SgKey,_,clause(Head,_Vars_u,ClKey,Body)),
            ( get_memo_table(ClKey, _AbsInt, _, no, _Vars, ASub, _) ->
                atom_concat(ClKey, '/1', PPKey),
                ( get_memo_table(PPKey, _AbsInt, _, _, _Vars, PPASub, _), is_bottom(_, PPASub) ->
                    report_message(ClKey,"clause body of ~w is never executed~n", [ClKey])
                ; is_bottom(Head,ASub) ->
                    report_message(ClKey,"clause ~w always fails or loops~n",[ClKey])
                ;   true )
            ;
                ( Body \= g(_,[],'$built'(_,true,_),'true/0',true) -> % fact
                    report_message(ClKey,"clause body of ~w is never executed~n", [ClKey])
                ; report_message(ClKey,"~w fact is never unified~n", [ClKey]) )
            ),
            fail
        ;   true ),
        fail
    ; true
    ).

report_message(ClKey,Mess,Params) :-
    % this is not working because the dump does not contain the clause locators
    clause_locator(ClKey,Loc), !,
    show_message(simple,Loc,Mess,Params).
report_message(_PredKey,Mess,Params) :- % we don't have locators for predicates
    show_message(simple,Mess,Params).

detect_dead_predicate(SgKey) :-
    findall(comp(Sg, Prime), complete(SgKey, _AbsInt, Sg, _, Prime, _,_), LPrimes),
    process_comps(LPrimes, Fails, Dead),
    ( var(Fails) ->
        report_message(SgKey,"Pred ~w always fails or loops~n",[SgKey])
    ; true ),
    ( var(Dead) ->
        report_message(SgKey,"Pred ~w is never executed~n",[SgKey]), !, fail ; true
    ).

% proces_comps if _Fails is var, it means it fails, if _Dead is var, it means it is never called.
process_comps([], _Fails, _Dead).
process_comps([comp(Sg,Prime)|Cs], Fails, Dead) :- % if there is a complete, it is never dead
    Dead = no,
    ( \+ is_bottom(Sg,Prime) -> Fails = no ; true ),
    process_comps(Cs, Fails, Dead).

% if the head has no vars [] does not imply bottom (like in fixpo_ops)
is_bottom(_Sg,Prime) :- Prime = ['$bottom'].
