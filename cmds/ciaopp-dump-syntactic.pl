:- module(_, [main/1], [assertions,datafacts]).

:- doc(title, "A syntactic statistics report of the code of a program").

:- doc(author, "Isabel Garcia-Contreras").

:- use_module(library(lists), [length/2]).
:- use_module(library(streams)).
:- use_module(library(format), [format/3]).
:- use_module(library(process), [process_call/3]).

:- use_module(ciaopp(frontend_driver)).
:- use_module(ciaopp(analyze_driver)).

:- use_module(ciaopp(plai), [generate_trans_clauses/4]).
:- use_module(library(compiler/p_unit), [program/2]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).
:- use_module(ciaopp(plai/tarjan), [recursive_classes/1]).

:- doc(module, "A command to extract simple syntactic characteristics from
   programs: LOC, no of predicates, no of clauses, no of variables, avg no of
   literals per clause, number of SCC, max no of preds per SCC, min no of preds
   per SCC, avg no of preds per SCC").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(section, "Counters").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- data counter/2.
:- data seen_pred/1.

inc_counter(Key,N) :-
    ( retract_fact(counter(Key, N0)), ! ; N0 = 0 ),
    N1 is N0 + N,
    assertz_fact(counter(Key, N1)).

set_counter(Key,N) :-
    ( retract_fact(counter(Key, _)), ! ; true ),
    assertz_fact(counter(Key, N)).

% doc_counter(loc, 'Number of lines of code').
doc_counter(preds, 'Number of predicates').
doc_counter(cls, 'Number of clauses').
doc_counter(vars, 'Number of variables').
doc_counter(max_vars_cls, 'Maximum number of variables of a clause').
doc_counter(facts, 'Number of facts').
doc_counter(lits, 'Number of literals').
doc_counter(max_lits, 'Maximum number of literals of a clause').
doc_counter(rec_cls, 'Number of recursive clauses').
doc_counter(n_SCC, 'Number of SCC').
doc_counter(max_pred_SCC, 'Max preds SCC').

main(['--print-header', Output]) :- !,
    open(Output,'write',S),
    ( % failure-driven loop
      doc_counter(Key, _Expl),
        format(S,'~w,', [Key]),
        fail
    ; close(S) ).
main([Output|Files]) :- !,
    print_loc(Files),
    module(Files),
    program(Cls, Ds),
    generate_trans_clauses(Cls,Ds,pdb,_),
    process_trans_clauses,
    recursive_classes(RC),
    length(RC, L),
    set_counter(n_SCC, L),
    get_max_scc(RC,0,MaxRC),
    set_counter(max_pred_SCC,MaxRC),
    print_stats(Output).
main(_) :-
    format(user, 'Error in parameters~n', []).

print_loc(Files) :-
    format(user, 'Lines of code:~n', []),
    process_call(path(wc), ['-l'|Files], []).

process_trans_clauses :-
    ( % failure-driven loop
      trans_clause(Key, RFlag, X),
        X = clause(Head, Vars, _ClKey, Body),
        ( process_clause(Head, Vars, Key, RFlag, Body), fail
        ; true
        ),
        fail
    ; true ).

% each of the clauses must fail to continue processing
process_clause(_Head, _Vars, _Key, _RFlag, _Body) :-
    inc_counter(cls,1).
process_clause(_Head, _Vars, Key, _RFlag, _Body) :-
    ( seen_pred(Key) -> true
    ; inc_counter(preds,1), assertz_fact(seen_pred(Key))
    ).
process_clause(_Head, Vars, _Key, _RFlag, _Body) :-
    length(Vars, N),
    inc_counter(vars,N).
process_clause(_Head, Vars, _Key, _RFlag, _Body) :-
    length(Vars, N),
    ( counter(max_vars_cls, N0) -> true ;  N0 = 0 ),
    ( N0 < N ->
        set_counter(max_vars_cls,N)
    ;
        true
    ).
process_clause(_Head, _Vars, _Key, _RFlag, Body) :-
    ( Body = g(_,[],'$built'(_,true,_),'true/0',true) ->
        inc_counter(facts,1)
    ;
        count_literals(Body, N),
        inc_counter(lits,N),
        ( counter(max_lits, N0) -> true ;  N0 = 0 ),
        ( N0 < N -> set_counter(max_lits,N) ; true )
    ).
process_clause(_Head, _Vars, _Key, RFlag, _Body) :-
    ( RFlag = r ->
        inc_counter(rec_cls, 1)
    ; true ).

count_literals(g(_Key,_Vars,_Info,_SgKey,_Sg),1):- !.
count_literals((g(_Key,_Vars,_Info,_SgKey,_Sg),Goals),N):-!,
    count_literals(Goals, N0),
    N is N0 + 1.

:- doc(section, "Printing statistics").

print_stats(Output) :-
    open(Output,'write',S),
    ( % failure-driven loop
      doc_counter(Key, _Expl),
        ( counter(Key, N) -> true ; N = 0),
        %format(S,'~w: ~d~n', [_Expl, N]),
        format(S,'~d,', [N]),
        fail
    ;
        close(S)
    ).

get_max_scc([],N,N).
get_max_scc([RC|RCs],N0,Max) :-
    length(RC,L),
    ( N0 > L -> N = N0 ; N = L),
    get_max_scc(RCs,N,Max).