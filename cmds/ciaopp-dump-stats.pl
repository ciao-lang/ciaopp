:- module(_, [main/1], [assertions, datafacts]).

:- doc(title, "Reporting statistics of a dumped CiaoPP  analysis").
:- doc(author, "Isabel Garcia-Contreras").

:- use_module(library(format), [format/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(lists), [length/2]).
:- use_module(library(streams)).
:- use_module(library(aggregates), [findall/3]).

:- use_module(ciaopp(p_unit/p_dump), [restore/1]).
:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(ciaopp(plai/domains), [identical_abstract/3, unknown_call/5, unknown_entry/4]).

:- doc(module, "A command to extract basic statistics of a ciaopp analysis
result, stored in @tt{.dump} format").

main(['--print-header', Output]) :- !,
    open(Output,'write',S),
    ( % failure-driven loop
      doc_counter(Key, _Expl),
        functor(Key,F,_),
        format(S,'~w,', [F]),
        fail
    ; close(S) ).
main([Output|Files]) :- !,
    ( % failure-driven loop
      member(F,Files),
        restore(F),
        fail
    ; true ),
    collect_statistics,
    print_stats(Output).
main(_) :-
    format(user, 'Error in parameters~n', []).

collect_statistics :-
    traverse_completes.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(section, "Counters").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- data counter/2.
%% TODO: count widening points!
:- data seen_pred/1.

inc_counter(Key,N) :-
    ( retract_fact(counter(Key, N0)), ! ; N0 = 0 ),
    N1 is N0 + N,
    assertz_fact(counter(Key, N1)).

set_counter(Key,N) :-
    ( retract_fact(counter(Key, _)), ! ; true ),
    assertz_fact(counter(Key, N)).

doc_counter(preds, 'Predicates with completes').
doc_counter(mult(_), '# of abstract versions of a predicate').
doc_counter(contexts(_), '# of calling context of all abstract versions of a predicate').
doc_counter(call_top, '# of calling context of all abstract versions of a predicate').
doc_counter(succ_top, '# of completes with top as success asub').
doc_counter(succ_bot, '# of completes with bot as success asub').

traverse_completes :-
    ( % failure-driven loop
      complete(SgKey,AbsInt,Sg,Proj,[Prime],_Id,Parents), % assuming not multi succ
        ( seen_pred(SgKey) -> true
        ; inc_counter(preds,1), assertz_fact(seen_pred(SgKey))
        ),
        % Multivariant calls
        inc_counter(mult(SgKey), 1),
        % calling contexts
        length(Parents, LC),
        inc_counter(contexts(SgKey), LC),
        % Call is top
        varset(Sg, Vars),
        unknown_entry(AbsInt,Sg,Vars,TopCall),
        ( identical_abstract(AbsInt,Proj,TopCall) ->
            inc_counter(call_top, 1)
        ; true),
        % Succ is top
        unknown_call(AbsInt,Sg,Vars,Proj,SuccCall),
        ( identical_abstract(AbsInt,Prime,SuccCall) ->
            inc_counter(succ_top, 1)
        ; true),
        % Succ is bot
        ( identical_abstract(AbsInt,Prime,'$bottom') ->
            inc_counter(succ_bot, 1)
        ; true),
        fail
    ; true ).

print_stats(Output) :-
    open(Output,'write',S),
    ( % failure-driven loop
      doc_counter(Key, _Expl),
        ( functor(Key,F,1) ->
            functor(Key2,F,1),
            findall(X,counter(Key2,X), L),
            add_all(L,0,N)
        ;
            ( counter(Key, N) -> true ;  N = 0 )
        ),
        format(S, '~d,', [N]),
        fail
    ;
        close(S)
    ).

add_all([],Sum,Sum).
add_all([N|Ns],Sum0,Sum) :-
    Sum1 = Sum0 + N,
    add_all(Ns, Sum1, Sum).