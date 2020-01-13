:- module(raw_printer, [
    raw_output/1,
    show_trans_clauses/0,
    show_analysis/0,
    show_registry_info/0,
    show_global_answer_table/1,
    show_change_list/0
    ], [assertions, datafacts]).

:- doc(title, "Advanced output of preprocessor").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "
Raw printer outputs the analysis results of ciaopp without
preprocessing any information, as it is represented internally in CiaoPP

@section{How to use it}
@begin{verbatim}
?- set_pp_flag(output_lang, raw).

yes
% make analysis
?- module(foo).
{Loading current module from foo.pl
{loaded in 390.268 msec.}
}

yes
?- analyze(eterms).
{Analyzing foo.pl
{preprocessed for the plai fixpoint in 1.736 msec.}
{analyzed by plai using eterms with local-control off in 5.106 msec.}
}

?- output.
{written file .../foo_eterms_co.pl}

yes
?- % open file or C-c C-v in emacs

@end{verbatim}

The output will be generated as a module importing package raw. The
idea is to be able to load this analysis (containing the translations
to avoid recomputation), but it not implemented yet.").

:- doc(bug, "Fix output when nothing has been loaded.").
:- doc(bug, "Not tested for all domains.").
:- doc(bug, "Modular analysis output is not correctly distributed in modules.").
:- doc(bug, "Add syntax explanations in comments.").

:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(write), [portray_clause/1, portray_clause/2, write/1, numbervars/3]).
:- use_module(library(format), [format/2, format/3]).
:- use_module(library(lists), [append/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(assertions/assrt_write), [write_assertion/7]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2, typeanalysis/1]).
:- use_module(ciaopp(plai/transform), [trans_clause/3, cleanup_trans_clauses/0]).
:- use_module(ciaopp(plai/plai_db), [complete/7, memo_table/6]).
:- use_module(typeslib(typeslib), [show_types/0, show_types_raw_printer/0]).
:- use_module(ciaopp(p_unit/p_abs), [registry_headers/2, registry/3]).
:- use_module(ciaopp(plai), [generate_trans_clauses/4]).
:- use_module(ciaopp(plai/fixpo_dd), ['$change_list'/2]).
:- use_module(ciaopp(p_unit/program_keys),
    [decode_litkey/5, decode_clkey/4, get_predkey/3]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(ciaopp(p_unit), [program/2]).
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3]).

:- set_prolog_flag(write_strings, on).

:- pred show_trans_clauses #"Shows the code transformed to be
used by the fixpoints (given by @pred{trans_clause/3}).".
show_trans_clauses :-
    trans_clause(Key, RFlag, X),
    X = clause(Head, _Vars, ClKey, Body),
    format('% ~w ~w ~w ~n', [Key, ClKey, RFlag]),
    numbervars(X, 0, _),
    format('~w :-~n', [Head]),
    display_body(Body),
    fail.
show_trans_clauses.

display_body(Body) :-
    Body = g(Id, _, RFlag, _, Goal), !,
    format('      ~w. %~w ~w~n~n', [Goal, RFlag, Id]).
display_body((Body, Goals)) :-
    Body = g(Id, _, RFlag, _, Goal),
    format('      ~w, %~w ~w~n', [Goal, RFlag, Id]),
    display_body(Goals).

% TODO: pretty_dump?
:- pred show_analysis #"Shows all the information inferred by ciaopp.".
show_analysis :-
    display('------- Showing analysis -------'), nl, nl,
    complete(A, B, C, D, E, Id, G),
%       Id \= no,
    show_data(complete(A, B, C, D, E, Id, G)),
    fail.
show_analysis :-
    nl,
    memo_table(A, B, C, D, E, F ),
    show_data(memo_table(A, B, C, D, E, F )),
    fail.
show_analysis :-
    nl,
    \+ \+ complete(_,eterms,_,_,_,_,_), % TODO: other type domains?
    show_types_raw_printer,
    fail.
show_analysis :-
    nl.

:- doc(show_registry_info/0, "Shows information about the modular
analysis registries.").
show_registry_info :-
    registry(A,B,C),
    show_data(registry(A,B,C)), nl,
    fail.
show_registry_info.

:- pred show_data(+X) #"Pretty print custom data (the variables are renamed).".
show_data(R) :-
    \+ \+ (numbervars(R, 0, _), show_data_(R)).

show_data_(R) :-
    R = registry(Pred,_Mod,C), !,
    C = regdata(Id,_AbsInt, Sg, Call, Succ, _Spec, Deps, Children,Mark),
    format(user, '~w | ~w | ~w | ~w | ~w | ~w |', [Id, Pred,Sg,Call,Succ,Mark]),
  show_data_(dep_list(Deps)),
  format(user,' | ',[]),
  show_data_(dep_list(Children)),
  format(user,'~n',[]).
show_data_(C) :-
    C = complete(SgKey,_,Sg,Proj,Prime,Id,Parents), !,
    format(user, '~w | ~w | ~w | ~w | ~w | ~w\n', [SgKey, Id, Sg,Proj,Prime, Parents]).
show_data_(dep_list(L)) :-
    show_dep_list_(L), !.
show_data_(X) :-
    write(X), nl.

show_dep_list_([]).
show_dep_list_([(Id,_,_,_)|Es]) :- !,
    format(user,' ~w', [Id]),
    show_dep_list_(Es).
show_dep_list_([(Id,_,_)|Es]) :- !,
    format(user,' ~w', [Id]),
    show_dep_list_(Es).
show_dep_list_([E|Es]) :-
    format(user,' ~w, ', [E]),
    show_dep_list_(Es).

:- use_module(ciaopp(p_unit/p_abs), [typedb/2]).

:- pred show_global_answer_table(AbsInt) #"Shows de global answer
    table for modular analysis with domain @var{AbsInt}".
show_global_answer_table(AbsInt) :-
    show_gat_header(AbsInt),
    registry(Pred,Mod,R),
    show_data(registry(Pred,Mod,R)),
    fail.
show_global_answer_table(_) :-
    display(user, '------+---------+------+---------'), nl,
    ( % failure-driven loop
      p_abs:typedb(A, B),
        show_data(typedb(A, B)),
        fail
    ; true
    ).

show_gat_header(AbsInt) :-
    format('Global answer table for ~w~n', [AbsInt]),
    display(user, ' Pred | SubGoal | Call | Success '), nl,
    display(user, '------+---------+------+---------'), nl.

:- doc(show_change_list/0, "Shows the list of changes that need
computation in the fixpoint dd.").
show_change_list :-
    '$change_list'(A,B),
    display(ch(A, B)), nl,
    fail.
show_change_list.

:- pred raw_output(File) : stream(File)
    #"Shows the current state of the plai databases in file
    @var{File}, including:
     @begin{itemize}
     @item Transformed clauses.
     @item Inferred assertions (completes).
     @item Information at program point (memo_tables).
     @item State of the types library.
@end{itemize} ".
raw_output(_) :-
    \+ trans_clause(_, _, _),  !,
    % Nothing analyzed, transform for a simple domain (gr)
    program(Cls, Ds),
    generate_trans_clauses(Cls,Ds,gr,_),
    fail.
raw_output(S) :-
    retractall_fact(last_pred(_)),
    output_directives(S),
    findall((RFlag, X), trans_clause(_, RFlag, X), Clauses),
    output_raw_clauses(Clauses, S),
    write_raw_types(S).

output_directives(S) :-
    ( source_clause(_, directive(module(A,B,_)),_)
    ; source_clause(_, directive(module(A,B)),_)),
    portray_clause(S, ':-'(module(A,B, [assertions,regtypes]))),
    nl(S),
    source_clause(_,directive(use_module(Path,Imports)),_), % backtracking here
    portray_clause(S, ':-'(use_module(Path,Imports))),
    fail.
output_directives(_).

write_raw_types(S) :-
    complete(_,AbsInt,_,_,_,_,_),
    typeanalysis(AbsInt),  !,% Check if analysis was done
    display(S, '/*\n'),
    current_output(CO),
    set_output(S),
    show_types,
    set_output(CO),
    display(S, '*/\n').
write_raw_types(_).

:- data last_pred/1. % last written predicate

output_raw_clauses([], _).
output_raw_clauses([(RFlag, X)|Clauses], S) :-
    X = clause(Head, Vars, ClKey, Body),
    decide_print_assertions(ClKey, S),
    format(S, '% ~w ~w ~n', [ClKey, RFlag]),
    add_ppoints(Body, Vars, PBody),
    list_to_clause_body(PBody, ClBody),
    portray_clause(S, ':-'(Head, ClBody)),
    nl(S),
    output_raw_clauses(Clauses, S).

% print assertions when switching to a new pred
% (it assumes that all predicate clauses are contiguous)
decide_print_assertions(ClKey, S) :-
    decode_clkey(ClKey, P, A, _),
    get_predkey(P,A, PredKey),
    \+ last_pred(PredKey), !,
    set_fact(last_pred(PredKey)),
    output_raw_inferred_assertions(PredKey, S).
decide_print_assertions(_, _).

output_raw_inferred_assertions(PredKey, S) :-
    findall(comp(Sg,Proj,Prime,(complete_id(Id), domain(AbsInt), callers(Parents))), complete(PredKey,AbsInt,Sg,Proj,Prime,Id,Parents), Completes),
    write_assertions(Completes, S), nl(S).

write_assertions([], _).
write_assertions([C|Cs], S) :-
    C = comp(Sg,Proj,Prime,Comps),
    assertion_body(Sg, [], [Proj], Prime, [Comps], [], Body),
    numbervars(Body, 0, _), % Not dangerous because it was copied
    write_assertion(S, Sg, true, pred, Body, [], status), nl(S),
    write_assertions(Cs, S).

add_ppoints(g(LitKey, _, _, _, Goal), Vars, Clause) :-
    prepare_memo(LitKey, Vars, PPSubs),
    ( LitKey = ! ->
    append(PPSubs, [!|PPSubs2], Clause),
    ClKey = '!'
      ;
        decode_litkey(LitKey, P, A, Cl, _Lit),
        make_atom([P, A, Cl], ClKey),
        append(PPSubs, [Goal|PPSubs2], Clause)
    ),
    prepare_memo(ClKey, Vars, PPSubs2).
add_ppoints((g(LitKey, _, _, _, Goal), Goals), Vars, Clause) :-
    prepare_memo(LitKey, Vars, PPSubs1),
    append(PPSubs1, [Goal|PPSubs],Clause),
    add_ppoints(Goals, Vars, PPSubs).

prepare_memo(MemoKey, Vars, NPPSubs) :-
    findall(true(Caller,Subs,Vars), memo_table(MemoKey, _AbsInt, Caller, _Child, Vars, Subs), PPSubs),
    bind_vars(PPSubs, Vars, NPPSubs),
    numbervars(NPPSubs, 0, _).

bind_vars([], _, []).
bind_vars([true(A,B,Vars)|Xs], Vars, [true(A,B)|Ys]) :-
    bind_vars(Xs, Vars, Ys).

list_to_clause_body([X], (X)) :- !.
list_to_clause_body([X|Xs], (X,Ys)) :-
    list_to_clause_body(Xs, Ys).
