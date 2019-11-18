:- module(_, [main/1], [assertions, datafacts]).

:- doc(title, "@tt{ciaopp-dump-fmt}: Graph formatting for PLAI dumped results").

:- doc(summary, "Command that takes any dump file of PLAI and produces a
    visualization of the analysis graph in dot (and pdf) format.").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(stability, devel).

:- doc(module, "
This module implements a command to show a graph generated with
the graphviz library (dot comand).

@section{Usage}

Analyze a module and dump the result
@begin{verbatim}
?- use_module(ciaopp(ciaopp)).
?- use_module(ciaopp(p_unit/p_dump)).

?- module(['path/to/your/main', 'path/to/your/lib', '...']).
?- Domain = shfr, analyze(Domain).
?- dump('path/to/dump/analysis.dump').
@end{verbatim}

To generate the graph:
@begin{verbatim}
$ ciao build ciaopp
$ ciaopp-dump-fmt \"path/to/dump/analysis.dump\"
@end{verbatim}

It is generated as @code{path/to/dump/analysis.pdf} (also
@code{path/to/dump/analysis.dot} is generated).

@section{Graph example (dot format)}

@begin{verbatim}
digraph G {
    subgraph cluster_0 {
            style=filled;
            color=lightgrey;
            node [style=filled,color=white];
            a0 -> a1 -> a2 -> a3;
            label = \"process #1\";
    }
    subgraph cluster_1 {
            node [style=filled];
            b0 -> b1 -> b2 -> b3;
            label = \"process #2\";
            color=blue
    }
    start -> a0;
    start -> b0;
    a1 -> b3;
    b2 -> a3;
    a3 -> a0;
    a3 -> end;
    b3 -> end;

    start [shape=Mdiamond];
    end [shape=Msquare];
}
@end{verbatim}
").

% TODO: use gendot bundle without strong dependency

:- use_module(ciaopp(plai/incanal/plai_db_instances), [plai_db_tuple/8]).
:- use_module(ciaopp(p_unit/program_keys),
    [is_entrykey/1, decode_litkey/5, decode_predkey/3]).
:- use_module(ciaopp(test_aux/compare_dump), [restore_and_copy_db/3]).

:- use_module(library(lists), [member/2]).
:- use_module(engine(stream_basic)).
:- use_module(library(format), [format/3]).
:- use_module(library(pathnames), [path_splitext/3, path_split/3]).
:- use_module(library(process), [process_call/3]).
:- use_module(engine(runtime_control), [module_split/3]).

main([InFile]) :- !,
    path_splitext(InFile, InT, _),
    path_splitext(OutFile, InT, '.pdf'),
    path_splitext(GraphFile, InT, '.dot'),
    path_split(InT, _, Base),
    analysis_to_dot(InFile,Base,GraphFile),
    absolute_file_name(GraphFile, AGF),
    absolute_file_name(OutFile, AOF),
    process_call(path(dot), ['-Tpdf', AGF, '-o', AOF],[]).
main(_) :-
    show_help.

show_help. % TODO:

:- data visiting/1.

% TODO: Allow user to write a string in options to write directly in the dot file
% TODO: generalize for directories of modular analysis results
:- export(analysis_to_dot/3).
analysis_to_dot(InFile, AName, OutFile) :-
    restore_and_copy_db(complete, InFile, to_view),
    process_abs_db,
    open(OutFile, write, OS),
    graph_write_header(OS, AName),
    first_mod(M0),
    set_fact(visiting(M0)),
    subgraph_write_header(OS,M0),
    ( % failure-driven loop
      retract_fact(to_visit_mod(M)),
      node(local,Id,M,PKey),
        ( visiting(M) ->
            true
          ;
            set_fact(visiting(M)),
            subgraph_write_footer(OS),
            subgraph_write_header(OS,M)
        ),
        format(OS, '~w [label = "Id~w ~w"]~n', [Id,Id,PKey]),
        write_edges(OS, local, Id),
        fail
    ;
        subgraph_write_footer(OS)
    ),
    write_edges(OS, global, _),
    graph_write_footer(OS),
    close(OS).

:- data edge/4, node/4.
add_edge(Scope, A, B,_) :-
    edge(Scope,A,B,_), !.
add_edge(Scope, A, B,LitKey) :-
    assertz_fact(edge(Scope,A,B,LitKey)).

add_node(Scope, Id, _, _) :-
    node(Scope, Id, _, _), !.
add_node(Scope, Id, M, PKey) :-
    assertz_fact(node(Scope, Id, M, PKey)).

process_abs_db :-
    retractall_fact(edge(_,_,_,_)),
    retractall_fact(node(_,_,_,_)),
    ( % failure-driven loop
      plai_db_tuple(to_view,SgKey,_AbsInt,_Sg,_Call,_Succ,Id,Add),
      \+ Id = no,
        module_split(SgKey, M, Key),
        add_mod_to_visit(M),
        add_node(local, Id, M, Key),
        ( % failure-driven loop
          member((LitKey,PId), Add),
            module_split(LitKey, _, PM),
            ( M = PM ->
                add_edge(local,Id,PId,LitKey)
            ;
                add_edge(global,Id,PId,LitKey)
            ),
            fail
        ;
            true
        ),
        fail
    ; true
    ).

first_mod(M) :-
    to_visit_mod(M), !.

graph_write_header(S, AName) :-
    format(S, 'digraph ~w {~n ~n', [AName]),
    format(S, 'node [shape=box,fixedheight=true,height=.3];~n', []).
graph_write_footer(S) :-
    format(S, '}~n~n', []).

subgraph_write_header(S, MName) :-
    format(S, 'subgraph cluster_~w {~n~n', [MName]),
    format(S, 'label =\"~w\";~n', [MName]),
    format(S, 'style=filled;~n color=lightgrey;~n', []).
subgraph_write_footer(S) :-
    format(S, '}~n~n', []).

write_edges(S, Scope, Id) :-
    ( % failure-driven loop
      edge(Scope,Id,PId,LitKey),
        ( is_entrykey(LitKey) -> % TODO: OK?
            format(S, 'entry~w [shape=Mdiamond];~n', [PId]),
            format(S, 'entry~w -> ~w;~n', [PId,Id])
        ;
            decode_litkey(LitKey, _, _, ClN, LitN),
            format(S, '~w -> ~w [label="C~w L~w"];~n', [PId,Id,ClN,LitN])
        ),
        fail
    ;
        true
    ).

:- data to_visit_mod/1.

add_mod_to_visit(M) :-
    to_visit_mod(M), !.
add_mod_to_visit(M) :-
    assertz_fact(to_visit_mod(M)).
