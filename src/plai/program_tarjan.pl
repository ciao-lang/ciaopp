:- module(_, [program_tarjan/1, program_recursive_classify/3, program_recursive_class/2], [assertions, datafacts]).

:- doc(summary, "SCCs of program predicates using tarjan implementation asserting vertexes from @mod{contrib/modgraph/mtarjan.pl}").

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [member/2]).

:- use_module(library(mtarjan), [find_sccs/3]).

:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3]).
:- use_module(ciaopp(p_unit/program_keys),
	[get_predkey/3, predkey_from_sg/2, decode_predkey/3]).

:- data program_vertex/1, program_edge/2. % predicates for enumerating program
:- data recursive_class_elem/2.
% Given an Identifier for the recursive class, it enumerates all its elements.
:- data recursive_class_id/2.
% Given an element it returns the identifier of the RC that it belongs to.

cleanup_program_tarjan :-
	retractall_fact(program_vertex(_)),
	retractall_fact(program_edge(_,_)),
	retractall_fact(recursive_class_elem(_,_)),
	retractall_fact(recursive_class_id(_,_)).

program_tarjan(Program):-
	cleanup_program_tarjan,
	program_strong_connected_components(Program,_Calls,_P).

program_strong_connected_components(Program,_Calls,_Ps) :-
	init_program_graph(Program),
	find_sccs(program_vertex, program_edge, SCCs),
	assert_recursive_classes(SCCs).

:- export(add_rc_elem/2).
add_rc_elem(Id, Elem) :-
	assertz_fact(recursive_class_elem(Id, Elem)),
	assertz_fact(recursive_class_id(Elem, Id)).

assert_recursive_classes([]).
assert_recursive_classes([RC|RCs]) :-
	assert_recursive_class(RC),
	assert_recursive_classes(RCs).

assert_recursive_class([Id|Elems]) :-
	add_rc_elem(Id, Id),
	assert_recursive_class_(Elems, Id).

assert_recursive_class_([], _).
assert_recursive_class_([E|Elems], Id) :-
	add_rc_elem(Id, E),
	assert_recursive_class_(Elems, Id).

program_recursive_classify(Clauses,ClRecs,RecPreds) :-
	retractall_fact(rec_pred(_)),
	program_recursive_classify_(Clauses,ClRecs),
	findall(P, rec_pred(P), RecPreds).

program_recursive_classify_([],[]).
program_recursive_classify_([Cl:_ClKey|Cls],[ClR|ClRs]) :-
	Cl = clause(Head,B),
	predkey_from_sg(Head, PKey),
	program_classify_body(B, PKey, ClR),
	( ClR = nr -> true
	;
	    functor(Head, F, A),
	    add_rec_pred(F/A)
	),
	program_recursive_classify_(Cls,ClRs).

program_classify_body((Lit, Body), Cl, LitRec) :- !,
	program_classify_literal(Cl, Lit, LitRec),
	program_classify_body(Body, Cl, LitRec).
program_classify_body(Lit, Cl, LitRec) :-
	program_classify_literal(Cl, Lit, LitRec).

program_classify_literal(_, !, _) :- !.
program_classify_literal(Cl, Lit:_BodyKey, LitRec) :- !,
	predkey_from_sg(Lit, PKey),
	( same_scc(Cl, PKey) ->
	    LitRec = r
	;   true).
program_classify_literal(Cl, LitH:_BodyKey, LitRec) :-
	type_of_goal(metapred(_Type,_Meta),LitH), !,
	functor(LitH,_,A),
	classify_meta_calls(A,LitH,Cl,LitRec).

classify_meta_calls(0,_,_,_) :- !.
classify_meta_calls(A,G,Cl,LitRec):-
	A > 0,
	arg(A,G,GA),
	( nonvar(GA), GA='$'(Term,Body,goal) ->
	  ( var(Term) -> true
	   ; program_classify_body(Body,Cl,LitRec))
	; true
	),
	A1 is A-1,
	classify_meta_calls(A1,G,Cl,LitRec). % Is this call needed?

:- data rec_pred/1.

add_rec_pred(P) :-
	rec_pred(P), !.
add_rec_pred(P) :-
	assertz_fact(rec_pred(P)).

same_scc(Key1, Key2) :-
	recursive_class_id(Key1, KeyN), !,% Key1 is unique
	recursive_class_elem(KeyN, Key2), !.

program_recursive_class(P/A, Class) :-
	get_predkey(P, A, PKey),
	recursive_class_id(PKey, ClassId),
	findall(Key, recursive_class_elem(ClassId,Key), ClassKeys),
	decode_predkeys(ClassKeys, Class).

decode_predkeys([], []).
decode_predkeys([PK|ClassKeys], [P/A|Class]) :-
	decode_predkey(PK,P,A),
	decode_predkeys(ClassKeys, Class).

% ------------------------------------------------------------
init_program_graph(Program) :-
	( % failure-driven loop
	  member(clause(H,B):_, Program),
	    predkey_from_sg(H, PKey),
	    assertz_fact(program_vertex(PKey)), % TODO: if not added
	    add_edges_body(B, PKey),
	    fail
	; true).

add_edges_body((Lit, RBody), PKey) :- !,
	add_edge_lit(Lit,PKey),
	add_edges_body(RBody, PKey).
add_edges_body(Lit, PKey) :-
	add_edge_lit(Lit,PKey).

add_edge_lit(!, _) :- !.
add_edge_lit(true, _) :- !.
add_edge_lit(LitH:_BodyKey, PKey):-
	type_of_goal(metapred(_Type,_Meta),LitH), !,
	functor(LitH,_,A),
	meta_calls(LitH,A,PKey).
add_edge_lit(LitH:_BodyKey, _PKey):-
	type_of_goal(impl_defined,LitH), !.
add_edge_lit(LitH:_BodyKey, _PKey):-
	type_of_goal(wam_builtin,LitH), !.
add_edge_lit(LitH:_BodyKey, PKey):-
	predkey_from_sg(LitH, LitPKey),
	assertz_fact(program_edge(PKey, LitPKey)).

meta_calls(_G,0,_) :- !.
meta_calls(G,A,PKey):-
	A > 0,
	arg(A,G,GA),
	( nonvar(GA), GA='$'(Term,Body,goal) ->
	  ( var(Term) -> true
	   ; add_edges_body(Body,PKey))
	; true
	),
	A1 is A-1,
	meta_calls(G,A1,PKey).
