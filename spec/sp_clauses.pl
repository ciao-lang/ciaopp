:- module(sp_clauses,
	[
	    init_unfold/0,
	    sp_clause/2,
	    add_all_clauses/4,
	    orig_clause/3,
	    orig_predicate_names/1,
	    collect_orig_clauses/2,
	    collect_one_orig_clause/3
	],
	[assertions, datafacts]).

:- use_package(.(nounfold_stats)).

:- doc(title,"Module which handles specialized clauses").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains the operations for handling
    clauses during partial evaluation.").

:- use_module(spec(ch_trees), [clean_up_ch_trees/0]).
:- use_module(spec(unfold_builtins), [init_cut_predicates/0, decide_has_cuts/3 ]).
:- use_module(ciaopp(p_unit), [ program/2]).
:- use_module(ciaopp(p_unit/program_keys), [inverse_rewrite_source_program/2]).
:- use_module(spec(unfold_operations), [body2list/2, list2body/2]).

:- use_module(ciaopp(preprocess_flags)).

:- use_module(library(terms), [copy_args/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(lists), [length/2]).
:- use_module(spec(generalize_emb_atoms), 
	      [cleanup_gen_hints/0,cleanup_petype_masks/0]).

:- data sp_clause/2.
:- data orig_clause/3.

init_unfold:-
	current_pp_flag(local_control,off),
	current_pp_flag(fixpoint,Opt),
	Opt \== poly_spec,!.
init_unfold:-
	retractall_fact(sp_clause(_,_)),
	retractall_fact(orig_clause(_,_,_)),
	init_cut_predicates,
	program(Cls,_Ds),
	inverse_rewrite_source_program(Cls,Cls1),
	assert_all_clauses(Cls1,1),
	clean_up_ch_trees,
	cleanup_gen_hints,
	cleanup_petype_masks.
%	load_modules_with_eval.

assert_all_clauses([],_).
assert_all_clauses([clause(Head,Body)|Cls],Counter):-
	body2list(Body,LBody),
	functor(Head,F,A),
	decide_has_cuts(LBody,F,A),
	assertz_fact(orig_clause(Head,LBody,Counter)),
	NCounter is Counter + 1,
	assert_all_clauses(Cls,NCounter).
	
:- doc(add_all_clauses(Clauses,NF), "@var{Clauses} are the
     new definition of the specialized version of new predicate
     @var{NF} after unfolding.").

add_all_clauses([],NF,A,[]):-!,
	functor(NHead,NF,A),
	Body = 'basiccontrol:fail',
	assertz_fact(sp_clause(NHead,Body)).
add_all_clauses(Clauses,NF,A,Newclauses):-
	add_all_clauses_(Clauses,NF,A,Newclauses).
add_all_clauses_([],_NF,_A,[]).
add_all_clauses_([clause(Head,LBody)|Clauses],NF,A,[Cl|NewClauses]):-
 	functor(NHead,NF,A),
 	copy_args(A,Head,NHead),
	list2body(LBody,Body),
	assertz_fact(sp_clause(NHead,Body)),
	Cl = clause(NHead,Body),
	add_all_clauses_(Clauses,NF,A,NewClauses).


:- doc(orig_predicate_names(Names), "@var{Names} is the list of
     predicates in the original program.").

orig_predicate_names(Names):-
	findall(Name/Arity,
	   (orig_clause(Head,_,_), functor(Head,Name,Arity)),
	    Names0),
	sort(Names0,Names).

collect_orig_clauses(L,UnfClauses_Paths):-
	findall((clause(L,Body),Counter), orig_clause(L, Body, Counter), UnfClauses_Paths),
	length(UnfClauses_Paths,Der),
	inc_derivation_steps(Der).

:- pred collect_one_orig_clause(L,Clause,Counter) # "@var{Clause} is a
      clause which can unify with the goal @var{L}, though this
      predicate does not perform unification, since that complicates
      removal of useless clauses.".

collect_one_orig_clause(L,clause(Head,Body),Counter):-
	orig_clause(Head,Body,Counter),
	\+ \+ (L = Head),
	inc_derivation_steps(1).


