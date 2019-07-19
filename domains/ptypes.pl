:- module(ptypes,[
	ptypes_widen/3,ptypes_widencall/3
	     ],
	     [assertions,regtypes,basicmodes
	     ]).

:- doc(title,"Types Abstract Domain").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").

:- doc(module,"

This module implements the topological clash widening operator for
types domain.

").
:- use_module(library(lists), 
	[
	    member/2,
	    reverse/2
	]).


:- use_module(library(sort), 
	[
	    sort/2
	]).

:- use_module(domain(termsd)).
:- use_module(typeslib(typeslib), 
	[
	    compound_pure_type_term/4,
	    construct_compound_pure_type_term/2,
	    dz_type_included/2,
	    em_defined_type_symbol/2,
	    insert_rule/2,
	    new_type_symbol/1,
	    unfold_type_union_1/4
	]).

ptypes_widencall(Prime0,Prime1,Result):-
	(
	    terms_less_or_equal(Prime1,Prime0) ->
	    Result = Prime0
	;
	    terms_compute_lub_el(Prime0,Prime1,Prime),
	    henten(Prime0,Prime,Prime2),
	    ( 
		terms_identical_abstract(Prime2,Prime) ->
		Result = Prime1
	    ;
		Result = Prime2
	    )
	).

ptypes_widen(Prime0,Prime1,NewPrime):-
	terms_compute_lub_el(Prime0,Prime1,Prime),
	henten(Prime0,Prime,NewPrime).

henten('$bottom','$bottom','$bottom').
henten('$bottom',Prime,Prime).
henten([],[],[]).
henten([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
	hentenwid(T1,T2,T,[],[],no),
	henten(Prime0,Prime,NewPrime).

samepf([],[]).
samepf([T|Def],[T2|Def2]):-
	samefunctor(T,T2),!,
	samepf(Def,Def2).

samefunctor(T,T).
samefunctor(T,T2):-
	compound_pure_type_term(T,_Term,F,A),!,
	compound_pure_type_term(T2,_Term2,F,A).
	
hentenancestor(T2,Seen,NT):-
	member((T,NT),Seen),
	dz_type_included(T2,T).
	
hentendef([],[],[],_,_,_).
hentendef([T1|Def1],[T2|Def],[T|NewDef],Seen,Prev,Flag):-
	hentenwid(T1,T2,T,Seen,Prev,Flag),
	hentendef(Def1,Def,NewDef,Seen,Prev,Flag).

hentenwid_arg(0,_Term1,_Term2,_NewTerm,_Seen,_Prev,_Flag).
hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag):-
	arg(A,Term2,Arg2),
	arg(A,Term1,Arg1),
	hentenwid(Arg1,Arg2,NewArg,Seen,Prev,Flag),	
	arg(A,NewTerm,NewArg),
	A1 is A - 1,
	hentenwid_arg(A1,Term1,Term2,NewTerm,Seen,Prev,Flag).

hentenwid(T1,T2,T,Seen,Prev,Flag):-
	em_defined_type_symbol(T2,Def),!,
	(
	    member((T2,T),Seen) -> true
	;
	    (
		(
		    em_defined_type_symbol(T1,Def1) ->
		    NewPrev = [T1|Prev],
		    (
			(Flag == yes;member(T1,Prev)) ->
			 NewFlag = yes
		    ;
			NewFlag = Flag
		    )
		;
		    NewPrev = Prev,
		    Def1 = [T1],
		    NewFlag = Flag
		),
		(
		    (samepf(Def,Def1),NewFlag = no) ->
		     new_type_symbol(NT),
		     hentendef(Def1,Def,NewDef,[(T2,NT)|Seen],NewPrev,NewFlag),
		     (
			 Def == NewDef ->
			 T = T2
		     ;
			 T = NT,
			 unfold_type_union_1(NewDef, [T], [], TmpDefin),
			 reverse(TmpDefin,NewDef_u),
			 sort(NewDef_u,NewDef_u_s),
			 insert_rule(T,NewDef_u_s)
		     )
		;
		    (
			hentenancestor(T2,Seen,T) ->
			true
		    ;
			T = T2
		    )
		)
	    )
	).

hentenwid(T1,T2,T,Seen,Prev,Flag):-
	compound_pure_type_term(T2,Term2,F,A),!,
	compound_pure_type_term(T1,Term1,F,A),
	functor(NewTerm,F,A),
	hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag),
	construct_compound_pure_type_term(NewTerm,T).

hentenwid(_T1,T2,T2,_Seen,_Prev,_Flag).	
