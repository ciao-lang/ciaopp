:- module(useless_clauses,
	[ decide_remove_useless_pre/6,
	  decide_remove_useless_post/6,
	  check_not_useless_pre/5,
	  check_not_useless_post/5
	],[]).

:- use_package(assertions).

:- doc(title,"Removal of Useless Clauses During Program Specialization").

:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains the implementation of the
      removal of useless clauses.").

:- use_module(library(lists), [member/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(ciaopp(plai/domains), [call_to_entry/10]).
:- use_module(ciaopp(plai/fixpo_ops), [bottom/1]).

decide_remove_useless_pre(Clauses,AbsInt,Sg,Sv,Proj,NClauses):-
	current_pp_flag(rem_use_cls,RUC),
	(member(RUC,[pre,both]) ->
	    filter_useless_clauses(Clauses,AbsInt,Sg,Sv,Proj,NClauses)
	;
	    NClauses = Clauses).

decide_remove_useless_post(Clauses,AbsInt,Sg,Sv,Proj,NClauses):-
	current_pp_flag(rem_use_cls,RUC),
	(member(RUC,[post,both]) ->
	    filter_useless_clauses(Clauses,AbsInt,Sg,Sv,Proj,NClauses)
	;
	    NClauses = Clauses).

filter_useless_clauses([],_AbsInt,_Sg,_Sv,_Proj,[]).
filter_useless_clauses([C|Cs],AbsInt,Sg,Sv,Proj,NCs):-
	useless_clause(C,AbsInt,Sg,Sv,Proj),!,
	filter_useless_clauses(Cs,AbsInt,Sg,Sv,Proj,NCs).
filter_useless_clauses([C|Cs],AbsInt,Sg,Sv,Proj,[C|NCs]):-
	filter_useless_clauses(Cs,AbsInt,Sg,Sv,Proj,NCs).

useless_clause(residual(C),AbsInt,Sg,Sv,Proj):-!,
	useless_clause(C,AbsInt,Sg,Sv,Proj).
useless_clause(fact(C),AbsInt,Sg,Sv,Proj):-!,
	useless_clause(C,AbsInt,Sg,Sv,Proj).
useless_clause(clause(Head,_),AbsInt,Sg,Sv,Proj):-
	varset(Head,Hv),
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,[],Proj,Entry,_),
	bottom([Entry]).


:- pred check_not_useless_pre(Clause,AbsInt,Sg,Sv,Proj) # "If this
	predicate fails, this particular clause is useless and can be
	removed. If removal of useless clauses has not been selected,
	then we do nothing".

check_not_useless_pre(Clause,AbsInt,Sg,Sv,Proj):-
	current_pp_flag(rem_use_cls,RUC),
	(member(RUC,[pre,both]) ->
	    \+ useless_clause(Clause,AbsInt,Sg,Sv,Proj)
	;
	    true).

check_not_useless_post(Clause,AbsInt,Sg,Sv,Proj):-
	current_pp_flag(rem_use_cls,RUC),
	(member(RUC,[post,both]) ->
	    \+ useless_clause(Clause,AbsInt,Sg,Sv,Proj)
	;
	    true).
