
:- data pgm_required_type/1. %% For user programs.
:- data lib_required_type/1. %% For libraries.

required_type(T):-
	pgm_required_type(T).
required_type(T):-
	lib_required_type(T).

:- use_module(library(assoc), [get_assoc/3]).

%% is_required_type(T):-
%% 	required_type(T).

recorda_required_types([T|Types]):-
	assert_required_type(T),
	recorda_required_types(Types).
recorda_required_types([]).

assert_required_type(T):-
	required_type(T), !.
assert_required_type(T):-
	functor(T,F,A),
	A1 is A+1,
	functor(G,F,A1),
	type_of_goal(imported,G), !.
assert_required_type(T):-
	asserta_fact(pgm_required_type(T)).

get_required_types(TypeRules):-
	findall(T,required_type(T),L),
%% 	findall(UT,user_type(UT/1),UL),
%% 	append(L,UL,TL),
	TL = L,
	debug_message("CALL: ~q",[get_required_rules(TL, TypeRules0)]),
	get_required_rules(TL, TypeRules0),
	debug_message("EXIT: ~q",[get_required_rules(TL, TypeRules0)]),
	debug_message("CALL: ~q",[filter_required_rules(TypeRules0, TypeRules)]),
%	filter_required_rules(TypeRules0, TypeRules),
	TypeRules0 = TypeRules,
	debug_message("EXIT: ~q",[filter_required_rules(TypeRules0, TypeRules)]).

%% filter_required_rules([Rule|Rules0],[Rule|Rules]):-
%% 	Rule=typedef('::='(T,_)),
%% 	norm_goal_prop(T,P,_),
%% 	\+ type(P), !,
%% 	filter_required_rules(Rules0,Rules).
%% filter_required_rules([_Rule|Rules0],Rules):-
%% 	filter_required_rules(Rules0,Rules).
%% filter_required_rules([],[]).


insert_renamed_type_defs([],_).
insert_renamed_type_defs([TypeRen-Def|TypeDefs],Rens):-
	rename_typedef(Def,Rens,RenDef),
	insert_rule(TypeRen,RenDef),
	insert_renamed_type_defs(TypeDefs,Rens).

rename_typedef([],_,[]).
rename_typedef([D|Def],Rens,[RD|RenDef]):-
	( get_assoc(D,Rens,RD0) ->
	    RD = RD0
	; compound_pure_type_term(D, Comp, _, _) ->
	    Comp =.. [Fct|Args],
	    rename_typedef(Args,Rens,RenArgs),
	    RenComp =.. [Fct|RenArgs],
	    construct_compound_pure_type_term(RenComp, RD)
	;   RD = D
	),
	rename_typedef(Def,Rens,RenDef).
