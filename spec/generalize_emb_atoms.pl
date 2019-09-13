:- module(generalize_emb_atoms,
	[add_gen_emb_hint/2, 
	 add_gen_memo_hint/1,
	 cleanup_gen_hints/0,
	 cleanup_petype_masks/0,
	 there_is_gen_hint/2,
	 decide_lc_filter/2,
	 decide_lc_filter_f/2,
	 decide_generalize_atom/2,
	 get_petype_mask/2
	],[assertions, isomodes, datafacts]).

:- use_package(spec(no_debug)).

:- doc(title,"Basic operations regarding local control filtering and 
                  generalization with the embedded and memo atoms").

:- doc(author, "M. Zamalloa").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module,"This module provides a series of basic operations 
	for performing atom filtering during local control rules which are 
	based on homeomorphic embedding, as well as generalization between the 
	embedded atom and its corresponding ancestor and relatives before the 
	global control. It also provides support for the generalization among
	relative memo atoms").

:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(library(lists), [member/2]).
:- use_module(library(terms_check), [variant/2, most_specific_generalization/3]).
:- use_module(library(term_filtering/term_filtering), [filter_term/4]).
:- use_module(library(term_filtering/fr_notation), [term_to_fr/3]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9, assertion_body/7]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(ciaopp(preprocess_flags)).
:- use_module(unfold_builtins, [check_not_ignore/2]).
:- use_module(typeslib(typeslib), [get_type_definition/2]).

:- data gen_hint/2.
:- data petype_mask/2.
:- data gc_gen_mask/2.
:- data mask_mode/1.

:- pred add_gen_emb_hint(Sg,GSg) #"Adds a new gen_hint from an embedded atom".
add_gen_emb_hint(L,Anc) :-
	current_pp_flag(gen_emb_atm,relatives),
	functor(L,F,Ar),
	functor(A,F,Ar),
	decide_lc_filter(L,(FiltL,_)),
	findall(A,(gen_hint(A,_GenA),
	           decide_lc_filter(A,(FiltA,_)),
	           variant(FiltL,FiltA)),
		 AList),
	AList \== [],!,
	AList = [A1|_],gen_hint(A1,GenA),
	most_specific_generalization(L,Anc,GenL),
	most_specific_generalization(GenL,GenA,SuperGen),
	update_given_hints(AList,SuperGen),
	assertz_fact(gen_hint(L,SuperGen)),
	print_gen_hints.
add_gen_emb_hint(_L,_Anc) :- current_pp_flag(gen_emb_atm,none),!.
add_gen_emb_hint(L,_Anc) :- 
	current_pp_flag(gen_emb_atm,offline),!,
	decide_generalize_atom(L,GenL),
	assertz_fact(gen_hint(L,GenL)).
add_gen_emb_hint(L,Anc) :- % gen_emb_etm = ancestor or first rule fails
	most_specific_generalization(L,Anc,GSg),
	assertz_fact(gen_hint(L,GSg)),
	print_gen_hints.

:- pred add_gen_memo_hint/1 #"Adds a new gen_hint from a memo atom".
add_gen_memo_hint(L) :-
	current_pp_flag(gen_emb_atm,relatives),
	functor(L,F,Ar),
	functor(A,F,Ar),
	decide_lc_filter(L,(FiltL,_)),
	findall(A,(gen_hint(A,_GenA),
	           decide_lc_filter(A,(FiltA,_)),
	           variant(FiltL,FiltA)),
		 AList),
	(AList == [] -> SuperGen = L
	             ; (AList = [A1|_],
	                gen_hint(A1,GenA),
			most_specific_generalization(L,GenA,SuperGen),
			update_given_hints(AList,SuperGen))),
	assertz_fact(gen_hint(L,SuperGen)),
	print_gen_hints.
add_gen_memo_hint(L) :- 
	current_pp_flag(gen_emb_atm,offline),!,
	decide_generalize_atom(L,GenL),
	assertz_fact(gen_hint(L,GenL)).
add_gen_memo_hint(_L).


% Why not fail type loop
update_given_hints([],_).
update_given_hints([A|R],SuperGen) :-
	retractall_fact(gen_hint(A,_)),
	assertz_fact(gen_hint(A,SuperGen)),
	update_given_hints(R,SuperGen).

:- pred cleanup_gen_hints #"Clean up all gen_hints".

cleanup_gen_hints :-
	retractall_fact(gen_hint(_Id,_Ch_Tree)).

:- pred cleanup_petype_masks #"Clean up all petype_masks".

cleanup_petype_masks :-
	retractall_fact(petype_mask(_Pred,_Mask)),
	retractall_fact(gc_gen_mask(_Pred,_Mask)),
	retractall_fact(mask_mode(_)).

:- pred there_is_gen_hint(Sg,Gsg) #"Checks if it exists a gen_hint for a 
	given atom Sg. Then we may obtain the corresponding generalized atom Gsg".

there_is_gen_hint(Sg,GSg) :-
	print_gen_hints,
	current_pp_flag(gen_emb_atm,PPFlag),
	PPFlag \== none,!,
	functor(Sg,F,Ar),
	functor(Sg0,F,Ar),
	gen_hint(Sg0,GSg0),
	variant(Sg,Sg0),!,
	GSg = GSg0, 
	retract_fact(gen_hint(Sg0,GSg0)).

:- pred decide_lc_filter_f(-G,G_f) #"It performs the filtering of G returning G_f, 
	which is the Filtered part of the FR notation if there exists the 
	corresponding pe_type annotation, otherwise it does nothing". 

decide_lc_filter_f(Goal,Goal_f) :- 
	decide_lc_filter(Goal,FRGoal),
	(functor(FRGoal,',',2) -> FRGoal = (Goal_f,_Goal_r)
	                        ; Goal_f = FRGoal).

:- pred decide_lc_filter(-G,FG) #"It performs the filtering of G returning FG in 
	FR notation by looking at the corresponding pe_type assertion if so, 
	otherwise it does nothing". 

decide_lc_filter(Goal,FRGoal) :-
	functor(Goal,FGoal,_Args),
	petype_mask(FGoal,Mask),% May I put a cut here?
	%execute(Call)
	term_to_fr(Goal,Mask,FRGoal),!,
	debug('Lc Filtering:'),debug(FRGoal).
decide_lc_filter(Goal,FRGoal) :-
	functor(Goal,FGoal,_Args),
	\+ petype_mask(FGoal,Mask),
	current_pp_flag(pe_type_ignore,PPFlag),
	PPFlag \== all,
	assertion_read(Goal,M,Status,comp,Body,_VarNames,_S,_LB,_LE),
	check_not_ignore(PPFlag,M),
	member(Status,[trust,true]),
	assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
	member('basic_props:pe_type'(_Goal),Comp),
	set_fact(mask_mode(pe_type)),
	create_petype_mask(FGoal,Call),
	petype_mask(FGoal,Mask),
	%execute(Call)
	term_to_fr(Goal,Mask,FRGoal),!,
	debug('Lc Filtering:'),debug(FRGoal).
decide_lc_filter(T,T).

create_petype_mask(PredName,PeTypes) :-
	findall(FPTi,
		(member(PTi,PeTypes),functor(PTi,FPTi,_)),
		PeTypesFs),
	pt_args_to_mask(PredName,PeTypesFs,Mask),
	(mask_mode(pe_type) -> assertz_fact(petype_mask(PredName,Mask))
	                     ; assertz_fact(gc_gen_mask(PredName,Mask))).

pt_args_to_mask(PredName,PeTypes,Mask) :-
	findall(Maski,
	        (member(PeTypei,PeTypes),pt_term_to_mask(PeTypei,Maski)),
		Masks),
	Mask =..[PredName|Masks].

pt_term_to_mask(PT,Mask) :-
	split_module_atom(PT,_M,PTF),
	basic_petype(PTF,Mask),!.
pt_term_to_mask(PT,Mask) :-
	PT =..[^,Aux], Aux =..[Func|SubPeTypes],!,
	pt_args_to_mask(Func,SubPeTypes,Mask).
pt_term_to_mask(PT,Mask) :-
	get_type_definition(PT,PTDefs),
	PTDefs \== [bot],!,
	findall(Maski,
	        (member(PTDefi,PTDefs),pt_term_to_mask(PTDefi,Maski)),
	        PossibleMasks),
	(PossibleMasks = [Mask] 
	    -> true
	    ; Mask =..[;|PossibleMasks]).
pt_term_to_mask(PT,Mask) :-
	get_type_definition(PT,PTDefs),
	PTDefs == [bot],!,
	PT =..[Func|Args],
	pt_args_to_mask(Func,Args,ArgsMasks),
	Mask =..[Func|ArgsMasks].
pt_term_to_mask([],[]).
pt_term_to_mask([PT1|RestPTs],Masks) :-
	pt_term_to_mask(PT1,Mask1),
	((get_type_definition(RestPTs,RestDef),RestDef = [[],[PT1|_]])
	    -> Masks = [Mask1]
	    ; pt_term_to_mask(RestPTs,RestMasks),Masks = [Mask1|RestMasks]).

basic_petype(T,V) :- basic_petype_(T,V),!.
basic_petype(T,V) :-
	split_module_atom(T,_M,A),
	basic_petype_(A,V).

basic_petype_(dyn,0).
basic_petype_(dyn(_),0).
basic_petype_(const,0) :- mask_mode(pe_type),!.
basic_petype_(const(_),0) :- mask_mode(pe_type),!.
basic_petype_(const,1).
basic_petype_(const(_),1).
basic_petype_(f_sig,1).
basic_petype_(f_sig(_),1).
basic_petype_(term,1).
basic_petype_(term(_),1).
basic_petype_(i_sig,0).
basic_petype_(i_sig(_),0).

% TODO: duplicated?
split_module_atom(M:A,M,A) :- !.
split_module_atom(T,M,A) :-
	T =..[FQual|Args],
	module_split(FQual,M,F), !,
	A =..[F|Args].
split_module_atom(T,_,T).

:- pred get_petype_mask(F,Mask) #"Checks if there is a petype mask for the F functor".
get_petype_mask(F,Mask) :- petype_mask(F,Mask).

% :- pred get_gc_gen_mask(F,Mask) #"Checks if there is a gc_gen mask for the F functor".
% get_gc_gen_mask(F,Mask) :- gc_gen_mask(F,Mask).

:- pred decide_generalize_atom(-A,GenA) #"It performs a blind (offline-type) 
	generalization by looking only at the corresponding pe-type. To be called 
	only, when gen_emb_atm = offline.".
decide_generalize_atom(Goal,GenGoal) :-
	functor(Goal,FGoal,_Args),
	gc_gen_mask(FGoal,Mask),% May I put a cut here?
	filter_term(Goal,Mask,GenGoal,gen),!,
	debug('Offline generalization:'),debug(GenGoal).
decide_generalize_atom(Goal,GenGoal) :-
	functor(Goal,FGoal,_Args),
	\+ gc_gen_mask(FGoal,Mask),
	current_pp_flag(pe_type_ignore,PPFlag),
	PPFlag \== all,
	assertion_read(Goal,M,Status,comp,Body,_VarNames,_S,_LB,_LE),
	check_not_ignore(PPFlag,M),
	member(Status,[trust,true]),
	assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
	member('basic_props:pe_type'(_Goal),Comp),
	set_fact(mask_mode(gc_gen)),
	create_petype_mask(FGoal,Call),
	gc_gen_mask(FGoal,Mask),
	filter_term(Goal,Mask,GenGoal,gen),!,
	debug('Offline generalization:'),debug(GenGoal).
decide_generalize_atom(T,T).


print_gen_hints :-
	gen_hint(X,Y),
	debug(gen_hint(X,Y)),
	fail.
print_gen_hints.
