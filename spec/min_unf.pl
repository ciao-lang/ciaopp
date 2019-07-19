:- module( min_unf, 
	[
	 group_versions/4,
	 find_canonical_rep/4,
	 is_canonical/1,
	 gen_equivs/0,
	 clean_up_min_unf_facts/0,
	 generalize_and_flatten/2
	], 
	[assertions, isomodes, datafacts]).

:- use_module(spec(isomorphism)).
:- use_module(spec(unfold_operations), 
	[
	    orig_pred_name/2,
	    body2list/2,
	    list2body/2
        ]).
:- use_module(spec(unfold_builtins), [can_be_evaluated/1]).
:- use_module(ciaopp(p_unit/program_keys),
	[decode_litkey/5, get_predkey/3, predkey_from_sg/2]).
:- use_module(spec(global_control), [locate_spec_definition/3]).
:- use_module(spec(sp_clauses), [sp_clause/2]).
:- use_module(spec(ch_trees),   [ch_tree/2]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(spec(spec), [versions/2]).
:- use_module(library(terms_check), [most_specific_generalization/3]).
:- use_module(library(llists), [flatten/2]).
:- use_module(library(aggregates), [findall/3]). 
:- use_module(library(terms), [copy_args/3]). 
:- use_module(library(lists), [member/2, append/3, length/2]). 
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- doc(title,"A Minimization Algorithm based on unfolding and
matching of characteristic trees").

:- doc(author, "Germ@'{a}n Puebla").
:- doc(author, "Claudio Ochoa").

:-data equivs/2.

:- pred clean_up_min_unf_facts #"Cleans up local facts".
clean_up_min_unf_facts:-
	retractall_fact(gen_residual(_)),
	retractall_fact(case(_,_,_)),
	assertz_fact(case(0,0,0)),
	retractall_fact(equivs(_,_)),
	retractall_fact(versions(_,_)).

:- pred find_canonical_rep(+Flag,+Pred,+Spec,-Can) #" When @var{Flag}
is set to @tt{can}, it retrieves the equivalence classes of @var{Pred}
and returns the canonical representative @var{Can} of the class to
whom @var{Spec} belongs".

find_canonical_rep(no,_Orig,Sp_name,Sp_name).
find_canonical_rep(can,Orig,Sp_name,Can_name):-!,
	predkey_from_sg(Orig,Pred),
	current_fact(equivs(Pred,Equiv)),
	find_canonical_in_equiv(Sp_name,Equiv,Can_name).

find_canonical_in_equiv(Key,[H|T],Can):-
	(member(Key,H)->
	    H=[Can|_]
	;
	    find_canonical_in_equiv(Key,T,Can)).

:- pred is_canonical(+Id) #"Determines whether the predicate
identified by @var{Id} is a canonical representative of any
equivalence class".
is_canonical(Id):- 
	locate_spec_definition(Id,NF,A),
	orig_pred_name(NF,Orig_name),
	get_predkey(Orig_name,A,Pred),
	current_fact(equivs(Pred,Equiv)),!,
	is_key_canonical(Equiv,NF).

:- pred is_key_canonical(+L, +Key) #"It succeds if @var{Key} is the
canonical representative of any equivalence class in
@var{L}. Canonical representatives are always in the head of each list
representing an equivalence class".

is_key_canonical([[Key|_]|_],Key):-!.
is_key_canonical([_|T],Key):- is_key_canonical(T,Key).

:- pred gen_equivs #"It generates equivalence classes from asserted
versions".
gen_equivs:-
	retract_fact(versions(Key,Versions)),
 	simplify_versions(Versions,Equiv),
 	asserta_fact(equivs(Key,Equiv)),
 	asserta_fact(versions(Key,Versions)),
	fail.
gen_equivs.

simplify_versions([],[]).
simplify_versions([(Vers,_Class)|T],[NVers|NT]):-
	simplify_version(Vers,NVers),
	simplify_versions(T,NT).

simplify_version([],[]).
simplify_version([(_FC,Id)|T],[NF|NT]):-
	locate_spec_definition(Id,NF,_A),
	simplify_version(T,NT).

:- pred group_versions(+L,+Key,+UPD,-Ls) #"Takes a list @var{L} of
        atom calls (after unfolding), and groups them in equivalence
        classes @var{CL} (union phase). Each element of @var{L} is a
        tuple @tt{(FC,S,Sg,Cls)}, where @tt{FC} is a list of parents
        (if they are not used then @tt{no} should be used instead),
        @tt{S} is a characteristic tree, @tt{Sg} is the atom call, and
        @tt{Cls} is a list of clauses resulting from
        unfolding. @var{UPD} indicates whether the parent list
        contains specialized definitions".
group_versions(L,Key,UPD,Ls):-
	group_by_S(L,[],Key,UPD,Ls),
	print_debug_info(Ls).

:- pred group_by_S(+L,+,+,+,-CL) #"Groups elements in @var{L} into
equivalence classes".
group_by_S([],L,_,_,L).
group_by_S([(FC,S,Sg,Cls)|T],Cur_classes,Key,UPD,CL):-
	(UPD -> 
	    update_parents(FC,NFC)
	;
	    NFC = FC),
	insert_into_equiv(Cur_classes,elem(NFC,S,Sg,Cls),Key,New_classes),
	group_by_S(T,New_classes,Key,UPD,CL).

:- pred insert_into_equiv(+Class,+Elem,-,+) #"Inserts @var{Elem}
in the corresponding equivalence class @var{Class}. In this case, the
canonical representant of @var{Class} (placed in the head of the list)
must be isomorphic (according to some minimization criterion) to
@var{Elem}. If no isomorphic canonical representant is found, then a
new equivalence class is created".

%be careful, Elem is a list [F,C]
insert_into_equiv([],elem(Elem,Class,Sg,Cls),_,[(Elem,Class,Sg,Cls)]).
insert_into_equiv([(L,Cclass,Csg,Ccls)|T],elem(Elem,Class,Sg,Cls),Key,[(New_l,Cclass,Csg,Ccls)|T]):-
	isomorphic(call1(Cls,Sg,Class),call2(Ccls,Csg,Cclass),Key),!,
	append(L,Elem,New_l).
insert_into_equiv([(L,Cl,S,D)|T],elem(Elem,Class,Sg,Cls),Key,[(L,Cl,S,D)|T2]):-
	insert_into_equiv(T,elem(Elem,Class,Sg,Cls),Key,T2).

:- pred update_parents(+,-) #"Takes a list of parents (atoms) and
update them changing their names by the original predicate names".
update_parents([(Pl,Id)],[(Npl,Id)]):-
	update_parent_list(Pl,Npl).

update_parent_list([],[]).
update_parent_list([(N,Pid)|T],[(ON,Pid)|NT]):-
	get_orig_pred_name(N,ON),
	update_parent_list(T,NT).

:- pred get_orig_pred_name(+,-) #"It takes an atom and returns its
original predicate name".
get_orig_pred_name(P,OP):-
	(decode_litkey(P,N,A,Cl,L) ->
	    orig_pred_name(N,OName),
	    make_atom([OName,A,Cl,L],OP)
	;
	    OP=P).

:- pred generalize_and_flatten(+L,-FGL) #"Takes some code in @var{L},
generalizes using @tt{msg}, and flattens the list".
generalize_and_flatten(L,FGL):-
	generalize_prog(L,GL),
	flatten(GL,FGL).        

:- pred generalize_prog(+L,-GL) #"Takes a list of list of clauses
@var{L}, and replaces each list of clauses by the @tt{mgu} of all of
them".
generalize_prog([],[]).
generalize_prog([L|T],[L2|T2]):-
	(L == [] ->
	    L = L2
	;
	    L=[C|_],
	    get_list_clauses(C,LL),
	    (current_pp_flag(min_crit,residual)->
 	        add_builtins_to_clause(L,LB),
		most_specific_general_clause([LB|LL],LMsg),
		remove_evaluable_builtins(LMsg,L2)
	    ;	    	        
	        most_specific_general_clause([L|LL],L2))
	),	    
 	generalize_prog(T,T2).

:- pred most_specific_general_clause(+L,-MSG) #"Takes a list of
clauses @var{L}, and performs a @tt{msg} among all of them".

most_specific_general_clause([L],L).
most_specific_general_clause([L1,L2|T],GC):-
	most_specific_generalization(L1,L2,Gen_C),
	most_specific_general_clause([Gen_C|T],GC).

:- pred remove_evaluable_builtins(+L,-) #"Removes builtins from the
body of each clause in @var{L}".

remove_evaluable_builtins([],[]).
remove_evaluable_builtins([clause(H,B)|T],[clause(H,NB)|NT]):-
	body2list(B,LB),
	split_list(LB,Builtins,Body),
 	get_nonevaluable_builtins(Builtins,NEBuiltins),
	mark_builtins(NEBuiltins,MBuiltins),
	append(MBuiltins,Body,NBody),
	list2body(NBody,NB),
	remove_evaluable_builtins(T,NT).
 

:- pred split_list(+Body,-Builtins,-Rest) #"Splits the body @var{Body}
of a predicate into a list of builtins @var{Builtins} and the rest of
the body @var{Rest}. Builtins are always placed in the beginning of
the body, and marked by the functor @tt{builtin/1}".


split_list([builtin(B)|T],[B|T1],T2):-!,
	split_list(T,T1,T2).
split_list(L,[],L).


:- pred get_nonevaluable_builtins(+L,-R) #"Takes a list of builtins
@var{L} and filters those that are evaluable".


get_nonevaluable_builtins([],[]).
get_nonevaluable_builtins([B|T],ET):-
	copy_term(B,B_copy),
	can_be_evaluated(B_copy),!,
	get_nonevaluable_builtins(T,ET).
get_nonevaluable_builtins([B|T],[B|ET]):-
	get_nonevaluable_builtins(T,ET).

:- pred get_list_clauses(+Cl,-R) #"Takes a clause @var{Cl}, retrieves
the equivalence class corresponding to it, and collects all clauses
belonging to such equivalence class".

get_list_clauses(clause(Head,_),R):-
        functor(Head,N,A),
	orig_pred_name(N,ON),
	get_predkey(ON,A,Pred),
	current_fact(equivs(Pred,Equiv)),
	member([N|T],Equiv),
	clauses_from_versions(T,N,A,R).

clauses_from_versions([],_,_,[]).
clauses_from_versions([Key|T],Rep,A,[RClauses|T2]):-
	functor(Head,Key,A),
	findall(clause(Head,Body),
	        sp_clause(Head,Body),		
		Clauses),
	add_builtins_to_clause(Clauses,BClauses),
	rename_clauses(BClauses,Rep,A,RClauses),
	clauses_from_versions(T,Rep,A,T2).

:- pred rename_clauses(+L,+Rep,+,-R) #"Takes a list of clauses
@var{L}, and renames each of them with the name of its canonical
representative @var{Rep}".
	
rename_clauses([],_,_,[]).
rename_clauses([C|T],Rep,A,[RN|RT]):-
	rename_clause(C,Rep,A,RN),
	rename_clauses(T,Rep,A,RT).

rename_clause(clause(Head,Body),Rep,A,clause(NHead,Body)):-
	functor(NHead,Rep,A),
	copy_args(A,Head,NHead).

:- pred add_builtins_to_clause(+Cl,-R) #"Takes a list of clauses
@var{Cl}, and add builtins to each if needed. ".

add_builtins_to_clause(Clauses,BClauses):-
	(current_pp_flag(min_crit,residual)->
	    Clauses=[clause(Head,_)|_],
	    get_predname(Head,Key),
	    (gen_residual(Key)->
	        functor(Head,NF,_A),
		locate_spec_definition(Id,NF,_),
		ch_tree(Id,S),
		get_builtins_per_cl(S,Builtins),
		add_builtins_to_cl(Clauses,Builtins,BClauses)
	    ;
		BClauses=Clauses)
	;
	    BClauses=Clauses).

get_predname(Head,Pred):-
        functor(Head,N,A),
	orig_pred_name(N,ON),
	get_predkey(ON,A,Pred).

:- pred get_builtins_per_cl(+L,-R) #"Given a list of chtrees @var{L},
it retrieves their builtins in @var{R}".

get_builtins_per_cl([],[]).
get_builtins_per_cl([S|T],[B|T2]):-
	get_builtins(S,B),
	get_builtins_per_cl(T,T2).

:- pred add_builtins_to_cl(+L,+B,-R) #"Given a list of clauses
@var{L}, and a list of builtins @var{B}, it marks all builtins with a
@tt{builtin} functor, and then adds them to the beginning of the body
of each clause".

add_builtins_to_cl([],_,[]).
add_builtins_to_cl([clause(H,B)|T],[Builtins|BuiltinsT],[clause(H,BB)|T2]):-
 	mark_builtins(Builtins,MBuiltins),
	append_list_conj(MBuiltins,B,BB),
	add_builtins_to_cl(T,BuiltinsT,T2).

append_list_conj([],Body,Body).
append_list_conj([H|T],Body,Result):-!,
	append_list_conj(T,Body,Tmp_Result),
	Result = (H,Tmp_Result).
	
mark_builtins([],[]).
mark_builtins([B|T],[(builtin(B))|MT]):-
	mark_builtins(T,MT).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  DEBUG

:- use_module(engine(io_basic), [nl/0]).
:- use_module(library(write), [write/1]).

debug:-fail.

print_debug_info(Ls) :-
	    debug,!,
	    print_cases_info,
	    print_list(Ls).
print_debug_info(_).


print_list([]).
print_list([(L,S)|T]):-
	write('Class for '),write(S),write(':'),nl,
	length(L,Len),write('Total:'),write(Len),nl,
	write(L),nl,nl,
	print_list(T).

print_cases_info:-
	current_fact(case(A,B,C)),
	write('No builtins:'),write(A),nl,
	write('Variants:'),write(B),nl,
	write('Same val:'),write(C),nl.
