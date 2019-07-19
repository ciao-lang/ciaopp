:- module(spec_multiple,
	[
	    mult_spec/7,
	    mult_spec_unf/3,
	    publish_pred_name/2,
	    reset_mult_spec/0,
	    all_versions/5,
	    second_components/2,
	    first_components/2,
	    simplif/3,
	    equalities/2,
	    search_version/3,
	    get_version_name/4,
	    reunion_phase/4,
	    split_phase/1
	],
	[assertions, datafacts]).

:- doc(title,"Multi Variant Program Specialization").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains the required machinery for
   performing minimal multiple specialization for allowing all
   optimizations based on the notiong of @em{abstract executability}.").

:- doc(bug,"1. Though it seems to work, it is unclear why keys for
       external entries sometimes have two and sometimes have tree
       elements (same as clause identifiers)").

:- use_module(spec(spec),
	[versions/2, simplify_versions/4, erase_all_local_data/0]).

:- use_module(spec(ch_trees),           [ch_tree/2]).
:- use_module(spec(sp_clauses),         [sp_clause/2]).
:- use_module(spec(spec_gen_pred_vers), [write_pred_versions/5]).
:- use_module(spec(spec_iterate),       [init_clause_result/0]).
:- use_module(spec(min_unf),            [group_versions/4]).
:- use_module(spec(global_control),     [spec_def_for/8, spec_wrt/3]).
:- use_module(ciaopp(plai/domains),            [identical_proj/5]).
:- use_module(spec(s_simpspec),         [make_atom/2, newformat/2]).
:- use_module(spec(s_simpspec), [list_format/2]).

:- use_module(ciaopp(p_unit),          [new_predicate/3, predicate_names/1]).
:- use_module(ciaopp(p_unit/itf_db),          [assert_itf/5, retract_itf/5]).
:- use_module(ciaopp(p_unit/program_keys),
        [decode_litkey/5, decode_entrykey/4, decode_predkey/3, get_predkeys/2,
	 get_predkey/3]).
:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(ciaopp(plai/plai_errors)).

:- use_module(spec(spec_support), 
	[record_latest_replacement/3, get_simplif/2, prepare_ai_info/2]).

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(aggregates), [findall/3]). 
:- use_module(library(lists), [member/2, append/3, length/2]). 
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]). 
:- use_module(library(idlists), [memberchk/2, subtract/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).


:- pred mult_spec(+Program,+Dicts,+Preds,+Abs,-Simp_S_Prog,-Simp_S_Dicts,-Simp_S_Preds).
mult_spec(Program,Dicts,Preds,Abs,Simp_S_Prog,Simp_S_Dicts,Simp_S_Preds):-
        get_predkeys(Preds,Keys),
        predicate_versions(Keys,Abs),
        prepare_ai_info(Keys,Abs),
        split_phase(Keys),
%	count_versions(Keys),
        enumerate_versions(Keys,Preds),
        replacements(Keys,Preds),!, % leaves choice_points!
	init_clause_result,
        write_pred_versions(Program,Dicts,Abs,S_Prog,S_Dicts),!, % leaves choice_points!
	simplify_versions(S_Prog,S_Dicts,Simp_S_Prog,Simp_S_Dicts),
	new_preds(Preds,Simp_S_Preds).

:- pred mult_spec_unf(+Preds,+Abs,-Versions).
%OV: #Versions in original prog
%EV: #quasi-isomorphic versions
%RV: #versions after reunion phase
%MV: #versions after minimization phase

mult_spec_unf(Preds,Abs,[OV,EV,RV,MV]):-
        get_predkeys(Preds,Keys),
        predicate_versions_unf(Keys,Abs,OV,EV,RV),
        prepare_ai_info(Keys,Abs),
        split_phase(Keys),
	count_min_versions(Keys,MV).

count_min_versions([],[]).
count_min_versions([Key|Keys],[L|T]):-
	current_fact(versions(Key,Ls)),	
	length2(Ls,L),
	count_min_versions(Keys,T).

length2([],[]).
length2([(H,_)|T],[L|R]):-
	length(H,L),
	length2(T,R).

reset_mult_spec:-
	retractall_fact(constraint(_,_)),
	retractall_fact(simplif(_,_,_)),
	retractall_fact(equalities(_,_)).

:- pred original_versions(+Preds,+Abs) #"We collect all the versions
generated for the analyser for each predicate.".
original_versions([],_).
original_versions([Key|Preds],Abs):-
        findall(([(F,C)],S), 
                ((current_fact(complete(Key,Abs,_,_,_,C,F))),
		 get_simplif(C,S)),Ls),
% turbo
 %%         sort_parents(Ls,SortedLs),
 %% 	length(Ls,L),
 %% 	length(SortedLs,SL),
 %% 	(L \== SL ->
 %% 	    format(user,"parents repetidos ~n ~a ~n ~a ~n",[Ls,SortedLs])
 %% 	;
 %% 	    true),
	SortedLs = Ls,
        asserta_fact(versions(Key,SortedLs)),
        original_versions(Preds,Abs).

:- pred predicate_versions(+Preds,+Abs) #" Creates the first set of
versions by collapsing all the versions for a predicate that have the
same set of simplifications".
predicate_versions([],_).
predicate_versions([Key|Preds],Abs):-
        findall(([(F,C)],S), % TODO: extract goal?
                ((current_fact(complete(Key,Abs,_,_,_,C,F),_)),
                 get_simplif(C,S)),Ls),
        SortedLs =Ls,
        collapse(SortedLs,NewList),
        asserta_fact(versions(Key,NewList)),
        predicate_versions(Preds,Abs).

:- pred predicate_versions_unf(+Abs,-Preds,-Orig_versions,-Equiv_versions, -Reunion_versions).
predicate_versions_unf([],_,[],[],[]).
predicate_versions_unf([Key|Preds],Abs,[L|T],[Eq|T2],[RV|T3]):-
 	findall(([(F,C)],S,Sg,Cls),
 	        (current_fact(complete(Key,Abs,_,_,_,Id,F)),
 		 spec_wrt(Id,Abs,C), 
 		 spec_def_for(_Key,Sg,_Sv,_Proj,Abs,C,NF,A),
 		 get_definition_for(NF,A,Cls),
		 ch_tree(C,S)
		 ),
 	         TmpLs),
        length(TmpLs,L),
	reunion_phase(TmpLs,Key,true,Ls),
	length2(Ls,RV),
        get_lengths(Ls,Eq),
        predicate_versions_unf(Preds,Abs,T,T2,T3).

get_definition_for(NF,A,Cls):-
	functor(Head,NF,A),
	findall(clause(Head,Body),
	        sp_clause(Head,Body),
		Cls).


reunion_phase(Ls1,Key,UPD,Ls):-
 	group_versions(Ls1,Key,UPD,Ls2),
 	simplify_list(Ls2,Ls),
        asserta_fact(versions(Key,Ls)).

:- pred simplify_list(+,-) #"Gets rid of Sg and Cls in the input list".
simplify_list([],[]).
simplify_list([(L,S,_Sg,_Def)|T],[(L,S)|T2]):-
	simplify_list(T,T2).

:- pred get_lengths(+L,-R) #"When minimization criterion is
@tt{residual}, it returns the lengths of first element of tuples in
@var{L}.".
get_lengths(L,R):-
	current_pp_flag(min_crit,residual),!,
	get_lengths_(L,R).
get_lengths(_,[]).

get_lengths_([],[]).
get_lengths_([(L,_)|T],[Len|T2]):-
	length(L,Len),
	get_lengths_(T,T2).

%% :- pred sort_parents(+Versions,-NewVersions) #"@var{NewVersions} is
%% @var{Versions} where all the list of parents have been sorted, and so
%% have no repetitions".
%% sort_parents([],[]).
%% sort_parents([([(F,C)],S)|More],[([(SortedF,C)],S)|SortedMore]):-
%%         sort(F,SortedF),
%%         sort_parents(More,SortedMore).

:- pred collapse(+Completes,-Versions) #"@var{Versions} results from
collapsing in one all the completes with the same set of
simplifications".
collapse([],[]).
collapse([(Completes,S)|Xs],NewXs):-
        (coll(Xs,(Completes,S),MoreXs)->
             collapse(MoreXs,NewXs)
        ;
             collapse(Xs,MoreXs),
             NewXs = [(Completes,S)|MoreXs]).

coll([(Comp2,S)|Xs],(Completes,S),[(NewComp,S)|Xs]):-
        !,
        append(Completes,Comp2,NewComp).
coll([X|Xs],(F,S),[X|Ys]):-
        coll(Xs,(F,S),Ys).

:- pred split_phase(+Keys) #"This predicate accomplishes the step2 of
the algorithm for obtaining specialized arguments".
split_phase(Keys):-
        first_constraints(Keys),
        split_iterate.

:- pred first_constraints(+Preds) #"Here we get all the constraints
introduced by the preliminary versions of predicates obtained in
@tt{predicate\_versions}".
first_constraints([]).
first_constraints([Key|Preds]):-
        current_fact(versions(Key,Vers)),
        versions2parents(Vers,Parents),
        constraints(Parents),
        first_constraints(Preds).

:- pred versions2parents(+Versions,-Parents) #"In @var{Parents} we
have all the information about where in the program each version is
called. As there may be more than one occurrence for each goal, we
gather in a list all the occurrences of a goal".
versions2parents([],[]).
versions2parents([V|Vers],[P|Parents]):-
        ver2parent(V,P),
        versions2parents(Vers,Parents).

ver2parent(([],_),Parents):-
        close_parents(Parents).
ver2parent(([(F,_)|More],_),Parents):-
        include(F,Parents),
        ver2parent((More,_),Parents).

include([],_).
include([(P,N)|MoreParents],Parents):-
        include_parent((P,N),Parents),
        include(MoreParents,Parents).

include_parent((P,N),[(P,L)|_]):-
        !,
        include_number(N,L).
include_parent((P,N),[_|More]):-
        include_parent((P,N),More).
include_number(N,[N|_]):-!.
include_number(N,[_|L]):-
        include_number(N,L).

close_parents([]):-
        !.
close_parents([(_,L)|More]):-
        close_list(L),
        close_parents(More).

close_list([]):-!.
close_list([_|L]):-
	close_list(L).

:- data constraint/2.

:- pred constraints(+Parents) #"With the information about places
where each version is called in @var{Parents}, we find all the
constraints we can deduce".
constraints([]).
constraints([_]). % IG missing cut?
constraints([P|Parents]):-
        constr(P,Parents,NewParents),
        constraints(NewParents).

constr([],P,P).
constr([(Father,List)|More],Parents,NewParents):-
	decode_litkey(Father,N,A,_,_),!,
        subtract_list(Parents,Father,MoreParents,Lists),
%	simplify_constraint([List|List]),
        asserta_fact(constraint(N/A,[List|Lists])),
        constr(More,MoreParents,NewParents).
constr([(_query,_)|More],Parents,NewParents):-
	constr(More,Parents,NewParents).

subtract_list([],_,[],[]).
subtract_list([P|Parents],Father,NewParents,Lists):-
        my_subtract(P,[(Father,L)],NewP),
        case_subtract(NewP,L,NewParents,MoreParents,Lists,MoreLists),
        subtract_list(Parents,Father,MoreParents,MoreLists).

case_subtract([],L,NewParents,MoreParents,Lists,MoreLists):-
        !,
	NewParents = MoreParents,
        Lists = [L|MoreLists].
case_subtract(NewP,L,NewParents,MoreParents,Lists,MoreLists):-
        nonvar(L),
        !,
	NewParents = [NewP|MoreParents],
	Lists = [L|MoreLists].
case_subtract(NewP,_,[NewP|MoreParents],MoreParents,MoreLists,MoreLists).

:- pred split_iterate #"Here we process all the constraints. We try
one at a time. If the constraint holds, we study the following one. If
it does not hold, we split the corresponding versions and check if
this imposes new constraints. e finish when there are no more
constraints to study".
split_iterate:-
        current_fact(constraint(N/A,Versions),Ref),
        !,
        erase(Ref),
        get_predkey(N,A,Key),
        current_fact(versions(Key,Vers),Ref2),
        erase(Ref2),
        partition(Vers,Versions,NewVers),
        asserta_fact(versions(Key,NewVers)),
        subtract(NewVers,Vers,Changed),
        versions2parents(Changed,Parents),
        constraints(Parents),
        split_iterate.
split_iterate.

:- pred partition(+Versions,+Constraint,-NewVersions)
#"@var{NewVersions} is the result of applying @var{Constraint} to
@var{Versions}".

partition([],_,[]).
partition([Set|Sets],Set_list,NewSets):-
        split(Set,Set_list,Split_set),
        append(Split_set,MoreSets,NewSets),
        partition(Sets,Set_list,MoreSets).

split(([],_),_,[]):-!.
split((Completes,Simp),Set_list,[(Intersection,Simp)|MoreSets]):-
        first_intersection(Completes,Set_list,Intersection,Remains),
        second_intersection(Completes,Remains,Still_remains),
        !,
        my_subtract(Completes,Intersection,NewSet),
        split((NewSet,Simp),Still_remains,MoreSets).
split(Set,_,[Set]).

first_intersection(Set,[First|Remains],Intersection,Remains):-
        get_by_number(Set,First,Intersection),
        Intersection \== [],
        !.
first_intersection(Set,[_|Rest],Intersection,Remains):-
        first_intersection(Set,Rest,Intersection,Remains).

second_intersection(Set,[First|Rest],[First|Rest]):-
        get_by_number(Set,First,Inter),
        Inter \==[],
        !.
second_intersection(Set,[_|Rest],Remains):-
        second_intersection(Set,Rest,Remains).

get_by_number([],_,[]).
get_by_number([(Complete,N)|More],Set,[(Complete,N)|Intersect]):-
        memberchk(N,Set),
        !,
        get_by_number(More,Set,Intersect).
get_by_number([_|More],Set,Intersect):-
        get_by_number(More,Set,Intersect).

:- pred enumerate_versions(+Keys,+Preds) #"Once we have the final set
of specialized versions, for all the predicates in the program, we
must give a name to each version.".

enumerate_versions([],_).
enumerate_versions([Key|Keys],[(N/A)|Preds]):-
        current_fact(versions(Key,Versions),Ref),
        erase(Ref),
        enumerate(Versions,NumVersions,Key,N,A),
	original_version_first(N,NumVersions,Ord_NumVersions),
        asserta_fact(versions(Key,Ord_NumVersions)),
        enumerate_versions(Keys,Preds).

original_version_first(N,NumVersions,Ord_NumVersions):-
	eliminate_if_found(NumVersions,N,NewNumVersions,Info),
	(nonvar(Info) ->
	    Ord_NumVersions = [(Info,N)|NewNumVersions]
	;
	    Ord_NumVersions = NumVersions).

eliminate_if_found([],_,[],_).
eliminate_if_found([(Version,N)|MoreVersions],N,NewVersions,Info):-!,
	Info = Version,
	NewVersions = MoreVersions.
eliminate_if_found([Version|MoreVersions],N,[Version|NewVersions],Info):-
	eliminate_if_found(MoreVersions,N,NewVersions,Info).

:- pred enumerate(+Vers,-NumVers,+Key,+Name,+Arity) #"Whenever a
version is used from an entry or module declaration we try to give it
that name. When it is not used from outside we are free to generate a
new version for it. However, if it has no simplifications and no other
version has received it, we give this version the original name of the
predicate.".

enumerate(Vers,NumVers,Key,Name,Arity):-
	suggested_names(Vers,Sug_names),
	findall(N,(name_conflicts(Sug_names,[],N)),Conflicts),
	conflicts(Conflicts),
	assignments(Vers,Sug_names,Conflicts,NumVers,Key,Name,Arity,ANames),
	check_assignments(NumVers,Sug_names,Arity),
	decide_remove_original_exported_predicate(Sug_names,ANames,Name,Arity).

:- pred suggested_names(Vers,Sug_Names) # "Collects the names
suggested in the entry declarations present for the module.".

suggested_names([],[]).
suggested_names([(Completes,_)|Versions],[L|Names]):-
	get_entry_numbers(Completes,L),
	suggested_names(Versions,Names).

get_entry_numbers([],[]).
get_entry_numbers([(Parents,_)|Completes],Entries):-
	get_entry_in_parents(Parents,L),
	append(L,More,Entries),
	get_entry_numbers(Completes,More).

% TODO: replace by is_entrykey and decode_entrykey
get_entry_in_parents([],[]).
get_entry_in_parents([(K,_N)|Parents],More):-
	decode_litkey(K,_,_,_,_),!,
	get_entry_in_parents(Parents,More).
get_entry_in_parents([(Clause,_N)|Parents],[Name|More]):-
	decode_entrykey(Clause,Name,_Arity,_),!,
	get_entry_in_parents(Parents,More).
get_entry_in_parents([(Pred,_N)|Parents],[Name|More]):-
	decode_predkey(Pred,Name,_A),  % IG not possible?
 	get_entry_in_parents(Parents,More).

assignments([(Completes,[])],[[]],_,[(Completes,Name)],_,Name,_Arity,[]):-!.
assignments(Vers,Sug_names,Conflicts,NumVers,Key,Name,Arity,ANames):-
	assign(Vers,Sug_names,Conflicts,NumVers,Key,Name,Arity,[],ANames).

:- pred
assign(+Vers,+Sug_names,+Conflicts,+NumVers,+Key,+Name,+Arity,+AN,+ANames)
# "This is where each version gets a name assigned. If several entries
with the same suggested name exist, then none of them gets the
original name in order to avoid confussion. This is detected by
checking membership of the candidate name in @var{Conflict}. ".

assign([],[],_,[],_,_,_,ANames,ANames).
assign([Ver|Vers],[[]|Sug_names],Conflicts,[NVer|NumVers],Key,Name,Arity,AN,ANames):-!,
	Ver = (Completes,Simp),
	NVer= (Completes,NewNum),
	new_predicate(Name,Arity,NewNum),
	record_simplif(Simp,NewNum),
	assign(Vers,Sug_names,Conflicts,NumVers,Key,Name,Arity,[NewNum|AN],ANames).
assign([Ver|Vers],[LN|Sug_names],Conflicts,[NVer|NumVers],Key,Name,Arity,AN,ANames):-
	member(NN,LN),
	\+ memberchk(NN,AN),
	\+ memberchk(NN,Conflicts),
	Ver = (Completes,Simp),
	NVer = (Completes,NN),
	record_simplif(Simp,NN),
	assign(Vers,Sug_names,Conflicts,NumVers,Key,Name,Arity,[NN|AN],ANames).
assign([Ver|Vers],[_|Sug_names],Conflicts,[NVer|NumVers],Key,Name,Arity,AN,ANames):-
	Ver = (Completes,Simp),
	NVer= (Completes,NewNum),
	new_predicate(Name,Arity,NewNum),
	record_simplif(Simp,NewNum),
	assign(Vers,Sug_names,Conflicts,NumVers,Key,Name,Arity,[NewNum|AN],ANames).


:- pred	check_assignments(NumVers,Sug_names,Arity)
	# "Basically, if specialized versions of exported predicates are 
           generated, here we inform ciaopp about it so that the output file
           export such new predicates.".

check_assignments([],[],_).
check_assignments([_|Vers],[[]|SNames],Arity):-!,
	check_assignments(Vers,SNames,Arity).
check_assignments([(_,Name)|Vers],[LN|SNames],Arity):-
	subtract(LN,[Name],Missing),
	warnings(Missing,Name,Arity),
	check_assignments(Vers,SNames,Arity).

name_conflicts([SN|_],L,Name):-
	member(Name,L),
	memberchk(Name,SN).
name_conflicts([SN|SNames],L,Name):-
	append(SN,L,L1),
	name_conflicts(SNames,L1,Name).


:- pred conflicts(List)
	# "Issues warnings when several entries with the same suggested 
	  name give place to different versions and thus the suggested name 
	  cannot be used for all such versions". 
conflicts([]):-!.
conflicts([_Entry|_Entries]). %:-
%	compiler_error(conflict(_Entry)).

:- data equalities/2.

:- data publish_pred_name/2.

:- doc(publish_pred_name(Pred,Arity), "A fact for this predicate
   is asserted for exported predicates for which several
   implementations are available."). 

warnings([],_,_):-!.
warnings(L,Name,Arity):-
%	compiler_error(versions(L,Name)),
	assert_itf(new_exports,_,Name,Arity,_),
%	build_clauses(L,Name,Arity,Cs,Ds),
%	asserta_fact(equalities(Cs,Ds)),
	L = [Pred|_],
	asserta_fact(publish_pred_name(Pred,Arity)).

%% build_clauses([],_,_,[],[]).
%% build_clauses([N|NN],Name,Arity,[C|Cs],[D|Ds]):-
%% 	functor(Head,N,Arity),
%% 	functor(Body,Name,Arity),
%% 	copy_args(Arity,Head,Body),
%% %  PBC: create_dict/2
%% % 	varset(Head,Vars),
%% % 	copy_term(Vars,Copy),
%% % 	numbervars(Copy,0,_),
%% % 	build_dict(Copy,Names),
%% 
%% 	create_dict(Head,D),
%% 	make_atom([N,Arity,1],Clid),
%% 	C = clause(Head,[Body:noinfo]):Clid,
%% 	build_clauses(NN,Name,Arity,Cs,Ds).

:- pred decide_remove_original_exported_predicate(Sug_names,ANames,Name,Arity)
	# "We remove the original exported predicate when it is no longer 
           needed. This only happens if the original name is suggested to 
           more than one version. Additionally, this is not needed if any 
           of the versions get the name of the original predicate. In other 
           case, we remove it.".

decide_remove_original_exported_predicate(Sug_names,_ANames,_Name,_Arity):-
	no_names(Sug_names),!.
decide_remove_original_exported_predicate(_,ANames,Name,_Arity):-
	member(Name,ANames),
	!.
decide_remove_original_exported_predicate(_,_,Name,Arity):-
	retract_itf(exports,_,Name,Arity,_).

no_names([]).
no_names([[]|T]):-
	no_names(T).

%% :- pred empty_simplifications(+Versions) #"There is at list one
%% version in @var{Versions} with empty as the set of simplifications".
%% 
%% empty_simplifications([(_,[])|_]).
%% empty_simplifications([_|Versions]):-
%%         empty_simplifications(Versions).
%% 
%% member_list(X,[L|_]):-
%% 	memberchk(X,L),!.
%% member_list(X,[_|Ls]):-
%% 	member_list(X,Ls).

:-pred replacements(+Keys,+Preds) #"We record which version must be
called in each goal for each predicate. If the called version keeps
the original name of the predicate then nothing need be done with that
version".

replacements([],[]).
replacements([Key|Keys],[Name/_|Preds]):-
        current_fact(versions(Key,Versions)),
        decide_replace_version(Versions,Name),
        replacements(Keys,Preds).

:- pred decide_replace_version(+Versions,+Name) #
  "If there is only one version for the predicate and it keeps
   the original name there is no need to do any replacements
   for that predicate.".

decide_replace_version([(_,Name)],Name):-!.
decide_replace_version(Versions,Name):-
	replace_version(Versions,Name).

replace_version([],_).
 %% GP commented temporarily to detect clashes in spec with delay
 %% replace_version([(_,Name)|Completes],Name):-!,
 %% 	replace_version(Completes,Name).
replace_version([(Parents,NewName)|Completes],Name):-
        replace_complete(Parents,NewName),
        replace_version(Completes,Name).

replace_complete([],_).
replace_complete([(Father,_)|More],Name):-
        replace(Father,Name),
        replace_complete(More,Name).

replace([],_).
replace([(GoalKey,Num)|Parents],Name):-
	decode_litkey(GoalKey,N,A,_,_),!,
        get_predkey(N,A,Pred),
        (search_version(Num,Pred,Version) ->
	    record_latest_replacement(GoalKey,Version,Name)
	;
	    compiler_error(no_complete((GoalKey,Num)))),
        replace(Parents,Name).
replace([(_query,_)|More],Name):-
	replace(More,Name).

:- pred search_version(+Num,+Pred,-Version) #"The @var{Num} occurrence
of @var{Pred} is included in @var{Version}. In other words, the
@var{Num} th complete for @var{Pred} belongs to @var{Version}".

search_version(Num,Pred,Version):-
        current_fact(versions(Pred,Vers)),
        search(Vers,Num,Version).
search([(Complete,Version)|_],Num,Version):-
        number_complete(Complete,Num),
        !.
search([_|More],Num,Version):-
        search(More,Num,Version).

number_complete([(_,Num)|_],Num):-!.
number_complete([_|More],Num):-
        number_complete(More,Num).

:- data simplif/3.


:- pred record_simplif(+Simplif,+Version) #"Records all the
simplifications for @var{Version}".

record_simplif([],_).
record_simplif([(K,Sense)|Simps],Version):-
        asserta_fact(simplif(K,Version,Sense)),
        record_simplif(Simps,Version).

% the subtract in basics.pl cannot be used the way I want it
my_subtract([], _, []) :- !.
my_subtract([C|D], A, B) :-
        member(C, A), !,
        my_subtract(D, A, B), !.
my_subtract([B|C], A, [B|D]) :-
        my_subtract(C, A, D), !.

:- pred new_preds(+Preds,-New_Preds) #"During the specialization
process, new predicates may be generated and other ones may be
eliminated. @var{New_Preds} is the list of predicates in the new
program".

new_preds([],[]).
new_preds([(N/A)|Preds],New_preds):-
        get_predkey(N,A,Key),
	current_fact(versions(Key,V)),
	second_components(V,Versions),
        process(Versions,(N/A),New_preds,More_preds),
	new_preds(Preds,More_preds).
process([],Pred,[Pred|Tail],Tail):-!.
process(Preds,(N/A),NewPreds,Tail):-
        proc_vers(Preds,N,A,NewPreds,Tail).
proc_vers([],_,_,T,T).
proc_vers([P|Preds],N,A,[(P/A)|More_Preds],Tail):-
        proc_vers(Preds,N,A,More_Preds,Tail).

second_components([],[]).
second_components([(_,X2)|More],[X2|Others]):-
	second_components(More,Others).

first_components([],[]).
first_components([(X1,_X2)|More],[X1|Others]):-
	first_components(More,Others).

:- pred all_versions(+Program,+Dicts,+Abs,-Sp_program,-Sp_Dicts)
#"@var{Sp_program} is the specialized program generated by the
analyzer, without simplificating or collapsing versions. It is only
used when we ask for versions in specialization options".
all_versions(Program,Dicts,Abs,Sp_program,Sp_Dicts):-
	pp_statistics(runtime,_),
	erase_all_local_data,
	retractall_fact(versions(_,_)),
	list_format(Program,Prog),
	predicate_names(Preds),
	get_predkeys(Preds,Keys),
	prepare_ai_info(Keys,Abs),
	original_versions(Keys,Abs),
	enumerate_versions(Keys,Preds),
	replacements(Keys,Preds), !, % leaves choice_points
	write_pred_versions(Prog,Dicts,Abs,Sp_Prog,Sp_Dicts),!, % leaves choice_points
	newformat(Sp_Prog,Sp_program),
	erase_all_local_data,
	pp_statistics(runtime,[_,T]),
	message(inform, ['{transformed by vers in ', ~~(T),' msec.}']).

:- pred get_version_name(+AbsInt,+Sg,+Call,-Name) 
# "Given a predicate call @var{Sg} and a call pattern @var{Call} in
  the abstract domain @var{AbsInt}, returns @var{VersionName}, the
  name of the specialized version in which best fits that call and
  call pattern. Note that @var{CallComplete} has to be sorted.".
get_version_name(AbsInt,SgComplete,CallComplete,NewSpecName):-
	functor(SgComplete, F, A),
	get_predkey(F, A, Key),
	versions(Key,Versions),
	(Versions == [_] ->
	    NewSpecName = F
	;
	    current_fact(complete(Key,AbsInt,Sg,Proj,_,Id,_)),
	    identical_proj(AbsInt,SgComplete,CallComplete,Sg,Proj),
	    search_version(Id,Key,NewSpecName)
	).
