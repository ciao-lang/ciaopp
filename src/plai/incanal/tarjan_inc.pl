:- module(tarjan_inc,
	[ inc_add_source_clauses/3,
	  rearrange_tarjan_after_deletion/1
	], [assertions, datafacts]).

:- doc(title, "Incremental computation of tarjan algorithm").

:- doc(author, "Isabel Garcia-Contreras (ported from ciaopp-0.8)").

:- use_module(library(lists), [member/2, append/3, select/3, union/3, difference/3]).
:- use_module(library(sets), [merge/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(sort)).
:- use_module(library(idlists), [subtract/3]).

:- use_module(ciaopp(plai/tarjan), [
	step2/2, tarjan/2, recursive_classify/4,
	user_clauses/5, program_pred/4, init_cls/2, get_vertex/3,
	get_recursivity_class/3, init_depends/3, recursive_classes/1]).

:- use_module(ciaopp(plai/transform),
	[trans_clause/3, update_trans_clause_rflag/3, update_trans_clause/6,
	 trans_clause_/6]).
:- use_module(ciaopp(p_unit/program_keys),
	[decode_predkey/3, decode_clkey/4, decode_litkey/5, get_predkeys/2,
	 get_predkey/3]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(ciaopp(plai), [transform_clauses_/5]).

:- use_module(ciaopp(p_unit/clause_db), [source_clause/3]).

:- use_module(ciaopp(analysis_stats)).

:- doc(bug, "meta calls are not tested.").

% TODO: unify body processing with tarjan

:- doc(module, "This module contains predicates for computing
incrementally the strongly connected components of programs using the
tarjan algorithm.").

% from incanal_deletion
:- export(tarjan_data/1).
:- doc(tarjan_data/1, "Computed recursive classes of the tarjan algorithm.").
:- data tarjan_data/1.
:- export(predicates/1).
:- doc(predicates(Ps), "@var{Ps} is a list of the predicates of the program.").
:- data predicates/1.
:- export(rec/1).
:- doc(rec(P/A), "Succeeds if @var{P/A} is a recursive predicate of the program.").
:- data rec/1.

% from tarjan
:- export(vertexes/1).
:- doc(vertexes/1, "The vertexes of the graph for performing the tarjan algorithm.").
:- data vertexes/1.

% ----------------------------------------------------------------------
:- doc(section, "Program call graph managing predicates").

:- pred inc_add_source_clauses(Cls, Ds, AbsInt) : list * list * atm
	#"Adds incrementally clauses of list @var{Cls} with their
         respective dictionaries in @var{Ds} for abstract domain
         @var{AbsInt} to the source code database, and updates the
         recursivity of the clauses that may have changed .".
inc_add_source_clauses([], _, _) :- !.
inc_add_source_clauses(Cls, Ds, AbsInt) :-
	inc_preprocess(AbsInt, Cls, Ds).

:- pred inc_preprocess(+AbsInt, +NCls, +Ds) #"Adds clauses
	to the ciaopp transformed code database.

        First program recursive classes are recalculated and previous
        clauses updated, then new clauses are added to the database".
inc_preprocess(AbsInt, NCls, Ds) :-
	update_program_rec(NCls,Rs,RC),
	rec_preds(Ps),
	transform_clauses_(NCls,Ds,Rs,Ps,AbsInt), % Ps recursive predicates
	findall(Clid, source_clause(Clid, clause(_, _), _), Clids),
	stat(upd_clauses, update_clauses_opt(Clids, RC)).
            % IG update clauses from nr to r

:- pred update_program_rec(Cls, Rs, RC)
	#"Updates program data about recursion with new clauses in @var{Cls}.".
update_program_rec(NewCls, Rs, RC) :-
	recalculate_sccs(NewCls, _PrevPs, Calls, RC),
	recursive_classify(NewCls, (Calls, RC), Rs, NRPs), % missing new RPs?
	add_rec_preds(NRPs).

add_rec_preds([]).
add_rec_preds([P|Ps]) :-
	add_rec_pred(P),
	add_rec_preds(Ps).

 % from incanal_driver % TODO: remove duplicates
:- export(rec_preds/1).
:- pred rec_preds(Ps) => list #"@var{Ps} is the list of recursive
	predicates of the loaded program.".
rec_preds(Ps) :-
	findall(P, rec(P), Ps_u),
	sort(Ps_u, Ps).

add_rec_pred(P) :- % TODO: This check is linear!!!, see if it is really necessary
	rec(P), !.
add_rec_pred(P) :-
	assertz_fact(rec(P)).

% This is supposed to be the incremental version for adding clauses of
% strong_connected_components in tarjan.pl
% recalculate_sccs(+,-,-,-)
recalculate_sccs(NewCls, Predicates, Calls, RC) :-
 	previous_predicates(Predicates), % IG this is done inside
	program_pred(NewCls,Calls,[],PPreds), % PPreds is a list of the program heads
	union(PPreds, Predicates, New_Preds),
 	set_fact(predicates(New_Preds)), % IG set_fact of list?
	% Empties is a list of empty lists
	init_cls(PPreds,Empties),
	% Collect all the user predicates called by each predicate (edges)
	user_clauses(NewCls,Calls,PPreds,Empties,Edges),
 	previous_vertex(NVs),
	merge_vertex(PPreds,Edges,NVs,Vertexes,Flag),
 	(var(Flag) -> % IG: this means that there were no changes
 	    current_fact(tarjan_data(RC))
 	;
	    sort(Vertexes, Vs),
	    Vs = [V1|_],
 	    S0 = state(Vs,V1,[],0),
 	    step2(S0,RC), % IG RC are the predicates in the same SCC of the origina predicate?
	    set_fact(tarjan_data(RC)),
	    set_fact(recursive_classes(RC)), % update data in tarjan
					     % for later determine_r_flag
	    set_fact(vertexes(Vs))
 	).

previous_vertex(NVs):-
	current_fact(vertexes(Vs)),!,
	NVs = Vs.
previous_vertex([]).

previous_predicates(Ps):-
	current_fact(predicates(Ps)),!.
previous_predicates([]).

:- pred update_clauses_opt(Clauses, RC) : list(Clauses)
      #"@var{Clauses} we had stored previously may have changed due to
      diferent recursivity of the clause or of any of the literals in
      its body. As this predicate is used when new clauses are added,
      the only possible change is from nr to r, but not vice-versa.".
% Includes reordering
update_clauses_opt([], _).
update_clauses_opt([ClKey|ClKeys], RC) :-
	decode_clkey(ClKey,F,Ar,_),
	get_predkey(F, Ar, PKey),
	retract_fact(trans_clause_(PKey,RFlag,Head,Vs,ClKey,Body)), !,
	get_recursivity_class(F/Ar,RC,Class),
	update_clause_body(Body,NBody,NRFlag1,Class),
	( RFlag = r ->
	    NRFlag = r % cannot change to nr
	;
	    ( var(NRFlag1) -> NRFlag = nr ; NRFlag = r )
	),
	assertz_fact(trans_clause_(PKey,NRFlag,Head,Vs,ClKey,NBody)),
	% always assert to keep order
	update_clauses_opt(ClKeys, RC).

%----------------------------------------------------------------------
:- pred update_clause_body(+Body,-NBody,-NClRec,+Class)
    #"We go over all the literals in Body to see if the recursivity of
any of them has changed.".
update_clause_body(true,true,_,_). % IG Is this case possible?
% the information of recursivity cannot have changed for builtins as
% they are always non-recursive (so no flag is needed for them)
update_clause_body(B,NewBody,NClRec,Class):-
	B = g(Id,Vars,Info,SgKey,Goal),
	!,
	NewBody = g(Id,Vars,NInfo,SgKey,NGoal),
	update_clause_goal(Goal,NGoal, Info,NInfo,NClRec,Class).
update_clause_body(Body,NBody,NClRec,Class):-
	Body = (Goal,Goals),
	NBody = (NGoal,NGoals),
	update_clause_body(Goal,NGoal,NClRec,Class),
	update_clause_body(Goals,NGoals,NClRec,Class).

update_clause_goal(G, G, r, r, ClRec, Class) :- !,
	functor(G, F, A),
	( member(F/A, Class) -> ClRec = r ; true).
update_clause_goal(G, G, nr, LitInfo, ClRec, Class) :- !, % check sccs
	functor(G, F, A),
	( member(F/A, Class) ->
	    ClRec = r,
	    LitInfo = r
	;
	    ( rec(F/A) -> % linear check
	        LitInfo = r
	    ;
		LitInfo = nr
	    )
	).
% LitInfo is not about recursivity
update_clause_goal('$meta'(Blt,Call,_A),NG,LitInfo,LitInfo,ClRec,Class) :-
	!,
 	NG = '$meta'(Blt, NCall, _A),
 	update_clause_goal_meta_call(Call, NCall, ClRec, Class).
update_clause_goal(G, G, LitInfo, LitInfo, _, _).  % not recursivity info

% TODO: Check that this is updated
% $:(foo:p(a))  % This is the goal case
update_clause_goal_meta_call(Goal,NGoal,ClRec,Class) :-
	functor(Goal,N,1),!,
	functor(NGoal,N,1),
	arg(1,Goal,G),
	arg(1,NGoal,NG),
	update_clause_body(G,NG, ClRec,Class).
% $:(PA(p,(X), foo:p(X))) % case for pred(N) expansion
update_clause_goal_meta_call(Goal,NGoal,ClRec,Class):-
	functor(Goal,N,3),
	functor(NGoal,N,3),
	arg(1,Goal,V),
	arg(1,NGoal,V),
	arg(3,Goal,L),
	arg(3,NGoal,L),
	arg(2,Goal,G),  % IG: Is this wrong?, is it the 3rd argument?
	arg(2,NGoal,NG),
	update_clause_body(G,NG,ClRec,Class).

merge_vertex([],[],Vs,Vs,_).
merge_vertex([N/A|Preds],[Ed|Edges],Vs,Result,Flag):-
	get_vertex(N/A,Vs,Vertex),!,
	Vertex = vertex(N/A,OldEd,0,0,undef),
	merge(Ed,OldEd,NewEd),
	(NewEd \== OldEd ->
	    select(vertex(N/A,OldEd,0,0,undef),Vs,TmpVs),!,
	    TmpResult = [vertex(N/A,NewEd,0,0,undef)|TmpVs],
	    Flag = yes
	;
	    TmpResult = Vs),
	merge_vertex(Preds,Edges,TmpResult,Result,Flag).
merge_vertex([N/A|Preds],[Ed|Edges],Vs,Result,yes):-
	TmpResult = [vertex(N/A,Ed,0,0,undef)|Vs],
	merge_vertex(Preds,Edges,TmpResult,Result,yes).

% ----------------------------------------------------------------------
% From incanal deletion
% -------------------------------------------------------------------------
:- doc(section, "Code recursivity predicates").
% IG: For computing this information, no analyzer is needed nor abstract operations!!

:- pred rearrange_tarjan_after_deletion(+Preds)
	# "@var{Preds} is the list of predicates for which clauses have been
          deleted. This predicate updates the SCCs after deleting a set of
clauses.".
rearrange_tarjan_after_deletion(Preds):-
	split_in_still_clauses_or_not(Preds,Removed,Remaining,Calls),
	retract_fact(tarjan_data(RC)),
	init_cls(RC,Empty),
	group_in_classes4(Removed,RC,Empty,NSub_Remove),
	group_in_classes7(Remaining,Calls,RC,Empty,NSub_Remain,Empty,Calls_Cla),
	retract_fact(vertexes(Vs)),
	top_down_del_tarjan_ls(NSub_Remove,NSub_Remain,Calls_Cla,RC,Vs),!,
	update_pred_recs,
	update_rec_all_literals. % TODO: review this

update_pred_recs :- % this is for keeping track of the
	( % failure-driven loop
	  rec(Key),
	    Key = F/A,
	    get_predkey(F, A, SgKey),
	    ( trans_clause(SgKey, r, _) -> true
	    ;
		retract_fact(rec(Key))
	    ),
	    fail
	; true).

%--------------------------------------------------------------------
% We group all the predicates corresponding to the same SCC previously.
% This way we only execute only once tarjan algorithm for each class
group_in_classes7([],[],_,Subclasses,Subclasses,SubCalls,SubCalls).
group_in_classes7([Pred|Preds],[C|Cs],Classes,Subclasses,NSubclass,Calls,NCalls):-
	find_class8(Pred,C,Classes,TmpClasses,Subclasses,TmpSubclasses,Calls,TmpCalls),
	group_in_classes7(Preds,Cs,TmpClasses,TmpSubclasses,NSubclass,TmpCalls,NCalls).

find_class8(Pred,Call,[C|Cs],TmpClasses,Subcl,TmpSubclasses,SubCalls,TmpCalls):-
	select(Pred,C,NC),!,
	Subcl = [Sc|Scs],
	SubCalls = [SCall|SCalls],
	TmpClasses = [NC|Cs],
	TmpSubclasses = [[Pred|Sc]|Scs],
	TmpCalls = [[Call|SCall]|SCalls].
find_class8(Pred,Call,[C|Cs],[C|NCs],[Sc|Scs],[Sc|NScs],[CC|CCs],[CC|NCCs]):-
	find_class8(Pred,Call,Cs,NCs,Scs,NScs,CCs,NCCs).

%--------------------------------------------------------------------
% We group all the predicates corresponding to the same SCC previously.
% This way we only execute only once tarjan algorithm for each class
group_in_classes4([],_,Subclasses,Subclasses).
group_in_classes4([Pred|Preds],Classes,Subclasses,NSubclasses):-
	find_class5(Pred,Classes,TmpClasses,Subclasses,TmpSubclasses),
	group_in_classes4(Preds,TmpClasses,TmpSubclasses,NSubclasses).

find_class5(Pred,[C|Cs],TmpClasses,[Sc|Scs],TmpSubclasses):-
	select(Pred,C,NC),!,
	TmpClasses = [NC|Cs],
	TmpSubclasses = [[Pred|Sc]|Scs].
find_class5(Pred,[C|Cs],[C|NCs],[Sc|Scs],[Sc|NScs]):-
	find_class5(Pred,Cs,NCs,Scs,NScs).

%-----------------------------------------------------------------------
% If we have to delete several clauses that belonged to the same SCC
% we erase them all at once
top_down_del_tarjan_ls([],[],[],RC,Vs):-
	asserta_fact(tarjan_data(RC)),
	set_fact(recursive_classes(RC)),
	asserta_fact(vertexes(Vs)).
top_down_del_tarjan_ls([[]|Sub_Remove],[[]|S_Rn],[[]|Cs],RC,Vs):-!,
	top_down_del_tarjan_ls(Sub_Remove,S_Rn,Cs,RC,Vs).
top_down_del_tarjan_ls([Sub_Remove|MoreRv],[S_Rn|MoreRn],Cs,RC,Vs):-
	Sub_Remove = [N/A|_],!,
	get_recursivity_class(N/A,RC,Class),
	subtract(Class,Sub_Remove,NClass),
	select(Class,RC,TmpRC),!,
	remove_list_vertex(Sub_Remove,Vs,NVs),
	top_down_change_tarjan(MoreRv,[S_Rn|MoreRn],Cs,TmpRC,NVs,NClass,Class).
top_down_del_tarjan_ls([[]|MoreRv],[S_Rn|MoreRn],Cs,RC,Vs):-
	S_Rn = [N/A|_],
	get_recursivity_class(N/A,RC,Class),
	select(Class,RC,TmpRC),!,
	top_down_change_tarjan(MoreRv,[S_Rn|MoreRn],Cs,TmpRC,Vs,Class,Class).

top_down_change_tarjan(MoreRv,[[]|MoreRn],[_|Cs],TmpRC,Vs,NClass,Class):-
	get_predkeys(Class,ClassKeys),
	%get_prev_recursivity(ClassKeys,Oldrec), % IG this already deletes
	%delete_recursivity(ClassKeys),
	delete_tarjan_case(NClass,Vs,NRC),
	append(NRC,TmpRC,NewRC),
	post_process_old_clauses(ClassKeys,Class,NRC),
	%update_recursivity_of_literals(Oldrec,ClassKeys),
	update_rec_all_literals,
	top_down_del_tarjan_ls(MoreRv,MoreRn,Cs,NewRC,Vs).

top_down_change_tarjan(MoreRv,[S_Rn|MoreRn],[C|Cs],TmpRC,Vs,NClass,Class):-
	remove_list_vertex(S_Rn,Vs,NVs1),
	init_depends(S_Rn,Changed_Vs,C),
	append(Changed_Vs,NVs1,NVs),
	get_predkeys(Class,ClassKeys),
	%get_prev_recursivity(ClassKeys,Oldrec),
	%delete_recursivity(ClassKeys),
	delete_tarjan_case(NClass,NVs,NRC),
	append(NRC,TmpRC,NewRC),  % HERE
	post_process_old_clauses(ClassKeys,Class,NRC),
	%update_recursivity_of_literals(Oldrec,ClassKeys),
	update_rec_all_literals,
	top_down_del_tarjan_ls(MoreRv,MoreRn,Cs,NewRC,NVs).

remove_list_vertex([],L,L).
remove_list_vertex([X|Xs],L,NewL):-
	select(vertex(X,_,_,_,_),L,Tmp),!,
	remove_list_vertex(Xs,Tmp,NewL).

%----------------------------------------------------------------------
% Before erasing the recursiveness information we collect it to compare
% it with the obtained after the deletion of a predicate
get_prev_recursivity([],[]).
get_prev_recursivity([Key|Keys], Rec):-
	retract_fact(rec(Key)), !,
	Rec = [r|MoreRec],
	get_prev_recursivity(Keys, MoreRec).
get_prev_recursivity([_|Keys],[nr|Rec]):-
	get_prev_recursivity(Keys,Rec).

delete_recursivity([]).
delete_recursivity([Key|_]):-
	retract_fact(rec(Key)),
	fail.
delete_recursivity([_|Keys]):-
	delete_recursivity(Keys).

split_in_still_clauses_or_not([],[],[],[]).
split_in_still_clauses_or_not([N/A|Preds], Removed, Remaining, Calls):-
	get_predkey(N, A, Key),
	findall(Body, trans_clause_(Key, _, _, _, _, Body), List),
	List \== [], !,
	Remaining = [N/A|NewRemaining],
	get_calls_in_recorded_bodies(List, C),
	sort(C, C_s),
	Calls = [C_s|NewCalls],
	split_in_still_clauses_or_not(Preds,Removed,NewRemaining,NewCalls).
split_in_still_clauses_or_not([N/A|Preds],[N/A|NewRemoved],Remaining,Calls):-
	split_in_still_clauses_or_not(Preds,NewRemoved,Remaining,Calls).
 
get_calls_in_recorded_bodies([],[]).
get_calls_in_recorded_bodies([Body|Bodies],Calls):-
	get_calls_in_one_body(Body,C),
	append(C,MoreCalls,Calls),
	get_calls_in_recorded_bodies(Bodies,MoreCalls).

get_calls_in_one_body(true, []) :- !.
get_calls_in_one_body(G, Calls) :-
	G = g(_Id, _Vars, _Info, _SgKey, Goal), !,
	get_calls_in_recorded_goal(Goal, Calls).
get_calls_in_one_body((G, Goals), Calls):- !,
	G = g(_Id, _Vars, _Info, _SgKey, Goal),
	get_calls_in_recorded_goal(Goal, Call),
	append(Call, MoreCalls, Calls),
	get_calls_in_one_body(Goals, MoreCalls).

get_calls_in_recorded_goal((!),[]) :- !.  % IG new
get_calls_in_recorded_goal('basiccontrol:fail',[]) :- !.  % IG new
get_calls_in_recorded_goal('$var',[]) :- !.  % IG added new clause
get_calls_in_recorded_goal('$built'(_Blt,_Call, _),[]) :- !. % IG modified shape
get_calls_in_recorded_goal('$meta'(_Blt,Goal, _),Call) :- !, % IG modified shape
	get_calls_in_recorded_goal_meta_call(Goal, Call).
get_calls_in_recorded_goal(G, [P/A]) :-  % IG HERE CHECK THE SHAPE
	functor(G, P, A), !.
get_calls_in_recorded_goal(_, []).

get_calls_in_recorded_goal_meta_call(Goal,Call):-
	functor(Goal,_N,1),!,
	arg(1,Goal,G),
	get_calls_in_recorded_goal(G,Call).
get_calls_in_recorded_goal_meta_call(Goal,Call):-
	functor(Goal,_N,3),
	arg(2,Goal,G),
	get_calls_in_recorded_goal(G,Call).

:- pred delete_tarjan_case(+NClass, +NVs, -NRC) #"
	@var{NClass} is the SCC of the removed predicate. @var{NVs} is
	the list of vertexes and @var{NRC} is the new SCC's. We must
	execute tarjan algorithm inside the SCC as some predicates
	that were recursive may not be anymore. However if the SCC
	contained one (first clause) or two elements (Second clause)
	then nothing need be done.".
delete_tarjan_case([],_,[]):-!.
delete_tarjan_case([N/A],_,[[N/A]]):-!.
delete_tarjan_case(NClass,NVs,NRC):-
	get_vertex_list(NClass,NVs,[V|Vs]),
	S0 = state([V|Vs],V,[],0),
	step2(S0,NRC).

get_vertex_list([],_,[]).
get_vertex_list([N/A|Vs],Vertexs,[V|MoreVs]):-
	get_vertex(N/A,Vertexs,V),
	get_vertex_list(Vs,Vertexs,MoreVs).

%----------------------------------------------------------------------
% we study if the recursive clauses for the predicates in the SCC of 
% the deleted predicate are still recursive
post_process_old_clauses([], [], _).
post_process_old_clauses([Key|Keys], [N/A|Preds], RecClass):-
	findall((K, B), trans_clause_(Key, r, _H, _V, K, B), Clauses),
	get_recursivity_class(N/A,RecClass,Class),
	post_process_rec_clause(Clauses,Class,Key),
	post_process_old_clauses(Keys,Preds,RecClass).

%----------------------------------------------------------------------
% if the clause is still recursive, nothing must be done, otherwise we 
% erase the clause and record the new version
post_process_rec_clause([],_,_).
post_process_rec_clause([(_,Body)|Clauses],Class,Key):-
	post_process_rec_body(Body,Class),!, % HERE
	post_process_rec_clause(Clauses,Class,Key).
post_process_rec_clause([(Clid,Body)|Clauses],Class,Key):-
	retract_fact(trans_clause_(Key, r, Head, Vars, Clid, Body)),
	asserta_fact(trans_clause_(Key, nr, Head, Vars, Clid, Body)),
	post_process_rec_clause(Clauses,Class,Key).
%----------------------------------------------------------------------
% succeeds only if the body of the clause is recursive
post_process_rec_body(Body,Class) :-
	Body = g(_, _, _, _, '$meta'(_, Goal, _)),
	functor(Goal,_,1), !,
	arg(1,Goal,NewGoal),
	post_process_rec_body(NewGoal, Class).
post_process_rec_body(Body, Class) :-
	Body = g(_, _, _, _,'$meta'(_, Goal, _)),
	functor(Goal,_,3), !,
	arg(2,Goal,NewGoal),
	post_process_rec_body(NewGoal,Class).
post_process_rec_body(Body, Class) :-
	Body = g(_, _, _, _GKey, Goal),
	\+ Goal = '$built'(_, Goal, _),
	functor(Goal, N, A),
	member(N/A, Class), !,
	add_rec_pred(N/A).
post_process_rec_body((Goal,_),Class) :-
	post_process_rec_body(Goal,Class), !.
post_process_rec_body((_,Goals),Class) :-
	post_process_rec_body(Goals,Class).

%----------------------------------------------------------------------
% The information about the recursivity of predicates may have changed.
% if a predicate was nr then it is still nr and nothing must be done
% if the predicate was recursive but it is not anymore then we must 
% update the recorded clauses that call the predicate
update_recursivity_of_literals([],[]).
update_recursivity_of_literals([nr|Recs],[_|Keys]):-
	update_recursivity_of_literals(Recs,Keys).
update_recursivity_of_literals([r|Recs],[Key|Keys]):-
	rec(Key), !,
	update_recursivity_of_literals(Recs,Keys).
update_recursivity_of_literals([_|Recs],[_Key|Keys]):-
	findall(Parents, complete(_, _, _, _, _, _, Parents), All_parents),
	% TODO: IG get them from arcs
	find_literals_from_parents(All_parents,Literals),
	update_rec_literals(Literals),
	update_recursivity_of_literals(Recs,Keys).

:- pred find_literals_from_parents(Ps,Lits) #"Transforms a list of lists of 
	parents @var{Ps} into a list of literals @var{Lits}.".
find_literals_from_parents([],[]).
find_literals_from_parents([P|Ps],Literals):-
	eliminate_comp_numbers(P,Lit),
	sort(Lit,S_Lit),
	find_literals_from_parents(Ps,MoreLit),
	merge(S_Lit,MoreLit,Literals).

eliminate_comp_numbers([],[]).
eliminate_comp_numbers([(Lit,_)|Parents],[Lit|Lits]):-
	eliminate_comp_numbers(Parents,Lits).

%----------------------------------------------------------------------
% Literals is a list of literals whose information of recursivity must
% be changed from r to nr
update_rec_literals([]).
update_rec_literals([Lit|Lits]):-
	decode_litkey(Lit, P, A, C, _),
	get_predkey(P, A, Key),
	make_atom([P, A, C], Clid),
	current_fact(trans_clause_(Key, R, H, V, Clid, Body), Ref), !,
	update_rec_body(Body, NBody),
	erase(Ref),
	asserta_fact(trans_clause_(Key, R, H, V, Clid, NBody)),
	update_rec_literals(Lits).
update_rec_literals([_|Lits]):- % it is a clause of the deleted predicate
	update_rec_literals(Lits).

%----------------------------------------------------------------------
% Added by IG
update_rec_all_literals :-
	( % failure-driven loop
	  current_fact(trans_clause_(Key, R, H, V, Clid, Body), Ref),
	    update_rec_body(Body, NBody), %\+ Body = NBody,
	    % TODO: IG assert and retract allways to keep the correct
	    % order of clauses
	    erase(Ref),
	    asserta_fact(trans_clause_(Key, R, H, V, Clid, NBody)),
	    fail
	 ; true).

%----------------------------------------------------------------------
% We search in the body of the clause the literal whose recursivity has
% changed and update it
update_rec_body(Body, NBody):-
	Body = g(Id,Vars,PrevInfo,SgKey,Goal), !,
	NBody = g(Id,Vars,NInfo,SgKey,NGoal),
	update_rec_goal(Goal,PrevInfo, NInfo, NGoal).
update_rec_body(Body, Body) :-  % IG This case will never happen, remove prev cut?
	Body = g(_Id,_Vars,_Info,_SgKey,_Goal), !.
update_rec_body((Goal, Goals), (NGoal, NGoals)) :-
	update_rec_body(Goal, NGoal),
	update_rec_body(Goals, NGoals).

update_rec_goal('$meta'(Blt,Goal, _A), PrevInfo, Info, NewGoal) :- % TODO: fix this
	functor(Goal,N,1), !,
	NewGoal = '$meta'(Blt, NGoal, _A),
	functor(NGoal,N,1),
	arg(1,Goal,Call),
	arg(1,NGoal,NCall),
	update_rec_goal(Call, PrevInfo, Info, NCall).
update_rec_goal('$meta'(Blt, Goal, _A),PrevInfo, Info,NewGoal) :-
	functor(Goal, N, 3), !,
	NewGoal = '$meta'(Blt, NGoal, _A),
	functor(NGoal,N,3),
	arg(1,Goal,V),
	arg(1,NGoal,V),
	arg(3,Goal,L),
	arg(3,NGoal,L),
	arg(2,Goal,Call),
	arg(2,NGoal,NCall),
	update_rec_goal(Call, PrevInfo, Info, NCall).
update_rec_goal(G, PrevInfo, NInfo, G) :-
	( PrevInfo = r ; PrevInfo = nr ), !,
	functor(G, F, A),
	( rec(F/A) ->
	    NInfo = r
	;
	    NInfo = nr
	).
update_rec_goal(G, Info, Info, G).
