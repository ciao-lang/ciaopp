:- module(incanal_deletion,
	[ erase_clauses_for_preds/1,
	  remove_clauses_and_related_info_collect_preds/4,
	  erase_previous_memo_lubs/2,
	  bottom_up_delete_mark_preds/4,
	  bottom_up_delete_mark_one/5,
	  erase_memo_tables_and_parents_one_Id/5
	],
	[assertions, datafacts, isomodes, nativeprops]).

:- doc(title, "Update plai_db after clause deletion (incremental analysis)").

:- doc(author, "Isabel Garcia-Contreras (ported from ciaopp-0.8)").

:- doc(module, "This module contains predicates for removing completes
and related memo_table data from analysis necessary for recomputing
correctly analysis after removing clauses or modifying the answers of
the analysis.").

:- use_module(ciaopp(plai/re_analysis), []).
:- import(re_analysis,  % TODO: fix me
	[erase_previous_memo_tables_and_parents/4,
	 erase_previous_parents_info/5,
	 erase_last_memo_table/3
	]).

:- use_module(ciaopp(plai/tarjan), [get_recursivity_class/3]).

:- use_module(ciaopp(p_unit/program_keys),
	[decode_clkey/4, decode_litkey/5, get_predkey/3, decode_predkey/3]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(ciaopp(plai/domains), [abs_sort/3]).

:- use_module(library(sort)).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(messages)).
:- use_module(library(lists), [member/2, append/3]).

:- use_module(ciaopp(plai/plai_db), [memo_lub/5, complete/7, memo_table/6]).
:- use_module(ciaopp(plai/transform), [cleanup_trans_clauses_pred/1, trans_clause/3, remove_trans_clause/2]).

:- pred erase_clauses_for_preds(+Preds)
	# "We erase from the analysis database all the clauses for the
           predicates in the list @var{Preds}.".
erase_clauses_for_preds([]).
erase_clauses_for_preds([Pred|Preds]):-
	erase_clauses_one_pred(Pred),
	erase_clauses_for_preds(Preds).

erase_clauses_one_pred(Pred):-
	Pred = F/A,
	get_predkey(F,A,NewKey),
	cleanup_trans_clauses_pred(NewKey).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- pred remove_clauses_and_related_info_collect_preds(+Clids, +AbsInt, -Preds,-Keys) #
	"@var{Cls} is a set of clauses which has have been eliminated from 
 the program. Thus, they must be deleted from the database of clauses used 
 by the analyzer. In addition to the clause, we delete all the memo_tables 
 and memo_lubs for the clauses. In @var{Preds} and @var{Keys} we collect the 
 name,arity and keys of predicates for which clauses have been deleted. This 
 will later be used for updating the SCCs.".

remove_clauses_and_related_info_collect_preds([], _, [], []).
remove_clauses_and_related_info_collect_preds([Clid|Clids], AbsInt, [F/A|Preds],[Key|Keys]):-
	!,
	decode_clkey(Clid, F, A, _),
	get_predkey(F,A,Key),
	trans_clause(Key, _, clause(_, _, Clid, Body)),
	remove_trans_clause(Key, Clid),
	%%	delete_recursivity_if_necessary(RFlag,Key),
  make_atom([Clid,1],Key1),
  erase_memo_tables_and_parents(Body, Clid, Key1, AbsInt),
	erase_previous_memo_lubs(Body,Clid),
	remove_clauses_and_related_info_collect_preds(Clids, AbsInt, Preds, Keys).
remove_clauses_and_related_info_collect_preds([_|Clids], AbsInt, Preds, Keys):- % TODO: why?
        remove_clauses_and_related_info_collect_preds(Clids, AbsInt, Preds, Keys).

:- pred erase_previous_memo_lubs(+Body, +Clid) 
	# "This predicate traverses @var{Body} and removes the existing 
           memo_lubs. When @var{Body} is finished, we also remove the 
           memo-lub for the end of the clause using @var{Clid}.".
erase_previous_memo_lubs(true,_):- !.
erase_previous_memo_lubs((Goal,Goals),K):-
	Goal = g(_Id, _Vars, _Info, Key, _),
	retract_fact(memo_lub(Key, _, _, _, _)), !,
	erase_previous_memo_lubs(Goals,K).
erase_previous_memo_lubs(Goal,K):-
	Goal = g(_Id, _Vars, _Info, Key, _),
	retract_fact(memo_lub(Key, _, _, _, _)), !,
	erase_last_memo_lub(K).
erase_previous_memo_lubs(_,_). %nothing had been recorded

erase_last_memo_lub(K):-
	retract_fact(memo_lub(K, _, _, _, _)), !.
erase_last_memo_lub(_). %maybe we have not written it yet

% ----------------------------------------------------------------------
:- pred bottom_up_delete_mark_preds(+Keys,SCCs,+AbsInt,-Completes) + not_fails
	# "@var{Keys} is the list of keys of predicates for which clauses
        have been deleted. The completes for such predicates may no longer
        be accurate enough. Thus we collect them in @var{Completes} and
        erase the corresponding completes from the analysis database.".
bottom_up_delete_mark_preds([],_,_,[]).
bottom_up_delete_mark_preds([Key|Keys], SCCs, AbsInt, Completes):-
  decode_predkey(Key,N,A),
	get_recursivity_class(N/A,SCCs,SCC),
	bottom_up_delete_mark(Key,Complete,SCC,AbsInt),
	append(Complete,MoreCompletes,Completes),
	bottom_up_delete_mark_preds(Keys,SCC,AbsInt,MoreCompletes).

:- pred bottom_up_delete_mark_one(+SgKey, +Id, +SCC, +AbsInt,-Completes) + not_fails.
bottom_up_delete_mark_one(Key, Id, SCC, AbsInt, Completes) :-
	retract_fact(complete(Key, AbsInt, Sg, Call, Answer, Id, Fs)), !,
	% IG: retract also auxiliary completes (Id = no) created from this one
  % IG: not necessary, they are not created (see add_complete_builtin in fixpo_ops.pl)
	% ( % failure-driven loop
  %   current_fact(complete(_BKey,AbsInt,_,_,_,no,Ps), Ref),
  %       member((_,Id), Ps), % TODO: performance!
  %       erase(Ref),
  %       fail
  % ; true ),
	AllCompletes = [comp(Sg, Call, Answer, Id, Fs)],
	bottom_up_mark_list_completes(AllCompletes, Completes, SCC, AbsInt),
	bottom_up_delete_mark_clauses(AllCompletes, Key, AbsInt).
bottom_up_delete_mark_one(_Key, _Id, _SCC, _AbsInt, []).

bottom_up_delete_mark(Key, Completes, SCC, AbsInt):-
	findall(comp(Sg, Proj, LPrime, Id, Fs), % Old comp table in the paper
	        retract_fact(complete(Key, AbsInt, Sg, Proj, LPrime, Id, Fs)),
		AllCompletes),
	bottom_up_mark_list_completes(AllCompletes, Completes, SCC, AbsInt),
	bottom_up_delete_mark_clauses(AllCompletes, Key, AbsInt).

bottom_up_delete_mark_clauses([], _, _).
% bottom_up_delete_mark_clauses([comp(_, _, _, Id, _)|_], Key, AbsInt):- % IG: equivalent?
% 	trans_clause(Key, _, clause(_, _, Clid, Body)),
% 	erase_previous_memo_tables_and_parents(Body,AbsInt,Clid,Id),
% 	erase_previous_memo_lubs(Body,Clid),
%  	fail.
bottom_up_delete_mark_clauses([comp(_, _, _, Id, _)|_], Key, AbsInt):-
 	trans_clause(Key, _, clause(_, _, Clid, Body)),
 	make_atom([Clid,1],Key1),
 	erase_memo_tables_and_parents_one_Id(Body,Clid,Key1,Id, AbsInt),
 	erase_previous_memo_lubs(Body,Clid),
  fail.
bottom_up_delete_mark_clauses([_|Comps], Key, AbsInt):-
	bottom_up_delete_mark_clauses(Comps, Key, AbsInt).

% IG: change name by filter external completes??
:- pred bottom_up_mark_list_completes(+Completes, -ExtCompletes, +SCCs, +AbsInt)
	# "We filter out from @var{Completes} those which are not seen from
           outside the SCC for the corresponding predicate. The result is
           given in @var{ExtCompletes}.".
bottom_up_mark_list_completes([], [], _, _).
bottom_up_mark_list_completes([comp(Sg, Call_u, Answer, Id, Fs)|Comps], Completes,
	                                                       SCC, AbsInt):-
	external_calls(Fs,External,Internal,SCC),
	(External \== [] ->
	    abs_sort(AbsInt,Call_u,Call),
	    Completes = [comp(Sg,Call,Answer,Id,External)|MoreCompletes]
	;
	    Completes = MoreCompletes),
	sort(Internal,Internal_s),
	eliminate_self_recursive(Internal_s,Id,Inter),
	bottom_up_delete_recursively_mark_parents(Inter,Comp,SCC,AbsInt),
	append(Comp,NewComp,MoreCompletes),
	bottom_up_mark_list_completes(Comps,NewComp,SCC,AbsInt).

:- pred bottom_up_delete_recursively_mark_parents(+Inter,-Comp,+SCCs,+AbsInt).
bottom_up_delete_recursively_mark_parents([],[],_,_).
bottom_up_delete_recursively_mark_parents([(Key,Id)|Fs],Comp,SCC,AbsInt):-
	bottom_up_delete_mark_one(Key,Id,SCC,AbsInt,Complete),
	append(Complete,MoreComp,Comp),
 %% 	Complete = [C],
 %% 	!,
 %% 	Comp = [C|MoreComp],
	bottom_up_delete_recursively_mark_parents(Fs,MoreComp,SCC,AbsInt).
 %% bottom_up_delete_recursively_mark_parents([_|Fs],Comp,SCC,AbsInt):-
%% 	bottom_up_delete_recursively_mark_parents(Fs,Comp,SCC,AbsInt).

external_calls([],[],[],_).
external_calls([(Lit,Id)|Fs],External,Internal,SCC):-
	decode_litkey(Lit,N,A,_,_), % IG leaves choicepoint
	get_predkey(N,A,Key),
	member(N/A,SCC),!,
	Internal = [(Key,Id)|More_Internal],
	External = More_External,
	external_calls(Fs,More_External,More_Internal,SCC).
external_calls([(Lit,Id)|Fs],[(Lit,Id)|More_External],Internal,SCC):-
	external_calls(Fs,More_External,Internal,SCC).

eliminate_self_recursive([],_Id,[]).
eliminate_self_recursive([(F,Id1)|Parents],Id,NewParents):-
	(Id = Id1 ->
	    NewParents = MoreParents
	;
	    NewParents = [(F,Id1)|MoreParents]),
	eliminate_self_recursive(Parents,Id,MoreParents).

% IG: this was thought to be used with the old definition of Goal:
%      erase_previous_parents_info(Child, Goal, AbsInt, Key, Id),
:- pred erase_memo_tables_and_parents(+Body, +Clid, +Key1, +AbsInt)
	# "All the memo_tables and parents information for the clause
        @var{Body} with key @var{Clid} are erased (note that
        they may correspond to different completes). @var{Key1} is the key
        of the first literal in @var{Body}".
erase_memo_tables_and_parents((Body,RestBody), Clid, Key1, AbsInt) :-
	Body = g(MKey, _Vars, _Info, SgKey, _Goal),
	current_fact(memo_table(Key1, AbsInt, Id, Child, _, _)), % IG backtracking here
	erase_previous_parents_info(Child, SgKey, AbsInt, MKey, Id),
	erase_previous_memo_tables_and_parents(RestBody, AbsInt, Clid, Id),
	fail.
erase_memo_tables_and_parents(g(MKey,_,_,SgKey,_), Clid, Key1, AbsInt):-
	current_fact(memo_table(Key1, AbsInt, Id, Child, _, _)),
	erase_previous_parents_info(Child, SgKey, AbsInt, MKey, Id),
	erase_last_memo_table(AbsInt, Clid, Id),
	fail.
erase_memo_tables_and_parents(_, _, _, _).

:- pred erase_memo_tables_and_parents_one_Id(+Body, +Clid, +Key1, +Id, +AbsInt)
	# "The memo_tables and parents information for the clause
        @var{Body} with key @var{Clid} which correspond to the
        complete @var{Id} are erased. @var{Key1} is the key of the
        first literal in @var{Body}. The difference with
        erase_memo_tables_and_parents is that it only deletes the
        memo_tables and parents that correspond to one complete (Id)
      instead of to all the completes for the predicate.".
erase_memo_tables_and_parents_one_Id((Body,RestBody),Clid,Key1,Id, AbsInt) :-
	Body = g(MKey, _Vars, _Info, SgKey, _Goal),
	current_fact(memo_table(Key1, AbsInt, Id, Child, _, _)), !,
	erase_previous_parents_info(Child, SgKey, AbsInt, MKey, Id),
	erase_previous_memo_tables_and_parents(RestBody, AbsInt, Clid, Id),
	fail.
erase_memo_tables_and_parents_one_Id(g(MKey,_,_,SgKey,_),Clid, Key1, Id,AbsInt) :-
	current_fact(memo_table(Key1, AbsInt, Id, Child, _, _)), !,
	erase_previous_parents_info(Child, SgKey, AbsInt, MKey, Id),
	erase_last_memo_table(AbsInt, Clid, Id),
	fail.
erase_memo_tables_and_parents_one_Id(_, _, _, _, _).

% TODO: IG These predicates are not fully ported, they were commented
% originally but they are useful

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- pred remove_useless_calls(+AbsInt)
% 	# "This predicates eliminates the analysis subtrees that are not 
%            reachable from any of the entry points to the program. 
%            We first mark all the completes that are reachable and then erase 
%            the rest. This subtrees are not needed for the program.
%            If the fixpoint algorithm works in a top_down basis they may 
%            also be incorrect as since they became unreachable they have 
%            no longer been updated. However, in this case they must have a 
%            $change_list associated.".
% 
% remove_useless_calls(AbsInt):-
% 	get_queries(AbsInt,Queries), % TODO: search
% 	mark_useful_calls(Queries, AbsInt, [], Completes),
% 	%recorded_internal(predicates,Preds,_), % TODO: where is this being asserted?
% 	predicates(Preds),
% 	remove_useless_completes(Preds,Completes, AbsInt).
%
% mark_useful_calls([], _, Completes, Completes).
% mark_useful_calls([query(Num,Key,_,_,_,_,_)|Queries], AbsInt, Comp1, Completes):-
% 	find_entry(Key, Num, Id, AbsInt),
% 	insert_call(Comp1, Id, Key, AbsInt, TmpComp),
% 	mark_useful_calls(Queries, AbsInt, TmpComp, Completes).
%
% find_entry(Key, Num, Id, AbsInt):-
% 	%recorded_internal(Key,complete(_,_,_,Id,Fs),_),
% 	complete(Key, AbsInt, _, _, _, Id, Fs),
% 	%member((query,Num),Fs).
% 	member((_,0),Fs). % IG 0 means query
% 
% insert_call(Comp1,Id, _, _,TmpComp):-
% 	ord_member(Id,Comp1),!,
% 	TmpComp = Comp1.
% insert_call(Comp1, Id, Key, AbsInt, TmpComp):-
% 	insert(Comp1,Id,Comp2),
% 	insert_all_sons(Id, Key, AbsInt, Comp2, TmpComp).
% 
% insert_all_sons(Id, Key, AbsInt, Comp2, TmpComp):-
% 	%findall((Clid,Body),
% 	%    recorded_internal(Key,clause(_,_,_,Clid,Body),_),Clauses),
% 	findall((Clid, Body), clause(Key, _, _, _, Clid, Body), Clauses),
% 	insert_sons_from_clause(Clauses, AbsInt, Id, Comp2, TmpComp).
% 
% insert_sons_from_clause([], _, _, Comp, Comp).
% insert_sons_from_clause([(Clid,Body)|Clauses], AbsInt, Id, Comp2, TmpComp):-
% 	make_atom([Clid,1],_Key1),
% 	insert_sons_from_body(Body, AbsInt, Id,Comp2,Comp3),
% 	insert_sons_from_clause(Clauses, AbsInt, Id, Comp3, TmpComp).
% 
% % TODO: IG these bodies have outdated shape
% insert_sons_from_body(([Key,_,_],RestBody), AbsInt,Id,Comp1,TmpComp):-
% 	%recorded_internal(Key,memo_table(Id,no,_,_),_),!,
% 	memo_table(Key, AbsInt, Id, no, _, _), !,
% 	insert_sons_from_body(RestBody, AbsInt, Id,Comp1,TmpComp).
% insert_sons_from_body(([Key,_,Goal],RestBody),AbsInt, Id,Comp1,TmpComp):-
% 	%recorded_internal(Key,memo_table(Id,Child,_,_),_),!,
% 	memo_table(Key, AbsInt, Id, Child, _, _), !,
% 	get_calls_in_recorded_goal(Goal,[N/A]),
% 	get_predkey(N,A,Key1),
% 	insert_call(Comp1, Child, Key1, AbsInt, Comp2),
% 	insert_sons_from_body(RestBody, AbsInt, Id, Comp2, TmpComp).
% insert_sons_from_body([Key,_,_], AbsInt, Id, Comp1,TmpComp):-
% 	%recorded_internal(Key,memo_table(Id,no,_,_),_),!,
% 	memo_table(Key, AbsInt, Id, no, _, _), !,
% 	TmpComp = Comp1.
% insert_sons_from_body([Key,_,Goal], AbsInt, Id,Comp1,TmpComp):-
% 	%recorded_internal(Key,memo_table(Id,Child,_,_),_),!,
% 	memo_table(Key, AbsInt, Id, Child, _, _), !,
% 	get_calls_in_recorded_goal(Goal,[N/A]),
% 	get_predkey(N, A, Key1),
% 	insert_call(Comp1, Child, Key1, AbsInt, TmpComp).
% insert_sons_from_body(_, _, _, Comp, Comp). %the body can be true or no memo_table
% % because the clause does not apply
% 	
% remove_useless_completes([], _, _).
% remove_useless_completes([N/A|_], Completes, AbsInt):-
% 	get_predkey(N, A, Key),
% 	%recorded_internal(Key,complete(_,_,_,Id,_),Ref),
% 	current_fact(complete(Key, AbsInt, _, _, _, Id, _), Ref),
% 	\+ member(Id,Completes),
% 	simple_message("useless node :~d",[Id]),
% 	erase(Ref),
% 	fail.
% remove_useless_completes([_|Preds], Completes, AbsInt):-
% 	remove_useless_completes(Preds, Completes, AbsInt).
