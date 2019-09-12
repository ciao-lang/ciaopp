:- module(incanal_driver,
	[init_empty_inc_analysis/0,
	 init_file_inc_analysis/3,
	 cl_from_clid/2,
	 td_add_clauses/2,
	 td_delete_clauses/2,
	 bu_delete_clauses/2
	],
	[assertions, isomodes, datafacts, nativeprops]).

:- doc(title, "Incremental analysis (low level)").
:- doc(author, "Isabel Garcia-Contreras (ported from ciaopp-0.8)").

:- doc(module, "This module contains the basic operations for adding
	or removing clauses to ciaopp (currently working for fixpoint
	dd) and perform an incremental reanalysis.

The posible actions are:
@begin{itemize}

@item Initialize ciaopp for incremental analysis (see
@pred{init_empty_inc_analysis}), for clauses to be added/removed from, they
should be implemented in a file passed to this predicate.

@item Add clauses to analysis (see @pred{td_add_clauses/2}). Adds
	clauses and performs top down reanalysis.

@item Remove clauses from analysis, following a top down strategy (see
@pred{td_delete_clauses/2}). Removes clauses and performs top down
reanalysis.

@item Remove clauses from analysis, following a bottom up strategy
(see @pred{bu_delete_clauses/2}). Removes clauses and reanalyzes
according to the strategy defined.

@end{itemize}").

:- use_module(ciaopp(plai/fixpo_dd), [add_change/5, add_external_complete_change/6]).
:- import(fixpo_dd, ['$change_list'/2, proj_to_prime/9, compute/9,
        fixpoint_compute_change/9, proj_to_prime_r/8, proj_to_prime_nr/9]). % TODO: fix me
:- use_module(ciaopp(plai/transform), [trans_clause/3, cleanup_trans_clauses/0]).
:- import(transform, [determine_r_flag/3]). % TODO: fix me
:- use_module(ciaopp(plai/domains), [identical_proj/5, init_abstract_domain/2, abs_sort/3, identical_abstract/3]).
:- use_module(ciaopp(plai/tarjan), [recursive_class/2, get_recursivity_class/3]).
:- use_module(ciaopp(p_unit/program_keys),
        [decode_clkey/4, decode_litkey/5, decode_predkey/3, get_predkey/3,
         predkey_from_sg/2, is_entrykey/1, get_litkey/5]).

%%%%% IG NEW CIAOPP IMPORTS %%%%%
:- use_module(ciaopp(frontend_driver), [module/1]).
:- use_module(ciaopp(analyze_driver), [clean_analysis_info/0, assert_domain/1]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2, set_pp_flag/2]).

:- use_module(ciaopp(p_unit), [program/2]).
:- use_module(ciaopp(p_unit/p_dump), [clean_all_ciaopp_db/0]).
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3, cleanup_clause_db/0]).
:- use_module(ciaopp(p_unit/assrt_db), [cleanup_assrt_db/0]).

:- use_module(ciaopp(plai/plai_db)).
:- use_module(ciaopp(plai), []). % Do not remove!! Low level imports below.
:- import(plai, [topdown_analysis/3, mod_topdown_analysis/3, transform_clauses_/6]). % TODO: fix me

:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(engine(messages_basic), [message/2]).

% IG old lib imports
:- use_module(library(aggregates)).
:- use_module(library(lists), [member/2, append/3, difference/3,union/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sort)).

:- use_module(ciaopp(plai/intermod_entry), [get_entry_info/3]).

:- use_module(ciaopp(plai/incanal/tarjan_inc),
        [inc_add_source_clauses/3, tarjan_data/1, rec_preds/1,
         rearrange_tarjan_after_deletion/1]).
:- use_module(ciaopp(plai/incanal/plai_db_comparator),
        [check_same_success/3, check_same_calls/5]).
:- use_module(ciaopp(plai/incanal/incanal_deletion)). % low level deletion functionality
:- use_module(ciaopp(plai/incanal/incanal_db), [init_clids/0,
        clean_incremental_db/0, get_changed_registry/4]).
:- use_module(typeslib(dumper),
        [restore_auxiliary_info/2, imp_auxiliary_info/4]).

:- use_module(ciaopp(analysis_stats)).

% ----------------------------------------------------------------------
:- doc(section, "Initialization predicates").

:- doc(init_empty_inc_analysis/0, "Initializes ciaopp for incremental
analysis. @bf{Removes all previous analysis info}.").
init_empty_inc_analysis :-
	cleanup_trans_clauses, % IG asserted clauses in traverse_clauses
	clean_analysis_info,
	clean_incremental_db,
	cleanup_clause_db,
  cleanup_assrt_db, % removes only program assertion (not cached lib assertions)
	clean_all_ciaopp_db.

:- pred init_file_inc_analysis(Files, Cls, Ds) : list(Files)
	#"Initializes incremental analysis with a file.".
init_file_inc_analysis(Files, Cls, Ds) :-
 	init_empty_inc_analysis,
 	read_file(Files, Cls, Ds),
 	init_clids.

read_file(AbsoluteName,Cls, Ds) :-
	module(AbsoluteName),
	program(Cls,Ds). % IG transformations are already done

:- pred cl_from_clid(+Clid, -Cl) : atm(Clid)
	#"Gets the processed clause @var{Cl} associated with clause id @var{Clid}.".
cl_from_clid(Clid, Cl) :-
	trans_clause(SgKey, RFlag, clause(Head, Vars_u, Clid, Body)),
	Cl = clause(SgKey,RFlag,Head,Vars_u,Clid,Body).

source_from_clid(Clid, Cl, D) :-
	source_clause(Clid, Cl, D).

sources_from_clids([], [], []).
sources_from_clids([Clid|Clids], [Cl:Clid|Cls], [D|Ds]) :-
	source_from_clid(Clid, Cl, D),
	sources_from_clids(Clids, Cls, Ds).

%---------------------------------------------------------------------
:- doc(section, "Incremental addition").

:- pred td_add_clauses(Clids, AbsInt) : list * atm #"Adds a list of
	already processed clauses, expressed with their clause id
	(@var{Clids}) to the code database and updates the analysis of
	abstract domain @var{AbsInt} with them.".
td_add_clauses([], _) :- !.
td_add_clauses(Clids, AbsInt) :-
	sources_from_clids(Clids, Cls, Ds),
	inc_plai_add(Cls, Ds, dd, AbsInt, _).

% the clause (that may have been transformed into more than one) needs to be
% reanalized (in fact is the first time it is going to be analyzed). We
% start from the beginning. We use the artificial key P/A/C/0
td_mark_add_clauses([], _).
td_mark_add_clauses([clause(_Head,_Body):Clid|Clauses], AbsInt) :-
	decode_clkey(Clid, P, A, C), !, % TODO: IG leaves choicepoint
	get_predkey(P,A,Key),
	get_litkey(P,A,C,0,LitKey),
	td_mark_add_complete(Key,LitKey,P/A/C/0, AbsInt), % module before
	td_mark_add_clauses(Clauses, AbsInt).

td_mark_add_complete(Key,LitKey,Literal, AbsInt) :-
        current_fact(complete(Key,AbsInt,_,_,_,Id,Parents)),
        add_change(Id,LitKey,Literal,Parents, AbsInt), % why free _A ?
        fail.
td_mark_add_complete(_, _, _, _).

% ----------------------------------------------------------------------
:- doc(section, "Top down deletion").

:- pred td_delete_clauses(Clids, AbsInt) : list * atm
	#"Removes clauses with ids of list @var{Clids} for abstract
          domain @var{AbsInt} from analysis using top-down deletion
 strategy and performs a reanalysis.".
td_delete_clauses([], _) :- !.
td_delete_clauses(Clids, AbsInt) :-
	stat(preproc, del_preprocess_clauses(Clids, AbsInt, Keys)),
	init_rev_idx(AbsInt), % TODO: !!!
	stat(td_delete, td_rec_delete_completes(Keys, AbsInt)),
	clean_rev_idx(AbsInt), % TODO: !!!
	run_inc_fixpoint(AbsInt).

% IG BEGIN NEW CODE

% ---- begin hack: construct reverse indices for better indexing ----
% TODO: merge with complete and memo_table updates (if it works)
:- data complete_id_key_/3.
:- data memo_table_id_key_/3.
:- export(init_rev_idx/1). % for inc assertions
init_rev_idx(AbsInt) :-
	clean_rev_idx(AbsInt),
	( complete(Key, AbsInt, _Sg, _Proj, _Prime, Id, _Parents),
	    \+ Id = no,
	    assertz_fact(complete_id_key_(Id,AbsInt,Key)),
	    fail
	; true
	),
	( memo_table(MKey, AbsInt, Id, _Child, _Sg, _Proj),
	    assertz_fact(memo_table_id_key_(Id,AbsInt,MKey)),
	    fail
	; true
	).
:- export(clean_rev_idx/1). % for inc assertions
clean_rev_idx(AbsInt) :-
	retractall_fact(complete_id_key_(_,AbsInt,_)),
	retractall_fact(memo_table_id_key_(_,AbsInt,_)).

% IG: ensure that the deletion does not fail even if the indexes are not created
:- export(complete_id_key/3). % for inc assertions
complete_id_key(A, B, C) :-
	complete_id_key_(A, B, C), !.
complete_id_key(_, _, _).

:- export(memo_table_id_key/3). % for inc assertions ( % TODO: not necessary )
memo_table_id_key(_, _, _) :-
	\+ memo_table_id_key_(_, _, _), !.
memo_table_id_key(A, B, C) :-
	memo_table_id_key_(A, B, C).

% ---- end hack: construct reverse indices for better indexing ----

td_rec_delete_completes([], _).
td_rec_delete_completes([Key|Keys], AbsInt) :-
	findall(Id, complete(Key, AbsInt, _, _, _, Id, _), Ids),
	td_rec_delete_completes_(Ids, Key, AbsInt), !,
	td_rec_delete_completes(Keys, AbsInt).
td_rec_delete_completes([_|Keys], AbsInt) :-
	td_rec_delete_completes(Keys, AbsInt).

td_rec_delete_completes_([], _, _).
td_rec_delete_completes_([Id|Ids], Key, AbsInt) :-
	td_rec_delete_complete(Id, Key, AbsInt), !,
	td_rec_delete_completes_(Ids, Key, AbsInt).
td_rec_delete_completes_([_|Ids], Key, AbsInt) :-
	td_rec_delete_completes_(Ids, Key, AbsInt).

:- export(td_rec_delete_complete/3).
:- pred td_rec_delete_complete(+Id, ?Key, +AbsInt)
        : (plai_db_id(Id), atm(AbsInt)) + not_fails
 #"This predicate removes the complete with @var{Id} in domain @var{AbsInt} and
  	all its dependent information".
td_rec_delete_complete(no, _Key, _) :- !.
td_rec_delete_complete(Id, Key, AbsInt) :- % pass Key
        %	complete_id_key(Id, AbsInt, Key), % (for indexing) % this should work
        retract_fact(complete(Key, AbsInt, _Sg, _Proj, _Prime, Id, Parents)), !,
        remove_memo_table(Id, AbsInt),
        remove_memo_table_depends_complete(Parents, AbsInt, Id).
td_rec_delete_complete(_,_,_).

remove_memo_table_depends_complete([], _, _).
remove_memo_table_depends_complete([(PKey, _Id)|Parents], AbsInt, Id) :-
        is_entrykey(PKey), !,
        remove_memo_table_depends_complete(Parents, AbsInt, Id).
remove_memo_table_depends_complete([(LitKey, PId)|Parents], AbsInt, Id) :-
        ( get_parent_key(LitKey,PId,AbsInt,Key) -> % get_parent_key may fail if the complete was already removed
            td_rec_delete_complete(PId, Key, AbsInt) 
        ; true
        ),
        remove_memo_table_depends_complete(Parents, AbsInt, Id).

% remove all the arcs of the call that depends on that memo_table entry
remove_memo_table(Id, AbsInt) :-
	( % failure-driven loop
	  memo_table_id_key(Id, AbsInt, MKey), % (for indexing)
	  retract_fact(memo_table(MKey, AbsInt, Id, Child, _Sg, _Proj)),
	     % TODO: check PKey for basicprops completes
	     complete_key_from_id(Child, AbsInt, PKey),
	     erase_rec_prev_parents(PKey, MKey, AbsInt, Id, Child),
	     fail
	; true
	).

complete_key_from_id(Id, AbsInt, Key) :-
	complete_id_key(Id, AbsInt, Key0), % (for indexing)
	% complete(Key, AbsInt, _, _, _, Id, _), % slower (no indexing)
	!,
	Key = Key0.

erase_rec_prev_parents(GKey,K,AbsInt,NewN,Id):-
        atom(GKey), !,
        del_parent_complete(GKey,AbsInt,Id,K,NewN,NewParents),
        decide_delete_complete(GKey,NewParents),
        td_rec_delete_complete(Id, GKey, AbsInt). % TODO:!!
erase_rec_prev_parents(_,_,_,_,_).

:- export(decide_delete_complete/2).
decide_delete_complete(_, []) :- !. % The complete has no more parents
decide_delete_complete(GKey, NewParents) :-
	decode_predkey(GKey, P, A),
	recursive_class(P/A, Class),
	all_parents_same_rec_class(NewParents, Class).

% [IG]
% We remove the complete if all its parents belong to the same
% recursive class.  The recursive class is an over-approximation of
% the actual dinamic call graph that is stored in the memo_table.  The
% use of the static recursive classes for deciding wether there are
% cycles in the complete parents may cause deletions that were not
% necessary (i.e., for example the parents could be in the same rec
% class but with a call pattern comming from a different call).
all_parents_same_rec_class([], _Class).
all_parents_same_rec_class([(LitKey, _)|Ps], Class) :-
	decode_litkey(LitKey, P, A, _C, _L),
	member(P/A, Class), !,
	all_parents_same_rec_class(Ps, Class).

:- data useful/1.

useless(no) :- !, fail.
useless(0) :- !, fail. % query Id is never useless
useless(Id) :- % IG: only to check, do not generate.
        \+ useful(Id), !.

% TODO: review for non-modular driver
remove_useless_completes(AbsInt) :-
	init_rev_idx(AbsInt), % TODO: !!!
	retractall_fact(useful(_)),
  ( curr_mod_entry(SgKey, AbsInt, Sg, Proj), % backtrack here
      mark_useful_complete(SgKey,AbsInt,Sg,Proj),
	    fail
	; true),
  remove_useless_tuples(AbsInt),
	clean_rev_idx(AbsInt). % TODO: !!!

mark_useful_complete(SgKey,AbsInt,Sg,Proj) :-
	  complete(SgKey, AbsInt, Sg1, Proj1, _E, Id, _Fs), % creating choicepoints
	  check_same_calls(AbsInt, Sg, Proj, Sg1, Proj1), !,
    mark_useful_sons(Id, AbsInt).
mark_useful_complete(_SgKey,_AbsInt,_Sg,_Proj).

mark_useful_sons(no, _AbsInt) :- !. % special case (auxiliary completes have Id = no)
mark_useful_sons(Id, _AbsInt) :-
	useful(Id), !. % do nothing if already visited
mark_useful_sons(Id, AbsInt) :-
	assertz_fact(useful(Id)),
	( % failure-driven loop
	  memo_table_id_key(Id, AbsInt, MKey),
	    memo_table(MKey, AbsInt, Id, Child, _, _),
	    mark_useful_sons(Child, AbsInt),
	    fail
	; true
	).

remove_useless_tuples(AbsInt) :-
	current_fact(complete(SgKey, AbsInt, Sg, Proj, Prime, Id, Fs), Ref),
	( useless(Id) -> true
	;
	    ( (Id = no, Fs = []) -> true % Auxiliary complete, remove for now
	    ;
          update_parents(Fs, NFs),
          assertz_fact(complete(SgKey, AbsInt, Sg, Proj, Prime, Id, NFs))
	    )
	),
	erase(Ref),
	fail.
remove_useless_tuples(AbsInt) :-
	current_fact(memo_table(_MKey, AbsInt, Id, _, _, _), Ref),
	useless(Id),
	erase(Ref),
	fail.
remove_useless_tuples(_).

update_parents([], []).
update_parents([(_,Id)|Fs], NFs) :-
	useless(Id), !,
	update_parents(Fs, NFs).
update_parents([F|Fs], [F|NFs]) :-
	update_parents(Fs, NFs).
% IG END NEW CODE

% ----------------------------------------------------------------------
% for preprocessing when deleting
del_preprocess_clauses(Clids, AbsInt, Keys) :-
	remove_clauses_and_related_info_collect_preds(Clids, AbsInt, Preds_u,Keys),
	sort(Preds_u,Preds), % no repetitions
	rearrange_tarjan_after_deletion(Preds).

:- doc(section, "Bottom-up down deletion").

:- pred bu_delete_clauses(Clids, AbsInt) : list * atm + not_fails
  	#"Removes clauses @var{Cls} for abstract domain @var{AbsInt}
          from analysis using the bottom up deletion strategy and
          performs a reanalysis.".
bu_delete_clauses([], _) :- !.
bu_delete_clauses(Clids, AbsInt) :-
	set_pp_flag(widen, on),
	retractall_fact('$change_list'(_,_)), % TODO: IG store context??
	stat(preproc, del_preprocess_clauses(Clids, AbsInt,Keys_u)),
	%
	sort(Keys_u,Keys),
	tarjan_data(SCCs),
	stat(bu_delete, bottom_up_delete_mark_preds(Keys,SCCs,AbsInt,Completes)),
	stat(fixp, run_bu_del_fixp(Completes,AbsInt,SCCs)),
	remove_useless_completes(AbsInt).

run_bu_del_fixp(Completes,AbsInt,SCCs) :-
	analyze_external_calls(Completes,New_answers,AbsInt),
	bottom_up_reanalyze_SCC(Completes,New_answers,AbsInt,SCCs).

% IG: removing the 'useless' completes, i.e., completes which have no
% parents would not be necessary if during the reanalysis, completes
% with empty parents would be (recursively) deleted.

bottom_up_reanalyze_SCC(Completes,New_answers,AbsInt,SCCs) :-
	% IG: get the list of answers that changed
	only_different(Completes,New_answers,Differ,AbsInt),
	bottom_up_reanalyze_another_level(Differ,AbsInt,SCCs), !.

only_different([],[],[],_) :- !.
only_different(Comps1,[N_Prime|N_Primes],Differ,AbsInt):-
	Comps1 = [comp(_,_,O_Prime,_,Fs)|Comps],
	( check_same_success(AbsInt,O_Prime,N_Prime) ->
	    Differ = N_differ
	;
	    Differ = [Fs|N_differ]),
	only_different(Comps,N_Primes,N_differ,AbsInt).

bottom_up_reanalyze_another_level([], _, _) :- !.
bottom_up_reanalyze_another_level(Fss, AbsInt, SCCs) :-
	b_up_mark_prev_parents(Fss, NewCompletes, AbsInt, SCCs),
	analyze_external_calls(NewCompletes, New_answers, AbsInt), !,
	bottom_up_reanalyze_SCC(NewCompletes, New_answers, AbsInt, SCCs).

b_up_mark_prev_parents([], [], _, _).
b_up_mark_prev_parents([Fs|Fss], Completes, AbsInt, SCCs) :-
	b_up_prev_literal(Fs, Complete, AbsInt, SCCs),
	append(Complete, MoreCompletes, Completes),
	b_up_mark_prev_parents(Fss, MoreCompletes, AbsInt, SCCs).

b_up_prev_literal([],[],_,_).
b_up_prev_literal([(_Clid, 0)|Fs],Completes,AbsInt,SCCs) :- !, 
	% Id = 0,   % IG: entries have clause id of parent 0
	b_up_prev_literal(Fs,Completes,AbsInt,SCCs).
b_up_prev_literal([(Lit,Id)|Fs],Completes,AbsInt,SCCs):-
	decode_litkey(Lit,N,A,_,_),
	get_recursivity_class(N/A,SCCs,SCC),
	get_predkey(N,A,Key),
	bottom_up_delete_mark_one(Key,Id,SCC,AbsInt,Complete),
	append(Complete,MoreCompletes,Completes),
	b_up_prev_literal(Fs,MoreCompletes,AbsInt,SCCs).

% analyze_external_calls(+,-,+)
analyze_external_calls([],[],_).
analyze_external_calls([comp(Sg,Proj,_,Id,Fs)|Comps],[Answer|Answers],AbsInt):-
	functor(Sg,P,A),
	rec_preds(Ps),  % IG added, needed for determine_r_flag/3
	determine_r_flag(Ps, P/A,RFlag),
	varset(Sg,Sv),
	% this may not work for alls AbsInt as 3rd argument is not filled
	get_predkey(P,A,SgKey),
	bu_del_call_to_succ(RFlag,SgKey,Proj,Proj,Sg,Sv,AbsInt,Answer,Fs,Id), % Call=Proj
	remove_useless_completes(AbsInt),
	analyze_external_calls(Comps,Answers,AbsInt).

:- pred bu_del_call_to_succ(+R_flag,+SgKey,+Call,+Proj,+Sg,+Sv,+AbsInt,-Succ,+Fs,+Id)
	# "This predicate is a modification of predicate
           @pred{call_to_success/11} defined in an analysis
           algorithms.  The main differences are that rather than
           adding one element to the list of clauses for the complete,
           we add the list of external calls previously computed for
           the complete.".
% TODO: This predicate is never used
% bu_del_call_to_success(_,SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,Fs,Id) :-
% %	display('WARNING! using bu_del_call_to_success/10'), nl,
% 	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs1), Ref), % IG up
% 	identical_proj(AbsInt,Sg,Subg,Proj,Proj1),!,
% 	abs_sort(AbsInt,Prime1,TempPrime), % TODO: WRONG! Prime1 is a list!
% 	erase(Ref),
% 	(retract_fact('$change_list'(Id,ChList)) ->
% 	    fixpoint_compute_change(ChList,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id),
% 	    delete_complete_and_aux(complete(SgKey, AbsInt, A,B,C,Id,Fs2)),
% 	    union(Fs,Fs2,Fs3),
% 	    asserta_fact(complete(SgKey, AbsInt, A,B,C,Id,Fs3)) % IG up
% 	;
% 	    Prime = TempPrime,
% 	    union(Fs,Fs1,Fs3),
% 	    asserta_fact(complete(SgKey, AbsInt, Sg,Proj,Prime,Id,Fs3)) % IG up
% 	),
% 	extend(AbsInt,Prime,Sv,Call,Succ), !.

bu_del_call_to_succ(nr,SgKey,Call,Proj,Sg,Sv,AbsInt,Prime,Fs,Id) :-
	proj_to_prime_nr(SgKey, Sg, Sv, Call, Proj, AbsInt, SgKey, Prime, Id),
	% compute_lub(AbsInt,ListPrime,Prime), % IG not needed
	%extend(AbsInt,Prime,Sv,Call,Succ), % IG already extended
	asserta_fact(complete(SgKey, AbsInt, Sg,Proj,Prime,Id,Fs)), !. % IG: why the cut here, assert never fails
bu_del_call_to_succ(r,SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,Fs,Id) :-
	proj_to_prime_r(SgKey, Sg, Sv, Call, Proj, AbsInt, TempPrime, Id), % IG
	% compute_lub(AbsInt,ListPrime,TempPrime), % IG not needed
	asserta_fact(complete(SgKey, AbsInt, Sg,Proj,TempPrime,Id,[])),
	% IG: asserting a complete with no parents!
	bagof(X, X^(trans_clause(SgKey, r, X)),Clauses), % IG old, moved to the first line
	compute(Clauses,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id),
	(current_fact('$change_list'(Id,ChList), Ref2) ->
	   erase(Ref2),
	   fixpoint_compute_change(ChList,SgKey,Sg,Sv,Proj,AbsInt,Prime,NPrime,Id)
	;
	    NPrime = Prime
	),
	retract_fact(complete(SgKey, AbsInt, A,B,C,Id,Fs2)),
	%delete_complete_and_aux(complete(SgKey, AbsInt, A,B,C,Id,Fs2)),
	union(Fs,Fs2,Fs3),
	asserta_fact(complete(SgKey, AbsInt, A,B,C,Id,Fs3)),
	Succ = NPrime. % IG Is this right?
        % extend(AbsInt,NPrime,Sv,Call,Succ),!. % IG Is this extend needed?
                                             % IG probably made by project

delete_complete_and_aux(complete(SgKey,AbsInt,C,D,E,Id,Fs)) :-
	( % failure-driven loop
    current_fact(complete(_, AbsInt, _, _, _, no, Ps), Ref), % TODO: performance
    member((_, Id), Ps),
        erase(Ref),
        fail
	; retract_fact(complete(SgKey, AbsInt, C,D,E,Id,Fs))
	).

%-------------------------------------------------------------------
:- doc(section, "Predicates for running the fixpoint.").

:- export(run_inc_fixpoint/1).
:- pred run_inc_fixpoint(AbsInt) #"This predicate runs fixpoint for
	abstract domain @var{AbsInt}. It is thought to be runned after
	adding information from registry files in intermodular analysis.".
run_inc_fixpoint(AbsInt) :-
	rec_preds(Ps),
	set_pp_flag(widen, on),
	inc_query(dd, AbsInt, Ps), !. % analyzing leaves choicepoints

%  Here we start the top-down incremental analysis. It is the
% same as abs_interpret, but we do not reset fixpoint_id to 0 as that
% may be dangerous (two different completes may get the same number)

inc_plai_add(Cls,Ds,Fixp,AbsInt,_):-
	% initialization
	init_abstract_domain(AbsInt,_Flags),
	do_inc_plai_add(Cls, Ds, Fixp, AbsInt, _, _).

do_inc_plai_add(Cls, Ds, dd, AbsInt, _, _) :-
	%add_packages_if_needed(AbsInt), % TODO: IG: This is for output only
	stat(preproc, inc_add_source_clauses(Cls, Ds, AbsInt)),
	% update the recursivity after new clauses
	stat(td_add, td_mark_add_clauses(Cls, AbsInt)),
  run_inc_fixpoint(AbsInt).

inc_query(dd, AbsInt, Ps) :-
	init_abstract_domain(AbsInt, _Flags), % IG flags is an output var? % fast
	call_inc_fixpoint(dd,AbsInt,Ps), !,
  remove_useless_completes(AbsInt).
inc_query(Fixp, _, _) :-
	( Fixp = dd ->
	    message(error, ['Analysis failed'])
	;
	    message(warning, ['incremental analysis works only for fixpoint dd'])
	).

call_inc_fixpoint(Fixp,AbsInt,Ps) :-
	assert_domain(AbsInt),
  using_modular_driver, !,
	stat(fixp, mod_topdown_analysis(AbsInt, Fixp, Ps)).
call_inc_fixpoint(Fixp,AbsInt,Ps) :-
	stat(fixp, topdown_analysis(Fixp, AbsInt, Ps)).

using_modular_driver :-
        \+ current_pp_flag(intermod, off).

% --------------------------------------------------
:- doc(section, "Modular analysis predicates").

:- export(incrementally_update_analysis/2).
:- pred incrementally_update_analysis(Mod, AbsInt) #" @var{Mod} is the module
	that will be reanalyzed after updating its external
	completes. To be called in modular analysis, no following
 analysis needed. This is a top-down strategy update".
incrementally_update_analysis(Mod, AbsInt) :-
        get_external_completes(Mod, AbsInt, Comps),
        init_rev_idx(AbsInt), % TODO: !!!
        update_imported_completes(Comps, Mod, AbsInt),
        remove_useless_completes(AbsInt). % Index cleaned here

get_external_completes(Mod, AbsInt, Cs) :-
 	findall((EMod, C), external_updated_complete(Mod, AbsInt, C, EMod), Cs).

:- pred external_updated_complete(Module, AbsInt, C, ExtMod) #"@var{C}
	is a complete of a predicate which is not defined in
	@var{Module}.".
external_updated_complete(Module, AbsInt, C, M) :-
 	complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents),
 	decode_predkey(SgKey, P, _),
 	module_split(P, M, _),
	Module \= M,
	\+ Id = no,
 	C = complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Parents).

:- pred update_imported_completes/3 + not_fails.
update_imported_completes([], _, _).
update_imported_completes([(ImpMod, C)|Cs], CMod, AbsInt) :-
	filter_comps_mod(Cs, ImpMod, NCs, RestCs),
	apply_changes_imported_mod([C|NCs], CMod, ImpMod),
	update_imported_completes(RestCs, CMod, AbsInt).

:- pred filter_comps_mod/4 + not_fails.
filter_comps_mod([], _, [], []).
filter_comps_mod([(Mod, C)|Cs], Mod, [C|NCs], RestCs) :- !,
	filter_comps_mod(Cs, Mod, NCs, RestCs).
filter_comps_mod([Comp|Cs], Mod, NCs, [Comp|RestCs]) :-
	filter_comps_mod(Cs, Mod, NCs, RestCs).

:- pred apply_changes_imported_mod/3 + not_fails.
apply_changes_imported_mod(Comps, CMod, Mod) :-
	restore_types_mod(Mod, Dict), % restore module types
	findall((SgKey, Reg), get_changed_registry(SgKey, CMod, Mod, Reg), ChRegs),
	decide_apply_changed_registries(ChRegs, Mod, Comps, Dict).

:- pred decide_apply_changed_registries/4 + not_fails.
decide_apply_changed_registries([], _, _, _).
decide_apply_changed_registries([(SgKey,ChReg)|ChRegs], Mod, Comps, Dict) :-
	ChReg = regdata(_,AbsInt,Sg,RegProj,RegPrime,_,_,_,_),
	( AbsInt = eterms -> % TODO: generalize % Importing should be a domain action
	    imp_auxiliary_info(AbsInt, Dict, [RegProj,RegPrime],[Proj,Prime])
	;
	    Proj = RegProj, Prime = RegPrime
	),
	abs_sort(AbsInt, Proj, Proj_s),
	apply_changes_imported_comps(Comps,SgKey,Sg,Proj_s,Prime,_RestComps),
	decide_apply_changed_registries(ChRegs, Mod, Comps, Dict).

:- pred apply_changes_imported_comps/6 + not_fails.
apply_changes_imported_comps([],_,_,_,_,[]).
apply_changes_imported_comps([Comp|Comps],SgKey,Sg,ImpProj,ImpPrime,Comps) :-
        Comp = complete(SgKey,AbsInt,Sg,Proj,OldPrime,Id,_),
        abs_sort(AbsInt, Proj, Proj_s),
        identical_proj(AbsInt,Sg,ImpProj,Sg,Proj_s), !,
        CNPrime = [ImpPrime],
        % IG this [ImpPrime] list is because registries do not store success
        % patterns as lists (multivariant is not considered for intermod?)
        ( check_same_success(AbsInt, OldPrime, CNPrime) -> % this predicate sorts the abs subs
            true
        ;
            add_external_complete_change(AbsInt, CNPrime, SgKey,Sg,Id,Proj)
        ).
apply_changes_imported_comps([Comp|Comps], SgKey, Sg, ImpProj, ImpPrime, [Comp|NComps]) :-
	apply_changes_imported_comps(Comps, SgKey, Sg, ImpProj, ImpPrime, NComps).

restore_types_mod(Mod, Dict) :-
	set_fact(restore_module(Mod)),
	restore_auxiliary_info(enum_types,Dict).

:- use_module(ciaopp(p_unit/p_abs), [curr_mod_entry/4]).
:- import(p_abs, [typedef/2]). % TODO: fix me

:- data restore_module/1.

enum_types(TypeDef):-
	current_fact(restore_module(Module)),
	current_fact(typedef(Module,TypeDef)).
