:- module(prepare_ai_output,
	[ cleanup_output/1,
	  prepare_ai_output/4
	],
	[assertions, datafacts, ciaopp(ciaopp_options)]).

:- use_module(engine(io_basic)).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists),      [append/3]).
:- use_module(library(sets),       [ord_subtract/3]).
:- use_module(library(sort)).
:- use_module(library(terms_vars), [varset/2]).

% CiaoPP library
:- use_module(ciaopp(infer/infer_db), [inferred/3, point_info/5]).
:- use_module(ciaopp(infer/infer_dom), [asub_to_out/6, knows_of/2, non_collapsable/1]).
:- use_module(ciaopp(plai/domains), 
	[ abs_sort/3,
	  asub_to_out/5,  % IG: asub_to_out/6 also!!!!
	  call_to_entry/10,
	  compute_lub/3
	]).
:- use_module(ciaopp(plai/plai_db)).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(ciaopp(p_unit/assrt_db), [
	assertion_body/7,
	removeall_assertion_read/9,
	add_assertion_read/9]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(typeslib(typeslib), [simplify_step2/0]).
:- if(defined(has_ciaopp_extra)).
:- use_module(infercost(infercost_register),
	[is_ualb_complexity_analysis/3]).
:- endif.

:- use_module(ciaopp(pool)).

:- include(domain_dep).


% -------------------------------------------------------------------------

:- doc(bug,"1. The information gathered here could have been already
	computed before and be stored in infer_db.").
%% :- doc(bug,"2. Should not prepare info for imported: since it does not go
%% 	out, some not required types might go out anyway...").
:- doc(bug,"3. This occurs when transforming info for output:
        {WARNING (lsign): not normalised program: goal
           'sqr:.=.'(_269,_272*_272) wrt head 'sqr:.=.'(_479,_480)}").
:- doc(bug,"4. To reduce type simplification, we are asserting tmp_*_info
	when lub required. Instead, we should first do all the lubs (memo_lub,
	complete_lub) and then use them for asub_to_info (thus, avoiding yet
        more asserts).").
:- doc(bug,"5. After type simplification the type analysis info asserted
	is kind of inconsistent: we have X:t55, ask for the definition for
	t55 and we get a definition for listint --or none-- because they are
	equivalent. Thus, we should change all asserted info by collapsing to
	equivalent types.").
%% :- doc(bug,"6. Calling asub_to_info from any other place asserts
%% 	required types which are not so, and go out...").
:- doc(bug,"7. prepare_succ_list_info/7 is wrong: we cannot accumulate
        SuccInfo and CompInfo in parallel, it results in wrong assertions.
	E.g., :- true pred r(A) : rt0(A) => rt0(A) + fails.
        for r(a). r(b). with rt(0):==^a").

% -------------------------------------------------------------------------

cleanup_output(M):-
	retractall_fact(point_info(_,_,_,_,_)),
	removeall_assertion_read(_Goal,M,true,pred,_Body,_Dict,no,0,0).

% -------------------------------------------------------------------------

%% prepare_ai_output prepares the info from analysis to be printed
%% according to the options selected by the user

prepare_ai_output(PPoints,Modes,AbsInt,Collapse):-
	retractall_fact(tmp_point_info(_Key0,AbsInt,_Vars,_ASub)),
	retractall_fact(tmp_complete_info(_Key1,AbsInt,_Goal,_Call,_Succ)),
        prepare_ai_output_(PPoints,Modes,AbsInt,Collapse).

prepare_ai_output_(_PPoints,_Modes,AbsInt,_Collapse):-
	% currently, have a different treatment
	current_fact(inferred(AbsInt,_,_)), 
        !,
	simplify_types_anyway(AbsInt),
	prepare_infer_output(AbsInt).
:- if(defined(has_ciaopp_extra)).
prepare_ai_output_(_PPoints,_Modes,AbsInt,_Collapse):-
	% currently, have a different treatment
        is_ualb_complexity_analysis(AbsInt, Lower_An, Upper_An),
	current_fact(inferred(Lower_An,_,_)), 
        current_fact(inferred(Upper_An,_,_)), 
        !,
        prepare_infer_output(AbsInt).
:- endif.
prepare_ai_output_(PPoints,Modes,AbsInt,Collapse):-
	simplify_types_if_no_lub(Collapse,AbsInt),
	complete_info(Collapse,Modes,AbsInt),
	memo_info(PPoints,Collapse,Modes,AbsInt),
	simplify_types_if_lub(Collapse,AbsInt),
	tmp_info_to_complete_info(AbsInt,Modes).

complete_info(off,Modes,AbsInt):-
	complete_info_no(Modes,AbsInt).
complete_info(on,Modes,AbsInt):-
	complete_info_yes(Modes,AbsInt).

complete_info_no(Modes,AbsInt):-
	there_is_delay, !,
	get_del_completes(AbsInt,Modes).
complete_info_no(Modes,AbsInt):-
	get_completes(AbsInt,Modes).

complete_info_yes(Modes,AbsInt):-
	there_is_delay, !,
	lub_del_completes(AbsInt,Modes).
complete_info_yes(Modes,AbsInt):-
	lub_completes(AbsInt,Modes).

memo_info(off,_Collapse,_Modes,_AbsInt).
memo_info(on,Collapse,Modes,AbsInt):-
	memo_info_(Collapse,Modes,AbsInt).

memo_info_(off,Modes,AbsInt):- get_memo_table(AbsInt,Modes).
memo_info_(on,Modes,AbsInt):- lub_memo_table(AbsInt,Modes).

%% This issue with type simplification, ugh!
%% type simplification must be done before asub_to_info
%% when lub required, asub_to_info is delayed (see tmp_info_to_complete_info/2)
%%     so that type simplification is called only once

simplify_types_anyway(AbsInt):-
	knows_of(regtypes,AbsInt), !,
	simplify_step2.
simplify_types_anyway(_AbsInt).

simplify_types_if_lub(on,AbsInt):-
	knows_of(regtypes,AbsInt),
	\+ non_collapsable(AbsInt), !,
	simplify_step2.
simplify_types_if_lub(_Collapse,_AbsInt).

simplify_types_if_no_lub(off,AbsInt):-
	knows_of(regtypes,AbsInt), !,
	simplify_step2.
simplify_types_if_no_lub(on,AbsInt):-
	knows_of(regtypes,AbsInt),
	non_collapsable(AbsInt), !,
	simplify_step2.
simplify_types_if_no_lub(_Collapse,_AbsInt).

%% simplify_step2_:-
%% 	display('calling...'),
%% 	simplify_step2,
%% 	display(done), nl.

%% Get complete records and recorda info to be printed
%% (when no lub required and del_interpret used)

get_del_completes(AbsInt,Modes):-
	non_imported_complete(Key,AbsInt,Goal,d(ACns,Del,_),Succ),
	assert_complete_info(AbsInt,Modes,Key,Goal,d(ACns,Del),Succ),
	fail.
get_del_completes(_AbsInt,_Modes).

assert_complete_info(AbsInt,Output,_Key,Goal,Call,Succ):-
	varset(Goal,Vars),
	prepare_call_info(Output,AbsInt,Vars,Call,Call_s,CallInfo),
	prepare_succ_info(Output,AbsInt,Vars,Call_s,Succ,SuccInfo,CompInfo),
	assert_pred_info(Goal,CallInfo,[SuccInfo],[CompInfo]),
	!.

%% Get complete records and recorda info to be printed
%% (when no lub required and abs_interpret or or_abs_interpret used)

get_completes(AbsInt,Modes):-
	non_imported_complete(Key,AbsInt,Goal,Call,Succs),
	assert_complete_list_info(AbsInt,Modes,Key,Goal,Call,Succs),
	fail.
get_completes(_AbsInt,_Modes).

assert_complete_list_info(AbsInt,O,_Key,Goal,Call,Succs):-
	varset(Goal,Vars),
	prepare_call_info(O,AbsInt,Vars,Call,Call_s,CallInfo),
	prepare_succ_list_info(Succs,AbsInt,O,Vars,Call_s,SuccInfos,CompInfos),
	assert_pred_info(Goal,CallInfo,SuccInfos,CompInfos),
	!.

non_imported_complete(Key,AbsInt,Goal,Call,Succs):-
	current_fact(complete(Key,AbsInt,Goal,Call,Succs,_,_)),
	\+ type_of_goal(imported,Goal).

%% Get complete records and recorda info to be printed
%% (when lub required and del_interpret used)

lub_del_completes(AbsInt,Modes):-
	findall((Key,Goal,d(ACns,Del),Succ),
	        non_imported_complete(Key,AbsInt,Goal,d(ACns,Del,_),Succ),
		Completes),
	sort(Completes,Completes_s),
	group_completes(Completes_s,Completes_g),
	lub_and_assert_del_complete_info(Completes_g,AbsInt,Modes).

:- push_prolog_flag(multi_arity_warnings,off).

group_completes(Completes_s,Completes_g):-
	Completes_s = [(Key,Goal,Call,Succ)|Completes], !,
	group_completes(Completes,Key,[(Goal,Call,Succ)|L],L,Completes_g).
group_completes(Completes,Completes).


group_completes([],Key0,List,[],[(Key0,List)]) :-
	!.
group_completes([(Key,Goal,Call,Succ)|Completes],Key,List,Tail,Completes_g):- 
	Tail = [(Goal,Call,Succ)|Tail1],
	!,
	group_completes(Completes,Key,List,Tail1,Completes_g).
group_completes([(Key,Goal,Call,Succ)|Completes],Key0,List,[],[(Key0,List)|Completes_g]):-
	group_completes(Completes,Key,[(Goal,Call,Succ)|Tail1],Tail1,Completes_g).

:- pop_prolog_flag(multi_arity_warnings).

lub_and_assert_del_complete_info([(Key,Calls)|Completes],AbsInt,Output):-
	Calls=[(Goal,_Call1,_Succ1)|_],
	del_lub_of_calls(Calls,Goal,AbsInt,'$bottom','$bottom',Call,Succ),
	assert_complete_info(AbsInt,Output,Key,Goal,Call,Succ),
	lub_and_assert_del_complete_info(Completes,AbsInt,Output).
lub_and_assert_del_complete_info([],_AbsInt,_Output).

del_lub_of_calls([],_Goal,_AbsInt,Call,Succ,Call,Succ).
del_lub_of_calls([(Goal,Call,Succ)|Calls],Goal,AbsInt,TmpCall,TmpSucc,NCall,NSucc):-
	del_compute_lub([Call,TmpCall],AbsInt,Call2),
	del_compute_lub([Succ,TmpSucc],AbsInt,Succ2),
	del_lub_of_calls(Calls,Goal,AbsInt,Call2,Succ2,NCall,NSucc).

%% Get complete records and recorda info to be printed
%% (when lub required and abs_interpret or or_abs_interpret used)

lub_completes(AbsInt,Modes):-
	findall((Key,Goal,Call,Succs),
	        non_imported_complete(Key,AbsInt,Goal,Call,Succs),
		Completes),
	lub_and_assert_completes(Completes,AbsInt,Modes).

lub_and_assert_completes(Completes,AbsInt,Modes):-
	sort(Completes,Completes_s),
	group_completes(Completes_s,Completes_g),
	lub_and_assert_complete_info(Completes_g,AbsInt,Modes).

lub_and_assert_complete_info([(Key,Calls)|Completes],AbsInt,Output):-
	Calls=[(Goal1,_Call1,_Succ1)|_],
	functor(Goal1,F,A),
	functor(Goal,F,A),
	varset(Goal,Gv),
	lub_of_calls(Calls,AbsInt,Goal,Gv,'$bottom','$bottom',Call,Succ),
	assert_complete_info_(AbsInt,Output,Key,Goal,Call,Succ),
	lub_and_assert_complete_info(Completes,AbsInt,Output).
lub_and_assert_complete_info([],_AbsInt,_Output).

lub_of_calls([],_AbsInt,_Goal,_Gov,Call,Succ,Call,Succ).
lub_of_calls([(Goal1,Call1,Succs)|Calls],AbsInt,Goal,Gov,
	      TmpCall,TmpSucc,NCall,NSucc):-
        sort_list_subs(Succs,AbsInt,Succs_s),
	compute_lub_(AbsInt,Succs_s,Succ1),
	most_general_goal(Goal1,Call1,Succ1,AbsInt,Goal,Gov,Call,Succ),
	compute_lub(AbsInt,[Call,TmpCall],Call2),
	compute_lub(AbsInt,[Succ,TmpSucc],Succ2),
	lub_of_calls(Calls,AbsInt,Goal,Gov,Call2,Succ2,NCall,NSucc).

% TODO: duplicated
most_general_goal(Goal1,Call1,Succ1,AbsInt,Goal,Gov,Call,Succ):-
	abs_sort(AbsInt,Call1,Call_s),
	abs_sort(AbsInt,Succ1,Succ_s),
	varset(Goal1,Go1v),
	decide_call_to_entry(Call_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Call),
	decide_call_to_entry(Succ_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Succ).

% TODO: duplicated
decide_call_to_entry('$bottom',_AbsInt,_Go1v,_Goal1,_Gov,_Goal,_,'$bottom'):-!.
decide_call_to_entry(Call_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Call):-
	call_to_entry(AbsInt,Go1v,Goal1,Gov,Goal,not_provided,[],Call_s,Call,_).

%% Get memo_table records and recorda info to be printed
%% (when no lub required)

get_memo_table(AbsInt,Modes):-
	current_fact(memo_table(Key,AbsInt,_,_,Vars,ASubs)),
	member_(ASub,ASubs),
	prepare_point_info(Modes,AbsInt,Vars,ASub,Info),
	assert_point_info(Key,Vars,AbsInt,Info),
	fail.
get_memo_table(_AbsInt,_Modes).

member_(ASub,[X|_]):- nonvar(X), X=ASub.
member_(ASub,[_|Xs]):- nonvar(Xs), member_(ASub,Xs).

%% Get memo_table records and recorda info to be printed
%% (when lub required)

lub_memo_table(AbsInt,Modes):-
	findall((Key,Vars,ASubs),
	        current_fact(memo_table(Key,AbsInt,_,_,Vars,ASubs)),
		Memos),
	sort(Memos,Memos_s),
	group_lub_and_assert_memos(Memos_s,AbsInt,Modes).
	
group_lub_and_assert_memos([(Key,Vars,ASubs)|Memos],AbsInt,Modes):-
        sort_list_subs(ASubs,AbsInt,ASubs_s),
	group_memos(Memos,Key,Vars,ASubs_s,AbsInt,Modes).
group_lub_and_assert_memos([],_AbsInt,_Modes).

group_memos([(Key,Vars,ASubs)|Memos],Key,Vars,ASubs0,AbsInt,Modes):- !,
        sort_list_subs(ASubs,AbsInt,ASubs_s),
	append(ASubs_s,ASubs0,ASubs1),
	group_memos(Memos,Key,Vars,ASubs1,AbsInt,Modes).
group_memos([(Key,Vars,ASubs)|Memos],Key0,Vars0,ASubs0,AbsInt,Modes):-
	lub_and_assert_memo(Key0,Vars0,ASubs0,AbsInt,Modes),
        sort_list_subs(ASubs,AbsInt,ASubs_s),
	group_memos(Memos,Key,Vars,ASubs_s,AbsInt,Modes).
group_memos([],Key0,Vars0,ASubs0,AbsInt,Modes):-
	lub_and_assert_memo(Key0,Vars0,ASubs0,AbsInt,Modes).

lub_and_assert_memo(Key,Vars,ASubs,AbsInt,Modes):-
	do_compute_lub(AbsInt,ASubs,ASub),
	assert_memo_(Key,Vars,ASub,AbsInt,Modes).

assert_memo(Key,Vars,ASub,AbsInt,Modes):-
	point_info_format(Modes,AbsInt,ASub,Vars,Info),
	assert_point_info(Key,Vars,AbsInt,Info).

sort_list_subs([Subst_uns|Substs_uns],AbsInt,[Subst|Substs]):- !,
	abs_sort(AbsInt,Subst_uns,Subst),
	sort_list_subs(Substs_uns,AbsInt,Substs).
sort_list_subs([],_AbsInt,[]):-!.

%% Prepare info to be printed

prepare_call_info(Output,AbsInt,Vars,Call,Call_s,CallInfo):-
	abs_sort(AbsInt,Call,Call_s),
	call_info_format(Output,AbsInt,Call_s,Vars,CallInfo).

prepare_succ_info(Output,AbsInt,Vars,Call_s,Succ,SuccInfo,CompInfo):-
	abs_sort(AbsInt,Succ,Succ_s),
	join_if_needed(AbsInt,Call_s,Succ_s,Vars,Succ_ok),
	succ_info_format(Output,AbsInt,Succ_ok,Vars,SuccInfo,CompInfo).

prepare_point_info(Output,AbsInt,Vars,Call,CallInfo):-
	abs_sort(AbsInt,Call,Call_s),
	point_info_format(Output,AbsInt,Call_s,Vars,CallInfo).

%% prepare_call_list_info([Call|Calls],AbsInt,Output,Vars,[Call0|CallInfo]):-
%% 	prepare_call_info(Output,AbsInt,Vars,Call,_,Call0),
%% 	prepare_call_list_info(Calls,AbsInt,Output,Vars,CallInfo).
%% prepare_call_list_info([],_AbsInt,_Output,_Vars,[]).

prepare_succ_list_info([Succ|Succs],AbsInt,O,Vars,Call_s,SuccInfo,CompInfo):-
	prepare_succ_info(O,AbsInt,Vars,Call_s,Succ,Succ0,Comp0),
	accumulate(Succ0,SuccInfo0,SuccInfo),
	accumulate(Comp0,CompInfo0,CompInfo),
	prepare_succ_list_info(Succs,AbsInt,O,Vars,Call_s,SuccInfo0,CompInfo0).
prepare_succ_list_info([],_AbsInt,_Output,_Vars,_Call_s,[],[]).

accumulate([],SuccInfo0,SuccInfo):- !, SuccInfo=SuccInfo0.
accumulate(Succ,SuccInfo,[Succ|SuccInfo]).

call_info_format(Output,AbsInt,ASub,Gv,OutASub):-
	info_format(Output,AbsInt,ASub,Gv,OutASub,_), !.
call_info_format(_Output,_AbsInt,_ASub,_Gv,[]).

succ_info_format(Output,AbsInt,ASub,Gv,Succ,Comp):-
	info_format(Output,AbsInt,ASub,Gv,Succ,Comp), !.
succ_info_format(_Output,_AbsInt,_ASub,_Gv,[],[fails]).

point_info_format(Output,AbsInt,ASub,Gv,Succ):-
	info_format(Output,AbsInt,ASub,Gv,Succ0,Comp), !,
	append(Succ0,Comp,Succ).
point_info_format(_Output,_AbsInt,_ASub,_Gv,[fails]).

info_format(cl,AbsInt,ASub,Gv,OutASub,Comp):-
	asub_to_out(AbsInt,ASub,Gv,OutASub,Comp).
info_format(pl,AbsInt,ASub,Gv,OutASub,Comp):-
	output_interface(AbsInt,ASub,Gv,OutASub,Comp).

%% Recorda info to be printed for completes
%% There may be more than one for each Key
%% Call is a list of properties
%% Succs is a list of lists of properties
%% Comp is a list of properties

assert_pred_info(Goal,Call,Succs,Comp):-
	curr_file(_,M),
	assertion_body(Goal,[],Call,Succs,Comp,[],Body),
	add_assertion_read(Goal,M,true,pred,Body,no,no,0,0).

%% Recorda info to be printed for memo_table
%% There may be more than one for each Key
%% Info is a list of properties

assert_point_info(Key,Vars,AbsInt,Info):-
	free_vars_in_asub(AbsInt,Vars,Info,FVars),
	assertz_fact(point_info(Key,AbsInt,Vars,FVars,Info)).

% -------------------------------------------------------------------------

%% temporary asserts to delay type simplification for optimizing times

:- data tmp_point_info/4,
	tmp_complete_info/5.

assert_complete_info_(AbsInt,cl,Key,Goal,Call,Succ):-
	knows_of(regtypes,AbsInt), !,
	assertz_fact(tmp_complete_info(Key,AbsInt,Goal,Call,Succ)).
assert_complete_info_(AbsInt,Modes,Key,Goal,Call,Succ):-
	assert_complete_info(AbsInt,Modes,Key,Goal,Call,Succ).

assert_memo_(Key,Vars,ASub,AbsInt,cl):-
	knows_of(regtypes,AbsInt), !,
	assertz_fact(tmp_point_info(Key,AbsInt,Vars,ASub)).
assert_memo_(Key,Vars,ASub,AbsInt,Modes):-
	assert_memo(Key,Vars,ASub,AbsInt,Modes).

tmp_info_to_complete_info(AbsInt,Modes):-
	retract_fact(tmp_complete_info(Key,AbsInt,Goal,Call,Succ)),
	assert_complete_info(AbsInt,Modes,Key,Goal,Call,Succ),
	fail.
tmp_info_to_complete_info(AbsInt,Modes):-
	retract_fact(tmp_point_info(Key,AbsInt,Vars0,ASub)),
	sort(Vars0,Vars),
	assert_memo(Key,Vars,ASub,AbsInt,Modes),
	fail.
tmp_info_to_complete_info(_AbsInt,_Modes).

% -------------------------------------------------------------------------

:- if(defined(has_ciaopp_extra)).
prepare_infer_output(An):-
        is_ualb_complexity_analysis(An, Lower_An, Upper_An),
        !,
	current_fact(inferred(Lower_An, Goal, AbsLb)),
	current_fact(inferred(Upper_An, Goal, AbsUb)),
	asub_to_out(An,Goal,[AbsLb,AbsUb],Call,Succ,Comp),
	assert_pred_info(Goal,Call,[Succ],[Comp]),
	fail.
:- endif.
prepare_infer_output(An):-
	current_fact(inferred(An, Goal, Abs)),
	asub_to_out(An,Goal,Abs,Call,Succ,Comp),
	assert_pred_info(Goal,Call,[Succ],[Comp]),
	fail.
prepare_infer_output(_An).

% -------------------------------------------------------------------------

