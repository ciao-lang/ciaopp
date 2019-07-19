:- module(_,
	[form_one_rule_with_susp/4,
	 can_continue/3,
	 can_continue/5,
	 unfold_literal_one_step/5,
	 fact_or_residual/1,
	 peel_fact_or_residual/2,	 
	 peel_fact_or_residual_tree/2,
	 peel_call/4,
	 form_one_rule_tree_with_susp/4,
	 add_parents/3,
	 pack_abs_info/6,
	 unpack_abs_info/5,
	 decide_arith_simp/2,
	 is_recursive/1
	],[]).

:- use_package(assertions).
:- use_package(.(nounfold_stats)).
:- use_package(spec(no_debug)).

:- doc(title,"Depth-first Operations").

:- doc(module,"Common stuff to different depth-first unfolding rules").

:- doc(author, "Elvira Albert").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(author, "Jos@'{e} F. Morales (improving hiord support)").

%:- use_package(.(nomem_usage)).

:- use_module(spec(modular_spec), [equiv/3]).
:- use_module(spec(abs_exec), [determinable/2]).
:- use_module(spec(spec_iterate), [minimal_unif/3]).
:- use_module(spec(abs_exec_ops), 
	[adapt_info_to_assrt_head/6, abs_exec_regtype_in_clause/8]).

:- use_module(spec(abs_exec_cond), [abs_exec_conj_props/3]).
:- use_module(spec(sp_clauses), [collect_one_orig_clause/3]).

:- use_module(spec(unfold_operations), [filter_pops/2]).
:- use_module(spec(unfold_builtins), [can_be_evaluated/1, has_cuts/2, is_memo/1]).
:- use_module(spec(mem_usage), [update_mem_usage/0]).
:- use_module(spec(spec_support), [non_static/1]).
:- use_module(spec(arith_simplify), [arith_simp/2]).
:- use_module(spec(generalize_emb_atoms), [add_gen_memo_hint/1]).

:- use_module(typeslib(regtype_basic_lattice), [translate_lattice_types/4]).
:- use_module(ciaopp(plai/domains), [call_to_entry/9]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).

:- use_module(ciaopp(p_unit), [type_of_goal/2, native_prop/2]).
:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(engine(internals), [module_concat/3]).
:- use_module(engine(hiord_rt), ['$meta_call'/1]).

:- use_module(library(terms_vars), [varset/2]). 
:- use_module(library(lists), [member/2, append/3, length/2]).
:- use_module(library(sets), [ord_subtract/3]).
:- use_module(library(aggregates)).
:- use_module(library(terms), [copy_args/3]).

form_one_rule_with_susp(clause(Sg,[L|R]),Susp,clause(L,Body), clause(Sg,NBody)):-
	append(Body,R,Tmp),
	append(Susp,Tmp,NBody).

:- pred can_continue(Info,L,Lit,Sg,Case) # "Decides whether literal
     @var{L} can be executed during specialization given @var{Info}
     and @var{Sg}. If it succeeds it provides in @var{Case} a keyword
     indicating the kind of execution which can be performed.".

can_continue(none,L,Lit,_Sg,Case):-!,
	can_continue(L,Lit,Case).
can_continue(r(AbsInt,OldSg,OldSv,OldProj),L,Lit,Sg,Case):-!,
	varset(Sg,Sv),
	varset(L,BodyVars),
	ord_subtract(BodyVars,Sv,Fv),
	call_to_entry(AbsInt,OldSv,OldSg,Sv,Sg,Fv,OldProj,Entry,_),
	(Entry == '$bottom' ->
	    debug('useless clause'),
	    Case = 'basiccontrol:fail'
	;
	    can_continue(L,Lit,Case)
	).
can_continue(e(AbsInt,OldSg,OldSv,OldProj),L,_Lit,Sg,Case):-
	functor(L,F,A),
	functor(NGoal,F,A),
	equiv(NGoal,Cond,Sense),
	varset(Sg,Sv),
	varset(L,BodyVars),
	ord_subtract(BodyVars,Sv,Fv),
	call_to_entry(AbsInt,OldSv,OldSg,Sv,Sg,Fv,OldProj,Entry,_),
	adapt_info_to_assrt_head(AbsInt,L,BodyVars,Entry,NGoal,NewInfo),
	abs_exec_conj_props(Cond,AbsInt,NewInfo),!,
	NGoal = L, 
	Case = Sense,
	debug('abstractly executed ').
%simp_body_list(F/A,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs):-
can_continue(e(AbsInt,OldSg,OldSv,OldProj),L,_Lit,Sg,Case):-
        determinable(AbsInt,types),
	functor(L,F,A),
	translate_lattice_types(F,A,L,NL),
	native_prop(NL,regtype(SPred)),

	varset(Sg,Sv),
	varset(L,BodyVars),
	ord_subtract(BodyVars,Sv,Fv),
	call_to_entry(AbsInt,OldSv,OldSg,Sv,Sg,Fv,OldProj,Entry,_),

	abs_exec_regtype_in_clause(AbsInt,SPred,F,A,L,BodyVars,Entry,Sense),!,

	Case = Sense,
	debug('abstractly executed ').
can_continue(e(_AbsInt,_OldSg,_OldSv,_OldProj),L,Lit,_Sg,Case):-
	can_continue(L,Lit,Case),!.

can_continue(a(AbsInt,OldSg,OldSv,OldProj),L,Lit,Sg,Case):-
	varset(Sg,Sv),
	varset(L,BodyVars),
	ord_subtract(BodyVars,Sv,Fv),
	call_to_entry(AbsInt,OldSv,OldSg,Sv,Sg,Fv,OldProj,Entry,_),
	(Entry == '$bottom' ->
	    debug('useless clause'),
	    Case = 'basiccontrol:fail'
	;
	    ((functor(L,F,A),
	      functor(NGoal,F,A),
	      equiv(NGoal,Cond,Sense),
	      adapt_info_to_assrt_head(AbsInt,L,BodyVars,Entry,NGoal,NewInfo),
	      abs_exec_conj_props(Cond,AbsInt,NewInfo)) ->
	        NGoal = L, 
	        Case = Sense,
	        debug('abstractly executed ')
	    ;
		((determinable(AbsInt,types),
		  functor(L,F,A),
		  translate_lattice_types(F,A,L,NL),
		  native_prop(NL,regtype(SPred)),

%% 		  varset(Sg,Sv),
%% 		  varset(L,BodyVars),
%% 		  ord_subtract(BodyVars,Sv,Fv),
%% 		  call_to_entry(AbsInt,OldSv,OldSg,Sv,Sg,Fv,OldProj,Entry,_),
%% 
		  abs_exec_regtype_in_clause(AbsInt,SPred,F,A,L,BodyVars,Entry,Sense)) ->
		     Case = Sense,
		     debug('abstractly executed ')
		     
		  ;
	          can_continue(L,Lit,Case)
               )
	    )
	).
	
can_continue(!,_Lit,_Case):-!, 
	fail.
can_continue('aggregates:findall'(T,Goal,L),_Lit,Case):-
	nonvar(Goal),
	can_be_evaluated(Goal),
	Case = findall(T,Goal,L).
can_continue('aggregates:setof'(T,Goal,L),_Lit,Case):-
	nonvar(Goal),
	can_be_evaluated(Goal),
	Case = setof(T,Goal,L).
can_continue('aggregates:bagof'(T,Goal,L),_Lit,Case):-
	nonvar(Goal),
	can_be_evaluated(Goal),
	Case = bagof(T,Goal,L).
can_continue(L,_Lit,Case):-
	can_be_evaluated(L),!,
	Case = external.
can_continue(L,_Lit,_Case):-
	type_of_goal(imported,L),!, 
	fail.
can_continue(L,_Lit,_Case):-
	non_static(L),!,
	fail.
can_continue(L,_Lit,_Case):-
	is_memo(L),!,
	debug('MEMO'),
	debug(L),
	add_gen_memo_hint(L),
	fail.
can_continue(L,_Lit,_Case):-
	functor(L,F,A),
	has_cuts(F,A),!,
	fail.
can_continue(_L,1,Case):-!,
	Case = internal.
can_continue(L,_Lit,Case):-
	current_pp_flag(unf_bra_fac,BF),
	(BF > 0 ->
	    BF1 is BF + 1,
	    findnsols(BF1,a,collect_one_orig_clause(L,_UnfClause,_Id),Results),
	    length(Results,Num_Results),
	    (Num_Results > BF ->
	        debug(non_deterministic),
		debug(L),fail
	    ;
		true)
	;
	    true),
	Case = internal.


unfold_literal_one_step(internal,L,_AbsInt,UnfClause,Id):-!,
	update_mem_usage,
	collect_one_orig_clause(L,UnfClause,Id).

% if the execution of the builting does not generate bindings, 
% it is indeed equivalent to a call to predicate true/0.
unfold_literal_one_step(external,L,_AbsInt,UnfClause,Id):-!,
	copy_term(L,L_call),
	'$meta_call'(L),
	inc_unfold_evals(1),
	UnfClause=clause(L,[]),
	debug('UNFOLDED builtin '),
	debug(L),
	minimal_unif(L_call,L,Bindings),
	Id = (L_call,Bindings).
% 	(instance(L_call,L) ->
% 	    Id = 'basiccontrol:true'
% 	;
% 	    Id = L).

unfold_literal_one_step(findall(T,Goal,List),L,_AbsInt,UnfClause,Id):-!,
	findall(T,'$meta_call'(Goal),List),
	UnfClause=clause(L,[]),
	debug('UNFOLDED builtin '),
	debug(L),
        Id = no.
unfold_literal_one_step(setof(T,Goal,List),L,_AbsInt,UnfClause,Id):-!,
	setof(T,'$meta_call'(Goal),List),
	UnfClause=clause(L,[]),
	debug('UNFOLDED builtin '),
	debug(L),
        Id = no.
unfold_literal_one_step(bagof(T,Goal,List),L,_AbsInt,UnfClause,Id):-!,
	bagof(T,'$meta_call'(Goal),List),
	UnfClause=clause(L,[]),
	debug('UNFOLDED builtin '),
	debug(L),
        Id = no.

unfold_literal_one_step(true,L,_AbsInt,UnfClause,Id):-!,
	UnfClause=clause(L,[]),
	debug('ABS EXEC to true '),
	debug(L),
        Id = (L,[]). %'basiccontrol:true'.

unfold_literal_one_step('basiccontrol:fail',L,_AbsInt,_UnfClause,Id):-!,
	debug('ABS EXEC to fail '),
	debug(L),
        Id = no,
	fail.

unfold_literal_one_step(Sense,L,_AbsInt,UnfClause,Id):-
	UnfClause=clause(L,[Sense]),
	debug('ABS EXEC '),
	debug(L),
        Id = (Sense,[]).


fact_or_residual(residual(_)).
fact_or_residual(fact(_)).
fact_or_residual(clause(_,[])).


peel_fact_or_residual(residual(Cl),clause(Head,NewBody)):-!,
	Cl=clause(Head,Body),
	filter_pops(Body,NewBody).
peel_fact_or_residual(fact(Cl),clause(Head,NewBody)):-!,
	Cl=clause(Head,Body),
	filter_pops(Body,NewBody).
peel_fact_or_residual(Cl,clause(Head,NewBody)):-
	Cl=clause(Head,Body),
	filter_pops(Body,NewBody).

peel_fact_or_residual_tree(residual(Cl),clause(Head,NewBody)):-!,
	Cl=clause(Head,Body),
	filter_parents(Body,NewBody).
peel_fact_or_residual_tree(fact(Cl),clause(Head,NewBody)):-!,
	Cl=clause(Head,Body),
	filter_parents(Body,NewBody).
peel_fact_or_residual_tree(Cl,clause(Head,NewBody)):-
	Cl=clause(Head,Body),
	filter_parents(Body,NewBody).

filter_parents([],[]).
%% filter_parents(['$pop$'|Body],NBody):-!,
%% 	filter_parents(Body,NBody).
filter_parents([(L,_Parent)|Body],[L|NBody]):-!,
	filter_parents(Body,NBody).
filter_parents([L|Body],[L|NBody]):-
	filter_parents(Body,NBody).

form_one_rule_tree_with_susp(clause(Sg,[(L,_)|R]),Susp,clause(L,Body), clause(Sg,NBody)):-!,
	append(Susp,Body,Aux),
        append(Aux,R,NBody).
form_one_rule_tree_with_susp(clause(Sg,[L|R]),Susp,clause(L,Body), clause(Sg,NBody)):-
	append(Susp,Body,Aux),
        append(Aux,R,NBody).


add_parents(clause(Head,Body),Parent,clause(Head,NBody)):-
	add_all_parents(Body,Parent,NBody).

add_all_parents([],_,[]).
add_all_parents([A|As],Parent,[(A,Parent)|NAs]):-
	add_all_parents(As,Parent,NAs).


pack_abs_info(off,_AbsInt,_Sg,_Sv,_Proj,Info):-!,
	Info = none.
pack_abs_info(rem,AbsInt,Sg,Sv,Proj,Info):-!,
	Info = r(AbsInt,Sg,Sv,Proj).
pack_abs_info(exec,AbsInt,Sg,Sv,Proj,Info):-!,
	Info = e(AbsInt,Sg,Sv,Proj).
pack_abs_info(all,AbsInt,Sg,Sv,Proj,Info):-
	Info = a(AbsInt,Sg,Sv,Proj).

unpack_abs_info(e(AbsInt,Sg,Sv,Proj),AbsInt,Sg,Sv,Proj):-!.
unpack_abs_info(a(AbsInt,Sg,Sv,Proj),AbsInt,Sg,Sv,Proj).

%%%%%%%%%%%%%%%%%%%%%
decide_arith_simp('myprofiler_rt:is'(Res,Form),L1):-
	current_pp_flag(sim_ari_exp,SIMP),
	member(SIMP,[pre,both]),!,
	arith_simp(Form,Form1),
%% 	debug('ARITH'),
%% 	debug(Form),
%% 	debug(Form1),
	L1 = 'myprofiler_rt:is'(Res,Form1).
decide_arith_simp('arithmetic:is'(Res,Form),L1):-
	current_pp_flag(sim_ari_exp,SIMP),
	member(SIMP,[pre,both]),!,
	arith_simp(Form,Form1),
	debug('ARITH'),
	debug(Form),
	debug(Form1),
	L1 = 'arithmetic:is'(Res,Form1).
decide_arith_simp(L,L).

% TODO: weird and incomplete; merge with mexpand format?
get_pa_goal(X, _) :- var(X), !, fail.
get_pa_goal($(X,_,goal), R) :- !, get_pa_goal(X, R).
get_pa_goal(R, R).

%%%%%%%
% TODO: duplicated
peel_call('hiord_rt:call'(Goal),Body,NGoal,NBody):-
	nonvar(Goal),
	functor(Goal,':',2),
	arg(1,Goal,Module),
	ground(Module),
	arg(2,Goal,Pred),
	nonvar(Pred),!,
	functor(Pred,F,A),
	module_concat(Module,F,Name),
	functor(NGoal,Name,A),
	copy_args(A,Pred,NGoal),
	Body = ['hiord_rt:call'(Goal)|Rest],
	NBody = [NGoal|Rest].
peel_call('hiord_rt:call'(PA0,Args),Body,NGoal,NBody):-
 	nonvar(Args),
	% TODO: fix get_pa_goal/2
	get_pa_goal(PA0, Goal),
 	!,
 	% TODO: merge with mexpand apply (not good arg order)
 	Args =.. [_|NewArgs],
 	Goal =.. [F|GoalArgs],
 	append(GoalArgs, NewArgs, Args2),
 	NGoal =.. [F|Args2],
 	Body = ['hiord_rt:call'(PA0,Args)|Rest],
 	NBody = [NGoal|Rest].
peel_call(Goal,Body,Goal,Body).

is_recursive(L):-
	predkey_from_sg(L,SgKey),
	trans_clause(SgKey,r,_),!.

