:- module(unfold,
	[unfold/10,
	 unf_int/11
	],[]).

%:- use_package(.(nomem_usage)).
:- use_package(.(nounfold_stats)).
:- use_package(.(no_debug)).

:- use_package(assertions).

:- doc(title,"A Partial Evaluator Integrated with Abstract Interpretation").

:- doc(author, "Germ@'{a}n Puebla").
:- doc(author, "Elvira Albert").

:- doc(module," This module contains the implementation of local
     control for partial evaluation to be used in conjunction with
     PLAI.").

:- doc(bug,"1. does not seem to work if the program contains negation
      as failure (and possibly, meta-calls in general).").

:- doc(bug,"2. for exported predicates, if no clause remains after 
	specialization, a clause with 'fail' in its body should be added.").

:- doc(bug,"3. The unfolding rule @tt{df_tree_hom_emb} cannot
   choose now any value for the flag @tt{comp_rule} different from
   @tt{leftmost}. This is currently hardwired in the code. Although,
   in the long term, the menu should disable those values which are
   not applicable. In the case of @tt{hom_emb_anc}, the computation
   rule was fixed to leftmost since the beginning.  (Elvira Albert)").

:- use_module(spec(unfold_local), [select_atom/9]).
:- use_module(spec(sp_clauses), 
	[ add_all_clauses/4,
	  collect_orig_clauses/2
	]).
:- use_module(spec(unfold_builtins), 
	[can_be_evaluated/1,
	 has_cuts/2]).
:- use_module(spec(homeo_emb), [homeomorphic_embedded/2]).
:- use_module(spec(abs_exec), [abs_exec/4]).
:- use_module(spec(unfold_operations), 
	[replicate_atoms/4,
	 is_embedded/3,
	 filter_pops/2]).
:- use_module(spec(unfold_df_operations), 
	[decide_arith_simp/2,
	 form_one_rule_with_susp/4]).
:- use_module(spec(useless_clauses), 
	[ decide_remove_useless_pre/6,
	  decide_remove_useless_post/6,
          check_not_useless_post/5
	]).
:- use_module(spec(mem_usage), 
	[readjust_max_mem_usage/0, update_mem_usage/0]).
:- use_module(spec(unfold_times), 
	[global_time_ellapsed/3,
	 increment_unfold_time/1,
	 increment_local_control_time/1
	]).
:- use_module(spec(spec_iterate), [minimal_unif/3]).
:- use_module(spec(unfold_df_hom_emb_as)).
:- use_module(spec(unfold_df_hom_emb_as_orig)).
:- use_module(spec(unfold_df_tree_hom_emb)).
:- use_module(spec(unfold_df_hom_emb)).
:- use_module(spec(unfold_decompile)).
:- use_module(spec(spec_multiple), 
	[first_components/2,
	 second_components/2
	]).
:- use_module(spec(spec_support), 
	[
	    non_static/1
	]).
:- use_module(spec(ch_trees), [add_ch_tree/2]).
:- use_module(spec(debug_write_atoms)).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(plai/transform), [transform_clauses/5]).
:- use_module(ciaopp(plai/domains),   [abs_sort/3]).
:- use_module(ciaopp(p_unit), [ new_predicate/3, type_of_goal/2]).
:- use_module(ciaopp(p_unit/program_keys), [rewrite_source_all_clauses/2]).
%% 
:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(vndict), [create_pretty_dict/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(library(write), [write/1]).
:- use_module(library(lists), [member/2, append/3, length/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(engine(hiord_rt), ['$meta_call'/1]).

unfold(SelRule,Unfold,Sg,Sv,Proj,AbsInt,Id,NF,A,LC_Time):-
	decide_write_goal(Sg),
	pp_statistics(runtime,[GT,_]),
	functor(Sg,F,A),
	new_predicate(F,A,NF),
	readjust_max_mem_usage,
	unf_int(Unfold,SelRule,Sg,Sv,Proj,AbsInt,Id,F,A,UnfClauses0,_ChTree),
	pp_statistics(runtime,[_,T_u]),
	(current_pp_flag(verbosity,very_high) -> 
	    message(inform, ['{unfolded in ', ~~(T_u), ' msec.}'])
	;
	    true
	),
	increment_unfold_time(T_u),
       	decide_remove_useless_post(UnfClauses0,AbsInt,Sg,Sv,Proj,UnfClauses),
	add_all_clauses(UnfClauses,NF,A,NewClauses),
	decide_write_clause(NewClauses),
	create_dicts_and_recs(NewClauses,Dicts,Recs),
	rewrite_source_all_clauses(NewClauses,NClauses),
	transform_clauses(NClauses,Dicts,Recs,notarjan,AbsInt),
	pp_statistics(runtime,[GT1,_]),
	global_time_ellapsed(GT1,GT,LC_Time),
	increment_local_control_time(LC_Time),
	message(inform, ['{local control ',~~(LC_Time), ' msec.}']).

decide_write_goal(Sg):-
	debug_write('GOAL'),
	debug_write_atom_nl(Sg).

decide_write_clause(NewClauses):-
	debug_write_nl('CLAUSES'),
	write_all_clauses(NewClauses).

write_all_clauses([]).
write_all_clauses([clause(H,B)|NewClauses]):-
	debug_write_atom(H),
	debug_write_nl(' :- '),
	write_body(B), 
	debug_write_nl('.'), 
	write_all_clauses(NewClauses).

write_body((A,B)):-!,
	debug_write_atom(A), debug_write_nl(','),
	write_body(B).
write_body(A):-
	debug_write_atom(A), debug_write_nl('.').


        

unf_int(df_tree_hom_emb,SelRule,Sg,Sv,Proj,AbsInt,Id,_F,_A,UnfClauses0,ChTree):-!,
	perform_unfolding_depth_tree(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses0,ChTree).

unf_int(df_hom_emb,SelRule,Sg,Sv,Proj,AbsInt,Id,_F,_A,UnfClauses0,ChTree):-!,
	perform_unfolding_depth_hom_emb(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses0,ChTree).

unf_int(df_hom_emb_as,SelRule,Sg,Sv,Proj,AbsInt,Id,_F,_A,UnfClauses0,ChTree):-!,
	perform_unfolding_depth(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses0,ChTree).

unf_int(df_hom_emb_as_orig,SelRule,Sg,Sv,Proj,AbsInt,Id,_F,_A,UnfClauses0,ChTree):-!,
	perform_unfolding_depth_orig(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses0,ChTree).

unf_int(decompile,SelRule,Sg,Sv,Proj,AbsInt,Id,_F,_A,UnfClauses0,ChTree):-!,
	perform_unfolding_decompile(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses0,ChTree).

unf_int(Unfold,SelRule,Sg,Sv,Proj,AbsInt,Id,F,A,UnfClauses0,ChTree):-
	collect_definition(Unfold,F,A,Sg,Clauses_Paths),
	first_components(Clauses_Paths,Clauses),
	second_components(Clauses_Paths,ClauseIds),
	initial_chtree(ClauseIds,Chtree_i),
	decide_remove_useless_pre(Clauses,AbsInt,Sg,Sv,Proj,Clauses0),
	perform_unfolding(Unfold,SelRule,AbsInt,Sg,Sv,Proj,Clauses0,UnfClauses0,Chtree_i,Chtree_f),
	debug('CHTREE'),debug(Chtree_f),
	return_or_assert_chtree(Chtree_f,Id,ChTree).

collect_definition(orig,F,A,_Sg,Clauses):-!,
	functor(Temp,F,A),
	collect_orig_clauses(Temp,Clauses).
collect_definition(_Unfold,_F,_A,Sg,Clauses):-
	collect_orig_clauses(Sg,Clauses).

perform_unfolding(Local,SelRule,AbsInt,Sg,Sv,Proj,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	perform_unfolding_(Local,SelRule,AbsInt,Sg,Sv,Proj,Clauses,UnfClauses,Chtree_i,Chtree_tmp),
	close_chtree(Chtree_tmp),
	diff_to_reg(Chtree_tmp,Chtree_f).	

perform_unfolding_(orig,_SelRule,_,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_i):-
	UnfClauses = Clauses.
perform_unfolding_(inst,_SelRule,_,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_i):-
	UnfClauses = Clauses.
perform_unfolding_(det,SelRule,AbsInt,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	unfold_while_deterministic(SelRule,Clauses,1,AbsInt,UnfClauses,Chtree_i,Chtree_f).
perform_unfolding_(det_la,SelRule,AbsInt,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	current_pp_flag(unf_depth,K),
	unfold_while_deterministic(SelRule,Clauses,K,AbsInt,UnfClauses,Chtree_i,Chtree_f).
perform_unfolding_(depth,SelRule,AbsInt,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	current_pp_flag(unf_depth,K),
	unfold_depthk(SelRule,Clauses,AbsInt,UnfClauses,K,Chtree_i,Chtree_f).
perform_unfolding_(first_sol,SelRule,AbsInt,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	unfold_first_sol(SelRule,Clauses,AbsInt,UnfClauses,Chtree_i,Chtree_f).
perform_unfolding_(first_sol_d,SelRule,AbsInt,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	current_pp_flag(unf_depth,K),
	unfold_first_sol_or_depth(SelRule,Clauses,AbsInt,UnfClauses,K,Chtree_i,Chtree_f).
perform_unfolding_(all_sol,SelRule,AbsInt,_,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	unfold_all_sol(SelRule,Clauses,AbsInt,UnfClauses,Chtree_i,Chtree_f).
perform_unfolding_(hom_emb,SelRule,AbsInt,Sg,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	copy_term(Sg,NSg),
	replicate_atoms(Clauses,[NSg],[],NAs),
	unfold_hom_emb(SelRule,Clauses,NAs,AbsInt,UnfClauses,Chtree_i,Chtree_f).
perform_unfolding_(hom_emb_anc,SelRule,AbsInt,Sg,_,_,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	copy_term(Sg,NSg),
	initial_ancestors(Clauses,NSg,AClauses),
	(current_pp_flag(min_crit,none) ->
	    unfold_hom_emb_ancestors_no_path(SelRule,AClauses,AbsInt,AUnfClauses),
	    Chtree_f = Chtree_i
	;
	    unfold_hom_emb_ancestors(SelRule,AClauses,AbsInt,AUnfClauses,Chtree_i,Chtree_f)
	),
	remove_ancestors(AUnfClauses,UnfClauses).
perform_unfolding_(hom_emb_as,SelRule,AbsInt,Sg,_Sv,_Proj,Clauses,UnfClauses,Chtree_i,Chtree_f):-
	copy_term(Sg,NSg),
	replicate_atoms(Clauses,[NSg],[],NAs),
	unfold_hom_emb_local_as(SelRule,Clauses,NAs,AbsInt,UnfClauses,Chtree_i,Chtree_f).

perform_unfolding_depth(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses,ChTree):-
	copy_term((Sg,Proj),(Sg_C,Proj_C_u)),
	varset(Sg_C,Sv_C),
	abs_sort(AbsInt,Proj_C_u,Proj_C),
	findall((UnfClause,Ch_Path),
	    (depth_first_emb_local_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path),
	     check_not_useless_post(UnfClause,AbsInt,Sg_C,Sv_C,Proj_C)),
	     UnfClauses_Chtree),
	first_components(UnfClauses_Chtree,UnfClauses),
	second_components(UnfClauses_Chtree,Chtree),
	return_or_assert_chtree(Chtree,Id,ChTree).
perform_unfolding_depth_orig(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses,ChTree):-
	copy_term((Sg,Proj),(Sg_C,Proj_C_u)),
	varset(Sg_C,Sv_C),
	abs_sort(AbsInt,Proj_C_u,Proj_C),
	findall((UnfClause,Ch_Path),
	    (depth_first_emb_local_orig_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path),
	     check_not_useless_post(UnfClause,AbsInt,Sg_C,Sv_C,Proj_C)),
	     UnfClauses_Chtree),
	first_components(UnfClauses_Chtree,UnfClauses),
	second_components(UnfClauses_Chtree,Chtree),
	return_or_assert_chtree(Chtree,Id,ChTree).
perform_unfolding_decompile(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses,ChTree):-
	copy_term((Sg,Proj),(Sg_C,Proj_C_u)),
	varset(Sg_C,Sv_C),
	abs_sort(AbsInt,Proj_C_u,Proj_C),
	findall((UnfClause,Ch_Path),
	    (depth_first_decompile(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path),
	     check_not_useless_post(UnfClause,AbsInt,Sg_C,Sv_C,Proj_C)),
	     UnfClauses_Chtree),
	first_components(UnfClauses_Chtree,UnfClauses),
	second_components(UnfClauses_Chtree,Chtree),
	return_or_assert_chtree(Chtree,Id,ChTree).
perform_unfolding_depth_tree(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses,ChTree):-
	copy_term((Sg,Proj),(Sg_C,Proj_C_u)),
	varset(Sg_C,Sv_C),
	abs_sort(AbsInt,Proj_C_u,Proj_C),
	findall((UnfClause,Ch_Path),
	    (depth_first_emb_tree_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path),
             check_not_useless_post(UnfClause,AbsInt,Sg_C,Sv_C,Proj_C)),
	     UnfClauses_Chtree),
	first_components(UnfClauses_Chtree,UnfClauses),
	second_components(UnfClauses_Chtree,Chtree),
	return_or_assert_chtree(Chtree,Id,ChTree).
perform_unfolding_depth_hom_emb(SelRule,AbsInt,Sg,Sv,Proj,Id,UnfClauses,ChTree):-
	copy_term((Sg,Proj),(Sg_C,Proj_C_u)),
	varset(Sg_C,Sv_C),
	abs_sort(AbsInt,Proj_C_u,Proj_C),
	findall((UnfClause,Ch_Path),
	    (depth_first_emb_hom_emb_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path),
             check_not_useless_post(UnfClause,AbsInt,Sg_C,Sv_C,Proj_C)),
	     UnfClauses_Chtree),
	first_components(UnfClauses_Chtree,UnfClauses),
	second_components(UnfClauses_Chtree,Chtree),
	return_or_assert_chtree(Chtree,Id,ChTree).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%               DETERMISTIC UNFOLDING               %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- doc(unfold_while_deterministic/9,"Implements an unfolding rule
     which expands derivations while they are deterministic and stops
     them otherwise.").

unfold_while_deterministic(_SelRule,[],_,_AbsInt,[],[],[]).
unfold_while_deterministic(SelRule,[clause(Sg,[])|Clauses],K,AbsInt,[clause(Sg,[])|NCls],[Path-[]|Paths],[Path-[]|Chtree_tmp]):-!,
	unfold_while_deterministic(SelRule,Clauses,K,AbsInt,NCls,Paths,Chtree_tmp).
unfold_while_deterministic(SelRule,[clause(Sg,Body)|Clauses],K,AbsInt,Result,[Path|Paths],Chtree_f):-
	(unfold_deterministically_in_k_steps(SelRule,K,[clause(Sg,Body)],AbsInt,UnfClauses,[Path],NPath) ->
	    debug(yes),
	    (UnfClauses == [] ->
	        unfold_while_deterministic(SelRule,Clauses,K,AbsInt,Result,Paths,Chtree_tmp),
		append(NPath,Chtree_tmp,Chtree_f)
	    ; 
		UnfClauses = [clause(Sg,OtherBody)],
		append(NPath,Paths,Chtree_tmp),
		unfold_while_deterministic(SelRule,[clause(Sg,OtherBody)|Clauses],K,AbsInt,Result,Chtree_tmp,Chtree_f)
	    )
	;
	    debug(no),
	    Result = [clause(Sg,Body)|NClauses],
	    Chtree_f = [Path|Chtree_tmp],
	    unfold_while_deterministic(SelRule,Clauses,K,AbsInt,NClauses,Paths,Chtree_tmp)).
	

is_deterministic([]).
is_deterministic([residual(_)]):-!,fail.
is_deterministic([_]).

:- doc(unfold_deterministically_in_k_steps/5,"Implements an
unfolding rule which expands derivations while they are deterministic
and their length is less than @tt{k}.").

unfold_deterministically_in_k_steps(SelRule,K,Clauses,AbsInt,UnfClauses,Chtree_i,Chtree_f):-
	K > 0,
	unfold_all_clauses_one_step(SelRule,Clauses,AbsInt,TmpClauses,Chtree_i,Chtree_tmp),!,
	(is_deterministic(TmpClauses) ->
	    UnfClauses = TmpClauses,
	    Chtree_f = Chtree_tmp
	;
	    K1 is K - 1,
	    unfold_deterministically_in_k_steps(SelRule,K1,TmpClauses,AbsInt,UnfClauses,Chtree_tmp,Chtree_f)
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%              FIRST SOLUTION UNFOLDING             %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unfold_first_sol(_SelRule,[],_AbsInt,[],[],[]):-!.
unfold_first_sol(SelRule,Clauses,AbsInt,UnfClauses,Chtree_i,Chtree_f):-
	(there_is_solution_or_residual(Clauses) ->
	    peel_residual(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_one_step(SelRule,Clauses,AbsInt,UnfClauses1Step,Chtree_i,Chtree_tmp),
	    unfold_first_sol(SelRule,UnfClauses1Step,AbsInt,UnfClauses,Chtree_tmp,Chtree_f)).


unfold_first_sol_or_depth(_SelRule,[],_AbsInt,[],_,[],[]):-!.
unfold_first_sol_or_depth(_SelRule,Clauses,_AbsInt,UnfClauses,0,Chtree,Chtree):-!,
	peel_residual(Clauses,UnfClauses).
unfold_first_sol_or_depth(SelRule,Clauses,AbsInt,UnfClauses,K,Chtree_i,Chtree_f):-
	(there_is_solution_or_residual(Clauses) ->
	    peel_residual(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_one_step(SelRule,Clauses,AbsInt,UnfClauses1Step,Chtree_i,Chtree_tmp),
	    K1 is K - 1,
	    unfold_first_sol_or_depth(SelRule,UnfClauses1Step,AbsInt,UnfClauses,K1,Chtree_tmp,Chtree_f)).
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%              ALL SOLUTIONS UNFOLDING              %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unfold_all_sol(_SelRule,[],_AbsInt,[],[],[]):-!.
unfold_all_sol(SelRule,Clauses,AbsInt,UnfClauses,Chtree_i,Chtree_f):-
	(all_solutions_or_residual(Clauses) ->
	    peel_residual(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_one_step(SelRule,Clauses,AbsInt,UnfClauses1Step,Chtree_i,Chtree_tmp),
	    unfold_all_sol(SelRule,UnfClauses1Step,AbsInt,UnfClauses,Chtree_tmp,Chtree_f)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%                 DEPTH-K UNFOLDING                 %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unfold_depthk(_SelRule,[],_AbsInt,[],_,[],[]):-!.
unfold_depthk(_SelRule,Clauses,_AbsInt,UnfClauses,1,Chtree,Chtree):-!,
	peel_residual(Clauses,UnfClauses).
unfold_depthk(SelRule,Clauses,AbsInt,UnfClauses,K,Chtree_i,Chtree_f):-
	(all_solutions_or_residual(Clauses) ->
	    peel_residual(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_one_step(SelRule,Clauses,AbsInt,UnfClauses1Step,Chtree_i,Chtree_tmp),
	    K1 is K-1,
	    unfold_depthk(SelRule,UnfClauses1Step,AbsInt,UnfClauses,K1,Chtree_tmp,Chtree_f)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%          COMMON CODE TO THE ABOVE STRATEGIES      %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


unfold_all_clauses_one_step(_SelRule,[],_AbsInt,[],[],[]).
unfold_all_clauses_one_step(SelRule,[Cl|Clauses],AbsInt,Result,[P|Ps],Chtree):-
	unfold_one_step(SelRule,Cl,AbsInt,Result,MoreClauses,P,Chtree,MoreChtree),
	unfold_all_clauses_one_step(SelRule,Clauses,AbsInt,MoreClauses,Ps,MoreChtree).

unfold_one_step(_SelRule,residual(Cl),_AbsInt,NCls,Cont,P-[],Cht,Cht_cont):-!,
	NCls = [residual(Cl)|Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step(_SelRule,fact(Cl),_AbsInt,NCls,Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(Cl)|Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step(SelRule,clause(Sg,Body),AbsInt,NCls,Cont,P-X,Cht,Cht_cont):-
	(Body == [] ->
	    NCls = [fact(clause(Sg,Body))|Cont],
	    X = [],
	    Cht = [P-X|Cht_cont]
	;   
	    select_atom(SelRule,Sg,none,Susp,Body,NewBody,[],_Emb,Lit),
            (NewBody=[] ->
         	NCls = [residual(clause(Sg,Susp))|Cont], 
		X = [],
		Cht = [P-X|Cht_cont]
            ;
		NewBody = [L|R],
		decide_arith_simp(L,LS),
		NewBody1 = [LS|R],
		copy_term(LS,L1),
		(unfold_literal_if_possible(L1,AbsInt,UnfClauses,Clids) ->
		    debug(yes),
		    (UnfClauses == [] ->
		        NCls = Cont,
			Cht = Cht_cont
		    ;
			copy_paths(Clids,Lit,P-X,NPaths),
			append(NPaths,Cht_cont,Cht),
			form_rules_with_susp(UnfClauses,Susp,clause(Sg,NewBody1),NCls,Cont)
		    )
		;
		    debug(no),
		    append(Susp,NewBody1,SBody),
		    NCls = [residual(clause(Sg,SBody))|Cont],
		    X = [],
		    Cht = [P-X|Cht_cont]
		)
	    )
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%     NAIVE UNFOLDING WITH EMBEDDING        %%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- doc(unfold_hom_emb(SelRule,Clauses,Atoms,AbsInt,UnfClauses),"This
    predicate implements an unfolding rule which stops a derivation when
    the selected atom subsumes a previously selected one according to the
    embedding ordering. An efficient implementation using ancestor stacks
    is done in predicate @tt{unfold_hom_emb_local_as}").

unfold_hom_emb(_SelRule,[],_,_AbsInt,[],[],[]):-!.
unfold_hom_emb(SelRule,Clauses,Atoms,AbsInt,UnfClauses,Chtree_i,Chtree_f):-
	(all_solutions_or_residual(Clauses) ->
	    peel_residual(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_with_atoms(SelRule,Clauses,Atoms,AbsInt,UnfClauses1Step,NewAtoms,Chtree_i,Chtree_tmp),
	    unfold_hom_emb(SelRule,UnfClauses1Step,NewAtoms,AbsInt,UnfClauses,Chtree_tmp,Chtree_f)).


unfold_all_clauses_with_atoms(_SelRule,[],[],_AbsInt,[],[],[],[]).
unfold_all_clauses_with_atoms(SelRule,[Cl|Clauses],[A|As],AbsInt,NClauses,NAtoms,[P|Ps],Chtree):-
	unfold_one_step_with_atoms(SelRule,Cl,A,AbsInt,NClauses,MoreClauses,NAtoms,MoreAtoms,P,Chtree,MoreChtree),
	unfold_all_clauses_with_atoms(SelRule,Clauses,As,AbsInt,MoreClauses,MoreAtoms,Ps,MoreChtree).

unfold_one_step_with_atoms(_SelRule,residual(Cl),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [residual(Cl)|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms(_SelRule,fact(Cl),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(Cl)|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms(_SelRule,clause(Sg,[]),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(clause(Sg,[]))|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms(SelRule,clause(Sg,Body),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-
	select_atom(SelRule,Sg,none,Susp,Body,NewBody,A,_Emb,_Lit),
	NewBody = [Lit|_],
	functor(Lit,F,Arity),
	functor(Atom,F,Arity),
 	member(Atom,A),
	debug(hom_emb),
 	homeomorphic_embedded(Atom,Lit),!,
	debug(embedded),
	append(Susp,NewBody,SBody),
	NCls = [residual(clause(Sg,SBody))|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].

unfold_one_step_with_atoms(SelRule,clause(Sg,Body),A,AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-X,Cht,Cht_cont):-
	select_atom(SelRule,Sg,none,Susp,Body,NewBody,A,_Emb,Lit),
	(NewBody = [] ->
	      NCls = [residual(clause(Sg,Susp))|Cl_Cont],
	      NAs = [A|As_Cont],
	      X = [],
	      Cht = [P-X|Cht_cont]
	  ;
	    NewBody = [L|R],
	    decide_arith_simp(L,LS),
	    NewBody1 = [LS|R],
	    copy_term(LS,L1),
	    (unfold_literal_if_possible(L1,AbsInt,UnfClauses,Clids) ->
	     debug(yes),
	     (UnfClauses == [] ->
	         NCls = Cl_Cont,
		 NAs = As_Cont,
		 Cht = Cht_cont
	     ; 
		 copy_paths(Clids,Lit,P-X,NPaths),
		 append(NPaths,Cht_cont,Cht),
		 form_rules_with_susp(UnfClauses,Susp,clause(Sg,NewBody1),NCls,Cl_Cont),
		 (UnfClauses = [clause(_,[])] ->
		     NA = A
		 ;
		     copy_term(L1,NL1),
		     NA = [NL1|A]
		 ),
		 replicate_atoms(UnfClauses,NA,As_Cont,NAs)
	     )
	    ;
		debug(no),
		append(Susp,NewBody1,SBody),
		NCls = [residual(clause(Sg,SBody))|Cl_Cont],
		NAs = [A|As_Cont],
		X = [],
		Cht = [P-X|Cht_cont]
	    )
	).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%     NAIVE UNFOLDING WITH EMBEDDING AND ANCESTORS       %%% 
%%%            only leftmost computation rules             %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unfold_hom_emb_ancestors(_SelRule,[],_AbsInt,[],[],[]):-!.
unfold_hom_emb_ancestors(SelRule,Clauses,AbsInt,UnfClauses,Chtree_i,Chtree_f):-
	(all_solutions_or_residual(Clauses) ->
	    peel_residual_A(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_with_atoms_A(SelRule,Clauses,AbsInt,UnfClauses1Step,Chtree_i,Chtree_tmp),
	    unfold_hom_emb_ancestors(SelRule,UnfClauses1Step,AbsInt,UnfClauses,Chtree_tmp,Chtree_f)).

% GP added to avoid wasting memory in computing paths
unfold_hom_emb_ancestors_no_path(_SelRule,[],_AbsInt,[]):-!.
unfold_hom_emb_ancestors_no_path(SelRule,Clauses,AbsInt,UnfClauses):-
	(all_solutions_or_residual(Clauses) ->
	    peel_residual_A(Clauses,UnfClauses)
	;
	    unfold_all_clauses_with_atoms_A_no_path(SelRule,Clauses,AbsInt,UnfClauses1Step),
	    unfold_hom_emb_ancestors_no_path(SelRule,UnfClauses1Step,AbsInt,UnfClauses)).


unfold_all_clauses_with_atoms_A(_SelRule,[],_AbsInt,[],[],[]).
unfold_all_clauses_with_atoms_A(SelRule,[Cl|Clauses],AbsInt,NClauses,[P|Ps],Chtree):-
	unfold_one_step_with_atoms_A(SelRule,Cl,AbsInt,NClauses,MoreClauses,P,Chtree,MoreChtree),
	unfold_all_clauses_with_atoms_A(SelRule,Clauses,AbsInt,MoreClauses,Ps,MoreChtree).

unfold_all_clauses_with_atoms_A_no_path(_SelRule,[],_AbsInt,[]).
unfold_all_clauses_with_atoms_A_no_path(SelRule,[Cl|Clauses],AbsInt,NClauses):-
	unfold_one_step_with_atoms_A_no_path(SelRule,Cl,AbsInt,NClauses,MoreClauses),
	unfold_all_clauses_with_atoms_A_no_path(SelRule,Clauses,AbsInt,MoreClauses).

unfold_one_step_with_atoms_A(_SelRule,residual(Cl),_AbsInt,NCls,Cl_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [residual(Cl)|Cl_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms_A(_SelRule,fact(Cl),_AbsInt,NCls,Cl_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(Cl)|Cl_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms_A(_SelRule,clause(Sg,[]),_AbsInt,NCls,Cl_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(clause(Sg,[]))|Cl_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms_A(_SelRule,clause(Sg,Body),_AbsInt,NCls,Cl_Cont,P-[],Cht,Cht_cont):-
	Body = [(Lit,A)|_],
	functor(Lit,F,Arity),
	functor(Atom,F,Arity),
 	member(Atom,A),
	debug(hom_emb),
 	\+ \+(homeomorphic_embedded(Atom,Lit)),!,
	debug(embedded),
	NCls = [residual(clause(Sg,Body))|Cl_Cont],
	Cht = [P-[]|Cht_cont].

unfold_one_step_with_atoms_A(SelRule,clause(Sg,Body),AbsInt,NCls,Cl_Cont,P-X,Cht,Cht_cont):-
	select_atom(SelRule,Sg,none,Susp,Body,NewBody,_A,_Emb,Lit),
	(NewBody = [] ->
	      NCls = [residual(clause(Sg,Susp))|Cl_Cont],
	      X = [],
	      Cht = [P-X|Cht_cont]
	;
	      NewBody = [(L,_)|_],
  	      copy_term(L,L1),
	      copy_term(L,L2),
	      (unfold_literal_if_possible(L1,AbsInt,UnfClauses,Clids) ->
	          debug(yes),
	          (UnfClauses == [] ->
		     NCls = Cl_Cont,
		     Cht = Cht_cont
		  ; 
		     copy_paths(Clids,Lit,P-X,NPaths),
		     append(NPaths,Cht_cont,Cht),
		     form_rules_A(UnfClauses,clause(Sg,Body),L2,NewClauses),
		     append(NewClauses,Cl_Cont,NCls)
		  )
	      ;
		  debug(no),
		  NCls = [residual(clause(Sg,Body))|Cl_Cont],
		  X = [],
		  Cht = [P-X|Cht_cont]
	      )
	).

unfold_one_step_with_atoms_A_no_path(_SelRule,residual(Cl),_AbsInt,NCls,Cl_Cont):-!,
	NCls = [residual(Cl)|Cl_Cont].
unfold_one_step_with_atoms_A_no_path(_SelRule,fact(Cl),_AbsInt,NCls,Cl_Cont):-!,
	NCls = [fact(Cl)|Cl_Cont].
unfold_one_step_with_atoms_A_no_path(_SelRule,clause(Sg,[]),_AbsInt,NCls,Cl_Cont):-!,
	NCls = [fact(clause(Sg,[]))|Cl_Cont].
unfold_one_step_with_atoms_A_no_path(_SelRule,clause(Sg,Body),_AbsInt,NCls,Cl_Cont):-
	Body = [(Lit,A)|_],
	functor(Lit,F,Arity),
	functor(Atom,F,Arity),
 	member(Atom,A),
	debug(hom_emb),
 	\+ \+(homeomorphic_embedded(Atom,Lit)),!,
	debug(embedded),
	NCls = [residual(clause(Sg,Body))|Cl_Cont].

unfold_one_step_with_atoms_A_no_path(SelRule,clause(Sg,Body),AbsInt,NCls,Cl_Cont):-
	select_atom(SelRule,Sg,none,Susp,Body,NewBody,_A,_Emb,_Lit),
	(NewBody = [] ->
	      NCls = [residual(clause(Sg,Susp))|Cl_Cont],
	      X = []
	;
	      NewBody = [(L,_)|_],
  	      copy_term(L,L1),
	      copy_term(L,L2),
	      (unfold_literal_if_possible(L1,AbsInt,UnfClauses,_Clids) ->
	          debug(yes),
	          (UnfClauses == [] ->
		     NCls = Cl_Cont
		  ; 
%% 		     copy_paths(Clids,Lit,P-X,NPaths),
%% 		     append(NPaths,Cht_cont,Cht),
		     form_rules_A(UnfClauses,clause(Sg,Body),L2,NewClauses),
		     append(NewClauses,Cl_Cont,NCls)
		  )
	      ;
		  debug(no),
		  NCls = [residual(clause(Sg,Body))|Cl_Cont],
		  X = []
	      )
	).


form_rules_A([],_,_,[]).
form_rules_A([C2|Clauses],C,Atom,[C3|RClauses]):-
	copy_term(C,C1),
	form_one_rule_A(C1,C2,Atom,C3),
	form_rules_A(Clauses,C,Atom,RClauses).


form_one_rule_A(clause(Sg,[(L,L1)|R]),clause(L,Body), Atom, clause(Sg,NBody)):-
	update_ancestors(Body,(Atom,L1),ABody),
	append(ABody,R,NBody).

update_ancestors([],_L,[]).
update_ancestors([B|R],(L,A),[(B,[L1|A])|Rlist]):-
	copy_term(L,L1),
%	fresh_stack(A,A1),
	update_ancestors(R,(L,A),Rlist).

%% fresh_stack([],[]).
%% fresh_stack([L|R],[L1|R1]):-
%% 	copy_term(L,L1),
%% 	fresh_stack(R,R1).

initial_ancestors([],_L,[]).
initial_ancestors([clause(Sg,B)|R],L,[clause(Sg,NB)|Rlist]):-
	update_ancestors(B,(L,[]),NB),
	initial_ancestors(R,L,Rlist).

remove_ancestors([],[]).
remove_ancestors([clause(Sg,B)|R],[clause(Sg,NB)|Rlist]):-
	delete_ancestors(B,NB),
	remove_ancestors(R,Rlist).

delete_ancestors([],[]).
delete_ancestors([(B,_)|R],[B|R1]):-
	delete_ancestors(R,R1).

peel_residual_A([],[]).
peel_residual_A([residual(Cl)|Clauses],[NCl|NClauses]):-!,
	Cl = clause(Head,Body),
	NCl = clause(Head,Body),
	peel_residual_A(Clauses,NClauses).
peel_residual_A([fact(Cl)|Clauses],[NCl|NClauses]):-!,
	Cl = clause(Head,Body),
	NCl = clause(Head,Body),
	peel_residual_A(Clauses,NClauses).
peel_residual_A([Cl|Clauses],[NCl|NClauses]):-
	Cl = clause(Head,Body),
	NCl = clause(Head,Body),
	peel_residual_A(Clauses,NClauses).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%       EFFICIENT   UNFOLDING WITH EMBEDDING BASED ON STACKS       %% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


unfold_hom_emb_local_as(_SelRule,[],_,_AbsInt,[],[],[]):-!.
unfold_hom_emb_local_as(SelRule,Clauses,Atoms,AbsInt,UnfClauses,Chtree_i,Chtree_f):-
	(all_solutions_or_residual(Clauses) ->
%	(there_is_solution_or_residual(Clauses) ->
	    peel_residual_l(Clauses,UnfClauses),
	    Chtree_i = Chtree_f
	;
	    unfold_all_clauses_with_atoms_local(SelRule,Clauses,Atoms,AbsInt,UnfClauses1Step,NewAtoms,Chtree_i,Chtree_tmp),
	    unfold_hom_emb_local_as(SelRule,UnfClauses1Step,NewAtoms,AbsInt,UnfClauses,Chtree_tmp,Chtree_f)).

unfold_all_clauses_with_atoms_local(_SelRule,[],[],_AbsInt,[],[],[],[]).
unfold_all_clauses_with_atoms_local(SelRule,[Cl|Clauses],[A|As],AbsInt,NClauses,NAtoms,[P|Ps],Chtree):-
	unfold_one_step_with_atoms_local(SelRule,Cl,A,AbsInt,NClauses,MoreClauses,NAtoms,MoreAtoms,P,Chtree,MoreChtree),
	unfold_all_clauses_with_atoms_local(SelRule,Clauses,As,AbsInt,MoreClauses,MoreAtoms,Ps,MoreChtree).

unfold_one_step_with_atoms_local(_SelRule,residual(Cl),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [residual(Cl)|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms_local(_SelRule,fact(Cl),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(Cl)|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms_local(_SelRule,clause(Sg,[]),A,_AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-[],Cht,Cht_cont):-!,
	NCls = [fact(clause(Sg,[]))|Cl_Cont],
	NAs = [A|As_Cont],
	Cht = [P-[]|Cht_cont].
unfold_one_step_with_atoms_local(SelRule,clause(Sg,['$pop$'|R]),A,AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-X,Cht,Cht_cont):-!,
	A = [_|A1s],
	unfold_one_step_with_atoms_local(SelRule,clause(Sg,R),A1s,AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-X,Cht,Cht_cont).
unfold_one_step_with_atoms_local(SelRule,clause(Sg,Body),A,AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-X,Cht,Cht_cont):-
	select_atom(SelRule,Sg,none,Susp,Body,NewBody,A,Flag,Lit),  
	(NewBody = [] ->	  
	     NCls = [residual(clause(Sg,Susp))|Cl_Cont],
	     NAs = [A|As_Cont],
	     X = [],
	     Cht = [P-X|Cht_cont]
	;
	    NewBody = [L|R],    
	    (L='$pop$' -> 
	        append([L|Susp],R,SBody),
	        unfold_one_step_with_atoms_local(SelRule,clause(Sg,SBody),A,AbsInt,NCls,Cl_Cont,NAs,As_Cont,P-X,Cht,Cht_cont)
	    ;
		debug(embed),
		(is_embedded(Flag,L,A) ->
	            debug('EMBEDDED'),
		    append(Susp,NewBody,SBody),
		    NCls = [residual(clause(Sg,SBody))|Cl_Cont],
		    NAs = [A|As_Cont]
		;
		    decide_arith_simp(L,LS),
		    NewBody1 = [LS|R],
		    copy_term(LS,L1),
		    (unfold_literal_if_possible(L1,AbsInt,UnfClauses,Clids) ->
		        debug(yes),
			(UnfClauses == [] ->
			     NCls = Cl_Cont,
			     NAs = As_Cont,
			     Cht = Cht_cont
			; 
			    copy_paths(Clids,Lit,P-X,NPaths),
			    append(NPaths,Cht_cont,Cht),
			    (UnfClauses = [clause(_,[])] ->
			        NA = A,
				form_rules_with_susp(UnfClauses,Susp,clause(Sg,NewBody1),NCls,Cl_Cont)
			    ;
				copy_term(L1,NL1),
				NA = [NL1|A],
				form_rules_with_susp(UnfClauses,Susp,clause(Sg,[L,'$pop$'|R]),NCls,Cl_Cont)
			    ),
			    replicate_atoms(UnfClauses,NA,As_Cont,NAs)
			)
		    ;
			append(Susp,NewBody1,SBody),
			NCls = [residual(clause(Sg,SBody))|Cl_Cont],
			NAs = [A|As_Cont],
			X = [],
			Cht = [P-X|Cht_cont]
		    )
		)
	    )
	).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%     COMMON CODE TO ALL ABOVE STRATEGIES   %%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

form_rules_with_susp([],_Susp,_,Cont,Cont).
form_rules_with_susp([C2|Clauses],Susp,C,[C3|RClauses],Cont):-
	copy_term((C,Susp),(C1,Susp1)),
	form_one_rule_with_susp(C1,Susp1,C2,C3),
	form_rules_with_susp(Clauses,Susp,C,RClauses,Cont).

%% form_rules([],_,Cont,Cont).
%% form_rules([C2|Clauses],C,[C3|RClauses],Cont):-
%% 	copy_term(C,C1),
%% 	form_one_rule(C1,C2,C3),
%% 	form_rules(Clauses,C,RClauses,Cont).
%% 
%% 
%% form_one_rule(clause(Sg,[L|R]),clause(L,Body), clause(Sg,NBody)):-
%% 	append(Body,R,NBody).
%% 
%% form_one_rule_tree(clause(Sg,[(L,_)|R]),clause(L,Body), clause(Sg,NBody)):-
%% 	append(Body,R,NBody).

:- doc(unfold_literal_if_possible(L,AbsInt,UnfClauses,Clids),
  "Unfolding steps are now always performed via this
  predicate. Requests to unfold a call to a predicate not defined in
  the current module and for which @pred{can_be_evaluated(L)} fails,
  finish with failure.").


unfold_literal_if_possible(L,AbsInt,_UnfClauses,_Clids):-
	update_mem_usage,
	current_pp_flag(abs_spec_defs,on),
	functor(L,F,A),
	abs_exec(AbsInt,F/A,_Sense,_Cond),
	write('missed opportunity?'),
	fail.
unfold_literal_if_possible(\+(L),_AbsInt,UnfClauses,Clids):-
%	type_of_goal(builtin(_TypeGoal),L),
	can_be_evaluated(L),!,
	findall(sol,'$meta_call'(L),Solutions),
	length(Solutions,Evals),
	inc_unfold_evals(Evals),
	(Solutions = [] ->
	    UnfClauses = [clause(\+(L),[])],
	    Clids = [no]
	;
	    UnfClauses = [], 
	    Clids = []).
unfold_literal_if_possible(L,_AbsInt,UnfClauses,Clids):-
	type_of_goal(imported,L),!, 
	(can_be_evaluated(L) ->
	    copy_term(L,L_call),	    
	    findall(clause(L,[]),'$meta_call'(L),UnfClauses),
	    length(UnfClauses,Evals),
	    inc_unfold_evals(Evals),
	    external_clids(UnfClauses,L_call,Clids),
	    debug('UNFOLDED builtin '),
	    debug(L)
	;
	    debug('NOT unfolded builtin '),
	    debug(L),
	    fail
	).
unfold_literal_if_possible(L,_AbsInt,_UnfClauses,_Clids):-
	non_static(L),!,
	fail.
unfold_literal_if_possible(L,_AbsInt,_UnfClauses,_Clids):-
	functor(L,F,A),
	has_cuts(F,A),!,
	fail.
unfold_literal_if_possible(L,_AbsInt,UnfClauses,Clids):-
	can_be_evaluated(L),!,
	copy_term(L,L_call),	    
	findall(clause(L,[]),'$meta_call'(L),UnfClauses),
	length(UnfClauses,Evals),
	inc_unfold_evals(Evals),
	external_clids(UnfClauses,L_call,Clids),
	debug('EXECUTED local predicate '),
	debug(L).
unfold_literal_if_possible(L,_AbsInt,UnfClauses,Clids):-
	collect_orig_clauses(L,UnfClauses_paths),
	first_components(UnfClauses_paths,UnfClauses),
	second_components(UnfClauses_paths,Clids).






create_dicts_and_recs([],[],[]).
create_dicts_and_recs([Cl|Clauses],[D|Ds],[r|Rs]):-
	create_pretty_dict(Cl,D),
	create_dicts_and_recs(Clauses,Ds,Rs).

there_is_solution_or_residual([fact(_)|_]):-!.
there_is_solution_or_residual([residual(_)|_]):-!.
%there_is_solution_or_residual([clause(_,[])|_]):-!.
there_is_solution_or_residual([_|Clauses]):-
	there_is_solution_or_residual(Clauses).
	
%% there_is_solution([clause(_,true)|_]):-!.
%% there_is_solution([_|Clauses]):-
%% 	there_is_solution(Clauses).
%% 	
%% all_residual([]).
%% all_residual([residual(_)|Clauses]):-
%% 	all_residual(Clauses).

all_solutions_or_residual([]).
all_solutions_or_residual([residual(_)|Clauses]):-
	all_solutions_or_residual(Clauses).
all_solutions_or_residual([fact(_)|Clauses]):-
	all_solutions_or_residual(Clauses).
all_solutions_or_residual([clause(_,[])|Clauses]):-
	all_solutions_or_residual(Clauses).

peel_residual([],[]).
peel_residual([residual(Cl)|Clauses],[Cl|NClauses]):-!,
	peel_residual(Clauses,NClauses).
peel_residual([fact(Cl)|Clauses],[Cl|NClauses]):-!,
	peel_residual(Clauses,NClauses).
peel_residual([Cl|Clauses],[Cl|NClauses]):-
	peel_residual(Clauses,NClauses).

peel_residual_l([],[]).
peel_residual_l([residual(Cl)|Clauses],[NCl|NClauses]):-!,
	Cl = clause(Head,Body),
	NCl = clause(Head,NBody),
	filter_pops(Body,NBody),
	peel_residual_l(Clauses,NClauses).
peel_residual_l([fact(Cl)|Clauses],[NCl|NClauses]):-!,
	Cl = clause(Head,Body),
	NCl = clause(Head,NBody),
	filter_pops(Body,NBody),
	peel_residual_l(Clauses,NClauses).
peel_residual_l([Cl|Clauses],[NCl|NClauses]):-
	Cl = clause(Head,Body),
	NCl = clause(Head,NBody),
	filter_pops(Body,NBody),
	peel_residual_l(Clauses,NClauses).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%             CODE SPECIFIC FOR CHTREES             %%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- pred initial_chtree(+,-) #"Given a list of clause ids, it generates
an initial chtree having incomplete characteristics paths (expressed
thru difference lists). These paths will be completed with the
corresponding unfoldings".

initial_chtree([],[]).
initial_chtree([Id|Ids],[[(1:Id)|X]-X|T1]):-
	initial_chtree(Ids,T1).


:- pred close_chtree(Tree) #"Closes a chtree having incomplete
characteristic paths".

close_chtree([]).
close_chtree([_-[]|T]):-
	close_chtree(T).



:- pred diff_to_reg(+,-) #"Transforms difference lists into regular lists".

diff_to_reg([],[]).
diff_to_reg([P-[]|R1],[P|R2]):-
%	dlist(L,DL,[]),
	diff_to_reg(R1,R2).


:- pred copy_paths(+Ids,+Lit,+Path,-) #"Given a list of @var{Ids}
representing new unfolded clauses, and a literal representing the
choosen goal used in the unfolding, it replicates the input @var{Path}
returning a list of characteristic paths".

copy_paths([],_,_,[]).
copy_paths([Id|Ids],Lit,Path-Y,[NPath-X|T]):-
	copy_term(Path,Path1),
	append(Path1,[(Lit:Id)|X],NPath),!,
	copy_paths(Ids,Lit,Path-Y,T).


:- pred external_clids(+,?,-) # "Given a list of external calls, it returns a
list of their corresponding IDs".

external_clids([],_,[]).
external_clids([clause(L,[])|T],L_call,[Id|R]):-
	minimal_unif(L_call,L,Bindings),
	Id = (L_call,Bindings),
	external_clids(T,L_call,R).


:- pred return_or_assert_chtree(+Paths,+,-) 
	# "Characteristic tree @var{Paths} is asserted or returned
	  only if needed (i.e., when ppflag @tt{min_crit} is different
	  from @tt{none}). PCPE does not assert any chtree".

return_or_assert_chtree(Paths,Id,ChTree) :-
	(current_pp_flag(min_crit,none) ->
	    true
	;
	    (current_pp_flag(fixpoint,poly_spec) ->
	        ChTree = Paths
	    ;
		add_ch_tree(Id,Paths))
	).

