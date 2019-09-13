:- module(_,[depth_first_emb_local_0/7],[assertions, isomodes]).

:- use_package(spec(no_debug)).

:- doc(title,"Depth-first Unfolding with embedding based on ancestor stacks").

:- doc(author, "Elvira Albert").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains an implementation of local
     control for partial evaluation to be used in conjunction with
     PLAI.").

:- use_package(.(no_debug)).

:- use_module(spec(sp_clauses),        [collect_one_orig_clause/3]).
:- use_module(spec(unfold_operations), [is_embedded/4]).
:- use_module(spec(unfold_df_operations), 
	[can_continue/5,
	 fact_or_residual/1,
	 peel_fact_or_residual/2,
	 unfold_literal_one_step/5,
	 form_one_rule_with_susp/4,
	 pack_abs_info/6,
	 decide_arith_simp/2,
	 peel_call/4
	]).
:- use_module(spec(unfold_local),         [select_atom/9]).
:- use_module(spec(useless_clauses),      [check_not_useless_pre/5]).
:- use_module(spec(generalize_emb_atoms), [decide_lc_filter/2]).
:- use_module(ciaopp(preprocess_flags),   [current_pp_flag/2]).
:- use_module(library(lists)).
:- use_module(library(write)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    DEPTH-FIRST UNFOLDING WITH EMBEDDING BASED ON STACKS  %%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred depth_first_emb_local_0(+SelRule,+AbsInt,+Sg,+Sv,+Proj,-UnfClause,-Ch_Path).

depth_first_emb_local_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path):-
	copy_term((Sg,Sv,Proj),(NSg,NSv,NProj)),
	collect_one_orig_clause(Sg,Clause,Counter),
	check_not_useless_pre(Clause,AbsInt,Sg,Sv,Proj),
	Clause = clause(Sg,_),
	current_pp_flag(abs_spec_defs,Abs_Spec),
	current_pp_flag(hom_emb_nums,FNums),
	pack_abs_info(Abs_Spec,AbsInt,NSg,NSv,NProj,Info),
	decide_lc_filter(NSg,NSg_fr),
	(current_pp_flag(min_crit,none) ->
	    depth_first_emb_local_no_path(SelRule,Clause,[NSg_fr],Info,FNums,UnfClause),
	    Ch_Path = null
	;
	    Ch_Path = [(1:Counter)| Ch_Path_Res ],
	    depth_first_emb_local(SelRule,Clause,[NSg_fr],Info,FNums,
	                          UnfClause,Ch_Path_Res)).

depth_first_emb_local_no_path(SelRule,Clause,Atoms,Info,FNums,UnfClause):-
 	(current_pp_flag(verbosity,very_high) ->
	    write('.')
	;
	    true),
	(fact_or_residual(Clause) ->
	    peel_fact_or_residual(Clause,UnfClause)
	;
	    unfold_one_step_one_clause(Clause,SelRule,Atoms,Info,FNums,UnfClause1Step,NewAtoms,_Id,_Lit),
	    depth_first_emb_local_no_path(SelRule,UnfClause1Step,NewAtoms,Info,FNums,UnfClause)
	).

depth_first_emb_local(SelRule,Clause,Atoms,Info,FNums,UnfClause,Ch_Path):-
	(fact_or_residual(Clause) ->
	    peel_fact_or_residual(Clause,UnfClause),
	    Ch_Path = []
	;
	    unfold_one_step_one_clause(Clause,SelRule,Atoms,Info,FNums,UnfClause1Step,NewAtoms,Id,Lit),
            (Id = no -> 
	        Ch_Path = Ch_Path_Rest
	     ;
		Ch_Path = [(Lit:Id) | Ch_Path_Rest]
	    ),
	    depth_first_emb_local(SelRule,UnfClause1Step,NewAtoms,Info,FNums,UnfClause,Ch_Path_Rest)
	).

unfold_one_step_one_clause(residual(Cl),_SelRule,A,_Info,_FNums,Clause,A,no,_Lit):-!,
	Clause = residual(Cl).
unfold_one_step_one_clause(fact(Cl),_SR,A,_Info,_FNums,Clause,A,no,_Lit):-
	!,
	Clause = fact(Cl).
unfold_one_step_one_clause(clause(Sg,[]),_SR,A,_Info,_FNums,Clause,A,no,_Lit):-
	!,
	Clause = fact(clause(Sg,[])).
unfold_one_step_one_clause(clause(Sg,['$pop$'|R]),SelRule,[_|A1s],Info,FNums,Clause,NewAtoms,Id,Lit):-!,
	unfold_one_step_one_clause(clause(Sg,R),SelRule,A1s,Info,FNums,Clause,NewAtoms,Id,Lit).
unfold_one_step_one_clause(clause(Sg,Body),SelRule,A,Info,FNums,NCl,NAs,Id,Lit):-
	select_atom(SelRule,Sg,Info,Susp,Body,NewBody,A,Flag,Lit0),   
	(NewBody=[] ->
	    NCl = residual(clause(Sg,Susp)),
	    NAs = A,
	    Id = no
	;
	    NewBody = [L|R],    
	    (L='$pop$' -> 
	        A = [_|NA],
		combine_susp(Susp,R,NR),
		unfold_one_step_one_clause(clause(Sg,NR),SelRule,NA,Info,FNums,NCl,NAs,Id,Lit)
	    ;
		Lit = Lit0,
		decide_arith_simp(L,L1),
		NewBody1 = [L1|R],
		mark_susp(Susp,MSusp),
		unfold_literal_or_residualize(clause(Sg,NewBody1),MSusp,R,L1,A,Info,FNums,Lit,NCl,NAs,Flag,Id)
	    )
	).

% GP comment out or uncomment first or second version for tests
combine_susp(Susp,R,NR):- append(Susp,R,NR).
%% combine_susp([],R,R).
%% combine_susp([L|Ls],R,['$susp'(L)|NR]):-
%% 	combine_susp(Ls,R,NR).

% GP comment out or uncomment first or second version for tests
mark_susp(Susp,Susp).
%% mark_susp([],[]).
%% mark_susp([L|Ls],['$susp'(L)|NLs]):-
%% 	mark_susp(Ls,NLs).

unfold_literal_or_residualize(clause(Sg,[]),Susp,_R,_L,A,_Info,_FNums,_Lit,NCl,NAs,_Flag,Id):-!,
	NCl = residual(clause(Sg,Susp)),
	NAs = A,
        Id = no.

unfold_literal_or_residualize(clause(Sg,NewBody),Susp,_R,L,A,_Info,FNums,_Lit,NCl,NAs,Flag,Id):-
	debug(embed),
	is_embedded(Flag,FNums,L,A),!,
	debug('EMBEDDED '),
	debug(L),
	append(Susp,NewBody,Body),
	NCl = residual(clause(Sg,Body)),
	NAs = A,
        Id = no.
	
unfold_literal_or_residualize(clause(Sg,NewBody),Susp,R,L,A,Info,_FNums,Lit,NCl,NAs,_Flag,Id):-
	peel_call(L,NewBody,L1,NewBody1), 
	copy_term(L1,L2),
	can_continue(Info,L1,Lit,Sg,Case),!,
%%  	write(' processing '),
%%  	write(L1), nl,
 	debug(processing),
 	debug(L1),
	decide_lc_filter(L2,L2_fr),
	unfold_literal_one_step(Case,L1,Info,UnfClause,Id),
	(UnfClause = clause(H,[]) ->
	    form_one_rule_with_susp(clause(Sg,NewBody1),Susp,clause(H,[]),NCl),
	    NAs = A
	;
%% 	    (is_recursive(L2) ->
	        form_one_rule_with_susp(clause(Sg,[L1,'$pop$'|R]),Susp,UnfClause,NCl),
	        NAs = [L2_fr|A]
%% 	    ;
%% 		form_one_rule_with_susp(clause(Sg,[L1|R]),Susp,UnfClause,NCl),
%% 		NAs = A
%% 	    )
	).
			 
unfold_literal_or_residualize(clause(Sg,NewBody),Susp,_R,_L,A,_Info,_FNums,_Lit,NCl,NAs,_Flag,Id):-
	append(Susp,NewBody,Body),
	NCl = residual(clause(Sg,Body)),
	NAs = A,
	debug('NOT unfolded builtin '),
	(Body = [L|_] ->
	    debug(L)
	;
	    true),
        Id = no.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  END DEPTH-FIRST UNFOLDING WITH EMBEDDING BASED ON STACKS  %%% 
