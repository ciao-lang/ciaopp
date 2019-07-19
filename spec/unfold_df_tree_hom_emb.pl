:- module(_,[depth_first_emb_tree_0/7],[assertions, datafacts]).

:- doc(title,"Depth-first Unfolding with embedding based on
proof trees").
:- doc(author, "Elvira Albert").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains an implementation of local
     control for partial evaluation to be used in conjunction with
     PLAI.").

:- doc(bug,"1 jump_builtins does not work here because atoms are
tuples now with the parent enclosed").

:- use_package(spec(no_debug)).

:- use_module(spec(sp_clauses),        [collect_one_orig_clause/3]).
:- use_module(spec(unfold_operations), [is_embedded_tree/4]).
:- use_module(spec(unfold_df_operations), 
        [can_continue/5,
         fact_or_residual/1,
	 peel_fact_or_residual_tree/2,
	 unfold_literal_one_step/5,
	 form_one_rule_tree_with_susp/4,
         pack_abs_info/6,
         add_parents/3,
	 decide_arith_simp/2
        ]).

:- use_module(spec(unfold_local), [select_atom/9]).
:- use_module(spec(useless_clauses), [check_not_useless_pre/5]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(library(lists)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  DEPTH-FIRST UNFOLDING WITH EMBEDDING BASED ON PROOF TREES  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred depth_first_emb_tree_0(+SelRule,+AbsInt,+Sg,+Sv,Proj,-UnfClause,-Ch_Path).

depth_first_emb_tree_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path):-
	copy_term((Sg,Sv,Proj),(NSg,NSv,NProj)),
	collect_one_orig_clause(Sg,Clause,Counter),
	check_not_useless_pre(Clause,AbsInt,Sg,Sv,Proj),
	Clause = clause(Sg,_),
	current_pp_flag(abs_spec_defs,Abs_Spec),
	pack_abs_info(Abs_Spec,AbsInt,NSg,NSv,NProj,Info),
	add_parents(Clause,1,NClause),
	(current_pp_flag(min_crit,none) ->
	    depth_first_emb_tree_no_path(SelRule,NClause,[(1,NSg,0)],Info,UnfClause),
	    Ch_Path = null
	;
	    Ch_Path = [(1:Counter)| Ch_Path_Res ],
	    depth_first_emb_tree(SelRule,NClause,[(1,NSg,0)],Info,UnfClause,Ch_Path_Res)).


depth_first_emb_tree_no_path(SelRule,Clause,Atoms,Info,UnfClause):-
	(fact_or_residual(Clause) ->
	    peel_fact_or_residual_tree(Clause,UnfClause)
	;
	    unfold_one_step_one_clause_tree(Clause,SelRule,Atoms,Info,UnfClause1Step,NewAtoms,_Id,_Lit),
	    depth_first_emb_tree_no_path(SelRule,UnfClause1Step,NewAtoms,Info,UnfClause)).

depth_first_emb_tree(SelRule,Clause,Atoms,Info,UnfClause,Ch_Path):-
	(fact_or_residual(Clause) ->
	    peel_fact_or_residual_tree(Clause,UnfClause),
	    Ch_Path = []
	;
	    unfold_one_step_one_clause_tree(Clause,SelRule,Atoms,Info,UnfClause1Step,NewAtoms,Id,Lit),
            (Id = no -> 
	        Ch_Path = Ch_Path_Rest
	     ;
		Ch_Path = [(Lit:Id) | Ch_Path_Rest]
	    ),
	    depth_first_emb_tree(SelRule,UnfClause1Step,NewAtoms,Info,UnfClause,Ch_Path_Rest)).

unfold_one_step_one_clause_tree(residual(Cl),_SelRule,A,_Info,Clause,A,no,_Lit):-!,
	Clause = residual(Cl).
unfold_one_step_one_clause_tree(fact(Cl),_SelRule,A,_Info,Clause,A,no,_Lit):-!,
	Clause = fact(Cl).
unfold_one_step_one_clause_tree(clause(Sg,[]),_SelRule,A,_Info,Clause,A,no,_Lit):-!,
	Clause = fact(clause(Sg,[])).
unfold_one_step_one_clause_tree(clause(Sg,['$pop$'|R]),SelRule,[_|A1s],Info,Clause,NewAtoms,Id,Lit):-!,
	unfold_one_step_one_clause_tree(clause(Sg,R),SelRule,A1s,Info,Clause,NewAtoms,Id,Lit).
unfold_one_step_one_clause_tree(clause(Sg,Body),SelRule,A,Info,NCl,NAs,Id,Lit):-
	select_atom(leftmost,Sg,Info,Susp,Body,NewBody,A,Flag,Lit0),  
        NewBody = [(L,Parent)|R],    
	(L='$pop$' -> 
	    A = [_|NA],
	    append(Susp,R,SBody),
	    unfold_one_step_one_clause_tree(clause(Sg,SBody),SelRule,NA,Info,NCl,NAs,Id,Lit)
	   ;
	    Lit = Lit0,
	    decide_arith_simp(L,L1),
	    NewBody1 = [L1|R],
	    unfold_literal_or_residualize_tree(clause(Sg,NewBody1),Susp,R,L1,Parent,A,Info,Lit,NCl,NAs,Flag,Id)
	).

unfold_literal_or_residualize_tree(clause(Sg,NewBody),Susp,_R,L,Parent,A,_Info,_Lit,NCl,NAs,Flag,Id):-
	debug(embed),
	is_embedded_tree(Flag,L,Parent,A),!,
	debug('EMBEDDED'),
	append(Susp,NewBody,SBody),
	NCl = residual(clause(Sg,SBody)),
	NAs = A,
	Id = no.
	

unfold_literal_or_residualize_tree(clause(Sg,NewBody),Susp,_R,L,Parent,A,Info,Lit,NCl,NAs,_Flag,Id):-
	copy_term(L,L2),
	can_continue(Info,L,Lit,Sg,Case),!,
	unfold_literal_one_step(Case,L,Info,UnfClause,Id),
	parent_id(New_Parent),
	add_parents(UnfClause,New_Parent,UnfClauseP),
	(UnfClauseP = clause(H,[]) ->
	    form_one_rule_tree_with_susp(clause(Sg,NewBody),Susp,clause(H,[]),NCl),
	    NAs = A
	;
	    NAs = [(New_Parent,L2,Parent)|A],
	    form_one_rule_tree_with_susp(clause(Sg,NewBody),Susp,UnfClauseP,NCl)
	).
	
		 
unfold_literal_or_residualize_tree(clause(Sg,NewBody),Susp,_R,_L,_Parent,A,_Info,_Lit,NCl,NAs,_Flag,Id):-
	append(Susp,NewBody,SBody),
        NCl = residual(clause(Sg,SBody)),
	NAs = A,
	debug('NOT unfolded builtin '),
	(SBody = [L|_] ->
	    debug(L)
	;
	    true),
	Id = no.


:- data par_id/1.

par_id(1).

parent_id(Id):-
	retract_fact(par_id(Id0)),
	Id is Id0+1,
	asserta_fact(par_id(Id)).
