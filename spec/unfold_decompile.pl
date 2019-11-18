:- module(_, [depth_first_decompile/7], [assertions, isomodes]).

:- use_package(spec(no_debug)).

:- doc(title,"Depth-first Unfolding with embedding based on ancestor stacks").

:- doc(author, "Elvira Albert").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains an implementation of local
     control for partial evaluation to be used in conjunction with
     PLAI.").

:- use_module(spec(sp_clauses), [collect_one_orig_clause/3]).
:- use_module(spec(unfold_df_operations_decompile), 
    [can_continue/5,
     fact_or_residual/1,
     peel_fact_or_residual/2,
     unfold_literal_one_step/3,
     form_one_rule_with_susp/3,
     decide_arith_simp/2,
     peel_call/4
    ]).

:- use_module(spec(unfold_local), [select_atom/9]).
%:- use_module(spec(generalize_emb_atoms), [decide_lc_filter/2]).

:- use_module(library(lists)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    DEPTH-FIRST UNFOLDING WITH EMBEDDING BASED ON STACKS  %%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred depth_first_decompile(+SelRule,+AbsInt,+Sg,+Sv,+Proj,-UnfClause,-Ch_Path).

depth_first_decompile(SelRule,_AbsInt,Sg,_Sv,_Proj,UnfClause,Ch_Path):-
%       write(hola),
%       copy_term((Sg,Sv,Proj),(NSg,NSv,NProj)),
    collect_one_orig_clause(Sg,Clause,_Counter),
%       check_not_useless_pre(Clause,AbsInt,Sg,Sv,Proj),
    Clause = clause(Sg,Body),
    NClause = clause(Sg,Body,[]),
%       current_pp_flag(abs_spec_defs,Abs_Spec),
%       current_pp_flag(hom_emb_nums,FNums),
%%      pack_abs_info(Abs_Spec,AbsInt,NSg,NSv,NProj,Info),
%%      decide_lc_filter(NSg,NSg_fr),
    depth_first_emb_local_no_path(SelRule,NClause,UnfClause),
    Ch_Path = null.

depth_first_emb_local_no_path(SelRule,Clause,UnfClause):-
    (fact_or_residual(Clause) ->
        peel_fact_or_residual(Clause,UnfClause)
    ;
        unfold_one_step_one_clause(Clause,SelRule,UnfClause1Step),
        depth_first_emb_local_no_path(SelRule,UnfClause1Step,UnfClause)
    ).

unfold_one_step_one_clause(residual(Cl),_SelRule,Clause):-!,
    Clause = residual(Cl).
unfold_one_step_one_clause(fact(Cl),_SR,Clause):-
    !,
    Clause = fact(Cl).
unfold_one_step_one_clause(clause(Sg,[],Res),_SR,Clause):-
    !,
    (Res = [] ->
        Clause = fact(clause(Sg,[]))
    ;
        Clause = residual(clause(Sg,Res))
    ).
%% unfold_one_step_one_clause(clause(Sg,['$pop$'|R],Res),SelRule,Clause):-!,
%%      unfold_one_step_one_clause(clause(Sg,R,Res),SelRule,Clause).
unfold_one_step_one_clause(clause(Sg,Body,Res),SelRule,NCl):-
    select_atom(SelRule,Sg,_Info,Susp,Body,NewBody,[],Flag,Lit),   
    append(Res,Susp,NSusp),
    (NewBody=[] ->
        NCl = residual(clause(Sg,NSusp))
    ;
        NewBody = [L|R],    
%%          (L='$pop$' -> 
%% %            A = [_|NA],
%%              unfold_one_step_one_clause(clause(Sg,R,NSusp),SelRule,NCl)
%%          ;
            decide_arith_simp(L,L1),
            NewBody1 = [L1|R],
            unfold_literal_or_residualize(clause(Sg,NewBody1,NSusp),R,L1,Lit,NCl,Flag)
%           )
    ).

unfold_literal_or_residualize(clause(Sg,[],Susp),_R,_L,_Lit,NCl,_Flag):-!,
    NCl = residual(clause(Sg,Susp)).

%% unfold_literal_or_residualize(clause(Sg,NewBody),Susp,_R,L,A,_Info,FNums,_Lit,NCl,NAs,Flag,Id):-
%%      debug(embed),
%%      is_embedded(Flag,FNums,L,A),!,
%%      debug('EMBEDDED '),
%%      debug(L),
%%      append(Susp,NewBody,Body),
%%      NCl = residual(clause(Sg,Body)),
%%      NAs = A,
%%         Id = no.
    
unfold_literal_or_residualize(clause(Sg,NewBody,Susp),R,L,Lit,NCl,_Flag):-
    peel_call(L,NewBody,L1,NewBody1), 
%       copy_term(L1,L2),
    can_continue(none,L1,Lit,Sg,Case),!,
    debug(processing),
    debug(L1),
    unfold_literal_one_step(Case,L1,UnfClause),
    (UnfClause = clause(H,[]) ->
        form_one_rule_with_susp(clause(Sg,NewBody1,Susp),clause(H,[]),NCl)
    ;
%%          (is_recursive(L2) ->
%%              form_one_rule_with_susp(clause(Sg,[L1,'$pop$'|R],Susp),UnfClause,NCl)
%%          ;
            form_one_rule_with_susp(clause(Sg,[L1|R],Susp),UnfClause,NCl)
%           )
    ).
                     
unfold_literal_or_residualize(clause(Sg,NewBody,Susp),_R,_L,_Lit,NCl,_Flag):-
    append(Susp,NewBody,Body),
    NCl = residual(clause(Sg,Body)),
%       NAs = A,
    debug('NOT unfolded builtin '),
    (Body = [L|_] ->
        debug(L)
    ;
        true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  END DEPTH-FIRST UNFOLDING WITH EMBEDDING BASED ON STACKS  %%% 
