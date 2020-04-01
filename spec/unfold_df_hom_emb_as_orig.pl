:- module(_,[depth_first_emb_local_orig_0/7],[assertions, isomodes]).

:- doc(title,"Depth-first Unfolding with embedding based on ancestor stacks").

:- doc(author, "Elvira Albert").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains an implementation of local
     control for partial evaluation to be used in conjunction with
     PLAI.").

:- use_package(spec(no_debug)).

:- use_module(spec(sp_clauses),        [collect_one_orig_clause/3]).
:- use_module(spec(unfold_operations), [is_embedded/3]).
:- use_module(spec(unfold_df_operations), 
    [can_continue/5,
     fact_or_residual/1,
     peel_fact_or_residual/2,
     unfold_literal_one_step/5,
     form_one_rule_with_susp/4,
     pack_abs_info/6
    ]).

:- use_module(spec(unfold_local),       [select_atom/9]).
:- use_module(spec(useless_clauses),    [check_not_useless_pre/5]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

:- use_module(library(lists)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    DEPTH-FIRST UNFOLDING WITH EMBEDDING BASED ON STACKS  %%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred depth_first_emb_local_orig_0(+SelRule,+AbsInt,+Sg,+Sv,+Proj,-UnfClause,-Ch_Path).

depth_first_emb_local_orig_0(SelRule,AbsInt,Sg,Sv,Proj,UnfClause,Ch_Path):-
    copy_term((Sg,Sv,Proj),(NSg,NSv,NProj)),
    collect_one_orig_clause(Sg,Clause,Counter),
    check_not_useless_pre(Clause,AbsInt,Sg,Sv,Proj),
    Clause = clause(Sg,_),
    current_pp_flag(abs_spec_defs,Abs_Spec),
    pack_abs_info(Abs_Spec,AbsInt,NSg,NSv,NProj,Info),
    (current_pp_flag(min_crit,none) ->
        depth_first_emb_local_no_path(SelRule,Clause,[NSg],Info,UnfClause),
        Ch_Path = null
    ;
        Ch_Path = [(1:Counter)| Ch_Path_Res ],
        depth_first_emb_local(SelRule,Clause,[NSg],Info,
                              UnfClause,Ch_Path_Res)).

depth_first_emb_local_no_path(SelRule,Clause,Atoms,Info,UnfClause):-
    pplog(spec_module, ['.']),
    (fact_or_residual(Clause) ->
        peel_fact_or_residual(Clause,UnfClause)
    ;
        unfold_one_step_one_clause(Clause,SelRule,Atoms,Info,UnfClause1Step,NewAtoms,_Id,_Lit),
        depth_first_emb_local_no_path(SelRule,UnfClause1Step,NewAtoms,Info,UnfClause)
    ).

depth_first_emb_local(SelRule,Clause,Atoms,Info,UnfClause,Ch_Path):-
    (fact_or_residual(Clause) ->
        peel_fact_or_residual(Clause,UnfClause),
        Ch_Path = []
    ;
        unfold_one_step_one_clause(Clause,SelRule,Atoms,Info,UnfClause1Step,NewAtoms,Id,Lit),
        (Id = no -> 
            Ch_Path = Ch_Path_Rest
         ;
            Ch_Path = [(Lit:Id) | Ch_Path_Rest]
        ),
        depth_first_emb_local(SelRule,UnfClause1Step,NewAtoms,Info,UnfClause,Ch_Path_Rest)
    ).

unfold_one_step_one_clause(residual(Cl),_SelRule,A,_Info,Clause,A,no,_Lit):-!,
    Clause = residual(Cl).
unfold_one_step_one_clause(fact(Cl),_SelRule,A,_Info,Clause,A,no,_Lit):-!,
    Clause = fact(Cl).
unfold_one_step_one_clause(clause(Sg,[]),_SelRule,A,_Info,Clause,A,no,_Lit):-!,
    Clause = fact(clause(Sg,[])).
unfold_one_step_one_clause(clause(Sg,['$pop$'|R]),SelRule,[_|A1s],Info,Clause,NewAtoms,Id,Lit):-!,
    unfold_one_step_one_clause(clause(Sg,R),SelRule,A1s,Info,Clause,NewAtoms,Id,Lit).
unfold_one_step_one_clause(clause(Sg,Body),SelRule,A,Info,NCl,NAs,Id,Lit):-
    select_atom(SelRule,Sg,Info,Susp,Body,NewBody,A,Flag,Lit0),   
    (NewBody=[] ->
        NCl = residual(clause(Sg,Susp)),
        NAs = A,
        Id = no
    ;
        NewBody = [L|R],    
        (L='$pop$' -> 
            A = [_|NA],
            append(Susp,R,NR),
            unfold_one_step_one_clause(clause(Sg,NR),SelRule,NA,Info,NCl,NAs,Id,Lit)
        ;
            Lit = Lit0,
            NewBody1 = [L|R],
            unfold_literal_or_residualize(clause(Sg,NewBody1),Susp,R,L,A,Info,Lit,NCl,NAs,Flag,Id)
        )
    ).

unfold_literal_or_residualize(clause(Sg,[]),Susp,_R,_L,A,_Info,_Lit,NCl,NAs,_Flag,Id):-!,
    NCl = residual(clause(Sg,Susp)),
    NAs = A,
    Id = no.

unfold_literal_or_residualize(clause(Sg,NewBody),Susp,_R,L,A,_Info,_Lit,NCl,NAs,Flag,Id):-
    debug(embed),
    is_embedded(Flag,L,A),!,
    debug('EMBEDDED'),
    append(Susp,NewBody,Body),
    NCl = residual(clause(Sg,Body)),
    NAs = A,
    Id = no.
    
unfold_literal_or_residualize(clause(Sg,NewBody),Susp,R,L,A,Info,Lit,NCl,NAs,_Flag,Id):-
    copy_term(L,L2),
    can_continue(Info,L,Lit,Sg,Case),!,
    unfold_literal_one_step(Case,L,Info,UnfClause,Id),
    (UnfClause = clause(H,[]) ->
        form_one_rule_with_susp(clause(Sg,NewBody),Susp,clause(H,[]),NCl),
        NAs = A
    ;
%%          (is_recursive(L2) ->
            NAs = [L2|A],
            form_one_rule_with_susp(clause(Sg,[L,'$pop$'|R]),Susp,UnfClause,NCl)
%%          ;
%%              NAs = A,
%%              form_one_rule_with_susp(clause(Sg,[L|R]),Susp,UnfClause,NCl))
    ).
                     
unfold_literal_or_residualize(clause(Sg,NewBody),Susp,_R,_L,A,_Info,_Lit,NCl,NAs,_Flag,Id):-
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
