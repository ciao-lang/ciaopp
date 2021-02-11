:- module(spec,
    [
        show_simplif/1,
        simplify_specialize/6,
        versions/2,
        abs_ex/2,
        versions/2,
        simplify_versions/4,
        erase_all_local_data/0
    ],
    [assertions, datafacts]).

:- doc(bug,"1. warplan_shfr_vers gives problems with plai. Probably
       due to plai...").
:- doc(bug,"2. has to use G from type_of_goal(builtin(fail),G)
       instead of simply use fail. Check others, like true, etc.
       Check with, e.g., plus1_pe with spec (shows fail instead of
       basiccontrol:fail.)").
:- doc(bug,"3. When calling remove_useless_info(AbsInt), the 
       generation of multiple versions goes wrong: it might be
       removing too much! Check with, e.g., plus1_pe with vers,
       which has output empty.").
:- doc(bug,"4. Have to incorporate the reorganization of the and-or
       graph in the presence of meta-predicates. This will probably
       do with the following problem:
       {ERROR (plai_errors): Acc without Complete: 
              mmatrix_parallelized:multiply/3/2/4,15}").
:- doc(bug,"5. Seems to be the same as the one
       above. Specialization of parallelized programs does not work.").

:- use_module(engine(io_basic)).
:- use_module(spec(spec_iterate), 
    [
        init_clause_result/0,
        iterate/7,
        simplify/6,
        body_result/4]).

:- use_module(spec(spec_multiple), 
    [ 
        mult_spec/7,
        publish_pred_name/2,
        reset_mult_spec/0
    ]).

:- use_module(spec(abs_exec_ops), 
    [
        adapt_info_to_assrt_head/6,
        abs_exec_regtype_in_clause/8
    ]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

:- use_module(ciaopp(plai/fixpo_ops), [bottom/1]).
:- use_module(ciaopp(plai/domains), [call_to_entry/10, abs_sort/3, concrete/4]).
:- use_module(ciaopp(plai/plai_db), [complete/7, memo_table/6]).

:- use_module(ciaopp(p_unit), [predicate_names/1]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3, predkey_from_sg/2]).

:- use_module(spec(unfold_builtins), [translate_lattice_types/4]).

:- use_module(library(aggregates)).
:- use_module(library(format)).
:- use_module(library(lists),      [member/2, append/3, length/2]).
:- use_module(library(terms_vars), [varset/2]). 
:- use_module(library(terms),      [copy_args/3]). 
:- use_module(library(write),      [write/1]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(ciaopp(pool),        [there_is_delay/0]).

%%
:- use_module(spec(abs_exec), [dyn_abs_exec/4, determinable/2]).
:- use_module(spec(abs_exec_cond), [cond/4, abs_exec_conj_props/3]).
:- use_module(spec(modular_spec), 
    [generate_abs_execs_from_equivs/0, reset_equivs/0, equiv/3]).
:- use_module(spec(s_simpspec),
    [body2list/2, next_pred/2, next_or_last_key/3, newformat/2]).

:- use_module(ciaopp(infer), [get_memo_lub/5]).

% interface

:- use_module(spec(spec_support), [
    simplify_indep/4,
    simplify_ground/4,
    special_simp_indep/4,
    special_simp_ground/4,
    no_repetitions/5,
    change_call/3,
    do_spec/0,
    set_spec_flag/1,
    add_simplif/3,
    replace/3,
    simp/2,
    non_static/1]).

:- use_module(spec(spec_delay)).
%% :- use_module(spec(unfold_bultins), [peel_call/2]).
:- use_module(ciaopp(p_unit), [prop_to_native/2]).

:- doc(bug,"Types defined but not called dissapear!").


/*             Copyright (C)1993-2001 UPM-CLIP                     */

%-------------------------------------------------------------------%
%                                                                   %
%                     started: October 93                           %
%              programmed: A.German Puebla Sanchez                  %
%                last modified: July 2001                           %
%-------------------------------------------------------------------%

:- data abs_ex/2.

%-------------------------------------------------------------------%
% simplify_specialize(+,+,+,+,-,-)                                  %
% simplify_specialize(Abs,Spec,Prog,Dicts,NewProg,NewDicts)         %
% Produces the simplified and specialized version of program Prog,  %
% with dictionaries Dicts, according to the abstract domain Abs and %
% the flag Spec and writes it in NewProg and NewDicts               %
%-------------------------------------------------------------------%

simplify_specialize(none,_Spec,Prog,Dicts,Prog,Dicts):-!.
simplify_specialize(Abs,Spec,Prog,Dicts,NewProg,NewDicts):-
    pp_statistics(runtime,_),
    cleanup_specialize,
    generate_abs_execs_from_equivs,
    set_spec_flag(Spec),
    simplify_prog(Prog,Dicts,Abs,Nprog,Ndicts), !, %leaves choice_point
    predicate_names(Preds), % TODO: merge below, avoid findall
    filter_out_non_static(Preds,Static_Preds),
    decide_specialize(Spec,Nprog,Ndicts,Static_Preds,Abs,Sp_prog,Sp_Dicts,Sp_Preds),
    iterate(Sp_prog,Sp_Dicts,0,Sp_Preds,Abs,TmpProg,TmpDicts),
    specialize_blocks(Spec,TmpProg,TmpDicts,NTmpProg,NewDicts),
%       decide_perform_unif(NTmpProg0,NewDicts0,NTmpProg,NewDicts),
    newformat(NTmpProg,NewProg),
    erase_all_local_data,
    pp_statistics(runtime,[_,T]),
    pplog(spec_module, ['{transformed by ', ~~(Spec), ' in ', time(T), ' msec.}']).

filter_out_non_static([],[]).
filter_out_non_static([F/A|Preds],Static_Preds):-
    functor(Goal,F,A),
    non_static(Goal),!,
    filter_out_non_static(Preds,Static_Preds).
filter_out_non_static([F/A|Preds],[F/A|Static_Preds]):-
    filter_out_non_static(Preds,Static_Preds).

%% decide_perform_unif(NTmpProg0,NewDicts0,NTmpProg,NewDicts):-
%%      current_pp_flag(exec_unif,off),!,
%%      NTmpProg = NTmpProg0,
%%      NewDicts = NewDicts0.
%% decide_perform_unif(NTmpProg0,NewDicts0,NTmpProg,NewDicts):-
%%      do_perform_unif(NTmpProg0,NewDicts0,NTmpProg,NewDicts).
%% 
%% 
%% do_perform_unif([],[],[],[]).
%% do_perform_unif([directive(Dir):Id|Cs],[D|Ds],[directive(Dir):Id|SCs],[D|NDs]):-
%%         do_perform_unif(Cs,Ds,SCs,NDs).
%% %-------------------------------------------------------------%
%% % This is the unique clause for a fact previously reduced to  %
%% % true, so it is removed, as is no longer needed.             %
%% %-------------------------------------------------------------%
%% do_perform_unif([clause(H,Body):Clid|Cs],[D|Ds],[clause(H,NBody):Clid|SCs],[ND|NDs]):-
%%      do_perform_unif_list(Body,NBody,Flag),
%%      (Flag == newdict ->
%%          sort_dict(D,D0),
%%          remove_duplicated_vars_in_dict(D0,D1),
%%          complete_dict(D1,NBody,D2),
%%          prune_dict(NBody,D2,ND)
%%      ;
%%          ND = D
%%      ),
%%         do_perform_unif(Cs,Ds,SCs,NDs).
%% 
%% do_perform_unif_list([],[],_).
%% do_perform_unif_list([(A = B):noinfo|Body],NBody,Flag):-!,
%%      call(A = B),
%%      Flag = newdict,
%%      do_perform_unif_list(Body,NBody,Flag).
%% do_perform_unif_list([B|Body],[B|NBody],Flag):-
%%      do_perform_unif_list(Body,NBody,Flag).
%% 
%% remove_duplicated_vars_in_dict(dic([],[]),NDict):-!,
%%      NDict = dic([],[]).
%% remove_duplicated_vars_in_dict(dic([V|Vs],[N|Names]),NDict):-
%%      NDict = dic([V|NVs],[N|NNames]),
%%      rem_dup_dict(Vs,V,NVs,Names,NNames).
%% 
%% rem_dup_dict([],_V,[],[],[]).
%% rem_dup_dict([V0|Vs],V,NVs,[_N|Names],NNames):-
%%      V0 == V,!,
%%      rem_dup_dict(Vs,V,NVs,Names,NNames).
%% rem_dup_dict([V0|Vs],_V,NVs,[N|Names],NNames):-
%%      NVs = [V0|MoreVs],
%%      NNames = [N|MoreNames],
%%      rem_dup_dict(Vs,V0,MoreVs,Names,MoreNames).

    
cleanup_specialize:-
    erase_all_local_data,
    retractall_fact(versions(_,_)),
    retractall_fact(spec_multiple:publish_pred_name(_,_)).

:- data versions/2.


erase_all_local_data:-
    retractall_fact(abs_ex(_,_)),
    init_clause_result,
    retractall_fact(iterations(_)),
    retractall_fact(spec_support:simp(_,_)),
    retractall_fact(spec_support:replace(_,_,_)),
    reset_equivs,
    reset_mult_spec.



%-------------------------------------------------------------------%
% simplify_prog(+,+,+,-,-).                                         %
% simplify_prog(Prog,Dicts,Abs,SimpProg,SimpDicts)                  %
%  First step of the simplifying and specializing process. Prog is  %
% simplified based on abstractly executable goals and information   %
% about simplifications in future specialized versions gathered     %
%-------------------------------------------------------------------%
simplify_prog([],[],_,[],[]).

:- data block_cond/2.

%-------------------------------------------------------------%
% We simplify block declarations                              %
%-------------------------------------------------------------%
simplify_prog([directive(block(Specs)):Id|Cs],[D|Ds],Abs,NCs,NDs):-!,
    (Specs = (L,_) ->
        functor(L,F,A)
    ;
        functor(Specs,F,A)),
    current_fact(block_cond(F/A,Conditions)),
    get_predkey(F,A,Key),
    findall(c(Head,Call,Fs),
            current_fact(complete(Key,Abs,Head,Call,_,_,Fs)),List),
    simplify_block(Conditions,Abs,List,NConditions),
    (NConditions = [] ->
        NCs = SCs,
        NDs = NewDicts
    ;
        build_each_block(NConditions,F,A,NSpec),
        NCs = [directive(block(NSpec)):Id|SCs],
        NDs = [D|NewDicts]),
    simplify_prog(Cs,Ds,Abs,SCs,NewDicts).

%-------------------------------------------------------------%
% The rest of directives cannot be simplified                 %
%-------------------------------------------------------------%
simplify_prog([directive(Dir):Id|Cs],[D|Dicts],Abs,
                 [directive(Dir):Id|SCs],[D|NewDicts]):-
    simplify_prog(Cs,Dicts,Abs,SCs,NewDicts).
%-------------------------------------------------------------%
% No complete unifies with this clause. This means that       %
% the clause is never reached and so eliminated.              %
%-------------------------------------------------------------%
simplify_prog([clause(H,Body):Clid|Cs],[_|Dicts],Abs,SCs,NewDicts):-
    predkey_from_sg(H,Key),
    get_all_completes(Key,Abs,H,Completes),
    decide_unreachable(Completes,H,Body,Clid,Cs,Dicts,Abs,SCs,NewDicts).


%-------------------------------------------------------------%
% The clause is a fact                                        %
%-------------------------------------------------------------%
simplify_prog([clause(H,true:_):Clid|Cs],[D|Dicts],Abs,
                         [clause(H,[]):Clid|SCs],[D|NewDicts]):-
    simplify_prog(Cs,Dicts,Abs,SCs,NewDicts).
%-------------------------------------------------------------%
% The body is just a cut                                      %
%-------------------------------------------------------------%
simplify_prog([clause(H,!):Clid|Cs],[D|Dicts],Abs,
                        [clause(H,NBody):Clid|SCs],[D|NewDicts]):-!,
    simplify(clause(H,[!]),Cs,NCs,NBody,Dicts,NDicts),
    simplify_prog(NCs,NDicts,Abs,SCs,NewDicts).
%-------------------------------------------------------------%
% Rest of clauses. We try to simplify its body                %
%-------------------------------------------------------------%
simplify_prog([clause(H,Body):Clid|Cs],[dic(Vars,Names)|Dicts],Abs,
          [clause(H,SimpBody):Clid|NewSimp],[dic(Vars,Names)|Ndicts]):-
    simplify_body(H,Body,SimpBody,Vars,Abs,Clid),
    simplify_prog(Cs,Dicts,Abs,NewSimp,Ndicts).


%-------------------------------------------------------------%
% Handling of useless clauses, either globally or in 
% specialized versions.
%-------------------------------------------------------------%
decide_unreachable([],_H,_Body,Clid,Cs,Dicts,Abs,SCs,NewDicts):-!,
    asserta_fact(abs_ex(notreached,Clid)),
    simplify_prog(Cs,Dicts,Abs,SCs,NewDicts).
decide_unreachable(Completes,H,Body,Clid,Cs,Dicts,Abs,SCs,NewDicts):-
    filter_applicable(Completes,Abs,H,Body,NCompletes),
    decide_now_unreachable(NCompletes,Completes,Clid,Cs,Dicts,Abs,SCs,NewDicts).

decide_now_unreachable([],_Completes,Clid,Cs,Dicts,Abs,SCs,NewDicts):-!,
    asserta_fact(abs_ex(notreached,Clid)),
    simplify_prog(Cs,Dicts,Abs,SCs,NewDicts).
decide_now_unreachable(NCompletes,Completes,Clid,_Cs,_Dicts,_Abs,_SCs,_NewDicts):-
    current_fact(do_spec),
    length(Completes,LC),
    length(NCompletes,NLC),
    (NLC < LC ->
        store_useless_clauses_in_completes(Completes,Clid,NCompletes),
        fail
    ;
        fail
    ).


store_useless_clauses_in_completes([],_,[]).
store_useless_clauses_in_completes([c(Id,_,_)|Cs],Clid,[Id|NCs]):-!,
    store_useless_clauses_in_completes(Cs,Clid,NCs).
store_useless_clauses_in_completes([c(Id,_,_)|Cs],Clid,NCs):-
    add_simplif(Id,Clid,useless),
    store_useless_clauses_in_completes(Cs,Clid,NCs).

:- doc(get_all_completes(Key,Abs,H,-Completes),"Returns the
       list of completes which are applicable to this clause").

get_all_completes(Key,Abs,H,Completes):-
    findall(c(Id,Sg,Proj_u),
      (current_fact(complete(Key,Abs,Sg,Proj_u,_,Id,_)),
       \+(\+(Sg=H))),
      Completes).
:- doc(get_useful_completes(Key,Abs,H,-Completes),"Returns the
       list of completes which are applicable to this clause").

filter_applicable([],_Abs,_H,_Body,[]).
filter_applicable([c(Id,Sg,Proj_u)|Completes],Abs,H,Body,NCompletes):-
    neck_substitution(Body,Abs,H,Id,Sg,Proj_u,NeckSubs),
    (bottom(NeckSubs) ->
        NCompletes = MoreCompletes
    ;
        NCompletes = [Id|MoreCompletes]
    ),
    filter_applicable(Completes,Abs,H,Body,MoreCompletes).

neck_substitution(true:_,Abs,H,_Id,Sg,Proj_u,NeckSubs):-
    !,
    varset(Sg,Sv),
    varset(H,Hv),
    abs_sort(Abs,Proj_u,Proj),
    call_to_entry(Abs,Sv,Sg,Hv,H,not_provided,[],Proj,Entry,_Info), % TODO: add some ClauseKey? (JF)
    NeckSubs = [Entry].
neck_substitution(_:K,Abs,_H,Id,_Sg,_Proj_u,NeckSubs):-
    !,
    current_fact(memo_table(K,Abs,Id,_,_Vars,NeckSubs)).
neck_substitution((_:K,_),Abs,_H,Id,_Sg,_Proj_u,NeckSubs):-
    !,
    current_fact(memo_table(K,Abs,Id,_,_Vars,NeckSubs)).

%-------------------------------------------------------------------%
% simplify_body(+,+,-,+,+,+)                                        %
% simplify_body(H,Body,SimpBody,Vars,Abs,Clid)                      %
%  Simplifies a clause whose head is H and body Body and returs the %
% simplified body in SimpBody, according to Abs.      Vars are nece-%
% ssary to access the information from the interpreter              %
%-------------------------------------------------------------------%
simplify_body(H,Body,SimpBody,Vars,Abs,Clid):-
    body2list(Body,Blist),
    next_pred(Blist,Pred),
    ((there_is_delay, perform_reord(on))->
        simp_body_list_del(Pred,Blist,TmpBlist,Vars,Result,Abs,Del),
        reorder_del_body(TmpBlist,Del,Abs,Vars,SimpBlist0,NDel),
        wake_end_of_clause(NDel,Abs,Vars,Clid,Wakes),
        append(SimpBlist0,Wakes,SimpBlist)
    ;
        simp_body_list(Pred,Blist,SimpBlist,Vars,Result,Abs)),
    body_result(Result,H,SimpBlist,SimpBody).

%-------------------------------------------------------------------%
% simp_body_list(+,+,-,+,-,+)                                       %
% simp_body_list(Pred,Goals,NewGoals,Vars,Result,Abs)               %
%  Simplifies the list of goals Goals according to Abs and returns  %
% NewGoals and Result, which is a flag to know if a goal reducible  %
% to fail or error has been found                                   % 
%-------------------------------------------------------------------%
simp_body_list(none,[],[],_,nonerror,_).
simp_body_list((!/0),[!|Goals],[!|NewGoals],Vars,Result,Abs):-!,
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NewGoals,Vars,Result,Abs).

%% %% For simplification of delay not needed
%% %-------------------------------------------------------------%
%% % Goal is a set of parallel goals                             %
%% %-------------------------------------------------------------%
%% simp_body_list('.'/2,[P_exp|Goals],NewGoals,Vars,Result,Abs):-!,
%%      next_pred(P_exp,Pred),
%%         simp_body_list(Pred,P_exp,P_Goals,Vars,TmpResult,Abs),
%%         (TmpResult == fail -> % if one fails they all fail!!
%%          P_exp = [_:K|_],
%%             NewGoals = [(fail:K)],
%%          Result = fail
%%         ;
%%             (TmpResult == error ->
%%                 get_last(P_Goals,Last),
%%                 NewGoals = [Last,(error:'$bottom')],
%%              Result = error
%%             ;
%%                 NewGoals = [P_Goals|MoreGoals],
%%                 next_pred(Goals,NPred),
%%                 simp_body_list(NPred,Goals,MoreGoals,Vars,Result,Abs)
%%             )
%%         ).
%-------------------------------------------------------------%
% Goal from an imported predicate with an equiv assertion     %
%-------------------------------------------------------------%
simp_body_list(F/A,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs):-
    functor(NGoal,F,A),
    equiv(NGoal,Cond,Sense),
    get_memo_lub(K,Vars,Abs,yes,Info),
    adapt_info_to_assrt_head(Abs,Goal,Vars,Info,NGoal,NewInfo),
    abs_exec_conj_props(Cond,Abs,NewInfo),!,
    Goal = NGoal, % to propagate bindings to the literal "Sense"
    simp_abs_ex_body_list(Sense,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs).

%-------------------------------------------------------------%
% Goal is an abstractly executable type                       %
%-------------------------------------------------------------%
simp_body_list(F/A,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs):-
    determinable(Abs,types),
    translate_lattice_types(F,A,Goal,NGoal),
    prop_to_native(NGoal,regtype(SPred)),
    get_memo_lub(K,Vars,Abs,yes,Info),
    abs_exec_regtype_in_clause(Abs,SPred,F,A,Goal,Vars,Info,Sense),!,
    simp_abs_ex_body_list(Sense,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs).

%-------------------------------------------------------------%
% We search for optimizations is particular versions          %
%-------------------------------------------------------------%
simp_body_list(F/A,[(Goal:K)|_Goals],_NewGoals,Vars,_Result,Abs):-
    current_fact(do_spec),
    functor(NGoal,F,A),
    equiv(NGoal,Cond,Sense),
    try_imported_in_each_id(K,Abs,Vars,Goal,NGoal,Cond,Sense),
    fail.

%-------------------------------------------------------------%
% We search for optimizations is particular versions          %
%-------------------------------------------------------------%
simp_body_list(Pred,[(Goal:K)|_Goals],_NewGoals,Vars,_Result,Abs):-
    current_fact(do_spec),
    (dyn_abs_exec(Abs,Pred,_Sense,_Cond) ->
        findall(Id,memo_table(K,_,Id,_,_,_),Ids),
        try_dyn_table_in_each_id(Ids,K,Abs,Vars,Pred,Goal),
        fail
    ;
        fail).

% GP finally removed!!
%% %-------------------------------------------------------------%
%% % Goal is abstractly executable                               %
%% %-------------------------------------------------------------%
%% simp_body_list(Pred,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs):-
%%      abs_exec(Abs,Pred,Sense,Cond),
%%      condition_holds(Cond,K,Vars,Abs,Goal),!,
%%      simp_abs_ex_body_list(Sense,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs).


%-------------------------------------------------------------%
% Goal is  is/2                                               %
%-------------------------------------------------------------%
% the whole call to is/2 can be abstractly executed
simp_body_list('arithmetic:is'/2,[('arithmetic:is'(A,_B):K)|Goals],NewGoals,Vars,
                                                    Result,Abs):-
    determinable(Abs,types),
    next_or_last_key(Goals,K,Key1),
    get_memo_lub(Key1,Vars,Abs,yes,Info),
    var(A),
    concrete(Abs,A,Info,[V]),
    !,
    (current_pp_flag(exec_unif,on) ->
        (A = V ->
         simp_abs_ex_body_list(true,[_|Goals],NewGoals,Vars,Result,Abs)
        ;
            simp_abs_ex_body_list(fail,[(_:K)|Goals],NewGoals,Vars,Result,Abs))
    ;
        next_pred(Goals,NPred),
        NewGoals = [((A = V):K)|MoreGoals],
        simp_body_list(NPred,Goals,MoreGoals,Vars,Result,Abs)).
% though it cannot be fully executed, at least some values of variables are know
simp_body_list('arithmetic:is'/2,[('arithmetic:is'(A,B):K)|Goals],[((A is NB):K)|NewGoals],
                                                         Vars,Result,Abs):-
    determinable(Abs,types),
    get_memo_lub(K,Vars,Abs,yes,Info),
    var(A),
    varset(B,VarsB),
    has_concret_one(VarsB,Abs,Info,InfoConcr),
    InfoConcr \== [],
    !,
    copy_term((B,VarsB,InfoConcr),(CopyB,CopyVarsB,CopyInfoConcr)),
    apply(CopyInfoConcr),
    eval_partial(CopyB,NB,CopyVarsB,VarsB),
    next_pred(Goals,NPred),
    simp_body_list(NPred,Goals,NewGoals,Vars,Result,Abs).
%% GPS to be done!
%% %-------------------------------------------------------------%
%% % Goal is a check program point assertion                     %
%% %-------------------------------------------------------------%
%% simp_body_list(check/1,[(check(Goal):K)|Goals],NewGoals,Vars,Result,Abs):-
%%      abs_exec(Abs,Pred,Sense,Cond),
%%      (Cond \== true ->
%%          get_memo_lub(K,Vars,Abs,yes,Info)
%%      ;
%%          true),
%%      cond(Cond,Abs,Goal,Info),
%%         !,
%%         simp_abs_ex_body_list(Sense,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs).
%% For simplification of delay not needed
%-------------------------------------------------------------%
% Goal has bottom as success substitution                     %
%-------------------------------------------------------------%
simp_body_list(_P,[(Goal:K)|Goals],NewGoal,Vars,Result,Abs):-
    next_or_last_key(Goals,K,Key1),
    get_memo_lub(Key1,Vars,Abs,yes,Info),
    Info == '$bottom',
    !,
    NewGoal = [(Goal:K),(fail:'$bottom')],
    Result = fail.

%-------------------------------------------------------------%
% None of the previous                                        %
%-------------------------------------------------------------%
simp_body_list(_,[(Goal:K)|Goals],[(Goal:K)|NewGoals],Vars,
                                                    Result,Abs):-
    next_pred(Goals,NPred),
    simp_body_list(NPred,Goals,NewGoals,Vars,Result,Abs).

%% :- doc(condition_holds(Cond,K,Vars,Abs,Goal),"We check whether
%% @var{Cond} holds and thus @{Goal} can be abstractly executed. ").
%% 
%% condition_holds(true,_K,_Vars,_Abs,_Goal):-!.
%% condition_holds(Cond,K,Vars,Abs,Goal):-
%%      get_memo_lub(K,Vars,Abs,yes,Info),
%%      cond(Cond,Abs,Goal,Info).

%-------------------------------------------------------------------%   
% simp_abs_ex_body_list(+,+,-,+,-,+)                                %
% simp_abs_ex_body_list(Sense,Goals,NewGoals,Vars,Result,Abs)       %
%  Special case of simp_body_list when the goal is abstractly       %
%  executable                                                       %
%-------------------------------------------------------------------%
%-----------------------------------------------------------------------
% simp_abs_ex_body_list(when,+,-,+,+,-,+).
% main entry point for optimization of dynamic scheduling.
%-----------------------------------------------------------------------

% The goal definitely does not delay. No need to reorder. 
simp_abs_ex_body_list(when,[when(_,Goal):K|Goals],NewGoals,Vars,Result,Abs):-
    key_after_reordering(Goals,K,Key),
    no_delayed_in_point(Key,K),!,
    NewGoals = [Goal:K|NGoals],
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NGoals,Vars,Result,Abs).

simp_abs_ex_body_list(when,[when(Cond,Goal):K|Goals],NGoals,Vars,Result,Abs):-
    findall((_,Vars,Info),(current_fact(memo_table(K,Abs,_,_,Vars,[Info]),_)),InfoList),
    no_repetitions(InfoList,[],Abs,Vars,LInfo),
    NGoals = [when(NewCond,Goal):K|MoreGoals],
    simp_when_no_lub_each_info(Cond,LInfo,Abs,TmpCond,_),
    simplify_when_false_or_chose(TmpCond,Abs,K,Goal,NewCond,_,_),
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,MoreGoals,Vars,Result,Abs).

simp_abs_ex_body_list(freeze,[freeze(Var,Goal):K|Goals],NGoals,Vars,R,Abs):-
    key_after_reordering(Goals,K,Key),
    (no_delayed_in_point(Key,K) ->
        NGoals = [Goal:K|MoreGoals]
    ;
        NGoals = [freeze(Var,Goal):K|MoreGoals]),
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,MoreGoals,Vars,R,Abs).
simp_abs_ex_body_list(block_cond(_),[Goal:K|Goals],[Goal:K|NGoals],Vars,Result,Abs):-
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NGoals,Vars,Result,Abs).
simp_abs_ex_body_list(true,[_|Goals],NewGoals,Vars,Result,Abs):-
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NewGoals,Vars,Result,Abs).

simp_abs_ex_body_list(fail,[_:K|_],[(fail:K)],_Vars,fail,_Abs).
simp_abs_ex_body_list('basiccontrol:fail',[_:K|_],[('basiccontrol:fail':K)],_Vars,fail,_Abs).

simp_abs_ex_body_list(error,[Goal|_],[Goal,(error:'$bottom')],_,error,_Abs).
simp_abs_ex_body_list(indep,['andprolog_rt:indep'(L):K|Goals],NewGoals,Vars,Result,Abs):-
    get_memo_lub(K,Vars,Abs,yes,Info),
    simplify_indep(L,Abs,Info,NewL),
    !,
    (NewL == [] ->
        NewGoals = NGoals
    ;
        NewGoals = ['andprolog_rt:indep'(NewL):K|NGoals],
        special_simp_indep(K,Vars,Abs,NewL)),
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NGoals,Vars,Result,Abs).
simp_abs_ex_body_list(indep,['andprolog_rt:indep'(_):K|_],[fail:K],_,fail,_).

simp_abs_ex_body_list(ground,['term_typing:ground'(T):K|Goals],NewGoals,Vars,Result,Abs):-
    varset(T,L),
    get_memo_lub(K,Vars,Abs,yes,Info),
    simplify_ground(L,Abs,Info,NewL),
    !,
    (NewL == [] ->
        NewGoals = NGoals
    ;
        (NewL = [Var] ->
            Term = Var
        ;
            Term = NewL),
        NewGoals = [ground(Term):K|NGoals],
        special_simp_ground(K,Vars,Abs,NewL)),
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NGoals,Vars,Result,Abs).
simp_abs_ex_body_list(ground,['term_typing:ground'(_):K|_],[fail:K],_,fail,_).
%jcf
simp_abs_ex_body_list(imported(SpecName),[Goal:K|Goals],[NewGoal:K|NewGoals],Vars,Result,Abs):-
    functor(Goal,_,A),
    functor(NewGoal,SpecName,A),
    copy_args(A,Goal,NewGoal),
    next_pred(Goals,Pred),
    simp_body_list(Pred,Goals,NewGoals,Vars,Result,Abs).
%jcf

%% GPS not needed anymore
%% %-------------------------------------------------------------------%
%% % clear(+)                                                          %
%% %  Clear all the information recorded during the previous iteration %
%% % before starting a new one                                         %
%% %-------------------------------------------------------------------%
%% clear(Keys):-
%%         clear_tag(Keys,nonerror),
%%         clear_tag(Keys,error),
%%         clear_tag(Keys,fact(_)),
%%         clear_tag(Keys,bridge(_,_)),
%%         clear_tag(Keys,failure).
%% 
%% %-------------------------------------------------------------------%
%% % clear_tag(+,+)                                                        %
%% % clear_tag(Keys,Tag)                                                   %
%% %  Removes all the information recorded with Tag during previous    %
%% % iteration for predicates whith Keys                               %
%% %-------------------------------------------------------------------%
%% clear_tag([],_).
%% clear_tag([Key|_],Tag):-
%%         recorded_internal(Key,Tag,Ref),
%%         erase(Ref),
%%         fail.
%% clear_tag([_|Keys],Tag):-
%%      clear_tag(Keys,Tag).
%% 
%-------------------------------------------------------------------%
% show_simplif(+)                                                   %
% show_simplif(N)                                                   %
%  This predicate gives information about the simplifications done  %
% N is the number of iterations that have been necessary.           %
%-------------------------------------------------------------------%
show_simplif(N):-
       iterations(N),
    notreached,
    reducedfail,
    reduced(true),
    reduced(error).
iterations(0):-!.
iterations(N):-
    format("~N     ~c        simplify: ~d iterations ~N",[37,N]).

notreached:-
    current_fact(abs_ex(notreached,_)),
    !,
    format("~N     ~c  clauses never reached",[37]),
    notreach.
notreached.
notreach:-
    current_fact(abs_ex(notreached,Pred)),
    nl,
    write('                  '),put_code(37),write('  '),
    write(Pred),
    fail.
notreach:-nl.
reducedfail:-
    current_fact(abs_ex(_,fail)),
    !,
    format('~N     ~c  predicates reduced to fail:',[37]),
    reducfail.
reducedfail.
reducfail:-
    current_fact(abs_ex(Pred,fail)),
    nl,
    write('                  '),put_code(37),write('  '),
    write(Pred),
    fail.
reducfail:-nl.
reduced(Sense):-
    current_fact(abs_ex(_,Sense)),
    !,

    format('~N     ~c  predicates reduced to ~w:',[37,Sense]),
    reduc(Sense).
reduced(_).
reduc(Sense):-
    current_fact(abs_ex(Pred,Sense)),
    nl,
    write('                  '),write('%'),write('  '),
    write(Pred),
    fail.
reduc(_):-nl.

%-------------------------------------------------------------------%
% decide_specialize(+,+,+,+,-,-)                                    %
% decide_specialize(Spc,Program,Dicts,Abs,Spc_Program,Spc_Dicts)    %
%  Spc_Program and Sps_Dicts are the specialized versions of Program%
% and Dicts according to Spc. If Spc is no, then no specialization  %
% takes place.                                                      %
%-------------------------------------------------------------------%
decide_specialize(simp,Program,Dicts,Preds,_,SimpProg,SimpDicts,SimpPreds):-
    SimpPreds = Preds,
    simplify_versions(Program,Dicts,SimpProg,SimpDicts).
decide_specialize(spec,Program,Dicts,Preds,_,Simp_S_Prog,Simp_S_Dicts,Simp_S_Preds):-
    there_is_delay,!,
    Simp_S_Preds = Preds,
    simplify_versions(Program,Dicts,Simp_S_Prog,Simp_S_Dicts).
decide_specialize(spec,Program,Dicts,Preds,Abs,Simp_S_Prog,Simp_S_Dicts,Simp_S_Preds):-
    mult_spec(Program,Dicts,Preds,Abs,Simp_S_Prog,Simp_S_Dicts,Simp_S_Preds).

%-------------------------------------------------------------------%
% simplify_versions(+,+,-,-)                                        %
% simplify_versions(Program,Dicts,NewProgram,NewDicts               %
%  For all the newly generated versions we must call simplify to    %
%  eliminate clauses after a cut (!) and to record information      %
%  needed by reduce_last_iteration                                  %
%-------------------------------------------------------------------%
simplify_versions([],[],[],[]).
simplify_versions([directive(D):Id|Cs],[Dict|Dicts],
              [directive(D):Id|SCs],[Dict|NewDicts]):- !,
    simplify_versions(Cs,Dicts,SCs,NewDicts).
simplify_versions([clause(Head,Body):Clid|Cs],[D|Dicts],
                                             SimpProg,NewDicts):-
    simplify(clause(Head,Body),Cs,RestOut,NewBody,Dicts,DictsOut),
    ((NewBody = [('basiccontrol:fail':_)];
         NewBody = [(fail:_)]) ->
        SimpProg = NewSimp,
        NewDicts = Ndicts
    ;
        SimpProg = [clause(Head,NewBody):Clid|NewSimp],
        NewDicts = [D|Ndicts]),
    simplify_versions(RestOut,DictsOut,NewSimp,Ndicts).

%% %----------------------------------------------------------------------
%% % This is needed because delay analysis may leave approx instead of
%% % completes. It would be very messy to modify all the code for 
%% % simplification and specialization to also deal with approx register
%% rename_approx_to_completes:-
%%      there_is_delay,!, 
%%      approx_to_completes_delay.
%% rename_approx_to_completes:-
%%      approx_to_completes.
%% 
%% approx_to_completes_delay:-
%%      current_fact(approx(Key,Abs,A1,d(A21,A22,_,_),A3,A4,A5)),
%%      retract_fact(approx(Key,Abs,A1,d(A21,A22,_,_),A3,A4,A5)),
%%      asserta_fact(complete(Key,Abs,A1,d(A21,A22,_),A3,A4,A5)),
%%      fail.
%% approx_to_completes_delay.
%% 
%% approx_to_completes:-
%%      current_fact(approx(Key,Abs,A1,A2,A3,A4,A5)),
%%      retract_fact(approx(Key,Abs,A1,A2,A3,A4,A5)),
%%      asserta_fact(complete(Key,Abs,A1,A2,A3,A4,A5)),
%%      fail.
%% approx_to_completes.

%% renaming_clashes:-
%%      findall(clash(Version,K,Name1,Name2),
%%          (current_fact(spec_support:replace(K,Version,Name1)),
%%           current_fact(spec_support:replace(K,Version,Name2)),
%%           Name1\==Name2),Clashes),
%%      eliminate_eq_clashes(Clashes,NClashes),
%%      write_clashes(NClashes).
%% eliminate_eq_clashes([],[]).
%% eliminate_eq_clashes([clash(Version,K,Name1,Name2)|Cs],NClashes):-
%%      member(clash(Version,K,Name2,Name1),Cs),!,
%%      eliminate_eq_clashes(Cs,NClashes).
%% eliminate_eq_clashes([clash(Version,K,Name1,Name2)|Cs],NClashes):-
%%      member(clash(Version,K,Name1,Name2),Cs),!,
%%      eliminate_eq_clashes(Cs,NClashes).
%% eliminate_eq_clashes([C|Cs],[C|NCs]):-
%%      eliminate_eq_clashes(Cs,NCs).
%% 
%% 
%% write_clashes([]).
%% write_clashes([clash(Version,K,Name1,Name2)|Cs]):-
%%      write(user,'In literal '),
%%      write(user,K),
%%      write(user,', '),
%%      write(user,Version),
%%      write(user,' : '),
%%      write(user,Name1),
%%      write(user,' and '),
%%      write(user,Name2),
%%      nl(user),
%%      write_clashes(Cs).

%---------

has_concret_one([],_Abs,_Info,[]).
has_concret_one([Var|Vars],Abs,Info,[Var:A|InfoConcr]):-
    concrete(Abs,Var,Info,C),!,
    C = [A],
    has_concret_one(Vars,Abs,Info,InfoConcr).
has_concret_one([_|Vars],Abs,Info,InfoConcr):-
    has_concret_one(Vars,Abs,Info,InfoConcr).

apply([X:Term|ASub]):-
    X=Term,
    apply(ASub).
apply([]).

change_var(X,Y,[X1|_],[Y|_]):- X == X1,!.
change_var(X,Y,[_|Xs],[_|Ys]):- !,change_var(X,Y,Xs,Ys).


eval_partial(X,Y,_,_):-
    varset(X,[]),
    Y is X.
eval_partial(X,Y,NV,V):-
    var(X),
    change_var(X,Y,NV,V).
eval_partial(X,Y,NV,V):-
    functor(X,F,1),
    arg(1,X,Arg),
    eval_partial(Arg,Arg1,NV,V),
    functor(Y,F,1),
    arg(1,Y,Arg1).
eval_partial(X,Y,NV,V):-
    functor(X,F,2),
    arg(1,X,Arg1),
    arg(2,X,Arg2),
    eval_partial(Arg1,EArg1,NV,V),
    eval_partial(Arg2,EArg2,NV,V),
    functor(Y,F,2),
    arg(1,Y,EArg1),
    arg(2,Y,EArg2).


%% try_reg_type_in_each_id(K_Pre,K_Post,Abs):-
%%      current_fact(do_spec),
%%      current_fact(memo_table(K_Post,Abs,Num,_,_,_)),
%%      abs_exec_reg_type_with_post_info_one_version(Num,K_Pre,K_Post,Abs,Sense),
%%      add_simplif(Num,K_Pre,Sense),
%%      fail.
%% try_reg_type_in_each_id(_K,_Key1,_Abs).

try_imported_in_each_id(K,Abs,Vars,Goal,NGoal,Cond,Sense):-
    current_fact(memo_table(K,Abs,Num,_,Vars,[Info_u])),
    abs_sort(Abs,Info_u,Info),
    adapt_info_to_assrt_head(Abs,Goal,Vars,Info,NGoal,NewInfo),
    abs_exec_conj_props(Cond,Abs,NewInfo),
    add_simplif(Num,K,imported(Goal,Sense)),
    fail.
try_imported_in_each_id(_K,_Abs,_Vars,_Goal,_NGoal,_Cond,_Sense).

try_dyn_table_in_each_id([],_K,_Abs,_Vars,_Pred,_Goal).
try_dyn_table_in_each_id([Id|Ids],K,Abs,Vars,Pred,Goal):-
    current_fact(memo_table(K,Abs,Id,_,Vars,[Info_u])),
    abs_sort(Abs,Info_u,Info),
    dyn_abs_exec(Abs,Pred,Sense,Cond),
    cond(Cond,Abs,Goal,Info),!,
    Sense = imported(RealSense),
    change_call(Goal,NewGoal,RealSense),
    add_simplif(Id,K,imported(Goal,NewGoal)),
    try_dyn_table_in_each_id(Ids,K,Abs,Vars,Pred,Goal).
try_dyn_table_in_each_id([_Id|Ids],K,Abs,Vars,Pred,Goal):-
    try_dyn_table_in_each_id(Ids,K,Abs,Vars,Pred,Goal).
