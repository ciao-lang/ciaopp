:- module(plai,
    [ plai/5,
      cleanup_plai/1,
      mod_plai/5,
      %% *** Needs revising MH
      is_checker/1,
      analyze/7,       %% JNL
      init_fixpoint/1, %% JNL         
      entry_point/5    %% JNL
    ],
    [ assertions ]).

% Ciao library
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(counters), [setcounter/2, inccounter/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(vndict), [vars_names_dict/3]).
:- use_module(library(port_reify), [once_port_reify/2, port_call/1]).
:- use_module(library(messages),[warning_message/2]).
%% *** MH

% CiaoPP library
:- use_module(ciaopp(analysis_stats), [stat_no_store/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(spec(sp_clauses), [init_unfold/0]).
:- use_module(spec(unfold_times), 
    [ init_unfold_times/0, ask_unfold_times/1, global_time_ellapsed/3 ]).
:- use_module(ciaopp(p_unit),
    [entry_assertion/3, type_of_goal/2, type_of_directive/2]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3, predkey_from_sg/2]).
:- use_module(ciaopp(plai/intermod_entry), [get_entry_info/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2,
    push_pp_flag/2, pop_pp_flag/1]).
:- use_module(spec(mem_usage), [reset_mem_usage/0, ask_mem_usage/2]).

%:- use_package(spec(nomem_usage)).

% Plai library
:- use_module(ciaopp(plai/domains), 
    [ init_abstract_domain/2, empty_entry/4, unknown_entry/4, 
      info_to_asub/7,dom_statistics/2]).
:- use_module(ciaopp(plai/normalize_args), [normalize_args/4]).
:- use_module(ciaopp(plai/plai_errors), [undo_errors/0]).
:- use_module(ciaopp(plai/fixpo_plai), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_dd), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_di), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_check_di), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_check_di2), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_check_di3), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_check_di4), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_check_di5), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_plai_gfp), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- use_module(ciaopp(plai/fixpo_check_reduced_di), [query/8, init_fixpoint/0, cleanup_fixpoint/1]).
:- if(defined(has_ciaopp_extra)).
:- use_module(poly_spec(heuristic_pcpe), [query/1, init_fixpoint/0, cleanup_fixpoint/0]).
:- endif.
:- use_module(ciaopp(plai/fixpo_bu), [tp/1, init_fixpoint/0, cleanup_fixpoint/1]).

:- use_module(ciaopp(plai/tarjan), [tarjan/2, recursive_classify/4, fake_recursive_classify/2]).
:- use_module(ciaopp(plai/transform), 
    [ cleanup_trans_clauses/0,transform_clauses/5,determine_r_flag/3]).
:- use_module(ciaopp(plai/fixpo_ops), [
    store_previous_analysis/1,
    store_previous_analysis_completes/1,
    reset_previous_analysis/1,
    remove_useless_info/1]).
:- use_module(ciaopp(plai/trace_fixp), [trace_reset/0]).

:- if(defined(has_ciaopp_java)).
:- use_module(ciaopp(plai/output_java_info), [java_statistics/1]).
:- else.
java_statistics(_).
:- endif.
%------------------------------------------------------------------------%

:- doc(title,"Program Analysis (PLAI)").

:- doc(stability, devel).
:- doc(bug,"Call patterns generated for imported predicates should be 
    saved in the related modules .asr files after analysis.").
:- doc(bug,"Meta-preds should be analysed as such only if imported.
    Otherwise, there is the code... and it may be recursive!").
:- doc(bug,"An export from a reexport yields unknown and bottom.").

%------------------------------------------------------------------------%

:- doc(cleanup_plai(AbsInt),"Cleanups the database of analysis
    of all permanent information regarding abstract
    domain @var{AbsInt}.").

cleanup_plai(AbsInt):-
    fixpo_plai:cleanup_fixpoint(AbsInt),
    %fixpo_plai_with_static_profiling_info:cleanup_fixpoint(AbsInt),
    fixpo_plai_gfp:cleanup_fixpoint(AbsInt),
    fixpo_dd:cleanup_fixpoint(AbsInt),
    fixpo_di:cleanup_fixpoint(AbsInt),
    fixpo_check_di:cleanup_fixpoint(AbsInt),
    fixpo_check_di2:cleanup_fixpoint(AbsInt),
    fixpo_check_di3:cleanup_fixpoint(AbsInt),
    fixpo_check_reduced_di:cleanup_fixpoint(AbsInt),
    fixpo_check_di4:cleanup_fixpoint(AbsInt),
    fixpo_check_di5:cleanup_fixpoint(AbsInt),
    fixpo_bu:cleanup_fixpoint(AbsInt),
    cleanup_pcpe.

:- if(defined(has_ciaopp_extra)).
cleanup_pcpe :-
    heuristic_pcpe:cleanup_fixpoint.
:- else.
cleanup_pcpe.
:- endif.

init_fixpoint(plai):- fixpo_plai:init_fixpoint.
%init_fixpoint(plai_sp):- fixpo_plai_with_static_profiling_info:init_fixpoint.
init_fixpoint(plai_gfp):- fixpo_plai_gfp:init_fixpoint.
init_fixpoint(dd):- fixpo_dd:init_fixpoint.
init_fixpoint(di):- fixpo_di:init_fixpoint.
init_fixpoint(check_di):- fixpo_check_di:init_fixpoint.
init_fixpoint(check_di2):- fixpo_check_di2:init_fixpoint.
init_fixpoint(check_di3):- fixpo_check_di3:init_fixpoint.
init_fixpoint(check_reduc_di):- fixpo_check_reduced_di:init_fixpoint.
init_fixpoint(check_di4):- fixpo_check_di4:init_fixpoint.
init_fixpoint(check_di5):- fixpo_check_di5:init_fixpoint.
init_fixpoint(bu):- fixpo_bu:init_fixpoint.
:- if(defined(has_ciaopp_extra)).
init_fixpoint(poly_spec):- heuristic_pcpe:init_fixpoint.
:- endif.

:- doc(plai(Cls,Ds,Fixp,AbsInt,Info),"Performs the analysis of the
    clauses in @var{Cls} (dictionaries of variables in @var{Ds})
    with fixpoint algorithm @var{Fixp} and analysis domain
    @var{AbsInt}.  The analysis results are left in a permanent
    database (see @lib{plai_db}). @var{Info} is a list of
    properties and informations. One possible value is
    @tt{[time(Total,[(subtask1,T1),...,(subtaskN,TN)])]}.").

plai(Cls,Ds,Fixp,AbsInt,Stats):-
    plai_(Cls,Ds,Fixp,AbsInt,mon,Stats).

plai_(Cls,Ds,Fixp,AbsInt,ModFlag,Stats) :-
    stat_no_store(init_plai(AbsInt,Flags,Fixp), InitT),
    pplog(analyze_module, ['{init for the ', Fixp, ' fixpoint in ',InitT, ' msec.}']),
    ( ModFlag = mon -> % TODO: why once_port_reify?
        once_port_reify(do_plai(Cls,Ds,Fixp, AbsInt,TPre,TAna), Port)
    ; ModFlag = mod ->
        once_port_reify(do_mod_plai(Cls,Ds,Fixp,AbsInt,TPre,TAna), Port)
    ),
    pop_pp_flags(Flags),
    port_call(Port),
    Total is TPre + TAna,
    TimeInfo = time(Total,[(prep,TPre),(ana,TAna)|Local_C_Info]),
    ( ModFlag = mon ->
        current_pp_flag(local_control,LC),
        ( is_checker(Fixp) -> PH = 'certificate checked by' ;  PH = 'analyzed by'),
        pplog(analyze_module, ['{', PH, ' ', Fixp, ' using ', AbsInt,
                               ' with local-control ', LC,' in ', TAna, ' msec.}']),
        % TODO: Total time is wrong, Local_C_Info not added!!!
        ask_unfold_times(Local_C_Info),
        java_statistics(AbsInt),
        ask_mem_usage(Delta,Details),
        MemoryInfo = memory(Delta,Details),
        Stats = [TimeInfo,MemoryInfo|DomInfo]
    ; ModFlag = mod ->
        pplog(analyze_module, ['{analyzed by ', Fixp, ' using ', AbsInt, ' in ', TAna,
                               ' msec.}']),
        Local_C_Info = [],
        Stats = [TimeInfo|DomInfo]
    ),
    ( current_pp_flag(remove_useless_abs_info,on) ->
        remove_useless_info(AbsInt) % TODO: time
    ; true
    ),
    dom_statistics(AbsInt, DomInfo).

do_plai(Cls,Ds,Fixp, AbsInt, TPre, TAna):-
    stat_no_store(preprocess(Fixp,AbsInt,Cls,Ds,Ps), TPre), !, % TODO: fix, move cuts deeper
    pplog(analyze_module, ['{preprocessed for the ', Fixp, ' fixpoint in ',TPre, ' msec.}']),
    reset_mem_usage,
    stat_no_store(topdown_analysis(Fixp,AbsInt,Ps),TAna).

init_plai(AbsInt,Flags,Fixp) :-
    init_abstract_domain(AbsInt,Flags),
    init_fixpoint(Fixp), !, % TODO: fix, move cuts deeper
    trace_reset, % reset tracing for the new fixpoint
    init_unfold, !, % TODO: fix, move cuts deeper
    init_unfold_times, !, % TODO: fix, move cuts deeper
    cleanup_trans_clauses, !, % TODO: fix, move cuts deeper
    undo_errors, !. % TODO: fix, move cuts deeper

% TODO: (IG) define with multifile?
is_checker(check_di).
is_checker(check_di2).
is_checker(check_di3).
is_checker(check_di4).
is_checker(check_di5).
is_checker(check_reduc_di).

preprocess(di,AbsInt,Cls,Ds,Ps):- !,
    current_pp_flag(local_control,LC),
    ( LC == df_hom_emb_as ->
        tarjan(Cls,Sccs),
        recursive_classify(Cls,Sccs,Rs,Ps)
    ;
        fake_recursive_classify(Cls,Rs), 
        Ps = notarjan
    ),
    transform_clauses_(Cls,Ds,Rs,Ps,AbsInt).
preprocess(Fixp,AbsInt,Cls,Ds,Ps):-
    ( Fixp == check_di ; Fixp == check_di2 ; Fixp == check_di3 ; Fixp == check_reduc_di), !,
    % check_di doesn't need tarjan 
    fake_recursive_classify(Cls,Rs), 
    Ps = notarjan,
    transform_clauses_(Cls,Ds,Rs,Ps,AbsInt),
    reset_previous_analysis(AbsInt),
    store_previous_analysis_completes(AbsInt),
    ( Fixp == check_di ->
        fixpo_check_di:cleanup_fixpoint(AbsInt)
    ; Fixp == check_di2 ->
        fixpo_check_di2:cleanup_fixpoint(AbsInt)
    ; Fixp == check_reduc_di ->
        fixpo_check_reduced_di:cleanup_fixpoint(AbsInt)
    ;
        fixpo_check_di3:cleanup_fixpoint(AbsInt)
    ).
preprocess(check_di4,AbsInt,Cls,Ds,Ps):-!, % TODO: merge with check_di5
    % check_di doesn't need tarjan 
    fake_recursive_classify(Cls,Rs),
    Ps = notarjan,
    transform_clauses_(Cls,Ds,Rs,Ps,AbsInt),
    store_previous_analysis(AbsInt),
    fixpo_check_di4:cleanup_fixpoint(AbsInt).
preprocess(check_di5,AbsInt,Cls,Ds,Ps):-!,
    % check_di doesn't need tarjan 
    fake_recursive_classify(Cls,Rs), 
    Ps = notarjan,
    transform_clauses_(Cls,Ds,Rs,Ps,AbsInt),
    store_previous_analysis(AbsInt),
    fixpo_check_di5:cleanup_fixpoint(AbsInt).
:- if(defined(has_ciaopp_extra)).
preprocess(poly_spec,_AbsInt,_Cls,_Ds,_Ps):-!,
    heuristic_pcpe:cleanup_fixpoint.
:- endif.
preprocess(Fixp,AbsInt,Cls,Ds,Ps):-
    ( Fixp == plai ; Fixp == plai_sp ; Fixp == plai_gfp ; Fixp == dd), !,
      % TODO:[new-resources] plai_sp is not used? it was in fixpo_plai_with_static_profiling_info.pl
    generate_trans_clauses(Cls,Ds,AbsInt,Ps).
preprocess(bu,AbsInt,Cls,Ds,Ps):- !,
    generate_trans_clauses(Cls,Ds,AbsInt,Ps).
% preprocess(bu,AbsInt,Cls,Ds,Ps):-!,
%       fake_recursive_classify(Cls,Rs),
%       Ps = notarjan,
%       transform_clauses_(Cls,Ds,Rs,Ps,AbsInt).
preprocess(delay,AbsInt,Cls,Ds,[]):- !, % TODO: does Fixp=delay work?
    normalize_args(Cls,Ds,NormCls,NormDs),
    transform_clauses(NormCls,NormDs,[],[],AbsInt).

:- export(generate_trans_clauses/4).
% TODO: move to transform/clause_db ?
generate_trans_clauses(Cls,Ds,AbsInt,Ps) :-
    tarjan(Cls,Sccs),
    recursive_classify(Cls,Sccs,Rs,Ps),
    transform_clauses_(Cls,Ds,Rs,Ps,AbsInt).

:- export(transform_clauses_/5).
transform_clauses_(Cls,Ds,Rs,Ps,AbsInt):-
    current_pp_flag(normalize, off), !,
    transform_clauses(Cls,Ds,Rs,Ps,AbsInt).
transform_clauses_(Cls,Ds,Rs,Ps,AbsInt):-
    normalize_args(Cls,Ds,NormCls,NormDs),
    transform_clauses(NormCls,NormDs,Rs,Ps,AbsInt).

:- export(topdown_analysis/3).
:- if(defined(has_ciaopp_extra)).
topdown_analysis(poly_spec,_AbsInt,_Ps):-!,
    findall(Goal, entry_point(_AbsInt,Goal,_Gv,_Call,_Name), Goals),
    heuristic_pcpe:query(Goals).
:- endif.
topdown_analysis(bu,AbsInt,_):- !,
    tp(AbsInt).
topdown_analysis(_Fixp,AbsInt,_Ps) :-
    \+ entry_point(AbsInt,_,_,_,_), !,
    warning_message("No entries found for ~w", [AbsInt]).
topdown_analysis(Fixp,AbsInt,Ps):-
    entry_point(AbsInt,Goal,Gv,Call,Name),
    functor(Goal,F,A),
    determine_r_flag(Ps,F/A,RFlag),
    ( analyze(Fixp,AbsInt,RFlag,Goal,Gv,Call,Name) -> true ),
    fail.
topdown_analysis(_Fixp,_AbsInt,_Ps).

analyze(plai,AbsInt,RFlag,Goal,Gv,Call,Name):-
    functor(Goal,F,A),
    get_predkey(F,A,K),
    fixpo_plai:query(AbsInt,K,Goal,Gv,RFlag,Name,Call,_Succ).
% analyze(plai_sp,AbsInt,RFlag,Goal,Gv,Call,Name):-
%       functor(Goal,F,A),
%       get_predkey(F,A,K),
%       determine_r_flag(Ps,F/A,RFlag),
%       fixpo_plai_with_static_profiling_info:query(AbsInt,K,Goal,Gv,RFlag,Name,Call,_Succ).
analyze(plai_gfp,AbsInt,RFlag,Goal,Gv,Call,Name):-
    functor(Goal,F,A),
    get_predkey(F,A,K),
    fixpo_plai_gfp:query(AbsInt,K,Goal,Gv,RFlag,Name,Call,_Succ).
analyze(dd,AbsInt,RFlag,Goal,Gv,Call,Name):-
    functor(Goal,F,A),
    get_predkey(F,A,K),
  fixpo_dd:query(AbsInt,K,Goal,Gv,RFlag,Name,Call,_Succ).
analyze(di,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    predkey_from_sg(Goal,K),
    fixpo_di:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ).
analyze(check_di,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    push_pp_flag(reuse_fixp_id,on),
    predkey_from_sg(Goal,K),
    fixpo_check_di:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ),
    pop_pp_flag(reuse_fixp_id).
analyze(check_di2,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    push_pp_flag(reuse_fixp_id,on),
    predkey_from_sg(Goal,K),
    fixpo_check_di2:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ),
    pop_pp_flag(reuse_fixp_id).
analyze(check_di3,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    push_pp_flag(reuse_fixp_id,on),
    predkey_from_sg(Goal,K),
    fixpo_check_di3:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ),
    pop_pp_flag(reuse_fixp_id).
analyze(check_reduc_di,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    push_pp_flag(reuse_fixp_id,on),
    predkey_from_sg(Goal,K),
    fixpo_check_reduced_di:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ),
    pop_pp_flag(reuse_fixp_id).
analyze(check_di4,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    push_pp_flag(reuse_fixp_id,on),
%       push_pp_flag(widencall,off),
    predkey_from_sg(Goal,K),
    fixpo_check_di4:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ),
%       pop_pp_flag(widencall),
    pop_pp_flag(reuse_fixp_id).
analyze(check_di5,AbsInt,_RFlag,Goal,Gv,Call,Name):-
    push_pp_flag(reuse_fixp_id,on),
    predkey_from_sg(Goal,K),
    fixpo_check_di5:query(AbsInt,K,Goal,Gv,_,Name,Call,_Succ),
    pop_pp_flag(reuse_fixp_id).

% TODO: unify with intermod_entry: entry_point/6
entry_point(AbsInt,Goal,Qv,Call,Name):-
    ( type_of_goal(exported,Goal)
    ; type_of_goal(multifile,Goal),
      % TODO: ugly hack to ignore multifile introduced (temporarily until we
      % have custom meta_predicatate for phrase?) in by modules using dcg_phrase
      % (e.g., module/2)
      \+ Goal = 'multifile:\6\call_in_module'(_,_)
    ),
    functor(Goal,F,A),
    functor(G,F,A),
    \+ entry_assertion(G,_Call,_Name),
    get_predkey(F,A,Name), % Name the unique topmost version of F/A
    varset(Goal,Qv),  
    unknown_entry(AbsInt,Goal,Qv,Call).
entry_point(AbsInt,Name,[],Call,Name):-
    setcounter(0,0),
    ( type_of_directive(initialization,Body)
    ; type_of_directive(on_abort,Body) ),
    inccounter(0,Name), % Name of directive a number
    varset(Body,Bv),
    vars_names_dict(Ds,Bv,_Ns),
    transform_clauses([(clause(Name,Body),Name)],Ds,[nr],[],AbsInt),
    empty_entry(AbsInt,Name,[],Call). % TODO: make sure that Name is right here
entry_point(AbsInt,Goal,Qv,Call,Name):-
    setcounter(1,0),
    entry_assertion(Goal,CInfo,Name0),
    ( functor(Goal,Name0,A)  % Name one possible entry version
    -> inccounter(1,C),
       make_atom([Name0,A,C],Name)
     ; Name=Name0
    ),
%       get_unify(CInfo,CInfo0,Unif),
    varset(Goal,Qv),
%       varset((Goal,Unif),Qa),
    info_to_asub(AbsInt,_approx,CInfo,Qv,Call,Goal,no).
%       analyze_unify(Unif,AbsInt,Call0,Call).
% TODO: Add here clauses for get_entry_info to merge with mod_topdown_analysis

     % get_unify([],[],[]).
% get_unify([U|CInfo],CInfo0,[U|Unif]):-
%       functor(U,=,2),!,
%       get_unify(CInfo,CInfo0,Unif).
% get_unify([I|CInfo],[I|CInfo0],Unif):-
%       get_unify(CInfo,CInfo0,Unif).


% analyze_unify([],_AbsInt,Call,Call):- !.
% analyze_unify([U|Unif],AbsInt,Call0,Call):-
%         builtin_info(U,'=/2',AbsInt,T,_,Cv),
%       varset(U,Sv),
%       project(AbsInt,Sv,_,Call0,Proj),
%       body_succ_builtin(AbsInt,T,U,Cv,Sv,_,Call0,Proj,Call1),!,
%       analyze_unify(Unif,AbsInt,Call1,Call).
    

%------------------------------------------------------------------------%
:- doc(mod_plai(Cls,Ds,Fixp,AbsInt,Time),"Performs the 
    analysis of the clauses in @var{Cls} (dictionaries of
    variables in @var{Ds}) with fixpoint algorithm @var{Fixp} and
    analysis domain @var{AbsInt}.  The analysis results are left
    in a permanent database (see @lib{plai_db}).

    The analysis uses the entry information provided by the entry
    policy selected in entry_policy preprocessing flag.").

mod_plai(Cls,Ds,Fixp,AbsInt,Stats):-
    plai_(Cls,Ds,Fixp,AbsInt,mod,Stats).

do_mod_plai(Cls,Ds,Fixp,AbsInt,TPre,TAna):-
    stat_no_store(preprocess(Fixp,AbsInt,Cls,Ds,Ps), TPre), !, % TODO: fix, move cuts deeper
    pplog(analyze_module, ['{preprocessed for ', Fixp, ' in ', TPre, ' msec.}']),
    stat_no_store(mod_topdown_analysis(AbsInt,Fixp,Ps), TAna).
%------------------------------------------------------------------------%

:- export(mod_topdown_analysis/3).
mod_topdown_analysis(AbsInt,_Fixp,_Ps) :-
    \+ get_entry_info(AbsInt,_,_), !,
    warning_message("No entries found for ~w", [AbsInt]).
% TODO: merge with topdown_analysis/3
mod_topdown_analysis(AbsInt,Fixp,Ps):-
    setcounter(1,0),
    get_entry_info(AbsInt,Goal,Call),
    varset(Goal,Gv),
    functor(Goal,F,A),
    inccounter(1,C),
    make_atom([F,A,C],Name),
    determine_r_flag(Ps,F/A,RFlag),
    ( analyze(Fixp,AbsInt,RFlag,Goal,Gv,Call,Name) -> true ),
    fail.
mod_topdown_analysis(_AbsInt,_Fixp,_Ps).

pop_pp_flags([]).
pop_pp_flags([H|T]):-
    pop_pp_flag(H),
    pop_pp_flags(T).
