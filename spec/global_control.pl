:- module(global_control,
    [
     spec_definition/8,
     spec_def_for/8,
     spec_wrt/3,
     cleanup_unfolds/0,
     locate_spec_definition/3
    ],
    [assertions, datafacts]).

:- use_package(spec(no_debug)).

:- doc(title,"A Partial Evaluator Integrated with Abstract Interpretation").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains the implementation of global
     control for partial evaluation to be used in conjunction with
     PLAI.").

:- doc(bug,"2. Multi_part_conc/4 is not exploited").
:- doc(bug,"3. The handling of abstract substitutions after applying 
      the msg should be improved"). 
:- doc(bug,"4. The handling of abstract substitutions after applying 
      make_dynamic should be improved"). 

%% DONE
%% :- doc(bug," 1. Abstract substitution has to be updated after applying the msg").

:- use_module(spec(unfold), [unfold/10]).
:- use_module(spec(homeo_emb), 
    [homeomorphic_embedded/2,
     homeomorphic_embedded_num/2,
     homeomorphic_embedded_type/2]).
:- use_module(spec(filter), [decide_predicate_filter/6]).
:- use_module(spec(unfold_times), 
    [increment_global_control_time/1, global_time_ellapsed/3]).
:- use_module(spec(debug_write_atoms)).
:- use_module(spec(generalize_emb_atoms), [decide_lc_filter_f/2, decide_generalize_atom/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).
:- use_module(ciaopp(plai/domains), [part_conc/5, call_to_entry/10, 
                    identical_proj/5,abstract_instance/5]).
:- use_module(library(compiler/p_unit/program_keys), [get_predkey/3, predkey_from_sg/2]).

:- use_module(spec(generalize_emb_atoms), [there_is_gen_hint/2]).

:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(terms), [copy_args/3]).
:- use_module(library(terms_check), 
    [ instance/2, variant/2, most_specific_generalization/3 ]).
:- use_module(library(aggregates), [findall/3, '^'/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).

:- doc(spec_def_for(Key,Sg,Sv,Proj,AbsInt,Id,NF,A),
     "@var{NF}/@var{A} is the specialized definition for @var{Sg} and
     @var{Proj}").

:- data spec_def_for/8.

:- doc(spec_wrt(Id,AbsInt,OldId), "The specialized definition for
     call pattern @var{Id} in the corresponding fact of
     @pred{complete/7} has been obtained wrt the call pattern which
     corresponds to @var{OldId} in @pred{spec_def_for/8}. Since the
     call pattern corrsponding to @var{OldId} is a generalization of
     that in @var{Id}, it has to be equal or more general, in order to
     ensure global level termination.  Note that the fact that
     @var{Id} and @var{OldId} are the same does not mean that the call
     patterns are the same since they correspond to different
     tables. They just happen to have the same identifier in both
     tables!").

:- data spec_wrt/3.

cleanup_unfolds:-
    retractall_fact(spec_def_for(_,_,_,_,_,_,_,_)),
    retractall_fact(spec_wrt(_,_,_)).

spec_definition(Sg,_Sv,_Proj,_AbsInt,_Id,Clauses,NClauses,NSg):-
    debug_write('ATOM : '), 
    debug_write_atom_nl(Sg),
    current_pp_flag(local_control,off),!,
    NClauses = Clauses,
    NSg = Sg.
spec_definition(Sg,Sv,Proj,AbsInt,Id,_Clauses,NClauses,NSg):-
    decide_gen_hint(Sg,Sv,Proj,GSg,GSv,GProj),
    do_spec_definition(GSg,GSv,GProj,AbsInt,Id,NClauses,NSg).

do_spec_definition(Sg,Sv,Proj,AbsInt,Id,NClauses,NSg):-
    pp_statistics(runtime,[GT,_]),
    current_pp_flag(part_conc,Part_Conc),
    decide_part_conc(Part_Conc,AbsInt,Sg,Sv,Proj,Sg0,Sv0,Proj0),
    current_pp_flag(global_control,Global),
    (Global == dyn ->
        make_dynamic(Sg0,Sv0,Proj0,FSg,FSv,FProj),
        reuse_definition(id,FSg,FSv,FProj,AbsInt,Id,Sg1,Sv1,Proj1,Flag,OldId)
    ;
        decide_filter_nums(Sg0,Sv0,Proj0,FSg,FSv,FProj),
        decide_predicate_filter(FSg,FSv,FProj,FFSg,FFSv,FFProj),
        reuse_definition(Global,FFSg,FFSv,FFProj,AbsInt,Id,Sg1,Sv1,Proj1,Flag,OldId)
    ),
    
    (Sg1 == FFSg ->
        debug_write_nl(iguales)
    ;
        debug_write_nl('NO IGUALES')),
    functor(Sg,F,A),
    get_predkey(F,A,Key),
    pp_statistics(runtime,[GT1,_]),
    (Flag == done ->
        debug('HECHO'),
        current_fact(spec_def_for(Key,Sg1,_Sv1,_Proj1,AbsInt,OldId,NF,A)),
        Id_wrt = OldId
%           LC_Time = 0
    ;
        debug('no hecho'),
        current_pp_flag(local_control,Unfold),
        current_pp_flag(comp_rule,SelRule),
        unfold(SelRule,Unfold,Sg1,Sv1,Proj1,AbsInt,Id,NF,A,_LC_Time),
        asserta_fact(spec_def_for(Key,Sg1,Sv1,Proj1,AbsInt,Id,NF,A)),
        Id_wrt = Id

    ),
    assertz_fact(spec_wrt(Id,AbsInt,Id_wrt)),
    get_predkey(NF,A,NSgKey),
    functor(NSg,NF,A),
    copy_args(A,Sg,NSg),
%       bagof(X, Y^X^(trans_clause(NSgKey,Y,X)),NClauses).
    findall(X, Y^X^(trans_clause(NSgKey,Y,X)),NClauses),
    global_time_ellapsed(GT1,GT,TT),
%       TT is TT0 - LC_Time,
    increment_global_control_time(TT),
    pplog(spec_module, ['{global control ',time(TT), ' msec.}']).

decide_part_conc(mono,AbsInt,Sg0,_Sv0,Proj0,Sg,Sv,Proj):-!,
    copy_term((Sg0,Proj0),(Sg1,Proj1)),
    part_conc(AbsInt,Sg1,Proj1,Sg,Proj),
    varset(Sg,Sv),
    (Sg1 \== Sg ->
        debug('CONCRETIZED: '),
        debug(Sg1),
        debug(' -> '),
        debug(Sg)
    ;
        true
    ).
decide_part_conc(multi,AbsInt,Sg0,_Sv0,Proj0,Sg,Sv,Proj):-!,
    copy_term((Sg0,Proj0),(Sg1,Proj1)),
    part_conc(AbsInt,Sg1,Proj1,Sg,Proj),
    varset(Sg,Sv),
    (Sg1 \== Sg ->
        debug('CONCRETIZED: '),
        debug(Sg1),
        debug(' -> '),
        debug(Sg)
    ;
        true
    ).
decide_part_conc(_Part_Conc,_AbsInt,Sg,Sv,Proj,Sg,Sv,Proj).

:- doc(decide_filter_nums(Sg0,Sv,Proj,FSg,Sv,Proj), "@var{FSg} is
       the result of filtering out numbers from
       @var{Sg0}. Unfortunately, if builtins are evaluated at partial
       evaluation time, homeomorphic embedding is not enough for
       ensuring global termination. An infinite number of atoms may be
       created using different numbers.").

decide_filter_nums(Sg0,Sv,Proj,FSg,Sv,Proj):-
    current_pp_flag(filter_nums,Filter),
    (Filter == on ; Filter = safe),!,
    functor(Sg0,F,A),
    functor(FSg,F,A),
    filter_nums_N(A,Sg0,FSg),
    (Sg0 \== FSg ->
        debug('FILTERED')
    ;
        true
    ).
decide_filter_nums(Sg,Sv,Proj,Sg,Sv,Proj).

filter_nums_N(0,_Sg,_FSg):-!.
filter_nums_N(A,Sg0,FSg):-
    arg(A,Sg0,Arg),
    arg(A,FSg,FArg),
    filter_nums(Arg,FArg),
    A1 is A - 1,
    filter_nums_N(A1,Sg0,FSg).

filter_nums(Arg,FArg):-
    number(Arg),!,
    (safe_number(Arg) ->
        FArg = Arg
    ;
        true).
filter_nums(Arg,FArg):-
    (var(Arg) ->
        FArg = Arg
    ;
        functor(Arg,F,A),
        functor(FArg,F,A),
        filter_nums_N(A,Arg,FArg)
    ).
    
:- data safe_number/1.

decide_gen_hint(Sg,_Sv,Proj,GSg,GSv,GProj):-
    there_is_gen_hint(Sg,GSg),!,
    varset(GSg,GSv),
    GProj = Proj. % Needs fixing!
decide_gen_hint(Sg,Sv,Proj,Sg,Sv,Proj).

reuse_definition(off,Sg,Sv,Proj,_AbsInt,_Id,NSg,NSv,NProj,Flag,_):-!, 
    Flag = notdone,
    NSg = Sg,
    NSv = Sv,
    NProj = Proj.
reuse_definition(id,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
%       current_fact(spec_def_for(Key,OldSg,_OldSv,OldProj,AbsInt,OldId,_NF,_A)),
    previous_atom(Key,AbsInt,Id,OldSg,OldProj,OldId),
    decide_identical(AbsInt,Sg,Proj,OldSg,OldProj),!,
    Flag = done,
    NSg = Sg,
    NSv = Sv,
    NProj = Proj.
reuse_definition(inst,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
%       current_fact(spec_def_for(Key,OldSg,_OldSv,OldProj,AbsInt,OldId,_NF,_A)),
    previous_atom(Key,AbsInt,Id,OldSg,OldProj,OldId),
    decide_instance(AbsInt,Sg,Proj,OldSg,OldProj),!,
    Flag = done,
    NSg = Sg,
    NSv = Sv,
    NProj = Proj.
reuse_definition(hom_emb,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
    reuse_def_emb(Key,AbsInt,Id,Sg,Sv,Proj,nonum,NSg,NSv,NProj,Flag,OldId),!.
reuse_definition(hom_emb_num,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
    reuse_def_emb(Key,AbsInt,Id,Sg,Sv,Proj,num,NSg,NSv,NProj,Flag,OldId),!.
reuse_definition(hom_emb_pt,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
    reuse_def_emb(Key,AbsInt,Id,Sg,Sv,Proj,pt,NSg,NSv,NProj,Flag,OldId),!.
reuse_definition(hom_emb_t,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
    reuse_def_emb(Key,AbsInt,Id,Sg,Sv,Proj,types,NSg,NSv,NProj,Flag,OldId),!.
reuse_definition(offline,Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    offline_generalization(Sg,Sv,Proj,Sg0,Sv0,Proj0),
    reuse_definition_offline(Sg0,Sv0,Proj0,AbsInt,Id,NSg,NSv,NProj,Flag,OldId).

reuse_definition(_,Sg,Sv,Proj,_AbsInt,_Id,NSg,NSv,NProj,Flag,_):-
    Flag = notdone,
    NSg = Sg,
    NSv = Sv,
    NProj = Proj.

offline_generalization(Sg,Sv,Proj,Sg0,Sv0,Proj0) :-
    decide_generalize_atom(Sg,Sg0),
    % MGZ:The following needs revision
    Sv0 = Sv, Proj0 = Proj.

reuse_definition_offline(Sg,Sv,Proj,AbsInt,Id,NSg,NSv,NProj,Flag,OldId):-
    predkey_from_sg(Sg,Key),
%       current_fact(spec_def_for(Key,OldSg,_OldSv,OldProj,AbsInt,OldId,_NF,_A)),
    previous_atom(Key,AbsInt,Id,OldSg,OldProj,OldId),
    decide_identical(AbsInt,Sg,Proj,OldSg,OldProj),!,
    Flag = done,
    NSg = Sg,
    NSv = Sv,
    NProj = Proj.

reuse_definition_offline(Sg,Sv,Proj,_AbsInt,_Id,NSg,NSv,NProj,Flag,_OldId):-
    Flag = notdone,
    NSg = Sg,
    NSv = Sv,
    NProj = Proj.

reuse_def_emb(Key,AbsInt,Id,Sg,_Sv,Proj,_Num,_NSg,_NSv,_NProj,Flag,OldId):-
%       current_fact(spec_def_for(Key,OldSg,_NSv,OldProj,AbsInt,OldId,_NF,_A)),
    previous_atom(Key,AbsInt,Id,OldSg,OldProj,OldId),
    decide_identical(AbsInt,Sg,Proj,OldSg,OldProj),!,
    Flag = done.
reuse_def_emb(Key,AbsInt,Id,Sg,Sv,Proj,Num,NSg,NSv,NProj,Flag,Id_wrt):-
%       current_fact(spec_def_for(Key,OldSg,_OldSv,_OldProj,AbsInt,_OldId,_NF,_A)),
    previous_atom(Key,AbsInt,Id,OldSg,_OldProj,_OldId),
    gc_is_embedded(Num,OldSg,Sg),
%       (Num = nonum ->
%           homeomorphic_embedded(OldSg,Sg)
%       ;
%           (Num = num ->
%            homeomorphic_embedded_num(OldSg,Sg)
%           ;
%               decide_lc_filter_f(OldSg,OldSg_f),
%               decide_lc_filter_f(Sg,Sg_f),
%               homeomorphic_embedded(OldSg_f,Sg_f)
%           )
%       ),
    !,
    most_specific_generalization(OldSg,Sg,NSg),
    varset(NSg,NSv),
%%%%%%%%%%%%%%%%%%%%%
%%      ord_subtract(NSv,Sv,NewVars),
%%      copy_term(Sg,CSg),
%%      varset(CSg,CSv),
%%      call_to_entry(AbsInt,Sv,Sg,CSv,CSg,not_provided,NewVars,Proj,Proj0,_),
%%      unknown_call(AbsInt,Sg,Proj0,NewVars,Proj1),
%%      append(CSv,NewVars,HvFv_u),
%%      project(AbsInt,NSv,HvFv_u,Proj1,NProj),
%%%%%%%%%%%%%%%%%%%%%
%%      call_to_entry(AbsInt,Sv,Sg,NSv,NSg,not_provided,[],Proj,NProj1,_ExtraInfo1),
%%      call_to_entry(AbsInt,OldSv,OldSg,NSv,NSg,not_provided,[],OldProj,NProj2,_ExtraInfo2),
%%      widen(AbsInt,NProj1,NProj2,NProj),
%%%%%%%%%%%%%%%%%%%%%
%%      unknown_entry(AbsInt,NSg,NSv,NProj),
%%%%%%%%%%%%%%%%%%%%%
    call_to_entry(AbsInt,Sv,Sg,NSv,NSg,not_provided,[],Proj,NProj,_ExtraInfo1), % TODO: add some ClauseKey? (JF)
    (current_fact(spec_def_for(Key,OtherSg,_OtherSv,OtherProj,AbsInt,OtherId,_,_)),
     decide_identical(AbsInt,NSg,NProj,OtherSg,OtherProj) ->
        Flag = done,
        Id_wrt = OtherId
    ;
        Flag = notdone
    ).

gc_is_embedded(nonum,OldSg,Sg) :- homeomorphic_embedded(OldSg,Sg).
gc_is_embedded(num,OldSg,Sg) :- homeomorphic_embedded_num(OldSg,Sg).
gc_is_embedded(pt,OldSg,Sg) :- 
    decide_lc_filter_f(OldSg,OldSg_f),
    decide_lc_filter_f(Sg,Sg_f),
    homeomorphic_embedded(OldSg_f,Sg_f).
gc_is_embedded(types,OldSg,Sg) :- homeomorphic_embedded_type(OldSg,Sg).

locate_spec_definition(Id,NF,A):-
    spec_wrt(Id,_,OldId),
    spec_def_for(_,_,_,_,_,OldId,NF,A).


decide_identical(AbsInt,Sg,Proj,OldSg,OldProj):-
    (current_pp_flag(abs_spec_defs,off) ->
        variant(OldSg,Sg)
    ;
        identical_proj(AbsInt,Sg,Proj,OldSg,OldProj)
    ).

decide_instance(AbsInt,Sg,Proj,OldSg,OldProj):-
    (current_pp_flag(abs_spec_defs,off) ->
        instance(Sg,OldSg)
    ;
        abstract_instance(AbsInt,Sg,Proj,OldSg,OldProj)
    ).

make_dynamic(Sg0,Sv0,Proj0,FSg,Sv0,Proj0):-
    functor(Sg0,F,A),
    functor(FSg,F,A).

:- include(global_trees).
