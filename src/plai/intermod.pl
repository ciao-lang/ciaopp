:- module(intermod,
    [
        cleanup_intermod/0,
        valid_mod_analysis/1,
        intermod_analyze/2,
        intermod_analyze/3,
        intermod_ctcheck/2,
        auto_transform/3,
        auto_simp_libs/2,
        auto_simp_libs/3,
        % scenario 5
        inductive_ctcheck/2,
        inductive_ctcheck/4,
        inductive_ctcheck_summary/3,
        % scenario 3
        auto_ctcheck_opt/2,
        auto_ctcheck_opt/3
    ],[assertions, basicmodes, nativeprops, fsyntax]).

:- use_package(dynamic). % TODO: use datafacts? dynamic is here only for asserta/1, retract/1 and the 'dead-code' part

:- use_package(spec(nomem_usage)).
:- use_module(spec(mem_usage)).

:- include(intermod_options). % intermod compilation options

%%------------------------------------------------------------------
:- doc(title, "Modular driver").
%%------------------------------------------------------------------

:- doc(stability, devel).
:- doc(author, "The Ciao Development Team").
% Improvements to support incremental analysis by:
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "This module provides intermodular analysis to CiaoPP (high-level).

Global compilation options of intermodular analysis are available in
@tt{intermod_options}. Edit this file to activate tracing or run-time checks.
").

%%------------------------------------------------------------------
:- use_module(ciaopp(plai/intermod_db)).
:- use_module(ciaopp(plai/intermod_schedule)).
:- use_module(ciaopp(plai/intermod_punit)).
:- use_module(ciaopp(plai/intermod_entry), [add_entries_to_registry/1]).
:- use_module(ciaopp(plai/intermod_ops)).

:- use_module(ciaopp(frontend_driver), [module/1,module/2,output/1,output/0]).
:- use_module(ciaopp(analyze_driver),
              [analyze/1,analyze1/2,acheck_summary/1, acheck/1, acheck/2]).
:- use_module(ciaopp(p_unit), [program/2, replace_program/2]).
:- use_module(ciaopp(plai/re_analysis), [update_ai_info_case/4]).
:- use_module(ciaopp(plai), [cleanup_plai/1]).

:- use_module(spec(spec), [simplify_specialize/6]).
:- use_module(spec(codegen), [codegen/4, codegen_af/4]).
:- use_module(ciaopp(plai/plai_db), [complete/7, cleanup_plai_db/1]).
:- use_module(ciaopp(plai/fixpo_ops), [
    complete_prev/7,
    store_previous_analysis_completes/1,
    store_previous_analysis_aux_info/1,
    reset_previous_analysis/1,
    restore_previous_analysis/1,
    compare_completes_with_prev/3,
    remove_useless_info/1
     ]).
:- use_module(ciaopp(p_unit/aux_filenames), [get_module_filename/3, just_module_name/2]).
:- use_module(ciaopp(p_unit/itf_db), [get_module_from_sg/2]).
:- use_module(ciaopp(preprocess_flags)).
:- use_module(ciaopp(p_unit/p_dump), [dump_dir/1, dump/2]).
:- use_module(ciaopp(ciaopp_log)).
:- use_module(ciaopp(raw_printer)).
% ctcheck
:- use_module(ciaopp(ctchecks/ctchecks_pred)).

% ciao libraries
:- use_module(engine(internals), [ast_filename/2]).
:- use_module(library(counters)).
:- use_module(spec(unfold_times), [global_time_ellapsed/3]).
:- use_module(library(system),
    [ delete_file/1, delete_directory/1, file_property/2,
      directory_files/2, file_exists/1]).
:- use_module(library(process)).
:- use_module(library(system_extra), [mkpath/1]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(library(compiler/c_itf), [cleanup_itf_cache/0]).
:- use_module(library(lists), [append/3]).
:- use_module(library(llists), [append/2]).
:- use_module(library(pathnames)).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(hiordlib), [maplist/3]).
:- use_module(engine(stream_basic), [absolute_file_name/7]).
:- use_module(engine(runtime_control), [push_prolog_flag/2, pop_prolog_flag/1]).
:- use_module(engine(messages_basic), [message/2]).

% statistics
:- use_module(ciaopp(analysis_stats)).

%%------------------------------------------------------------------
:- multifile dump_flags_list/2.
dump_flags_list(intermod, [entry_policy,global_scheduling,punit_boundary]).

%%------------------------------------------------------------------

:- pred cleanup_intermod #"Cleans up the internal database of the intermodular
   analysis global level.".

% TODO: this sets some pp_flags. Restrict cleaning to used fixpoints?
cleanup_intermod:-
    % get widen value
    current_pp_flag(widen, W),
    % TODO: this is done because some fixpoints change the value
    % of the widen flag during the cleanup_fixpoint operation.
    % This may cause that the modular fixpoint never finishes for
    % regtypes analysis.
    % A solution is to initialize only the fixpoint that is going
    % to be used each time
    plai_db:cleanup_plai_db(AbsInt),
    fixpo_ops:reset_previous_analysis(AbsInt),
    cleanup_plai(AbsInt), % cleans all the fixpoints
    %%
    cleanup_intermod_scheduling,
    clean_program_structure,
    cleanup_p_abs_all,
    set_pp_flag(widen, W).

:- data there_are_previous_errors/0.

%% ********************************************************************
%% Intermodular analysis with manual scheduling.
%% ********************************************************************
% TODO: this is not used, delete?
:- pred manual_analyze(+AbsInt,+FileName,+OpenMode)
   # "Performs the analysis of module @var{FileName} in the @var{AbsInt}
   abstract domain using the @em{manual} global scheduling, and sets the mode of
   the registry file of module @var{FileName} to @var{OpenMode}. @var{OpenMode}
   can take the values @code{read_write} (which allows updating the registry
   information of module @var{FileName} when other related modules are being
   analyzed) or @code{read_only} (the registry information of @var{Module} will
   not be changed unless it is reanalyzed using @code{manual_analyze/2-3}).".
manual_analyze(AbsInt,FileName,OpenMode):-
    atom(AbsInt),!,
    manual_analyze([AbsInt],FileName,OpenMode).
manual_analyze(AbsInts,FileName,OpenMode):-
    absolute_file_name(FileName, '_opt', '.pl', '.', _, Base, _),
    valid_mod_analysis(AbsInts), !,
    push_pp_flag(intermod,on),
    module(Base,_LoadInfo),
    pplog(modular, ['{Analyzing with manual_analyze: ',~~(FileName)]),
    add_main_module(Base),
    ( var(OpenMode) -> true ; change_open_mode(Base,OpenMode) ), !,
    reset_total_info,
    analyze1(AbsInts,Info),
    add_to_total_info(Info),
    gen_registry_info(quiet,_,_,_),
    save_registry_info(quiet,_SaveInfo),  %% all registry files must be saved.
    pop_pp_flag(intermod),
    set_modules_analyzed([Base]),
    pplog(modular, ['}']).

%%------------------------------------------------------------------
:- prop valid_mod_analysis(Domain) # "Succeeds if @var{Domain} is a
   valid analysis domain for modular analysis".
:- prop valid_mod_analysis(DomainList) # "Succeeds if the domains in
   @var{DomainList} are valid analysis domains for modular analysis".

valid_mod_analysis([]).
valid_mod_analysis([A|As]):- !,
    valid_mod_analysis(A),
    valid_mod_analysis(As).
valid_mod_analysis(AbsInt):-
    aidomain(AbsInt), !.
valid_mod_analysis(AbsInt):-
    message(error0, ['{Not a valid modular analysis: ',~~(AbsInt),'}']),
    fail.

:- multifile aidomain/1.  % This predicate is defined in domains.pl.

%% ********************************************************************
:- doc(section, "Intermodular fixpoint analysis").
%% ********************************************************************
intermod_analyze(AbsInt,TopLevel):-
    intermod_analyze(AbsInt,TopLevel,_Info).
intermod_analyze(AbsInt,TopLevel,Info):-
    set_modules_analyzed([]),
    current_pp_flag(mnu_modules_to_analyze, Mods),
    current_pp_flag(ext_policy, ExtPolicy),
    current_pp_flag(module_loading, LoadPolicy),
    intermod_analyze_(Mods,ExtPolicy,LoadPolicy,AbsInt,TopLevel,Info).

intermod_analyze_(current,registry,_,AbsInt,TopLevel,Info):- !,
    manual_analyze(AbsInt,TopLevel,Info).
intermod_analyze_(all,registry,one,AbsInt,TopLevel,Info):- !,
    modular_analyze(AbsInt,TopLevel,Info).
intermod_analyze_(all,registry,all,AbsInt,TopLevel,Info):- !,
    monolithic_analyze(AbsInt,TopLevel,Info).
intermod_analyze_(all,registry,threshold,_AbsInt,_TopLevel,_Info):- !,
    pplog(modular, ['threshold loading policy not implemented yet.']).
intermod_analyze_(all,registry,threshold_scc,_AbsInt,_TopLevel,_Info):- !,
    pplog(modular, ['threshold_scc loading policy not implemented yet.']).
intermod_analyze_(Mods,Ext,Load,_AbsInt,_TopLevel,_Info):-
    pplog(modular, ['Incompatible configuration:~nmnu_modules_to_analyze=',Mods,
                    '~next_policy=',Ext, '~nmodule_loading=', Load, '~n']).

%% ********************************************************************
%% Intermodular analysis with automatic scheduling.
%% ********************************************************************
:- pred modular_analyze(+AbsInt, +TopLevel, -Info)
   # "Performs the analysis of the program unit for which @var{Module} is
   the top-level module in the @var{AbsInt} abstract domain using an
   @em{automatic} global scheduling. The global scheduling to be
   used is determined by the 'global_scheduling' preprocessing flag.".
modular_analyze(AbsInt,TopLevel,Info):-
    atom(AbsInt),!,
    modular_analyze([AbsInt],TopLevel,Info).
modular_analyze(AbsInts,TopLevel,Info):-
    pp_statistics(runtime,[T1,_]),  %% total ellapsed time.
    valid_mod_analysis(AbsInts), !,
    pplog(modular, ['{Analyzing with modular_analyze: ',~~(TopLevel)]),
    reset_mem_usage,
    push_prolog_flag(gc,on), % TODO: why?
    set_main_module(TopLevel),
    push_pp_flag(intermod,auto),
    pp_statistics(runtime,[T3,_]),   %% setup time.
    compute_punit_modules(TopLevel,ModList),
    current_pp_flag(global_scheduling,Scheduling),
    setup_scheduling(Scheduling,AbsInts,TopLevel,ModList),
    pp_statistics(runtime,[T4,_]),  %% setup time.
    SetupTime is T4 - T3,
    modular_analyze_(Scheduling,AbsInts,AnInfo),
    save_registry_info(quiet,[time(SaveTime,_)]),
    pp_statistics(runtime,[T2,_]),  %% total ellapsed time.
    set_total_info(AnInfo),
    add_to_total_info([time(SaveTime,[(savereg,SaveTime)]),time(SetupTime,[(setup,SetupTime)])]),
    global_time_ellapsed(T2,T1,Ellapsed),
    add_to_total_info([time(Ellapsed,[(total_ellapsed,Ellapsed)])]),
    pop_prolog_flag(gc),
    ask_mem_usage(TotalMem,DetMem),
    ( nonvar(TotalMem) ->
        add_to_total_info([memory(TotalMem,DetMem)])
    ;   true
    ),
    get_total_info(Info0),
    add_iterations_info(Info0,Info),
    set_modules_analyzed(ModList),
    pop_pp_flag(intermod),
    pplog(modular, ['}']),
    !.

add_entries_to_registry_all([]).
add_entries_to_registry_all([AbsInt|AbsInts]) :-
    add_entries_to_registry(AbsInt),
    add_entries_to_registry_all(AbsInts).

%%------------------------------------------------------------------
increment_iterations:-
    ( retract_fact(iterations(It0)) ->
        It is It0 + 1,
        set_fact(iterations(It))
    ;   set_fact(iterations(1))
    ).

add_iterations_info(Info0,[iterations(N,[])|Info0]):-
    current_fact(iterations(N)), !.
add_iterations_info(Info0,[iterations(0,[])|Info0]).

%%------------------------------------------------------------------

modular_analyze_(Sched,AbsInts,Info):-
    reset_total_info,
    retractall_fact(there_are_previous_errors),
    ( is_naive_scheduling(Sched) ->
        do_naive_intermod(AbsInts)
    ;   do_intermod(Sched,AbsInts)
    ),
    get_total_info(Info).

:- pred do_naive_intermod/1 + not_fails.
do_naive_intermod(AbsInts):-
    current_fact(naive_pending_modules(_)), !,
    findall(CurrModBase, current_fact(naive_module_order(CurrModBase)), Modules),
    naive_analyze_modules(AbsInts,Modules),
    ( there_are_previous_errors ->
        true
    ;   do_naive_intermod(AbsInts)
    ).
do_naive_intermod(_AbsInts).

%% Analizes all modules in naive_module_order/1. Stores in
%% naive_pending_modules/1 those related modules which need
%% reanalysis.
%%
%% AbsInt can be either a domain name or a list of domains.
:- pred naive_analyze_modules/2 + not_fails.
naive_analyze_modules(_AbsInt, []) :- !.
naive_analyze_modules(_, _) :-
    there_are_previous_errors, !.
naive_analyze_modules(AbsInts, [CurrMod|Mods]) :-
    retract_fact(naive_pending_modules(CurrMod)), !,
    pplog(modular, ['{intermod: analyzing ',~~(CurrMod)]),
    module(CurrMod, Stats),
    get_stat(Stats, time(LoadTime,_)),
    add_stat(load, Stats),
    ( ( current_fact(force_analysis(CurrMod))
      ; current_pp_flag(interleave_an_check,on)
      ) ->
        push_pp_flag(entry_policy,force)
    ;   true
    ),
    increment_iterations,
    set_local_ana_modules([CurrMod]),
    add_entries_to_registry_all(AbsInts),
    ( punit_module(_, Mod), upload_typedefs_all_domains(Mod), fail ; true ),
    analyze1(AbsInts,Info),
    debug_inc_dump_dir(CurrMod),
    add_to_total_info(Info), % It adds Info to total_info.
    gen_registry_info(quiet,Callers,Imported,GenSts),
    get_stat(GenSts, time(GenRegTime,_)),
    add_stat(genreg, GenRegTime),
    pplog_registry(AbsInts,CurrMod),
    save_registry_info(quiet,[time(SaveTime,_)]),
    % IG: necessary because the module changes are updated there, move
    add_stat(savereg, SaveTime),
    add_stat_step(CurrMod),
    add_to_total_info([time(LoadTime,[(load,LoadTime)]),time(GenRegTime,[(genreg,GenRegTime)])]),
    ( ( retract_fact(force_analysis(CurrMod))
      ; current_pp_flag(interleave_an_check,on)
      ) ->
        ( pop_pp_flag(entry_policy) -> true )  % only once.
    ;   true
    ),
    add_naive_pending_modules(Callers),
    add_naive_pending_modules(Imported),
    ctcheck_module_naive(CurrMod),
    pplog(modular, ['}']),
    naive_analyze_modules(AbsInts,Mods).
naive_analyze_modules(AbsInts, [_CurrMod|Mods]):-
    naive_analyze_modules(AbsInts,Mods).

ctcheck_module_naive(Module):-
    current_pp_flag(interleave_an_check,on), !,
    acheck_info(assert_count(CTInfo),Summary),
    add_to_total_info([assert_count(Module,CTInfo)]),
    ( Summary == error ->
        message(inform, ['{Compile-time check errors found in: ', ~~(Module),'}']),
        retractall_fact(naive_pending_modules(_)),
        set_fact(there_are_previous_errors)
    ;   true
    ).
ctcheck_module_naive(_).

%%------------------------------------------------------------------
:- pred do_intermod(Scheduling, AbsInt) : atm * atm
   # "Computes the intermodular fixpoint of the analysis of the current program
   unit (given by top-level) in the @var{AbsInt} abstract domain and using
   @var{Scheduling} scheduling policy.

  @var{AbsInt} can be either a domain name or a list of domains.".

do_intermod(Scheduling,AbsInt):-
    do_intermod_one_module(Scheduling,AbsInt), !,
    do_intermod_remaining(Scheduling,AbsInt).
do_intermod(_Scheduling,_AbsInt).

do_intermod_remaining(Scheduling,AbsInt):-
    do_intermod_one_module(Scheduling,AbsInt),
    do_intermod_remaining(Scheduling,AbsInt).
do_intermod_remaining(_Scheduling,_AbsInt).

do_intermod_one_module(Scheduling,AbsInt):-
    pop(CurrMod,CurrPty),
    pplog(modular, ['{intermod: analyzing ',~~(CurrMod),' with priority ',~~(CurrPty)]),
    module(CurrMod,[time(LoadTime,_)]),
    ( current_fact(force_analysis(CurrMod)) ->
        push_pp_flag(entry_policy,force)
    ;   true
    ),
    increment_iterations,
    set_local_ana_modules([CurrMod]),
    add_entries_to_registry(AbsInt),
    ( punit_module(_, Mod), upload_typedefs_all_domains(Mod), fail ; true ),
    analyze1(AbsInt,Info),
    add_to_total_info(Info), % It adds Info to total_info.
    gen_registry_info(quiet,Callers,Imported,[time(GenRegTime,_)]),
    add_to_total_info([time(LoadTime,[(load,LoadTime)]),time(GenRegTime,[(genreg,GenRegTime)])]),
    pplog_registry(AbsInt,CurrMod),
%% jcf: following line only useful for testing output.
%% atom_concat(CurrMod,'_out.pl',CurrModOut), output(CurrModOut),
    ( retract_fact(force_analysis(CurrMod)) ->
        pop_pp_flag(entry_policy)
    ;   true
    ),
    calc_priority_callers(Scheduling,CurrPty,Callers,CallersPty),
    calc_priority_imported(Scheduling,CurrPty,Imported,ImportedPty),
    pplog(modular, ['{intermod: adding',~~(Callers),' to the priority queue.}']),
    pplog(modular, ['{intermod: adding',~~(Imported),' to the priority queue.}']),
    push(Callers,CallersPty),
    push(Imported,ImportedPty),
    ctcheck_module_intermod(CurrMod),
    pplog(modular, ['}']).

%% --------------------------------------------------------------------

ctcheck_module_intermod(Module):-
    current_pp_flag(interleave_an_check,on), !,
    acheck_summary(Result),
    ( Result == error ->
        message(inform, ['{Compile-time check errors found in: ',~~(Module),'}']),
        reset_queue,  %%Stops the intermodular algorithm.
        output
    ;   true
    ).
ctcheck_module_intermod(_).

%% --------------------------------------------------------------------

:- pred calc_priority_callers(Policy,CurrPty,Callers,CallersPty)
   : (atm(Policy), int(CurrPty), list(Callers)) => list(CallersPty)
   # "Calculates the priority of the callers modules in the priority queue,
   @var{CallersPty}, given the priority @var{CurrPty} of the current module that
   has been just analyzed, and the scheduling policy @var{Policy}.".
calc_priority_callers(depth_first,CurrPty,_Callers,CallersPty):-
    CallersPty is CurrPty-1.
calc_priority_callers(upper_first,CurrPty,_Callers,CallersPty):-
    CallersPty is CurrPty+1.
calc_priority_callers(once,_CurrPty,_Callers,none).
calc_priority_callers(abs_depth_first,_CurrPty,[],[]).
calc_priority_callers(abs_depth_first,_CurrPty,[Caller|Callers],[P|Ps]):-
    current_fact(module_depth(Caller,P)),
    calc_priority_callers(abs_depth_first,_CurrPty,Callers,Ps).

%% --------------------------------------------------------------------

:- pred calc_priority_imported(Policy,CurrPty,Imported,ImportedPty)
    : (atm(Policy), int(CurrPty), list(Imported)) => list(ImportedPty)
# "Calculates the priority of the imported modules in the priority
  queue, @var{ImportedPty}, given the priority @var{CurrPty} of the
  current module that has been just analyzed, using the scheduling
  policy @var{Policy}.".

calc_priority_imported(depth_first,CurrPty,_,ImportedPty):-
    ImportedPty is CurrPty+1.
calc_priority_imported(upper_first,CurrPty,_,ImportedPty):-
    ImportedPty is CurrPty-1.
calc_priority_imported(once,_CurrPty,_,none).
calc_priority_imported(abs_depth_first,_CurrPty,[],[]).
calc_priority_imported(abs_depth_first,_CurrPty,[IM|IMs],[P|Ps]):-
    current_fact(module_depth(IM,P)),
    calc_priority_callers(abs_depth_first,_CurrPty,IMs,Ps).

%% ********************************************************************
%% Monolithic intermodular analysis.
%% ********************************************************************

:- pred monolithic_analyze(+AbsInt,+TopLevel,-Info)
# "Performs the analysis of the program unit for which @var{Module} is
   the top-level module in the @var{AbsInt} abstract domain using a
   @em{monolithic} scheduling: all the modules in the program unit
   are loaded and analyzed simultaneously.".
monolithic_analyze(AbsInt,TopLevel,Info):-
    atom(AbsInt),!,
    monolithic_analyze([AbsInt],TopLevel,Info).
monolithic_analyze(AbsInts,TopLevel,Info):-
    pp_statistics(runtime,[T1,_]),  %% total ellapsed time.
    valid_mod_analysis(AbsInts), !,
    cleanup_intermod,
    pplog(modular, ['{Analyzing with monolithic_analyze: ',~~(TopLevel)]),
    reset_mem_usage,
    push_prolog_flag(gc,on), % TODO: why?
    add_main_module(TopLevel),
    push_pp_flag(intermod,auto),
    compute_punit_modules(TopLevel,_),
    get_punit_modules(ModList), % TODO: count execution time
    %%%%
    module(ModList,LStats),
    get_stat(LStats, time(LoadTime,_)),
    reset_total_info,
    set_local_ana_modules(ModList),
    cleanup_persistent_registry(ModList),
%    ensure_registry_current_files(quiet),
    add_entries_to_registry_all(AbsInts),
    analyze1(AbsInts,Info0),
    debug_inc_dump_dir(TopLevel),
    add_to_total_info(Info0), % It adds Info to total_info.
    %%%%
    gen_registry_info(quiet,_Callers,_Imported,[time(GenRegTime,_)]),
    % save_registry_info(quiet,[time(SaveTime,_)]),
    % ^-- IG: currently the registry of the imported module is not created, do not save it
    SaveTime = 0,
    pp_statistics(runtime,[T2,_]),  %% total ellapsed time.
    add_to_total_info([time(LoadTime,[(load,LoadTime)]),time(GenRegTime,[(genreg,GenRegTime)]),time(SaveTime,[(savereg,SaveTime)])]),
    global_time_ellapsed(T2,T1,Ellapsed),
    add_to_total_info([time(Ellapsed,[(total_ellapsed,Ellapsed)])]),
    pop_prolog_flag(gc),
    ask_mem_usage(TotalMem,DetMem), % ask_mem_usage returns DeltaMem
    ( nonvar(TotalMem) ->
        add_to_total_info([memory(TotalMem,DetMem)])
        %add_stat(itmem, memory(TotalMem,DetMem))
    ;   true
    ),
    get_total_info(Info),
    add_stat(load, LStats),
    add_stat(genreg, GenRegTime),
    add_stat(savereg, SaveTime),
    add_stat_step(TopLevel),  % There will be one step only
    %%
    pop_pp_flag(intermod),
    set_modules_analyzed(ModList),
    pplog(modular, ['}']).

debug_inc_dump_dir(CurrMod) :-
    dump_dir(DumpDir), !,
    ( iterations(N) -> true ; N = 1), % 1 for monolithic analysis
    atom_number(AN,N),
    path_basename(CurrMod, Mod),
    atom_concat(Mod,'_', CM1),
    atom_concat(CM1,AN, CM3),
    atom_concat(CM3,'.dump_inc',Name1),
    path_concat(DumpDir,Name1,DumpName),
    dump(DumpName,[incremental]).
debug_inc_dump_dir(_). % if the dump directory is not set, do not dump


%% ********************************************************************
:- doc(section, "Intermodular fixpoint checking (certificate)").
%% ********************************************************************
%%    registry must have reached a fixpoint!!!!!!!
% NOT reviewed by IG
:- pred auto_check(+AbsInt,+TopLevel) # "After using @pred{modular_analyze/2},
   this predicate allows checking the results of the analysis. Generates
   internal (@code{complete/7}) information for all the modules in the program
   unit @var{TopLevel}, and stores it in memory in order to compare it with the
   results of @pred{monolithic_analyze/2}.".
auto_check(AbsInt,TopLevel):-
    atom(AbsInt),  % Only one analysis domain is considered.
    valid_mod_analysis(AbsInt), !,
    cleanup_intermod,
    pplog(modular, ['{Generating check info for program unit: ',~~(TopLevel)]),
    set_main_module(TopLevel),
    push_pp_flag(intermod,auto),
    push_pp_flag(entry_policy,force),
    push_pp_flag(dump_pp,off),
    compute_punit_modules(TopLevel,_),
    get_punit_modules(ModList),
    retractall_fact(complete_prev(_,_,_,_,_,_,_)),
    push_pp_flag(reuse_fixp_id,on),
    fixpo_ops:reset_previous_analysis(AbsInt),
    auto_check_modules(AbsInt,ModList), %% reanalyzes all modules' entries.
    %%
    %% Checking that completes are equal to those computed with monolithic_analyze.
    module(ModList),
    fixpo_ops:restore_previous_analysis(AbsInt),   %% restores needed types. module/1 removes them.
    set_local_ana_modules(ModList),
    add_entries_to_registry(AbsInt),
    analyze1(AbsInt,_Info),
    remove_useless_info(AbsInt),
%       compare_completes_with_prev(AbsInt,Flag,'='),
    compare_completes_with_prev(AbsInt,Flag,'>='),
    ( var(Flag) ->
        pplog(modular, ['Comparison with monolithic analysis completed successfully.'])
    ;
        message(inform, ['Comparison with monolithic analysis has not succeeded. See previous messages.'])
    ),
    %%
    pop_pp_flag(reuse_fixp_id),
    pop_pp_flag(dump_pp),
    pop_pp_flag(entry_policy),
    pop_pp_flag(intermod),
    pplog(modular, ['}']).

% checking_fixpoint(check_di).

auto_check_modules(_AbsInt,[]).
auto_check_modules(AbsInt,[M|Ms]):-
    auto_check_one_module(AbsInt,M),
    auto_check_modules(AbsInt,Ms).

auto_check_one_module(AbsInt,File):-
    absolute_file_name(File, '_opt', '.pl', '.', _, BaseAbs, _),
    just_module_name(BaseAbs,Module),
    pplog(modular, ['{generating check info for module: ',~~(BaseAbs)]),
%jcf (to save memory; the process will be slower).
%jcf    cleanup_p_abs_all,
    module(BaseAbs),
    fixpo_ops:restore_previous_analysis(AbsInt),   %% restores needed types (module/1 removes them)
    %
    set_local_ana_modules([BaseAbs]),
    add_entries_to_registry(AbsInt),
    analyze1(AbsInt,_),
    remove_useless_info(AbsInt),
    gen_registry_info(quiet,_,_),
    filter_completes(AbsInt,Module),
    fixpo_ops:store_previous_analysis_aux_info(AbsInt), %% Stores types of previous analyses.
    fixpo_ops:store_previous_analysis_completes(AbsInt), %%Stores info of latest analysis.
    !.

filter_completes(AbsInt,Module):-
    current_fact(complete(_A,AbsInt,Sg,_C,_D,_E,_F),Ref),
    get_module_from_sg(Sg,Module0),
    Module \= Module0,
    Module0 \= multifile,
    module_is_processable(Module0),
    erase(Ref),
    fail.
filter_completes(_AbsInt,_Module).

%% ******************************************************************
:- doc(section, "Intermodular program transformation").
%% Modular program transformations (for specialization)
%% ******************************************************************
% NOT reviewed by IG
:- pred auto_transform(+AbsInt,+Trans,+TopLevel)
# "Performs transformation @var{Trans} of the program unit which has
  @var{TopLevel} as top-level module, using @var{AbsInt} to get
  information about the program.".
auto_transform(AbsInt,Trans,TopLevel):-
    auto_transform_(AbsInt,Trans,TopLevel,_Info).

auto_transform_(AbsInt,Trans,TopLevel,Info):-
    valid_transformation(Trans), !,
    cleanup_intermod,
    pplog(modular, ['{Transforming with auto_transform: ',~~(TopLevel)]),
    set_main_module(TopLevel),
    push_pp_flag(intermod,auto),
    push_pp_flag(entry_policy,force),
    %%
    get_all_module_cycles(TopLevel,CycleList),
    pp_statistics(runtime,[T1,_]),
    auto_transform_cycles(CycleList,AbsInt,Trans),
    pp_statistics(runtime,[T2,_]),
    global_time_ellapsed(T2,T1,Ellapsed),
    Info = [time(Ellapsed,[(transform,Ellapsed)])],
    save_registry_info(quiet,_SaveInfo),
    %%
    pop_pp_flag(entry_policy),
    pop_pp_flag(intermod),
    pplog(modular, ['}']).

valid_transformation(Trans):-
    transformation(Trans), !.
valid_transformation(Trans):-
    message(error0, ['{Not a valid transformation: ',~~(Trans),'}']),
    fail.

:- prop transformation(Transformation)
    # "@var{Transformation} is a valid transformation identifier.".
:- multifile transformation/1.

%% ---------------------------------------------------------------------------

auto_transform_cycles([], _AbsInt,_Trans) :- !.
auto_transform_cycles([Cycle|CycleList], AbsInt,Trans):-
    transform_one_cycle(AbsInt,Trans,Cycle),
    auto_transform_cycles(CycleList,AbsInt,Trans).

transform_one_cycle(AbsInt,Trans,[Base]):- !,
    transform_one_module(AbsInt,Trans,Base,_Changed).
transform_one_cycle(AbsInt,Trans,Cycle):-
    transform_fixpoint(AbsInt,Trans,Cycle).

transform_fixpoint(AbsInt,Trans,Cycle):-
    transform_module_list(AbsInt,Trans,Cycle,Changed),
    ( Changed = yes ->
        transform_fixpoint(AbsInt,Trans,Cycle)
    ;   true
    ).

transform_module_list(_AbsInt,_Trans,[],no) :- !.
transform_module_list(AbsInt,Trans,[Base|Bases],Changed):-
    transform_one_module(AbsInt,Trans,Base,Changed0),
    ( Changed0 == yes ->
        Changed = yes
    ;   Changed = Changed1
    ),
    transform_module_list(AbsInt,Trans,Bases,Changed1).

transform_one_module(AbsInt,Trans,File,Changed):-
    absolute_file_name(File, '_opt', '.pl', '.', _, BaseAbs, _),
    pplog(modular, ['{intermod: transforming ',~~(BaseAbs),'}']),
%jcf%-very special cases: basiccontrol.pl, etc.
    just_module_name(BaseAbs,Mod),
    ( module_not_transformable(Mod) ->
        pplog(modular, ['{intermod: Module not transformable: ',~~(BaseAbs),'}'])
    ; registry_is_empty(AbsInt,Mod,BaseAbs) ->
        pplog(modular, ['{intermod: Module does not need transformation: ',~~(BaseAbs),'}'])
    ;
        module(BaseAbs),
        set_local_ana_modules([BaseAbs]),
        add_entries_to_registry(AbsInt),
        analyze1(AbsInt,_),
        gen_registry_info(quiet,_Callers,_Imported),
        %    Program must be re-read.
        program(Cls2,Ds2),
        get_spec_info_imported,
        transform_(Trans,AbsInt,Cls2,Ds2,BaseAbs,Changed),
        % Missing: replacement of specialized versions in .reg files!!
        save_registry_info(quiet,BaseAbs,_SaveInfo),
        atom_concat(BaseAbs,'_opt.pl',OutFile),
        output(OutFile)
    ),
    !.

%KLUDGE!!
module_not_transformable(basiccontrol).
%module_not_transformable(internals).

transform_(Trans,AbsInt,Cls,Ds,BaseAbs,Changed):-
    simpspec_(Trans,AbsInt,Cls,Ds,TmpCls,TmpDs),
    update_spec_info(BaseAbs,Changed),
    update_ai_info_case(TmpCls,TmpDs,NewCls,NewDs),
    replace_program(NewCls,NewDs).

%%This pred has been taken and adapted from driver.pl.
simpspec_(vers,_AbsInt,_Cls,_Ds,_NewCls,_NewDs):- !,
    message(inform, ['{vers not implemented yet in auto_transform/4}']),
    fail.
simpspec_(codegen,AbsInt,Cls,Ds,NewCls,NewDs):- !,
    ( current_pp_flag(local_control,off) ->
        NewCls = Cls,
        NewDs = Ds
    ;
        codegen(AbsInt,NewCls,NewDs,_Info)
    ).
simpspec_(codegen_af,AbsInt,Cls,Ds,NewCls,NewDs):- !,
    ( current_pp_flag(local_control,off) ->
        NewCls = Cls,
        NewDs = Ds
    ;
        codegen_af(AbsInt,NewCls,NewDs,_Info)
    ).
simpspec_(Spec,AbsInt,Cls,Ds,NewCls,NewDs):-
    simplify_specialize(AbsInt,Spec,Cls,Ds,NewCls,NewDs).

%% ******************************************************************
:- doc(section, "Intermodular compile-time checking.").
%% ******************************************************************

:- pred intermod_ctcheck(+AbsInts,+Modules) + not_fails
   #"Assuming that modular fixpoint already reached. Only supporting ctchecks of
    pred assertions (not program point)".
% reviewed by IG
intermod_ctcheck(AbsInts,Modules) :-
    current_pp_flag(module_loading,LoadPolicy),
    current_pp_flag(ct_modular,CTModPolicy),
    stat_no_store(intermod_ctcheck_(AbsInts,Modules,LoadPolicy,CTModPolicy), CTime),
    pplog(ctchecks, ['{(intermod) assertions checked in ',time(CTime), ' msec.}']).

% monolithic analysis, ctcheck all modules (analysis already loaded)
intermod_ctcheck_(AbsInts,_Modules,all,all) :- !,
    acheck(AbsInts).
% monolithic analysis, ctcheck only `Modules` (analysis already loaded)
intermod_ctcheck_(AbsInts,Modules,all,curr_mod) :- !,
    maplist(just_module_name, Modules, ModNames),
    acheck(AbsInts,ModNames).
% modular analysis, ctcheck all modules
intermod_ctcheck_(AbsInts,_Modules,one,all) :- !,
    get_punit_modules(ModList),
    modular_ctcheck(ModList,AbsInts).
% modular analysis, ctcheck only `Modules`
intermod_ctcheck_(AbsInts,Modules,one,curr_mod) :- !,
    modular_ctcheck(Modules,AbsInts).

modular_ctcheck([], _AbsInts).
modular_ctcheck([Module|Modules], AbsInts) :-
    module(Module,_LoadInfo),
    pplog(modular, ['{(intermod) analyzing for ctcheck: ',~~(Module)]),
    set_local_ana_modules([Module]),
    analyze1(AbsInts,_Info),
    pplog(modular, ['}']),!,
    just_module_name(Module, ModName),
    simplify_assertions_mods(AbsInts,[ModName]),
    modular_ctcheck(Modules, AbsInts).

% -----------------------------------------------------------------------------
:- pred auto_ctcheck_opt(+AbsInt,+TopLevel)
# "Performs CT assertion checking of the program unit which has
  @var{TopLevel} as a top-level module, using @var{AbsInt} to get
  information about the program (exploits order of the modules).".
% NOT reviewed by IG
:- doc(bug,"auto_ctcheck_opt/2-3 does modify the source code of
    program modules.  This issue can only be solved when _opt.pl
    files are handled properly.").

auto_ctcheck_opt(AbsInt, TopLevel) :-
    auto_ctcheck_opt(AbsInt, TopLevel,_Info).

auto_ctcheck_opt(AbsInt, TopLevel, [(time,Time),Info]) :-
    valid_mod_analysis(AbsInt),!,
    cleanup_intermod,
    pplog(modular, ['{Modular-based assertion checking with auto_ctcheck_opt: ',~~(TopLevel)]),
%jcf%   copy_sources,
    push_pp_flag(intermod,auto),
    push_pp_flag(entry_policy,force),
    TopLevel = CopyTopLevel,
%jcf%   modular_analyze(AbsInt, CopyTopLevel),
    pp_statistics(runtime,[T1,_]),
    set_main_module(CopyTopLevel),
    get_all_module_cycles(CopyTopLevel, ModuleLList),
    append(ModuleLList, ModuleList),
    auto_ctcheck_opt_(ModuleList, AbsInt, TopLevel, Info),
    pop_pp_flag(entry_policy),
    pop_pp_flag(intermod),
    pp_statistics(runtime,[T2,_]),
    Time is T2 - T1,
    pplog(modular, ['}']).

auto_ctcheck_opt_([], _AbsInt, _TopModule, assert_count([])).
auto_ctcheck_opt_([Module|Modules], AbsInt, TopModule, assert_count(Info)) :-
%       absolute_file_name(FileName, '_opt', '.pl', '.', _, Base, _),
    module(Module,_LoadInfo),
    pplog(modular, ['{Analyzing for auto_ctcheck: ',~~(Module)]),
    set_main_module(TopModule),
%       push_pp_flag(entry_policy,all),
    cleanup_p_abs,
    set_local_ana_modules([Module]),
    add_entries_to_registry(AbsInt),
    analyze1(AbsInt,_Info),
    pplog(modular, ['}']),!,
    acheck_info(assert_count(Info1),_),
    atom_concat(Module,'.pl',Module_pl),
    output(Module_pl),
%       atom_concat(Module,'.ast',Module_ast),
    absolute_file_name(Module, '_opt', '.pl', '.', _, BaseAbs, _),
    ast_filename(BaseAbs, Module_ast),
    ( file_exists(Module_ast) ->
      delete_file(Module_ast)
    ; true
    ),
    auto_ctcheck_opt_(Modules, AbsInt, TopModule, assert_count(Info2)),
    combine_info(Info1, Info2, Info).

% -----------------------------------------------------------------------------

inductive_ctcheck_summary(AbsInt,TopLevel,ERR):-
    inductive_ctcheck(AbsInt,TopLevel,_Info,ERR).
% NOT reviewed by IG
inductive_ctcheck(AbsInt,TopLevel):-
    inductive_ctcheck(AbsInt,TopLevel,_Info,_ERR).

inductive_ctcheck(AbsInt,TopLevel,[(time,Time),Info],ERR):-
%       valid_mod_analysis_all(AbsInt), !,
    pplog(modular, ['{Inductive assertions checking in : ',~~(TopLevel)]),
    compute_punit_modules(TopLevel,_),
    get_punit_modules(ModList),
    push_pp_flag(intermod, off),
    pp_statistics(runtime,[T1,_]),
    ind_ctcheck_(AbsInt, ModList, Info,ERR),
    pop_pp_flag(intermod),
    pplog(modular, ['}']),
    pp_statistics(runtime,[T2,_]),
    Time is T2 - T1,
    set_modules_analyzed(ModList).

ind_ctcheck_(_AbsInt, [], assert_count([]),ok).
ind_ctcheck_(AbsInt, [Module|Modules], assert_count(Info),ERR) :-
    module(Module),
    set_local_ana_modules([Module]),
    analyze_list(AbsInt), !,
    acheck_info(assert_count(Info1),ERR1),
    output,
    ind_ctcheck_(AbsInt, Modules, assert_count(Info2),ERR2),
    combine_info(Info1, Info2, Info),
    combine_summ(ERR1,ERR2,ERR).

combine_summ(ok,ok,OK) :- !, OK = ok.
combine_summ(error,_,E) :- !, E=error.
combine_summ(_,error,E) :- !, E=error.
combine_summ(_,_,warning).

combine_info(I, [], I) :- !.
combine_info([], I, I) :- !.
combine_info([(C,V)|Is],[(C,V1)|Is1],[(C,V2)|Is2]) :-
    V2 is V + V1,
    combine_info(Is, Is1, Is2).

analyze_list([]).
analyze_list([A|As]):-
    analyze1(A,_),
    analyze_list(As).

% -----------------------------------------------------------------------------

acheck_info(Info,Summary) :-
    setcounter(pp_checked_c,0),
    setcounter(pp_check_c,0),
    setcounter(pp_false_c,0),
    setcounter(simp_checked_c,0),
    setcounter(simp_check_c,0),
    setcounter(simp_false_c,0),
    setcounter(pp_checked_s,0),
    setcounter(pp_check_s,0),
    setcounter(pp_false_s,0),
    setcounter(simp_checked_s,0),
    setcounter(simp_check_s,0),
    setcounter(simp_false_s,0),
    setcounter(simp_true_s,0),
    acheck_summary(Summary),
    getcounter(pp_checked_c,PPCheckedC),
    getcounter(pp_check_c,PPCheckC),
    getcounter(pp_false_c,PPFalseC),
    getcounter(simp_checked_c,SimpCheckedC),
    getcounter(simp_check_c,SimpCheckC),
    getcounter(simp_false_c,SimpFalseC),
    getcounter(pp_checked_s,PPCheckedS),
    getcounter(pp_check_s,PPCheckS),
    getcounter(pp_false_s,PPFalseS),
    getcounter(simp_checked_s,SimpCheckedS),
    getcounter(simp_check_s,SimpCheckS),
    getcounter(simp_false_s,SimpFalseS),
    getcounter(simp_true_s,SimpTrueS),
    Info = assert_count([(pp_checked_c,PPCheckedC),
            (pp_check_c,PPCheckC),
            (pp_false_c,PPFalseC),
            (simp_checked_c,SimpCheckedC),
            (simp_check_c,SimpCheckC),
            (simp_false_c,SimpFalseC),
            (pp_checked_s,PPCheckedS),
            (pp_check_s,PPCheckS),
            (pp_false_s,PPFalseS),
            (simp_checked_s,SimpCheckedS),
            (simp_check_s,SimpCheckS),
            (simp_false_s,SimpFalseS),
            (simp_true_s,SimpTrueS)]).


get_modules_regnames([],[]).
get_modules_regnames([Mod|ModList],[Reg|RegList]):-
    get_module_filename(reg,Mod,Reg),
    get_modules_regnames(ModList,RegList).
%%-------------------------------------------------------------------

delete_files(FileList):-
    list(FileList), !,
    delete_files_('.',FileList).
delete_files(Dir):-
    directory_files(Dir,Files),
    delete_files_(Dir,Files).

delete_files_(_Dir,[]) :- !.
delete_files_(Dir,['.'|Files]):- !,
    delete_files_(Dir,Files).
delete_files_(Dir,['..'|Files]):- !,
    delete_files_(Dir,Files).
delete_files_(Dir,[File|Files]):-
    ( path_is_absolute(File) ->
        File = AbsFile
    ;
        path_concat(Dir,File,AbsFile)
    ),
    ( file_exists(AbsFile) ->
        ( file_property(AbsFile,type(directory)) ->
            delete_files(AbsFile),
            delete_directory(AbsFile)
        ;
            pplog(modular, ['{Erasing ',~~(AbsFile),'}']),
            delete_file(AbsFile)
        )
    ;   true
    ),
    delete_files_(Dir,Files).

copy_file(FileSpec,TargetDir):-
    process_call(path(cp),[FileSpec,TargetDir],[]).

%---------------------------------------------------------------------

delete_files_type(Dir,Ext):-
    directory_files(Dir,Files),
    delete_files_type_(Dir,Ext,Files).

delete_files_type_(_Dir,_Ext,[]).
delete_files_type_(Dir,Ext,[File|Files]):-
    absolute_file_name(File,'',Ext,Dir,AbsFile,_,_),
    ( file_exists(AbsFile) ->
        delete_file(AbsFile)
    ;   true
    ),
    delete_files_type_(Dir,Ext,Files).

%% ******************************************************************
%% dead-code elimination for libraries.
%% ******************************************************************
% NOT reviewed by IG
:- doc(bug,"The code for auto_simp_libs/2-3 is still under rough
    development.").

:- pred auto_simp_libs(+TopLevel,+Dir)
# "Generates a copy of the program represented by @var{TopLevel} and
   the libraries used (except those in @tt{engine}) in @var{Dir}, and
   removes dead-code from both user modules and libraries.".

auto_simp_libs(TopLevel,Dir0):-
    auto_simp_libs(TopLevel,Dir0,_Info).

auto_simp_libs(TopLevel,Dir,Info):-
    cleanup_intermod,
    file_exists(Dir), !,
    pplog(modular, ['{Processing with auto_simp_libs: ',~~(TopLevel)]),
    set_main_module(TopLevel),
    pplog(modular, ['{Removing all files in ',~~(Dir),'}']),
    push_pp_flag(intermod,auto),
    push_pp_flag(entry_policy,force),
    push_pp_flag(punit_boundary,on),
%
    delete_files(Dir),
    %           cleanup_itf_cache,
    get_punit_modules(ModList),
    get_punit_included_files(InclList),
    pplog(modular, ['Copying library files to ',~~(Dir)]),
    copy_modules(ModList,Dir,TargetList),
    copy_modules(InclList,Dir,_InclTargetList),
    get_modules_regnames(TargetList,RegList),
    delete_files(RegList),
    asserta(library_directory(Dir)),
    atom_concat(Dir,'/engine',DirEngine),
    asserta(file_search_path(engine,DirEngine)),
    get_new_base(Dir,TopLevel,NewTopLevel),
    cleanup_itf_cache,
    modular_analyze(pdb,NewTopLevel,Info0),
    %           monolithic_analyze(pdb,NewTopLevel),
    auto_transform_(pdb,simp,NewTopLevel,Info1),
    append(Info0,Info1,Info),
    retract(library_directory(Dir)),
    retract(file_search_path(engine,DirEngine)),
    pop_pp_flag(punit_boundary),
    pop_pp_flag(entry_policy),
    pop_pp_flag(intermod),
    pplog(modular, ['}']).
auto_simp_libs(_TopLevel,Dir,_Info):-
    pplog(modular, ['Directory does not exist: ',~~(Dir)]).

copy_modules([],_,[]).
copy_modules([Mod|ModList],Dir,[TargetMod|TargetModList]):-
    get_module_filename(pl,Mod,FileName),
    pplog(modular, ['{Copying: ',~~(FileName), '}']),
    copy_lib_subdir(Dir,FileName,SubDir),
    get_new_base(SubDir,Mod,TargetMod),
    copy_modules(ModList,Dir,TargetModList).

% If FileName (absolute file name) is in a subdirectory of a library directory, then the
% subdir must be reproduced in Dir. Returns SubDir, the absolute path of
% the subdirectory in Dir.
% If FileName is not in a library directory, it is copied directly to Dir, and Dir is
% returned as third argument.
copy_lib_subdir(Dir,FileName,SubDir):-
    get_lib_subdir0(FileName,SubDir0),
    !,
    path_concat(Dir,SubDir0,SubDir),
    mkpath(SubDir),
    copy_file(FileName,SubDir).
copy_lib_subdir(Dir,FileName,Dir):-
    copy_file(FileName,Dir).

:- dynamic library_directory/1.
:- multifile library_directory/1.
:- multifile file_search_path/2.
:- dynamic file_search_path/2.
get_lib_subdir0(FileName,SubDir):-
    library_directory(LibDir0),
    path_concat(LibDir0,SubDirFile,FileName),
    path_basename(FileName,NoPathFile),
    atom_concat(SubDir,NoPathFile,SubDirFile),
    !.

get_new_base(Dir,Mod,TargetMod):-
    just_module_name(Mod,ModName),
    absolute_file_name(ModName,'','.pl',Dir,_,TargetMod,_).

%%------------------------------------------------------------------
:- doc(section, "Debugging predicates").

pplog_registry(_AbsInt,ModPath) :-
    path_basename(ModPath,Mod),
    ( member(intermod_reg, ~current_pp_flag(pplog)) -> true ; fail),
    pplog(intermod_reg, ['{']),
    pplog(intermod_reg,['It ', ~~(~iterations), ' ----------', 'Registry updated with ',~~(Mod)]),
    show_registry_info,
    pplog(intermod_reg, ['}']),
    fail.
pplog_registry(_,_) :-
    ( member(intermod_dump, ~current_pp_flag(pplog)) -> true ; fail),
    pplog(intermod_dump, ['{']),
    pplog(intermod_reg,['It ', ~~(~iterations), ' ----------']),
    show_analysis,
    pplog(intermod_dump, ['}']),
    fail.
pplog_registry(_,_).
