:- module(p_abs,[
    cleanup_p_abs/0,
    cleanup_p_abs_all/0,
    gen_registry_info/3,
    gen_registry_info/4,
    save_registry_info/2,
    save_registry_info/3,
    update_spec_info/2,
    get_spec_info_imported/0,
    cleanup_persistent_registry/1,
    %%%%%%%%%%%%%%%%%%%%%%% LOW-LEVEL FILE ACCESS PRIMITIVES
    ensure_registry_file/3, % (read and patch registry)
    read_registry_file/3, % TODO:{JF2} NOTE THAT THIS ONE DOES NOT PATCH!!!
%       reread_registry_file/3,
    write_registry_file/3,
    registry/3,
    %%%%%%%%%%%%%%%%%%%%%%% 
    get_imported_modules/0,
    get_imported_module_base/2,
    imported_module/2,
    registry_headers/2,
    add_to_imdg_list/4,
    add_changed_module/5,
    open_mode/3,
    change_open_mode/2,
    may_be_improved_mark/2,
    not_valid_mark/2,
%%%intermodule-graph
    get_modules_to_analyze/3,
    get_all_modules/2,
    get_all_modules/3,
    get_all_module_cycles/2,
    get_all_modules_depth/2,
    get_module_from_sg/2,
    recover_from_invalid_state/2,
    propagate_invalid_info/3,
%%%intermodule-graph
    module_is_processable/1,
    registry_is_empty/3,
%%%Resource intermodule-analysis (JNL)
    get_imported_calls/1 % used only in resources/intermod
 ],[assertions,regtypes,basicmodes,isomodes,datafacts,hiord]).

:- use_module(engine(hiord_rt), [call/1]). % TODO: review uses here

:- use_package(spec(nomem_usage)). % IG: comment to get memory statistics

% Ciao libraries %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(library(sort)).
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(read),   [read/2]).
:- use_module(library(write),  [writeq/2]).
:- use_module(library(system), [modif_time0/2, file_exists/1,
    working_directory/2]).
:- use_module(library(system_extra), [del_file_nofail/1]).
:- use_module(library(pathnames),  [path_splitext/3]).
:- use_module(library(bundle/bundle_paths), [reverse_bundle_path/3]).
:- use_module(library(aggregates), [findall/3, setof/3, '^'/2]).
:- use_module(spec(modular_spec), [dyn_abs_spec/5]).
:- use_module(library(compiler/c_itf), 
    [false/1, process_files_from/7, uses/2, includes/2]).
:- use_module(library(assertions/c_itf_props)).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(ctrlcclean), [ctrlc_clean/1]).
:- use_module(library(errhandle), [error_protect/2]).
:- use_module(engine(messages_basic), [message/2]).

% CiaoPP libraries %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(ciaopp(p_unit/itf_db), [current_itf/3, curr_file/2, exports/2]).
:- use_module(ciaopp(infer/infer_db), [domain/1]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).
:- use_module(ciaopp(plai/plai_db),   [complete/7, get_parent_key/4]).
:- use_module(ciaopp(plai/domains),   [identical_proj/5, less_or_equal_proj/5, abs_sort/3]).
:- use_module(ciaopp(p_unit/auxinfo_dump), [
    acc_auxiliary_info/2,
    dump_auxiliary_info/1,
    is_dump_auxiliary_fact/1,
    imp_auxiliary_info/4,
    restore_auxiliary_info/2]).
:- use_module(ciaopp(p_unit/aux_filenames), [
    get_module_filename/3,
    just_module_name/2,
    is_library/1,
    get_loaded_module_name/3]).
:- use_module(ciaopp(p_unit/program_keys), [
    decode_litkey/5, predkey_from_sg/2, get_predkey/3]).
:- use_module(ciaopp(plai/tarjan), [step2/2]).

:- use_module(spec(spec_multiple), [publish_pred_name/2, get_version_name/4]).

:- use_module(ciaopp(plai/incanal/incanal_db),
    [add_changed_registry/4, clean_incanal_mod_data/0]).
:- use_module(ciaopp(analysis_stats), [stat_no_store/2]).

:- use_module(ciaopp(plai/intermod), [top_level/1]). % IG added for loading bundles

% :- doc(bug,"Fast read/write must replace term-read/write.").
:- doc(bug,"auxiliary files version must be handled correctly.").
:- doc(bug,"Success information cannot be multivariant.").
:- doc(bug, "Unify ASubs and Subs (they mean Abstract Substitutions)").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% JUST FOR TESTING %%%%%%%%%%%%%%%%%%%%%%
:- use_module(library(fastrw), [fast_read/1, fast_write/1, fast_read/2, fast_write/2]).
:- use_module(ciaopp(plai/intermod_entry), [check_curr_entry_id/1, curr_entry_id/1]).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7]).
% IG: Added for keeping track of the changes in the registry

% A 'complete' is an element of the local answer table.
% A 'registry' is an element of the global answer table.

% TODO: create a package that given a regtype and some indexing annotations
%   create these predicates?

:- data program_module_base_/2.
% IG: For storing module bases independently of the itf_db (erased each
% time a module is loaded otherwise)
add_program_module_base(Mod, _) :-
    program_module_base_(Mod, _), !.
add_program_module_base(Mod, File) :-
    get_imported_module_base_name(File, Mod, Base),
    assertz_fact(program_module_base_(Mod, Base)).

program_module_base(Mod, Base) :-
    program_module_base_(Mod, Base), !.

:- regtype regdata_type/1
    #"Regular type to store the semantic information of a
     predicate in a registry. It has the form
     @tt{regdata(Id,AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,Mark)}
     where:

    @begin{itemize}
    @item @tt{Id}: @bf{Unique} Id for that @tt{Sg}:@tt{Call}.
    @item @tt{AbsInt}: Abstract domain of the information.
    @item @tt{Sg}: Exported goal.
    @item @tt{Call}: Call pattern of the exported goal.
    @item @tt{Succ}: Success pattern for @tt{Sg}:@tt{Call}.
    @item @tt{Spec}: Abstract specialization information.
    @item @tt{Imdg}: List of @tt{P:CP} that may produce a call to
       @tt{Sg:Call} exported in other modules.
    @item @tt{Chdg}: List of @tt{P:CP} to imported predicates.
    @item @tt{Mark}: Determines whether the value of @tt{Succ}
       can/must be improved (depending on the success policy).
    @end{itemize}".
regdata_type(regdata(_Id, _AbsInt,_Sg,_Call,_Succ,_Spec,_Imdg,_Chdg,_Mark)).

:- pred registry(Key,Module,Registry) :: atm * atm * regdata_type
# "Data predicate to locally store information about the registry of
  one or several modules. @var{Module} is the name of the module for
  which @var{Registry} is an entry in the registry file. It
  corresponds to the @em{global answer table} as it is described in
  @cite{mod-an-spec_tr_2003}, or other auxiliary information (e.g.,
  types).".

:- data registry/3.

add_registry(Module, Reg) :-
    ( Reg = regdata(_Id, _AbsInt,Sg,_Call,_Succ,_Spec,_ImdgList,_,_Mark) ->
        predkey_from_sg(Sg, SgKey)
    ; SgKey = none %% It has no key!! % TODO: does it make sense?; throw exception if code never reaches this point
    ),
    assertz_fact(registry(SgKey,Module,Reg)).

regdata_set_mark(OldReg, Mark, NewReg) :-
    OldReg = regdata(Id, AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,_),
    NewReg = regdata(Id, AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,Mark).

%% --------------------------------------------------------------------

:- export(typedb/2).
:- pred typedb(Module,TypeDef) :: atm * term
# "Data predicate to locally store information about the types used in
  the registry of one or several modules. @var{Module} is the name of
  the module for which the type definition @var{TypeDef} is referenced
  in the registry file. The original definition of @var{TypeDef} may
  not reside in @var{Module}, but in a related module.".
:- data typedb/2.

%% :- pred typedef_already_loaded(Module) : atm
%%
%% # "Succeeds if the type definitions for module @var{Module} have been
%%   already uploaded to ciaopp (by means of @code{dumper} predicates).".
%%
%% :- data typedef_already_loaded/1.

%% --------------------------------------------------------------------

:- pred registry_headers(Module,HeaderTerm) :: atm * term
# "@var{HeaderTerm} is a term read from the registry header of module
  @var{Module}. Data predicate to store the header terms of every
  registry file read. The list of registry header terms depends on the
  registry file version, and is stored in
  @tt{registry_header_format/2}".
:- data registry_headers/2.

%% --------------------------------------------------------------------

:- pred imported_module(Module,Base) :: atm * atm
# "Enumerates the modules imported by the current module".
:- data imported_module/2.

:- pred caller_module(Module,BaseName) :: atm * atm
# "List of caller modules to be processed.".
:- data caller_module/2.

:- pred changed_module(Module,Base,SourceModule,Mode,WhenModuleChanged,RequireReanalysis) 
# "List of modules changed when updating the analysis results in the
  registry. Registry information of @var{Module} with basename
  @var{Base} has been changed as a result of analyzing
  @var{SourceModule}. @var{Mode} represents the relationship between
  @var{Module} and @var{SourceModule}, and it can be @code{imported},
  @code{caller} or @code{current}.

  @var{WhenModuleChanged} indicates in which run of the analysis of
  @var{SourceModule} the registry information of @var{Module}
  changed. This argument can be instantiated to values @code{current}
  (modules whose information changed as result of the last analysis
  run) or @code{previous} (modules whose information changed as result
  of a previous analysis run).

  @var{RequireReanalysis} indicates that the module should be
  reanalyzed. This is only useful in the context of
  @pred{gen_registry_info/3-4}.".

:- data changed_module/6.

%% --------------------------------------------------------------------

% IG: not needed
% :- pred external_reachable(SgImpKey,AbsInt,SgExp,CallExp,SgImp,CallImp)
% # "List of pairs (exported call pattern, imported call pattern) for a
%   given domain for computing the intermodular dependency graph.".
% :- data external_reachable/6.

%% --------------------------------------------------------------------

:- pred reg_version(Version) : atm
# "Contains a version number which identifies
   the registry files associated with this version of the assertion
   library. Should be changed every time changes are made which render
   registry files incompatible, since this forces recomputation
   of all such files.".
reg_version('2.3').

%reg_extension('.reg').  %% moved to in p_asr

:- pred registry_header_format(Version,TermList) : atm * list(term) 
# "@var{TermList} is the list of terms which must appear in the header
   of version @var{Version} registry files, excluding the version
   number term itself.".
registry_header_format('1.0',[]).
registry_header_format('2.0',
    [ pl_date(_),    %% Date of the .pl file to which refers the .reg file.
      already_analyzed(_) %% List of domains for which module entries have been analyzed.
    ]).
registry_header_format('2.1',
    [ pl_date(_),   %% Date of the .pl file to which refers the .reg file.
      already_analyzed(_),%% List of domains for which module entries have been analyzed
      open_mode(_)  %% Mode in which the .reg file is opened (read_write, read_only).
    ]).
registry_header_format('2.2',
    [ pl_date(_),    %% Date of the .pl file to which refers the .reg file.
      entries_already_analyzed(_),%% List of domains for which module entries have been analyzed
      open_mode(_)   %% Mode in which the .reg file is opened (read_write, read_only).
    ]).
registry_header_format('2.3',
    [ pl_date(_),    %% Date of the .pl file to which refers the .reg file.
      entries_already_analyzed(_),%% List of domains for which module entries have been analyzed
      open_mode(_)   %% Mode in which the .reg file is opened (read_write, read_only).
    ]).
% TODO: IG, update registry_header_format with module base
% TODO: IG: document that pl_date is not used because we use the
% compiler to detect changes in the source

:- pred cleanup_p_abs # "Cleans up internal data predicates.".
cleanup_p_abs:-
    retractall_fact(imported_module(_,_)),
    retractall_fact(caller_module(_,_)),
    retractall_fact(module_is_processable_cache(_,_,_)),
%       retractall_fact(typedef_already_loaded(_)),
    move_last_changes_to_previous.

move_last_changes_to_previous:-
    retract_fact(changed_module(Mod,Base,CurrModule,Mode,current,ReqReanalysis)),
    ( current_fact(changed_module(Mod,Base,CurrModule,Mode,previous,ReqReanalysis)) ->
      true
    ; asserta_fact(changed_module(Mod,Base,CurrModule,Mode,previous,ReqReanalysis))
    ),
    fail.
move_last_changes_to_previous.

:- pred cleanup_p_abs_all # "Cleans up all the data predicates.".
cleanup_p_abs_all:-
    cleanup_registry(_),
    clean_incanal_mod_data,
    retractall_fact(changed_module(_,_,_,_,_,_)),
    cleanup_p_abs.

cleanup_registry(Module):-
    retractall_fact(registry(_,Module,_)),
    retractall_fact(registry_headers(Module,_)),
    retractall_fact(typedb(Module,_)),
%       retractall_fact(typedef_already_loaded(Module)).
    true.

% TODO: get this from semantic info: completes?
:- pred get_imported_modules
# "Gets the list of imported modules from the current module. This list is
  obtained from the itf information of the current module, and is stored in
 @tt{imported_module/1}.".
get_imported_modules :-
    current_fact(imported_module(_,_)), !.
get_imported_modules:-
    current_itf(imports,_Sg,Module), atom(Module),
    %just_module_name(Module0,Module), % IG already done in get_loaded_mod...
    \+ imported_module(Module, _),
    get_loaded_module_name(Module,_AbsFile,AbsBase),
    assertz_fact(imported_module(Module,AbsBase)),
    fail.
get_imported_modules.

get_imported_module_base(M, Base) :-
    current_fact(imported_module(M,Base)), !.
get_imported_module_base(M, Base) :-
    get_loaded_module_name(M,_AbsFile,Base),
    assertz_fact(imported_module(M,Base)).

get_imported_used_modules :-
    ( processed_sg(_,Sg),
        get_module_from_sg(Sg,Module),
        \+ imported_module(Module, _),
        get_loaded_module_name(Module,_AbsFile,AbsBase),
        assertz_fact(imported_module(Module,AbsBase))
    ; true).

:- pred get_caller_modules # "Gets the list of caller modules to the
    current modules. This list is obtained from the registry
    information for the current modules, and is stored in
    @tt{caller_modules/2}.".
get_caller_modules:-
    current_fact(caller_module(_,_)), !.
get_caller_modules:-
    ( % (failure-driven loop)
      curr_file(_F,CurrModule),
      current_fact(registry(_,CurrModule,regdata(_,_AbsInt,_Sg,_Call,_Succ,_Spec,ImdgList,_,_Mark))),
        get_module_names(ImdgList,Modules,Bases),
        add_caller_modules(Modules,Bases),
        fail
    ; true
    ).

get_module_names([],[],[]).
get_module_names(['$query'|Imdgs],Ms,Bases):- !,
    get_module_names(Imdgs,Ms,Bases).
get_module_names([(_Id,_SgCaller,_Caller,Base)|Imdgs],[M|Ms],[Base|Bases]):-
    just_module_name(Base,M),
    get_module_names(Imdgs,Ms,Bases).

:- pred gen_registry_info(+Verb,-Callers,-Imported)
# "Obtains from analysis internal structures the information on
  exported predicates regarding the current module and related
  modules. Returns in @var{Callers} and @var{Imported} the list of
  basenames of related modules whose registry information has been
  updated.".
gen_registry_info(Verb,Callers,Imported):-
    compute_external_reachability,
    get_imported_used_modules,
    ensure_registry_current_files(Verb),
    ensure_registry_imported_files(Verb),
    get_caller_modules,
    ensure_registry_caller_files(Verb),
    ( curr_file(File, Mod),
      update_registry_dependencies(_, File, Mod),
      fail
    ; true),
    get_imported_changed_modules(Imported),
    get_caller_changed_modules(Callers),
    unmark_typedefs_already_loaded.

% TODO: review when we fix modular incremental analysis
unmark_typedefs_already_loaded:-
%       retractall_fact(typedef_already_loaded(_)).
    true.

:- pred gen_registry_info(+Verb,-Callers,-Imported,-Info)
# "As @pred{gen_registry_info/3}, but also returns @var{Info}.".
gen_registry_info(Verb,Callers,Imported,[time(Time,[])]):-
    stat_no_store(gen_registry_info(Verb,Callers,Imported), Time),
    pplog(p_abs, ['{Generated registry in ',Time,' msec.}']).

get_imported_changed_modules(Imported):-
    findall(Base,imported_changed_module(Base),Imported).

imported_changed_module(Base) :-
    curr_file(_,CurrModule),
    changed_module(M,Base,CurrModule,imported,current,yes),
    \+ curr_file(_,M),
    module_is_processable(Base).

get_caller_changed_modules(Callers):-
    findall(Base,caller_changed_module(Base),Callers).

caller_changed_module(Base) :-
    curr_file(_,CurrModule),
    changed_module(M,Base,CurrModule,caller,current,yes),
    \+ curr_file(_,M).

%% --------------------------------------------------------------------

:- export(ensure_registry_current_files/1). % TODO: move above
ensure_registry_current_files(Verb):-
    curr_file_base(CurrBase,CurrModule),
    ensure_registry_file(CurrModule,CurrBase,Verb),
    fail.
ensure_registry_current_files(_Verb).

:- doc(bug,"Currently ensure_registry_imported_files/1 and
    ensure_registry_caller_files/1 read reg files for all imported
    and caller modules. An interesting improvement could be to
    read only those files of modules for which we have new call
    patterns").

ensure_registry_imported_files(Verb):-
    current_fact(imported_module(IM,Base)),
    ensure_registry_file(IM,Base,Verb),
    fail.
ensure_registry_imported_files(_Verb).

ensure_registry_caller_files(Verb):-
    caller_module(CM,Base),
%%      current_itf(defines_module,CM,Base),
    ensure_registry_file(CM,Base,Verb),
    fail.
ensure_registry_caller_files(_Verb).

%% ====================================================================

% IG: not used
% :- pred update_current_files(+Verb)
% # "This predicate updates the registry of the current modules. If the
%   current modules source files have been modified after generating the
%   registry, all its results are discarded, generating a new
%   registry. If not, the registries are updated modifying only those
%   entries for which we have better results.".
% update_current_files(Verb):-
%       curr_file_base(Base,CurrModule),
%       update_current_registry(Base,CurrModule,Verb),
%       unset_src_changed(Base),
%       update_registry_header_pl_date(CurrModule,Base), % TODO: not needed?
%       fail.
% update_current_files(_Verb).

% :- pred update_current_registry(+CurrBase,+CurrModule,+Verb)
% # "This predicate updates the registry of the current module. If the
%   current module has been modified after generating the registry, all
%   its results are discarded, generating a new registry. If not, the
%   file is updated modifying only those entries for which we have
% better results. Type definitions are replaced accordingly.".
% update_current_registry(Base,CurrModule,_Verb):-
%       current_fact(registry(SgKey,CurrModule,OldReg),Ref),
%       OldReg = regdata(Id,AbsInt,Sg,Call,OldSucc,SpecName,ImdgList,Chdg,OldMark),
%       check_curr_entry_id(Id),
%       current_fact(complete(SgKey,AbsInt,SgComplete,CallComplete,[Succ],_Id,_)), %access by SgKey
%       abs_sort(AbsInt,CallComplete,CallComplete_s),
%       abs_sort(AbsInt,Call,Call_s),
%       identical_proj(AbsInt,SgComplete,CallComplete_s,Sg,Call_s),
% %% If the entry has been reanalyzed, it is unmarked in registry.
%       erase(Ref),
%       NewReg = regdata(Id,AbsInt,SgComplete,CallComplete,Succ,SpecName,ImdgList,Chdg,unmarked),
%       assertz_fact(registry(SgKey,CurrModule,NewReg)),
%       add_changed_module(CurrModule,Base,CurrModule,current,n),
%       %% If success info has changed, callers must be marked for reanalysis or invalidated.
%       abs_sort(AbsInt,Succ,Succ_s),
%       abs_sort_nonfree(AbsInt,OldSucc,OldSucc_s),
%       update_mem_usage,
%       current_pp_flag(success_policy,SP),
%       ( nonvar(OldSucc_s),
%         identical_proj(AbsInt,SgComplete,Succ_s,Sg,OldSucc_s) ->
%           ( not_valid_mark(SP,OldMark) ->
% %jcf-26.11.2004 (study this!!!)           ,current_pp_flag(intermod, Imod),
%             %jcf-26.11.2004       Imod \== auto ->   %% oops, only with manual_analyze!!!!
%               may_be_improved_mark(SP,CallersMark),
%               mark_callers_registry(ImdgList,SgKey,NewReg,AbsInt,CurrModule,CallersMark,_)
%             ; true
%             )
%       ;
%           fixpoint_trace('mod succ changed',Id,CurrModule,SgKey,Sg,Succ,_),
%           compare_and_get_mark(SP,AbsInt,SgComplete,Succ_s,Sg,OldSucc_s,CallersMark),
%           mark_callers_registry(ImdgList,SgKey,NewReg,AbsInt,CurrModule,CallersMark,_)
%       ),
%       fail.
% update_current_registry(_Base,CurrModule,_Verb):-
%       update_current_typedefs(CurrModule),
%       !.

%% --------------------------------------------------------------------

%% NOTE: This predicate decides when to set invalid marks, depending on the success policy.
compare_and_get_mark(SP,_AbsInt,_SgComplete,_Succ_s,_Sg,OldSucc_s,Mark):-
%% This case should not occur.
    var(OldSucc_s), !,
    may_be_improved_mark(SP,Mark).
compare_and_get_mark(_SP,AbsInt,SgComplete,Succ_s,Sg,OldSucc_s,'+'):-
    less_or_equal_proj(AbsInt,SgComplete,Succ_s,Sg,OldSucc_s),
    !.
compare_and_get_mark(_SP,_AbsInt,_SgComplete,_Succ_s,_Sg,_OldSucc_s,'-').

%% ********************************************************************
%% ********************************************************************

:- pred not_valid_mark(?SP,?Mark) 
# "Succeeds if a registry entry marked with @var{Mark} cannot be used
  when the success policy @var{SP} is applied.".
not_valid_mark(SP,Mark):-
    may_be_improved_mark(SP,OppositeMark),
    opposite_mark(OppositeMark, Mark).

opposite_mark('-','+').
opposite_mark('+','-').

:- pred may_be_improved_mark(?SP,?Mark) 
# "Succeeds if a registry entry marked with @var{Mark} can be used
when the success policy @var{SP} is applied, and the analysis results
can be improved by reanalysing the module.".
may_be_improved_mark(over_first,'+').
may_be_improved_mark(over_best,'+').
may_be_improved_mark(over_all,'+').
may_be_improved_mark(top,'+').
may_be_improved_mark(under_first,'-').
may_be_improved_mark(under_best,'-').
may_be_improved_mark(under_all,'-').
may_be_improved_mark(bottom,'-').
may_be_improved_mark(bottom_up,'+').  % Is this right?

:- data tmp_current_module/1.

update_current_typedefs(CurrModule):-
    retractall_fact(typedb(CurrModule,_TypeDef)),
%       retractall_fact(typedef_already_loaded(CurrModule)),
    set_fact(tmp_current_module(CurrModule)),
    %
    ( % (failure-driven loop)
      current_fact(registry(_,CurrModule,Reg)),
      Reg = regdata(_,AbsInt,_Sg,Call,Succ,_SpecName,ImdgList,Chdg,_Mark),
        get_imdg_asubs(ImdgList,ImdgSubsList),
        get_chdg_asubs(Chdg,ChdgSubs),
        append(ChdgSubs, ImdgSubsList, DepsASubs),
        auxinfo_dump:acc_auxiliary_info(AbsInt,[Call,Succ|DepsASubs]),
        fail
    ; true
    ),
    auxinfo_dump:dump_auxiliary_info(store_typedef).

add_imported_typedefs(AbsInt,Module,ASubs):-
%       retractall_fact(typedef_already_loaded(Module)),
    set_fact(tmp_current_module(Module)),
    auxinfo_dump:acc_auxiliary_info(AbsInt,ASubs),
    auxinfo_dump:dump_auxiliary_info(store_typedef), !.

store_typedef(TypeDef):-
    current_fact(tmp_current_module(CurrModule)),
    ( current_fact(typedb(CurrModule,TypeDef)) ->
        %%%NOTE: TypeDef comparison should be smarter!!!!!!!
        true
    ;
        asserta_fact(typedb(CurrModule,TypeDef))
    ).

%% If substitution is a free var, there is nothing to sort.
abs_sort_nonfree(_AbsInt,Sub1,Sub1):-
    var(Sub1), !.
abs_sort_nonfree(AbsInt,Sub1,Sub2):-
    abs_sort(AbsInt,Sub1,Sub2).

:- pred mark_callers_registry(+ImdgList,+PKey,ParentReg,+AbsInt,+CurrModule,+NewMark,-BasenamesMarked)
    # "Entries of callers entries in @var{ImdgList} are marked with
    @var{NewMark} (if it is greater than their current mark).".

mark_callers_registry([],_,_,_,_CurrModule,_NewMark,[]).
mark_callers_registry(['$query'|Imdgs],PKey,ParentReg,AbsInt,CurrModule,NewMark,BasenamesMarked):- !,
    mark_callers_registry(Imdgs,PKey,ParentReg, AbsInt,CurrModule,NewMark,BasenamesMarked).
mark_callers_registry([(Id,SgCaller,_Caller,Base)|Imdgs],PKey,ParentReg, AbsInt,CurrModule,NewMark,BasenamesMarked):-
    current_pp_flag(success_policy,SP),
    just_module_name(Base,M),
    ensure_registry_file(M,Base,quiet),  %% just in case. If it is already loaded, it does nothing. % TODO: can we really ensure that it is loaded?
    predkey_from_sg(SgCaller, SgKey),
    ( current_fact(registry(SgKey,M,OldReg),Ref),
      OldReg = regdata(Id,AbsInt,Sg,Call,Succ,Spec,ImdgList,Chdg,OldMark) ->
        ( less_or_equal_mark(SP,NewMark,OldMark) ->
            BasenamesMarked = BasenamesMarked0
        ;
            erase(Ref),
            BasenamesMarked = [Base|BasenamesMarked0],
            NewReg = regdata(Id,AbsInt,Sg,Call,Succ,Spec,ImdgList,Chdg,NewMark),
            assertz_fact(registry(SgKey,M,NewReg))
        ),
        ( nonvar(PKey) -> % IG this is for invalidate_callers
            add_changed_registry(PKey,M,CurrModule,ParentReg)
        ; true),
        add_changed_module(M,Base,CurrModule,caller,yes)
    ;
        true % If there is no registry, this is suspicious... (possible bug)
    ),
    update_mem_usage,
    mark_callers_registry(Imdgs,PKey,ParentReg,AbsInt,CurrModule,NewMark,BasenamesMarked0).

%% ******************** SPEC ************************************************

:- pred update_spec_info(+File,-Changed) # "Updates the information
    about version names of specialized predicates in @var{File}.".
update_spec_info(File,Changed):-
    absolute_file_name(File,'_opt','.pl','.',_,AbsBase,_),
    just_module_name(AbsBase,Module),
    ensure_registry_file(Module,AbsBase,quiet), % TODO: can we really ensure that it is loaded?
    update_current_registry_spec_info(AbsBase,Module,Changed).

:- data changed/1.

update_current_registry_spec_info(Base,CurrModule,Changed):-
    set_fact(changed(no)),
    ( % (failure-driven loop)
      publish_pred_name(PredName,PredArity), % (loop)
      % functor(Sg,PredName,PredArity), % [IG] Sg not needed
      get_predkey(PredName,PredArity,SgKey),
      current_fact(registry(SgKey,CurrModule,OldReg),Ref), % (may fail)
        OldReg = regdata(Id,AbsInt,Sg,Call,Succ,SpecName,ImdgList,Chdg,Mark),
        get_version_name(AbsInt,Sg,Call,NewSpecName),
        SpecName \== NewSpecName,
        erase(Ref),
        set_fact(changed(yes)), % (mark that there are changes)
        NewReg = regdata(Id,AbsInt,Sg,Call,Succ,NewSpecName,ImdgList,Chdg,Mark),
        assertz_fact(registry(SgKey,CurrModule,NewReg)),
        add_changed_module(CurrModule,Base,CurrModule,current,no),
        fail
    ; true
    ),
    current_fact(changed(Changed)).

:- pred get_spec_info_imported
# "Gets the information about version names of specialized predicates
  belonging to the list of imported modules from the current module,
  and puts them into the specializer's abstract executability table.".

get_spec_info_imported:-
    get_imported_modules,         %% just in case.
    findall(M,current_fact(imported_module(M,_)),Modules),
    get_spec_info(Modules).

get_spec_info([]).
get_spec_info([Module|Modules]):-
    current_itf(defines_module,Module,Base),
    just_module_name(Base,Module),
    ensure_registry_file(Module,Base,quiet), % TODO: can we really ensure that it is loaded?
    retractall_fact(dyn_abs_spec(Module,_,_,_,_)),
    get_spec_info_one_module(Module,SpecList),
    sort_spec_info_one_module(SpecList,SortedSpecList),
    assert_spec_info_one_module(Module,SortedSpecList),
    get_spec_info(Modules).

get_spec_info_one_module(Module,NameList):-
    findall((AbsInt,Sg,Proj,SpecName), spec_info_nonvar(Module,AbsInt,Sg,Proj,SpecName), NameList).

spec_info_nonvar(Module,AbsInt,Sg,Proj,SpecName) :-
    registry(_,Module,regdata(_,AbsInt,Sg,Proj,_,SpecName,_,_,unmarked)),
    nonvar(SpecName).

sort_spec_info_one_module(L1,L2):-
    qsort(L1,L2,[]).

% TODO: qsort reimplemented for comparing with spec_less
qsort([X|L],R,R2) :-
    partition(L,X,L1,L2),
    qsort(L2,R1,R2),
    qsort(L1,R,[X|R1]).
qsort([],R,R).

partition([],_,[],[]).
partition([E|R],C,[E|Left1],Right):- 
    spec_less(E,C), !,
    partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]):-
    partition(R,C,Left,Right1).

spec_less((AbsInt1,_Sg1,_Proj1,_SpecName1),(AbsInt2,_Sg2,_Proj2,_SpecName2)):-
    AbsInt1 @< AbsInt2, !.
spec_less((AbsInt,Sg1,_Proj1,_SpecName1),(AbsInt,Sg2,_Proj2,_SpecName2)):-
    functor(Sg1,F1,A1),
    functor(Sg2,F2,A2),
    (F1 @< F2 ; A1 < A2), !.
spec_less((AbsInt,Sg1,Proj1,_SpecName1),(AbsInt,Sg2,Proj2,_SpecName2)):-
    abs_sort(AbsInt,Proj1,Proj1_s),
    abs_sort(AbsInt,Proj2,Proj2_s),
    less_or_equal_proj(AbsInt,Sg1,Proj1_s,Sg2,Proj2_s),
    \+ identical_proj(AbsInt,Sg1,Proj1_s,Sg2,Proj2_s), !.

assert_spec_info_one_module(_,[]) :- !.
assert_spec_info_one_module(Module,[(AbsInt,Sg,Proj,SpecName)|SpecList]):-
    assertz_fact(dyn_abs_spec(Module,Sg,AbsInt,Proj,SpecName)),
    assert_spec_info_one_module(Module,SpecList).

%% ***************** SAVE REGISTRY *****************************************

:- set_prolog_flag(multi_arity_warnings,off).

:- pred save_registry_info(+Verb,-Info) : atm * term
# "Writes on disk the registry information of the modules loaded into
  Ciaopp or related to modules loaded into Ciaopp. This information is
  updated by @pred{gen_registry_info/3}. This predicate must be called
  after performing intermodular preprocessing (analysis,
  specialization...), even if @pred{save_registry_info/3} has been
  used.".
save_registry_info(Verb,[time(T,[])]):-
    %ALL changed modules MUST be saved!
    pp_statistics(runtime,_),
    ( setof(Base,M^M2^Mode^All^Req^(changed_processable_module(Base,M,M2,Mode,All,Req)),ML) ->
      write_registry_files(ML,Verb),
      retract_saved_files(ML)
    ; true
    ),
    pp_statistics(runtime,[_,T]),
    pplog(p_abs, ['{Saved registry in ',T,' msec.}']),
    update_mem_usage,
    !.

changed_processable_module(Base,M,M2,Mode,All,Req) :-
    changed_module(M,Base,M2,Mode,All,Req),
    module_is_processable(Base).

% TODO: EXACTLY THE SAME CODE
:- pred save_registry_info(+Verb,+CurrBase,-Info) : atm * atm * term
# "Writes on disk the registry information of the modules related to
  the current module (@var{CurrBase}) which have been modified. This
  information is updated by @pred{gen_registry_info/3}. Even if this
  predicate is used, @pred{save_registry_info/2} must be used after
  performing intermodular preprocessing.".
save_registry_info(Verb,CurrBase,[time(T,[])]):-
    pp_statistics(runtime,_),
    just_module_name(CurrBase,CurrModule),
    ( setof(Base,Mode^M^All^Req^(changed_processable_module(Base,M,CurrModule,Mode,All,Req)),ML) ->
      write_registry_files(ML,Verb),
      retract_saved_files(ML)
    ; true
    ),
    pp_statistics(runtime,[_,T]),
    pplog(p_abs, ['{Saved registry in ',T,' msec.}']),
    update_mem_usage,
    !.

write_registry_files([],_Verb).
write_registry_files([Base|BList],Verb):-
    just_module_name(Base,M),
    write_registry_file(Base,M,Verb),
    write_registry_files(BList,Verb).

retract_saved_files([]).
retract_saved_files([Base|Bases]):-
    retractall_fact(changed_module(_,Base,_,_,_,_)),
    retract_saved_files(Bases).

%% ====================================================================
% IG: used now only for spec and somewhere in resources
:- pred get_imported_calls(-ICalls) 
# "Returns a list of tuples (@var{IM},@var{IMBase},@var{Sg}), where
  @var{Sg} is an imported call of module @var{IM} (basename
  @var{IMBase}).  Only the imported calls from processable modules are
  considered.".
get_imported_calls(ICalls):-
    ( setof((ModName,Sg), (current_itf(imports,Sg,ModName), atom(ModName)), ICalls0) ->
        remove_duplicates(ICalls0,ICalls1),
        get_module_names_bases(ICalls1,ICalls)
    ;
        ICalls = []
    ).

%% Tries to remove the calls that unify, but that are not removed by setof/3.
remove_duplicates(L1,L2):-
    sort(L1,L11),
    remove_duplicates(L11,[],L2).

remove_duplicates([],L,L).
remove_duplicates([X|Xs],[X|Ys],L):-
    remove_duplicates(Xs,[X|Ys],L), !.
remove_duplicates([X|Xs],Ys,L):-
    remove_duplicates(Xs,[X|Ys],L), !.
:- set_prolog_flag(multi_arity_warnings,on).

get_module_names_bases([],[]).
get_module_names_bases([(user,_Sg)|Xs],Ys):-
    !,
    get_module_names_bases(Xs,Ys).
get_module_names_bases([(File,Sg)|Xs],[(IM,IMBase,Sg)|Ys]):-
    get_imported_module_base_name(File, IM, IMBase),
    !,
    get_module_names_bases(Xs,Ys).
get_module_names_bases([(_File,_Sg)|Xs],Ys):-
    get_module_names_bases(Xs,Ys).
 
get_imported_module_base_name(File, Mod, Base) :-
    just_module_name(File,Mod),
    current_fact(imported_module(Mod,Base)),
    module_is_processable(Base).

:- pred add_to_imdg_list(+Caller,+OldList,-NewList,-Added) 
# "Adds an element @var{Caller} (formed by either a tuple
  (@var{SgCaller},@var{Caller_s},@var{Base}) or an atom
  @code{'$query'}) to @var{OldList}, a list of intermodular
  dependencies. @var{Added} will be instantiated to 'y' if
  @var{Caller} is actually added to @var{NewList}, and 'n' if it was
  already in @var{OldList}.".

% TODO: IG: AbsInt not needed in this predicate
add_to_imdg_list([],'$query',['$query'],y).
add_to_imdg_list(['$query'|Is], '$query',['$query'|Is],n):- !.
add_to_imdg_list([(Id,Sg,Caller,Base)|Is],'$query',[(Id,Sg,Caller,Base)|NIs],Added):-
    add_to_imdg_list(Is,'$query',NIs,Added),!. % Why added last?
add_to_imdg_list([],(Id,Sg,Caller,Base),[(Id,Sg,Caller,Base)],y) :- !.
add_to_imdg_list(Is,(Id,_,_,Base),Is,n):-
    Is = [(IdOld,_,_,Base)|_],
    Id = IdOld, !.
add_to_imdg_list([I|Is],(Id,SgCaller,Caller_s,Base),[I|NIs],Added):-
    add_to_imdg_list(Is,(Id,SgCaller,Caller_s,Base),NIs,Added),!.

%% --------------------------------------------------------------------

% TODO: document
ensure_registry_file(Module,Base,Verb):-
    read_registry_file_(Module,Base,Verb),
    patch_registry_(Module,Base,_).

:- pred read_registry_file(+Module,+Base,+Verb) : atm * atm * atm
# " Reads the registry file of @var{Module} and loads it into
  @tt{registry/2}, erasing any previous registry information for that
  module. @var{Base} must be the absolute file name, but excluding
  file extension.".
read_registry_file(Module,Base,Verb):-
    % TODO:{JF2} split in a simple pred that read the registry and other that computes NeedsTreat, patches Mark at registry (if needed), and does upload_typedefs_all_domains
    read_registry_file_(Module,Base,Verb).
%%%     patch_registry_(Module,Base,_). % TODO:{JF2} is this correct??? we assume that none of the previous read registry need patching the registry info w.r.t. src_changed/1

read_registry_file_(Module,_Base,_Verb):-
    check_registry_already_read(Module), !.
read_registry_file_(Module,Base,Verb):-
    % Just make sure that the registry is loaded
    cleanup_registry(Module),
    get_module_filename(reg,Base,RegName),
    get_module_filename(pl,Base,PlName),
    ( file_exists(RegName) ->
      open(RegName, read, Stream),
      ( read_registry_header(Verb,Module,Stream) ->
          current_input(CI),
          set_input(Stream),
          pplog(p_abs, ['{Reading ',RegName]),
          read_types_data_loop(Module,NextTuple),   % NextTuple is the tuple after the last type definition.
          read_reg_data_loop(Module,NextTuple),
          set_input(CI),
          pplog(p_abs, ['}']),
          fixpoint_trace('mod reg read',Module,_,_,Base,_,_)
      ; pplog(p_abs, ['{Wrong version of file: ',RegName,'. It will be overwritten.}']),
        create_registry_header(Module,PlName),
        add_changed_module(Module,Base,Module,registry_created,no),
        fixpoint_trace('mod reg header created',Module,_,_,Base,_,_)
      ),
      close(Stream)
    ; pplog(p_abs, ['{Non-existing file: ',RegName,'}']),
      create_registry_header(Module,PlName),
      add_changed_module(Module,Base,Module,registry_created,no),
      fixpoint_trace('mod reg header created',Module,_,_,Base,_,_)
    ),
    !.

% (needs src_changed/1)
peek_needs_treat(Base,NeedsTreat):-
    % NOTE: (previous code do not create a RegName file yet)
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        % TODO:{JF2} assume read_registry_header succeeded
        % consult some data that we annotate during process_one_module
        ( src_changed(Base) -> NeedsTreat = yes
        ; NeedsTreat = no
        )
    ; NeedsTreat = yes
    ).

% (needs src_changed/1)
patch_registry_(Module,_Base,NeedsTreat):-
    registry_headers(Module, patched_registry(NeedsTreat0)),
    !,
    NeedsTreat = NeedsTreat0,
    upload_typedefs_all_domains(Module). % TODO:{JF2} repeated?
patch_registry_(Module,Base,NeedsTreat):-
    % NOTE: (previous code do not create a RegName file yet)
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        peek_needs_treat(Base,NeedsTreat),
        assertz_fact(registry_headers(Module, patched_registry(NeedsTreat))),
        ( NeedsTreat = no ->
            ForceMark = unmarked  %% no mark at all.
        ; 
%jcf-26.11.2004         ForceMark = invalid,
%jcf-26.11.2004         pplog(p_abs, ['{Non-up-to-date file: ',RegName,'. All entries will be marked as invalid.}'])
            current_pp_flag(success_policy,SP),
            may_be_improved_mark(SP,ForceMark)
%jcf-26.11.2004
        ),
        patch_read_reg_data_loop(Module,ForceMark),
        upload_typedefs_all_domains(Module)
    ; NeedsTreat = yes
    ),
    !.

%% --------------------------------------------------------------------

% Reads types from std. input. The last tuple read (immediately after the last type read) is 
% returned in NextTuple.
read_types_data_loop(Module,NextTuple):-
    retractall_fact(typedb(Module,_)),
%       retractall_fact(typedef_already_loaded(Module)),
    repeat,
    ( fast_read(NextTuple) ->
        ( % NextTuple = typedef(TypeName,TypeDef) ->
          is_dump_auxiliary_fact(NextTuple) ->
            assertz_fact(typedb(Module,NextTuple)),
            fail
        ; 
            true
        )
    ;
        NextTuple = end_of_file
    ).

%% --------------------------------------------------------------------

read_reg_data_loop(_,end_of_file) :- !.
read_reg_data_loop(Module,Reg) :-
    add_registry(Module, Reg),
    ( fast_read(NextRegistry) ->
        read_reg_data_loop(Module,NextRegistry)
    ; true
    ).

:- data new_registry/3.

patch_read_reg_data_loop(Module,ForceMark) :-
    retractall_fact(new_registry(_,_,_)),
    ( % (failure-driven loop)
      retract_fact(registry(SgKey,Module,OldReg)),
      OldReg = regdata(Id,AbsInt,Sg,Call,Succ,SpecName,ImdgList,Chdg,Mark),
        current_pp_flag(success_policy,SP),
        ( less_or_equal_mark(SP,Mark,ForceMark) ->
            CurrMark = ForceMark
        ; 
            CurrMark = Mark
        ),
        NewReg = regdata(Id,AbsInt,Sg,Call,Succ,SpecName,ImdgList,Chdg,CurrMark),
        assertz_fact(new_registry(SgKey,Module,NewReg)),
        fail
    ; true
    ),
    ( % (failure-driven loop)
      retract_fact(new_registry(SgKey,Module,Reg)),
        assertz_fact(registry(SgKey,Module,Reg)),
        %add_changed_registry(SgKey,Module,Reg),
        fail
    ; true
    ).

check_registry_already_read(Module):-
    current_fact(registry_headers(Module,_)).

% TODO: this is not working for incremental modular analysis
:- pred upload_typedefs(+AbsInt,+Module) : atm * atm
# "Uploads into CiaoPP the types used by the registry entries of
  @var{Module} in domain @var{AbsInt}. @var{Module} registry info must
  be already loaded into memory. If the type information has been
  already uploaded, it is not loaded again.".
upload_typedefs(AbsInt,Module):-
    %%% uploading typedefs, and updating registry information with typedef renamings.
    set_fact(tmp_current_module(Module)),
    auxinfo_dump:restore_auxiliary_info(current_typedb,Dict),
    ( % (failure-driven loop)
      current_fact(registry(SgKey,Module,OldReg),Ref),
        OldReg = regdata(Id,AbsInt,Sg,Call0,Succ0,SpecName,ImdgList0,Chdg0,Mark),
        get_imdg_asubs(ImdgList0,ImdgSubsList0),
        get_chdg_asubs(Chdg0,ChdgSubs0),
        append(ChdgSubs0, ImdgSubsList0, DepsSubs0),
        auxinfo_dump:imp_auxiliary_info(AbsInt,Dict,[Call0,Succ0|DepsSubs0],[Call,Succ|DepsSubs]),
        replace_chdg_subs(Chdg0,DepsSubs,Chdg,ImdgSubsList),
        replace_imdg_subs(ImdgList0,ImdgSubsList,ImdgList),
        erase(Ref),
        NewReg = regdata(Id,AbsInt,Sg,Call,Succ,SpecName,ImdgList,Chdg,Mark),
        assertz_fact(registry(SgKey,Module,NewReg)),
        %add_changed_registry(SgKey,Module,NewReg),
        fail
    ; true
    ),
    %%% downloading typedef renamings again, and replacing typedef/2 definitions.
    update_current_typedefs(Module),
    !.
%       assertz_fact(typedef_already_loaded(Module)),

upload_typedefs_all_domains(Module):-
    upload_typedefs(_AbsInt,Module).

% Returns the type definitions on backtracking from the temporary pred typedb/2 for tmp_current_module/1.
current_typedb(TypeDef):-
    current_fact(tmp_current_module(Module)),
    retract_fact(typedb(Module,TypeDef)).

% Given a list of imdg tuples, obtains the list of asubs for those imdg tuples.
get_imdg_asubs([],[]).
get_imdg_asubs(['$query'|Imdgs],Asubs) :- !,
    get_imdg_asubs(Imdgs,Asubs).
get_imdg_asubs([(_Id,_Sg,Proj,_Base)|Imdgs],[Proj|Asubs]) :-
    get_imdg_asubs(Imdgs,Asubs).

get_chdg_asubs([],[]).
get_chdg_asubs([(_Id,_Sg,Proj)|Chdgs],[Proj|Asubs]) :-
    get_chdg_asubs(Chdgs,Asubs).

%% --------------------------------------------------------------------

% Replaces the asubs of a list of imdg tuples by a list of new asubs.
% TODO: review consistency with Ids
replace_imdg_subs([],[],[]).
replace_imdg_subs(['$query'|Imdgs0],Asubs,['$query'|Imdgs]) :- !,
    replace_imdg_subs(Imdgs0,Asubs,Imdgs).
replace_imdg_subs([(Id,Sg,_,Base)|Imdgs0],[Proj|Asubs],[(Id,Sg,Proj,Base)|Imdgs]) :-
    replace_imdg_subs(Imdgs0,Asubs,Imdgs).

replace_chdg_subs([],L,[], L).
replace_chdg_subs([(Id,Sg,_)|Chdgs0],[Proj|Asubs],[(Id,Sg,Proj)|Chdgs], ImdgL) :-
    replace_chdg_subs(Chdgs0,Asubs,Chdgs, ImdgL).

%% --------------------------------------------------------------------

:- pred read_registry_header(Verb,Module,Stream) : atm * atm * stream 
# "Reads the header of @var{Module}'s registry file from @var{Stream},
  and stores it in the data predicate @tt{registry_header/2}. If the
  registry header is wrong, or it corresponds to a non-valid
  version, this predicate fails.".
read_registry_header(_Verb,Module,Stream):-
    read(Stream,v(V)),
    registry_header_format(V,HeaderTerms),
    read_registry_header_terms(Stream,Module,HeaderTerms).
read_registry_header(_Verb,Module,_Stream):-
    current_itf(defines_module,Module,Base),
    pplog(p_abs, ['{Wrong version or corrupted file header: ',Base,'}']),
    fail.

% TODO: unify with itf read
read_registry_header_terms(_Stream,_Module,[]) :- !.
read_registry_header_terms(Stream,Module,[H|Hs]) :-
    fast_read(Stream,H),
    assertz_fact(registry_headers(Module,H)),
    read_registry_header_terms(Stream,Module,Hs).

:- pred create_registry_header(+Module,+PlFileName) : atm * atm
# "Creates in memory a new registry header for @var{Module}. This
  predicate must be aware of the contents of the header and the order
  of the header terms (stored as terms in
  @pred{registry_header_format/2})".
create_registry_header(Module,PlFile) :-
    retractall_fact(registry_headers(Module,_)),
    modif_time0(PlFile,Date),
    assertz_fact(registry_headers(Module,pl_date(Date))),
    assertz_fact(registry_headers(Module,entries_already_analyzed([]))),
    path_splitext(PlFile, FileBase, _),
    assertz_fact(registry_headers(Module,module_base(FileBase))),
    ( (is_library(PlFile), \+current_pp_flag(punit_boundary,on)) ->
      assertz_fact(registry_headers(Module,open_mode(read_only)))
    ; assertz_fact(registry_headers(Module,open_mode(read_write)))
    ).

% IG: This is updated after the registry info is created/updated
% TODO: [IG] I think the logic of pl_date is redundant now
% (IG) Not used, done by the compiler, remove if everything works
% update_registry_header_pl_date(Module,Base):-
%       get_module_filename(pl,Base,FileName),
%       modif_time(FileName, FileTime),
%       retract_fact(registry_headers(Module,pl_date(_))),
%       assertz_fact(registry_headers(Module,pl_date(FileTime))),
%       retract_fact(registry_headers(Module, patched_registry(_))), % IG: always failing
%       assertz_fact(registry_headers(Module, patched_registry(no))).

%% --------------------------------------------------------------------

:- pred write_registry_header(Module,Stream) : atm * stream 
    # "Writes the header of @var{Module}'s registry file to @var{Stream}
    from the data predicate @tt{registry_headers/2}.".
write_registry_header(Module,Stream) :-
    reg_version(V),
    writeq(Stream,v(V)),display(Stream,'.'),nl(Stream),
    registry_header_format(V,HeaderTerms),
    write_header_terms(Stream,Module,HeaderTerms).

% TODO: unify with itf writting
write_header_terms(_Stream,_Module,[]) :- !.
write_header_terms(Stream,Module,[H|Hs]) :-
    registry_headers(Module,H),
    fast_write(Stream,H),
    write_header_terms(Stream,Module,Hs).

:- pred reread_registry_file(+Module,+Base,+Verb)
# "Overwrites the registry file of @var{Module} in memory reading it
  from disk.".
reread_registry_file(Module,Base,Verb):-
    cleanup_registry(Module),
    read_registry_file(Module,Base,Verb).

%% ********************************************************************
%% ********************************************************************
% TODO: IG merge predicates get_all_modules/2 and get_all_modules/3 ?
:- pred get_all_modules(+TopLevelFile,-ModList) 
# "Obtains @var{ModList}, the list of modules in the program unit
  whose top-level module is @var{TopLevelFile}. This list is formed by
  the modules which appear in the top-down modular graph traversal
  with registries set to read_write mode (and including library
  modules if punit_boundary flag is set to 'on'.".

get_all_modules(TopLevelFile,ModList):-
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,_,_),
    get_intermodule_graph(AbsFile,true),
    ( setof(M ,intermodule_list(M), ModList)
    ; ModList = []
    ),
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)),
    !.

:- pred get_all_modules(+TopLevelFile, -ModList, -IncludeList) 
    : filename(TopLevelFile) 
 => (list(filename,ModList), list(filename,IncludeList))
# "The same as @pred{get_all_modules/2}, but a list of included files
  is also returned.  This list includes not only files explicitly
  included with @code{:- include} declarations, but also packages
  used.".
get_all_modules(TopLevelFile,ModList,IncludeList):-
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,_,_),
    get_intermodule_graph(AbsFile,true),
    ( setof( M , intermodule_list(M) , ModList)
    ; ModList = []
    ),
    ( setof( I , include_list(I) , IncludeList)
    ; IncludeList = []
    ),
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)),
    !.

:- pred get_all_modules_depth(+TopLevelFile,-ModList) 
# "Given the top-level module of a program, @var{TopLevelFile},
  obtains in @var{ModList} the list of pairs (module,depth) with all
  modules in the modular graph with their maximal depth (without
  cycles).  All the modules in a cycle have the same depth.".
:- doc(bug,"not tested yet.").
get_all_modules_depth(TopLevelFile,ModList):-
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,AbsBase,_),
    get_intermodule_graph(AbsFile,true),
    compute_intermodule_graph_depth(AbsBase),
    ( setof( (M,D) , ( 
                         current_fact(intermodule_list(M)),
                         current_fact(intermodule_graph_depth(M,D))
                     ) , ModList)
    ; ModList = []),
    retractall_fact(intermodule_graph_depth(_,_)),
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)).

:- pred get_all_module_cycles(+TopLevelFile,-CycleList) 
# "Obtains @var{CycleList}, the list of cycles in the program unit
  whose top-level module is @var{TopLevelFile}.  A cycle is a ciclic
  dependency in the module dependency graph.  Every element of
  @var{CycleList} is a list of the modules which belong to each cycle.
  Modules not belonging to any cycle are represented as one-element
  lists. @var{CycleList} is sorted as a post-order traversal of the
  inter-cycle dependency graph.

  The modules included in @var{CycleList} are those which appear in
  the top-down modular graph traversal with registries set to
  read_write mode (and including library modules if punit_boundary
  flag is set to 'on'.)".
get_all_module_cycles(TopLevelFile,SortedCycleList):-
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,AbsBase,_),
    get_intermodule_graph(AbsFile,true),
    findall(vertex(M1,Ms,0,0,undef), initial_vertex(M1,Ms), Vertex),
    intermod_sccs(Vertex,CycleList),
    get_postorder_traversal(AbsBase,CycleList,SortedCycleList),
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)).

get_postorder_traversal(TopLevel,Cs,SortedCycles):-
    retractall_fact(module_scc(_,_)),
    retractall_fact(interscc_edge(_,_)),
    retractall_fact(scc_depth(_,_)),
    ( Cs = [] ->
        store_sccs([[TopLevel]],0)
    ;
        store_sccs(Cs,0)
    ),
    gen_interscc_edges,
    current_fact(module_scc(TopLevel,STopLevel)),
    interscc_postorder_traversal(STopLevel,SortedCs),
    get_cycles(SortedCs,SortedCycles),
    retractall_fact(module_scc(_,_)),
    retractall_fact(interscc_edge(_,_)),
    retractall_fact(scc_depth(_,_)).

%% In order to get the postorder traversal, 
%% difference lists are used, represented by List-Tail structures.
interscc_postorder_traversal(STopLevel,PostOrder):-
    interscc_children_traversal(STopLevel,A-A,PostOrder-Tail),
    Tail = [STopLevel].
    
interscc_children_traversal(Node, PO0-T0, PO1-T1):-
    findall(Child, interscc_edge(Node,Child), Children),
    interscc_children_traversal_2(Children,PO0-T0, PO1-T1).

interscc_children_traversal_2([],PO-T,PO-T).
interscc_children_traversal_2([Node|Nodes], PO0-T0, POn-Tn):-
    ( member_vartail(Node,PO0) ->
        PO1-T2 = PO0-T0
    ;
        interscc_children_traversal(Node, PO0-T0, PO1-T1),
        T1 = [Node|T2]
    ),
    interscc_children_traversal_2(Nodes, PO1-T2, POn-Tn).

member_vartail(_Node,V):-
    var(V), !, fail.
member_vartail(Node,[Node|_]):- !.
member_vartail(Node,[_|Rest]):-
    member_vartail(Node,Rest).

get_cycles([],[]).
get_cycles([CssId|CssIds],[Cycle|SortedCycles]):-
    findall(M, module_scc(M,CssId), Cycle),
    get_cycles(CssIds,SortedCycles).


%% ********************************************************************
%% ********************************************************************

:- pred propagate_invalid_info(+AbsInt,+TopLevel,+BaseList) 
# "Marks as 'invalid' all registry entries in @var{BaseList} which
  transitively depend on invalid entries. ".
:- doc(bug,"Not tested yet. Perhaps it is useless").
propagate_invalid_info(AbsInt,TopLevel,BaseList):-
    get_invalid_modules_from_list(AbsInt,BaseList,InvalidBaseListNoForce),
    propagate_invalid_info_(TopLevel,InvalidBaseListNoForce), !.

get_invalid_modules_from_list(_,[],[]) :- !.
get_invalid_modules_from_list(AbsInt,[Base|BaseList],[(Base,no_force)|InvalidBaseList]):-
    just_module_name(Base,Module),
    ensure_registry_file(Module,Base,quiet),
    \+ all_entries_valid(Base,AbsInt),
    !,
    get_invalid_modules_from_list(AbsInt,BaseList,InvalidBaseList).
get_invalid_modules_from_list(AbsInt,[_Base|BaseList],InvalidBaseList):-
    get_invalid_modules_from_list(AbsInt,BaseList,InvalidBaseList).

:- pred recover_from_invalid_state(+AbsInt,+TopLevel)
# "Checks if there is any invalid state in the program unit starting
  from @var{TopLevel}, and marks transitively as invalid all affected
  entries in any module of the program unit. This predicate is useful
  only in manual analysis of modular programs.".
recover_from_invalid_state(AbsInt,TopLevel):-
    get_invalid_modules(AbsInt,TopLevel,ModList),
    just_module_name(TopLevel,TopLevelModule),
    propagate_invalid_info_(TopLevelModule,ModList),!.

:- pred get_invalid_modules(+AbsInt,+TopLevelFile,-ModList)
# "Obtains in @var{ModList} the list of modules' basenames in the
  program unit which are in an invalid state, either if they have
  'invalid' entries in their .reg files, or their source code has
  changed since the last time they were analyzed.  If there is no .reg
  file for a module, its parents are added to @var{ModList}. Every
  element in @var{ModList} is a pair of the form
  (@var{Module},@var{Force}). If a source file has changed wrt since
  it was analyzed, or is the parent of a module with no .reg file,
  then @var{Force} is 'force', which means that all entries in the
  .reg file are invalid. The rest of the elements of @var{ModList}
  have 'no_force'.".
get_invalid_modules(AbsInt,TopLevelFile,ModList):-
    retractall_fact(module_to_analyze(_,_)),
    retractall_fact(module_to_analyze_parents(_)),
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,AbsBase,_),
    %
    get_intermodule_graph(AbsFile,check_registry_valid(AbsInt)),
    include_parents(AbsBase),
    ( setof((B,F), current_fact(module_to_analyze(B,F)), ModList)
    ; ModList = []),
    retractall_fact(module_to_analyze(_,_)),
    retractall_fact(module_to_analyze_parents(_)),
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)).

% Succeeds if the registry of Base is valid with respect to
% AbsInt: no registry entry is invalid, and the registry file exists.
check_registry_valid(Base,AbsInt):-
    just_module_name(Base,Module),
    cleanup_registry(Module), % TODO: force_read_registry_file_?
    read_registry_file_(Module,Base,quiet), % TODO:{JF} assume never fails!
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        peek_needs_treat(Base,NeedsTreat),
        ( NeedsTreat = no ->
            ( all_entries_valid(Base,AbsInt) ->
                % TODO: Previously this code depended on
                % patch_registry_file_, however we can see that if
                % NeedsTreat=no then the Invalid field in regdata
                % is not patched, so read_registry_file_ is enough
                true
            ; add_module_to_analyze(Base,no_force)
            )
        ;
            add_module_to_analyze(Base,force)
        )
    ; %% If there is no registry file, parent module is added
      %% for analysis (as call patterns are needed for the imported module).
      asserta_fact(module_to_analyze_parents(Base))
    ).

%% Succeeds if all entries of domain AbsInt are valid (marked or unmarked).
all_entries_valid(Base,AbsInt):-
    just_module_name(Base,Module),
    current_pp_flag(success_policy,SP),
    not_valid_mark(SP,Invalid),
    \+ current_fact(registry(_,Module,regdata(_,AbsInt,_,_,_,_,_,_,Invalid))).

%% --------------------------------------------------------------------

:- pred propagate_invalid_info_(+TopLevelModule,+ModList)
# "Traverses the intermodule dependency graph, and transitively
  propagates invalid states to caller modules. @var{ModList} is a pair
  of the form (@var{Module},@var{Force}). If @var{Force} is
  @code{force}, all registry entries must be marked as invalid, and
  their caller modules invalidated accordingly. If @var{Force} is
  @code{no_force}, then only the invalid registry entries are
  propagated to the caller modules.  This is an internal predicate
  (the corresponding exported predicate is
  propagate_invalid_info/2).".
propagate_invalid_info_(_TopLevel,[]) :- !.
propagate_invalid_info_(TopLevel,[(Base,Force)|ModList]) :-
    just_module_name(Base,Module),
    ensure_registry_file(Module,Base,quiet),
    ( Force = force ->  % All entries in the registry must be invalid.
        current_pp_flag(success_policy,SP),
        not_valid_mark(SP,Invalid),
        mark_all_entries(Module,Invalid),
        add_changed_module(Module,Base,TopLevel,transitive,no),
        invalidate_callers(Module,ModList1)
    ;
        invalidate_callers(Module,ModList1)
    ),
    append(ModList,ModList1,NewModList),
    propagate_invalid_info_(TopLevel,NewModList).

%%Marks all entries, even if they are of different domains.
mark_all_entries(Module,Mark):-
    ( % (failure-driven loop)
      retract_fact(registry(SgKey,Module,OldReg)),
        regdata_set_mark(OldReg, Mark, NewReg),
        assertz_fact(registry(SgKey,Module,NewReg)),
        fail
    ; true
    ).

%%Marks as invalid all the entries corresponding to the callers of invalid 
%%entries in Module.
invalidate_callers(Module,ModList):-
    current_pp_flag(success_policy,SP),
    not_valid_mark(SP,Invalid),
    Reg = regdata(_,AbsInt,_Sg,_Call,_Succ,_Spec,Imdg,_,Invalid),
    findall((AbsInt,Imdg),registry(_,Module,Reg),ListOfImdgs),
    invalidate_callers_1(Module,ListOfImdgs,ModList).

invalidate_callers_1(_,[],[]) :- !.
invalidate_callers_1(Module,[(AbsInt,ImdgList)|ListOfImdgs],ModList):-
    current_pp_flag(success_policy,SP),
    not_valid_mark(SP,Invalid),
    mark_callers_registry(ImdgList,_,_ParentReg,AbsInt,Module,Invalid,BasenamesMarked),
    include_no_force(BasenamesMarked,ModsMarked),
    invalidate_callers_1(Module,ListOfImdgs,ModList1),
    append(ModsMarked,ModList1,ModList).

include_no_force([],[]).
include_no_force([B|Bs],[(B,no_force)|Ms]):-
    include_no_force(Bs,Ms).

%% ********************************************************************
%% ********************************************************************

:- pred get_modules_to_analyze(+AbsInt,+TopLevel,-ModList) 
# "Obtains the list of modules to analyze. This list is formed by the modules
  which  have their .reg file outdated, or if the module is not
  completely analyzed (some of the entries in the .reg file are marked
  or invalid). For those modules which have no .reg file, the
  @em{parents} of the module are included in the list (as there are
  no call patterns for those modules without .reg file). 

  The structure of the elements in the list is a term
  (@var{Mod},@var{Depth},@var{Force}), where @var{Mod} stands for the
  module name, @var{Depth} is the maximum depth without cycles in the
  intermodular graph, and @var{Force} marks those modules which must
  be completely reanalyzed (only useful for the parents of the modules
  with no reg file).

  @var{AbsInt} can be either an abstract domain name or a list of
  abstract domains.".

get_modules_to_analyze(AbsInt,TopLevelFile,ModList):-
    retractall_fact(module_to_analyze(_,_)),
    retractall_fact(module_to_analyze_parents(_)),
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,AbsBase,_),
    %
    retractall_fact(delay_patch_registry(_,_,_)),
    get_intermodule_graph(AbsFile,check_registry_up_to_date(AbsInt,AbsBase)),
    delayed_patch_registry,
    compute_intermodule_graph_depth(AbsBase),
    include_parents(AbsBase),
    ( setof((M,D,F), module_to_analyze_depth(M,D,F), ModList)
    ; ModList = []),
    retractall_fact(module_to_analyze(_,_)),
    retractall_fact(module_to_analyze_parents(_)),
    retractall_fact(intermodule_graph_depth(_,_)),
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)).

module_to_analyze_depth(M,D,F) :-
    module_to_analyze(M,F),
    intermodule_graph_depth(M,D).

:- data delay_patch_registry/3. % ugly hack to delay patch until src_changed/1 is known

% module_to_analyze(Module,ForceAnalysis).
:- data module_to_analyze/2.  
:- data module_to_analyze_parents/1.

% Succeeds if the registry of Base is up-to-date with respect to
% AbsInt. TopLevelBase is handled in a special way, as it is
% checked that the module entries have been added to .reg file.
%
% AbsInt can be either a domain name or a list of domains.

% TODO: comment above is not correct now 

check_registry_up_to_date(Base,AbsInt,TopLevelBase):-
    just_module_name(Base,Module),
    cleanup_registry(Module),
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        read_registry_file_(Module,Base,quiet) % TODO:{JF} assume never fails!
    ; true
    ),
    assertz_fact(delay_patch_registry(Base,AbsInt,TopLevelBase)).

delayed_patch_registry :-
    ( % (failure-driven loop)
      retract_fact(delay_patch_registry(Base,AbsInt,TopLevelBase)),
        delayed_patch_registry_(Base,AbsInt,TopLevelBase),
        fail
    ; true
    ).

delayed_patch_registry_(Base,AbsInt,TopLevelBase) :-
    just_module_name(Base,Module),
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        patch_registry_(Module,Base,NeedsTreat), % TODO:{JF} assume never fails!
        ( NeedsTreat = no,
          all_entries_unmarked(Base,AbsInt,TopLevelBase) ->
            true
        ; add_module_to_analyze(Base,no_force)
        )
    ; %% If there is no registry file, parents of this module are added
      %% for analysis (as call patterns are needed for the imported module).
      asserta_fact(module_to_analyze_parents(Base))
    ).

%% Converts module_to_analyze_parents(X) into
%% module_to_analyze(Y,force), where Y is parent of X.
include_parents(TopBase):-
    current_fact(module_to_analyze_parents(Base)),
    ( Base == TopBase -> %% TopLevel module must be added even if it has parents.
        add_module_to_analyze(Base,force)
    ;
        true
    ),
    ( current_fact(intermodule_graph(_,Base)) ->
        current_fact(intermodule_graph(Parent,Base)),
        ( module_to_analyze_parents(Parent) ->
            true
        ;
            ( module_is_processable(Parent) ->
                add_module_to_analyze(Parent,force)
            ;
                true
            )
        )
    ; %% if there are no parents, Base must be added.
        ( module_is_processable(Base) ->
            add_module_to_analyze(Base,force)
        ;
            true
        )
    ),
    fail.
include_parents(_TopBase):-
    retractall_fact(module_to_analyze_parents(_)).

add_module_to_analyze(Base,Force):-
    ( current_fact(module_to_analyze(Base,Force0),Ref) ->
      ( Force = force, Force0 = no_force ->
        erase(Ref),
        asserta_fact(module_to_analyze(Base,force))
      ; true
      )
    ; asserta_fact(module_to_analyze(Base,Force))
    ).

% get_related_module(Base,IFile):-
%       imports_pred(Base,IFile,_F,_A,_DefType,_Meta,_EndFile).

%% Succeeds if all entries are unmarked for AbsInt.
%% AbsInt can be either a domain name or a list of domains.
all_entries_unmarked(Base,AbsInt,TopLevelBase):-
    just_module_name(Base,Module),
    (
        Base = TopLevelBase ->
        current_fact(registry_headers(Module,entries_already_analyzed(Domains))),
        list_member(AbsInt,Domains)
    ;
        true
    ),
    \+ current_fact(registry(_,Module,regdata(_,AbsInt,_,_,_,_,_,_,'+'))),
    \+ current_fact(registry(_,Module,regdata(_,AbsInt,_,_,_,_,_,_,'-'))).

true(_). % TODO: why?

% Succeeds when either first arg is an atom and it is in the list of the second
% arg, or if the intersection of both lists is not empty (it uses unification).
list_member([A|_As],Bs):-
    member(A,Bs).
list_member([_|As],Bs):-
    list_member(As,Bs).
list_member(A,Bs):-
    member(A,Bs).

%% ********************************************************************
%% INTERMODULAR GRAPH TRAVERSAL
%% ********************************************************************

:- pred intermodule_graph(Caller,Called) 
# "Module graph. It succeeds iff module with basename @var{Caller}
  imports module with basename @var{Called}.".

:- data intermodule_graph/2. 

:- data intermodule_list/1. 

:- data include_list/1. 

:- data initial_vertex/2.  %% For tarjan algorithm.

:- data src_not_changed/1.
:- data src_changed/1. % IG: data for storing which modules were
                  % detected to be modified by the compiler (and
                  % therefore need processing)

add_src_changed(Base) :-
    current_fact(src_changed(Base)), !.
add_src_changed(Base) :-
    assertz_fact(src_changed(Base)).

unset_src_changed(Base) :-
    retract_fact(src_changed(Base)), !.
unset_src_changed(_).

:- pred get_intermodule_graph(+AbsFile,+GoalBeforeLoading) 
# "Obtains in @pred{intermodule_graph/2} the dependencies among
  modules of the program unit given by the module in file
  @var{AbsFile} (depending on punit_boundary flag, library modules
  are included or not in the program unit).  For every module included
  in the intermodular graph, @var{ProcessGoal} is called.".
% TODO:{DOC} 
%   get_intermodule_graph/2 is called before analysis,
%   this predicate fills src_changed/1, which is used by 
%   gen_registry_info/?, which is called (for each module) after analysis

%get_intermodule_graph(AbsFile,_GoalBeforeLoading):-
%       read_grf_file(AbsFile),
%       !.
get_intermodule_graph(AbsFile,GoalBeforeLoading):-
    retractall_fact(intermodule_graph(_,_)),
    retractall_fact(intermodule_list(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)),
    retractall_fact(src_changed(_)),
    retractall_fact(src_not_changed(_)),
    error_protect(ctrlc_clean(
                                 process_files_from(AbsFile, zzz, any, 
                                 process_one_module, 
%                                    check_stop_one_module(GoalBeforeLoading), false, true)
                                 check_stop_one_module(GoalBeforeLoading), false, redo_one_module)
                             ),fail). % TODO: fail or abort?

% TODO: remove old code once we are happy with this version
quick_setup.
%quick_setup :- fail.

redo_one_module(Base) :- quick_setup, !,
    % we are here because the itf was up to date and
    % c_itf is asking if we want to re-treat the module,
    % lets add Base to the not-changed set and fill the intermod graph
    ( current_fact(src_not_changed(Base)) -> true
    ; assertz_fact(src_not_changed(Base)),
      fill_intermod_graph(Base)
    ),
    fail.
redo_one_module(Base) :-
    % we are here because the itf was up to date and
    % c_itf is asking if we want to re-treat the module,
    % lets remember this
    ( current_fact(src_not_changed(Base)) -> true
    ; assertz_fact(src_not_changed(Base))
    ).

% TASK: check that this is really traversing all dependencies
process_one_module(Base):- quick_setup, !,
    % add to src_changed/1 only if
    ( src_not_changed(Base) ->
        true
    ;
      add_src_changed(Base), % added to know that a module needs processing
      fill_intermod_graph(Base)
    ).
% TASK: check that this is really traversing all dependencies
process_one_module(Base):-
    % add to src_changed/1 only if
    ( src_not_changed(Base) ->
        true
    ;
      add_src_changed(Base) % added to know that a module needs processing
    ),
    fill_intermod_graph(Base).

fill_intermod_graph(Base) :-
    asserta_fact(intermodule_list(Base)),
    ( % setof(IFile,get_related_module(Base,IFile),IFileList0) ->
      findall(IFile,uses(Base,IFile),IFileList0) ->
        file_path(Base,BasePath),
        working_directory(Old,BasePath),
        processable_basenames(IFileList0,IBaseList),
        findall(I, includes(Base,I), IncludeList0),
        basenames(IncludeList0,IncludeList),
        assert_include_list(IncludeList),
        working_directory(BasePath,Old),
        assertz_fact(initial_vertex(Base,IBaseList)),
        assert_intermodule_graph(IBaseList,Base)
    ;
        assertz_fact(initial_vertex(Base,[]))
    ).

file_path(Base,Path):-
    absolute_file_name(Base,'_opt','.pl','.',_,_,Path).

%% Asserts the list of imported  modules received as argument. 
assert_intermodule_graph([],_Base).
assert_intermodule_graph([IBase|IBaseList],Base):-
    asserta_fact(intermodule_graph(Base,IBase)),
    assert_intermodule_graph(IBaseList,Base).

assert_include_list([]).
assert_include_list([I|Is]):-
    (
        current_fact(include_list(I)) ->
        true
    ;
        asserta_fact(include_list(I))
    ),
    assert_include_list(Is).

%% Calls Goal only once, adding Base as its first argument.
%% This predicate does not fail.
call_once_with_extra_arg(Base,Goal0):-
    Goal0 =.. [PredName | Args],
    Goal =.. [PredName, Base | Args],
    call(Goal),!.
call_once_with_extra_arg(_Base,_Goal0).

%% Given a list of file names, removes from them the modules
%% which are not processable, and returns the list of the remaining basenames.
processable_basenames([],[]).
processable_basenames([File|Files],[Base|Bases]):-
%%      Current dir is the one of the base being processed.
    absolute_file_name(File,'_opt','.pl','.',_,Base,_),
    module_is_processable(Base), !,
    processable_basenames(Files,Bases).
processable_basenames([_File|Files],Bases):-
    processable_basenames(Files,Bases).

basenames([],[]).
basenames([File|Files],[Base|Bases]) :-
%%      Current dir is the one of the base being processed.
    absolute_file_name(File,'_opt','.pl','.',_,Base,_),
    basenames(Files,Bases).

%% Checks if module traversal must stop at current Base (not reading below it).
check_stop_one_module(_GoalBeforeLoading,Base) :-
    \+ module_is_processable(Base), !.
check_stop_one_module(GoalBeforeLoading,Base) :-
    \+ call_once_with_extra_arg(Base,GoalBeforeLoading),
    % TODO:{JF} not reachable? never?
    asserta_fact(intermodule_list(Base)),  %% There is no need to load Base, but 
    assertz_fact(initial_vertex(Base,[])). %% these facts must be asserted.

%% ********************************************************************
%% INTERMODULAR GRAPH DEPTH COMPUTATION
%% ********************************************************************

:- pred intermodule_graph_depth(Module,Depth)
# "Module @var{Module} has depth @var{Depth} in the intermodular graph
  contained in @pred{intermodule_graph/2}. All modules included in a
  strongly connected component are labelled with the same depth.".

:- data intermodule_graph_depth/2. 

:- pred compute_intermodule_graph_depth(TopLevel) 
# "Computes the intermodule graph (contained in
  @pred{intermodule_graph/2}) with depths and stores it in
  @pred{intermodule_graph_depth/2}. The depth of every node in the
  graph is computed considering that all nodes in a strongly connected
  component are labelled with the same depth. The depth of a given
  node is the largest depth from the top-level module.

  This predicate must be called after calling get_intermodule_graph/2
  as it needs initial_vertex/2 already populated.".
compute_intermodule_graph_depth(TopLevel) :-
    retractall_fact(intermodule_graph_depth(_,_)),
    findall(vertex(M1,Ms,0,0,undef), initial_vertex(M1,Ms), Vertex),
    intermod_sccs(Vertex,Cs),
    compute_noncyclic_depth(TopLevel,Cs).

:- pred intermod_sccs(in(Vertices),out(Cs)) 
# "@var{Cs} is the list of strongly connected components in the
  digraph represented by the list @var{Vertex} of vertex/5
  structures.".

intermod_sccs([],[]) :- !.
intermod_sccs(Vertex,Cs) :-
    (Vertex == [] ->
        Cs = []
    ;
        Vertex = [V|Vs],
        S0 = state([V|Vs],V,[],0),
        step2(S0,Cs)
    ).

:- data module_scc/2.       % Module M belongs to scc S.
:- data interscc_edge/2.   % Scc S1 is connected to Scc S2.
:- data scc_depth/2.        % Scc S has depth D.

:- pred compute_noncyclic_depth(in(TopLevel),in(Cs)) 
# "computes the depth of every module, labelling the modules in a
  strongly connected component (in @var{Cs}) with the same depth. The
  result is stored in intermodule_graph_depth/2.".
compute_noncyclic_depth(TopLevel,Cs) :-
    retractall_fact(module_scc(_,_)),
    retractall_fact(interscc_edge(_,_)),
    retractall_fact(scc_depth(_,_)),
    ( Cs = [] ->
        store_sccs([[TopLevel]],0)
    ;
        store_sccs(Cs,0)
    ),
    gen_interscc_edges,
    current_fact(module_scc(TopLevel,STopLevel)),
    compute_scc_depth(STopLevel,0),
    gen_intermodule_graph_depth,
    retractall_fact(module_scc(_,_)),
    retractall_fact(interscc_edge(_,_)),
    retractall_fact(scc_depth(_,_)).

store_sccs([],_).
store_sccs([C|Cs],Id) :-
    store_scc(C,Id),
    Id1 is Id+1,
    store_sccs(Cs,Id1).

store_scc([],_).
store_scc([M|Ms],Id) :-
    assertz_fact(module_scc(M,Id)),
    store_scc(Ms,Id).

gen_interscc_edges :-
    current_fact(intermodule_graph(M,N)),
    current_fact(module_scc(M,SM)),
    current_fact(module_scc(N,SN)),
    SM \== SN,
    \+ current_fact(interscc_edge(SM,SN)),
    assertz_fact(interscc_edge(SM,SN)),
    fail.
gen_interscc_edges.

compute_scc_depth(Scc,Depth) :-
    ( current_fact(scc_depth(Scc,Depth0),Ref) ->
        ( Depth0 < Depth ->
            erase(Ref),
            assertz_fact(scc_depth(Scc,Depth))
        ;
            true
        )
    ;
        assertz_fact(scc_depth(Scc,Depth))
    ),
    recurse_scc_children(Scc,Depth).

recurse_scc_children(Scc,Depth):-
    Depth1 is Depth + 1,
    current_fact(interscc_edge(Scc,SccChild)),
    compute_scc_depth(SccChild,Depth1),
    fail.
recurse_scc_children(_Scc,_Depth).

gen_intermodule_graph_depth:-
    current_fact(scc_depth(Scc,Depth)),
    current_fact(module_scc(Mod,Scc)),
    assertz_fact(intermodule_graph_depth(Mod,Depth)),
    fail.
gen_intermodule_graph_depth.

%% ********************************************************************
%% ********************************************************************

:- pred write_registry_file(Base,Module,Verb) : atm * atm * atm
# "Writes to disk the registry information stored in memory for module
  @var{Module} which has as base file name @var{Base}.".
write_registry_file(Base,Module,_Verb):-
    get_module_filename(reg,Base,RegName),
    open(RegName,write,Stream), % overwrites the previous file.
    write_registry_header(Module,Stream),
    current_output(CO),
    set_output(Stream),
    pplog(p_abs, ['{Writing ',RegName]),
    write_registry_file_types(Module),
    write_registry_file_loop(Module),
    set_output(CO),
    close(Stream),
    pplog(p_abs, ['}']).

write_registry_file_types(Module):-
    current_fact(typedb(Module,TypeDef)),
    fast_write(TypeDef),
    fail.
write_registry_file_types(_Module).

write_registry_file_loop(Module):-
    current_fact(registry(_,Module,Reg)),
    fast_write(Reg),
    fail.
write_registry_file_loop(_Module).

:- pred change_open_mode(+Base,+OpenMode) 
# "@var{OpenMode} is the new open mode of the module with basename
  @var{Base}. @var{OpenMode} can take the values @code{read_write}
  and @code{read_only}.".
change_open_mode(Base,OpenMode):-
    just_module_name(Base,Module),
    read_registry_file(Module,Base,verbose),  %% if it is not loaded yet, loads it.
    retract_fact(registry_headers(Module,open_mode(_OldOpenMode))),
    asserta_fact(registry_headers(Module,open_mode(OpenMode))),
    add_changed_module(Module,Base,Module,current,no).

:- pred open_mode(Base,Type,OpenMode) 
# "Module with basename @var{Base} is of type @var{Type} and it is
   opened with mode @var{OpenMode}. @var{Type} can be @code{user} or
   @code{library}. @var{OpenMode} is used to indicate if an imported
   module's registry can be updated. It can take the values
   @code{read_write} or @code{read_only}.".
open_mode(Base,Type,OpenMode) :-
%% It only works if module's registry has been already loaded. If it has not, it fails.
    just_module_name(Base,Module),
    current_fact(registry_headers(Module,open_mode(OpenMode))),
    ( is_library(Base) ->
      Type = library
    ; Type = user
    ).

:- pred registry_is_empty(+AbsInt,+Mod,+Base): atm * atm * atm
# "Succeeds if the registry of module @var{Mod} with base name
  @var{Base} is empty for the abstract domain @var{AbsInt}.".
registry_is_empty(AbsInt,Mod,Base):-
    read_registry_file(Mod,Base,quiet),
    \+ current_fact(registry(_,Mod,regdata(_,AbsInt,_,_,_,_,_,_,_))).

:- pred module_is_processable(+Base) 
# "Succeeds if module in @var{Base} can be processed by intermodular
  preprocessing tools. This predicate may have to load the registry
  file of that module, in order to check that the module has
  read-write mode.".
module_is_processable(B):-
    current_pp_flag(punit_boundary,ProcessLibs),
    module_is_processable_(B,ProcessLibs).

module_is_processable_(Base,_ProcessLibs):-
    user_module(Base), !, fail.
module_is_processable_(Base,ProcessLibs):-
    current_fact(module_is_processable_cache(Base,Processable,ProcessLibs)), !,
    Processable == yes.
module_is_processable_(Base,ProcessLibs) :- %% all current modules are processable
    curr_file_base(Base,_Module), !,
    assert_if_not_asserted_yet(module_is_processable_cache(Base,yes,ProcessLibs)).
module_is_processable_(Base,ProcessLibs):-
    is_library(Base), 
    \+ (ProcessLibs == on), !,
    assert_if_not_asserted_yet(module_is_processable_cache(Base,no,off)),
    fail.
module_is_processable_(Base,ProcessLibs):-
    ProcessLibs = bundle,
    top_level(TopLevel),
    reverse_bundle_path(TopLevel, Bundle, _),
    reverse_bundle_path(Base, Bundle0, _),
    \+ Bundle0 = Bundle, !,
    assert_if_not_asserted_yet(module_is_processable_cache(Base,no,bundle)),
    fail.
module_is_processable_(Base,ProcessLibs):-
    just_module_name(Base,Module),
    read_registry_file(Module,Base,quiet),  %% just in case. % TODO:{JF2} does not need to check src_changed/1
    open_mode(Base,_,read_write), !,
    assert_if_not_asserted_yet(module_is_processable_cache(Base,yes,ProcessLibs)).
module_is_processable_(Base,ProcessLibs):-
    assert_if_not_asserted_yet(module_is_processable_cache(Base,no,ProcessLibs)),
    fail.

assert_if_not_asserted_yet(module_is_processable_cache(A,B,C)) :-
    \+ current_fact(module_is_processable_cache(A,B,C)), !,
    assertz_fact(module_is_processable_cache(A,B,C)).
assert_if_not_asserted_yet(_).


:- pred module_is_processable_cache(Base,Processable,ProcessLibsFlag)
# "Cache predicate for speeding up when checking whether a module is
   processable or not. It unifies @var{Processable} with 'yes' if
   module in @var{Base}.pl is processable, or 'no' if it is not.
   @var{ProcessLibs} contains the value of 'punit_boundary' flag
   for which the module is or is not processable.".

:- data module_is_processable_cache/3.

%% ********************************************************************
%% TOOLBOX
%% ********************************************************************

% TODO: get from the compiler
curr_file_base(Base,Module):-
    curr_file(File,Module),
    get_file_base(File,Base).

get_file_base(File,Base):-
    path_splitext(File,Base,_).

% TODO: not used (done with compiler)
% :- pred registry_up_to_date(Module,PLFile) : atom * atom
% # "Succeeds if registry header of @var{Module} refers to current
%   version of @var{PLFile} (comparing modification dates).".
% registry_up_to_date(Module,PlName):-
%       ( current_fact(registry_headers(Module,pl_date(RegTime))) ->
%         modif_time(PlName, PlTime),
%         RegTime = PlTime
%       ; true).

:- pred less_or_equal_mark(+SP,?Mark0,?Mark1) : atm * atm * atm
# "Given a success policy @var{SP}, succeeds if @var{Mark0} is less or
  equal than @var{Mark1}. Invalid marks are the biggest marks.".
less_or_equal_mark(_SP,Mark,Mark) :- !.      % if one of the marks is a free var, it is instantiated here.
less_or_equal_mark(_SP,unmarked,_Mark) :- !.
less_or_equal_mark(SP,Mark0,Mark1):-
    may_be_improved_mark(SP,Mark0),
    not_valid_mark(SP,Mark1).

%% --------------------------------------------------------------------

:- pred add_changed_module(+Module,+Base,+SourceModule,+Mode,+ReqReanalysis)
# "Adds a new entry to @pred{changed_module/6}. @var{Module} registry
  info has been changed as a result of analyzing @var{SourceModule},
  and the relatioship between @var{SourceModule} and @var{Module} is
  @var{Mode} (@code{imported}, @code{caller} or @code{current}).".
add_changed_module(Module,Base,SourceModule,Mode,ReqReanalysis):-
    changed_module(Module,Base,SourceModule,Mode,current,ReqReanalysis), !.
add_changed_module(Module,Base,SourceModule,Mode,ReqReanalysis):-
    assertz_fact(changed_module(Module,Base,SourceModule,Mode,current,ReqReanalysis)).

add_caller_module(M,_):-
    caller_module(M,_), !.
add_caller_module(M,Base):-
    assertz_fact(caller_module(M,Base)).

add_caller_modules([],[]).
% add_caller_modules([_|Ms],[B|Bs]):-
%       curr_file(B,_), !, %% Current modules are not considered caller modules.
%       add_caller_modules(Ms,Bs).
add_caller_modules([M|Ms],[B|Bs]):-
    add_caller_module(M,B),
    add_caller_modules(Ms,Bs), !.

%% 'user' module cannot be treated as a normal module.
user_module(user).  

%% ====================================================================

:- pred compute_external_reachability
# "For every exported predicate defined in the current module,
  calculates all the imported predicates which are reachable in a
  given abstract domain. Results are generated in
  graph_reachable/9".
compute_external_reachability :-
    ( % failure-driven loop
      domain(AbsInt),
        compute_external_reachability_1(AbsInt),
        fail
    ; true ).

:- pred graph_reachable(KeyFrom,AbsInt,SgFrom,ProjFrom,IdFrom,ModuleFrom,ImportedId,ImportedSg,ImportedASub) 
# "There is a path from node @var{IdFrom}, key @var{KeyFrom} in module
  @var{ModuleFrom} to the imported call pattern
  @var{ImportedSg}/@var{ImportedASub} in the abstract and-or
  graph. @var{ImportedId} is the Id of the complete containing the
  imported call pattern (used to speedup the process, avoiding the
  comparison of abstract substitutions with
  @var{ImportedSg}/@var{ImportedASub}.)".

:- data pending_graph/9.
:- data graph_reachable/9.
:- data graph_visited/7.    %% visited paths in the abstract graph.
                        %% (just to avoid cycles). It has the same structure than graph_reachable.

compute_external_reachability_1(AbsInt) :-
    retractall_fact(graph_reachable(_,_,_,_,_,_,_,_,_)),
    retractall_fact(graph_visited(_,_,_,_,_,_,_)),
    initial_graph(AbsInt),
    graph_closure(AbsInt),
    retractall_fact(graph_visited(_,_,_,_,_,_,_)),
    !.

exported_key(K) :-
    exports(Sg, _M), % _M is current file
    predkey_from_sg(Sg, K).

:- data processed_sg/2.
% processed_sg is also used for getting the imported used modules

initial_graph(AbsInt) :-
    retractall_fact(processed_sg(_,_)),
    ( % failure-driven loop over imported completes
      imported_complete(SgKey,AbsInt,Sg,Proj,Id,Ps,Mod), % backtrack here
        assert_initial_arcs(Ps, AbsInt, Id, Sg, Proj),
        add_processed_sg(SgKey, Mod, Sg),
        fail
    ; true ).

imported_complete(SgKey,AbsInt,Sg,Proj,Id,Parents,Mod) :-
    complete(SgKey,AbsInt,Sg,Proj,_,Id,Parents),
    \+ Id = no,
    get_module_from_sg(Sg, Mod),
    \+ curr_file(_, Mod).

add_processed_sg(SgKey, Mod, Sg) :-
    \+ processed_sg(SgKey, Sg),
    current_itf(imports, Sg, File),
    assertz_fact(processed_sg(SgKey, Sg)),
    add_program_module_base(Mod, File).

assert_initial_arcs([],_,_,_,_).
assert_initial_arcs([(PLitKey,PId)|RefList],AbsInt,Id,Sg,Proj):-
    get_parent_key(PLitKey,PId,AbsInt,PKey),
    decode_litkey(PLitKey,F,A,_,_),
    functor(CSg,F,A), % This is because of how meta_calls
                      % indexes/ids are treated
    get_module_from_sg(CSg, PModId),
    key_or_id_complete(PKey,AbsInt,PSg,PProj,_,PId,_,_),
    add_pending_graph(PKey,AbsInt,PSg,PProj,PId,PModId,Id,Sg,Proj),
    assert_initial_arcs(RefList,AbsInt,Id,Sg,Proj).

add_pending_graph(NKeyPrev,AbsInt,_,_,IdPrev,ModIdPrev,Id,_,_):-
    current_fact(pending_graph(NKeyPrev,AbsInt,_,_,IdPrev,ModIdPrev,Id,_,_)),
    !.
add_pending_graph(NKeyPrev,AbsInt,SgPrev,ProjPrev,IdPrev,ModIdPrev,Id,Sg,Proj):-
    assertz_fact(pending_graph(NKeyPrev,AbsInt,SgPrev,ProjPrev,IdPrev,ModIdPrev,Id,Sg,Proj)).

:- pred graph_closure(AbsInt) # "Calculates the reachability graph
    closure, given the initial @pred{pending_graph/9} nodes. This
    predicate goes backwards from imported predicates patterns
    towards exported predicates patterns, though it does not
    traverse the boundaries between modules (in case there were
    several current modules.)".
graph_closure(AbsInt):-
    repeat,
    ( retract_fact(pending_graph(Key0,AbsInt,Sg0,Proj0,Id0,Module0,Id,Sg,Proj)) ->
        process_pending_graph(Key0,AbsInt,Sg0,Proj0,Id0,Module0,Id,Sg,Proj),
        % in process_pending_graph/1 we allow assertz_fact(pending_graph(X))
        fail
    ; true
    ),
    !.

process_pending_graph(Key0,AbsInt,Sg0,Proj0,Id0,Module0,Id,Sg,Proj) :-
    assertz_fact(graph_reachable(Key0,AbsInt,Sg0,Proj0,Id0,Module0,Id,Sg,Proj)),
    assertz_fact(graph_visited(Key0,AbsInt,Id0,Module0,Id,Sg,Proj)),
    get_complete_parents(Key0,AbsInt,Id0,RefList),
    extend_graph_reachable(RefList,AbsInt,Module0,Id,Sg,Proj).

% get_complete_parents(+Key0,+AbsInt,+Id0,?RefList)
get_complete_parents(Key0,AbsInt,Id0,RefList) :-
    current_fact(complete(Key0,AbsInt,_,_,_,Id0,RefList)), !.

:- pred extend_graph_reachable(+AbsInt,+Module,+Id,+Sg,+Proj,+RefList).
extend_graph_reachable([], _AbsInt,_Module,_Id,_Sg,_Proj).
extend_graph_reachable([(KeyPrev,IdPrev)|RefList],AbsInt,Module,Id,Sg,Proj):-
    decode_litkey(KeyPrev,F,A,_,_), !, % IG if this fails, the parent is the entry
    get_predkey(F,A,NKeyPrev0),
    key_or_id_complete(NKeyPrev0,AbsInt,SgPrev,ProjPrev,_,IdPrev,_,NKeyPrev),
    ( \+ already_visited(NKeyPrev,AbsInt,IdPrev,Module,Id,Sg,Proj) ->
        add_pending_graph(NKeyPrev,AbsInt,SgPrev,ProjPrev,IdPrev,Module,Id,Sg,Proj)
    ;
        true
    ),
    extend_graph_reachable(RefList, AbsInt,Module,Id,Sg,Proj).
extend_graph_reachable([_|RefList],AbsInt,Module,Id,Sg,Proj):-
    extend_graph_reachable(RefList, AbsInt,Module,Id,Sg,Proj).

% already_visited(+Key0,+AbsInt,+Id0,+Module,+Sg,+Proj).
already_visited(Key0,AbsInt,Id0,Module,Id,_Sg,_Proj):-
    current_fact(graph_visited(Key0,AbsInt,Id0,Module,Id,_Sg0,_Proj0)), !.

% Id is unique
key_or_id_complete(SgKey,AbsInt,Sg,Proj,Succ,Id,Ref,SgKey):-
    current_fact(complete(SgKey,AbsInt,Sg,Proj,Succ,Id,Ref)), !.
key_or_id_complete(_SgKey0,AbsInt,Sg,Proj,Succ,Id,Ref,SgKey):-
    current_fact(complete(SgKey,AbsInt,Sg,Proj,Succ,Id,Ref)), !.

:- pred get_module_from_sg(+Sg, ?Module) :: term * atm
# "@var{Module} is the name of the module for the predicate to which
  call pattern @var{Sg} corresponds.".
% IG: another sort of module_split?
get_module_from_sg(Sg,Module):-
    current_itf(imports,Sg,Module0), atom(Module0),
    !,
    ( just_module_name(Module0,Module) ->
        true
    ;
        Module = Module0
    ).
get_module_from_sg(Sg,Module):-
    current_itf(defines_pred,Sg,Module0),
    !,
    ( just_module_name(Module0,Module) ->
        true
    ;
        Module = Module0
    ).
get_module_from_sg(Sg,Module):-
    % TODO: why? (inefficient!)
    functor(Sg,MF,_),
    module_split(MF, M, _),
    !,
    M = Module.
get_module_from_sg(_,''). %% Oops, '\+/1' has no module in Sg. % TODO: ??

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% IG improvements and new functionality

:- pred cleanup_persistent_registry(Bases) : list
    #"Removes the *.reg files associated to @var{Bases}.".
cleanup_persistent_registry(Bases) :-
    cleanup_p_abs_all,
    ( % failure-driven loop
      member(B, Bases),
        get_module_filename(reg,B,RegName),
        del_file_nofail(RegName),
        fail
    ; true).

:- pred update_registry_dependencies(AbsInt, File, Mod)
    #"Updates the registry: abstract (for domain @var{AbsInt}) and
     dependencies information of module @var{Mod}. This update
     consists on removing CPs that do not exist,
     updating the current entries of the registry and adding new
     entries.".
update_registry_dependencies(AbsInt, File, Mod) :-
    delete_unused_dep_entries(AbsInt, Mod),
    update_GAT_entries(AbsInt, File, Mod).

% Imdg are the modules from which this CP was generated
% Chdg are the (SgKey, Id, Sg, Proj) in which this CP generates a call (child)
delete_unused_dep_entries(AbsInt, Mod) :-
    ( % failure-driven loop
      current_fact(registry(SgKey, Mod, ExpReg), Ref),
      ExpReg = regdata(RId,AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,Mark),
      check_curr_entry_id(RId), % The entry was analyzed in this iteration
        abs_sort(AbsInt, Call, Call_s),
        still_reachable_children(Chdg, SgKey, Sg, Call_s, RId, AbsInt, NChdg),
        erase(Ref),
        NExpReg = regdata(RId,AbsInt,Sg,Call,Succ,Spec,Imdg,NChdg,Mark),
        assertz_fact(registry(SgKey,Mod,NExpReg)),
        fail
    ; true).

still_reachable_children([], _, _, _, _, _, []).
still_reachable_children([Child|Chs], SgKey, Sg ,Call, PId, AbsInt, NewChs) :-
    Child = (ChRId, ChSg, ChProj),
    ( cp_still_reachable(SgKey, Sg, Call, ChSgKey, ChSg, ChProj, AbsInt) ->
        NewChs = [Child|NChs]
    ;
        predkey_from_sg(ChSg, ChSgKey),
        remove_parent_from_reg(ChSgKey, ChRId, PId),
        NewChs = NChs
    ),
    still_reachable_children(Chs, SgKey, Sg, Call, PId, AbsInt, NChs).

cp_still_reachable(SgKey, Sg, Call, ChSgKey, ChSg, ChProj, AbsInt) :-
    graph_reachable(SgKey,AbsInt,PSg,PCall,_,_,_,ChSg,ImpProj), %backtrack here
    abs_sort(AbsInt, PCall, PCall_s),
    identical_proj(AbsInt, Sg, Call, PSg, PCall_s),
    abs_sort(AbsInt, ImpProj, ImpProj_s),
    abs_sort(AbsInt, ChProj, ChProj_s),
    identical_proj(AbsInt, ChSg, ChProj_s, ChSg, ImpProj_s), !,
    predkey_from_sg(ChSg,ChSgKey).

remove_parent_from_reg(SgKey, RId, ParentRId) :-
    retract_fact(registry(SgKey, Mod, regdata(RId,AbsInt,Sg,Proj,Succ,Spec,Imdg,Chdg,Mark))),
    remove_RId_from_dg(Imdg, ParentRId, NImdg),
    ( NImdg = [] ->
        % If the CP does not exist, remove the registry and its children
         ( member((ChRId, ChSgKey, _, _), Chdg),
             predkey_from_sg(ChSgKey, ChKey),
             remove_parent_from_reg(ChKey, ChRId, RId),
             fail
         ;
             true
         )
    ;
        NReg = regdata(RId,AbsInt,Sg,Proj,Succ,Spec,NImdg,Chdg,Mark),
        assertz_fact(registry(SgKey, Mod, NReg))
    ),
    % add change so it is written in the disk registry later
    program_module_base(Mod, ModBase),
    curr_file(_, CurrModule),
    add_changed_module(Mod,ModBase,CurrModule,imported,no).

remove_RId_from_dg([], _, []).
remove_RId_from_dg([P|Ps], ParentRId, Ps) :-
    P = (ParentRId, _, _, _), !.
remove_RId_from_dg([P|Ps], ParentRId, [P|NewPs]) :-
    remove_RId_from_dg(Ps, ParentRId, NewPs).

add_parent_to_reg(SgKey, RId,ParentKey,ParentRId) :-
    current_fact(registry(SgKey, Mod, Reg), Ref),
    Reg = regdata(RId,AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,Mark),
    registry(ParentKey, _, PReg),
    PReg = regdata(ParentRId,_,PSg,PProj,_,_,_,_,_), !,
    ( add_to_dglist(Imdg,ParentRId,PSg,PProj,NImdg) ->
      erase(Ref),
      NReg = regdata(RId,AbsInt,Sg,Call,Succ,Spec,NImdg,Chdg,Mark),
      assertz_fact(registry(SgKey,Mod,NReg))
    ; true ).

update_children([], L,_,_,L).
update_children([(Id,Sg,Proj)|AddCh],Ch,AbsInt,Mod,NCh) :-
    add_child(Ch,Id,Sg,Proj,ACh),
    add_imported_typedefs(AbsInt,Mod,[Proj]),
    update_children(AddCh,ACh,AbsInt,Mod,NCh).

add_child(Ch, Id, _, _, Ch) :-
    member((Id, _, _), Ch), !.
add_child(Ch, Id, Sg, Proj, [(Id,Sg,Proj)|Ch]).

add_to_children(IRId,_,_) :-
    child_to_add(IRId, _, _), !.
add_to_children(IRId,ImpSg,ImpProj) :-
    assertz_fact(child_to_add(IRId,ImpSg,ImpProj)).

:- data child_to_add/3.

registry_id(SgKey, Sg, Proj, AbsInt, RId, Reg) :-
    abs_sort(AbsInt,Proj,Proj_s),
    registry(SgKey,_,Reg), % backtracking here
    Reg = regdata(RId,_,SgR,Call,_,_,_,_,_),
    identical_proj(AbsInt, Sg, Proj_s, SgR, Call),
    !.

% fails if the child is already there
add_to_dglist(DgL,Id,_,_,_) :-
    member((Id,_,_,_),DgL), !, fail.
add_to_dglist(DgL,Id,Sg,Proj,[(Id,Sg,Proj,ModBase)|DgL]) :-
    get_module_from_sg(Sg, Mod),
    program_module_base(Mod, ModBase).

:- pred create_registry(+Key,+AbsInt,+CompId,?Spec,+Parents,-RId,-Reg)
    #"Stores a new registry geting the abstract info from
      @var{CompId} and asigning a new unique identifier
      @var{RId}. The information that was stored is unified in
      @var{Reg}".
create_registry(Key,AbsInt,CompId,Spec,Parents,RId,Reg) :-
    complete(Key,AbsInt,SgComp,Proj,[Prime],CompId,_), !,
    get_module_from_sg(SgComp,Mod),
    get_new_reg_id(RId),
    abs_sort(AbsInt, Proj, Proj_s),
    abs_sort(AbsInt, Prime, Prime_s),
    current_pp_flag(success_policy,SP),
    may_be_improved_mark(SP,Mark),
    Reg = regdata(RId,AbsInt,SgComp,Proj_s,Prime_s,Spec,Parents,[],Mark),
    add_imported_typedefs(AbsInt,Mod,[Proj_s,Prime_s]),
    assertz_fact(registry(Key,Mod,Reg)).

:- data reg_id/1.
% TODO: initialize when loading registries

:- export(get_new_reg_id/1).
:- pred get_new_reg_id(-Id) => atm
    #"Generates a new unique identifier for registries.".
get_new_reg_id(Id) :-
    retract_fact(reg_id(Id0)), !,
    Id is Id0 + 1,
    asserta_fact(reg_id(Id)).
get_new_reg_id(0) :-
    asserta_fact(reg_id(0)).

:- export(curr_mod_entry/4).
:- pred curr_mod_entry(SgKey,AbsInt,Sg,Proj) 
    #"Enumerates the CPs of the exported predicate of the current module(s).".
curr_mod_entry(SgKey,AbsInt,Sg, Proj) :-
    curr_file(_, Mod),
    registry(SgKey, Mod, Reg),
    Reg = regdata(_RId,AbsInt,Sg,Proj,_,_,_,_,_).
%       check_curr_entry_id(RId).

update_GAT_entries(AbsInt, File, Mod) :-  % also creates new entries
    get_file_base(File, PBase), % be consistent with Mod
    ( % failure-driven loop
      current_fact(registry(ExpKey, Mod, ExpReg), Ref),
      ExpReg = regdata(RId,AbsInt,Sg,Call,_Succ,Spec,Imdg,Chdg,_Mark),
      check_curr_entry_id(RId), % checking if it was analyzed this iteration
      fixpoint_trace('mod check reg',RId,Mod,ExpKey,Sg,Call,_),
        ( % several imported for the same exported
          graph_reachable(ExpKey,AbsInt,SgE,ProjE,_,Mod,ImpCId,ImpSg,ImpProj),
          abs_sort(AbsInt, ProjE, ProjE_s),
          identical_proj(AbsInt, SgE, ProjE_s, Sg, Call),
          % Add parent to imp registry (creating it if it did not exist)
            get_module_from_sg(ImpSg,ImMod),
            program_module_base(ImMod, IBase),
            abs_sort(AbsInt, ImpProj, ImpProj_s),
            Parent = (RId,Sg,Call,PBase),
            update_create_child_deps(ImpSg,ImpProj_s,ImpCId,IBase,AbsInt,Parent,IRId),
            add_to_children(IRId,ImpSg,ImpProj),
            fail
        ; true 
        ),
        update_registry_success(ExpKey,ExpReg,Mod,PBase,NSucc),
        % update children
        findall((IRId, ImpSg, ImpProj), retract_fact(child_to_add(IRId, ImpSg, ImpProj)), ToAddChdg),
        fixpoint_trace('mod new child',RId,ImMod,ExpKey,Sg,Call,_),
        update_children(Chdg, ToAddChdg, AbsInt, Mod,NChdg),
        NewReg = regdata(RId,AbsInt,Sg,Call,NSucc,Spec,Imdg,NChdg,unmarked),
        erase(Ref),
        assertz_fact(registry(ExpKey,Mod,NewReg)),
        add_changed_module(Mod,PBase,Mod,current,no),
        fail
    ; 
        update_current_typedefs(Mod)
    ).

update_create_child_deps(ImpSg,ImpProj_s,_ImpCId,_IBase,AbsInt,Parent,IRId) :-
    predkey_from_sg(ImpSg, ImpKey),
    current_fact(registry(ImpKey, ImMod, IReg), IRef), % imp reg
    IReg = regdata(IRId,AbsInt,ISg,ICall,ISucc,ISpec,IImdg,IChdg,IMark),
    identical_proj(AbsInt, ImpSg, ImpProj_s, ISg, ICall), !,
    add_to_imdg_list(IImdg,Parent,NIImdg,Added),
    Added = y, % do not update if there are not new parents
    erase(IRef),
    NewIReg = regdata(IRId,AbsInt,ISg,ICall,ISucc,ISpec,NIImdg,IChdg,IMark),
    assertz_fact(registry(ImpKey,ImMod,NewIReg)),
    fixpoint_trace('mod new parent',_,ImMod,_,ImpSg,ImpProj_s,_).
update_create_child_deps(ImpSg,ImpProj,ImpCId,IBase,AbsInt,Parent,IRId) :-
    predkey_from_sg(ImpSg, ImpKey),
    % this registry entry is new
    Parents = [Parent],
    create_registry(ImpKey,AbsInt,ImpCId,_,Parents,IRId,_Reg),
    get_module_from_sg(ImpSg,ImMod),
    fixpoint_trace('mod new registry',IRId,ImMod,_,ImpSg,ImpProj,_),
    add_imported_typedefs(AbsInt,Mod,[ImpProj]),
    add_changed_module(ImMod,IBase,Mod,imported,yes).

update_registry_success(SgKey,ExpReg,Mod,Base,NSucc_s) :-
    unset_src_changed(Base),
    ExpReg = regdata(ERId,AbsInt,Sg,Call,OldSucc,_,Imdg,_,OldMark),
    complete(SgKey,AbsInt,SgComplete,CallComplete,[NSucc],_Id,_),
    abs_sort(AbsInt,CallComplete,CallComplete_s),
    identical_proj(AbsInt,SgComplete,CallComplete_s,Sg,Call),
    abs_sort(AbsInt, NSucc, NSucc_s),
    current_pp_flag(success_policy,SP),
    NReg = regdata(ERId,AbsInt,SgComplete,CallComplete,NSucc,_,_,_,_),
    ( nonvar(OldSucc), identical_proj(AbsInt,SgComplete,NSucc_s,Sg,OldSucc) ->
        ( not_valid_mark(SP,OldMark) ->
            may_be_improved_mark(SP,CallersMark),
            mark_callers_registry(Imdg,SgKey,NReg,AbsInt,Mod,CallersMark,_)
        ; true
        )
    ;
        fixpoint_trace('mod succ changed',ERId,Mod,SgKey,Sg,NSucc_s,_),
        compare_and_get_mark(SP,AbsInt,SgComplete,NSucc_s,Sg,OldSucc,CallersMark),
        mark_callers_registry(Imdg,SgKey,NReg,AbsInt,Mod,CallersMark,_)
    ).
