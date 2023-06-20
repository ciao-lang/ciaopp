:- module(intermod_ops,[
    cleanup_p_abs/0,
    cleanup_p_abs_all/0,
    gen_registry_info/3,
    gen_registry_info/4,
    update_spec_info/2,
    get_spec_info_imported/0,
    cleanup_persistent_registry/1,
    %%%%%%%%%%%%%%%%%%%%%%% LOW-LEVEL FILE ACCESS PRIMITIVES
    add_to_imdg_list/4,
    add_changed_module/5,
    %% exported to obtain the entries of the fixpoint (intermod_entry/intermod_success modules)
    may_be_improved_mark/2,
    not_valid_mark/2,
    registry_is_empty/3,
%%%Resource intermodule-analysis (JNL)
    get_imported_calls/1 % used only in resources/intermod
 ],[assertions,regtypes,basicmodes,isomodes,datafacts,hiord,fsyntax,nativeprops]).

:- use_package(spec(nomem_usage)). % IG: comment to get memory statistics

% Ciao libraries %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module(library(sort)).
:- use_module(library(streams), [absolute_file_name/7]).
:- use_module(library(system_extra), [del_file_nofail/1]).
:- use_module(library(pathnames),  [path_basename/2]).
:- use_module(library(aggregates), [findall/3, setof/3]).
:- use_module(spec(modular_spec), [dyn_abs_spec/5]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(messages)).

% CiaoPP libraries %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module(ciaopp(p_unit/itf_db),
              [current_itf/3, curr_file/2, get_module_from_sg/2]).
:- use_module(ciaopp(infer/infer_db), [domain/1]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).
:- use_module(ciaopp(plai/plai_db), [complete/7, get_parent_key/4]).
:- use_module(ciaopp(plai/domains),
              [identical_proj/5, less_or_equal_proj/5, abs_sort/3, identical_abstract/3,
              needs/2]).
:- use_module(ciaopp(plai/auxinfo_dump)).
:- use_module(ciaopp(p_unit/aux_filenames), [
    get_module_filename/3, just_module_name/2, is_library/1, get_loaded_module_name/3]).
:- use_module(ciaopp(p_unit/program_keys),
              [decode_litkey/5, predkey_from_sg/2, get_predkey/3]).

:- use_module(spec(spec_multiple), [publish_pred_name/2, get_version_name/4]).

:- use_module(ciaopp(plai/incanal/incanal_db),
    [add_changed_registry/4, clean_incanal_mod_data/0]).
:- use_module(ciaopp(analysis_stats), [stat_no_store/2]).

:- use_module(ciaopp(plai/intermod_db)).
:- use_module(ciaopp(plai/intermod_punit)).

:- doc(bug,"auxiliary files version must be handled correctly.").
:- doc(bug,"Success information cannot be multivariant.").

%%%%%%%%%%%%%% Debugging %%%%%%%%%%%%%%%%%

:- use_module(ciaopp(plai/intermod_entry)).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7]).
% IG: Added for keeping track of the changes in the registry

% A 'complete' is an element of the local answer table.
% A 'registry' is an element of the global answer table.

% TODO: create a package that given a regtype and some indexing annotations
%   create these predicates?

program_module_base(Mod, Base) :-
    punit_module(Base, Mod), !.

%% --------------------------------------------------------------------
:- export(changed_module/6).
:- pred changed_module(Module,Base,SourceModule,Mode,WhenModuleChanged,RequireReanalysis) 
   # "List of modules changed when updating the analysis results in the
   registry. Registry information of @var{Module} with basename @var{Base} has
   been changed as a result of analyzing @var{SourceModule}. @var{Mode}
   represents the relationship between @var{Module} and @var{SourceModule}, and
   it can be @code{imported}, @code{caller} or @code{current}.

   @var{WhenModuleChanged} indicates in which run of the analysis of
   @var{SourceModule} the registry information of @var{Module} changed. This
   argument can be instantiated to values @code{current} (modules whose
   information changed as result of the last analysis run) or @code{previous}
   (modules whose information changed as result of a previous analysis run).

   @var{RequireReanalysis} indicates that the module should be reanalyzed. This
   is only useful in the context of @pred{gen_registry_info/3-4}.".

:- data changed_module/6.

%% --------------------------------------------------------------------
:- pred cleanup_p_abs_all # "Cleans up all the data predicates.".
cleanup_p_abs_all :-
    cleanup_registry(_),
    clean_incanal_mod_data,
    retractall_fact(changed_module(_,_,_,_,_,_)),
    cleanup_p_abs.

:- pred cleanup_p_abs + (not_fails, is_det) #"Cleans up internal data predicates.".
cleanup_p_abs :-
    retractall_fact(imported_module(_,_)),
    retractall_fact(caller_module(_,_)),
    % if we are able to do module without cleaning typeslib, the following could be removed
    retractall_fact(registry_in_typeslib(_)),
    move_last_changes_to_previous.

move_last_changes_to_previous :-
    retract_fact(changed_module(Mod,Base,CurrModule,Mode,current,ReqReanalysis)),
    ( current_fact(changed_module(Mod,Base,CurrModule,Mode,previous,ReqReanalysis)) ->
      true
    ; asserta_fact(changed_module(Mod,Base,CurrModule,Mode,previous,ReqReanalysis))
    ),
    fail.
move_last_changes_to_previous.

get_imported_used_modules :-
    ( processed_sg(_,Sg),
        get_module_from_sg(Sg,Module),
        \+ imported_module(Module, _),
        get_loaded_module_name(Module,_AbsFile,AbsBase),
        assertz_fact(imported_module(Module,AbsBase))
    ; true).

:- pred compute_caller_modules + (not_fails, is_det) # "Gets the list of caller modules to the
   current modules. This list is obtained from the registry
   information for the current modules, and is stored in
   @tt{caller_modules/2}.".
compute_caller_modules :-
    current_fact(caller_module(_,_)), !.
compute_caller_modules :-
    ( % (failure-driven loop)
      local_ana_module(_F,Mod),
      current_fact(registry(_,Mod,regdata(_,_,_,_,_,_,ImdgList,_,_))),
        get_module_names(ImdgList,Modules,Bases),
        add_caller_modules(Modules,Bases),
        fail
    ; true
    ).

get_module_names([],[],[]).
get_module_names(['$query'|Imdgs],Ms,Bases) :- !,
    get_module_names(Imdgs,Ms,Bases).
get_module_names([(_Id,_SgCaller,_Caller,Base)|Imdgs],[M|Ms],[Base|Bases]) :-
    just_module_name(Base,M),
    get_module_names(Imdgs,Ms,Bases).

:- pred gen_registry_info(+Verb,-Callers,-Imported) + (not_fails, is_det)
   # "Obtains from analysis internal structures the information on exported
   predicates regarding the current module and related modules. Returns in
   @var{Callers} and @var{Imported} the list of basenames of related modules
   whose registry information has been updated.".
gen_registry_info(Verb,Callers,Imported) :-
    compute_external_reachability,
    get_imported_used_modules,
    ensure_registry_current_files(Verb),
    ensure_registry_imported_files(Verb), % TODO: check that the types are there
    compute_caller_modules,
    ensure_registry_caller_files(Verb),
    ( local_ana_module(File, Mod),
        update_registry_dependencies(_, File, Mod),
        fail
    ; true),
    clean_unreach_registry_info,
    upload_typeslib_to_registry,
    get_imported_changed_modules(Imported),
    get_caller_changed_modules(Callers).

:- pred gen_registry_info(+Verb,-Callers,-Imported,?Info)
   # "As @pred{gen_registry_info/3}, but also returns @var{Info}.".
gen_registry_info(Verb,Callers,Imported,[time(Time,[])]) :-
    stat_no_store(gen_registry_info(Verb,Callers,Imported), Time),
    pplog(p_abs, ['{Generated registry in ',time(Time),' msec.}']).

get_imported_changed_modules(Imported) :-
    findall(Base,imported_changed_module(Base),Imported).

imported_changed_module(Base) :-
    local_ana_module(_,Mod),
    changed_module(M,Base,Mod,imported,current,yes),
    \+ local_ana_module(_,M),
    module_is_processable(Base).

get_caller_changed_modules(Callers) :-
    findall(Base,caller_changed_module(Base),Callers).

caller_changed_module(Base) :-
    local_ana_module(_,Mod),
    changed_module(M,Base,Mod,caller,current,yes),
    \+ local_ana_module(_,M).

%% --------------------------------------------------------------------

:- export(ensure_registry_current_files/1). % TODO: move above
ensure_registry_current_files(Verb) :-
    local_ana_module(CurrBase,CurrModule),
    ensure_registry_file(CurrModule,CurrBase,Verb),
    fail.
ensure_registry_current_files(_Verb).

:- doc(bug,"Currently ensure_registry_imported_files/1 and
    ensure_registry_caller_files/1 read reg files for all imported
    and caller modules. An interesting improvement could be to
    read only those files of modules for which we have new call
    patterns").

ensure_registry_imported_files(Verb) :-
    current_fact(imported_module(IM,Base)),
    local_ana_module(Base,_),
    ensure_registry_file(IM,Base,Verb),
    fail.
ensure_registry_imported_files(_Verb).

ensure_registry_caller_files(Verb) :-
    caller_module(CM,Base),
    local_ana_module(Base,_),
    ensure_registry_file(CM,Base,Verb),
    fail.
ensure_registry_caller_files(_Verb).

%% --------------------------------------------------------------------
:- doc(section, "Marking the entries that need reanalysis").

%% NOTE: This predicate decides when to set invalid marks, depending on the success policy.
:- pred compare_and_get_mark(AbsInt,+SgC,+SuccC,+SgR,+SuccR,Mark)
   : (atm(AbsInt)) => ground(Mark).
compare_and_get_mark(AbsInt,SgComplete,Succ_s,Sg,OldSucc_s,'+') :-
    less_or_equal_proj(AbsInt,SgComplete,Succ_s,Sg,OldSucc_s), !.
compare_and_get_mark(_,_,_,_,_,'-').

:- pred not_valid_mark(+SP,?Mark) 
   # "Succeeds if a registry entry marked with @var{Mark} cannot be used
   when the success policy @var{SP} is applied.".
not_valid_mark(SP,Mark) :-
    may_be_improved_mark(SP,OppositeMark),
    opposite_mark(OppositeMark, Mark).

opposite_mark('-','+').
opposite_mark('+','-').

:- pred may_be_improved_mark(+SP,?Mark)
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

%% --------------------------------------------------------------------
:- doc(section, "Annotating the entries that need reanalysis.").
%% --------------------------------------------------------------------

:- pred mark_callers_registry(+ImdgList,+PKey,PReg,+AbsInt,+CurrModule,+NewMark,-BasenamesMarked)
   + (not_fails, is_det)
   # "Entries of callers entries in @var{ImdgList} are marked with @var{NewMark}
   (if it is greater than their current mark).".

mark_callers_registry([],_,_,_,_CurrModule,_NewMark,[]).
mark_callers_registry(['$query'|Imdgs],PKey,ParentReg,AbsInt,CurrModule,NewMark,BasenamesMarked) :- !,
    mark_callers_registry(Imdgs,PKey,ParentReg, AbsInt,CurrModule,NewMark,BasenamesMarked).
mark_callers_registry([(Id,SgCaller,_Caller,Base)|Imdgs],PKey,ParentReg, AbsInt,CurrModule,NewMark,BasenamesMarked) :-
    current_pp_flag(success_policy,SP),
    just_module_name(Base,M),
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

:- export(mark_module_to_reanalyze/2).
:- pred mark_module_to_reanalyze(+ModName,+AbsInts) + det.
mark_module_to_reanalyze(ModName,AbsInts) :-
    current_pp_flag(success_policy,Policy),
    may_be_improved_mark(Policy,Mark),
    ( % failure-driven loop
      current_fact(registry(SgKey,ModName,OldReg), Ref),
      OldReg = regdata(Id,AbsInt0,Sg,Call,Succ,Spec,ImdgList,Chdg,_OldMark),
      ( member(AbsInt0, AbsInts) -> true ; fail),
      erase(Ref), %% remove fact here because AbsInt is checked after obtaining the fact
        NewReg = regdata(Id,AbsInt0,Sg,Call,Succ,Spec,ImdgList,Chdg,Mark),
        assertz_fact(registry(SgKey,ModName,NewReg)),
        fail
    ; true ).

%% ******************** SPEC ************************************************

:- pred update_spec_info(+File,-Changed) + (not_fails, is_det)
   # "Updates the information about version names of specialized predicates in
    @var{File}.".
update_spec_info(File,Changed) :-
    absolute_file_name(File,'_opt','.pl','.',_,AbsBase,_),
    just_module_name(AbsBase,Module),
    ensure_registry_file(Module,AbsBase,quiet), % TODO: can we really ensure that it is loaded?
    update_current_registry_spec_info(AbsBase,Module,Changed).

:- data changed/1.

update_current_registry_spec_info(Base,CurrModule,Changed) :-
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

:- pred get_spec_info_imported + (not_fails, is_det)
   # "Gets the information about version names of specialized predicates
   belonging to the list of imported modules from the current module, and puts
   them into the specializer's abstract executability table.".

get_spec_info_imported:-
    compute_imported_modules,         %% just in case.
    findall(M,current_fact(imported_module(M,_)),Modules),
    get_spec_info(Modules).

get_spec_info([]).
get_spec_info([Module|Modules]) :-
    current_itf(defines_module,Module,Base),
    just_module_name(Base,Module),
    ensure_registry_file(Module,Base,quiet), % TODO: can we really ensure that it is loaded?
    retractall_fact(dyn_abs_spec(Module,_,_,_,_)),
    get_spec_info_one_module(Module,SpecList),
    sort_spec_info_one_module(SpecList,SortedSpecList),
    assert_spec_info_one_module(Module,SortedSpecList),
    get_spec_info(Modules).

get_spec_info_one_module(Module,NameList) :-
    findall((AbsInt,Sg,Proj,SpecName), spec_info_nonvar(Module,AbsInt,Sg,Proj,SpecName), NameList).

spec_info_nonvar(Module,AbsInt,Sg,Proj,SpecName) :-
    registry(_,Module,regdata(_,AbsInt,Sg,Proj,_,SpecName,_,_,unmarked)),
    nonvar(SpecName).

sort_spec_info_one_module(L1,L2) :-
    qsort(L1,L2,[]).

% TODO: qsort reimplemented for comparing with spec_less
qsort([X|L],R,R2) :-
    partition(L,X,L1,L2),
    qsort(L2,R1,R2),
    qsort(L1,R,[X|R1]).
qsort([],R,R).

partition([],_,[],[]).
partition([E|R],C,[E|Left1],Right) :- 
    spec_less(E,C), !,
    partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]) :-
    partition(R,C,Left,Right1).

spec_less((AbsInt1,_Sg1,_Proj1,_SpecName1),(AbsInt2,_Sg2,_Proj2,_SpecName2)) :-
    AbsInt1 @< AbsInt2, !.
spec_less((AbsInt,Sg1,_Proj1,_SpecName1),(AbsInt,Sg2,_Proj2,_SpecName2)) :-
    functor(Sg1,F1,A1),
    functor(Sg2,F2,A2),
    (F1 @< F2 ; A1 < A2), !.
spec_less((AbsInt,Sg1,Proj1,_SpecName1),(AbsInt,Sg2,Proj2,_SpecName2)) :-
    abs_sort(AbsInt,Proj1,Proj1_s),
    abs_sort(AbsInt,Proj2,Proj2_s),
    less_or_equal_proj(AbsInt,Sg1,Proj1_s,Sg2,Proj2_s),
    \+ identical_proj(AbsInt,Sg1,Proj1_s,Sg2,Proj2_s), !.

assert_spec_info_one_module(_,[]) :- !.
assert_spec_info_one_module(Module,[(AbsInt,Sg,Proj,SpecName)|SpecList]) :-
    assertz_fact(dyn_abs_spec(Module,Sg,AbsInt,Proj,SpecName)),
    assert_spec_info_one_module(Module,SpecList).

%% ====================================================================
% IG: used now only for spec and somewhere in resources
:- pred get_imported_calls(-ICalls) => list + (not_fails, is_det)
   # "Returns a list of tuples (@var{IM},@var{IMBase},@var{Sg}), where @var{Sg}
   is an imported call of module @var{IM} (basename @var{IMBase}). Only the
   imported calls from processable modules are considered.".
get_imported_calls(ICalls) :-
    ( setof((ModName,Sg), (current_itf(imports,Sg,ModName), atom(ModName)), ICalls0) ->
        remove_duplicates(ICalls0,ICalls1),
        get_module_names_bases(ICalls1,ICalls)
    ;
        ICalls = []
    ).

%% Tries to remove the calls that unify, but that are not removed by setof/3.
remove_duplicates(L1,L2) :-
    sort(L1,L11),
    remove_duplicates_(L11,[],L2).

remove_duplicates_([],L,L).
remove_duplicates_([X|Xs],[X|Ys],L) :-
    remove_duplicates_(Xs,[X|Ys],L), !.
remove_duplicates_([X|Xs],Ys,L) :-
    remove_duplicates_(Xs,[X|Ys],L), !.

get_module_names_bases([],[]).
get_module_names_bases([(user,_Sg)|Xs],Ys) :- !,
    get_module_names_bases(Xs,Ys).
get_module_names_bases([(File,Sg)|Xs],[(IM,IMBase,Sg)|Ys]) :-
    get_imported_module_base_name(File, IM, IMBase), !,
    get_module_names_bases(Xs,Ys).
get_module_names_bases([(_File,_Sg)|Xs],Ys) :-
    get_module_names_bases(Xs,Ys).
 
get_imported_module_base_name(File, Mod, Base) :-
    just_module_name(File,Mod),
    current_fact(imported_module(Mod,Base)),
    module_is_processable(Base).

:- pred add_to_imdg_list(+OldList,+Caller,-NewList,-Added)
   : (list(OldList))
   => (list(NewList), atm(Added)) + (not_fails, is_det)
   # "Adds an element @var{Caller} (formed by either a tuple
   (@var{SgCaller},@var{Caller_s},@var{Base}) or an atom @code{'$query'}) to
   @var{OldList}, a list of intermodular dependencies. @var{Added} will be
   instantiated to 'y' if @var{Caller} is actually added to @var{NewList}, and
   'n' if it was already in @var{OldList}.".

add_to_imdg_list([],'$query',['$query'],y).
add_to_imdg_list(['$query'|Is], '$query',['$query'|Is],n) :- !.
add_to_imdg_list([(Id,Sg,Caller,Base)|Is],'$query',[(Id,Sg,Caller,Base)|NIs],Added) :-
    add_to_imdg_list(Is,'$query',NIs,Added),!. % Why added last?
add_to_imdg_list([],(Id,Sg,Caller,Base),[(Id,Sg,Caller,Base)],y) :- !.
add_to_imdg_list(Is,(Id,_,_,Base),Is,n) :-
    Is = [(IdOld,_,_,Base)|_],
    Id = IdOld, !.
add_to_imdg_list([I|Is],(Id,SgCaller,Caller_s,Base),[I|NIs],Added) :-
    add_to_imdg_list(Is,(Id,SgCaller,Caller_s,Base),NIs,Added),!.

:- export(upload_typedefs_all_domains/1).
upload_typedefs_all_domains(Module) :-
    upload_registry_to_typeslib(Module).

% Given a list of imdg tuples, obtains the list of asubs for those imdg tuples.
:- pred get_chdg_asubs(+,?).
get_imdg_asubs([],[]).
get_imdg_asubs(['$query'|Imdgs],Asubs) :- !,
    get_imdg_asubs(Imdgs,Asubs).
get_imdg_asubs([(_Id,_Sg,Proj,_Base)|Imdgs],[Proj|Asubs]) :-
    get_imdg_asubs(Imdgs,Asubs).

:- pred get_chdg_asubs(+,?).
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

%% ********************************************************************
:- pred registry_is_empty(+AbsInt,+Mod,+Base): atm * atm * atm
   # "Succeeds if the registry of module @var{Mod} with base name
   @var{Base} is empty for the abstract domain @var{AbsInt}.".
registry_is_empty(AbsInt,Mod,Base) :-
    read_registry_file(Mod,Base,quiet),
    \+ current_fact(registry(_,Mod,regdata(_,AbsInt,_,_,_,_,_,_,_))).

%% ********************************************************************
%% TOOLBOX
%% ********************************************************************

:- export(less_or_equal_mark/3).
:- pred less_or_equal_mark(+SP,?Mark0,?Mark1) : atm * atm * atm
   # "Given a success policy @var{SP}, succeeds if @var{Mark0} is less or
   equal than @var{Mark1}. Invalid marks are the biggest marks.".
less_or_equal_mark(_SP,Mark,Mark) :- !.  % if one of the marks is a free var, it is instantiated here.
less_or_equal_mark(_SP,unmarked,_Mark) :- !.
less_or_equal_mark(SP,Mark0,Mark1) :-
    may_be_improved_mark(SP,Mark0),
    not_valid_mark(SP,Mark1).

%% --------------------------------------------------------------------
:- pred add_changed_module(+Module,+Base,+SourceModule,+Mode,+ReqReanalysis)
   # "Adds a new entry to @pred{changed_module/6}. @var{Module} registry
   info has been changed as a result of analyzing @var{SourceModule},
   and the relatioship between @var{SourceModule} and @var{Module} is
   @var{Mode} (@code{imported}, @code{caller} or @code{current}).".
add_changed_module(Module,Base,SourceModule,Mode,ReqReanalysis) :-
    changed_module(Module,Base,SourceModule,Mode,current,ReqReanalysis), !.
add_changed_module(Module,Base,SourceModule,Mode,ReqReanalysis) :-
    assertz_fact(changed_module(Module,Base,SourceModule,Mode,current,ReqReanalysis)).

add_caller_module(M,_) :-
    caller_module(M,_), !.
add_caller_module(M,Base) :-
    assertz_fact(caller_module(M,Base)).

add_caller_modules([],[]).
add_caller_modules([M|Ms],[B|Bs]) :-
    add_caller_module(M,B),
    add_caller_modules(Ms,Bs), !.

%% ====================================================================

:- pred compute_external_reachability
   # "For every exported predicate defined in the current module, calculates all
   the imported predicates which are reachable in a given abstract domain.
   Results are generated in graph_reachable/9".
compute_external_reachability :-
    ( % failure-driven loop
      domain(AbsInt),
        compute_external_reachability_1(AbsInt),
        fail
    ; true ).

:- pred graph_reachable(KeyFrom,AbsInt,SgFrom,ProjFrom,IdFrom,ModuleFrom,ImportedId,ImportedSg,ImportedASub)
   # "There is a path from node @var{IdFrom}, key @var{KeyFrom} in module
   @var{ModuleFrom} to the imported call pattern
   @var{ImportedSg}/@var{ImportedASub} in the abstract and-or graph.
   @var{ImportedId} is the Id of the complete containing the imported call
   pattern (used to speedup the process, avoiding the comparison of abstract
   substitutions with @var{ImportedSg}/@var{ImportedASub}.)".

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
    \+ local_ana_module(_, Mod).

add_processed_sg(SgKey, Mod, Sg) :-
    \+ processed_sg(SgKey, Sg),
    current_itf(imports, Sg, Mod),
    assertz_fact(processed_sg(SgKey, Sg)).

assert_initial_arcs([],_,_,_,_).
assert_initial_arcs([(PLitKey,PId)|RefList],AbsInt,Id,Sg,Proj) :-
    get_parent_key(PLitKey,PId,AbsInt,PKey),
    decode_litkey(PLitKey,F,A,_,_),
    functor(CSg,F,A), % This is because of how meta_calls
                      % indexes/ids are treated
    get_module_from_sg(CSg, PModId),
    key_or_id_complete(PKey,AbsInt,PSg,PProj,_,PId,_,_),
    add_pending_graph(PKey,AbsInt,PSg,PProj,PId,PModId,Id,Sg,Proj),
    assert_initial_arcs(RefList,AbsInt,Id,Sg,Proj).

add_pending_graph(NKeyPrev,AbsInt,_,_,IdPrev,ModIdPrev,Id,_,_) :-
    current_fact(pending_graph(NKeyPrev,AbsInt,_,_,IdPrev,ModIdPrev,Id,_,_)),
    !.
add_pending_graph(NKeyPrev,AbsInt,SgPrev,ProjPrev,IdPrev,ModIdPrev,Id,Sg,Proj) :-
    assertz_fact(pending_graph(NKeyPrev,AbsInt,SgPrev,ProjPrev,IdPrev,ModIdPrev,Id,Sg,Proj)).

:- pred graph_closure(AbsInt)
   # "Calculates the reachability graph closure, given the initial
   @pred{pending_graph/9} nodes. This predicate goes backwards from imported
   predicates patterns towards exported predicates patterns, though it does not
   traverse the boundaries between modules (in case there were several current
   modules.)".
graph_closure(AbsInt) :-
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
extend_graph_reachable([(KeyPrev,IdPrev)|RefList],AbsInt,Module,Id,Sg,Proj) :-
    decode_litkey(KeyPrev,F,A,_,_), !, % IG if this fails, the parent is the entry
    get_predkey(F,A,NKeyPrev0),
    key_or_id_complete(NKeyPrev0,AbsInt,SgPrev,ProjPrev,_,IdPrev,_,NKeyPrev),
    ( \+ already_visited(NKeyPrev,AbsInt,IdPrev,Module,Id,Sg,Proj) ->
        add_pending_graph(NKeyPrev,AbsInt,SgPrev,ProjPrev,IdPrev,Module,Id,Sg,Proj)
    ;
        true
    ),
    extend_graph_reachable(RefList, AbsInt,Module,Id,Sg,Proj).
extend_graph_reachable([_|RefList],AbsInt,Module,Id,Sg,Proj) :-
    extend_graph_reachable(RefList, AbsInt,Module,Id,Sg,Proj).

% already_visited(+Key0,+AbsInt,+Id0,+Module,+Sg,+Proj).
already_visited(Key0,AbsInt,Id0,Module,Id,_Sg,_Proj) :-
    current_fact(graph_visited(Key0,AbsInt,Id0,Module,Id,_Sg0,_Proj0)), !.

% Id is unique
key_or_id_complete(SgKey,AbsInt,Sg,Proj,Succ,Id,Ref,SgKey) :-
    current_fact(complete(SgKey,AbsInt,Sg,Proj,Succ,Id,Ref)), !.
key_or_id_complete(_SgKey0,AbsInt,Sg,Proj,Succ,Id,Ref,SgKey) :-
    current_fact(complete(SgKey,AbsInt,Sg,Proj,Succ,Id,Ref)), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% IG improvements and new functionality

:- pred cleanup_persistent_registry(Bases) : list + (not_fails, is_det)
   #"Removes the *.reg files associated to @var{Bases}.".
cleanup_persistent_registry(Bases) :-
    cleanup_p_abs_all,
    ( % failure-driven loop
      member(B, Bases),
        get_module_filename(reg,B,RegName),
        del_file_nofail(RegName),
        fail
    ; true).

:- pred update_registry_dependencies(?AbsInt, +File, +Mod) + (not_fails, is_det)
   #"Updates the registry: abstract (for domain @var{AbsInt}) and dependencies
   information of module @var{Mod}. This update consists on removing CPs that do
   not exist, updating the current entries of the registry and adding new
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
      % TODO: change by member '$query'?
      ( member('$query', Imdg) -> true ; fail ),
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
    graph_reachable(SgKey,AbsInt,PSg,PCall,_,_,_,ChSg,ImpProj), % backtracking here
    abs_sort(AbsInt, PCall, PCall_s),
    identical_proj(AbsInt, Sg, Call, PSg, PCall_s),
    abs_sort(AbsInt, ImpProj, ImpProj_s),
    abs_sort(AbsInt, ChProj, ChProj_s),
    identical_proj(AbsInt, ChSg, ChProj_s, ChSg, ImpProj_s), !,
    predkey_from_sg(ChSg,ChSgKey).

remove_parent_from_reg(SgKey, RId, ParentRId) :-
    retract_fact(registry(SgKey, Mod, regdata(RId,AbsInt,Sg,Proj,Succ,Spec,Imdg,Chdg,Mark))),
    remove_RId_from_dg(Imdg, ParentRId, NImdg),
    %% do not remove entries with no parents (may be reused)
    NReg = regdata(RId,AbsInt,Sg,Proj,Succ,Spec,NImdg,Chdg,Mark),
    assertz_fact(registry(SgKey, Mod, NReg)),
    % add change so it is written in the registry later
    program_module_base(Mod, ModBase),
    local_ana_module(ModBase, CurrModule),
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
   + (not_fails, is_det)
   #"Stores a new registry geting the abstract info from @var{CompId} and
   asigning a new unique identifier @var{RId}. The information that was stored
   is unified in @var{Reg}".
create_registry(Key,AbsInt,CompId,Spec,Parents,RId,Reg) :-
    complete(Key,AbsInt,SgComp,Proj,[Prime],CompId,_), !,
    get_module_from_sg(SgComp,Mod),
    get_new_reg_id(RId),
    abs_sort(AbsInt, Proj, Proj_s),
    abs_sort(AbsInt, Prime, Prime_s),
    current_pp_flag(success_policy,SP),
    may_be_improved_mark(SP,Mark),
    Reg = regdata(RId,AbsInt,SgComp,Proj_s,Prime_s,Spec,Parents,[],Mark),
    mark_to_upload_to_registry_regdata(Reg),
    assertz_fact(registry(Key,Mod,Reg)).

:- data reg_id/1.
% TODO: initialize when loading registries

:- export(get_new_reg_id/1).
:- pred get_new_reg_id(-Id) => num + (not_fails, is_det)
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
    local_ana_module(_, Mod),
    registry(SgKey, Mod, Reg),
    Reg = regdata(_RId,AbsInt,Sg,Proj,_,_,_,_,_).

%% --------------------------------------------------------------------
:- doc(section, "Intermodular Graph Update").
%% --------------------------------------------------------------------

:- pred update_GAT_entries/3 + (not_fails, is_det).
update_GAT_entries(AbsInt, PBase, Mod) :-  % also creates new entries
    ( % failure-driven loop
      current_fact(registry(ExpKey, Mod, ExpReg), Ref),
      ExpReg = regdata(RId,AbsInt,Sg,Call,_Succ,Spec,Imdg,Chdg,_Mark),
      check_curr_entry_id(RId), % checking if it was analyzed this iteration
      fixpoint_trace('[mod] check reg',RId,Mod,ExpKey,Sg,Call,_),
        ( % several imported for the same exported
          graph_reachable(ExpKey,AbsInt,SgE,ProjE,_,Mod,ImpCId,ImpSg,ImpProj),
          abs_sort(AbsInt, ProjE, ProjE_s),
          identical_proj(AbsInt, SgE, ProjE_s, Sg, Call),
          % Add parent to imp registry (creating it if it did not exist)
            get_module_from_sg(ImpSg,ImMod),
            program_module_base(ImMod, IBase),
            abs_sort(AbsInt, ImpProj, ImpProj_s),
            Parent = (RId,Sg,Call,PBase),
            update_create_child_deps(ImpSg,ImpProj_s,ImpCId,IBase,AbsInt,Parent,IRId,Mod),
            add_to_children(IRId,ImpSg,ImpProj),
            fail
        ; true 
        ),
        update_registry_success(ExpKey,ExpReg,Mod,PBase,NSucc),
        % update children
        findall((IRId, ImpSg, ImpProj), retract_fact(child_to_add(IRId, ImpSg, ImpProj)), ToAddChdg),
        fixpoint_trace('[mod] new child',RId,ImMod,ExpKey,Sg,Call,_),
        update_children(Chdg, ToAddChdg, AbsInt, Mod,NChdg),
        NewReg = regdata(RId,AbsInt,Sg,Call,NSucc,Spec,Imdg,NChdg,unmarked),
        erase(Ref),
        assertz_fact(registry(ExpKey,Mod,NewReg)),
        add_changed_module(Mod,PBase,Mod,current,no),
        fail
    ; true
    ).

:- pred update_create_child_deps/8 + (not_fails, is_det).
update_create_child_deps(ImpSg,ImpProj_s,_ImpCId,_IBase,AbsInt,Parent,IRId,_Mod) :-
    predkey_from_sg(ImpSg, ImpKey),
    current_fact(registry(ImpKey, ImMod, IReg), IRef), % backtracking here
    IReg = regdata(IRId,AbsInt,ISg,ICall,ISucc,ISpec,IImdg,IChdg,IMark),
    identical_proj(AbsInt, ImpSg, ImpProj_s, ISg, ICall), !,
    add_to_imdg_list(IImdg,Parent,NIImdg,Added),
    ( Added = y -> % do not update if there are not new parents
        erase(IRef),
        NewIReg = regdata(IRId,AbsInt,ISg,ICall,ISucc,ISpec,NIImdg,IChdg,IMark),
        assertz_fact(registry(ImpKey,ImMod,NewIReg)),
        fixpoint_trace('[mod] new parent',_,ImMod,_,ImpSg,ImpProj_s,_)
    ; true ).
update_create_child_deps(ImpSg,ImpProj,ImpCId,IBase,AbsInt,Parent,IRId,Mod) :-
    predkey_from_sg(ImpSg, ImpKey),
    % this registry entry is new
    Parents = [Parent],
    create_registry(ImpKey,AbsInt,ImpCId,_,Parents,IRId,_Reg),
    get_module_from_sg(ImpSg,ImMod),
    fixpoint_trace('[mod] new reg',IRId,ImMod,_,ImpSg,ImpProj,_),
    add_changed_module(ImMod,IBase,Mod,imported,yes).

:- pred update_registry_success/5 + (not_fails, is_det).
update_registry_success(SgKey,ExpReg,Mod,Base,NSucc0) :-
    unset_src_changed(Base),
    ExpReg = regdata(ERId,AbsInt,Sg,Call,OldSucc,_,Imdg,_,OldMark),
    complete(SgKey,AbsInt,SgComplete,CallComplete,[NSucc],_Id,_),
    abs_sort(AbsInt,CallComplete,CallComplete_s),
    identical_proj(AbsInt,SgComplete,CallComplete_s,Sg,Call),
    abs_sort(AbsInt, NSucc, NSucc_s),
    current_pp_flag(success_policy,SP),
    NReg = regdata(ERId,AbsInt,Sg,Call,NSucc0,_,_,_,_),
    % using registry to avoid loading and unloading types
    ( nonvar(OldSucc), identical_proj(AbsInt,SgComplete,NSucc_s,Sg,OldSucc) ->
        NSucc0 = OldSucc,
        ( not_valid_mark(SP,OldMark) ->
            may_be_improved_mark(SP,CallersMark),
            mark_callers_registry(Imdg,SgKey,NReg,AbsInt,Mod,CallersMark,_)
        ; true
        )
    ;
        NSucc0 = NSucc_s,
        fixpoint_trace('[mod] succ changed',ERId,Mod,SgKey,Sg,NSucc_s,_),
        mark_to_upload_to_registry_lasub(AbsInt,[NSucc_s]),
        compare_and_get_mark(AbsInt,SgComplete,NSucc_s,Sg,OldSucc,CallersMark),
        mark_callers_registry(Imdg,SgKey,NReg,AbsInt,Mod,CallersMark,_)
    ).

%% --------------------------------------------------------------------
:- doc(subsection, "Delete unreachable nodes in intermodular analysis graph").
%% --------------------------------------------------------------------
%%%% TODO: Review to remove also the unreachable type definitions, use reference
%%%% counting?

:- data useful/1.

:- pred clean_unreach_registry_info/0 + (not_fails, is_det).
clean_unreach_registry_info :-
    retractall_fact(useful(_)),
    % find all queries and follow them
    ( % failure-driven loop
      registry(_,_,regdata(Id,_,_,_,_,_,Imdg,Chdg,_)), % backtracking here
        ( member('$query', Imdg) -> true ; fail ), % avoids backtracking in member
        mark_useful_registry(Id,Chdg),
        fail
    ; true
    ),
    ( \+ useful(_) -> warning_message("No intermod entries found",[]) ; true);
    remove_useless_registries,
    retractall_fact(useful(_)).

mark_useful_registry(Id,_Chdg) :-
    useful(Id), !.
mark_useful_registry(Id,Chdg) :-
    assertz_fact(useful(Id)),
    % follow children
    ( % failure-driven loop
      member((ChId,ChSg,_), Chdg),
        predkey_from_sg(ChSg,ChSgKey),
        get_registry(ChSgKey,_,regdata(ChId,_,_,_,_,_,_,ChChdg,_), _),
        mark_useful_registry(ChId,ChChdg),
        fail
    ; true ).

remove_useless_registries :-
    local_ana_module(_,Mod), !,
    ( current_fact(registry(_,Mod,regdata(Id,_,_,_,_,_,_,_,_)),Ref),
        \+ useful(Id),
        erase(Ref),
        punit_module(ModBase,RMod),
        add_changed_module(RMod,ModBase,Mod,'*',no),
        fail
    ; true ).

%% --------------------------------------------------------------------
:- doc(section, "Type loading/restore operations").
%% --------------------------------------------------------------------

:- use_module(library(assoc)).
:- use_module(typeslib(typeslib), []). %% using rename_typedef/3
:- import(typeslib, [rename_typedef/3]).

% To avoid name clashes in typeslib, we are going to store the types in the
% registry with names that cannot clash with those generated automatically by
% the library. This could be generalized for other external solvers.

% We have a global counter to name the types.

:- pred registry_in_typeslib(Module) %% : atm
   %% IG: disabled types to be able to run rtchecks on data
   # "Succeeds if the type definitions for module @var{Module} have been already
   uploaded to the registry.".
:- data registry_in_typeslib/1.

:- data tmp_typedef/2.
:- data mod_tmp_ren/2.
:- data type_counter/1.
type_counter(-1).

next_mod_type_name(Name) :-
    N = ~(~type_counter+1),
    set_fact(type_counter(N)),
    atom_number(NA,N),
    atom_concat('mrt', NA, Name).

:- pred is_modtype(+TypeName).
is_modtype(A) :-
    atom_concat('rt',N,A), atom_number(N,_), !, fail.
is_modtype(A) :-
    atom_concat('pt',N,A), atom_number(N,_), !, fail.
is_modtype(_). % predefined types do not need renaming

mark_to_upload_to_registry_lasub(AbsInt,LASub) :-
    auxinfo_dump:acc_auxiliary_info(AbsInt,LASub).

:- pred mark_to_upload_to_registry_regdata/1 + (not_fails, is_det).
mark_to_upload_to_registry_regdata(regdata(_,AbsInt,_Sg,Call,Succ,_,Imdg,Chdg,_)) :-
    needs(AbsInt, auxinfo), !,
    get_imdg_asubs(Imdg,ImdgASubs),
    get_chdg_asubs(Chdg,ChdgASubs),
    append(ChdgASubs, ImdgASubs, DepsASubs),
    mark_to_upload_to_registry_lasub(AbsInt,[Call,Succ|DepsASubs]).
mark_to_upload_to_registry_regdata(_).

store_tmp_typedef(typedef(T,D)) :-
    assertz_fact(tmp_typedef(T,D)).

:- pred upload_typeslib_to_registry/0 + (not_fails, is_det)
   #"Stores types in the registry (after renaming).".
upload_typeslib_to_registry :-
    has_dump_auxiliary_info, !,
    pplog(p_abs,'{ Uploading typeslib to registry }'),
    %% accumulate types already accumulated by mark_to_upload_to_registry
    auxinfo_dump:dump_auxiliary_info(store_tmp_typedef), % stores in the local type db
    % find typedefs to rename
    ( % failure-driven loop
      tmp_typedef(T,_),
        \+ is_modtype(T),
        next_mod_type_name(RName),
        assertz_fact(mod_tmp_ren(T,RName)),
        fail
    ; true
    ),
    findall(T-RenT,mod_tmp_ren(T,RenT), Rens0),
    Rens0 \= [], !,
    sort(Rens0,Rens1),
    ord_list_to_assoc(Rens1,Rens),
    Dict = (Rens,[]), %% Names = [] (copied from auxinfo_dump.pl), it should only affect eterms
    % rename new type definitions (cache the ones that don't need it)
    ( % failure-driven loop
      mod_tmp_ren(T,RenT),
      retract_fact(tmp_typedef(T,TDef)), % should include !
      rename_typedef(TDef,Rens,RenDef),
        add_mod_typedb(RenT,RenDef),
        fail
    ; true),
    % abstract subtitutions
    ( % failure-driven loop
      current_fact(registry(SgKey,Module,Reg), Ref),
      Reg = regdata(Id,AbsInt,Sg,Call0,Succ0,SpecName,ImdgList0,Chdg0,Mark),
        get_imdg_asubs(ImdgList0,ImdgASubsList0),
        get_chdg_asubs(Chdg0,ChdgASubs0),
        append(ChdgASubs0, ImdgASubsList0, DepsASubs0),
        auxinfo_dump:imp_auxiliary_info(AbsInt,Dict,[Call0,Succ0|DepsASubs0],[Call,Succ|DepsASubs],Changed),
        Changed == yes,
        replace_chdg_subs(Chdg0,DepsASubs,Chdg,ImdgASubsList),
        replace_imdg_subs(ImdgList0,ImdgASubsList,ImdgList),
        erase(Ref),
        NewReg = regdata(Id,AbsInt,Sg,Call,Succ,SpecName,ImdgList,Chdg,Mark),
        assertz_fact(registry(SgKey,Module,NewReg)),
        fail
    ; true
    ),
    retractall_fact(tmp_typedef(_,_)),
    retractall_fact(mod_tmp_ren(_,_)).
upload_typeslib_to_registry.

:- pred upload_registry_to_typeslib(Module) + (not_fails, is_det)
   #"Uploads in typeslib the necessary types for analyzing @var{Module}.".
upload_registry_to_typeslib(_Module) :-
    \+ enum_mod_typedb(_), !. % there are no types
upload_registry_to_typeslib(Module) :-
    \+ registry_in_typeslib(Module), !, 
    pplog(p_abs,['{ Uploading registry to typeslib for ', Module, '}']),
    auxinfo_dump:restore_auxiliary_info(enum_mod_typedb,DumpDict),
    DumpDict = (TypesDict, _Names), % actually, Names = [] always
    \+ empty_assoc(TypesDict),
    % renaming shouldn't be necessary!!!, make sure of this
    ( % (failure-driven loop)
      current_fact(registry(SgKey,Module,OldReg),Ref),
        OldReg = regdata(Id,AbsInt,Sg,Call0,Succ0,SpecName,ImdgList0,Chdg0,Mark),
        needs(AbsInt, auxinfo),
        get_imdg_asubs(ImdgList0,ImdgASubsList0),
        get_chdg_asubs(Chdg0,ChdgASubs0),
        append(ChdgASubs0, ImdgASubsList0, DepsASubs0),
        auxinfo_dump:imp_auxiliary_info(AbsInt,DumpDict,[Call0,Succ0|DepsASubs0],[Call,Succ|DepsASubs],Changed),
        Changed == yes,
        replace_chdg_subs(Chdg0,DepsASubs,Chdg,ImdgASubsList),
        replace_imdg_subs(ImdgList0,ImdgASubsList,ImdgList),
        erase(Ref),
        NewReg = regdata(Id,AbsInt,Sg,Call,Succ,SpecName,ImdgList,Chdg,Mark),
        assertz_fact(registry(SgKey,Module,NewReg)),
        fail
    ).
upload_registry_to_typeslib(Module) :-
    ( registry_in_typeslib(Module) -> true
    ; assertz_fact(registry_in_typeslib(Module))
    ).
