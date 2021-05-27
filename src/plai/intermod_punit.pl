:- module(_,[
    compute_punit_modules/3,
    get_punit_modules/1,
    get_punit_included_files/1,
    get_all_module_cycles/2,
%    get_all_modules_depth/2,
    module_is_processable/1,
    %%%%%%%%%%%%%%%%%%%%%%% 
    ensure_registry_file/3, % (read and patch registry)
    read_registry_file/3, % TODO:{JF2} NOTE THAT THIS ONE DOES NOT PATCH!!!
    write_registry_file/3,
    open_mode/3,
    change_open_mode/2,
    save_registry_info/3,
    save_registry_info/2
    %%%%%%%%%%%%%%%%%%%%%%% 
    ],[assertions, isomodes, nativeprops, datafacts]).

:- doc(title, "Program structure for intermodular analysis").

:- doc(module, "This module contains the functionality to compute the
intermodular graph of a program, i.e., the dependencies of its modules.

The predicate @pred{compute_intermodule_graph/1} calls the Ciao compiler to
obtain which modules are in the intermodular punit, which is controlled by the
flag @tt{punit_boundary}. This is done by:
@begin{itemize}

@item @pred{process_changed_module/1}: Is executed if the module changed (w.r.t. the
@tt{.itf} file.

@item @pred{check_stop_one_module/1}: Decides whether the compiler needs to keep
processing the modules imported by the current module.

@item @pred{redo_unchanged_module/1}: Is executed if there were no changes since
the last time the module was @bf{compiled}, if always fails because it is asking
whether to process the file @bf{again}.

@end{itemize}
").

:- use_module(ciaopp(preprocess_flags)).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(ciaopp(plai/intermod_db)).
:- use_module(ciaopp(plai/tarjan), [step2/2]).
:- use_module(ciaopp(p_unit/itf_db), [current_itf/3]).
:- use_module(ciaopp(p_unit/p_asr), [there_was_error/1]).
:- use_module(ciaopp(p_unit/aux_filenames), [
    get_module_filename/3, just_module_name/2, is_library/1, get_loaded_module_name/3]).
:- use_module(ciaopp(plai/intermod_ops),
              [add_changed_module/5, less_or_equal_mark/3, may_be_improved_mark/2,
               upload_typedefs_all_domains/1, changed_module/6]).

:- use_module(library(assertions/c_itf_props), [filename/1]).
:- use_module(library(aggregates), [setof/3, findall/3, '^'/2]).
:- use_module(library(ctrlcclean), [ctrlc_clean/1]).
:- use_module(library(errhandle), [error_protect/2]).
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(streams), [absolute_file_name/7]).
:- use_module(library(write),  [writeq/2]).
:- use_module(library(read),   [read/2]).
:- use_module(library(pathnames),  [path_splitext/3]).
:- use_module(library(system), [file_exists/1]).
:- use_module(library(fastrw),
              [fast_read/1, fast_write/1, fast_read/2, fast_write/2]).
:- use_module(library(hiordlib), [maplist/2]).
:- use_module(library(system), [working_directory/2, file_exists/1, modif_time0/2, modif_time/2]).
:- use_module(library(bundle/bundle_paths), [reverse_bundle_path/3]).
:- use_module(library(compiler/c_itf), 
    [false/1, process_files_from/7, uses/2, includes/2]).

%% ********************************************************************
:- doc(section, "Public database").
%% ********************************************************************

:- data module_is_processable_cache/3.

:- export(compute_imported_modules/0).
:- pred compute_imported_modules + (not_fails, is_det)
   # "Gets the list of imported modules from the current module. This list is
   obtained from the itf information of the current module, and is stored in
   @tt{imported_module/1}.".
compute_imported_modules :-
    current_fact(imported_module(_,_)), !.
compute_imported_modules :-
    current_itf(imports,_Sg,Module), atom(Module),
    \+ imported_module(Module, _),
    get_loaded_module_name(Module,_AbsFile,AbsBase),
    assertz_fact(imported_module(Module,AbsBase)),
    fail.
compute_imported_modules.

:- data modules_analyzed/1.
:- export(get_imported_module_base/2).
get_imported_module_base(M, Base) :-
    current_fact(imported_module(M,Base)), !.
get_imported_module_base(M, Base) :-
    get_loaded_module_name(M,_AbsFile,Base),
    assertz_fact(imported_module(M,Base)).

:- export(get_modules_analyzed/1).
:- pred get_modules_analyzed(ModList) => list(ModList)
   # "Returns the list of modules analyzed the last time a modular
   analysis was executed.".
get_modules_analyzed(ModList):-
    current_fact(modules_analyzed(ModList)).

:- pred set_modules_analyzed(ModList) : list(ModList)
   # "Sets the list of modules which have been analyzed.".
:- export(set_modules_analyzed/1).
set_modules_analyzed(ModList0):-
    get_module_names_only(ModList0,ModList),!,
    set_fact(modules_analyzed(ModList)).
set_modules_analyzed(ModList):-
    set_fact(modules_analyzed(ModList)).

get_module_names_only([],[]).
get_module_names_only([(M,_,_)|ModList0],[M|ModList]):-
    get_module_names_only(ModList0,ModList).

:- pred patched_registry(Pred).
:- data patched_registry/1.

%% ********************************************************************
:- pred get_punit_modules(-ModList)
   => (list(ModList)) + (not_fails, is_det)
   # "Obtains @var{ModList}, the list of modules in the program unit that is
   currently loaded. This list is formed by the modules which appear in the
   top-down modular graph traversal with registries set to read_write mode (and
   including library modules if punit_boundary flag is set to 'on'.
   @pred{compute_punit_modules/2} needs to be called before.".
get_punit_modules(ModList) :-
    findall(M, intermodular_graph_node(M), ModList).

:- pred get_punit_included_files(-IncludeList) => list(filename,IncludeList)
   + (not_fails, is_det)
   # "Returns the list of included files in the program unit. This list includes
   not only files explicitly included with @code{:- include} declarations, but
   also packages used. @pred{compute_punit_modules/2} needs to be called
   before.".
get_punit_included_files(IncludeList) :-
    findall(I, include_list(I), IncludeList).

%% :- pred get_punit_modules_depth(-ModList)
%%     => (list(ModList)) + (not_fails, is_det)
%%    # "Given the top-level module of a program, @var{TopLevelFile}, obtains in
%%    @var{ModList} the list of pairs (module,depth) with all modules in the
%%    modular graph with their maximal depth (without cycles). All the modules in a
%%    cycle have the same depth.".
%% :- doc(bug,"not tested yet.").
%% get_punit_modules_depth(ModList) :-
%%     ( setof( (M,D) , ( 
%%                          current_fact(intermodular_graph_node(M)),
%%                          current_fact(intermodule_graph_depth(M,D))
%%                      ) , ModList)
%%     ; ModList = []).

:- pred get_all_module_cycles(+TopLevelFile,-CycleList) 
   => (list(CycleList)) + (not_fails, is_det)
   # "Obtains @var{CycleList}, the list of cycles in the program unit whose
   top-level module is @var{TopLevelFile}. A cycle is a ciclic dependency in the
   module dependency graph. Every element of @var{CycleList} is a list of the
   modules which belong to each cycle. Modules not belonging to any cycle are
   represented as one-element lists. @var{CycleList} is sorted as a post-order
   traversal of the inter-cycle dependency graph.

   The modules included in @var{CycleList} are those which appear in the
   top-down modular graph traversal with registries set to read_write mode (and
   including library modules if punit_boundary flag is set to 'on'.)".
get_all_module_cycles(TopLevelFile,SortedCycleList) :-
    absolute_file_name(TopLevelFile,'_opt','.pl','.',_AbsFile,AbsBase,_),
    findall(vertex(M1,Ms,0,0,undef), initial_vertex(M1,Ms), Vertex),
    intermod_sccs(Vertex,CycleList),
    get_postorder_traversal(AbsBase,CycleList,SortedCycleList).

get_postorder_traversal(TopLevel,Cs,SortedCycles) :-
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
interscc_postorder_traversal(STopLevel,PostOrder) :-
    interscc_children_traversal(STopLevel,A-A,PostOrder-Tail),
    Tail = [STopLevel].
    
interscc_children_traversal(Node, PO0-T0, PO1-T1) :-
    findall(Child, interscc_edge(Node,Child), Children),
    interscc_children_traversal_2(Children,PO0-T0, PO1-T1).

interscc_children_traversal_2([],PO-T,PO-T).
interscc_children_traversal_2([Node|Nodes], PO0-T0, POn-Tn) :-
    ( member_vartail(Node,PO0) ->
        PO1-T2 = PO0-T0
    ;
        interscc_children_traversal(Node, PO0-T0, PO1-T1),
        T1 = [Node|T2]
    ),
    interscc_children_traversal_2(Nodes, PO1-T2, POn-Tn).

member_vartail(_Node,V) :-
    var(V), !, fail.
member_vartail(Node,[Node|_]) :- !.
member_vartail(Node,[_|Rest]) :-
    member_vartail(Node,Rest).

get_cycles([],[]).
get_cycles([CssId|CssIds],[Cycle|SortedCycles]) :-
    findall(M, module_scc(M,CssId), Cycle),
    get_cycles(CssIds,SortedCycles).

%% ********************************************************************
% TODO: review this doc
:- pred compute_punit_modules(+TopLevel,-ModList,-Error)
   + (not_fails, is_det)
   # "Obtains the list of modules to analyze. This list is formed by the modules
   which have their .reg file outdated, or if the module is not completely
   analyzed (some of the entries in the .reg file are marked or invalid). For
   those modules which have no .reg file, the @em{parents} of the module are
   included in the list (as there are no call patterns for those modules without
   .reg file).

   The structure of the elements in the list is a term
   (@var{Mod},@var{Depth},@var{Force}), where @var{Mod} stands for the module
   name, @var{Depth} is the maximum depth without cycles in the intermodular
   graph, and @var{Force} marks those modules which must be completely
   reanalyzed (only useful for the parents of the modules with no reg file).
   ".
compute_punit_modules(TopLevelFile,ModList,Error) :-
    retractall_fact(module_to_analyze(_,_)),
    retractall_fact(module_to_analyze_parents(_)),
    absolute_file_name(TopLevelFile,'_opt','.pl','.',AbsFile,AbsBase,_),
    %
    retractall_fact(delay_patch_registry(_)),
    retractall_fact(patched_registry(_)),
    compute_intermodule_graph(AbsFile,Error),
    ( Error = no ->
        delayed_patch_registry,
        compute_intermodule_graph_depth(AbsBase),
        include_parents(AbsBase),
        ( setof((M,D,F), module_to_analyze_depth(M,D,F), ModList)
        ; ModList = []),
        findall(M, intermodular_graph_node(M), AllModList),
        set_punit_modules(AllModList)
    ;
        retractall_fact(delay_patch_registry(_)),
        retractall_fact(patched_registry(_))
    ),
    retractall_fact(module_to_analyze(_,_)),
    retractall_fact(module_to_analyze_parents(_)).

module_to_analyze_depth(M,D,F) :-
    module_to_analyze(M,F),
    intermodule_graph_depth(M,D).

%% --------------------------------------------------------------------
:- doc(section, "Intermodular Graph Traversal").
%% --------------------------------------------------------------------

:- pred intermodular_graph_edge(Caller,Called) # "Module graph. It succeeds iff module
   with basename @var{Caller} imports module with basename @var{Called}.".

% internal data only used to compute the intermodular graph
:- data intermodular_graph_edge/2.
:- data intermodular_graph_node/1.
:- data include_list/1. 
:- data initial_vertex/2.  %% For tarjan algorithm.

:- data src_not_changed/1.

:- data module_to_analyze/2.
:- data module_to_analyze_parents/1.

:- pred compute_intermodule_graph(+AbsFile,-Err) + (not_fails, is_det)
   # "Obtains in @pred{intermodule_graph/2} the dependencies among modules of
   the program unit given by the module in file @var{AbsFile} (depending on
   punit_boundary flag, library modules are included or not in the program
   unit). This predicate fills datas @pred{src_changed/1} and
   @pred{src_not_changed/1}, detecting if the analysis result is outdated for
   each module in the intermodular graph.".
compute_intermodule_graph(AbsFile,E) :-
    path_splitext(AbsFile, AbsBase, _),
    retractall_fact(intermodular_graph_edge(_,_)),
    retractall_fact(intermodular_graph_node(_)),
    retractall_fact(include_list(_)),
    retractall_fact(initial_vertex(_,_)),
    retractall_fact(src_changed(_)),
    retractall_fact(src_not_changed(_)),
    error_protect(ctrlc_clean(
        process_files_from(AbsFile, zzz, any,
                           process_changed_module,
                           check_stop_one_module(AbsBase),
                           c_itf:false,
                           redo_unchanged_module)
    ),fail), % TODO: fail or abort?
    ( there_was_error(_), E = no -> true ; E = error).

redo_unchanged_module(Base) :-
    % we are here because the itf was up to date and
    % c_itf is asking if we want to re-treat the module,
    % add Base to the not-changed set and fill the intermod graph
    ( current_fact(src_not_changed(Base)) -> true % IG: can this happen?
    ;
        get_module_filename(reg,Base,RegFile),
        ( modif_time(RegFile,RegTime) -> % file exists
            ( outdated_reg(Base,RegFile,RegTime) ->
                assertz_fact(src_changed(Base))
            ; assertz_fact(src_not_changed(Base))
            )
        ; % if the file does not exist we do not care if it changed (there is
          % not an analysis result)
          assertz_fact(src_not_changed(Base))
        ),
        fill_intermod_graph(Base)
    ),
    fail.
% Detect if the .reg file associated to Base is outdated w.r.t, its
% source .pl file (or any included .pl).

% (similar to c_itf:changed_dependencies/2 but for .reg and
% considering only included files)
outdated_reg(Base,RegFile,RegTime) :-
    ( changed_dep(Base,RegTime)
    ; includes(Base,I),
      changed_dep(I,RegTime)
    ),
    !,
    pplog(p_abs, ['{', ~~(RegFile), ' is not up-to-date}']).
outdated_reg(_Base,RegFile,_RegTime) :-
    pplog(p_abs, ['{', ~~(RegFile), ' is up-to-date}']).

changed_dep(Base,RegTime) :-
    get_module_filename(pl,Base,PlName),
    modif_time0(PlName,PlTime), % (0 if does not exist)
    PlTime > RegTime.

% TASK: check that this is really traversing all dependencies
% This predicate is only called if the module is changed
process_changed_module(Base) :-
    % add to src_changed/1 only if
    ( src_not_changed(Base) -> % WHY?
        throw(error_not_changed(Base)) ; true ),
    add_src_changed(Base), % added to know that a module needs processing
    get_module_filename(reg,Base,RegName),
    pplog(p_abs, ['{', ~~(RegName), ' is not up-to-date}']),
    fill_intermod_graph(Base).

fill_intermod_graph(Base) :-
    asserta_fact(intermodular_graph_node(Base)),
    findall(IFile,uses(Base,IFile),IFileList0),
    file_path(Base,BasePath),
    working_directory(Old,BasePath),
    processable_basenames(IFileList0,IBaseList),
    findall(I, includes(Base,I), IncludeList0),
    basenames(IncludeList0,IncludeList),
    assert_include_list(IncludeList),
    working_directory(BasePath,Old),
    assertz_fact(initial_vertex(Base,IBaseList)),
    assert_intermodule_graph(IBaseList,Base).

file_path(Base,Path) :-
    absolute_file_name(Base,'_opt','.pl','.',_,_,Path).

%% Asserts the list of imported  modules received as argument. 
assert_intermodule_graph([],_Base).
assert_intermodule_graph([IBase|IBaseList],Base) :-
    asserta_fact(intermodular_graph_edge(Base,IBase)),
    assert_intermodule_graph(IBaseList,Base).

assert_include_list([]).
assert_include_list([I|Is]) :-
    ( current_fact(include_list(I)) ->
        true
    ;
        asserta_fact(include_list(I))
    ),
    assert_include_list(Is).

%% Given a list of file names, removes from them the modules
%% which are not processable, and returns the list of the remaining basenames.
processable_basenames([],[]).
processable_basenames([File|Files],[Base|Bases]) :-
%%      Current dir is the one of the base being processed.
    absolute_file_name(File,'_opt','.pl','.',_,Base,_),
    module_is_processable(Base), !,
    processable_basenames(Files,Bases).
processable_basenames([_File|Files],Bases) :-
    processable_basenames(Files,Bases).

basenames([],[]).
basenames([File|Files],[Base|Bases]) :-
%%      Current dir is the one of the base being processed.
    absolute_file_name(File,'_opt','.pl','.',_,Base,_),
    basenames(Files,Bases).

:- pred check_stop_one_module(_,Base)
   #"Succeeds if the compiler does not need to continue processing
    the modules imported by this one.".
check_stop_one_module(_TopBase,Base) :-
    \+ module_is_processable(Base). % If the module is processable, fail

%% ********************************************************************
:- doc(section, "Intermodular graph depth computation").
%% ********************************************************************

:- pred intermodule_graph_depth(Module,Depth)
   # "Module @var{Module} has depth @var{Depth} in the intermodular graph
   contained in @pred{intermodule_graph/2}. All modules included in a strongly
   connected component are labelled with the same depth.".

:- data intermodule_graph_depth/2. 

:- pred compute_intermodule_graph_depth(TopLevel) 
   # "Computes the intermodule graph (contained in @pred{intermodule_graph/2})
   with depths and stores it in @pred{intermodule_graph_depth/2}. The depth of
   every node in the graph is computed considering that all nodes in a strongly
   connected component are labelled with the same depth. The depth of a given
   node is the largest depth from the top-level module.

   This predicate must be called after calling compute_intermodule_graph/2 as it
   needs initial_vertex/2 already populated.".
compute_intermodule_graph_depth(TopLevel) :-
    retractall_fact(intermodule_graph_depth(_,_)),
    findall(vertex(M1,Ms,0,0,undef), initial_vertex(M1,Ms), Vertex),
    intermod_sccs(Vertex,Cs),
    compute_noncyclic_depth(TopLevel,Cs).

:- pred intermod_sccs(in(Vertices),out(Cs)) 
   # "@var{Cs} is the list of strongly connected components in the digraph
   represented by the list @var{Vertex} of vertex/5 structures.".

intermod_sccs([],[]) :- !.
intermod_sccs(Vertex,Cs) :-
    (Vertex == [] ->
        Cs = []
    ;
        Vertex = [V|Vs],
        S0 = state([V|Vs],V,[],0),
        step2(S0,Cs)
    ).

:- data module_scc/2.      % Module M belongs to scc S.
:- data interscc_edge/2.   % Scc S1 is connected to Scc S2.
:- data scc_depth/2.       % Scc S has depth D.

:- pred compute_noncyclic_depth(in(TopLevel),in(Cs)) 
   # "computes the depth of every module, labelling the modules in a strongly
   connected component (in @var{Cs}) with the same depth. The result is stored
   in intermodule_graph_depth/2.".
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
    current_fact(intermodular_graph_edge(M,N)),
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

recurse_scc_children(Scc,Depth) :-
    Depth1 is Depth + 1,
    current_fact(interscc_edge(Scc,SccChild)),
    compute_scc_depth(SccChild,Depth1),
    fail.
recurse_scc_children(_Scc,_Depth).

gen_intermodule_graph_depth:-
    current_fact(scc_depth(Scc,Depth)),
    ( current_fact(module_scc(Mod,Scc)) -> true ; fail ),
    assertz_fact(intermodule_graph_depth(Mod,Depth)),
    fail.
gen_intermodule_graph_depth.

%% 'user' module cannot be treated as a normal module.
user_module(user).  

:- pred module_is_processable(+Base) 
   # "Succeeds if module in @var{Base} can be processed by intermodular
   preprocessing tools. This predicate may have to load the registry file of
   that module, in order to check that the module has read-write mode.".
module_is_processable(B) :-
    current_pp_flag(punit_boundary,ProcessLibs),
    module_is_processable_(B,ProcessLibs).

module_is_processable_(Base,_ProcessLibs) :-
    user_module(Base), !, fail.
module_is_processable_(Base,ProcessLibs) :-
    current_fact(module_is_processable_cache(Base,Processable,ProcessLibs)), !,
    Processable == yes.
module_is_processable_(Base,ProcessLibs) :-
    is_library(Base), 
    \+ (ProcessLibs == on), !,
    assert_if_not_asserted_yet(module_is_processable_cache(Base,no,off)),
    fail.
module_is_processable_(Base,ProcessLibs) :-
    ProcessLibs = bundle,
    main_module(TopLevelBase, _),
    reverse_bundle_path(TopLevelBase, Bundle, _),
    reverse_bundle_path(Base, Bundle0, _),
    \+ Bundle0 = Bundle, !,
    assert_if_not_asserted_yet(module_is_processable_cache(Base,no,bundle)),
    fail.
module_is_processable_(Base,ProcessLibs) :-
    just_module_name(Base,Module),
    read_registry_file(Module,Base,quiet),
    % does not need to check src_changed/1, reading so that `open_mode/3` is known.
    %
    % IG: reading the registry could be postponed to `process_changed_module/1`
    % or `redo_unchanged_module/1` if open_mode is not useful.
    open_mode(Base,_,read_write), !,
    ( delay_patch_registry(Base) -> true ; assertz_fact(delay_patch_registry(Base))),
    assert_if_not_asserted_yet(module_is_processable_cache(Base,yes,ProcessLibs)).
module_is_processable_(Base,ProcessLibs) :-
    assert_if_not_asserted_yet(module_is_processable_cache(Base,no,ProcessLibs)),
    fail.

assert_if_not_asserted_yet(module_is_processable_cache(A,B,C)) :-
    \+ current_fact(module_is_processable_cache(A,B,C)), !,
    assertz_fact(module_is_processable_cache(A,B,C)).
assert_if_not_asserted_yet(_).

:- pred module_is_processable_cache(Base,Processable,ProcessLibsFlag)
   # "Cache predicate for speeding up when checking whether a module is
   processable or not. It unifies @var{Processable} with 'yes' if module in
   @var{Base}.pl is processable, or 'no' if it is not. @var{ProcessLibs}
   contains the value of 'punit_boundary' flag for which the module is or is not
   processable.".

%% Converts module_to_analyze_parents(X) into
%% module_to_analyze(Y,force), where Y is parent of X.
include_parents(TopBase) :-
    module_to_analyze_parents(Base),
    ( Base == TopBase -> %% TopLevel module must be added even if it has parents.
        add_module_to_analyze(Base,force)
    ;   true
    ),
    ( intermodular_graph_edge(_,Base) ->
        current_fact(intermodular_graph_edge(Parent,Base)),
        ( module_to_analyze_parents(Parent) ->  true
        ;
            ( module_is_processable(Parent) ->
                add_module_to_analyze(Parent,force)
            ;   true
            )
        )
    ; %% if there are no parents, Base must be added.
        ( module_is_processable(Base) ->
            add_module_to_analyze(Base,force)
        ;   true
        )
    ),
    fail.
include_parents(_TopBase) :-
    retractall_fact(module_to_analyze_parents(_)).

add_module_to_analyze(Base,Force) :-
    ( current_fact(module_to_analyze(Base,Force0),Ref) ->
      ( Force = force, Force0 = no_force ->
          erase(Ref),
          asserta_fact(module_to_analyze(Base,force))
      ; true
      )
    ; asserta_fact(module_to_analyze(Base,Force))
    ).

:- data delay_patch_registry/1. % ugly hack to delay patch until src_changed/1 is known

delayed_patch_registry :-
    ( % (failure-driven loop)
      retract_fact(delay_patch_registry(Base)),
        delayed_patch_registry_(Base),
        fail
    ; true
    ).

:- pred delayed_patch_registry_/1 + (not_fails, is_det).
delayed_patch_registry_(Base) :-
    just_module_name(Base,Module),
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        patch_registry_(Module,Base,NeedsTreat),
        ( NeedsTreat = no,
          all_entries_unmarked(Base) ->
            true
        ; add_module_to_analyze(Base,no_force)
        )
    ; %% If there is no registry file, parents of this module are added
      %% for analysis (as call patterns are needed for the imported module).
      asserta_fact(module_to_analyze_parents(Base))
    ).

%% Succeeds if all entries are unmarked for AbsInt.
%% AbsInt can be either a domain name or a list of domains.
all_entries_unmarked(Base) :-
    just_module_name(Base,Module),
    \+ current_fact(registry(_,Module,regdata(_,_,_,_,_,_,_,_,'-'))),
    \+ current_fact(registry(_,Module,regdata(_,_,_,_,_,_,_,_,'+'))).

%% --------------------------------------------------------------------

% TODO: document
ensure_registry_file(Module,Base,Verb) :-
    read_registry_file_(Module,Base,Verb),
    patch_registry_(Module,Base,_).

:- pred read_registry_file(+Module,+Base,+Verb) : atm * atm * atm
   + (not_fails, is_det)
   # " Reads the registry file of @var{Module} and loads it into
   @tt{registry/2}, erasing any previous registry information for that module.
   @var{Base} must be the absolute file name, but excluding file extension.".
read_registry_file(Module,Base,Verb) :-
    % TODO:{JF2} split in a simple pred that read the registry and other that computes NeedsTreat, patches Mark at registry (if needed), and does upload_typedefs_all_domains
    read_registry_file_(Module,Base,Verb).

read_registry_file_(Module,_Base,_Verb) :-
    registry_already_read(Module), !.
read_registry_file_(Module,Base,Verb) :-
    % Just make sure that the registry is loaded
    cleanup_registry(Module),
    get_module_filename(reg,Base,RegName),
    get_module_filename(pl,Base,PlName),
    ( file_exists(RegName) ->
      open(RegName, read, Stream),
      ( read_registry_header(Verb,Module,Stream) ->
          pplog(p_abs, ['{Reading ',RegName, '}']),
          current_input(CI),
          set_input(Stream),
          read_types_data_loop(Module,NextTuple),   % NextTuple is the tuple after the last type definition.
          read_reg_data_loop(Module,NextTuple),
          set_input(CI)
      ; pplog(p_abs, ['{Wrong version of file: ',RegName,'. It will be overwritten.}']),
        create_registry_header(Module,PlName),
        add_changed_module(Module,Base,Module,registry_created,no)
      ),
      close(Stream)
    ; pplog(p_abs, ['{Non-existing file: ',RegName,'}']),
      create_registry_header(Module,PlName),
      add_changed_module(Module,Base,Module,registry_created,no)
    ),
    !.

% (needs src_changed/1)
:- pred patch_registry_/3 + (not_fails, is_det).
patch_registry_(_Module,Base,NeedsTreat) :-
    patched_registry(Base), !,
    NeedsTreat = no.
patch_registry_(Module,Base,NeedsTreat) :-
    % NOTE: (previous code do not create a RegName file yet)
    get_module_filename(reg,Base,RegName),
    ( file_exists(RegName) ->
        ( src_changed(Base) ->
            NeedsTreat = yes,
            current_pp_flag(success_policy,SP),
            may_be_improved_mark(SP,ForceMark),
            patch_read_reg_data_loop(Module,ForceMark)
        ; NeedsTreat = no
        ),
        upload_typedefs_all_domains(Module)
    ; NeedsTreat = yes
    ),
    assertz_fact(patched_registry(Base)).

%% --------------------------------------------------------------------
% Reads types from std. input. The last tuple read (immediately after the last type read) is 
% returned in NextTuple.
% TODO: IG: this needs to be fixed
read_types_data_loop(_Module,NextTuple) :-
    repeat,
    ( fast_read(NextTuple) ->
        ( NextTuple = mod_typedb(T,TD) ->
            add_mod_typedb(T,TD),
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

registry_already_read(Module) :-
    current_fact(registry_header(Module,_)), !.

%% --------------------------------------------------------------------
:- pred create_registry_header(+Module,+PlFileName) : atm * atm
   + (not_fails, is_det)
   # "Creates in memory a new registry header for @var{Module}. This predicate
   must be aware of the contents of the header and the order of the header terms
   (stored as terms in @pred{registry_header_format/2})".
create_registry_header(Module,PlFile) :-
    retractall_fact(registry_header(Module,_)),
    assertz_fact(registry_header(Module,entries_already_analyzed([]))),
    path_splitext(PlFile, FileBase, _),
    assertz_fact(registry_header(Module,module_base(FileBase))),
    ( (is_library(PlFile), \+current_pp_flag(punit_boundary,on)) ->
      assertz_fact(registry_header(Module,open_mode(read_only)))
    ; assertz_fact(registry_header(Module,open_mode(read_write)))
    ),
    pplog(p_abs, ['{Registry header created ',Module, ' }']).

:- pred read_registry_header(Verb,Module,Stream) : atm * atm * stream
    + (not_fails, is_det)
   # "Reads the header of @var{Module}'s registry file from @var{Stream}, and
   stores it in the data predicate @tt{registry_header/2}. If the registry
   header is wrong, or it corresponds to a non-valid version, this predicate
   fails.".
read_registry_header(_Verb,Module,Stream) :-
    read(Stream,v(V)),
    registry_header_format(V,HeaderTerms),
    read_registry_header_terms(Stream,Module,HeaderTerms), !.
read_registry_header(_Verb,Module,_Stream) :-
    pplog(p_abs, ['{Wrong version or corrupted file header: ',Module,'}']),
    fail.

% TODO: unify with itf read
read_registry_header_terms(_Stream,_Module,[]) :- !.
read_registry_header_terms(Stream,Module,[H|Hs]) :-
    fast_read(Stream,H),
    assertz_fact(registry_header(Module,H)),
    read_registry_header_terms(Stream,Module,Hs).

%% --------------------------------------------------------------------
:- pred write_registry_file(Base,Module,Verb)
   : atm * atm * atm  + (not_fails, is_det)
   # "Writes to disk the registry information stored in memory for module
   @var{Module} which has as base file name @var{Base}.".
write_registry_file(Base,Module,_Verb) :-
    get_module_filename(reg,Base,RegName),
    open(RegName,write,Stream), % overwrites the previous file.
    write_registry_header(Module,Stream),
    pplog(p_abs, ['{Writing ',RegName]),
    current_output(CO),
    set_output(Stream),
    write_registry_file_types(Module),
    write_registry_file_loop(Module),
    set_output(CO),
    close(Stream),
    pplog(p_abs, ['}']).

write_registry_file_types(_Module) :- % refine with acc aux info
    mod_typedb(T,TypeDef),
    fast_write(mod_typedb(T,TypeDef)),
    fail.
write_registry_file_types(_Module).

write_registry_file_loop(Module) :-
    registry(_,Module,Reg),
    fast_write(Reg),
    fail.
write_registry_file_loop(_Module).

:- pred write_registry_header(Module,Stream) : atm * stream + (not_fails, is_det)
   # "Writes the header of @var{Module}'s registry file to @var{Stream} from the
   data predicate @tt{registry_header/2}.".
write_registry_header(Module,Stream) :-
    reg_version(V),
    writeq(Stream,v(V)),display(Stream,'.'),nl(Stream),
    registry_header_format(V,HeaderTerms),
    write_header_terms(Stream,Module,HeaderTerms).

% TODO: unify with itf writting
write_header_terms(_Stream,_Module,[]) :- !.
write_header_terms(Stream,Module,[H|Hs]) :-
    ( registry_header(Module,H) -> true ; fail ),
    fast_write(Stream,H),
    write_header_terms(Stream,Module,Hs).

:- pred change_open_mode(+Base,+OpenMode)
   # "@var{OpenMode} is the new open mode of the module with basename
   @var{Base}. @var{OpenMode} can take the values @code{read_write} and
   @code{read_only}.".
change_open_mode(Base,OpenMode) :-
    just_module_name(Base,Module),
    read_registry_file(Module,Base,verbose),  %% if it is not loaded yet, loads it.
    retract_fact(registry_header(Module,open_mode(_OldOpenMode))),
    asserta_fact(registry_header(Module,open_mode(OpenMode))),
    add_changed_module(Module,Base,Module,current,no).

:- pred open_mode(Base,Type,OpenMode) 
   # "Module with basename @var{Base} is of type @var{Type} and it is opened
   with mode @var{OpenMode}. @var{Type} can be @code{user} or @code{library}.
   @var{OpenMode} is used to indicate if an imported module's registry can be
   updated. It can take the values @code{read_write} or @code{read_only}.".
open_mode(Base,Type,OpenMode) :-
%% It only works if module's registry has been already loaded. If it has not, it fails.
    just_module_name(Base,Module),
    current_fact(registry_header(Module,open_mode(OpenMode))),
    ( is_library(Base) ->
      Type = library
    ; Type = user
    ).

%% **********************************************************
:- doc(section, "Save registry").
%% **********************************************************

:- pred save_registry_info(+Verb,?Info) : atm * term + (not_fails, is_det)
   # "Writes on disk the registry information of the modules loaded into Ciaopp
   or related to modules loaded into Ciaopp. This information is updated by
   @pred{gen_registry_info/3}. This predicate must be called after performing
   intermodular preprocessing (analysis, specialization...), even if
   @pred{save_registry_info/3} has been used.".
save_registry_info(Verb,[time(T,[])]) :-
    %ALL changed modules MUST be saved!
    pp_statistics(runtime,_),
    ( setof(Base,M^M2^Mode^All^Req^(changed_processable_module(Base,M,M2,Mode,All,Req)),ML) ->
      write_registry_files(ML,Verb),
      retract_saved_files(ML)
    ; true
    ),
    pp_statistics(runtime,[_,T]),
    pplog(p_abs, ['{Saved registry in ',time(T),' msec.}']), !.

changed_processable_module(Base,M,M2,Mode,All,Req) :-
    changed_module(M,Base,M2,Mode,All,Req),
    module_is_processable(Base).

:- pred save_registry_info(+Verb,+CurrBase,?Info)
   : atm * atm * term + (not_fails, is_det)
   # "Writes on disk the registry information of the modules related to the
   current module (@var{CurrBase}) which have been modified. This information is
   updated by @pred{gen_registry_info/3}. Even if this predicate is used,
   @pred{save_registry_info/2} must be used after performing intermodular
   preprocessing.".
save_registry_info(Verb,CurrBase,[time(T,[])]) :-
    pp_statistics(runtime,[T0,_]),
    just_module_name(CurrBase,CurrModule),
    ( setof(Base,Mode^M^All^Req^(changed_processable_module(Base,M,CurrModule,Mode,All,Req)),ML) ->
      write_registry_files(ML,Verb),
      retract_saved_files(ML)
    ; true
    ),
    pp_statistics(runtime,[T1,_]),
    T is T0 - T1,
    pplog(p_abs, ['{Saved registry in ',time(T),' msec.}']), !.

write_registry_files([],_Verb).
write_registry_files([Base|BList],Verb) :-
    just_module_name(Base,M),
    write_registry_file(Base,M,Verb),
    write_registry_files(BList,Verb).

retract_saved_files([]).
retract_saved_files([Base|Bases]) :-
    retractall_fact(changed_module(_,Base,_,_,_,_)),
    retract_saved_files(Bases).
