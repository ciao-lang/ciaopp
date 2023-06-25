:- module(_,[
    % intermodular program graph
    add_main_module/1,
    main_module/2,
    punit_module/2,
    local_ana_module/2,
    % intermodular analysis graph
    registry/3,
    registry_header/2
    ],[assertions, isomodes, regtypes, nativeprops, datafacts]).

:- include(intermod_options). % intermod compilation options

% ------------------------------------------------------------
:- doc(title, "Database for intermodular analysis driver").
% ------------------------------------------------------------

:- doc(module, "This module contains the predicates used as data base (state) of
intermodular analysis. This includes the program unit graph, i.e., the
imported/exported modules graph; and the global analysis graph (registry), i.e.,
the intermodular equivalent of complete/7 in plai_db, that contains the
relations of the predicates in the boundaries of the modules, i.e., how exported
predicates call imported predicates.").

:- use_module(library(streams), [absolute_file_name/7]).
:- use_module(library(compiler/p_unit/aux_filenames), [just_module_name/2]).
:- use_module(library(compiler/p_unit/program_keys), [predkey_from_sg/2]).

% ------------------------------------------------------------
:- doc(section, "Program structure").
% ------------------------------------------------------------

:- export(module_depth/2).
:- data module_depth/2.

:- data main_module/2.
:- pred main_module(Base,Mod) # "Succeeds if @var{Base} is an entry module of the
   program unit to be analyzed.".

:- data punit_module/2.
:- pred punit_module(Base,Mod) # "Succeeds if @var{Base} is a module of the
   program unit to be analyzed (if reachable).".

:- data local_ana_module/2.
:- pred local_ana_module(Base,Mod) # "Succeeds if @var{File} is a module of the
   program unit that is being analyzed in this iteration of the intermodular analysis.".
% IG: replaces curr_file of itf_db

:- export(imported_module/2).
:- pred imported_module(Module,Base) %% => atm * atm
   %% IG: disabled types to be able to run rtchecks on data
   # "Enumerates the modules imported by the current module".
:- data imported_module/2.

:- export(caller_module/2).
:- pred caller_module(Module,BaseName) %% => atm * atm
   %% IG: disabled types to be able to run rtchecks on data
   # "List of caller modules to be processed.".
:- data caller_module/2.

:- export(src_changed/1).
:- data src_changed/1. % IG: data for storing which modules were
                  % detected to be modified by the compiler (and
                  % therefore need processing)
:- export(add_src_changed/1).
add_src_changed(Base) :-
    current_fact(src_changed(Base)), !.
add_src_changed(Base) :-
    assertz_fact(src_changed(Base)).

:- export(unset_src_changed/1).
unset_src_changed(Base) :-
    retract_fact(src_changed(Base)), !.
unset_src_changed(_).

:- export(clean_program_structure/0).
clean_program_structure :-
    retractall_fact(main_module(_,_)),
    retractall_fact(punit_module(_,_)),
    retractall_fact(local_ana_module(_,_)),
    retractall_fact(module_depth(_,_)),
    retractall_fact(imported_module(_,_)),
    retractall_fact(caller_module(_,_)),
    retractall_fact(src_changed(_)).

add_main_module(File):-
    absolute_file_name(File, '_opt', '.pl', '.', _, AbsBase, _),
    just_module_name(AbsBase,Module),
    % TODO: check if already added
    assertz_fact(main_module(AbsBase, Module)).

:- export(set_main_module/1).
:- pred set_main_module(+File) + not_fails.
set_main_module(File):-
    absolute_file_name(File, '_opt', '.pl', '.', _, AbsBase, _),
    just_module_name(AbsBase,Module),
    assertz_fact(main_module(AbsBase, Module)).

:- export(set_punit_modules/1).
:- pred set_punit_modules(+File) : list + not_fails.
set_punit_modules([]).
set_punit_modules([AbsBase|Ms]) :-
    just_module_name(AbsBase,Module),
    assertz_fact(punit_module(AbsBase, Module)),
    set_punit_modules(Ms).

:- pred set_local_ana_modules(Mods) : list + (not_fails, is_det).
:- export(set_local_ana_modules/1).
set_local_ana_modules(Mods) :-
    retractall_fact(local_ana_module(_,_)),
    ( % failure-driven loop
        member(File, Mods),
        just_module_name(File,Mod),
        assertz_fact(local_ana_module(File,Mod)),
        fail
    ; true
    ).

% ------------------------------------------------------------
:- doc(section, "Intermodular analysis graph").
% ------------------------------------------------------------

:- data registry/3.
:- pred registry(Key,Module,Registry) % :: atm * atm * regdata_type
   %% IG: disabled types to be able to run rtchecks on data
   # "Data predicate to locally store information about the registry of one or
   several modules. @var{Module} is the name of the module for which
   @var{Registry} is an entry in the registry file. It corresponds to the
   @em{global answer table} as it is described in @cite{mod-an-spec_tr_2003}, or
   other auxiliary information (e.g., types).".

%% ------------------------------------------------------------
:- data registry_header/2.
:- pred registry_header(Module,HeaderTerm) %% :: atm * term
   %% IG: disabled types to be able to run rtchecks on data
   # "@var{HeaderTerm} is a term read from the registry header of module
   @var{Module}. Data predicate to store the header terms of every registry file
   read. The list of registry header terms depends on the registry file version,
   and is stored in @tt{registry_header_format/2}".

:- regtype regdata_type/1
   #"Regular type to store the semantic information of a predicate in a
   registry. It has the form
   @tt{regdata(Id,AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,Mark)} where:

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

:- export(get_registry/4).
get_registry(SgKey,Mod,RegData,Ref) :-
    current_fact(registry(SgKey,Mod,RegData), Ref), !.

:- export(add_registry/2).
add_registry(Module, Reg) :-
    ( Reg = regdata(_Id, _AbsInt,Sg,_Call,_Succ,_Spec,_ImdgList,_,_Mark) ->
        predkey_from_sg(Sg, SgKey)
    ; SgKey = none %% It has no key!! % TODO: does it make sense?; throw exception if code never reaches this point
    ),
    assertz_fact(registry(SgKey,Module,Reg)).

regdata_set_mark(OldReg, Mark, NewReg) :-
    OldReg = regdata(Id, AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,_),
    NewReg = regdata(Id, AbsInt,Sg,Call,Succ,Spec,Imdg,Chdg,Mark).

:- export(cleanup_registry/1).
cleanup_registry(Module) :-
    retractall_fact(registry(_,Module,_)),
    retractall_fact(registry_header(Module,_)),
    retractall_fact(mod_typedb(_,_)).

%% --------------------------------------------------------------------
:- export(reg_version/1).
:- pred reg_version(Version) => atm
   # "Contains a version number which identifies
   the registry files associated with this version of the assertion
   library. Should be changed every time changes are made which render
   registry files incompatible, since this forces recomputation
   of all such files.".
reg_version('2.4').

%reg_extension('.reg').  %% moved to in p_asr

:- export(registry_header_format/2).
:- pred registry_header_format(Version,TermList) : atm(Version) => list(TermList)
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
% pl_date is not used because the compiler detects changes in the sources
registry_header_format('2.4',
    [ entries_already_analyzed(_),%% List of domains for which module entries have been analyzed
      open_mode(_),   %% Mode in which the .reg file is opened (read_write, read_only).
      module_base(_)
    ]).

%% --------------------------------------------------------------------
% global type definitions in the modular driver
:- export(mod_typedb/2).
:- pred mod_typedb(Module,TypeDef) => atm * term
   # "Data predicate to locally store information about the types used in the
   registry of one or several modules. @var{Module} is the name of the module
   for which the type definition @var{TypeDef} is referenced in the registry
   file. The original definition of @var{TypeDef} may not reside in
   @var{Module}, but in a related module.".
mod_typedb(T,D) :-
    mod_typedb_(T,D).

:- data mod_typedb_/2.
:- export(add_mod_typedb/2).
add_mod_typedb(T,D) :-
    ( get_mod_typedb(T,_,_) -> true ;
    assertz_fact(mod_typedb_(T,D))).
get_mod_typedb(T,D, Ref) :-
    current_fact(mod_typedb_(T,D), Ref).

:- export(enum_mod_typedb/1).
enum_mod_typedb(typedef(T,D)) :-
    mod_typedb_(T,D).