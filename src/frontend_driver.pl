:- module(_, [],
    [
        assertions,
        basicmodes,
        % isomodes, % TODO: for printer
        regtypes,
        nativeprops,
        hiord, % TODO: only for printer part
        datafacts,
        ciaopp(ciaopp_options)
    ]).

:- doc(title, "Frontend driver (monolithic)").
% TODO: add incrental/modular (with parts as a plugin)?

:- doc(usage, "@tt{:- use_module(ciaopp(frontend_driver))}.
   This module is loaded by default in the CiaoPP toplevel and
   reexported from the @lib{ciaopp} module.").

:- doc(module, "This module provides the main entry points for
   loading source programs (in a suitable form for performing analysis
   and transformations) and print them back as source.

   @section{Adding new frontend}

   (to be written)
").

:- doc(bug,"1. Remember to do the cleaning_up lazily").

% ---------------------------------------------------------------------------
% (Common)

:- use_package(ciaopp(p_unit/p_unit_argnames)).
:- use_module(ciaopp(p_unit), [get_output_package/1]).

:- use_module(ciaopp(p_unit/p_printer)).

:- use_module(ciaopp(ciaopp_log), [pplog/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(engine(internals), [module_concat/3]).

:- use_module(ciaopp(preprocess_flags),
    [current_pp_flag/2, set_pp_flag/2, push_pp_flag/2, pop_pp_flag/1]).

:- use_module(library(aggregates), [findall/3]).

% ===========================================================================
:- doc(section, "Frontend languages").

:- if(defined(has_ciaopp_llvm)).
:- use_module(ciaopp_llvm(c_translate)).
:- endif.

:- if(defined(has_ciaopp_java)).
:- use_module(ilciao(java_interface)).
:- use_module(cafelito(annotator),[cafelito_module/2]).
:- endif.

:- use_module(ciaopp(preprocess_flags),[current_pp_flag/2]).

:- regtype language/1.
language(X) :- atom(X).

:- regtype file_name/1. % TODO: duplicated?!
file_name(X) :- atom(X).

:- regtype module_name/1. % TODO: duplicated?!
module_name(X) :- atom(X).

:- regtype transformation/1. % TODO: duplicated?!
transformation(X) :- atom(X). % TODO: this is tranformation name, this should not be here

:- export(supported_language/1).
:- doc(supported_language(L),
    "Indicates that a translation is available from language
     @var{L} to Ciao Prolog language.").
supported_language(ciao).
:- if(defined(has_ciaopp_llvm)).
supported_language(c).
:- endif.
:- if(defined(has_ciaopp_java)).
supported_language(java).
:- endif.

:- export(language_extension/2).
:- doc(language_extension(L,E),
    "@var{E} is an extension (including the dot) for files
     that must be translated from language @var{L} to Ciao.").
language_extension(ciao,        '.pl').
:- if(defined(has_ciaopp_llvm)).
language_extension(c,           '.c').
:- endif.
:- if(defined(has_ciaopp_java)).
language_extension(java,        '.java').
:- endif.

:- export(language_output_extension/2).
:- doc(language_output_extension(L,E),
    "@var{E} is the extension of the file produced as
     output by the Ciao printer for language @var{L}.").
language_output_extension(ciao,        '.pl').
:- if(defined(has_ciaopp_llvm)).
language_output_extension(c,           '.pl').
:- endif.
:- if(defined(has_ciaopp_java)).
language_output_extension(java,        '.java').
:- endif.

:- use_module(engine(runtime_control),
              [push_prolog_flag/2, pop_prolog_flag/1]). % TODO: do in a better way

:- export(translate_input_file/5).
:- pred translate_input_file(L,In,O,M,Out)
    : (language(L),file_name(In),list(atm,O),module_name(M),var(Out))
       => (language(L),file_name(In),list(atm,O),module_name(M),file_name(Out)).
:- doc(translate_input_file(L,In,O,M,Out),
    "This is the main predicate called when the file @var{In}
     needs to be translated from language @var{L} into Ciao Prolog.
     Some options to the translation may be passed in the
     variable @var{O} and the module name that one wants to
     get can be given in @var{M}. The translation should produce
     a file and indicate where it is located through @var{O}.").
translate_input_file(ciao, I, _, _, I).
:- if(defined(has_ciaopp_llvm)).
translate_input_file(c, I, _, _, Pl) :- translate_c(I,Pl).
:- endif.
:- if(defined(has_ciaopp_java)).
translate_input_file(java, I, _, _, NI) :-
    current_pp_flag(java_analysis_level,source),!,
    cafelito_module(I,NI).
translate_input_file(java, I, _, _, NI) :-
    java_stop_jvm,
    push_prolog_flag(write_strings, on),
    java_start_jvm,
    get_class_name_from_file(I, Main_Class),
    java_generate_ciao(Main_Class),
    get_ilciao_output_file(NI),
    pop_prolog_flag(write_strings).
:- endif.

:- export(initial_transformations/2).
:- pred initial_transformations(L,T)
    : (language(L), var(T))
       => (language(L), list(transformation,T)).
:- doc(initial_transformations(L,T), "@var{T} is the initial list of
    transformations needed for language @var{L} after it has been
    loaded as clauses.").

initial_transformations(ciao,        []).
:- if(defined(has_ciaopp_llvm)).
initial_transformations(c,           [unfold_entry]).
:- endif.
:- if(defined(has_ciaopp_java)).
initial_transformations(java,        [unfold_entry]):-
    current_pp_flag(java_analysis_level, source),!.
initial_transformations(java,        []).
% (archived)
% initial_transformations(xc,          [unfold_entry]).
% initial_transformations(xc_assembly, [unfold_entry]).
:- endif.

:- export(detect_language/2).
:- pred detect_language(AbsFile, Lang) # "@var{Lang} is the
   detected language for @var{AbsFile} file.".

detect_language(AbsFile, Lang) :-
    ( supported_language(Lang0),
      language_extension(Lang0, Ext),
      atom_concat(_, Ext, AbsFile) ->
        Lang = Lang0
    ; Lang = ciao
    ).

% ===========================================================================
:- doc(section, "Module loading for preprocessing").

:- use_module(engine(internals), [opt_suff/1]).
:- use_module(engine(stream_basic), [sourcename/1, absolute_file_name/7]).
:- use_module(engine(runtime_control), [push_prolog_flag/2, pop_prolog_flag/1]).

:- use_module(ciaopp(p_unit), [preprocessing_unit/3]). 
% :- use_module(typeslib(typeslib),[assert_initial_types/0]). 
:- use_module(ciaopp(p_unit/unexpand), [ 
    generate_unexpanded_data/1, % TODO: kludge?
    clean_unexpanded_data/0     % TODO: kludge?
   ]).
:- use_module(ciaopp(p_unit/itf_db), [curr_module/1, curr_file/2]).

% (support for incremental analysis)
:- use_module(ciaopp(plai/incanal), [incremental_module/2]).

:- export(module/1).
:- pred module(+FileName) : sourcename
    # "Reads the code of @var{FileName} and its preprocessing unit,
      and sets it as the current module.".
:- pred module(+FileNameList) : list(atm)
    # "Reads the code of the list of file names @var{FileNameList} (and
       their preprocessing units), and sets them as the current
       modules.".
module(Ms):-
    module(Ms, _Info).

ensure_list(Ms0,Ms) :- Ms0 = [_|_], !, Ms = Ms0.
ensure_list(M,[M]).

:- export(module/2).
:- pred module(+Ms,-Info) # "Same as @pred{module/1} but it also
      prints the time required to read the module and returns extra
      information (including the time) on its second argument.".
module(Ms, Info):-
    ensure_list(Ms, Ms2),
    module_(Ms2, Info).

:- use_module(ciaopp(analyze_driver),
    [clean_analysis_info/0, clean_analysis_info0/0]).

:- if(defined(with_fullpp)).
module_(ModList, Info):-
    current_pp_flag(incremental, on), !,
    incremental_module(ModList, Info).
:- endif. % with_fullpp
module_(ModList, Info):-
    clean_analysis_info0, % TODO: merge! see definition, cleanup_types/0?
    cleanup_all,
    load_modules(ModList,Info),
    curr_file(_, Mod), % TODO: use failure-driven loop?
    clean_unexpanded_data,
    generate_unexpanded_data(Mod). % TODO: only for output?

load_modules(ModList,Info) :-
    ensure_lib_sources_loaded,
    pp_statistics(runtime,[T0,_]),
    absolute_file_names(ModList,AbsFileList),
    % (only for message, avoid list if possible)
    ( AbsFileList = [AbsFileDesc] -> true
    ; AbsFileDesc = AbsFileList
    ),
    pplog(load_module, ['{Loading current module from ' , ~~(AbsFileDesc)]),
    %
    assert_curr_files(AbsFileList), % TODO: move into preprocessing_unit/3?
    % assert_initial_types,
    preprocessing_unit(AbsFileList,_Ms,E),
    ( E == yes -> Info=[error|Info0] ; Info=Info0 ),
    pp_statistics(runtime,[T1,_]),
    TotalT is T1 - T0,
    pplog(load_module, ['{loaded in ',time(TotalT), ' msec.}']),
    Info0=[time(TotalT,[])],
    pplog(load_module, ['}']),
    % Perform initial transformations -- ASM % TODO: improve?
    detect_language_from_list(AbsFileList, Lang),
    initial_transformations(Lang, Trans),
    perform_transformations(Trans), !. % TODO: module leaves choicepoints, fix!!
    % The analysis is transparent so setting prog_lang to ciao
    % after loading module should not effect analysis.
    %set_pp_flag(prog_lang, ciao).

absolute_file_names([], []).
absolute_file_names([M|Ms], [A|As]):-
    opt_suff(Opt),
    absolute_file_name(M, Opt, '.pl', '.', A, _, _),
    absolute_file_names(Ms, As).

:- pred assert_curr_files(Fs) : list(Fs)
   # "Fill @pred{curr_module/1} and @pred{curr_file/2}.".
assert_curr_files([]) :- !.
assert_curr_files([F|Fs]) :-
    mod_from_base(F, M),
    % TODO: why not assertz? JF
    assertz_fact(curr_module(M)),
    assertz_fact(curr_file(F, M)),
    %
    assert_curr_files(Fs).

mod_from_base(N, M) :-
    path_splitext(N, NoExt, _),
    path_split(NoExt, _, M1),
    get_module(N,M1,M).

:- if(defined(has_ciaopp_java)).
% TODO: If file is java, module name is preceeded by 'examples.', needs to
%   be resolved at analysis part to avoid 'examples.' prefix.
get_module(File,M1,M):-
    % TODO: hack, added by UL % TODO: detect language and call hook
    current_pp_flag(java_analysis_level,bytecode),
    atom_concat(_, '.java', File),
    !,
    atom_concat('examples.',M1, M).
:- endif.
get_module(_,M0,M) :-
    opt_suff(Opt), % IG: remove suffix from module name (language-dependent?)
    atom_codes(M0, M0L),
    atom_codes(Opt,OL),
    append(ML,OL,M0L), !,
    atom_codes(M,ML).
get_module(_,M,M).

detect_language_from_list([AbsFile|_], Lang) :- !,
    detect_language(AbsFile, Lang).
detect_language_from_list(_, Lang) :- Lang = ciao.

% ---------------------------------------------------------------------------
% Use cached libraries
%
% Lib cache to load faster (requires running gen_lib_cache command)

:- use_module(library(persdb/datadir), [ensure_datadir/2]).
:- use_module(ciaopp(p_unit/p_asr), [load_lib_sources/1, loaded_lib_sources/0]).

:- export(ensure_lib_sources_loaded/0).

:- pred ensure_lib_sources_loaded/0 #"Loads the already preprocess sources of
the libraries. This predicate is called implicitly by @pred{module/1} but that
we can call it explicitly to ensure that the cache is preloaded.".
ensure_lib_sources_loaded :-
    current_pp_flag(preload_lib_sources, on),
    % Check if they were already loaded
    \+ loaded_lib_sources, !,
    ensure_datadir('ciaopp_lib_cache', Dir),
    catch(load_lib_sources(Dir), _, true).
    % TODO: warn if not defined??
    % TODO: call command to generate them if not defined??
ensure_lib_sources_loaded.

% ---------------------------------------------------------------------------
% Cleanup
:- use_module(ciaopp(analyze_driver), [clean_analysis_info/0]).
:- use_module(ciaopp(plai/intermod_ops), [cleanup_p_abs/0]).
:- use_module(ciaopp(p_unit/itf_db), [cleanup_itf_db/0]).
:- use_module(ciaopp(p_unit), [cleanup_punit/0, cleanup_comment_db/0]).
:- use_module(ciaopp(p_unit), [pr_key_clean/0, cleanup_commented_assrt/0]).
:- use_module(ciaopp(p_unit/p_asr), [cleanup_code_and_related_assertions/0, cleanup_pasr/0]).
%
% TODO: make sure that it does what it is documented (are domains, types, etc. cleanup?)
:- pred cleanup_all # "Cleanup the whole CiaoPP state (equivalent to
   start from scratch)".

cleanup_all :-
    cleanup_itf_db,
    clean_analysis_info,
    cleanup_punit,
    cleanup_pasr,
    cleanup_code_and_related_assertions,
    %
    cleanup_commented_assrt,
    cleanup_comment_db,
    pr_key_clean.

%------------------------------------------------------------------------

:- use_module(ciaopp(transform_driver), [transform/1]).

:- pred perform_transformations/1 : list(atom)
    # "Executes transformations over a file".
perform_transformations([]).
perform_transformations([E|Ls]) :-
    transform(E),
    perform_transformations(Ls).

% ===========================================================================

:- doc(section, "Output of preprocessor").

:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(system), [copy_file/3]).
:- use_module(library(pathnames)).
:- use_module(library(lists)).

:- use_module(ciaopp(p_unit), [internal_predicate_names/1]).
:- use_module(ciaopp(p_unit/itf_db),   [curr_file/2]).
:- use_module(ciaopp(p_unit/unexpand),
              [transform_clause_list/3, transform_name/3]).

:- if(defined(with_fullpp)).
:- use_module(ciaopp(raw_printer), [raw_output/1]).
:- endif. % with_fullpp

:- use_module(library(pretty_print),  [pretty_print/4]).
:- use_module(library(messages),      [error_message/2, warning_message/2]).
:- use_module(library(odd), [setarg/3]). % TODO: DO NOT USE IT!
:- use_module(library(terms),         [atom_concat/2]).

:- use_module(typeslib(typeslib), [get_required_types/1, typedef_to_pred/3]).
:- use_module(library(format), [format/3]).

% :- include(engine(builtin_exports)).
% :- include(engine(builtin_modules)).
% builtin_module(_):- fail.
% builtin_export(_ModName,_F,_A,_Meta):- fail.

%------------------------------------------------------------------------
% DUMP MODULE.
%------------------------------------------------------------------------
:- if(defined(with_fullpp)).
:- reexport(ciaopp(p_unit/p_dump)).
:- endif. % with_fullpp

%------------------------------------------------------------------------

% Solved already
% :- doc(bug,"Some assertions (for predicates with no clauses) might
%       be missing in the output.").
% :- doc(bug,"Multifile and meta_predicates declarations are not printed,
%       and initialization, and on_abort, and....").

% TODO: find test for these bugs
% Solved
% :- doc(bug,"1. Should not print required types if they are already
%       predicates in the source.").
% :- doc(bug,"2. Names of required types should not clash with names
%       already visible to the current module.").
% :- doc(bug,"3. Imports from engine() modules are not printed: this
%       might be wrong.").
% :- doc(bug,"4. An [assertions] package is printed: this might be wrong.
%        Idem with [regtypes].").
% :- doc(bug,"5. A use_module(library(assertions/native_props)) is printed:
%       this IS wrong!").
% :- doc(bug,"6. Operators should be activated to print.").
% :- doc(bug,"7. comp and prop assertions are lost in the output.").
:- doc(bug, "8. Printing a slightly big program takes too long!. This is 
    probably due to calling type simplification too many time...").
:- doc(bug, "9. It should be possible to decide which properties should be 
    printed when showing analysis results. For example, I may not be interested 
    in arguments being var but only on whether they are ground.").
:- doc(bug, "10. When showing predicate level analysis information, 
    normalization of the completes is not required if there is only one 
    complete for the predicate").
%% :- doc(bug,"11. When showing program point level analysis information and 
%%      collapse_ai_versions is turned off, info should not be collapsed 
%%         but instead shown as different possibilities").
%% :- doc(bug,"12. Unexpand module names in meta-arguments. This shows
%%      in list('basic_props:atm',A) in e.g. analisis.pl. Also in true(G)
%%         for the pp_info of an analysis.").
%% :- doc( bug, "13. When Asseritiong Body has ([A];[B]), A and B are
%%                   not well printed. Look at:
%%                   ['term_typing:var'(X)];['term_typing:var'(X)]." ).

%% :- doc( bug , "11. TODO:  _opt.pl link" ).

%% :- doc( bug , "12. The following comment
%%                    :- doc(title,"Term input").  
%%                    is written by output/1 as
%%                    :- doc(title,[84,101,114,109,32,105,110,112,117,116])"). 

%------------------------------------------------------------------------

:- use_module(ciaopp(p_unit), [get_output_path/2]).

:- export(output/0).
:- pred output # "Outputs the current Module preprocessing state to a
   file named Module@tt{_opt.ext}, where Module is the current
   module.".

output :-
    get_output_path(yes, OptFile),
    % Create output file
    output(OptFile),
    % Create _co symbolic link (points to latest output file)
    get_output_path(no, COFile),
    ( create_output_symlink(COFile, OptFile) ->
        true
    ; warning_message("Symbolic link to output file failed!", [])
    ).

% Create _co symbolic link (points to latest output file)
create_output_symlink(COFile, OptFile) :-
    ( COFile = OptFile ->
        true
    ; % Create relative symlink (assumes that dirnames are the same)
      path_split(OptFile, _, RelOptFile),
      copy_file(RelOptFile, COFile, [overwrite, symlink])
    ).

% TODO: output_by_ext/2 is strange, should it take lang instead?
:- export(output/1).
:- pred output(+Output) # "Outputs the current module preprocessing
   state to a file @var{Output}. The output format (which should be
   valid for the loaded program) is guessed from the file extension.".

output(File) :-
    path_splitext(File, _, Ext),
    ( output_ext(Ext) -> true
    ; error_message("unknown output extension ~w", [Ext]),
      fail
    ),
    open(File, write, Stream),
    ( output_by_ext(Ext, Stream) ->
        Err = no
    ; Err = yes
    ),
    close(Stream),
    ( Err = yes ->
        error_message("generating output of file ~w", [File]),
        fail
    ; true
    ),
    pplog(output, ['{written file ',~~(File),'}']).

% ---------------------------------------------------------------------------

:- export(output_ext/1).
:- pred output_ext(Ext) : (atm(Ext))
   # "Extension @var{Ext} is a supported output extension.".

:- discontiguous(output_ext/1).

:- export(output_by_ext/2).
:- pred output_by_ext(Ext, File) : (atm(Ext), sourcename(File))
   # "Produce output @var{File} for the given extension @var{Ext}.".

:- discontiguous(output_by_ext/2).

% ---------------------------------------------------------------------------
% TODO: move somewhere else?

:- use_module(ciaopp(infer/prepare_ai_output), [cleanup_output/1, prepare_ai_output/4]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(infer/infer_db), [domain/1]).
:- use_module(ciaopp(infer/infer_dom), [non_collapsable/1]).

% :- export(analysis_info_to_assertions/0).
analysis_info_to_assertions :-
    curr_file(_, M),
    % Delete true assertions
    cleanup_output(M),
    current_pp_flag(collapse_ai_vers, Collapse0),
    current_pp_flag(pp_info,          PPoints),
    current_fact(domain(AbsInt)),
    ( non_collapsable(AbsInt) -> Collapse=off ; Collapse=Collapse0 ),
    % TODO: dangling choice points in prepare_ai_output?
    ( prepare_ai_output(PPoints, cl, AbsInt, Collapse) -> true ),
    fail.
analysis_info_to_assertions.

% ---------------------------------------------------------------------------

output_ext('.pl').
:- if(defined(with_fullpp)).
output_by_ext('.pl', Stream) :-
    current_pp_flag(output_lang, raw), !,
    raw_output(Stream).
:- endif. % with_fullpp
output_by_ext('.pl', Stream) :- !,
    ( current_pp_flag(dump_ai, on) -> analysis_info_to_assertions ; true ),
    write_mod_headers(Stream),
    print_program(Stream),
    write_types(Stream).

% TODO: make output_by_ext/2 a hook
:- if(defined(with_fullpp)).
:- if(defined(has_ciaopp_llvm)).
:- include(ciaopp_llvm(printer_llvm)).
:- endif.
:- if(defined(has_ciaopp_java)).
:- include(ciaopp(printer_java)).
:- endif.
:- endif. % with_fullpp

% ---------------------------------------------------------------------------

:- if(defined(preserve_mod_headers)).
% Recover header declarations from the original source
% (EMM)

:- use_module(ciaopp(p_unit/clause_db), [source_clause/3]).

% TODO: MH: may be incorrect? Needs revision!

% TODO: merge versions, both are useful, e.g., when module is created
%   on the fly without any original source clauses (JF)

:- doc(bug, "MH: (decls_from_source) For user files use_packages are
   not recorded properly and are not returned by
   get_output_package. They are printed in the end from the code,
   except the first one which somehow disappears.").

% MH: Would need a bit of cleanup and moving some parts out to
%     separate predicates but bug above needs to be fixed first.
write_mod_headers(Stream) :-
    % Get all the packages used by the file (this probably needs some revision).
    findall(Pkg, get_output_package(Pkg), AllPackages),
    % If file contains a module directive, then include all the packages
    % in the module declaration.
    ( ( current_fact(source_clause(_Key, directive(module(Module, Exports, ModDeclPackages)), Dict), _Ref) ->
          difference(AllPackages, ModDeclPackages, AddtlPackages),
          append(ModDeclPackages, AddtlPackages, FinalPackages),
          Body = module(Module, Exports, FinalPackages)
      ; current_fact(source_clause(_Key, directive(module(Module, Exports)), Dict), _Ref) ->
          ( AllPackages = [] % May not happen in practice if some packages added by default
          -> Body = module(_, Exports) % TODO: wrong! only if AllPackages is the 'default' case
          ;  Body = module(Module, Exports, AllPackages)
          )
      ) ->
        pretty_print(Stream, directive(Body), [], Dict),
        nl(Stream)
    ; % TODO: MH: I think in the case of user files no packages are recorded and this does not work. 
      % (failure-driven loop)
      ( member(Package, AllPackages),
          pretty_print(Stream, directive(use_package(Package)), [], []),
          fail
      ; true
      )
    ).

:- else.

:- use_module(library(write),      [writeq/2]).
:- use_module(ciaopp(p_unit/unexpand),   [transform_body/3]).
:- use_module(ciaopp(p_unit),     [type_of_goal/2]).
:- use_module(ciaopp(p_unit/itf_db), [current_itf/3]).

write_mod_headers(S) :-
    curr_file(_, Mod), % TODO: is it correct?
% engine default imports
%       findall( engine(M) , builtin_module(M), B_List ),
%       required_engine(B_List, Flag),
% exports
    findall(F/A,
        ( pred_spec(exported(Mod), Mod, F, A),
            module_concat(Mod, F, MF),
% if imported and exported => reexported 
% ==> no need to appear in exported list
            current_itf(defines, MF, A)
        ), E_List),
    print_header(Mod, S, E_List),
    nl(S).

print_header(user(_Mod), S, _E_List) :-
    !,
    display(S, ':- use_package(assertions).\n').
print_header(_Mod, S, E_List) :-
    display(S, ':- module(_'),
% DTM: Note that module name should not contain
% illegal characters
%       atom_concat( '_' , Mod , Mod2 ),
%       displayq( S , Mod2 ),
    ( E_List = [_|_] ->
        display(S, ', ['),
        print_atom_list(E_List, S),
        display(S, ']')
    ;
        display(S, ', []')
    ),
    findall(Pkg, get_output_package(Pkg), Packages),
    display(S, ', ['),
    print_atom_list(Packages, S),
    display(S, ']).\n\n').

print_atom_list([],  _).
print_atom_list([A], S) :-
    !,
    writeq(S, A).
print_atom_list([A|As], S) :-
    writeq(S, A),
    display(S, ', '),
    print_atom_list(As, S).

pred_spec(T, N, F, A) :-
    type_of_goal(T, G),
    transform_body(G, N, GT0),
    dont_want_qualification(GT0, GT),
    functor(GT, F, A0),
    special(F, A0, A).

dont_want_qualification(_:G, G) :- !.
dont_want_qualification(G,   G).

special(this_module, 2, 1) :- !.
special(_,           A, A).

:- endif. % decls_from_source

% --- DTM: THIS HAS TO BE A HOOK
write_types(S) :-
    get_required_types(Rules),
    nl(S),
    write_list_types(Rules, S).

write_list_types([],       _).
write_list_types([Rule|L], S) :-
    write_one_type(Rule, S),
    write_list_types(L, S).

:- export(write_one_type/2).
write_one_type(typedef(::=(Pred, Def)), S) :-
    p_unit:internal_predicate_names(InternalNames),
    functor(Pred, TypeName, Ari),
    PredAri is Ari + 1,
    curr_file(_, M),
    ( member((TypeName, PredAri, Name), InternalNames) ->
        true
    ; Name=TypeName
    ),
    transform_name(Name, M, NameT),
    format(S, ":- regtype ~q/~w.~n", [NameT, PredAri]),
    transform_one_type_clause(Def, (TypeName, NameT), DefT),
    typedef_to_pred(DefT, NameT, Cls),
    transform_clause_list(Cls, M, ClsT),
%       transform_types_clauses( ClsT , (TypeName , NameT) , ClsTT ),
    pretty_print(S, ClsT, [], _),
    nl(S).

transform_one_type_clause(TH, (N, NT), THT) :-
    functor(TH, F, A),
    ( F==N ->
        FT = NT
    ; FT = F
    ),
    TH =.. [_|Args],
    THT =.. [FT|Args],
    transform_one_type_clause_args(A, THT, (N, NT)).
transform_one_type_clause(TH, _, TH).

transform_one_type_clause_args(0, _,    _) :- !.
transform_one_type_clause_args(N, Pred, T) :-
    N1 is N - 1,
    arg(N, Pred, ArgN),
    transform_one_type_clause(ArgN, T, ArgNT),
    setarg(N, Pred, ArgNT),
    transform_one_type_clause_args(N1, Pred, T).

% ---------------------------------------------------------------------------

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).

:- export(check_global_props/2).
check_global_props(In, Out) :-
    assertion_body(Pred, Compat, Call0, Succ, Comp0, Comm, In),
    compact_props(Call0, compact_calls_prop, Call),
    compact_props(Comp0, comp_remove_first_argument, Comp1),
    compact_props(Comp1, compact_global_prop, Comp),
    assertion_body(Pred, Compat, Call, Succ, Comp, Comm, Out).

:- meta_predicate compact_props(?, pred(2), ?).
compact_props([],   _,   []) :- !.
compact_props([A0|B0], CompactProp, [A|B]) :- !,
    compact_props(A0, CompactProp, A),
    compact_props(B0, CompactProp, B).
compact_props(A, CompactProp, B) :-
    CompactProp(A, B).

% TODO: rename by comp_remove_goal_arg or comp_unapply? (similar to prop_unapply)
comp_remove_first_argument(M:A, M:B) :- !,
    comp_remove_first_argument(A, B).
comp_remove_first_argument(A, B) :-
    A =.. [F, _|Args],
    !,
    B =.. [F|Args].
comp_remove_first_argument(A, B) :-
    A =.. [B].

% TODO: compact_global_prop/2 is a hook, and its implementation
% TODO: for cost properties must not be implemented here, but in a
% TODO: separated module (perhaps resources ???). --EMM

% :- multifile custom_compact_global_prop/2.

:- if(defined(with_fullpp)).
:- if(defined(has_ciaopp_cost)).
:- use_module(library(resdefs/rescostfunc), [compact_cf/3, compact_size/3]).
:- endif.
:- endif. % with_fullpp

:- if(defined(with_fullpp)).
:- if(defined(has_ciaopp_cost)).
compact_global_prop(cost(Rel, Ap, Type, Res, _, IF, CFN), Cost) :-
    compact_cf(CFN, IF, CF),
    compact_cost(Rel, Ap, Type, Res, CF, Cost),
    !.
:- endif.
:- endif. % with_fullpp
compact_global_prop(C, C).

:- if(defined(with_fullpp)).
:- if(defined(has_ciaopp_cost)).
compact_calls_prop(intervals(_, G, _, L), intervals(S, L)) :-
    compact_size(G, _, S), !.
:- endif.
:- endif. % with_fullpp
compact_calls_prop(A, A).

:- if(defined(with_fullpp)).
:- if(defined(has_ciaopp_cost)).
compact_cost(rel, Ap, Type, Res, CF, RelCost) :-
    compact_rel_cost(Type, Ap, Res, CF, RelCost).
compact_cost(abs, Ap, Type, Res, CF, AbsCost) :-
    compact_abs_cost(Type, Ap, Res, CF, AbsCost).

compact_rel_cost(call, Ap, Res, CF, rel_cost(Ap, Res, CF)) :- !.
compact_rel_cost(Type, Ap, Res, CF, rel_cost(Ap, Type, Res, CF)).

compact_abs_cost(call, Ap, Res, CF, cost(Ap, Res, CF)) :- !.
compact_abs_cost(Type, Ap, Res, CF, cost(Ap, Type, Res, CF)).
:- endif.
:- endif. % with_fullpp

% ---------------------------------------------------------------------------
:- doc(section, "Preload libraries").
% ---------------------------------------------------------------------------

:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaopp(p_unit/p_asr), [gen_lib_sources/1]).
:- use_module(ciaopp(p_unit/itf_db), [fake_module_name/1]).

:- export(cache_and_preload_lib_sources/0).
:- pred cache_and_preload_lib_sources/0
   # "Generate and preload the preprocessed assertions from the
     libraries (specified in the @tt{cmds/cachedmods/cached_core.pl}
     module.

     @alert{It cleans the current state of CiaoPP}.".

cache_and_preload_lib_sources :-
    clean_analysis_info0,
    cleanup_all,
    bundle_path(ciaopp, 'cmds/cachedmods/cached_core.pl', P),
    push_pp_flag(preload_lib_sources, off),
    module(P),
    pop_pp_flag(preload_lib_sources),
    set_fact(fake_module_name(cached_core)), % do not cache info of cached_core
    ensure_datadir('ciaopp_lib_cache', Dir),
    p_asr:gen_lib_sources(Dir),
    ensure_lib_sources_loaded.
