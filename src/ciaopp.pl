:- module(ciaopp, [], [assertions, ciaopp(ciaopp_options)]).

:- doc(title,"The CiaoPP low-level interface").
:- doc(author, "The Ciao Development Team").

% ---------------------------------------------------------------------------
% NOTE: Customize CiaoPP build modifiying the declarations at:
%
%                      ciaopp_options.pl
%
% ---------------------------------------------------------------------------

:- doc(module, "This module includes the low-level predicates for
interacting with CiaoPP. In this interaction model the user performs a
sequence of commands to obtain a certain result (e.g., load program,
analyze, check assertions).

The basic commands are:
@begin{itemize}
@item @tt{module(File)}: loads a (main) module into the preprocessor.

@item @tt{analyze(A)}: perform analysis @var{A} (see @ref{Available
  abstract domains}) on the loaded module.

@item @tt{acheck}: check assertions (using current analysis information).

@item @tt{transform(T)}: perform transformation @var{T} on the loaded module.

@item @tt{output}: output a file with the current program state (i.e.,
      the output includes transformations, analysis info, assertion
      checking, etc.  as controlled by the flags set and the actions
      performed).

@item @tt{output(File)}: same as @pred{output/0} but output to @var{File}.
@end{itemize}

The analyses and transformations are controlled by preprocessor flags. 
These flags can be modified or consulted with:

@begin{itemize}
@item @tt{current_pp_flag(F, V)}: consult the current value @var{V} of flag @var{F}.
@item @tt{set_pp_flag(F, V)}: change the value of flag @var{F} to @var{V}.
@item @tt{pp_flag(F)}: @var{F} is a preprocessor flag.
@item @tt{dump_flags(K)}: dump the set of flags identified by @var{K} (@tt{all} for all).
@end{itemize}

Other commands useful when developing or debugging CiaoPP:

@begin{itemize}
@item @tt{show_asr(File)}: displays the content of a .asr file.

@item @tt{show_dump(File)}: displays the content of a .dump file.

@item @tt{show_types}: display all current types (inferred or read).
@end{itemize}
").

% ---------------------------------------------------------------------------
% TODO: temporarily repeated here, because LPdoc is not able to include them
% TODO: (old) these onea [transformation/1], however, should be here on their own right, 
%   not in driver.pl (which goes to the internals):

%:- multifile analysis/1.
:- impl_defined(analysis/1).
:- prop analysis(Analysis)
    # "@var{Analysis} is a valid analysis identifier.".

:- doc(analysis/1, "The current supported analyses are in
   @ref{Available abstract domains}.").

%:- multifile transformation/1.
:- impl_defined(transformation/1).
:- prop transformation(Transformation)
    # "@var{Transformation} is a valid transformation identifier.".

:- doc(transformation/1, "The current supported transformations are in
   @ref{Available program transformations}.").

% ---------------------------------------------------------------------------

% TODO: hide or do not reexport?

:- reexport(ciaopp(frontend_driver)).
:- doc(doinclude,module/1).
:- doc(doinclude,analyze/1).
:- doc(hide,module/2).
:- doc(doinclude,output/1).
:- doc(doinclude,output/0).
:- doc(hide,check_global_props/2).
:- doc(hide,supported_language/1).
:- doc(hide,language_extension/2).
:- doc(hide,translate_input_file/5).
:- doc(hide,initial_transformations/2).

:- reexport(ciaopp(transform_driver)).
:- doc(doinclude,transformation/1).
:- doc(doinclude,transform/1).
:- doc(hide,transform/2).

:- reexport(ciaopp(analyze_driver)).
:- doc(doinclude,acheck/0).
:- doc(doinclude,analysis/1).
:- doc(hide,analyze/2).
:- doc(hide,acheck/1).
:- doc(hide,acheck_all/0).
% :- doc(hide,action/1).
% :- doc(hide,add_action/1).
:- doc(hide,clean_analysis_info/0).

%% From: :- reexport(ciaopp(p_unit/p_dump)).
% :- doc(hide,dump/1).
% :- doc(hide,restore/1).
% :- doc(hide,restore/2).
% :- doc(hide,show_dump/1).

% ---------------------------------------------------------------------------
% TODO: optional
% Plugin-like modules that define analyzers -- EMM

:- if(defined(with_fullpp)).
:- if(defined(has_ciaopp_extra)).
:- use_module(resources(resources_register), []).
:- use_module(infercost(infercost_register), []).
:- endif.
:- endif.

% -----------------------------------------------------------------------
% TODO: optional?
% Auto-interface

:- if(defined(with_fullpp)).
:- reexport(auto_interface(auto_interface)).
:- doc(hide,auto_analyze/1).
:- doc(hide,auto_analyze/2).
:- doc(hide,auto_optimize/1).
:- doc(hide,auto_optimize/2).
:- doc(hide,auto_check_assert/1).
:- doc(hide,auto_check_assert/2).
:- doc(hide,set_menu_level/1).
:- doc(hide,current_menu_level/1).
:- doc(hide,again/0).
:- doc(hide,set_last_file/1).
:- doc(hide,get_last_file/1).
:- doc(hide,ana_b/1).
:- doc(hide,customize_but_dont_save/1).
:- doc(hide,set_menu_flag/3).
:- doc(hide,get_menu_flag/3).

:- doc(hide,customize/1).
:- doc(hide,customize_and_preprocess/1).

%% From: :- reexport(ciaopp(menu_generator)).
:- doc(hide,get_menu_configs/1).
:- doc(hide,save_menu_config/1).
:- doc(hide,remove_menu_config/1).
:- doc(hide,restore_menu_config/1).
:- doc(hide,show_menu_configs/0).
:- doc(hide,show_menu_config/1).
:- else.
% TODO: include!
:- export(customize_and_preprocess/1).
:- impl_defined(customize_and_preprocess/1).
:- export(restore_menu_config/1).
:- impl_defined(restore_menu_config/1).
:- export(set_last_file/1).
:- impl_defined(set_last_file/1).
:- export(again/0).
:- impl_defined(again/0).
:- export(auto_analyze/2).
:- impl_defined(auto_analyze/2).
:- export(auto_check_assert/2).
:- impl_defined(auto_check_assert/2).
:- export(auto_optimize/2).
:- impl_defined(auto_optimize/2).
:- export(set_menu_flag/3).
:- impl_defined(set_menu_flag/3).
:- export(get_menu_flag/3).
:- impl_defined(get_menu_flag/3).
:- export(set_menu_flag/3).
:- impl_defined(set_menu_flag/3).
:- endif.

% -----------------------------------------------------------------------
% TODO: optional
% (optional: types)

:- if(defined(with_fullpp)).
:- reexport(typeslib(typeslib), [show_types/0]).
:- doc(hide,show_types/0).
:- endif.

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(p_unit/itf_db), [current_itf/3, preloaded_module/2]).
:- use_module(ciaopp(p_unit/aux_filenames), [is_library/1]).
:- use_module(engine(runtime_control), [module_split/3]).

% TODO: move somewhere else?
% Provide hook definitions for typeslib
:- include(typeslib(typeslib_hooks)).

% (hook)
typeslib_flag(typedefs_simp) :- current_pp_flag(typedefs_simp, yes).
typeslib_flag(use_deftypes) :- current_pp_flag(types, deftypes).
typeslib_flag(use_defined_types_filters) :- \+ current_pp_flag(type_precision,defined). % TODO: why? only when use_deftypes
typeslib_flag(type_output_all) :- current_pp_flag(type_output, all). % \+ current_pp_flag(type_output, defined).

% (hook)
typeslib_is_user_type(T) :-
    module_split(T,M,_),
    current_itf(defines_module,M,Base), !, % TODO: dangling choice points?
    \+ is_library(Base).

% (hook)
typeslib_interesting_type(T, Mode) :-
    atom(T),
    module_split(T,M,_),
    interesting_module(M,Mode).

interesting_module(M,build) :-
    preloaded_module(M,_Base),!,fail.
interesting_module(basic_props,_).
interesting_module(arithmetic,_).
interesting_module(assertions_props,_).
interesting_module(term_typing,_).
interesting_module(Module,_) :- 
    current_itf(defines_module,Module,Base), !, % TODO: dangling choice points?
    \+ is_library(Base).

% -----------------------------------------------------------------------
% TODO: optional?

:- if(defined(with_fullpp)).
:- reexport(ciaopp(p_unit/p_asr), [show_asr/1]).
:- doc(hide,show_asr/1).
:- endif.

% ---------------------------------------------------------------------------
% Preprocess flags

:- reexport(ciaopp(preprocess_flags),
    [ current_pp_flag/2,
      set_pp_flag/2,
      push_pp_flag/2,
      pop_pp_flag/1,
      pp_flag/1,
      flag_value/1,
      valid_flag_value/2]).
:- doc(doinclude,current_pp_flag/2).
:- doc(doinclude,set_pp_flag/2).
:- doc(doinclude,pp_flag/1).
% TODO: temporarily, LPdoc is not able to include them:
:- doc(pp_flag/1,"Valid flags:  @include{preprocess_flags.lpdoc}").
%
:- doc(doinclude,push_pp_flag/2).
:- doc(doinclude,pop_pp_flag/1).
:- doc(doinclude,flag_value/1).
:- doc(doinclude,valid_flag_value/2).
:- doc(hide,dump_flags/1).

%% From :- reexport(ciaopp(plai/trace_fixp)).
:- doc(hide,trace_fixp/1).

% ------------------------------------------------------------------------
:- doc(section, "Initialization checks").

:- use_module(library(messages), [error_message/2]).
:- use_module(library(system), [file_exists/2]).

% TODO: ad-hoc, this should be in the flag definition
flag_is_targetdir(asr_dir).
flag_is_targetdir(tmp_dir).

:- initialization(ciaopp_init).
ciaopp_init :-
    init_check_flags.

:- pred init_check_flags # "Check that the current default flag values
   are valid. See @pred{check_flag/2} and @pred{check_targetdir/2}.".

init_check_flags :-
    pp_flag(F),
    current_pp_flag(F, V),
    check_flag(F, V),
    ( flag_is_targetdir(F) ->
        check_targetdir(F, V)
    ; true
    ),
    fail.
init_check_flags.

check_flag(F, V) :-
    ( valid_flag_value(F, V) ->
        true
    ; error_message( 
        "INTERNAL ERROR: The flag ~w has a value ~w which is not correct",
        [F,V]),
      fail
    ).

check_targetdir(Flag, Dir) :-
    ( Dir == source -> true % TODO: ad-hoc...
    ; file_exists(Dir, 7) ->
        true
    ; error_message("INTERNAL ERROR: the directory ~w is not "||
                    "accesible (flag: ~w)" , [Dir,Flag]),
      fail
    ).
