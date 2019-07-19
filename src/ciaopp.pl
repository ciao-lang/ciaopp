:- module(ciaopp, [], [assertions, ciaopp(ciaopp_options)]).

:- doc(title,"The CiaoPP low-level interface").
:- doc(author, "The Ciao Development Team").

% ---------------------------------------------------------------------------
% NOTE: Customize CiaoPP build modifiying the declarations at:
%
%                      ciaopp_options.pl
%
% ---------------------------------------------------------------------------

:- doc(module, "This module includes low-level primitives for
   interacting with CiaoPP.

@section{Available abstract domains}
The available domains are:
@include{analysis.lpdoc}

@section{More flags related with program analysis}

In this section the flags related with program analysis are explained in
some detail. In particular, special attention is given to inter-modular
program analysis and partial deduction (performed in CiaoPP during 
analysis).

@include{analysis_more.lpdoc}
").

% ---------------------------------------------------------------------------
% TODO: temporarily repeated here, because LPdoc is not able to include them
% TODO: (old) these onea [transformation/1], however, should be here on their own right, 
%   not in driver.pl (which goes to the internals):

%:- multifile analysis/1.
:- impl_defined(analysis/1).
:- prop analysis(Analysis)
	# "@var{Analysis} is a valid analysis identifier.".

:- doc(analysis/1,"Analyses can be integrated in CiaoPP in an ad-hoc
   way (see the Internals manual), in which the CiaoPP menu would not
   be aware of them.  The current analyses supported in the menu are
   in @ref{Available abstract domains}.").

%:- multifile transformation/1.
:- impl_defined(transformation/1).
:- prop transformation(Transformation)
	# "@var{Transformation} is a valid transformation identifier.".

:- doc(transformation/1,"Transformations can be integrated in CiaoPP
   in an ad-hoc way (see the Internals manual), in which the CiaoPP
   menu would not be aware of them.  The current transformations
   supported in the menu are:

   @include{transformation.lpdoc}").

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
% TODO: optional?

:- if(defined(with_fullpp)).
:- reexport(auto_interface(auto_help)).
:- doc(hide,help/1).
:- doc(doinclude,help/0).
:- pred help/0.
help.
:- endif.

% -----------------------------------------------------------------------
% TODO: optional
% (optional: types)

:- if(defined(with_fullpp)).
:- reexport(typeslib(typeslib), [show_types/0]).
:- doc(hide,show_types/0).
:- endif.

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
