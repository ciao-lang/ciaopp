:- module(ciaoppcl, [main/1], [assertions, datafacts]).

:- use_module(engine(io_basic)).
:- use_module(library(lists), [member/2]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(library(menu/menu_generator), []).
:- use_module(library(toplevel), [toplevel/1]).
:- use_module(library(format), [format/3]).
:- use_module(library(system), [file_exists/1]).
:- use_module(engine(runtime_control), [set_prolog_flag/2]).

:- use_module(ciaopp(ciaopp), [
	set_last_file/1,
	again/0,
	auto_analyze/2,
	auto_check_assert/2,
	auto_optimize/2,
	%
	set_pp_flag/2,
	%
	customize_and_preprocess/1,
	restore_menu_config/1,
	set_menu_flag/3,
	get_menu_flag/3]).

:- doc(title,"The CiaoPP command-line interface").
:- doc(author, "The Ciao Development Team").
:- doc(module, 
"This is the top-level and command-line interface to CiaoPP. Please
look at @lib{ciaopp} documentation for top-level usage information.
The command-line interface allows the use of the system in batch
mode, using arguments for setting preprocessor flags and performing
actions.

@section{Command-line options}

This interface can be used by means of the following command-line
options:

@begin{verbatim}
@includefact{usage_message/1}
@end{verbatim}

@section{Description of the execution examples}

@begin{itemize}

@item The following command will prompt the user with the options needed to
preprocess @tt{myfile.pl}:

@tt{ciaopp -Q myfile.pl}

@item If we want to verify the assertions of @tt{myfile.pl}, and generate
the resulting source code that will the new status of the assertions
(either @tt{checked}, if CiaoPP has proved that the assertion holds,
or @tt{false} if it has falsified the assertion), the command line is
as follows:

@tt{ciaopp -o myfile_checked.pl -V myfile.pl}

@item To optimize @tt{myfile.pl}, and write the optimize code in a file
named automatically (e.g., @tt{myfile_pd_codegen_af_co.pl}), the
following command line must be used:

@tt{ciaopp -O myfile.pl}

@item If the default flag values need to be changed, the @tt{-f} option can
be used. For example, in order to analyze @tt{myfile.pl} to change the
types analysis domain to @tt{terms} instead of the default one, and
the mode-aliasing domain to @tt{pd}, the command line to use should
be:

@tt{ciaopp -A myfile.pl -ftypes=terms -f modes=pd}

@item Finally, the following command line can be used to start a top-level
CiaoPP shell (this is the default behavior):

@tt{ciaopp -T}

@end{itemize}
").


:- data output_file/1.

get_output_filename(X) :-
	output_file(X),
	!.
get_output_filename(_).

main(Args) :- process_args(Args).

process_args([]) :- !,
	ciaopp_toplevel([]).
process_args(['-T'|ToplevelOpts]) :- !,
	ciaopp_toplevel(ToplevelOpts).
process_args(['-Q', File]) :- !,
	customize_and_preprocess(File).
process_args(['-A', File | Opts]) :- !,
	process_args_opt(Opts, ana, File).

process_args(['-V', File | Opts]) :- !,
	process_args_opt(Opts, check, File).

process_args(['-O', File | Opts]) :- !,
	process_args_opt(Opts, opt, File).

process_args(['-o', File | More]) :- !,
	retractall_fact(output_file(_)),
	asserta_fact(output_file(File)),
	process_args(More).

process_args(['-U', Menu, File]) :- !,
	display('Restoring Menu Configuration '),
	display(Menu), nl,
	restore_menu_config(Menu),
	set_last_file(File),
	again.
process_args(_) :-
	usage_message(Text),
	format(user_error,Text,[]).

ciaopp_banner :-
	display('Ciao Preprocessor (integrated Alpha version)' ), nl,
	display(' | This is an alpha distribution, meant only for testing. Please do let us '), nl,
	display(' | know at ciaopp-bug<at>clip.dia.fi.upm.es any problems you may have.'), nl, nl.

usage_message(
"Usage 1: (batch mode)
	ciaopp [-o OutFile] Option Filename [FlagsValues]

  Where:
    -o OutFile  after processing Filename, the resulting source 
                code is written to OutFile.  If this option is
                omitted, the output is written to a file
                automatically named depending on the actions
                performed.

    Option must be one of the following:
    -Q          runs the interactive (text-based) menu for
                preprocessing Filename.
    -A          analyzes Filename with the default options
                except the flag values set with -f at the 
                command line.
    -O          optimizes Filename with the default options
                except the flag values set with -f at the 
                command line.
    -V          verifies the assertions of Filename with
                the default options except the flag values set 
                with -f at the command line.
    -U Config   processes Filename with the
                options set in the CiaoPP configuration Config.

    FlagsValues is a list of options -fFlagName=FlagValue
    separated by blank spaces, where FlagName is a valid
    CiaoPP flag name.  This list is optional, and does not need
    to include all flags applicable to the action to be performed:
    the flags not included in this list will be assumed to take
    their default value.  Examples:

    -flocal_control=on   where local_control is expected to be
                         a CiaoPP flag;
    -f local_control=on  same as above, with additional blank spaces

    Internal flags can also be changed using -pIntFlagName=Value.

Usage 2: (top-level mode)
       ciaopp -T <toplevel-opts>

  -T option starts a CiaoPP top-level shell (using <toplevel-opts> as
  options for the toplevel).  Any of the predicates described in the
  Section CiaoPP User Menu Interface of the CiaoPP Reference Manual
  can be used in this top-level.

Execution Examples:

  ciaopp -Q myfile.pl
  ciaopp -o myfile_checked.pl -V myfile.pl
  ciaopp -O myfile.pl
  ciaopp -A myfile.pl -ftypes=terms -f modes=pd
  ciaopp -T
").

process_args_opt([], ana, File) :-
	get_output_filename(OFile),
	auto_analyze(File, OFile).
process_args_opt([], check, File) :-
	get_output_filename(OFile),
	auto_check_assert(File, OFile).
process_args_opt([], opt, File) :-
	get_output_filename(OFile),
	auto_optimize(File, OFile).
process_args_opt(['-o', OFile|More], A, File) :-
	retractall_fact(output_file(_)),
	asserta_fact(output_file(OFile)),
	process_args_opt(More, A, File).
process_args_opt(['-f', FV|Opts], A, File) :-
	is_flag_value(FV, F, V),
	set_menu_flag_option(A, F, V),
	!,
	process_args_opt(Opts, A, File).
process_args_opt([FV|Opts], A, File) :-
	is_flag_value_f(FV, F, V),
	set_menu_flag_option(A, F, V),
	!,
	process_args_opt(Opts, A, File).
process_args_opt(['-p', FV|Opts], A, File) :-
	is_flag_value(FV, F, V),
	set_pp_flag(F, V),
	!,
	process_args_opt(Opts, A, File).
process_args_opt([PV|Opts], A, File) :-
	is_flag_value_p(PV, P, V),
	set_pp_flag(P, V),
	!,
	process_args_opt(Opts, A, File).
process_args_opt([F|Opts], A, File) :-
	display('Unrecognized option '),
	displayq(F),
	nl,
	process_args_opt(Opts, A, File).

set_menu_flag_option(opt, inter_optimize, V) :- !,
	set_menu_flag(opt, inter_optimize, V).
set_menu_flag_option(opt, F, V) :- !,
	get_menu_flag(opt, inter_optimize, P),
	set_menu_flag_option(P, F, V).
set_menu_flag_option(A, F, V) :-
	set_menu_flag(A, F, V).

is_flag_value(FV, F, V) :-
	atom_concat([F, '=', V], FV).

is_flag_value_f(FV, F, V) :-
	atom_concat(['-f', F, '=', V], FV).

is_flag_value_p(PV, P, V) :-
	atom_concat(['-p', P, '=', V], PV).

ciaopp_toplevel(Opts2) :-
	set_prolog_flag(quiet, warning),
	Opts = ['-p', 'ciaopp ?- '|Opts0], 
	CiaoRC = '~/.ciaorc',
	( \+ member('-f', Opts2), file_exists(CiaoRC) ->
	    Opts0 = ['-l', '~/.ciaorc'|Opts1]
	; Opts0 = Opts1
	),
	Opts1 = [
            % TODO: due to a bug in c_itf:use_mod_common/4 we must
	    %   enforce loading the .itf of the following reexported modules
            %   before ciaopp(ciaopp) is loaded
            '-e', 'use_module(ciaopp(frontend_driver), [])',
            '-e', 'use_module(ciaopp(analyze_driver), [])',
            '-e', 'use_module(ciaopp(transform_driver), [])',
	    '-e', 'use_module(ciaopp(preprocess_flags), [])',
	    '-e', 'use_module(auto_interface(auto_interface), [])',
	    '-e', 'use_module(auto_interface(auto_help), [])',
	    '-e', 'use_module(typeslib(typeslib), [])',
	    '-e', 'use_module(ciaopp(p_unit/p_asr), [])',
 	    '-u', ciaopp(ciaopp),
	    %
	    '-u', engine(runtime_control),
	    '-e', 'set_prolog_flag(quiet, off)'
          |Opts2],
	( member('-q', Opts2) -> true
	; ciaopp_banner
	),
	toplevel:toplevel(Opts).
