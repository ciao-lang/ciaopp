:- module(ciaoppcl, [main/1], [assertions, datafacts]).

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

:- use_module(engine(io_basic)).
:- use_module(library(format), [format/3]).
:- use_module(ciaopp_batch(ciaopp_worker)).

main(Args) :-
    catch(main_(Args), E, (handle_ciaopp_error(E), halt(1))).

main_(['--worker', ID]) :- % Worker mode (internal for ciaopp-batch)
    !,
    ciaopp_worker:start_worker(ID).
main_(Args) :-
    % TODO: use get_opts/1 like in lpdoc
    parse_opts(Args, Cmd, Flags),
    !,
    ciaopp_cmd(Cmd, Flags).
main_(_Args) :-
    short_usage_message(Text),
    format(user_error,Text,[]).

% ===========================================================================
:- doc(section, "Help").

ciaopp_banner :-
    display('Ciao Preprocessor (integrated Alpha version)' ), nl,
    display(' | This is an alpha distribution, meant only for testing. Please do let us '), nl,
    display(' | know at ciaopp-bug<at>clip.dia.fi.upm.es any problems you may have.'), nl, nl.

short_usage_message(
"Use 'ciaopp --help' for help.
").

usage_message(
"Usage 1: (batch mode)
    ciaopp [-o OutFile] Option Filename [FlagsValues]

  Where:
    -o OutFile  after processing Filename, the resulting source 
            code is written to OutFile.  If this option is
            omitted, the output is written to a file
            automatically named depending on the actions
            performed.
    -op <Suffix>   Use Suffix as the optional input code suffix 

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

% ---------------------------------------------------------------------------
:- doc(section, "Parse command line arguments").

:- use_module(library(terms), [atom_concat/2]).

:- data output_file/1.

parse_opts([], Cmd, Flags) :- !,
    ( var(Cmd) -> % default
        Cmd = toplevel([])
    ; true
    ),
    Flags = [].
% commands
parse_opts(['-h'|_], Cmd, Flags) :- !,
    Cmd = help,
    Flags = [].
parse_opts(['--help'|_], Cmd, Flags) :- !,
    Cmd = help,
    Flags = [].
parse_opts(['-T'|ToplevelOpts], Cmd, Flags) :- !,
    Cmd = toplevel(ToplevelOpts), % TODO: make behavior consistent with other ciao tools
    Flags = [].
parse_opts(['-Q', File|Opts], Cmd, Flags) :- !,
    Cmd = customize_and_preprocess(File),
    parse_opts(Opts, Cmd, Flags).
parse_opts(['-A', File|Opts], Cmd, Flags) :- !,
    Cmd = ana(File),
    parse_opts(Opts, Cmd, Flags).
parse_opts(['-V', File|Opts], Cmd, Flags) :- !,
    Cmd = check(File),
    parse_opts(Opts, Cmd, Flags).
parse_opts(['-O', File|Opts], Cmd, Flags) :- !,
    Cmd = opt(File),
    parse_opts(Opts, Cmd, Flags).
parse_opts(['-U', Menu, File|Opts], Cmd, Flags) :- !,
    Cmd = restore_menu(Menu,File),
    parse_opts(Opts, Cmd, Flags).
% input opts
parse_opts(['-op', Suff|Opts], Cmd, Flags) :- !,
    opt_suffix(_, Suff),
    parse_opts(Opts, Cmd, Flags).
% output
parse_opts(['-o', File|Opts], Cmd, Flags) :- !,
    retractall_fact(output_file(_)),
    asserta_fact(output_file(File)),
    parse_opts(Opts, Cmd, Flags).
% parse flags
parse_opts(['-f', FV|Opts], Cmd, Flags) :- is_flag_value(FV, F, V), !,
    Flags = [f(F,V)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
parse_opts([FV|Opts], Cmd, Flags) :- is_flag_value_f(FV, F, V), !,
    Flags = [f(F,V)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
parse_opts(['-p', FV|Opts], Cmd, Flags) :- is_flag_value(FV, F, V), !,
    Flags = [p(F,V)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
parse_opts([FV|Opts], Cmd, Flags) :- is_flag_value_p(FV, F, V), !,
    Flags = [p(F,V)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
% unknown argument
parse_opts([F|_Opts], _Cmd, _Flags) :-
    display('Unrecognized option '),
    displayq(F), nl,
    fail.

is_flag_value(FV, F, V) :- atom_concat([F, '=', V], FV).

is_flag_value_f(FV, F, V) :- atom_concat(['-f', F, '=', V], FV).

is_flag_value_p(FV, F, V) :- atom_concat(['-p', F, '=', V], FV).

% ===========================================================================
:- doc(section, "Commands").

:- use_module(library(menu/menu_generator), []).
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
:- use_module(library(toplevel), [toplevel/1]).
:- use_module(library(compiler/c_itf), [opt_suffix/2]).

ciaopp_cmd(help, _Flags) :- !,
    usage_message(Text),
    format(user_error,Text,[]).
ciaopp_cmd(toplevel(Opts), _Flags) :- !,
    ciaopp_toplevel(Opts).
ciaopp_cmd(customize_and_preprocess(File), _Flags) :- !,
    customize_and_preprocess(File).
ciaopp_cmd(restore_menu(Menu,File), _Flags) :- !,
    display('Restoring Menu Configuration '),
    display(Menu), nl,
    restore_menu_config(Menu),
    set_last_file(File),
    again.
ciaopp_cmd(ana(File), Flags) :- !,
    get_output_filename(OFile),
    set_flags(Flags, ana),
    auto_analyze(File, OFile).
ciaopp_cmd(check(File), Flags) :- !,
    get_output_filename(OFile),
    set_flags(Flags, check),
    auto_check_assert(File, OFile).
ciaopp_cmd(opt(File), Flags) :- !,
    get_output_filename(OFile),
    set_flags(Flags, opt),
    auto_optimize(File, OFile).

% TODO: use optional output(F) instead (so that no output/1 means default)
get_output_filename(X) :- output_file(X), !.
get_output_filename(_).

% ---------------------------------------------------------------------------
% Set flags (depends on command)

set_flags([], _) :- !.
set_flags([f(F,V)|Flags], Cmd0) :-
    set_menu_flag_option(Cmd0, F, V),
    !,
    set_flags(Flags, Cmd0).
set_flags([p(F,V)|Flags], Cmd0) :-
    set_pp_flag(F, V),
    !,
    set_flags(Flags, Cmd0).
set_flags([F|Flags], Cmd0) :-
    display('Unrecognized flag '),
    displayq(F),
    nl, % TODO: exit?
    set_flags(Flags, Cmd0).

set_menu_flag_option(opt, inter_optimize, V) :- !,
    set_menu_flag(opt, inter_optimize, V).
set_menu_flag_option(opt, F, V) :- !,
    get_menu_flag(opt, inter_optimize, P),
    set_menu_flag_option(P, F, V).
set_menu_flag_option(A, F, V) :-
    set_menu_flag(A, F, V).

% ---------------------------------------------------------------------------
% Toplevel

:- use_module(library(lists), [member/2]).
:- use_module(library(system), [file_exists/1]).
:- use_module(engine(runtime_control), [set_prolog_flag/2]).

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
        % '-e', 'use_module(typeslib(typeslib), [])',
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

% ===========================================================================
:- doc(section, "Handle errors").

:- use_module(library(errhandle), [default_error_message/1]).
%:- use_module(library(messages), [error_message/2]).

% handle_ciaopp_error(ciaopp_error(Format, Args)) :- !, % TODO: use
%       error_message(Format, Args).
handle_ciaopp_error(E) :-
    default_error_message(E),
    fail. % TODO: fail, abort or true?

