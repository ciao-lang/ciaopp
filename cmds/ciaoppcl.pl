:- module(ciaoppcl, [main/1], [assertions]).

:- compilation_fact(unified_menu).

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
:- use_module(ciaopp_actmod, [main/1]).
:- use_module(ciaopp(frontend_driver), [cache_and_preload_lib_sources/0]).
:- use_module(library(messages)).

main(Args) :-
    catch(main_(Args), E, handle_ciaopp_error(E)).

handle_ciaopp_error(E) :-
    ciaopp_error_message(E),
    halt(1).

main_(['--worker', ID]) :- % Worker mode (internal for ciaopp-batch)
    !,
    ciaopp_worker:start_worker(ID).
main_(['--actmod'|Args]) :- % Actmod mode (see 'service' entry in Manifest)
    !,
    ciaopp_actmod:main(Args).
main_(['--gen-lib-cache']) :- !,
    cache_and_preload_lib_sources.
main_(Args) :-
    % TODO: use get_opts/1 like in lpdoc
    parse_opts(Args, Cmd, Flags),
    ( var(Cmd) -> Cmd = toplevel([]) ; true ), % (default)
    !,
    ciaopp_cmd(Cmd, Flags).
main_(_Args) :-
    short_usage_message.

% ===========================================================================
:- doc(section, "Help").

ciaopp_banner.
% ciaopp_banner :-
%     display('CiaoPP Program Processor (integrated Alpha version)' ), nl,
%     display(' | This is an alpha distribution, meant only for testing. Please do let us '), nl,
%     display(' | know at ciaopp-bug<at>clip.dia.fi.upm.es any problems you may have.'), nl, nl.

:- export(short_usage_message/0).
short_usage_message :-
    display(user_error, 'Use \'ciaopp --help\' for help.'), nl(user_error).

usage_message(
"Usage 1: (batch mode)
    ciaopp [OPTIONS] Action Filename [FlagsValues]

  Where:
    -o <OutFile>
            after processing Filename, the resulting source 
            code is written to OutFile.  If this option is
            omitted, the output is written to a file
            automatically named depending on the actions
            performed.
    -op <Suffix>
            Use Suffix as the optional input code suffix 

    --cwd Dir
            Switch to the selected directory
    --timeout Timeout 
            Execute with a timeout limit (ms).
            Default is 0 (no timeout).

    Action must be one of the following:
    -Q      runs the interactive (text-based) menu for
            preprocessing Filename.
    -A      analyzes Filename with the default options
            except the flag values set with -f at the 
            command line.
    -O      optimizes Filename with the default options
            except the flag values set with -f at the 
            command line.
    -V      verifies the assertions of Filename with
            the default options except the flag values set 
            with -f at the command line.

    -U <Config>
            processes Filename with the options set in the
            configuration Config.

    FlagsValues is a list of options -fFlagName=FlagValue
    separated by blank spaces, where FlagName is a valid
    CiaoPP flag name.  This list is optional, and does not need
    to include all flags applicable to the action to be performed:
    the flags not included in this list will be assumed to take
    their default value.  Examples:

    -flocal_control=on
            where local_control is expected to be
            a CiaoPP flag;
    -f local_control=on 
            same as above, with additional blank spaces

    Internal flags can also be changed using -pIntFlagName=Value.

Usage 2: (top-level mode)
    ciaopp -T <toplevel-opts>

    -T     starts a CiaoPP top-level shell (using <toplevel-opts> as
           options for the toplevel).  Any of the predicates described
           in the Section 'CiaoPP User Menu Interface' of the CiaoPP
           Reference Manual can be used in this top-level.

Usage 3: cache libraries
    ciaopp --gen-lib-cache

    Preloads libraries for faster load in CiaoPP toplevel

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
:- use_module(library(compiler/c_itf), [opt_suffix/2]).

:- export(parse_opts/3).
parse_opts([], _Cmd, Flags) :- !,
    Flags = [].
% commands
parse_opts(['-h'|_], Cmd, Flags) :- !,
    Cmd = help,
    Flags = [].
parse_opts(['--help'|_], Cmd, Flags) :- !,
    Cmd = help,
    Flags = [].
% (unavailable as actmod)
parse_opts(['-T'|ToplevelOpts], Cmd, Flags) :- !,
    Cmd = toplevel(ToplevelOpts), % TODO: make behavior consistent with other ciao tools
    Flags = [].
% (unavailable as actmod)
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
% (unavailable as actmod)
parse_opts(['-U', Menu, File|Opts], Cmd, Flags) :- !,
    Cmd = restore_menu(Menu,File),
    parse_opts(Opts, Cmd, Flags).
% opt suffix
parse_opts(['-op', Suff|Opts], Cmd, Flags) :- !,
    Flags = [opt_suffix(Suff)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
% current working directory (absolute path)
parse_opts(['--cwd', AbsPath|Opts], Cmd, Flags) :- !,
    Flags = [cwd(AbsPath)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
% optional timeout
parse_opts(['--timeout', T|Opts], Cmd, Flags) :- !,
    atom_codes(T, TCs),
    number_codes(Tn, TCs),
    Flags = [timeout(Tn)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
% output
parse_opts(['-o', File|Opts], Cmd, Flags) :- !,
    Flags = [output_file(File)|Flags0],
    parse_opts(Opts, Cmd, Flags0).
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

% (options are passed through restore_menu_flags_list/1 pred)
:- use_module(library(menu/menu_generator), [
    % TODO: at least these operations should be in a separate module (menu_db?)
    get_menu_flags/1,
    exists_menu_flag/2,
    restore_menu_flags_list/1]).
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
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2,valid_flag_values/2]).
:- use_module(library(system), [working_directory/2]).
:- use_module(library(timeout), [call_with_time_limit/3]). % TODO: experimental!
:- use_module(library(port_reify), [once_port_reify/2, port_call/1]).

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
ciaopp_cmd(Cmd, Flags) :-
    ciaopp_run(Cmd, Flags).

:- export(ciaopp_run/2).
ciaopp_run(Cmd, Flags0) :-
    cmd_alias(Cmd,Cmd0,File,Flags0,Flags, Stop),
    Stop = no, !,
    ( member(output_file(OFile), Flags) -> true
    ; true % OFile unbound
    ),
    ( member(timeout(Timeout), Flags) -> true
    ; Timeout = 0 % No timeout
    ),
    get_menu_flags(OldMenuFlags),
    set_flags(Flags, Cmd0, [], OldFlags, FlagErrs), % TODO: add a way to reset flags
    ( var(FlagErrs) ->
        once_port_reify(ciaopp_run_with_time_limit(Timeout, Cmd0, File, OFile), Port)
    ; once_port_reify(throw(ciaopp_error(flag_errs)), Port)
    ),
    restore_flags(OldFlags),
    restore_menu_flags_list(OldMenuFlags),
    port_call(Port).
ciaopp_run(_, _).

% Expand command into CmdRun and flags
cmd_alias(opt(File), opt, File, Flags, Flags, no).
cmd_alias(ana(File), ana, File, Flags0, Flags, Stop) :-
    member(f(ctcheck,on), Flags0), !,
    cmd_alias(check(File), ana, File, Flags0, Flags, Stop).
cmd_alias(ana(File), ana, File, Flags0, Flags, no) :-
    ( member(f(dom_sel,V),Flags0) ->
        ( V = auto ->
            warning_message("Automatic domain selection is not valid if only analyzing. The default domains will be run.")
            % Stop = yes ?
        ;   true ),
        Flags1 = Flags0
    ;   Flags1 = [f(dom_sel,manual)|Flags0]
    ),
    ( member(f(ctcheck,_), Flags0) -> Flags=Flags1 ; Flags = [f(ctcheck,off)|Flags1]).
:- if(defined(unified_menu)).
cmd_alias(check(File), ana, File, Fs0, Flags, Stop) :-
    ( member(f(ctcheck,off), Fs0) ->
        warning_message("-V action is incompatible with ctcheck=off"),
        Stop = yes
    ; true
    ),
    ( member(f(output,_), Fs0) -> Fs1 = Fs0 ; Fs1 = [f(output,off)|Fs0] ),
    auto_include_dom_sel(Fs1, Flags),
    ( var(Stop) -> Stop = no ; true ).
:- else.
cmd_alias(check(File), check, File, Flags, Flags, no).
:- endif.

auto_include_dom_sel(Flags0, Flags) :-
    member(f(dom_sel,_), Flags0), !, % if defined by the user, do nothing
    Flags = Flags0.
auto_include_dom_sel(Flags0, Flags) :-
    valid_flag_values(inter_ana, sublist2(_,AnaKinds)),
    ( (member(Ana,AnaKinds), member(f(Ana,_),Flags0)) ->
        Flags = [f(dom_sel,manual)|Flags0]
    ;
        Flags = Flags0
    ).

ciaopp_run_with_time_limit(0, Cmd0, File, OFile) :- !,
    auto_run(Cmd0, File, OFile).
ciaopp_run_with_time_limit(Timeout, Cmd0, File, OFile) :-
    call_with_time_limit(Timeout, auto_run(Cmd0, File, OFile), throw(ciaopp_error(timeout))).

auto_run(Cmd0, File, OFile) :-
    ( Cmd0 = ana -> auto_analyze(File, OFile)
    ; Cmd0 = check -> auto_check_assert(File, OFile) % TODO: Needed? (JFMC)
    ; Cmd0 = opt -> auto_optimize(File, OFile)
    ).

% Set context and save previous state in OldFlags. Unify FlagErrs on errors
set_flags([], _Cmd0, OldFlags, OldFlags, _FlagErrs).
set_flags([Flag|Flags], Cmd0, OldFlags0, OldFlags, FlagErrs) :-
    set_flag(Flag, Cmd0, OldFlags0, OldFlags1, FlagErrs),
    set_flags(Flags, Cmd0, OldFlags1, OldFlags, FlagErrs).

set_flag(f(F,V), Cmd0, OldFlags0, OldFlags, FlagErrs) :- !,
    ( (exists_menu_flag(Cmd0, F) ; F = menu_config_name ; F = menu_last_config) ->
        set_menu_flag_option(Cmd0, F, V)
    ; error_message("Unrecognized flag ~q",[F]), FlagErrs = yes
    ),
    OldFlags = OldFlags0.
set_flag(opt_suffix(Suff), _Cmd0, OldFlags0, OldFlags, _FlagErrs) :- !,
    opt_suffix(OldSuff,Suff),
    OldFlags = [opt_suffix(OldSuff)|OldFlags0].
set_flag(cwd(AbsPath), _Cmd0, OldFlags0, OldFlags, _FlagErrs) :- !,
    working_directory(OldAbsPath,AbsPath),
    OldFlags = [cwd(OldAbsPath)|OldFlags0].
set_flag(p(F,V), _Cmd0, OldFlags0, OldFlags, _FlagErrs) :- !,
    ( current_pp_flag(F, OldV) ->
        set_pp_flag(F, V),
        OldFlags = [p(F,OldV)|OldFlags0]
    ; OldFlags = OldFlags0
    ).
set_flag(_Flag, _Cmd0, OldFlags, OldFlags, _FlagErrs).

% Restore saved context
restore_flags([]).
restore_flags([Flag|Flags]) :-
    restore_flag(Flag),
    restore_flags(Flags).

restore_flag(p(F,OldV)) :- !,
    set_pp_flag(F,OldV).
restore_flag(opt_suffix(Suff)) :- !,
    opt_suffix(_,Suff).
restore_flag(cwd(Dir)) :- !,
    working_directory(_,Dir).
restore_flag(_).

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
:- use_module(library(toplevel), [toplevel/1]).

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
        '-e', 'use_module(ciaopp(auto_interface), [])',
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
:- doc(section, "CiaoPP error messages").

:- use_module(library(errhandle), [default_error_message/1]).
%:- use_module(library(messages), [error_message/2]).

% ciaopp_error_message(ciaopp_error_msg(Format, Args)) :- !, % TODO: use?
%       error_message(Format, Args).
ciaopp_error_message(ciaopp_error(flag_errs)) :- !. % (message already shown)
ciaopp_error_message(ciaopp_error(timeout)) :- !,
    display(user_error, '{ERROR: timeout}'), nl(user_error).
ciaopp_error_message(E) :-
    default_error_message(E).
