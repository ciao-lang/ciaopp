:- module(ciaoppcl, [main/1], [assertions]).

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
:- use_module(ciaopp(frontend_driver), [gen_and_load_libcache/0]).
:- use_module(ciaopp(ciaoppcl_common), [
    parse_opts/3, ciaopp_run/2,
    ciaopp_error_message/1
]).
:- use_module(library(messages)).

main(['--worker', ID]) :- !, % Worker mode (internal for ciaopp-batch)
    ciaopp_worker:start_worker(ID).
main(['--actmod'|Args]) :- !, % Actmod mode (see 'service' entry in Manifest)
    ciaopp_actmod:main(Args).
main(Args) :-
    catch(main_(Args), E, handle_ciaopp_error(E)).

handle_ciaopp_error(E) :-
    ciaopp_error_message(E),
    halt(1).

main_(['--gen-lib-cache']) :- !,
    gen_and_load_libcache.
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

% ===========================================================================
:- doc(section, "Commands").

:- use_module(ciaopp(ciaopp), [
    set_last_file/1,
    again/0,
    customize_and_preprocess/1,
    restore_menu_config/1
]).

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
        '-u', ciaopp(ciaopp),
        %
        '-u', engine(runtime_control),
        '-e', 'set_prolog_flag(quiet, off)'
      |Opts2],
    ( member('-q', Opts2) -> true
    ; ciaopp_banner
    ),
    toplevel:toplevel(Opts).
