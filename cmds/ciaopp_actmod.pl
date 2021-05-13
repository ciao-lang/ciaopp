:- module(ciaopp_actmod, [], [assertions, fsyntax, dcg, actmod, datafacts]).

:- doc(title, "CiaoPP Actmod").

:- doc(module, "This is the CiaoPP active module").

:- doc(usage, "This module needs to be compiled as an active module
   (see @tt{Manifest.pl} rules). Use @tt{ciaopp-client.bash} as
   client.").

% NOTE: Instructions to rebuild and reload:
%   ciao build --bin ciaopp; ciao-serve stop; rm -f /tmp/ciaopp_actmod.pid
%
% NOTE: Start 'build/libexec/ciaopp_actmod' manually to debug this module.
%   (ciao-serve will not show the output of daemons)
%
% TODO: removing the .pid file is only needed to recover from failed daemons

:- use_module(library(actmod_http), []). % (include actmod_http)
:- use_module(ciaopp_client, _, [active]). % (for set_buf/2)

:- dist_node.

:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(lists)).
:- use_module(library(system)).
%
:- use_module(library(io_port_reify), [io_once_port_reify/4]).
:- use_module(library(port_reify), [port_call/1]).
:- use_module(library(timeout), [call_with_time_limit/3]). % TODO: experimental!
:- use_module(library(system_extra), [del_file_nofail/1]).
:- use_module(library(pathnames), [path_concat/3, path_split/3]).
:- use_module(library(pillow/json)).

% (options are passed through restore_menu_flags_list/1 pred)
:- use_module(ciaopp(ciaopp), [set_last_file/1, again/0]).
% ----- (loaded dynamically in ciaoppcl)
:- use_module(ciaopp(p_unit/p_asr), []).
:- use_module(ciaopp(analyze_driver), []).
:- use_module(ciaopp(transform_driver), []).
:- use_module(ciaopp(auto_interface), []). % TODO: needed?

% ---------------------------------------------------------------------------
% Ensure that libraries are cached

:- use_module(ciaopp(frontend_driver), [cache_and_preload_lib_sources/0]).

:- data cache_enabled/0.

ensure_cache_enabled :-
    ( cache_enabled -> true
    ; cache_and_preload_lib_sources,
      assertz_fact(cache_enabled)
    ).

% ---------------------------------------------------------------------------
% TODO: Work in progress, for ciaopp-client.sh

:- suspendable(cmdrun(json)).
cmdrun(Args) :-
    io_once_port_reify(cmdrun_(Args), Port, OutString, ErrString),
    Result = ~append(OutString,ErrString),
    port_call(Port),
    set_buf('console', Result).

cmdrun_(Args0) :-
    get_atmlist(Args0, Args), !,
    ( parse_opts(Args, Cmd, Flags),
      ciaopp_cmd(Cmd, Flags) ->
        true
    ; display(user_error, '{ERROR: unexpected failure}'), nl(user_error)
    ).
cmdrun_(_) :-
    display(user_error, '{ERROR: Unrecognized argument list}'), nl(user_error).

get_atmlist([], []).
get_atmlist([string(Cs)|Xs], [Y|Ys]) :-
    atom_codes(Y, Cs),
    get_atmlist(Xs, Ys).

% ---------------------------------------------------------------------------
% TODO: Merge with ciaoppcl.pl

% New options:
%   --cwd Dir : switch to the selected directory
%   --timeout Timeout : execute with a timeout limit (ms)

:- use_module(ciaopp(ciaopp), [
    set_last_file/1,
    again/0,
    auto_analyze/2,
    auto_check_assert/2,
    auto_optimize/2,
    %
    set_pp_flag/2,
    current_pp_flag/2,
    %
    set_menu_flag/3,
    get_menu_flag/3]).

:- use_module(library(terms), [atom_concat/2]).
:- use_module(library(compiler/c_itf), [opt_suffix/2]).
:- use_module(library(port_reify)).

:- use_module(library(menu/menu_generator), [
    % TODO: at least these operations should be in a separate module (menu_db?)
    get_menu_flags/1,
    restore_menu_flags_list/1]).

ciaopp_cmd(help, _Flags) :- !,
    display(user_error, 'Use \'ciaopp --help\' to see the available options.'), nl(user_error).
ciaopp_cmd(Cmd, Flags) :- !,
    ( Cmd = ana(File) -> Cmd0 = ana
    ; Cmd = check(File) -> Cmd0 = check
    ; Cmd = opt(File) -> Cmd0 = opt
    ),
    ( member(output_file(OFile), Flags) -> true
    ; true % OFile unbound
    ),
    ( member(timeout(Timeout), Flags) -> true
    ; Timeout = none % No timeout
    ),
    get_menu_flags(OldMenuFlags),
    set_flags(Flags, Cmd0, [], OldFlags), % TODO: add a way to reset flags
    once_port_reify(ciaopp_cmd_with_time_limit(Timeout, Cmd0, File, OFile, GotTimeout), Port),
    restore_flags(OldFlags),
    restore_menu_flags_list(OldMenuFlags),
    ( GotTimeout = yes ->
        display(user_error, '{ERROR: timeout}'), nl(user_error)
    ; true
    ),
    port_call(Port).

ciaopp_cmd_with_time_limit(none, Cmd0, File, OFile, GotTimeout) :- !,
    auto_cmd(Cmd0, File, OFile), GotTimeout = no.
ciaopp_cmd_with_time_limit(Timeout, Cmd0, File, OFile, GotTimeout) :-
    call_with_time_limit(Timeout, auto_cmd(Cmd0, File, OFile), GotTimeout = yes),
    ( var(GotTimeout) -> GotTimeout = no ; true ).

auto_cmd(Cmd0, File, OFile) :-
    ( Cmd0 = ana -> auto_analyze(File, OFile)
    ; Cmd0 = check -> auto_check_assert(File, OFile)
    ; Cmd0 = opt -> auto_optimize(File, OFile)
    ).

% Set context and save previous state in OldFlags
set_flags([], _Cmd0, OldFlags, OldFlags).
set_flags([Flag|Flags], Cmd0, OldFlags0, OldFlags) :-
    set_flag(Flag, Cmd0, OldFlags0, OldFlags1),
    set_flags(Flags, Cmd0, OldFlags1, OldFlags).

set_flag(f(F,V), Cmd0, OldFlags0, OldFlags) :- !,
    ( set_menu_flag_option(Cmd0, F, V) -> true
    ; display('Unrecognized flag '), displayq(F), nl
    ),
    OldFlags = OldFlags0.
set_flag(opt_suffix(Suff), _Cmd0, OldFlags0, OldFlags) :- !,
    opt_suffix(OldSuff,Suff),
    OldFlags = [opt_suffix(OldSuff)|OldFlags0].
set_flag(cwd(AbsPath), _Cmd0, OldFlags0, OldFlags) :- !,
    working_directory(OldAbsPath,AbsPath),
    OldFlags = [cwd(OldAbsPath)|OldFlags0].
set_flag(p(F,V), _Cmd0, OldFlags0, OldFlags) :- !,
    ( current_pp_flag(F, OldV) ->
        set_pp_flag(F, V),
        OldFlags = [p(F,OldV)|OldFlags0]
    ; OldFlags = OldFlags0
    ).
set_flag(_Flag, _Cmd0, OldFlags, OldFlags).

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

parse_opts([], Cmd, Flags) :- !,
    ( var(Cmd) -> % default
        Cmd = help
    ; true
    ),
    Flags = [].
% commands
parse_opts(['-A', File|Opts], Cmd, Flags) :- !,
    Cmd = ana(File),
    parse_opts(Opts, Cmd, Flags).
parse_opts(['-V', File|Opts], Cmd, Flags) :- !,
    Cmd = check(File),
    parse_opts(Opts, Cmd, Flags).
parse_opts(['-O', File|Opts], Cmd, Flags) :- !,
    Cmd = opt(File),
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

% ---------------------------------------------------------------------------
% TODO: part of this functionality should be in ciaopp itself
% TODO: see ciaopp_master.pl (for distributed, timeouts, etc.)

% TODO: pass menu_values everywhere! that is the whole state...
% TODO: save previous flags

% Set menu flags for specific commands
prepare_cmd_flags(analyze) :- % equivalent to auto_analyze/1
    % TODO: what happens with rest of default menu flags?
    set_menu_flag(all, inter_all, analyze).
prepare_cmd_flags(analyze_res_plai) :- % equivalent to auto_analyze/1
    % TODO: what happens with rest of default menu flags?
    set_menu_flag(all, inter_all, analyze),
    set_menu_flag(ana, ana_nf, none),
    set_menu_flag(ana, types, none),
    set_menu_flag(ana, modes, none),
    set_menu_flag(ana, ana_cost, res_plai).
prepare_cmd_flags(check_assert) :- % equivalent to auto_check_assert/1
    % TODO: what happens with rest of default menu flags?
    set_menu_flag(all, inter_all, check_assertions).
prepare_cmd_flags(optimize) :- % equivalent to auto_optimize/1
    % TODO: what happens with rest of default menu flags?
    set_menu_flag(all, inter_all, optimize).
prepare_cmd_flags(custom_do(MenuValues)) :-
    restore_menu_flags_list(MenuValues).

run_cmd(InFile) :-
    ensure_cache_enabled, % TODO: right place?
    again(InFile).

% TODO: move to auto_interface.pl?
again(InFile) :-
    set_last_file(InFile),
    again.

