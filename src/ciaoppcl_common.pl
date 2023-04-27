:- module(_, [], [assertions]).

:- compilation_fact(unified_menu).

:- doc(title,"Common for the CiaoPP command-line interface").
:- doc(author, "The Ciao Development Team").

:- use_module(engine(io_basic)).
:- use_module(ciaopp(frontend_driver), [cache_and_preload_lib_sources/0]).
:- use_module(library(messages)).
:- use_module(library(lists), [member/2]).

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
    auto_analyze/2,
    auto_check_assert/2,
    auto_optimize/2,
    %
    set_pp_flag/2,
    %
    set_menu_flag/3,
    get_menu_flag/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2,valid_flag_values/2]).
:- use_module(library(system), [working_directory/2]).
:- use_module(library(timeout), [call_with_time_limit/3]). % TODO: experimental!
:- use_module(library(port_reify), [once_port_reify/2, port_call/1]).

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

% ===========================================================================
:- doc(section, "CiaoPP error messages").

:- use_module(library(errhandle), [default_error_message/1]).
%:- use_module(library(messages), [error_message/2]).

:- export(ciaopp_error_message/1). % (exported actmod)
% ciaopp_error_message(ciaopp_error_msg(Format, Args)) :- !, % TODO: use?
%       error_message(Format, Args).
ciaopp_error_message(ciaopp_error(flag_errs)) :- !. % (message already shown)
ciaopp_error_message(ciaopp_error(timeout)) :- !,
    display(user_error, '{ERROR: timeout}'), nl(user_error).
ciaopp_error_message(E) :-
    default_error_message(E).
