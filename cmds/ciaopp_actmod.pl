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

% ----- (loaded dynamically in ciaoppcl)
:- use_module(ciaopp(p_unit/p_asr), []).
:- use_module(ciaopp(analyze_driver), []).
:- use_module(ciaopp(transform_driver), []).
:- use_module(ciaopp(auto_interface), []). % TODO: needed?
%
:- use_module(ciaoppcl, [
    short_usage_message/0, parse_opts/3, ciaopp_run/2,
    ciaopp_error_message/1
]).
%
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(io_port_reify), [io_once_port_reify/4]).
:- use_module(library(port_reify), [port_call/1]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(library(lists), [append/3]).

:- dist_node.

% TODO: ciaopp-client.bash does not pass the process error code correctly

:- suspendable(cmdrun(json)).
cmdrun(Args) :-
    io_once_port_reify(cmdrun_(Args), Port, OutString, ErrString),
    Result = ~append(OutString,ErrString),
    port_call(Port),
    set_buf('console', Result).

% TODO: propagate exceptions through actmod
cmdrun_(Args) :-
    catch(cmdrun__(Args), E, ciaopp_error_message(E)).

cmdrun__(Args0) :-
    get_atmlist(Args0, Args), !,
    ( parse_opts(Args, Cmd, Flags),
      ( var(Cmd) -> Cmd = help ; true ), % (default)
      ciaopp_cmd(Cmd, Flags) ->
        true
    ; display(user_error, '{ERROR: unexpected failure}'), nl(user_error)
    ).
cmdrun__(_) :-
    display(user_error, '{ERROR: Unrecognized argument list}'), nl(user_error).

ciaopp_cmd(help, _Flags) :- !,
    short_usage_message.
ciaopp_cmd(Cmd, _Flags) :- 
    ( Cmd = toplevel(_)
    ; Cmd = customize_and_preprocess(_)
    ; Cmd = restore_menu(_,_)
    ),
    !,
    display(user_error, '{ERROR: Action unavailable}'), nl(user_error).
ciaopp_cmd(Cmd, Flags) :-
    ciaopp_run(Cmd, Flags).

get_atmlist([], []).
get_atmlist([string(Cs)|Xs], [Y|Ys]) :-
    atom_codes(Y, Cs),
    get_atmlist(Xs, Ys).
