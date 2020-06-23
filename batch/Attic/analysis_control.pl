:- module(analysis_control, [main/1], [assertions]).

:- use_module(library(stream_utils), [string_to_file/2]).
:- use_module(library(terms_io), [file_to_terms/2]).
:- use_module(library(pathnames), [path_concat/3]).
:- use_module(library(process), [process_call/3, process_kill/1]).
:- use_module(library(system), [pause/1]).

:- use_module(deepfind(find_aux), [bundle_data_dir/1]).

:- doc(module, "This module controls the execution time of processes.").

:- pred main([Pid]) #"Controls the process with @var{Pid}, if this
    process has no changes after X seconds, where timeout(X), the
    process is killed.".
main([Pid]) :- set_fact(controlling_process(Pid)),
curr_file(F), set_fact(analyzing(F)), control(0).

:- data analyzing/1.
:- data controlling_process/1.

check_file(X) :-
    bundle_data_dir(D),
    path_concat(D, 'last_analyzed_file.pl', X).

% TODO: configure timeout
timeout(60).

% This process lasts timeout(X).
control(X) :-
    timeout(X), !,
    controlling_process(Pid),
    process_kill(Pid), % use process_terminate instead?
    curr_file(CFile),
    display_list(['Analysis timeout for: ', CFile]).
control(N) :-
    analyzing(AFile),
    curr_file(CFile),
    ( AFile = CFile ->
        N1 is N + 1
    ;
        N1 is 0,
        set_fact(analyzing(CFile))
    ),
    pause(1),
    control(N1).

curr_file(F) :-
    check_file(CF),
    file_to_terms(CF, T),
    T = [last_analyzed(F)|_].
            
