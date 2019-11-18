:- module(plai_errors, [compiler_error/1, undo_errors/0],[datafacts]).

% TODO: distinguish between errors and bugs; reuse this module for messages when
% applying assertions

:- use_module(library(messages)).

:- data given/1.

undo_errors:-
    retractall_fact(given(_)).

compiler_error(Error):-
    current_fact(given(Error)), !.
compiler_error(Error):-
    compiler_error_(Error),
    asserta_fact(given(Error)).

% s_interface
compiler_error_(bad_format(Type,Info)):-
    warning_message("bad format ~w(~q) in entry or trust declaration",
            [Type,Info]).
% simpspec
compiler_error_(versions(L,Name)):-
    warning_message("entry ~w uses version ~w",[L,Name]).
compiler_error_(conflict(Entry)):-
    warning_message("name conflict: entry ~w corresponds to more than one version",[Entry]).
compiler_error_(no_complete(Parent)):-
    error_message("Acc without Complete: ~w",[Parent]).
compiler_error_(diff_replace_reg):-
    error_message("different replace registers").
% support
compiler_error_(variable_call):-
%       warning_message("variable in meta_call: assuming top entries").
    warning_message("variable in meta_call:
            the program should include the required entries").
% domains
compiler_error_(not_implemented(AbsInt,SgKey)):-
    warning_message("builtin not yet implemented in ~w: ~w",
            [AbsInt,SgKey]).
compiler_error_(op_not_implemented(glb)):-
    warning_message("glb not yet implemented in this domain").
% fixpoint
compiler_error_(invalid_trust(SgKey)):-
    warning_message("invalid trust for predicate ~w: trust ignored",[SgKey]).
compiler_error_(failed):-
    error_message("Something has failed!").
% aeq_aux
compiler_error_(bad_entry):-
    warning_message("bad module or entry declaration found: no analysis performed").
% del/lsign
compiler_error_(not_normalized(Sg,Head)):-
    warning_message("not normalised program: goal ~q wrt head ~q",[Sg,Head]).
compiler_error_(not_normalized_pred):-
    warning_message("predicate not normalized").
compiler_error_(del_variable_call(Sg)):-
    error_message("variable as goal ~q: analysis fails!",[Sg]).
compiler_error_(del_no_conds):-
    warning_message("delay conditions non-normalized").
compiler_error_(del_var_conds):-
    warning_message("variable in delay condition").
% fr, min_*
compiler_error_(piii_lists):-
    warning_message("error in translation of piii-lists").
compiler_error_(cons_lists):-
    warning_message("normalisation problem: L and N in L::N are not variables").
compiler_error_(arg_not_normal):-
    warning_message("normalisation problem: A2 in arg(A1,A2,A3) should be a variable").
% several:
compiler_error_(error(Error)):-
    error_message(Error).

% TODO: unify with ctcheck_messages.pl and with trust.pl
:- export(invalid_trust_message/4).
invalid_trust_message(AssrtType,NASub,Sg:OldASub,Head) :-
    NASub='$bottom', OldASub\=='$bottom', !,
    note_message("invalid trusted ~w for ~w:~n analysis infers:~n ~w:~w",
                 [AssrtType,Head,Sg,OldASub]).
invalid_trust_message(_,_,_,_).
