:- module(preproc_errors,
	[ preproc_error/2,
	  preproc_warning/2,
	  cleanup_errors/0
	],
	[assertions, datafacts]).

:- use_module(library(messages)).
:- use_module(engine(stream_basic)).
:- use_module(library(format)).

:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(ciaopp(p_unit/program_keys), [decode_litkey/5]).
:- use_module(ciaopp(p_unit/clause_db), [maybe_clause_locator/2]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

preproc_error(_Kind,_Arguments):-
	current_pp_flag(error_log,off),!.
preproc_error(Kind,[Location,Expected,Actual,Rules]):-
	get_error_file_default(Chipre_Err_Stream),
	format(Chipre_Err_Stream,"error(~q, [~w, ~w, ~w, ~w]).~n", 
                       [Kind,Location,Expected,Actual,Rules]).

preproc_warning(always_fails,[Goal,K]):-!,
	decode_litkey(K,F,A,C,L),
        make_atom([F,A,C],ClId),
        maybe_clause_locator(ClId,LC),
	warning_message(LC,"goal ~w at literal ~w does not succeed!",[Goal,L]),
	preproc_warning0(always_fails,[Goal,lit(F,A,C,L)]).
preproc_warning(Kind,Arguments):-
	preproc_warning0(Kind,Arguments).

preproc_warning0(_Kind,_Arguments):-
	current_pp_flag(error_log,off),!.
preproc_warning0(undefined_pred,[pred(F,A)]):-!,
	get_error_file_default(Chipre_Err_Stream),
	format(Chipre_Err_Stream,"warning(undefined_pred(~w, ~w),[]).~n",[F,A]).
preproc_warning0(always_fails,[Goal,Location]):-!,
	debug_message("CALL always fails"),
	get_error_file_default(Chipre_Err_Stream),
	format(Chipre_Err_Stream,"warning(always_fails,[~w, ~w]).~n", 
                       [Location,Goal]),
	debug_message("EXIT always fails").
	
get_error_file_default(Chipre_Err_Stream):-
	error_file_opened(Chipre_Err_Stream),!,
	debug_message("already opened error file").
get_error_file_default(Chipre_Err_Stream):-
	debug_message("opening error file"),
	open_error_file(Chipre_Err_Stream).

:- data error_file_opened/1.

cleanup_errors:-
	retractall_fact(error_file_opened(_)).

open_error_file(Chipre_Err_Stream):-
	curr_file(AbsoluteName,_),
	(atom_concat(NewName,'.pl',AbsoluteName) ->
	    true
	;
	    NewName = AbsoluteName),
        atom_concat(NewName,'.err',Error_File),
	open(Error_File,append,Chipre_Err_Stream),
	asserta_fact(error_file_opened(Chipre_Err_Stream)).
