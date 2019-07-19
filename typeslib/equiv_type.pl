:- module(equiv_type, [equiv_type/2, pgm_equiv_type/2, lib_equiv_type/2],
	    [assertions, basicmodes, regtypes, datafacts]).

:- use_module(typeslib(regtype_rules_)).

:- pred equiv_type(?Type1, ?Type2) : type_symbol * type_symbol
# "Represents non-parametric type symbols which are equivalent.".

:- data pgm_equiv_type/2.
:- data lib_equiv_type/2. %% For libraries.

equiv_type(T1, T2) :-
	pgm_equiv_type(T1, T2).
equiv_type(T1, T2) :-
	lib_equiv_type(T1, T2).
