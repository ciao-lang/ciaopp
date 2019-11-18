:- module(type_parameter, [type_parameter/1], [assertions]).

type_parameter(Type) :-
    atom(Type),
    atom_concat(tp, N, Type),
    atom_number(N, _),
    !.
