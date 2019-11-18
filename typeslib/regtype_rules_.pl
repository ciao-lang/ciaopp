:- module(regtype_rules_, [type_symbol/1], [assertions, basicmodes, regtypes]).

:- regtype type_symbol/1.

type_symbol(Type) :-
    atom(Type),
    \+ Type = [].

%% :- pred type_symbol(Type)
%% 
%% ; "@var{Type} is a type symbol.".
%% 
%% type_symbol(Type):- 
%%     top_type(Type); 
%%     bot_type(Type); 
%%     ground_type(Type); 
%%     base_type_symbol(Type);
%%     rule_type_symbol(Type).
