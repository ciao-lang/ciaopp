:- module(typedef, [
            typedef/2,
            pgm_typedef/2,
            lib_typedef/2,
            paramtypedef/2,
            pgm_paramtypedef/2,
            lib_paramtypedef/2,
            param_matching_mode/1,
            param_type_symbol_renaming/2,
            pgm_param_type_symbol_renaming/2,
            lib_param_type_symbol_renaming/2,
            assert_just_param_renaming/2,
%               regtype
            par_rule_type_symbol/1,
            par_pred_arity/1,
            non_par_rule_type_symbol/1,
            non_par_pred_arity/1,
            type_disjunction/1,
            par_type_disjunction/1], [assertions, basicmodes, regtypes, datafacts]).

:- use_module(typeslib(type_parameter)).

:- regtype type_disjunction/1.

type_disjunction(A) :-
    list(A, gnd).

:- regtype par_rule_type_symbol(Type)

# "@var{Type} is a @tt{parametric type symbol} that should be defined by a 
   parametric type rule.".

par_rule_type_symbol(Type):-
   nonvar(Type),
   functor(Type, F, A),
   A > 0,
   par_pred_arity(F/A).

par_pred_arity(Pred):-
   \+ Pred = (^)/1,
   \+ Pred = (.)/2,
   %% \+ Pred = regtype/1, % Commented out PLG 16-Jun-99
   \+ Pred = call/1,
   \+ Pred = (=)/1.

:- regtype non_par_rule_type_symbol(Type)

# "@var{Type} is a @tt{non-parametric type symbol} 
   that should be defined by a type rule.".

%pp% non_par_rule_type_symbol(Type):-
%pp%    type_parameter(Type), !,
%pp%    fail.
non_par_rule_type_symbol(Type):-
   atom(Type),
   non_par_pred_arity(Type/0).

non_par_pred_arity(Pred):-
  fdtypes_non_par_pred_arity(Pred).

fdtypes_non_par_pred_arity(Pred):-
   % fdtypes
   \+ Pred = int/0,
   %% \+ Pred = rat/0,    %% PLG Dec-5-2003
   \+ Pred = nnegint/0,
   %% \+ Pred = anyfd/0,  %% PLG Dec-5-2003
   % regtypes
   \+ Pred = term/0,
   \+ Pred = bot/0,
   \+ Pred = gnd/0,
   \+ Pred = vr/0, % TODO:[new-resources] is this correct? (for etermsvar) -- yes if it must be the same name used in var_type/1
   \+ Pred = num/0,
   \+ Pred = flt/0,
   \+ Pred = atm/0,
   \+ Pred = var/0, % TODO:[new-resources] is this correct? (for etermsvar) -- not if it must be the same name used in var_type/1
   \+ Pred = struct/0,
   \+ Pred = gndstr/0,
   \+ Pred = []/0.

:- pred typedef(?TypeSymbol, ?Def)
    => non_par_rule_type_symbol * type_disjunction
# "Represents a type rule in internal format (data predicate). ".

:- data pgm_typedef/2. %% For types in programs.
:- data lib_typedef/2. %% For types in libraries.

typedef(Type, Defin) :-
    nonvar(Type), % to make it work as a type generator
    type_parameter(Type),
    param_matching_mode(off), !,
    ( pgm_typedef(Type, Defin) ->
        true
    ; Defin = [term]
    ).
typedef(TypeSymbol, Def) :-
    pgm_typedef(TypeSymbol, Def).
typedef(TypeSymbol, Def) :-
    lib_typedef(TypeSymbol, Def).

:- prop par_type_disjunction/1 + regtype.

par_type_disjunction(_).

:- pred paramtypedef(?TypeSymbol, ?Def)
    => par_rule_type_symbol * par_type_disjunction

# "Represents a parametric type rule in internal format (data predicate). ".

:- data pgm_paramtypedef/2.
:- data lib_paramtypedef/2.

paramtypedef(TypeSymbol, Def) :-
    pgm_paramtypedef(TypeSymbol, Def).
paramtypedef(TypeSymbol, Def) :-
    lib_paramtypedef(TypeSymbol, Def).

:- pred param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb)
# "The parametric type symbol @var{ParTypeSymb} is defined by a non-parametric 
    type rule with type symbol @var{NonParTypeSymb}.".

:- data pgm_param_type_symbol_renaming/2.
:- data lib_param_type_symbol_renaming/2.

param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb) :-
    ( pgm_param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb)
    ; lib_param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb)
    ).

assert_just_param_renaming(ParTypeSymb, NonParTypeSymb) :-
    ( pgm_param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb) ->
        true
    ; asserta_fact(pgm_param_type_symbol_renaming(ParTypeSymb,
                NonParTypeSymb))
    ).

:- data param_matching_mode/1.
param_matching_mode(off).
