
:- module(type_errors,[compiler_error/1],[]).

:- use_module(library(messages)).

output_message(w,S,Args):-
    warning_message(S,Args).
output_message(e,S,Args):-
    error_message(S,Args).

:- push_prolog_flag(multi_arity_warnings,off).

compiler_error(E):-
    compiler_error(E,I,S,Args),
    output_message(I,S,Args).

compiler_error(variable_in_body(B), e,
     "a body literal cannot be a variable: ~q", [B]).
compiler_error(type_pred_syntax(Clauses), e,
    "syntax error in regular type definition (in predicate format):~n ~q", [Clauses]).
compiler_error(type_rule_syntax(R), e, 
    "syntax error in regular type definition (in type rule format):~n",  [R]).
compiler_error(forbidden_pred_defined_as_type(Pred),e,
    "predicate ~q cannot be redefined as a type",
    [Pred]).
compiler_error(different_clause_predicate(Pred, Clause),e,
    "clause:~n ~q~n found in definition of type ~q",
    [Clause,Pred]).
compiler_error(invalid_type_parameters(Param, Vars, Lit, Clause),e,
    "parameter ~q in literal ~q~n in the body of clause:~n ~q~n should be a regular type expression where only parametric variables ~q are allowed",
    [Param,Lit,Clause,Vars]).
compiler_error(multiple_type_assignment(Var, Lit, Clause),e,
    "attempt to assign multiple type to term variable ~q in literal ~q~n in the body of clause:~n ~q~n",
    [Var,Lit,Clause]).
compiler_error(bad_term_variable(TermVars, Lit, Clause),e,
    "first argument of ~q~n should be a term variable, i.e., should be one of: ~q~n in the body of clause:~n ~q~n Recall that term variables are those appearing in the first argument of the head",
    [Lit,TermVars,Clause]).
compiler_error(bad_builtin_in_body_type(Built, Clause),e,
    "builtin predicate ~q cannot be used in the body of clause:~n ~q~n defining a type (only type/2 and true/0 are allowed",
    [Built,Clause]).
compiler_error(bad_common_vars(Vars, Type),e,
    "variables ~q are both, parametric, and term variables in the definition of type ~q~n Recall that all arguments (except the first one) should be distinct variables which do no occur in the first argument",
    [Vars,Type]).
compiler_error(bad_parametric_vars(Vars, Type),e,
    "bad parametric variables ~q in the definition of type ~q~n Recall that all arguments (except the first one) should be distinct variables which do no occur in the first argument",
    [Vars,Type]).
compiler_error(not_unique_term_vars(Vars, Type),e,
    "Term variables ~q are not unique in the definition of type ~q (i.e. it is not allowed to introduce equality restrictions between the variables of a regular type definition)",
    [Vars,Type]).
compiler_error(builtin_pred_redefined_as_type(T),e,
    "builtin predicate ~q cannot be redefined as a type",
    [T]).
compiler_error(bad_type_arity(T),e,
    "a predicate of arity 0 cannot define a type: ~q",
    [T]).
compiler_error(bad_clause_format(Clause),e,
    "bad format for clause defining a type:~n ~q~n",
    [Clause]).
compiler_error(there_are_no_type_clauses,e,
    "there are no clauses for type definition",
    []).
compiler_error(multiple_type_defin(T),w,
    "parametric type ~q defined by multiple type rules",
    [T]).
compiler_error(param_type_undefined(T),w,
    "parametric type ~q not defined",
    [T]).
compiler_error(type_undefined(T),w,
    "type ~q not defined",
    [T]).
compiler_error(req_type_undefined(T),w,
    "required type ~q not defined",
    [T]).

:- pop_prolog_flag(multi_arity_warnings).
