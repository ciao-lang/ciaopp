% (included from typeslib.pl)

% UTILITIES

%% var_intersection([], _L, []).
%% var_intersection([C|R], L, [C|IR]):-
%%        member_term(C, L), !,
%%        var_intersection(R, L, IR).
%% var_intersection([_C|R], L, IR):-
%%        var_intersection(R, L, IR).
%% 
%% % Warning: flat_seq_body is defined also in en gracos/gran_init.pl
%% 
%% %%---------------------------------------------------------------------
%% % Flattens a conjunction of goals
%% %%---------------------------------------------------------------------
%% 
%% 
%% flat_seq_body(((A,B), C), FlatBody):- 
%%        !,
%%        flat_seq_body(A, FA),
%%        flat_seq_body(B, FB),
%%        flat_seq_body(C, FC), 
%%        app_goals(FB, FC, AG),
%%        app_goals(FA, AG, FlatBody).
%% flat_seq_body((Lit, Body), (Lit, FlatBody)):- 
%%        !,
%%        flat_seq_body(Body, FlatBody).
%% flat_seq_body(Lit, Lit).
%% 
%% 
%% %%---------------------------------------------------------------------
%% % Appends two conjunctions of goals
%% %%---------------------------------------------------------------------
%% 
%% app_goals((Lit, Body), Goals, (Lit, AppGoals)):- 
%%         !,
%%      app_goals(Body, Goals, AppGoals).
%% app_goals(Lit, Goals, (Lit, Goals)).


get_head_body_clause((Head:-Body), Head, Body):-!.
get_head_body_clause(Head, Head, true).


:- pred all_occurs_vars(?Term, -VarList)

# "Creates a (closed) list of variables @var{VarList} with the
   ocurrences of variables in the term @var{Term}. Note that
   @var{VarList} can contain duplicated variables.".

all_occurs_vars(X, OVarSet):-
    all_occurs_vars_0(X, [], OVarSet).

all_occurs_vars_0(X, IVarSet, [X|IVarSet]):-
     var(X),
     !.
all_occurs_vars_0([], IVarSet, IVarSet):- 
     !.
all_occurs_vars_0([X|Xs], IVarSet, OVarSet):- 
     !,
     all_occurs_vars_0(X, IVarSet, TeVarSet),          
     all_occurs_vars_0(Xs, TeVarSet, OVarSet).
all_occurs_vars_0(X, IVarSet, OVarSet):-
     X=..[_|Args],
     all_occurs_vars_0(Args, IVarSet, OVarSet).

%% % Translation from clauses to typedef. 
%% 
%%  %% pred_to_typedef(Clauses, Type, TypeDefin):-
%%  %%         functor(Type, Name, A),
%%  %%  predicate_to_type_rule(Name, A, Clauses, TypeRule),
%%  %%  internal_rule_translate(TypeRule, TypeDefin).
%% 
%% pred_to_typedef(Clauses, Type, TypeDef):-
%%         functor(Type, Name, A),
%%      predicate_to_type_rule(Name, A, Clauses, TypeRule),
%%      internal_rule_translate(TypeRule, TypeDefin),
%%         TypeDefin = (typedef Type ::= TypeDef).

 %% predtypedef_to_grammartypedef(Clauses, T, TypeDef):-
 %%     predicate_2_type_rule(T, Clauses, TypeRule),
 %%     internal_rule_translate(TypeRule, TypeDefin),
 %%         TypeDefin = (typedef _TypeSymbol ::= TypeDef).

pred2par_non_par_rule(Type, Clauses, TypeRule):- 
   non_par_rule_type_symbol(Type), 
   !,
   functor(Type, Name, A),
   predicate_to_type_rule(Name, A, Clauses, TypeRule).
pred2par_non_par_rule(Type, Clauses, paramtypedef(Symbol, Defin)):- 
   par_rule_type_symbol(Type), 
   !,
   functor(Type, Name, A),
   predicate_to_type_rule(Name, A, Clauses, typedef(Symbol, Defin)).

predicate_to_type_rule(Predicate, Arity, Clauses, 
                   typedef(TypeSymbol, RuleBody)):-
   predicate_to_rule_type_symbol(Predicate, Arity, TypeSymbol, ParametricVars),
   clauses_to_rule_body(Clauses, ParametricVars, RuleBody).
      
predicate_to_rule_type_symbol(Predicate, Arity, Type, ParametricVars):-
     functor(Type, Predicate, Arity),
     Type =.. [Predicate|ParametricVars].
 
clauses_to_rule_body([], _ParametricVars, []).
clauses_to_rule_body([Clause|Rest], ParamVars, [Type|Rest_Types]):-
  clause_to_type(Clause, Type, ParametricVars),
  ParamVars = ParametricVars,
  clauses_to_rule_body(Rest, ParamVars, Rest_Types).

:- pred clause_to_type(+Clause, -Type, -ParametricVars)

# "Translate a clause into a type.  Variables which do not appear in
   the body are assigned top type. Warning: note that equality
   relations are overriden. Eg.: 
   @begin{verbatim}type1(mv(X, X)):- num(X)@end{verbatim} is
   translated into @begin{verbatim}mv(num, num).@end{verbatim}".

clause_to_type(InClause, Type, ParametricVars):-
  copy_term(InClause, Clause),
  get_head_body_clause(Clause, Head, Body),
  Head =.. [_Pred,Arg1|ParametricVars],
  escaped_type(Arg1, Type),
  (ground(Type)
   -> true
    ; body_to_type(Body),
      all_occurs_vars(Type, VarList),
      assign_top_type_to_non_parametric_vars(VarList, ParametricVars)).

escaped_type(Type, Type):-
    var(Type), !.
escaped_type(Type, Type):-
   (number(Type);
    Type = []),
    !.
escaped_type(Type, ^(Type)):-
    atom(Type),
    !.
escaped_type(Type, EscType):-
    functor(Type, F, A),
    functor(EType, F, A),
    comp_escaped_type(A, Type, EType),
    (F/A = (.)/2 
       -> EscType = EType
       ;  EscType = ^(EType)). 

comp_escaped_type(0, _, _):-!.
comp_escaped_type(A, Type, EscType):-
   A > 0,
   arg(A, Type, Arg),
   escaped_type(Arg, EscArg),
   arg(A, EscType, EscArg),
   A1 is A - 1,
   comp_escaped_type(A1, Type, EscType).

body_to_type(true):-!.
body_to_type((Lit, Body)):-!,
  one_literal_to_type(Lit),
  body_to_type(Body).
body_to_type(Lit):-
  one_literal_to_type(Lit).

one_literal_to_type(call(Type, Var)):- !, 
  Var = Type.
 %% one_literal_to_type(regtype(Var, Type)):- !,  % Commented out PLG 16-Jun-99 
 %%   Var = Type. 
one_literal_to_type(Lit):-
  Lit =.. [Name, Var|Param],
  Var =.. [Name|Param].

assign_top_type_to_non_parametric_vars([], _ParVars):-
    !. 
assign_top_type_to_non_parametric_vars([Var|List], ParVars):-
    member_term(Var, ParVars), 
    !,
    assign_top_type_to_non_parametric_vars(List, ParVars). 
assign_top_type_to_non_parametric_vars([Var|List], ParVars):-
    set_top_type(Var),
    assign_top_type_to_non_parametric_vars(List, ParVars). 

% End of translation from clauses to typedef. 

% Format translation

internal_rule_translate(typedef(TypSymbol, InDefin), 
                   (typedef TypSymbol ::= ExDefin)):-
     internal_union_translate(InDefin, ExDefin).

internal_union_translate([Type1,Type2|Defin], (NewType;NewDefin)):-!,
   internal_type_translate(Type1, NewType),
   internal_union_translate([Type2|Defin], NewDefin).
internal_union_translate([Type], NewType):- 
  internal_type_translate(Type, NewType).

internal_type_translate(X, X).


% End of format translation


% Types in predicate format

%% :- pred regular_type_pred_definition_e(+Clauses, -Error)
%% 
%% # "Checks whether @var{Clauses} define a valid regular type.  If they
%%    do, then the predicate succeeds and @var{Error} is an unbound
%%    variable.  Otherwise, either, the predicate fails, or succeeds with
%%    @var{Error} bound to an error message.".
%% 
%% regular_type_pred_definition_e([], Error):-
%%    !,
%%    Error = there_are_no_type_clauses.
%% regular_type_pred_definition_e(Clauses, Error):-
%%    Clauses = [Clause|Rest], 
%%    get_head_body_clause_e(Clause, Head, Body, Error),
%%    (var(Error) ->
%%        functor(Head, Name, Arity),
%%        regular_type_clause_definition(Clause, Head, Body, Name, Arity, Error),
%%        regular_type_pred_definition_1(Rest, Name/Arity, Error)
%%    ; true).
%% 
%% get_head_body_clause_e(Clause, Head, Body, _Error):- 
%%      get_head_body_clause(Clause, Head, Body), !.
%% get_head_body_clause_e(Clause, _Head, _Body, Error):-
%%      Error = bad_clause_format(Clause).
%% 
%% regular_type_clause_definition(_Clause, _Head, _Body, _Name, _Arity, Error):-
%%    nonvar(Error), !.
%% regular_type_clause_definition(Clause, Head, Body, Name, Arity, Error):-
%%    definable_type(Name/Arity, Error),
%%    (var(Error) -> 
%%         Head =.. [Name,Arg1|ParametricVars],
%%         list_of_unique_parametric_variables(ParametricVars, Name/Arity, Error),
%%         all_occurs_vars(Arg1, TermVars),
%%         list_of_unique_term_variables(TermVars, Name/Arity, Error),
%%         var_intersection(ParametricVars, TermVars, CommonVars),
%%         valid_common_vars(CommonVars, Name/Arity, Error),
%%         body_with_no_vars(Body, Error),
%%         (var(Error) -> 
%%               flat_seq_body(Body, FlatBody), 
%%               regular_type_body_definition(FlatBody, Clause, [], TermVars, 
%%                                            ParametricVars, Error)
%%               ; true)
%%         ; true).
%% 
%% body_with_no_vars(_, Error):-
%%        nonvar(Error), 
%%        !. 
%% body_with_no_vars(B, Error):- 
%%        var(B), 
%%        !,
%%        Error = variable_in_body(B). 
%% body_with_no_vars((A, B), Error):- 
%%        !,
%%        body_with_no_vars(A, Error),
%%        body_with_no_vars(B, Error).
%% body_with_no_vars(_Lit, _Error).
%% 
%% 
%% definable_type(_Pred, Error):-
%%    nonvar(Error), 
%%    !.
%% definable_type(Name/0, Error):- 
%%    !, 
%%    Error = bad_type_arity(Name/0).
%% definable_type(Name/Arity, Error):-
%%     Arity1 is Arity - 1,
%%     ((non_par_pred_arity(Name/Arity1) ; par_pred_arity(Name/Arity1))
%%        -> true
%%        ;
%%        Error = forbidden_pred_defined_as_type(Name/Arity)).
%% 
%% list_of_unique_term_variables(_TermVars, _Pred, Error):-
%%     nonvar(Error), !.
%% list_of_unique_term_variables(TermVars, _Pred, _Error):-
%%     list_of_unique_variables_2(TermVars, []), !.
%% list_of_unique_term_variables(TermVars, Pred, Error):-
%%     Error = not_unique_term_vars(TermVars, Pred).
%% 
%% valid_common_vars(_Vars, _, Error):-
%%    nonvar(Error), !.
%% valid_common_vars([], _, _Error):- !.
%% valid_common_vars(CommonVars, Pred, Error):-
%%    Error = bad_common_vars(CommonVars, Pred).
%% 
%% regular_type_pred_definition_1(_Clauses, _Pred, Error):-
%%    nonvar(Error), !.
%% regular_type_pred_definition_1([], _Pred, _Error).
%% regular_type_pred_definition_1(Clauses, Name/Arity, Error):-
%%    Clauses = [Clause|Rest], 
%%    get_head_body_clause_e(Clause, Head, Body, Error),
%%    (var(Error) ->
%%        (functor(Head, Name, Arity) ->
%%            regular_type_clause_definition(Clause, Head, Body, Name, 
%%                                           Arity, Error),
%%            regular_type_pred_definition_1(Rest,  Name/Arity, Error)
%%           ;
%%            Error = different_clause_predicate(Name/Arity, Clause))
%%     ; true).
%% 
%% regular_type_body_definition(_Body, _Clause, _TermVarsSeen,
%%                              _TermVars, _ParametricVars, Error):-
%%     nonvar(Error), !.
%% regular_type_body_definition((Lit,Body), Clause, TermVarsSeen,
%%                              TermVars, ParametricVars, Error):-
%%     !,
%%     regular_type_literal_definition(Lit, Clause, TermVarsSeen, TermVars, 
%%                   ParametricVars, NewTermVarsSeen, Error),
%%     regular_type_body_definition(Body, Clause, NewTermVarsSeen,
%%                              TermVars, ParametricVars, Error).
%% regular_type_body_definition(Lit, Clause, TermVarsSeen, TermVars, 
%%                              ParametricVars, Error):-
%%     regular_type_literal_definition(Lit, Clause, TermVarsSeen, TermVars, 
%%                                     ParametricVars, _NewTermVarsSeen, Error).
%% 
%% regular_type_literal_definition(_Lit, _Clause, _TermVarsSeen, _TermVars, 
%%                                 _ParametricVars, _NewTermVarsSeen, Error):-
%%    nonvar(Error), !. 
%% regular_type_literal_definition(Lit, _Clause, _TermVarsSeen, _TermVars, 
%%                                 _ParametricVars, _NewTermVarsSeen, _Error):-
%%    Lit == true, !. 
%% regular_type_literal_definition(Lit, Clause, TermVarsSeen, TermVars, 
%%                                 ParametricVars, NewTermVarsSeen, Error):-
%%    nonvar(Lit),
%%    functor(Lit, Name, Arity),
%%    regular_type_literal_definition_1(Name, Arity, Lit, Clause,
%%                                      TermVarsSeen, TermVars,
%%                                      ParametricVars, NewTermVarsSeen, Error).
%% 
%% regular_type_literal_definition_1(Name, Arity, Lit, Clause,
%%                  TermVarsSeen, TermVars, ParametricVars, [Arg1|TermVarsSeen],
%%               Error):-
%%    (valid_body_type(Name/Arity) ->  
%%         Lit =.. [Name, Arg1|Parameters],
%%         valid_term_var(Arg1, Lit, TermVarsSeen, TermVars, Clause, Error),  
%%         valid_parameters(Parameters, Lit, Clause, ParametricVars, Error)
%%         ;
%% %% PBC: call/2 with reversed args
%%      Name/Arity = call/2 ->
%%             Lit =.. [Name, Arg, Arg1],
%%          valid_term_var(Arg1, Lit, TermVarsSeen, TermVars, Clause, Error),  
%%          valid_parameters([Arg], Lit, Clause, ParametricVars, Error)
%%          ;
%%             Error = bad_builtin_in_body_type(Name/Arity, Clause)).
%% 
%%  %% valid_body_type(Pred):- 
%%  %%      nonvar(Pred),
%%  %%      Pred = Name/Arity,
%%  %%      \+ Name/Arity = (^)/2, 
%%  %%      \+ Name/Arity = (.)/3,
%%  %%      atom(Name), 
%%  %%      integer(Arity),
%%  %%      Arity > 0.     
%%     
%% valid_body_type(Name/Arity):- 
%%      Arity > 0, 
%%      Arity1 is Arity - 1,     
%%      valid_body_type_1(Name/Arity1).

%% % PBC: Not anymore (now call/2)
%% valid_body_type_1(regtype/1):-
%%      !.

%% valid_body_type_1(Pred):-
%%      par_pred_arity(Pred).     
%% 
%% valid_parameters(_Params, _Lit, _Clause, _ParametricVars, Error):-
%%    nonvar(Error), !.
%% valid_parameters([Param|Parameters], Lit, Clause, ParametricVars, Error):-
%%    (regular_type_expression(Param, ParametricVars)
%%      -> valid_parameters(Parameters, Lit, Clause, ParametricVars, Error)
%%      ;  Error = invalid_type_parameters(Param, ParametricVars, Lit,
%%                 Clause)).
%% valid_parameters([], _Lit, _Clause, _ParametricVars, _Error).
%% 
%% valid_term_var(Arg1, Lit, _TermVarsSeen, TermVars, Clause, Error):-
%%      nonvar(Arg1),
%%      !,
%%      Error =  bad_term_variable(TermVars, Lit, Clause).
%% valid_term_var(Arg1, Lit, _TermVarsSeen, TermVars, Clause, Error):-
%%      \+ member_term(Arg1, TermVars), !,
%%      Error = bad_term_variable(TermVars, Lit, Clause).
%% valid_term_var(Arg1, Lit, TermVarsSeen, _TermVars, Clause, Error):-
%%      member_term(Arg1, TermVarsSeen), !,
%%      Error = multiple_type_assignment(Arg1, Lit, Clause).
%% valid_term_var(_Arg1, _Lit, _TermVarsSeen, _TermVars, _Clause, _Error).

