% Validation of regular types in rule format 

%% :- pred valid_regular_type_rule(R)
%% 
%% # "@var{R} is a valid @tt{regular type rule}.".
%% 
%% valid_regular_type_rule(R):-
%%    valid_regular_type_rule_e(R, Error), 
%%    !,
%%    (nonvar(Error) -> 
%%       compiler_error(Error),
%%       fail
%%      ; true).
%% valid_regular_type_rule(R):-   
%%    compiler_error(type_rule_syntax(R)), 
%%    fail.
%% 
%% % End of validation of regular types in rule format 
%% 
%% % Apply a type to a term
%% 
%% set_type_of_term(Term,Type,Typing):-
%% 	Type =.. [T|Args],
%% 	Typing =.. [T,Term|Args].

% Translation of types

:- pred pretty_type_lit(+Type, -PreType, -TypeSymbolList)

# "@var{PreType} is @var{Type} in pretty unfolded
format. @var{TypeSymbolList} is a list with the type symbols appearing
in @var{PreType}.".

pretty_type_lit(Type, PreType, TypeSymbolList):-
    (simp_typedefs(yes) ->
         no_simp_pretty_type_lit(Type, PreType, TypeSymbolList)
         ;
         simp_pretty_type_lit(Type, PreType, TypeSymbolList)).

:- pred no_simp_pretty_type_lit(+Type, -PreType, -TypeSymbolList)

# "@var{PreType} is @var{Type} in pretty unfolded
format. @var{TypeSymbolList} is a list with the type symbols appearing
in @var{PreType}.".

no_simp_pretty_type_lit(Type, PreType, TypeSymbolList):-
     unfold_one_single_type(^(Type), [], UnfoldedPType),
     replace_one_non_par_type(UnfoldedPType, PType),
     PType = ^(PreType),
     type_symbols_0(PType, [], TypeSymbolList).

 %%      unfold_one_single_type(^(Type), [], UnfoldedPType),
 %%      UnfoldedPType = ^(PreType),
 %%      type_symbols_0(UnfoldedPType, [], TypeSymbols).

simp_pretty_type_lit(Type, PreType, TypeSymbolList):-
     type_symbols_0(^(Type), [], TypeSymbols),
     compute_transitive_closure(TypeSymbols, [], TransClosure),
     select_rules_2(TransClosure, RuleList),
     simplify_some_typedefs(RuleList, _TypeRuleList),
     no_simp_pretty_type_lit(Type, PreType, TypeSymbolList).

:- pred pretty_type_lit_rules(+Type, -PreType, -TypeSymbolList, -TypeRuleList)

# "@var{PreType} is @var{Type} in pretty unfolded
format. @var{TypeSymbolList} is a list with the type symbols appearing
in @var{PreType} and @var{TypeRuleList} a list with the rules defining
these type symbols.".

pretty_type_lit_rules(Type, PreType, TypeSymbolList, TypeRuleList):-
     pretty_type_lit(Type, PreType, TypeSymbolList),
     get_required_rules(TypeSymbolList, TypeRuleList).

%%  %% 
%%  %% pretty_type_lit_rules(Type, PreType, TypeSymbolList, TypeRuleList):-
%%  %%      (simp_typedefs(yes) ->
%%  %%            no_simp_pretty_type_lit_rules(Type, PreType, TypeSymbolList, TypeRuleList)
%%  %%            ;
%%  %%            simp_pretty_type_lit_rules(Type, PreType, TypeSymbolList, TypeRuleList)).
%%  %% 
%%  %% :- pred no_simp_pretty_type_lit_rules(+Type, -PreType, -TypeSymbolList, -TypeRuleList)
%%  %% 
%%  %% # "@var{PreType} is @var{Type} in pretty unfolded
%%  %% format. @var{TypeSymbolList} is a list with the type symbols appearing
%%  %% in @var{PreType} and @var{TypeRuleList} a list with the rules defining
%%  %% these type symbols.".
%%  %% 
%%  %% no_simp_pretty_type_lit_rules(Type, PreType, TypeSymbolList, TypeRuleList):-
%%  %%      no_simp_pretty_type_lit(Type, PreType, TypeSymbolList),
%%  %%      get_required_rules(TypeSymbolList, TypeRuleList).
%% 
%% :- pred translate_rule_list_to_internal(?InRules, ?ExRules)
%% 
%% => type_rule_list * external_type_rule_list
%% 
%%   # "@var{InRules} is the internal format of @var{ExRules}
%%      (which is in external format). Reversible".
%% 
%% :- regtype external_type_rule_list/1.
%% 
%% external_type_rule_list(A) :-
%% 	list(A, external_type_rule).
%% 
%% :- regtype external_type_rule/1.
%% 
%% external_type_rule((typedef TypSymbol ::= ExDefin)) :-
%% 	gnd(TypSymbol),
%% 	gnd(ExDefin).
%% 
%% translate_rule_list_to_internal([], []).
%% translate_rule_list_to_internal([IRule|IL], [Rule|L]) :- 
%%   internal_rule_translate(IRule, Rule),
%%   translate_rule_list_to_internal(IL, L).
%% 
%% 
%% translate_types_to_internal([], []).
%% translate_types_to_internal([Type|IL], [Type1|L]) :- 
%%   internal_type_translate(Type1, Type), 
%%   translate_types_to_internal(IL, L).
%% 
%% :- pred translate_predicates_to_type_rules(+TypeTable, -TypeRules)
%% 
%%  => type_table * type_rule_list
%% 
%% # "Translates the type definitions in predicate format (which are in
%%    @var{TypeTable} into rule format (@var{TypeRules}.".
%% 
%% translate_predicates_to_type_rules(TypeTable, TypeRules):-
%%    regtypes_translate_predicates_to_type_rules(TypeTable, TypeRules).
%% 
%% regtypes_translate_predicates_to_type_rules([], []).
%% regtypes_translate_predicates_to_type_rules([Entry|Tab], [TypeRule|RestRules]):-
%%     Entry = st(Pred/Arity, Clauses, _),
%%     Arity1 is Arity - 1,
%%     % ga_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule),
%%     % Old 4 May 98
%%     %% predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule), %% Good
%%     pawel_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule), % PLG patch 16 may 99
%%     %% debug_message("CALL: ~q ~n", [pawel_patch_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule)]),
%%     %% pawel_patch_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule), % PLG patch 15 may 99
%%     %% debug_message("EXIT: ~q ~n", [pawel_patch_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule)]),
%%     regtypes_translate_predicates_to_type_rules(Tab, RestRules).
%% 
%% %% Begin patch. 15 may 1999 PLG
%% 
%% pawel_patch_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule):-
%%     Arity1 == 0,
%%     Clauses = [(Head:-true)],
%%     arg(1, Head, Arg),
%%     pawel_type(Arg),
%%     !,
%%     TypeRule = typedef(Pred, [Arg]).
%% pawel_patch_predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule):-
%%     predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule).
%% 
%% pawel_type(intexpr).
%% pawel_type(numexp).
%% 
%% %% End patch 15 may 1999 PLG
%% 
%% %% Begin patch. 16 may 1999 PLG
%% 
%% pawel_predicate_to_type_rule(Predicate, Arity, Clauses, 
%%                        typedef(TypeSymbol, RuleBody)):-
%%    predicate_to_rule_type_symbol(Predicate, Arity, TypeSymbol, ParametricVars),
%%    pawel_clauses_to_rule_body(Clauses, ParametricVars, RuleBody).
%% 
%%  
%% pawel_clauses_to_rule_body([], _ParametricVars, []).
%% pawel_clauses_to_rule_body([Clause|Rest], ParamVars, [Type|Rest_Types]):-
%%   pawel_clause_to_type(Clause, Type, ParametricVars),
%%   ParamVars = ParametricVars,
%%   pawel_clauses_to_rule_body(Rest, ParamVars, Rest_Types).
%% 
%% pawel_clause_to_type(InClause, Type, _ParametricVars):-
%%   copy_term(InClause, Clause),
%%   get_head_body_clause(Clause, Head, Body),
%%   Body == true,
%%   functor(Head, _, 1),
%%   arg(1, Head, Arg),
%%   pawel_type(Arg),
%%   !,
%%   Type = Arg.
%% pawel_clause_to_type(InClause, Type, ParametricVars):-
%%   copy_term(InClause, Clause),
%%   get_head_body_clause(Clause, Head, Body),
%%   Head =.. [_Pred,Arg1|ParametricVars],
%%   escaped_type(Arg1, Type),
%%   (ground(Type)
%%    -> true
%%     ; body_to_type(Body),
%%       all_occurs_vars(Type, VarList),
%%       assign_top_type_to_non_parametric_vars(VarList, ParametricVars)).
%% 
%% %% End patch
%% 
%% :- pred builtin_type_preds_to_type_rules(+TypePreds, -TypeRules)
%% 
%%  => type_table * type_rule_list
%% 
%% # "Translates the definitions of builtin types @var{TypePreds} (which
%%    are obtained from builtintables.pl) in predicate format into type
%%    rule format (@var{TypeRules}.".
%% 
%% builtin_type_preds_to_type_rules([], []).
%% builtin_type_preds_to_type_rules([Entry|Tab], [TypeRule|RestRules]):-
%%     Entry = typepred(Pred/Arity, Clauses),
%%     Arity1 is Arity - 1,
%%     predicate_to_type_rule(Pred, Arity1, Clauses, TypeRule),
%%     builtin_type_preds_to_type_rules(Tab, RestRules).
%% 
%% %% Temporal translation to be removed soon. 
%%  %% He observado que el analisis de Gallager saca clausulas de este tipo:
%%  %% 
%%  %% t113(num):-true.
%%  %% 
%%  %% cuando en realidad lo que deberia de decir segun nuestra sintaxis es:
%%  %% 
%%  %% t113(X):- num(X).
%%  %% 
%%  %% Este problema tambien aparecia en el analisis de Pawel y lo
%%  %% solucionaste.
%%  %% 
%%  %% Esto hace que el tipo t113  se traduzca a typedef t113 ::= ^num ; ...
%%  %% en lugar de a t113 ::= num ; ... 
%%  %% 
%%  %% De momento he modificado el traductor de tipos a typedefs para que
%%  %% tenga en cuenta esto, pero lo suyo seria hacer que el analisis de
%%  %% Gallager devuelva los tipos en nuestro formato, no?
%% 
%% ga_predicate_to_type_rule(Predicate, Arity, Clauses, 
%%                          typedef(TypeSymbol, RuleBody)):-
%%    predicate_to_rule_type_symbol(Predicate, Arity, TypeSymbol, ParametricVars),
%%    ga_clauses_to_rule_body(Clauses, ParametricVars, RuleBody).
%%  
%% ga_clauses_to_rule_body([], _ParametricVars, []).
%% ga_clauses_to_rule_body([Clause|Rest], ParamVars, [Type|Rest_Types]):-
%%   ga_clause_to_type(Clause, Type, ParametricVars),
%%   ParamVars = ParametricVars,
%%   ga_clauses_to_rule_body(Rest, ParamVars, Rest_Types).
%% 
%% ga_clause_to_type(InClause, num, []):-
%%    nonvar(InClause),
%%    functor(InClause, (:-), 2),
%%    arg(1, InClause, Head),
%%    nonvar(Head),
%%    functor(Head, _F, 1),
%%    arg(1, Head, Arg),
%%    Arg == num,
%%    arg(2, InClause, Body),
%%    Body == true,
%%    !.
%% ga_clause_to_type(InClause, Type, ParametricVars):-
%%    clause_to_type(InClause, Type, ParametricVars).
%% 
%% % End temporary translation.
%% 
%% % Version for parametric types.
%% 
%% % Translation of types
%% 
%% 
%% % End of version for parametric types.
%% 
%% rules_to_pred_defs([], []).
%% rules_to_pred_defs([Rule|L], DefList) :- 
%%         debug_message("one_rule_to_pred(~q, ~q)", [Rule, DefList1]),
%% 	one_rule_to_pred(Rule, DefList1),
%%         debug_message("one_rule_to_pred(~q, ~q)", [Rule, DefList1]),
%% 	append(DefList1, DefList2, DefList),
%% 	rules_to_pred_defs(L, DefList2).
%% 
%% one_rule_to_pred(typedef(Pred, Def), Cls):-
%% 	one_typedef_to_pred(Def, Pred, Cls0),
%% 	rewrite_cls(Cls0, Cls1),
%% 	null_directive_key(DK),
%%         functor(Pred, Name, Ari),
%%         Arity is Ari + 1,
%% 	Cls=[(directive(type(Name/Arity)),DK)|Cls1].
%% 
%% :- prop internal_type_disjunction/1 + regtype # "A Type defined in
%% 	internal rule format.".
%% 
%% internal_type_disjunction(_).

:- prop clause_list/1 + regtype # "A list of clauses defining a
	predicate.".

clause_list(_).

%% :- pred one_typedef_to_pred(+Def, +Pred, -Cls)
%% 
%% => internal_type_disjunction * atm * clause_list
%% 
%% # "Translates a type defined in internal rule format (@var{Def}) into
%%    predicate format, and put the clauses defining the predicate 
%%    (named @var{Pred}) in @var{Cls}.".
%% 
%% one_typedef_to_pred([Or|Ors], Pred, [Clause|Cls]):- 
%% 	!,
%% 	debug_message("one_disjunct_to_clause(~q, ~q, ~q)", [Or, Pred, Clause]),
%% 	one_disjunct_to_clause(Or, Pred, Clause),
%% 	debug_message("one_disjunct_to_clause(~q, ~q, ~q)", [Or, Pred, Clause]),
%% 	one_typedef_to_pred(Ors, Pred, Cls).
%% one_typedef_to_pred([], _Pred, []).
%% 
%% rule_to_pred_one((typedef Pred ::= Def), Cls):-
%%         debug_message("typedef_to_pred(~q, ~q, ~q)", [Def, Pred, Cls0]),
%% 	typedef_to_pred(Def, Pred, Cls0),
%%         debug_message("typedef_to_pred(~q, ~q, ~q)", [Def, Pred, Cls0]),
%% 	debug_message("rewrite_cls(~q, ~q)", [Cls0, Cls1]),
%%         rewrite_cls(Cls0, Cls1),
%%         debug_message("rewrite_cls(~q, ~q)", [Cls0, Cls1]),
%% 	null_directive_key(DK),
%%         functor(Pred, Name, Ari),
%%         Arity is Ari + 1,
%% 	Cls=[(directive(type(Name/Arity)),DK)|Cls1].

% PARAMETRIC TYPES

remove_parametric_types_from_rules:-
    get_all_par_type_symbols_in_renamings_pgm(PList_pgm),
%    get_all_par_type_symbols_in_renamings_lib(PList_lib),
    get_all_defined_type_symbols_pgm(NPList_pgm),
%    get_all_defined_type_symbols_lib(NPList_lib),
%    append(PList, NPList, TypeSymbolList),  
    append(PList_pgm, NPList_pgm, TypeSymbolList),  
%    append(NPList_lib, TypeSymbolList_pgm, TypeSymbolList0),  
%    append(PList_lib, TypeSymbolList0, TypeSymbolList),  
    compute_transitive_closure(TypeSymbolList, [], TransClosure),
    remove_parametric_types_from_rules_2(TransClosure, NonParRules),
%    get_pgm_nonparrules(NonParRules0,TypeSymbolList_pgm,NonParRules),
    retractall_fact(pgm_typedef(_, _)),
    asserta_type_rule_list(NonParRules).

get_all_par_type_symbols_in_renamings_pgm(PList):-
    setof(ParTyp, N^pgm_param_type_symbol_renaming(ParTyp, N), PList), !.
get_all_par_type_symbols_in_renamings_pgm([]).

%% get_all_par_type_symbols_in_renamings_lib(PList):-
%%     setof(ParTyp, N^lib_param_type_symbol_renaming(ParTyp, N), PList), !.
%% get_all_par_type_symbols_in_renamings_lib([]).

get_all_defined_type_symbols_pgm(NPList):-
    setof(Typ, D^pgm_typedef(Typ, D), NPList), !.
get_all_defined_type_symbols_pgm([]).

% get_all_defined_type_symbols_lib(NPList):-
%     setof(Typ, D^lib_typedef(Typ, D), NPList), !.
% get_all_defined_type_symbols_lib([]).

:- pred remove_parametric_types_from_rules_2(?TypSymbols, ?NonParRules)

# "@var{NonParRules} is a list of type rules which do not contain
   parametric types and are equivalent to the rules defining the
   (possibly parametric) type symbols in the list @var{TypSymbols}.".

remove_parametric_types_from_rules_2([], []).
remove_parametric_types_from_rules_2([TypSymb|IL], [Rule|L]):-
  remove_parametric_types_from_one_rule(TypSymb, Rule),
  remove_parametric_types_from_rules_2(IL, L).

remove_parametric_types_from_one_rule(TypSymb, NonParamRule):-
   get_type_definition(TypSymb, Defin),  
   set_type_symbol_renaming(TypSymb, NonParamTypSymbol), 
   remove_parametric_types_from_union(Defin, NonParamDef),
   type_rule_symbol_def(NonParamRule, NonParamTypSymbol, NonParamDef).


set_type_symbol_renaming(TypSymbol, TypSymbol):-
    non_par_rule_type_symbol(TypSymbol), !.
set_type_symbol_renaming(ParamTypSymbol, NonParamTypSymbol):-
    par_rule_type_symbol(ParamTypSymbol),
    !,
    ground_params_if_any(ParamTypSymbol),
    (exist_type_symbol_renaming(ParamTypSymbol, NoParRenaming)
      -> NonParamTypSymbol = NoParRenaming
      ;
         new_param_type_symbol(NewNoParRenaming), 
         asserta_fact(pgm_param_type_symbol_renaming(ParamTypSymbol, NewNoParRenaming)),
         NonParamTypSymbol = NewNoParRenaming).
 
ground_params_if_any(ParSymbol) :- 
	varset(ParSymbol,Params),
	ground_params(Params).

ground_params([]).
ground_params([Param|Params]) :-
	new_type_parameter(Param),
	ground_params(Params).

exist_type_symbol_renaming(ParamTypSymbol, NoParRenaming):-
   param_type_symbol_renaming(ParamTypSymbol, NoParRenaming).

remove_parametric_types_from_union([], []). 
remove_parametric_types_from_union([ParType|ParDefin], 
                                   [NonParType|NonParDefin]):-
   !,
   remove_one_parametric_type(ParType, NonParType),
   remove_parametric_types_from_union(ParDefin, NonParDefin).

remove_one_parametric_type(Type, NType):-
   rule_type_symbol(Type), 
   !,
   set_type_symbol_renaming(Type, NType).
remove_one_parametric_type(Type, NType):-
   compound_pure_type_term(Type, Comp, Name, Arity),
   !,
   functor(NComp, Name, Arity),
   compound_remove_parametric_types(Arity, Comp, NComp), 
   construct_compound_pure_type_term(NComp, NType).
remove_one_parametric_type(Type, Type).
   
compound_remove_parametric_types(0, _Comp, _NComp):-!.
compound_remove_parametric_types(ArgNum, Comp, NComp):-
       ArgNum > 0, 
       arg(ArgNum, Comp, Arg),
       remove_one_parametric_type(Arg, NArg),
       arg(ArgNum, NComp, NArg),
       NArgNum is ArgNum - 1,
       compound_remove_parametric_types(NArgNum, Comp, NComp).

:- pred rewrite_as_parametric_rules(+NonParRules, +ParRules, -TypeSymbols)

# "Rewrites the rules @var{NonParRules} using the set of parametric
   type rules @var{ParRules}. var{TypeSymbols} is a list containing
   the type symbols which have been rewritten as parametric types.".

 %% rewrite_as_parametric_rules(NonParRules, ParRules):-
 %%     rewrite_as_parametric(NonParRules, ParRules, Bindings),
 %%     check_equiv_bindings(Bindings).

 %% consistent_bindings([]).
 %% consistent_bindings([(PType, NType)|Bindings]):-
 %%    one_consistent_binding(PType, NType),
 %%    consistent_bindings(Bindings).

 %% check_equiv_bindings([]).
 %% check_equiv_bindings([(NType1, NType2)|Bindings]):-
 %%    dz_equivalent_types(NType1, NType2),
 %%    check_equiv_bindings(Bindings).

rewrite_as_parametric_rules([], _ParRules, []).
rewrite_as_parametric_rules([NPRule|NonParRules], ParRules, Symbols):-
    (rewrite_as_parametric_rule_list(ParRules, NPRule, TypeSymbol)
     -> Symbols = [TypeSymbol|RSymbols]
     ;  Symbols = RSymbols),
    rewrite_as_parametric_rules(NonParRules, ParRules, RSymbols).

rewrite_as_parametric_rule_list([Rule|RestRul], NonParRule, TypeSymbol):-
    (rewrite_one_rule_as_parametric(Rule, NonParRule, NTypeSymbol)
      -> TypeSymbol = NTypeSymbol
      ; 
      rewrite_as_parametric_rule_list(RestRul, NonParRule, TypeSymbol)).
 
 %% one_consistent_binding(PType, NType, InBind, Bind):-
 %%    get_par_type_definition(PType, PDefin),
 %%    get_NO_par_type_definition(NType, NDefin),
 %%    replace_type_symbol(PDefin, PType, NType, RPDefin),
 %%    order_type_defin(RPDefin, OrdPDefin),
 %%    !,
 %%    rewrite_defin(OrdPDefin, NDefin, InBind, Bind).
 %% 

 %% NOTE: It is possible that new non-parametric type symbols are created, but
 %% all of them necessarily are renamings of parametric type symbol
 %% instances (note that if there is a non-parametric type symbol in the
 %% type rule defining a parametric type symbol it has necessarily be
 %% defined by a type rule.

rewrite_one_rule_as_parametric(ParRule, NonParRule, NTypeSymbol):-
        copy_term(ParRule, Rule),
        non_parametric_type_rule_symbol_def(NonParRule, NTypeSymbol, NDefin),
        parametric_type_rule_symbol_def(Rule, PTypeSymbol, PDefin),
        order_type_defin(PDefin, OrPDefin), !, 
        rewrite_defin(OrPDefin, NDefin), 
        ground(PTypeSymbol),
        assert_param_type_rule_instance(PTypeSymbol, NtypSymbol1),
        dz_equivalent_types(NTypeSymbol, NtypSymbol1),
        assert_and_propagate_type_equivalence(NTypeSymbol, NtypSymbol1).
        % actualize_renaming(NTypeSymbol, NtypSymbol1).

 %% actualize_equiv_types(NTypeSymbol, NtypSymbol1):-
 %%    retract(equiv_type(NTypeSymbol, _)),
 %%    asserta(equiv_type(NTypeSymbol, NtypSymbol1)).

 %% Version 15-1-97
 %% actualize_renaming(NTypeSymbol, NtypSymbol1):-
 %%    equiv_type_1(NTypeSymbol, EquivNTypeSymbol),
 %%    retract(equiv_type(NtypSymbol1, _)),
 %%    asserta(equiv_type(NtypSymbol1, EquivNTypeSymbol)),
 %%    retract(param_type_symbol_renaming(ParTyp, NtypSymbol1)),
 %%    assert(param_type_symbol_renaming(ParTyp, EquivNTypeSymbol)).


 %% rewrite_one_rule_as_parametric(ParRule, NonParRule):-
 %%    copy_term(ParRule, Rule),
 %%    non_parametric_type_rule_symbol_def(NonParRule, NTypeSymbol, NDefin), 
 %%    parametric_type_rule_symbol_def(Rule, PTypeSymbol, PDefin),
 %%    replace_type_symbol(PDefin, PTypeSymbol, NTypeSymbol, RPDefin),   
 %%    order_type_defin(RPDefin, OrPDefin),
 %%     % order_type_defin(PDefin, OrPDefin),
 %%    % replace_type_symbol(NDefin, NTypeSymbol, PTypeSymbol, RNDefin),
 %%    !,
 %%    rewrite_defin(OrPDefin, NDefin),
 %%    % rewrite_defin(OrPDefin, RNDefin),
 %%    ground(PTypeSymbol),
 %%    assert_param_type_instance(PTypeSymbol, NtypSymbol1),
 %%    dz_equivalent_types(NTypeSymbol, NtypSymbol1),
 %%    assert_and_propagate_type_equivalence(NTypeSymbol, NtypSymbol1).

   
rewrite_defin([], []).
rewrite_defin([PType|PDefin], NDefin):-
        unify_with_some_type(NDefin, PType, RestNDefin),
        rewrite_defin(PDefin, RestNDefin).

unify_with_some_type([NType|NDefin], PType, NDefin):-
        type_unify(NType, PType), !.
unify_with_some_type([NType|NDefin], PType, [NType|RestNDefin]):-
        unify_with_some_type(NDefin, PType, RestNDefin).

type_unify(NType, PType):-
    var(PType),
    !,
    NType = PType.
type_unify(NType, PType):- 
    NType == PType,
    !.
% type_unify(Type, Type, Bind, Bind):-!.
type_unify(NType, PType):-
   compound_pure_type_term(NType, NComp, Name, Arity),
   compound_pure_type_term(PType, PComp, Name, Arity), % PType is not a variable.
   !,
   compound_type_unify(Arity, NComp, PComp).
type_unify(NType, PType):-
   non_par_rule_type_symbol(NType),
   par_rule_type_symbol(PType), !.
type_unify(NType, PType):-
   non_par_rule_type_symbol(NType),
   non_par_rule_type_symbol(PType).

compound_type_unify(0, _NComp, _PComp):-!.
compound_type_unify(ArgNum, NComp, PComp):-
       ArgNum > 0, 
       arg(ArgNum, NComp, NArg),
       arg(ArgNum, PComp, PArg),
       type_unify(NArg, PArg),
       NArgNum is ArgNum - 1,
       compound_type_unify(NArgNum, NComp, PComp).

order_type_defin(PDefin, OrPDefin):-
    partition_ground(PDefin, GrounDef, Rest),
    append(GrounDef, Rest, OrPDefin).

partition_ground([], [], []).
partition_ground([Type|PDefin], [Type|GrounDef], Rest):-
     ground(Type), !, 
     partition_ground(PDefin, GrounDef, Rest).
partition_ground([Type|PDefin], GrounDef, [Type|Rest]):-
     partition_ground(PDefin, GrounDef, Rest).

% Remove non-parametric rules which can be colapsed to a parametric
% rule, i.e. remove the rule defining NoParRenaming if the fact
% param_type_symbol_renaming(ParamTypSymbol, NoParRenaming) is in the 
% database.
