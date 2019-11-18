%% :- pred regular_type_pred_definition(+Clauses)
%% 
%% # "Checks that @var{Clauses} define a valid regular type.".
%% 
%% regular_type_pred_definition(Clauses):- 
%%    regular_type_pred_definition_e(Clauses, Error),
%%    !,
%%    (nonvar(Error) -> 
%%       compiler_error(Error),
%%       fail
%%       ;
%%       true).
%% regular_type_pred_definition(Clauses):-
%%    compiler_error(type_pred_syntax(Clauses)),
%%    fail.
%% 
%% :- pred assert_type_definition(+TypSymbol, +Defin)
%% 
%% # "Assert the type rule defining @var{TypSymbol} as @var{Defin} in the
%%   typeslib module. Admits both parametric (containing variables) and
%%   non-parametic definitions.".
%% 
%% assert_type_definition(TypSymbol, Defin):-
%%     internal_union_translate(InDefin, Defin),
%%     type_rule_symbol_def(Rule, TypSymbol, InDefin),
%%     assertz_typedef_or_paramtypedef(Rule).


 %% Changed definition PLG 17-Dec-2002
 %% assert_param_type_instance(TypeInstance, NonParSymbol):-
 %%     set_type_symbol_renaming(TypeInstance, NonParSymbol).

% Pedro: puede haber llamadas a este con un Prop que ya se le ha llamado 
% antes (con lo que no hay que hacer nada excepto devolver NonParSymbol) --PBC
assert_param_type_instance(Prop, NonParSymbol):-
  remove_first_argument(Prop, TypeInstance),
  assert_param_type_rule_instance(TypeInstance, NonParSymbol).

:- pred assert_param_type_rule_instance(+TypeInstance, -NonParTypSymbol)
       
# "Takes a parametric rule type symbol instance @var{TypeInstance} and
assert a type rule (in the module typeslib) in which the parametric
type rule type symbols have been removed.
Before calling this predicate it is neccessary to have all the
parametric type rules asserted in the typeslib module.
Returns the type symbol of this asserted rule in @var{NonParTypSymbol}.
 It also assert in the module typeslib 
a fact param_type_symbol_renaming(@var{TypeInstance}, @var{NonParTypSymbol}) 
representing that @var{NonParTypSymbol} is a renaming of @var{TypeInstance} 
(@var{NonParTypSymbol} is defined by the asserted non-parametric type rule).".

assert_param_type_rule_instance(TypeInstance, NonParSymbol):-
    compute_transitive_closure([TypeInstance], [], TransClosure),
    remove_parametric_types_from_rules_2(TransClosure, NonParRules),
    assert_rules_if_not_exist(NonParRules), 
    param_type_symbol_renaming(TypeInstance, NonParSymbol).

%% Added definition PLG 17-Dec-2002
%% retractall_and_assert_rules([typedef(TypSymbol, Defin)|Types]):-
%%         retractall(typedef(TypSymbol, _)),
%%      assertz(typedef(TypSymbol, Defin)),
%%      retractall_and_assert_rules(Types).
%% retractall_and_assert_rules([]).


% Note: make sure that types rules created during intersection are in
% a suitable format for calling dz_type_included/2 (i.e. unfolded).

%% type_assignments_included(TypeList0, Goal0, TypeList1, Goal1):-
%%         lit_type_to_pure_type_lit(Goal0, TypeList0, Type0), 
%%         lit_type_to_pure_type_lit(Goal1, TypeList1, Type1), 
%%         ^(Type0) = PureType0,
%%         ^(Type1) = PureType1,
%%  %%         construct_compound_pure_type_term(Type0, PureType0),
%%  %%         construct_compound_pure_type_term(Type1, PureType1),
%%         types_are_included(PureType0, PureType1).
%% 
%% type_assignments_incompatible(TypeList0, Goal0, TypeList1, Goal1):-
%%         lit_type_to_pure_type_lit(Goal0, TypeList0, Type0), 
%%         lit_type_to_pure_type_lit(Goal1, TypeList1, Type1), 
%%         ^(Type0) = PureType0,
%%         ^(Type1) = PureType1,
%%  %%         construct_compound_pure_type_term(Type0, PureType0),
%%  %%         construct_compound_pure_type_term(Type1, PureType1),
%%      types_are_incompatible(PureType0, PureType1).
%% 
%% type_terms_included(Type0, Type1):-
%%         ^(Type0) = PureType0,
%%         ^(Type1) = PureType1,
%%  %%         construct_compound_pure_type_term(Type0, PureType0),
%%  %%         construct_compound_pure_type_term(Type1, PureType1),
%%         dz_type_included(PureType0, PureType1).
%% 
%% type_terms_incompatible(Type0, Type1):-
%%         ^(Type0) = PureType0,
%%         ^(Type1) = PureType1,
%%  %%         construct_compound_pure_type_term(Type0, PureType0),
%%  %%         construct_compound_pure_type_term(Type1, PureType1),
%%      types_are_incompatible(PureType0, PureType1).

types_are_incompatible(Typ1, Typ2):-
     init_before_type_intersection,
     typeslib:type_intersection(Typ1, Typ2, Intersec), 
     !,  
     debug_message("between here",[]),  
     (is_empty_type(Intersec) -> 
        debug_message("and here",[]),
        after_type_intersection
      ; 
     debug_message("and here",[]),
     after_type_intersection, !, fail),
     debug_message("or even here",[]).

%% types_are_included(Type1, Type0):-
%%      dz_type_included(Type1, Type0).
%% 
%% 
%%  %% types_are_included(Call, Body, TypeTerm):-
%%  %%      init_before_type_intersection,
%%  %%      create_type_term(Call, Body, TypeTerm).
%%  %%      % after_type_intersection.
%% 
%% %%
%% %% Create a type term from a type declaration.
%% %%
%% 
%% create_type_term(Body, Call, TypeTerm):-
%%      get_types_of_vars(Body, Types),
%%      var_list(Call, VarList),
%%      intersec_types_1(VarList, Types, [], TypeAss),
%%      replace_vars_by_types(TypeAss, Call, TypeTerm). 
%% 
%% get_types_of_vars((Lit,Body), Types):- !,
%%         get_type_of_one_var(Lit, Var, Type),
%%         insert_type(Types, Var, Type),
%%      get_types_of_vars(Body, Types).
%% get_types_of_vars(Lit, Types):-
%%         get_type_of_one_var(Lit, Var, Type),
%%         insert_type(Types, Var, Type).
%% 
%% 
%% create_type_term_l(Body, Call, TypeTerm):-
%%      get_types_of_vars_l(Body, Types),
%%      var_list(Call, VarList),
%%      intersec_types_1(VarList, Types, [], TypeAss),
%%      replace_vars_by_types(TypeAss, Call, TypeTerm). 
%% 
%% get_types_of_vars_l([Lit|Body], Types):- !,
%%         get_type_of_one_var(Lit, Var, Type),
%%         insert_type(Types, Var, Type),
%%      get_types_of_vars_l(Body, Types).
%% get_types_of_vars_l([], _Types).
%% 
%% get_type_of_one_var(Lit, Var, Type1):-
%%      functor(Lit, Type, 1),
%%         arg(1, Lit, Var),
%%      internal_type_translate(Type1, Type).
%% 
%% % Variables which do not have type are assigned the top type.
%% intersec_types_1(Var_List, _Var_Types, OTypeAss, OTypeAss):-
%%    var(Var_List), !.
%% intersec_types_1(Var_List, Var_Types, ITypeAss, OTypeAss):-
%%    nonvar(Var_List), 
%%    Var_List = [Var|List],
%%    find_list_entry(Var_Types, Var, Entry),
%%    (var(Entry) -> Types = _
%%                   ;
%%                   Entry = vt(_, Types)),
%%    set_top_type(Top),
%%    intersec_type_list_1(Types, Top, LType),
%%    % \+ bot_type(LType),
%%    intersec_types_1(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).
%% 
%% intersec_type_list_1(Type_List, Type, Type):-
%%    var(Type_List), !.
%% intersec_type_list_1(Type_List, InType, OutType):-
%%    nonvar(Type_List),
%%    Type_List = [Type | List],
%%    typeslib:type_intersection(InType, Type, Intersec),
%%    (is_empty_type(Intersec) -> 
%%       set_bottom_type(OutType) % , retract_1 -PL
%%       ;
%%       intersec_type_list_1(List, Intersec, OutType)).
%% 
%% 
%% % New
%% create_predicate_type(Body, Call, PredType):-
%%      Call =.. [PredName|VarList],
%%      create_type_list(VarList, Body, TypeList),
%%      PredType =.. [PredName|TypeList].
%% 
%% create_type_list([Var|VarList], Body, [Type|TypeList]):-
%%      find_declaration_in_list(Body, Var, Type),
%%      create_type_list(VarList, Body, TypeList).
%% 
%% %From infernf
%% 
%% find_declaration_in_list([], _Var, Declar):-!, 
%%       set_top_type(Declar).
%% find_declaration_in_list([Term|List], Var, Declar):-
%%       (is_a_type_declaration(Term, Var, F) ->
%%            % type_dec_translate(F, Declar) % infernf 
%%            type_dec_translate_2(F, Declar) % new
%%          ; find_declaration_in_list(List, Var, Declar)
%%       ).                   
%% 
%% % New
%% type_dec_translate_2(T1, T2):-
%%      ground_type(T1),
%%      !,
%%      set_top_type(T2). 
%% type_dec_translate_2(T1, T2):-
%%      var_type(T1),
%%      !,
%%      set_top_type(T2). 
%% type_dec_translate_2(ground, T2):-
%%      set_top_type(T2). 
%%  
%% 
%% 
%% %From infernf
%% % WARNING!: any declaration of arity 1 is considered a type.
%% % Perhaps we should escape type symbols instead of functors.
%% is_a_type_declaration(Lit, Var, F):-
%%   nonvar(Lit),
%%   functor(Lit, F, 1),
%%   arg(1, Lit, Arg),
%%   Arg == Var,
%%   !. 
%% is_a_type_declaration(Lit, Var, Var_Type):-
%%   nonvar(Lit),
%%   functor(Lit, regtype, 2),
%%   arg(1, Lit, Arg),
%%   Arg == Var,
%%   arg(2, Lit, Var_Type). 

