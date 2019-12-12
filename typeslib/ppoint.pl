% (included from typeslib.pl)

% Begin equal to non-failure analysis.

%% Operations on type assignments.

 %% find_type(+TypeAss, +Var, -Type)
 %% TypeAss: a type assignment.
 %% Var: a variable.
 %% Type: a type.
 %% Purpose: finds the type Type of variable Var in TypeAss.

find_type([Var:Type | _Rest], IVar, OutType) :- 
    Var == IVar,!, OutType = Type.
find_type([Var:_Type | Rest], IVar, OutType) :- 
    Var \== IVar, 
    find_type(Rest, IVar, OutType).
%%

:- pred compute_types(+Var_List, +Term_List, +Type_Ass, -Types)

# "Given the substitution which can be represented as subs(@var(Var_List),
@var{Term_List}), computes the type corresponding to each variable in the
list of terms @var{Term_List}, and store it in the data structure @var{Types}.
@var{Types} have the structure [vt(Var1, TypeList1), ..., vt(VarN,
TypeListN)|_], where TypeListN is the list of types corresponding to
variable VarN.".

 %% Note: we assume that bottom types are removed (and do not have any
 %% type rule defining a bottom type), and that type symbols
 %% equivalent to top are of the form T -> [top].

compute_types(Var_List, Term_List, _Type_Ass, _Types):-
   var(Var_List), var(Term_List), !.
compute_types(VL, TL, Type_Ass, Types):-
   nonvar(VL), nonvar(TL),
   VL = [Var|Var_List], TL = [Term|Term_List],
   (find_type(Type_Ass, Var, Type) -> true ; set_top_type(Type)),
   compute_type(Term, Type, Types),
   compute_types(Var_List, Term_List, Type_Ass, Types).

% Note: \+ bot_type(Type) will always fail if we do not allow to have empty
% types in type assignments.

compute_type(Term, Type, Types):-
    equivalent_to_top_type(Type), 
    % top_type(Type), 
    !, 
    insert_top_type(Term, Types).
compute_type(Term, Type, Types):-
    var(Term), 
    !, 
    insert_type(Types, Term, Type).
compute_type(Term, Type, _Types):-
    atomic(Term), 
    !, 
    ( belongs_to_type(Term, Type) -> true
    ; var_type(Type) % TODO:[new-resources] for etermsvar
    ).
 %%     escaped_type(Term, TypeTerm),
 %%     dz_type_included(TypeTerm, Type).
compute_type(Term, Type, Types):-
    nonvar(Term), 
    functor(Term, F, A),
    get_compatible_types(F/A, Type, [], CompTypes),
    \+ (CompTypes = []),
    (there_are_only_one_compa_type(CompTypes, CompTerm) -> 
    compute_args_type(A, Term, CompTerm, Types)
    ;
    insert_top_type(Term, Types)).

there_are_only_one_compa_type(CompTypes, CompTerm):-
  CompTypes = [CType],
  compound_pure_type_term(CType, CompTerm, _Name, _Arity).
  
compute_args_type(A, _Term, _CompType, _Types):-
   A =:= 0, !.
compute_args_type(A, Term, CompType, Types):-
   A > 0, 
   arg(A, Term, Term_Arg),
   arg(A, CompType, Type_Arg), 
   compute_type(Term_Arg, Type_Arg, Types),
   A1 is A - 1, 
   compute_args_type(A1, Term, CompType, Types).

% A type is equivalent to top, either if it is top, or is defined as top.  
equivalent_to_top_type(Type):- 
    type_parameter(Type),!,
    fail.
equivalent_to_top_type(Type):- 
   top_type(Type),
   !.
equivalent_to_top_type(Type):-
   non_par_rule_type_symbol(Type),
   get_NO_par_type_definition(Type, [Type1]),
   top_type(Type1).

 %% equivalent_to_top_type(Type):- 
 %%     set_top_type(TopType),
 %%     dz_type_included(Type, TopType).

%% insert_top_type(Term, Types):
%% Purpose: Adds the type "top" to the list of types (expressed in Types) 
%% corresponding to each variable appearing in Term.
 
insert_top_type(Term, Types):-
   (var(Term) ->
      set_top_type(TopType),
      insert_type(Types, Term, TopType);
      functor(Term, _F, A),
      insert_top_type_3(A, Term, Types)
   ).

insert_top_type_3(A, Term, Types):-
  (A = 0 -> true;
   arg(A, Term, Term_Arg),
   insert_top_type(Term_Arg, Types),
   A1 is A - 1,
   insert_top_type_3(A1, Term, Types)
  ).

insert_type(NVarList, Var, NVar):- 
    insert_list_entry(NVarList, Var, vt(Var, VList)),
    ins_without_dup(VList, NVar).

insert_list_entry(VT, Var, Entry) :- 
    var(VT), !,
    Entry = vt(Var, _),
    VT = [Entry|_].
insert_list_entry(VT, Var, Entry) :- 
    nonvar(VT),
    VT = [E|_],
    E = vt(EVar, _),
    EVar == Var, !,
    Entry = E.
insert_list_entry(VT, Var, Entry) :- 
    nonvar(VT),
    VT = [E|S],
    E = vt(EVar, _),
    EVar \== Var,
    insert_list_entry(S, Var, Entry).

%% %% Operations on type assignments.
%% 
%% % intersect_type_assigments(TypeAss1, TypeAss2, OutTypeAss)
%% 
%% intersect_type_assigments([], _TypAss2, []):-!.
%% intersect_type_assigments([Var:Type1|TypAss1], TypAss2, [Var:OutType|OutTypAss]):-
%%    (find_type(TypAss2, Var, Type2) ->
%%       type_intersection_2(Type1, Type2, OutType)
%%       ;
%%       OutType = Type1),
%%    intersect_type_assigments(TypAss1, TypAss2, OutTypAss).

% End equal to non-failure analysis.

% Begin Not equal to non-failure analysis.


 %% get_compatible_types(+F/+A, +Type, -Type1, -RestTypes).
 %% F/A: functor/arity of the subtype searched.
 %% Type: Type in which the subtype is searched.
 %% Type1: subtype of Type with functor/arity F/A.
 %% RestTypes: rest of types in the definition of Type. It's a list.
 %% Preconditions:
 %% TermAri > 0
 %% Comments: Type1 and the types in RestTypes are a partition of Type
 %%           (this means that they are disjoint). Fails if there is
 %%           no subtype which is a compound pure type term in Type,
 %%           in particular, if type is top, bottom, or a base type symbol.
 %%          
 %%  IMPORTANT: It is possible to write an specialized version asuming
 %%  that the rules are unfolded (or simplified without bottom, and
 %%  top). This version which does not expand the user defined type symbolS.

get_compatible_types(TermFun/TermAri, Type, _Seen, CompType):-
   compound_pure_type_term(Type, _Term, Name, Arity),
   !,
   Name = TermFun, 
   Arity = TermAri,
   CompType = [Type].
get_compatible_types(TermFun/TermAri, Type, Seen, CompTypes):-
   non_par_rule_type_symbol(Type),
   !,
   get_compatible_types_from_type_symbol(TermFun/TermAri, Type, Seen, CompTypes).
get_compatible_types(TermFun/TermAri, Type, _Seen, [CompType]):-
   ground_type(Type),
   !,
   create_compound_with_ground_args(TermAri, TermFun, CompType).
get_compatible_types(TermFun/TermAri, Type, _Seen, [CompType]):-
   struct_type(Type),
   !,
   create_compound_with_top_args(TermAri, TermFun, CompType).
get_compatible_types(TermFun/TermAri, Type, _Seen, [CompType]):-
   var_type(Type), % TODO:[new-resources] support for etermsvar
   !,
   create_compound_with_var_args(TermAri, TermFun, CompType).


create_compound_with_top_args(TermAri, TermFun, CompType):-
   create_top_sequence(TermAri, TopArgs),
   Compound =.. [TermFun|TopArgs],
   construct_compound_pure_type_term(Compound, CompType).

create_compound_with_ground_args(TermAri, TermFun, CompType):-
   create_ground_sequence(TermAri, GndArgs),
   Compound =.. [TermFun|GndArgs],
   construct_compound_pure_type_term(Compound, CompType).

% TODO:[new-resources] support for etermsvar
create_compound_with_var_args(TermAri, TermFun, CompType):-
   create_var_sequence(TermAri, VarArgs),
   Compound =.. [TermFun|VarArgs],
   construct_compound_pure_type_term(Compound, CompType).

get_compatible_types_from_type_symbol(_, Type, Seen, _CompTypes):-
   member_0(Type, Seen),
   !,
   fail.     
get_compatible_types_from_type_symbol(TermFun/TermAri, Type, Seen, CompTypes):-
   get_NO_par_type_definition(Type, Defin),
   get_compatible_types_from_union(Defin, TermFun/TermAri, [Type|Seen], CompTypes).

get_compatible_types_from_union([], _, _Seen, []):-!.
get_compatible_types_from_union([Type|TypUnion], TermFun/TermAri, Seen, CompTypes):-
  (get_compatible_types(TermFun/TermAri, Type, Seen, CTypes)
     -> append(CTypes, RestCompTypes, CompTypes)
      ; CompTypes = RestCompTypes),
  get_compatible_types_from_union(TypUnion, TermFun/TermAri, Seen, RestCompTypes).

%%


get_var_types_by_unification([], [], _Types):-
   !.
get_var_types_by_unification([Type|Type_List], [Term|Term_List], Types):-
   compute_type(Term, Type, Types),
   get_var_types_by_unification(Type_List, Term_List, Types).

% Variables which do not have type are assigned the top type.
intersec_types_2([], _Var_Types, OTypeAss, OTypeAss):-
   !.
intersec_types_2([Var|List], Var_Types, ITypeAss, OTypeAss):-
   find_list_entry(Var_Types, Var, Entry),
   (var(Entry) -> Types = _
              ;
              Entry = vt(_, Types)),
   set_top_type(Top),
   intersec_type_list_2(Types, Top, LType),
   % \+ bot_type(LType),
   intersec_types_2(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).

intersec_type_list_2(Type_List, Type, Type):-
   var(Type_List), 
   !.
intersec_type_list_2(Type_List, InType, OutType):-
   nonvar(Type_List),
   Type_List = [Type|List],
   type_intersection_2(InType, Type, Intersec),
   intersec_type_list_2(List, Intersec, OutType).

type_intersection_2(Type1, Type2, Intersect):-
   dz_type_included(Type1, Type2),
   !,
   Intersect = Type1.
type_intersection_2(Type1, Type2, Intersect):-
   dz_type_included(Type2, Type1),
   !,
   Intersect = Type2.
type_intersection_2(Type1, Type2, Intersect):-
    debug_message("Performing full intersection of ~q and ~q.", [Type1, Type2]),
    pp_type_intersection(Type1, Type2, Intersect),
    debug_message("Intersection of ~q and ~q is ~q.", [Type1, Type2, Intersect]).
 %% type_intersection_2(Type1, Type2, Intersect):-
 %%     Intersect = Type2,
 %%     warning_message("No inclusion relationship between types ~q and ~q.",[Type1, Type2]),
 %%     warning_message("Assumed that the intersection is ~q. This can be improved by performing full intersection.", [Intersect]).
   

pp_type_intersection(Typ1, Typ2, Inter):-
     typeslib:type_intersection(Typ1, Typ2, Intersec), 
     !, 
     (is_empty_type(Intersec) -> 
        clean_after_empty_pp_type_intersection,
        set_bottom_type(Inter)
        ; 
        simplify_types_after_pp_type_intersection,
        replace_one_equiv_type(Intersec, Inter)).

generate_a_type_assigment(Type_List, Term_List, TypeAss):- 
      varset(Term_List, Term_Vars),
      get_var_types_by_unification(Type_List, Term_List, Types),
      intersec_types_2(Term_Vars, Types, [], TypeAss).

 %% generate_a_type_assigment(Type_List, Term_List, TypeAss):- 
 %%    varset(Term_List, Term_Vars),     
 %%    (get_var_types_by_unification(Type_List, Term_List, Types)
 %%       -> intersec_types_2(Term_Vars, Types, [], TypeAss)
 %%        ; create_bottom_type_ass(Term_Vars, TypeAss)).

%% :- pred project_literal_type(Literal, PredType, InSubst, OutSubst)
%% 
%% # "Get the type of the variables in @var{Literal} by performing a type
%%    unification with the typing @var{PredType}, and put these types in
%%    the output abstract type substitution @var{OutSubst}. Fails if type
%%    unification fails, in which case @var{OutSubst} is set to the
%%    bottom substitution.".
%% 
%% project_literal_type(Literal, _PredType, InSubst, OutSubst):-
%%       varset(Literal, []),
%%       !,
%%       debug_message("Literal ~q has no variables.", [Literal]),
%%       OutSubst = InSubst.
%% project_literal_type(Literal, PredType, InSubst, OutSubst):-
%%       debug_message("project_literal_type(~q, ~q,", [Literal, PredType]),
%%       debug_message("~q,", [InSubst]),
%%       debug_message("~q).", [OutSubst]),
%%       %
%%       % Get the types of the variables in Literal by performing type unification with PredType. 
%%       Literal =.. [_F|Args], % Get the arguments of Literal.
%%       % Literal =.. [_F|LitArgs], % Get the arguments of Literal.
%%       % type_escape_term_list(LitArgs, Args),
%%       PredType =.. [_P|Types], % Get the arguments of PredType.
%%       generate_a_type_assigment(Types, Args, TypeAss),
%%       %
%%       % TypAss contains an item Variable:Type for each variable in Args (and only for these variables).  
%%       get_data_from_substitution(InSubst, Var_List, _InType_List, Term_List, InTypeAss),
%%       debug_message("Intersecting type assigments of the input substitution and the projection"),
%%       %% Note: is really neccessary this intersection? PLG
%%       debug_message("intersect_type_assigments(~q, ~q, ~q)", [InTypeAss, TypeAss, OutTypeAss]),
%%       intersect_type_assigments(InTypeAss, TypeAss, OutTypeAss),
%%       % OutTypeAss has the same variables that InTypeAss. 
%%       debug_message("intersect_type_assigments(~q, ~q, ~q)", [InTypeAss, TypeAss, OutTypeAss]),
%%       rewrite_terms_as_pure_type_terms(Term_List, OutTypeAss, OutType_List),  
%%       rewrite_as_type_symbols(OutType_List, OutTypeSymbolList),
%%       create_a_type_substitution(Var_List, OutTypeSymbolList, Term_List, OutTypeAss, OutSubst). 

type_escape_term_list([Arg|LitArgs], [EscArg|RArgs]):-
     !,
     escaped_type(Arg, EscArg),
     type_escape_term_list(LitArgs, RArgs).
type_escape_term_list([], []).

%% perform_one_type_unification(Unification, Subst, OutSubst):-
%%       get_data_from_substitution(Subst, Var_List, Type_List, Term_List, _TypeAss),
%%       arg(1, Unification, A1),
%%       arg(2, Unification, A2),
%%       % perform_unification(A1, A2),
%%       (A1 = A2 ->
%%             generate_a_type_assigment(Type_List, Term_List, TypeAss1),
%%             rewrite_terms_as_pure_type_terms(Term_List, TypeAss1, PTypeList),
%%             rewrite_as_type_symbols(PTypeList, TypeSymbol_List),
%%             create_a_type_substitution(Var_List, TypeSymbol_List, Term_List, TypeAss1, OutSubst)
%%             ;
%%             set_bottom_substitution(Var_List, OutSubst)).
%% 
%% rewrite_terms_as_pure_type_terms([], _TypeAss, []):-!.
%% rewrite_terms_as_pure_type_terms([Term|TermList], TypeAss, [PureTypeTerm|PTypeList]):-
%%     rewrite_one_term_as_a_pure_type_term(Term, TypeAss, PureTypeTerm),
%%     rewrite_terms_as_pure_type_terms(TermList, TypeAss, PTypeList).
%% 
%% :- pred rewrite_one_term_as_a_pure_type_term(+Term, +TypeAss, -PureTypeTerm)
%% 
%% # "Creates the Pure Type Term @var{PureTypeTerm} by rewriting
%%  @var{Term} as a type term (possibly with variables) and replacing each
%%  variable in this type term by its type in @var{TypeAss}.".
%% 
%% rewrite_one_term_as_a_pure_type_term(Term, TypeAss, PureTypeTerm):-
%%     escaped_type(Term, TypeTerm),
%%     replace_vars_by_types(TypeAss, TypeTerm, PureTypeTerm).
%% 
%% get_data_from_substitution(Substitution, Var_List, Type_List, Term_List, TypeAss):-
%%      Substitution = typesubs(Var_List, Type_List, Term_List, TypeAss).
%% 
%% set_bottom_substitution(Var_List, Substitution):-
%%      Substitution = typesubs(Var_List, '$bottom', '$bottom', '$bottom').
%% 
%% bottom_substitution(Substitution):-
%%      Substitution = typesubs(_Var_List, Type_List, _Term_List, _TypeAss),
%%      Type_List == '$bottom'.
%% 
%% create_a_type_substitution(Var_List, Type_List, Term_List, TypeAss, Substitution):-
%%      Substitution = typesubs(Var_List, Type_List, Term_List, TypeAss).
%% 
%% 
%% :- pred one_term_2_pure_type_term(Term, Var_List, Type_List, PureTypeTerm)
%% 
%% # "Create a pure type term (i.e. with no variables) by replacing the
%%    variables in @var{Term} by their types. @var{Var_List} is a list
%%    with all the variables of the clause, and @var{Type_List} is the list of
%%    their corresponding types".
%% 
%% one_term_2_pure_type_term(Term, Var_List, Type_List, PureTypeTerm):-
%%         two_lists_to_type_ass(Var_List, Type_List, TypeAss),
%%         rewrite_one_term_as_a_pure_type_term(Term, TypeAss, PureTypeTerm).
%% 
%% two_lists_to_type_ass([], [], []):-!.
%% two_lists_to_type_ass([Var|Vars], [Type|Types], [Var:Type|TypeAss]):-
%%      two_lists_to_type_ass(Vars, Types, TypeAss).
%% 
%% :- pred lit_type_substitution_to_pure_type_lit(+Literal, +Var_List, +Lit_Type_List, -PureTypeLit)
%% 
%% # "Create a pure type literal (i.e. with types as arguments and with
%%    no variables) by replacing the variables of @var{Literal} by their
%%    types. @var{Var_List} is a list with all the variables of the
%%    clause, and @var{Lit_Type_List} is the list of their corresponding
%%    types.".
%% 
%% lit_type_substitution_to_pure_type_lit(Literal, Var_List, Lit_Type_List, PureTypeLit):-
%%      lit_type_list_to_typeass(Var_List, Lit_Type_List, TypeAss),
%%      rewrite_one_term_as_a_pure_type_term(Literal, TypeAss, PureTypeTerm),
%%      PureTypeTerm = ^(PureTypeLit).
%%      % compound_pure_type_term(PureTypeTerm, PureTypeLit, _Name, _Arity).
%% 
%% :- pred lit_type_to_pure_type_lit(+Literal, +Lit_Type_List, -PureTypeLit)
%% 
%% # "Create a pure type literal @var{PureTypeLit} (i.e. with types as arguments and with
%%    no variables) by replacing the variables of @var{Literal} by their
%%    types. @var{Lit_Type_List} is the list of their corresponding
%%    types.".
%% 
%% lit_type_to_pure_type_lit(Literal, Lit_Type_List, PureTypeLit):-
%%      varset(Literal, Lit_Vars),
%%      lit_type_list_to_typeass(Lit_Vars, Lit_Type_List, TypeAss),
%%      % lit_type_list_to_typeass_2(Lit_Type_List, TypeAss),
%%      rewrite_one_term_as_a_pure_type_term(Literal, TypeAss, PureTypeTerm),
%%      PureTypeTerm = ^(PureTypeLit).
%%      % compound_pure_type_term(PureTypeTerm, PureTypeLit, _Name, _Arity).
%% 
%%  %% lit_type_to_pure_type_lit(Literal, Lit_Type_List, PureTypeLit):-
%%  %%      varset(Literal, Lit_Vars),
%%  %%      lit_type_list_to_typeass(Lit_Vars, Lit_Type_List, TypeAss),
%%  %%      % lit_type_list_to_typeass_2(Lit_Type_List, TypeAss),
%%  %%      rewrite_one_term_as_a_pure_type_term(Literal, TypeAss, PureTypeTerm),
%%  %%      compound_pure_type_term(PureTypeTerm, PureTypeLit, _Name, _Arity).
%% 
%% lit_type_list_to_typeass(Vars, LitTypes, TypeAss):-
%%     LitTypes == '$bottom',
%%     !,
%%     create_bottom_type_ass(Vars, TypeAss).       
%% lit_type_list_to_typeass(Vars, LitTypes, TypeAss):-
%%     lit_type_list_to_typeass_3(Vars, LitTypes, TypeAss).
%%   
%% lit_type_list_to_typeass_3([], _LitTypes, []):-!.
%% lit_type_list_to_typeass_3([Var|Vars], LitTypes, [Var:Type|TypeAss]):-
%%      search_var_type_in_literal_list(LitTypes, Var, Type),
%%      lit_type_list_to_typeass_3(Vars, LitTypes, TypeAss).
%% 
%% create_bottom_type_ass([], []):-!.
%% create_bottom_type_ass([Var|Vars], [Var:Type|TypeAss]):-
%%      set_bottom_type(Type),
%%      create_bottom_type_ass(Vars, TypeAss).
%% 
%% lit_type_list_to_typeass_2([], []):-!.
%% lit_type_list_to_typeass_2([Lit|LitTypes], [Var:Type|TypeAss]):-
%%      % search_var_type_in_literal_list(Lit, Type, Var),
%%      is_a_type_literal(Lit, Type, Var),
%%      lit_type_list_to_typeass_2(LitTypes, TypeAss).
%% 
%% % Searching for the type of a variable.
%% 
%% search_var_type_in_literal_list([], _Var, Var_Type):-
%%       !, 
%%       set_top_type(Var_Type).
%% search_var_type_in_literal_list([Literal|List], Var, Var_Type):-
%%       (is_a_type_declaration(Literal, Var, Type) ->
%%            Var_Type = Type
%%            ; 
%%            search_var_type_in_literal_list(List, Var, Var_Type)).                   
%% 
%% % Validation of types.
%% 
%% validate_literal_type_list([]):-!.
%% validate_literal_type_list([Literal|List]):-
%%     is_a_type_literal(Literal, _Type, _Var),
%%     validate_literal_type_list(List).                   
%% 
%% is_a_type_literal(Literal, Type, Var):-
%%   nonvar(Literal),
%%   functor(Literal, Type, 1),
%%   arg(1, Literal, Arg),
%%   var(Arg),
%%   var(Var),
%%   Arg = Var.

% End not equal to non-failure analysis.
