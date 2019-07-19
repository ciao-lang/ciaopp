% These predicates 
intersec_types(Var_List, _Var_Types, OTypeAss, OTypeAss):-
   var(Var_List), !.
intersec_types(Var_List, Var_Types, ITypeAss, OTypeAss):-
   nonvar(Var_List), 
   Var_List = [Var|List],
   find_list_entry(Var_Types, Var, vt(_, Types)),
   set_top_type(Top),
   intersec_type_list(Types, Top, LType),
   \+ bot_type(LType),
   intersec_types(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).

intersec_type_list(Type_List, Type, Type):-
   var(Type_List), !.
intersec_type_list(Type_List, InType, OutType):-
   nonvar(Type_List),
   Type_List = [Type | List],
   type_intersection_0(InType, Type, Intersec),
   (is_empty_type(Intersec) -> 
      set_bottom_type(OutType) % , retract_1 -PL
      ;
      intersec_type_list(List, Intersec, OutType)).

type_intersection_0(InType, Type, Intersec):-
   %% type_rule_simplify, % -PL warning !
   type_intersection(InType, Type, Intersec),
   selec_type_rule_simplify, !.
