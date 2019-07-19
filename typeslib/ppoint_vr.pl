% ===========================================================================
% TODO:[new-resources] preliminary support for var_type (for etermsvar)
% TODO: partially duplicates code from ppoint.pl

% ASM, 6 Sep 2012
% Special intersection for type assignment
% Variables which do not have type are assigned the top type.
% If a variable may be assigned the type var, a special case is used:
% - if only var is present, the resulting type is var
% - if not, the resulting type is the intersection without any var

intersec_types_2_special_var([], _Var_Types, OTypeAss, OTypeAss):-
   !.
intersec_types_2_special_var([Var|List], Var_Types, ITypeAss, OTypeAss):-
   find_list_entry(Var_Types, Var, Entry),
   (var(Entry) -> Types = _
                  ;
                  Entry = vt(_, Types)),
   set_top_type(Top),
   ( contains_var_type(Types)
   -> delete_var_type(Types,DTypes),
      ( var(DTypes) % Is list empty?
      -> set_var_type(LType)
       ; intersec_type_list_2_special_var(DTypes, Top, LType)
      )
    ; intersec_type_list_2_special_var(Types, Top, LType)
   ),
   % \+ bot_type(LType),
   intersec_types_2_special_var(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).

contains_var_type([Type|_]) :-
        nonvar(Type),
        var_type(Type),
        !.
contains_var_type([_|List]) :-
        nonvar(List),
        contains_var_type(List).

delete_var_type(Type_List,Type_List) :-
        var(Type_List),
        !.
delete_var_type([Type|List],DList) :-
        var_type(Type),
        !,
        delete_var_type(List,DList).
delete_var_type([Type|List],[Type|DList]) :-
        delete_var_type(List,DList).

intersec_type_list_2_special_var(Type_List, Type, Type):-
   var(Type_List), 
   !.
intersec_type_list_2_special_var(Type_List, InType, OutType):-
   nonvar(Type_List),
   Type_List = [Type|List],
   (
        var_type(Type) ->
        intersec_type_list_2_special_var(List, InType, Intersec),
        (
            ( top_type(Intersec) ; var_type(Intersec) ) ->
            set_var_type(OutType)
        ;
            OutType = Intersec
        )
   ;
        type_intersection_2_special_var(InType, Type, Intersec),
        intersec_type_list_2_special_var(List, Intersec, OutType)
   ).

type_intersection_2_special_var(Type1, Type2, Intersect):-
   dz_type_included(Type1, Type2),
   !,
   Intersect = Type1.
type_intersection_2_special_var(Type1, Type2, Intersect):-
   dz_type_included(Type2, Type1),
   !,
   Intersect = Type2.
type_intersection_2_special_var(Type1, Type2, Intersect):-
    debug_message("Performing full intersection of ~q and ~q.", [Type1, Type2]),
    pp_type_intersection_special_var(Type1, Type2, Intersect),
    debug_message("Intersection of ~q and ~q is ~q.", [Type1, Type2, Intersect]).
 %% type_intersection_2(Type1, Type2, Intersect):-
 %%     Intersect = Type2,
 %%     warning_message("No inclusion relationship between types ~q and ~q.",[Type1, Type2]),
 %%     warning_message("Assumed that the intersection is ~q. This can be improved by performing full intersection.", [Intersect]).
   

pp_type_intersection_special_var(Typ1, Typ2, Inter):-
     % Calls the special intersection which treats var as top
     typeslib:type_intersection_special_var(Typ1, Typ2, Intersec),
     !, 
     (is_empty_type(Intersec) -> 
            clean_after_empty_pp_type_intersection,
            set_bottom_type(Inter)
            ; 
            simplify_types_after_pp_type_intersection,
            replace_one_equiv_type(Intersec, Inter)).

generate_a_type_assigment_special_var(Type_List, Term_List, TypeAss):- 
      varset(Term_List, Term_Vars),
      get_var_types_by_unification(Type_List, Term_List, Types),
      intersec_types_2_special_var(Term_Vars, Types, [], TypeAss).

