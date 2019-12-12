% (included from typeslib.pl)

% ===========================================================================
% TODO:[new-resources] preliminary support for var_type (for etermsvar)
% TODO: partially duplicates code from basic_type_operations.pl

% ASM - Type intersection with special treatment of var
% If an element is not of a variable or term and the
% other is a variable, the result is not bottom,
% but the first element.
% The result of var /\ term = var
type_intersection_special_var(Typ1, Typ2, Typ1):-
    Typ1 == Typ2, !.
%type_intersection_special_var(Typ1, Typ2, Typ1) :-
%    var_type(Typ1),
%    top_type(Typ2), !.
%type_intersection_special_var(Typ1, Typ2, Typ2) :-
%    var_type(Typ2),
%    top_type(Typ1), !.
type_intersection_special_var(Typ1, Typ2, Typ2) :-
    var_type(Typ1), !.
type_intersection_special_var(Typ1, Typ2, Typ1) :-
    var_type(Typ2), !.
type_intersection_special_var(Typ1, Typ2, Typ2):-
    top_type(Typ1), !.
type_intersection_special_var(Typ1, Typ2, Typ1):-
    top_type(Typ2), !.
type_intersection_special_var(Typ1, _Typ2, Int):-
    bot_type(Typ1), !,
    set_bottom_type(Int).
type_intersection_special_var(_Typ1, Typ2, Int):-
    bot_type(Typ2), !,
    set_bottom_type(Int).
type_intersection_special_var(Typ1, Typ2, Typ3):-
    computed_type_intersec(Typ1, Typ2, Typ3), !.
type_intersection_special_var(Typ1, Typ2, Intersec):-
    rule_type_symbol(Typ1), 
    !,
    get_type_definition(Typ1, Defin1), 
    determine_type_union(Typ2, Defin2),
    type_intersection2_special_var(Typ1, Typ2, Defin1, Defin2, Intersec).
type_intersection_special_var(Typ1, Typ2, Intersec):-
    rule_type_symbol(Typ2), 
    !,
    get_type_definition(Typ2, Defin2), 
    determine_type_union(Typ1, Defin1),
    type_intersection2_special_var(Typ1, Typ2, Defin1, Defin2, Intersec).
type_intersection_special_var(Typ1, Typ2, Intersec):-
    regtype_basic_type_intersection(Typ1, Typ2, Intersec), !.
type_intersection_special_var(Typ1, Typ2, TypeInter):-
    compound_pure_type_term(Typ1, Comp1, Name1, Arity1), 
    compound_pure_type_term(Typ2, Comp2, Name2, Arity2),
    !,
    ((Name1 == Name2, Arity1 == Arity2) 
    ->
    functor(CompInter, Name2, Arity2),
    arg_typ_inter_special_var(Arity2, CompInter, Comp1, Comp2),
    construct_compound_pure_type_term(CompInter, TypeInter)
    ;  
    set_bottom_type(TypeInter)).
type_intersection_special_var(Typ1, Typ2, TypeInter):-
    compound_pure_type_term(Typ1, _Comp1, _Name1, _Arity1), 
    !,
    compound_pure_type_term_intersection_special_var(Typ1, Typ2, TypeInter).
type_intersection_special_var(Typ1, Typ2, TypeInter):-
    compound_pure_type_term(Typ2, _Comp2, _Name2, _Arity2), 
    !,
    compound_pure_type_term_intersection_special_var(Typ2, Typ1, TypeInter).
type_intersection_special_var(_Typ1, _Typ2, Intersec):- 
     set_bottom_type(Intersec).


compound_pure_type_term_intersection_special_var(Typ1, Typ2, TypeInter):-
    basic_lattice_type_includes_compound_type_term(Typ2), 
    !,
    TypeInter = Typ1.
compound_pure_type_term_intersection_special_var(Typ1, Typ2, TypeInter):-
    basic_lattice_type_needs_intersection_with_compound_type_term_args(Typ2, Intersec_with), 
    !,
    compound_pure_type_term(Typ1, Comp1, Name1, Arity1), 
    functor(CompInter, Name1, Arity1),
    compound_type_term_args_intersec_with_one_type_special_var(Arity1, CompInter, Comp1, Intersec_with),
    construct_compound_pure_type_term(CompInter, TypeInter).
compound_pure_type_term_intersection_special_var(_Typ1, _Typ2, TypeInter):-
    set_bottom_type(TypeInter).


arg_typ_inter_special_var(0, _Intersec, _Typ1, _Typ2):-!.
arg_typ_inter_special_var(Arg, Intersec, Typ1, Typ2):-
       Arg > 0, 
       arg(Arg, Typ1, Arg1),
       arg(Arg, Typ2, Arg2),
       type_intersection_special_var(Arg1, Arg2, Arg3),
       arg(Arg, Intersec, Arg3),
       NArg is Arg - 1,
       arg_typ_inter_special_var(NArg, Intersec, Typ1, Typ2).


compound_type_term_args_intersec_with_one_type_special_var(0, _Intersec, _CompType, _Not_Comp_Type):-!.
compound_type_term_args_intersec_with_one_type_special_var(Arg, Intersec, CompType, Not_Comp_Type):-
       Arg > 0, 
       arg(Arg, CompType, Arg1),
       type_intersection_special_var(Arg1, Not_Comp_Type, Arg3),
       arg(Arg, Intersec, Arg3),
       NArg is Arg - 1,
       compound_type_term_args_intersec_with_one_type_special_var(NArg, Intersec, CompType, Not_Comp_Type).

type_intersection2_special_var(Typ1, Typ2, TypUnion1, TypUnion2, NewIntersec):-
  new_type_symbol(Intersec),
  asserta_fact(computed_type_intersec(Typ1, Typ2, Intersec)),
  % asserta(no_simplified_type(Intersec)), % This is done by insert_new_type_rule 
  cp_intersec_special_var(TypUnion1, TypUnion2, [], Union),
  (Union == [] 
     -> set_bottom_type(X), NUnion = [X] 
     ;  NUnion = Union),
   insert_new_type_rule(Intersec, NUnion),
  ( current_pp_flag(types,deftypes) ->
    deftypes:approx_as_defined(Intersec,NewIntersec),
    remove_rule(Intersec)
  ; NewIntersec = Intersec
  ).

cp_intersec_special_var([], _TypUnion2, Union, Union):-!.
cp_intersec_special_var([Typ1|Union1], TypUnion2, Union, NUnion):-
  cp_intersec_2_special_var(TypUnion2, Typ1, Union, IUnion),
  cp_intersec_special_var(Union1, TypUnion2, IUnion, NUnion).

cp_intersec_2_special_var([], _Typ1, Union, Union):-!.
cp_intersec_2_special_var([Typ2|Union2], Typ1, Union, NUnion):-
  type_intersection_special_var(Typ1, Typ2, Inter),
  (bot_type(Inter) 
     -> AcUnion = Union 
     ;  AcUnion = [Inter|Union]),
  cp_intersec_2_special_var(Union2, Typ1, AcUnion, NUnion).  

