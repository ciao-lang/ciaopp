:- module(typeslib,
    [
      % operations
        dz_type_included/2,
        dz_equivalent_types/2,
        is_ground_type/1,
        type_intersection_2/3,  % for eterms domain
        is_infinite_type/1, % for non-failure
        belongs_to_type/2,
        create_new_type_rule/2,
        find_type_functor/5,
        equivalent_to_top_type/1,
        find_type/3, 
        compute_types/4,
        % compute_type/4,
        selec_type_rule_simplify/0, % Check!
        equivalent_to_numeric/1,
        functor_pure_type_term/1, % Remove asap.
        intersec_types/4,
      % checks
        is_empty_type/1, % for eterms domain
%%          types_are_included/2,
        types_are_incompatible/2,
      % type symbols
        lattice_type_symbol/1,
        em_defined_type_symbol/2,
        internally_defined_type_symbol/2,
        new_type_symbol/1,
        rule_type_symbol/1, % (internal)
      % type terms
        generate_a_type_assigment/3,
        type_escape_term_list/2,
      % type names
        get_type_name/2,
        insert_type_name/3, 
        new_type_name/1,
        retract_type_name/3,
        get_equiv_name/2,
        insert_equiv_name/2,
        retract_equiv_name/2,
      % type rules
        get_type_definition/2,
        get_type_defs/1,
        get_type_rule/2,
        insert_rule/2,
        remove_rule/1,
        insert_renamed_type_defs/2,
        insert_user_type_pred_def/2,
        legal_user_type_pred/1,
        retract_rule/1,
      % support
        assert_param_type_rule_instance/2,
        assert_param_type_instance/2,
        equiv_types/2,
        get_necessary_rules/2,
        get_required_types/1,
        pretty_type_lit_rules/4,
        assert_required_type/1,
        remove_parametric_types_from_rules/0,
        show_types/0,
        show_type_db/0,
        simplify_step1/0,
        simplify_step2/0,
        typedef_to_pred/3,
        collect_usedtypes/3,
        undoall_types/0,
        % assert_initial_types/0,
        get_module_types/1,
        contain_this_type/3,
        minimaltype/2,
        create_defined_types_filters/0,
        approx_as_defined/2,
        gen_lib_type_info/1,
        load_lib_type_info/1,
        cleanup_lib_type_info/0,
        set_param_matching_mode/1,
        pgm_dz_pair/2,
        get_preprocessing_unit_types/1,
        match_one_rule_as_parametric/2,
        get_compatible_types/4,
        prlb/2,
        new_param_type_symbol/1,
        is_param_type_symbol/1,
        non_parametric_type_rule_symbol_def/3,
        parametric_type_rule_symbol_def/3,
        is_user_defined_type_symbol/1,
        assert_and_propagate_type_equivalence/2,
        compute_transitive_closure/3,
        contains_type_param/1
    ], [assertions,
        basicmodes,
        regtypes,
        datafacts]).

% -----------------------------------------------------------------------

:- doc(title,"Operations on Regular Types").  

:- doc(author,"Pedro L@'{o}pez").  
%% :- doc(author, "The Ciao Development Team").

:- doc(module, "
   This library implements routines for manipulating regular types.
    Some of the procedures are adaptations of the work @em{A regular type
    language for logic programs} P.W. Dart and J. Zobel.  In
    F. Pfenning, editor, @em{Types in Logic Programming}, pages
    157--187.  MIT Press, 1987.").

:- doc(appendix, "@section{Regular Type Syntax}
    @include{regular_type_syntax.lpdoc}").

:- doc(bug,"1. Check that a proper cleaning-up is performed (eterms loops
    in a second call, now).").
:- doc(bug,"2. Implement a proper initialization (initial types) and
    finalization (required_types).").
:- doc(bug,"3. Check imports like database and builtintables.").
:- doc(bug,"4. Provide for distinct type names: now, if rt18 already exists
    in the source, we will have a clash!").
:- doc(bug,"5. No way with types like p::=list(p)!!!").
:- doc(bug,"6. insert_user_type_pred_def seems to loop when the type
    definition either: has a cut, a builtin, or a call to a predicate
    undefined (as a type), e.g., with gnd/1.").
% (PBC) Looks like this has been solved:
%:- doc(bug,"7. Has to use native_prop(Goal,regtype(G)) to change Goal
%       in the definition of user types when asserting them. Otherwise, in,
%       e.g., example7_2.pl:
%{WARNING (typeslib): Type 'basic_props:int' not defined, assumed bot}.").
:- doc(bug,"8. typeslib:dz_type_included(rt1,pt3) fails
    with asserted type definitions:
    typedef(rt1,[[[^(a)]]]).
    param_type_symbol_renaming(
                 'basic_props:list'('basic_props:gnd'),pt3).
    See bugs/assumed_bot.pl").

% ---------------------------------------------------------------------------
% (options for typeslib)

:- include(typeslib(typeslib_hooks)).

% ---------------------------------------------------------------------------

% ciao library
:- use_module(library(aggregates)).
:- use_module(library(sort)).
:- use_module(library(write)).
% :- use_module(library(formulae), [list_to_conj/3]).
:- use_module(library(lists), [member/2, append/3, reverse/2]).
:- use_module(library(llists), [flatten/2]).
:- use_module(library(idlists), [member_0/2, subtract/3]).
:- use_module(library(messages)).
:- use_module(library(terms_vars), [varset/2]).
%:- use_module(library(sets), [insert/4]).
%:- use_module(library(assoc),[get_assoc/3]).

% own library
:- use_module(typeslib(type_errors)).
:- use_module(typeslib(type_support)).
:- reexport(typeslib(regtype_basic_lattice)).
%:- reexport(typeslib(regtype_rules)).
%:- reexport(typeslib(basic_type_operations)).

% includes:
:- include(typeslib(type_ops)).
%:- include(typeslib(type_intersec)).
:- include(typeslib(basic_type_operations)).
:- include(typeslib(operations)).
:- include(typeslib(detunion)).
:- include(typeslib(type_simplification)).
:- include(typeslib(type_translate)).
:- include(typeslib(ppoint)).
%:- include(typeslib(fd_reg_type_lattice)).
:- include(typeslib(typedef_to_pred)).
:- include(typeslib(pred_to_typedef)).
:- include(typeslib(required_types)).
:- include(typeslib(name_types)).  % for eterms domain

%% :- reexport(typeslib(regtype_rules),
%%      [ internally_defined_type_symbol/2,
%%        legal_user_type_pred/1,
%%        new_type_parameter/1,
%%        new_type_symbol/1,
%%        rule_type_symbol/1,
%%        type_symbol/1
%%      ]).
:- include(typeslib(regtype_rules)).
:- reexport(typeslib(regtype_rules_), [type_symbol/1]).

% -----------------------------------------------------------------------
% TODO:[new-resources] reliminary support for var_type (for etermsvar domain)

:- export(type_intersection_2_special_var/3).
:- include(typeslib(basic_type_operations_vr)).
:- export(generate_a_type_assigment_special_var/3).
:- include(typeslib(ppoint_vr)).

% ---------------------------------------------------------------------------

undoall_types:- 
    undoall_type_equivs,
    retractall_fact(pgm_typedef(_, _)),
    retractall_fact(param_typ_sym_counter(_)),
    retractall_fact(pgm_param_type_symbol_renaming(_, _)),
    retractall_fact(pgm_paramtypedef(_, _)),
    retractall_fact(types_used_to_colapse_others(_)),
    retractall_fact(type_symbols_used_to_colapse_others(_)),
    retractall_fact(pgm_required_type(_)),
    retractall_fact(pgm_user_type(_)),
    undoall_type_parameters,
    %
    retractall_fact(pgm_computed_type_inclusion(_, _)),
    retractall_fact(pgm_dz_pair(_, _)), % currently not needed 
    retractall_fact(simplified_type_symbol_counter(_)),  % not really needed 
    % Assertions
    initialize_type_symbol_counter,
    retractall_fact(typ_sym_counter(_)),
    undoall_type_names,
    retractall_fact(functor_types(_,_,_)),
    retractall_fact(param_type_depth(_,_)).

undoall_type_equivs:-
    retractall_fact(pgm_equiv_type(_,_)).


%------------------------------------------------------------------%
% :- collect_usedtypes(listtype)::in, list(type)::in,list(type)::out) is det.
%------------------------------------------------------------------%
% Collects the set of type(names) used in the list of types (and 
% their definitions) provided as first argument.
%------------------------------------------------------------------%
collect_usedtypes([],UsedTypes,UsedTypes).
collect_usedtypes([Type|Types],UsedTypes,NUsedTypes):-
    collect_usedtype(Type,UsedTypes,UsedTypes0),
    collect_usedtypes(Types,UsedTypes0,NUsedTypes).
    
%------------------------------------------------------------------%
% :- collect_usedtypes(type::in, list(type)::in,list(type)::out) is det.
%------------------------------------------------------------------%
% Adds to UsedTypes the set of type(names) used in Type.
%------------------------------------------------------------------%
collect_usedtype(Type,UsedTypes,NUsedTypes):-
    ( rule_type_symbol(Type) ->
         insert(UsedTypes,Type,UsedTypes0,Member),
         ( Member = yes -> % already added to UsedTypes
              NUsedTypes = UsedTypes
         ; get_type_definition(Type,Def) -> 
              collect_usedtypes(Def,UsedTypes0,NUsedTypes)
         ;                 % parameter type, do not neet to add it
              NUsedTypes = UsedTypes 
         )
    ;    % does not have a definition (any, int, etc)
         NUsedTypes = UsedTypes
    ).

%------------------------------------------------------------------%
% :- pred insert(+Set1, +Element, -Set2, -Member)
%------------------------------------------------------------------%
%------------------------------------------------------------------%
insert([], Element, [Element],no).
insert([Head|Tail], Element, Set, Member) :-
    compare(Order, Head, Element),
    insert_comp0(Order, Head, Tail, Element, Set, Member).

insert_comp0(<, Head, Tail, Element, [Head|Set], Member) :-
    insert(Tail, Element, Set, Member).
insert_comp0(=, Head, Tail, _, [Head|Tail], yes).
insert_comp0(>, Head, Tail, Element, [Element,Head|Tail], no).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%  The following utilities are for debugging. Comment when included in
%  the source code. 

show_types:-
     nl, write('Type Names:'), nl, nl,
     write_type_names, 
     nl, write('Equiv Names:'), nl, nl,
     write_equivalents_names, 
     nl, write('Non-Parametric type definitions:'), nl, nl,
     write_all_typedef,
     nl, write('Parametric type definitions:'), nl, nl,
     write_all_paramtypedef,
     nl, write('Equivalent types:'), nl, nl,
     write_all_equiv_type,
     nl, write('Parametric type symbol renamings:'), nl, nl,
     write_all_param_type_symbol_renaming,
     nl, write('Required types:'), nl, nl,
     write_all_required_types.

write_type_names:-
    get_type_names(Names),
    write_names(Names).

write_equivalents_names:-
    get_equiv_names(Names),
    write_equiv_names(Names).


write_names([]).
write_names([N|Names]):-
    writeq(N), 
    write('.'),
    nl,     
    write_names(Names).

write_equiv_names([]).
write_equiv_names([N|Names]):-
    writeq(N), 
    write('.'),
    nl,     
    write_equiv_names(Names).


write_all_typedef:-
  get_type_rules(Rules),
  write_list2(Rules).

write_all_paramtypedef:-
   get_parametric_type_rules(Rules),
   write_list2(Rules).

write_all_equiv_type:-
  findall(equiv_type(X, Y), equiv_type(X, Y), Z),
  write_list2(Z). 

write_all_param_type_symbol_renaming:-
    findall(param_type_symbol_renaming(ParTyp, NPartyp),
            param_type_symbol_renaming(ParTyp, NPartyp),    
            Renamings), 
    write_list2(Renamings).  

write_list2([]).
write_list2([H|L]) :- writeq(H), 
                  write('.'),
                  nl, 
                  write_list2(L).

write_all_required_types:-
    required_type(T),
    write(T), nl,
    fail.
write_all_required_types.

%%

show_type_db:-
     nl, write('Non-Parametric type definitions:'), nl, nl,
     write_all_typedef,
     nl, write('Parametric type definitions:'), nl, nl,
     write_all_paramtypedef,
     nl, write('Equivalent types:'), nl, nl,
     write_all_equiv_type,
     nl, write('Parametric type symbol renamings:'), nl, nl,
     write_all_param_type_symbol_renaming, nl, 
     write_typ_sym_counter, nl,
     write_param_typ_sym_counter, nl,
     nl, write('Internal auxiliary info:'),
     nl, write('computed_type_inclusion'),
     nl, write_all_computed_type_inclusion,
     nl, write('no_simplified_type:'),
     nl, write_all_no_simplified_type,
     nl, write('computed_type_intersec:'),
     nl, write_all_computed_type_intersec,
     nl, write('computed_empty_type:'),
     nl, write_all_computed_empty_type,
     nl, write('computed_infinite_type:'),
     nl, write_all_computed_infinite_type,
     nl, write('already_validated:'),
     nl, write_all_already_validated.

write_typ_sym_counter :-
  typ_sym_counter(N), 
  !,
  write('Type symbol counter = '), 
  write(N). 
write_typ_sym_counter :-
    write('*There is no type symbol counter*'). 
   
write_param_typ_sym_counter :-
  param_typ_sym_counter(N), 
  !,
  write('Parametric type symbol counter = '), 
  write(N). 
write_param_typ_sym_counter :-
    write('*There is no parametric type symbol counter*'). 


write_all_computed_type_intersec :-
  findall(computed_type_intersec(A, B, C), computed_type_intersec(A, B, C), L),
  write_list2(L). 

write_all_already_validated :-
  findall('$already_validated$'(A), '$already_validated$'(A), L),
  write_list2(L). 

write_all_computed_infinite_type :-
  findall(computed_infinite_type(A), computed_infinite_type(A), L),
  write_list2(L). 

write_all_computed_empty_type :-
  findall(computed_empty_type(A), computed_empty_type(A), L),
  write_list2(L). 

write_all_no_simplified_type :-
  findall(no_simplified_type(A), no_simplified_type(A), L),
  write_list2(L). 

%%%%%

%%  %% print_type_rules([], _Modes).
%%  %% print_type_rules([Entry|Tab], Modes):-
%%  %%     Entry = st(Pred/_Arity, Clauses, _),
%%  %%     print_typedef(Modes, Pred, Clauses), %nd-PLG 
%%  %%     (define_numeric_type(Pred) -> 
%%  %%          true ; 
%%  %%          predicate_2_type_rule(Pred, Clauses, TypeRule),
%%  %%          internal_rule_translate(TypeRule, NewRule),
%%  %%          print_type_rule(Modes, NewRule)
%%  %%          % print_type_rule(Modes, TypeRule)
%%  %%     ),
%%  %%     print_type_rules(Tab, Modes).
%% 
%% print_type_rule(cl, TypeDef):-
%%      write(':- '), writeq(TypeDef), write('.'), nl.
%% print_type_rule(pl, TypeDef):-
%%      print_rul(TypeDef).
%% 
%% print_typedef(cl, Type, TypeDef):-
%%      write('%:- typedef( '), write(Type), 
%%      write(' , '), writeq(TypeDef), 
%%      write(' ).'),
%%      nl.
%% print_typedef(pl,_,TypeDef):-
%%      print_rul(TypeDef).
%% 
%% print_rul([Cl|TypeDef]):-
%%      write('%  '), writeq(Cl), nl,
%%      print_rul(TypeDef).
%% print_rul([]).

%----------------------------------------------------------------------%

get_module_types([term,bot|Types]):-
   get_preprocessing_unit_types(Types).

 %% :- data get_module_types/1.
 %% 
 %% assert_initial_types:-
 %%         get_module_types0(Types),       
 %%         set_fact(get_module_types([term,bot|Types])).
 %% 
 %% get_module_types0(Module_Types):-
 %%     findall(Typ,typedef(Typ, _Def),Module_Types).

contain_this_type([],_Type,[]).
contain_this_type([S|List],Type,[S|SuperSet]):-
    dz_type_included(Type,S),!,
    contain_this_type(List,Type,SuperSet).
contain_this_type([_S|List],Type,SuperSet):-
    contain_this_type(List,Type,SuperSet).

approx_as_defined(Type,ApproxType):-
    \+ internally_defined_type_symbol(Type,_),
    !,
    ApproxType = Type.
approx_as_defined(Type,ApproxType):-
    internal_approx_as_defined(Type,ApproxType).

internal_approx_as_defined(Type,ApproxType):-
    type_parameter(Type),
    param_matching_mode(on),!,
    ApproxType = Type.
internal_approx_as_defined(Type,ApproxType):-
    prlb(Type,Fs),
    gather_cands_decide(Fs,Type,SuperSet),
    reverse(['basic_props:term'|SuperSet], SS1),
    minimaltype(SS1,ApproxType),!.

gather_cands_decide(_Fs,Type,[ParType]):- % parametric rule
    match_one_rule_as_parametric(Type, ParType).
gather_cands_decide(Fs,Type,Cs):-
    gather_cands(Fs,Type,[],Cs).

gather_cands([],_,Cs,Cs) :-!.
gather_cands([F|Fs],Type,Seen,Cs) :-    
    get_functor_types(F,Ts),
    filter_cands(Ts,Type,Seen,Seen1),
    gather_cands(Fs,Type,Seen1,Cs).
    

get_functor_types(F,Ts) :-
    native_type_symbol(F),!,
    functor_types(F,Ts,basic).
get_functor_types(F,Ts) :-
    functor_types(F,Ts,rule),!.
get_functor_types(F,Ts) :-
    findall(T,
     (
      functor_types(B,T,basic),
      prepare_functor(F,F_ok),
      dz_type_included(F_ok,B)
     ), TTs),
     flatten(TTs,Ts).


prepare_functor(N/A,Term) :-
    !,
    functor(T0,N,A),
    Term = ^T0.
prepare_functor(F,F).


filter_cands([],_,Seen,Seen).
filter_cands([S|Cands],Type,Seen,SeenOut) :-
    \+ member(S,Seen),
    dz_type_included(Type,S),!,
    filter_cands(Cands,Type,[S|Seen],SeenOut).
filter_cands([_S|Cands],Type,Seen,FCands):-
    filter_cands(Cands,Type,Seen,FCands).


minimaltype([T],T).
minimaltype([T1,T2|List],T):-
    dz_type_included(T2,T1),!,
    minimaltype([T2|List],T).
minimaltype([T1,_T2|List],T):-
    minimaltype([T1|List],T).

:- pred lattice_type_symbol(+Type)

# "Succeeds if and only if @var{Type} is a rule type symbol that is
   defined by an (asserted) type rule or @var{Type} is a constant
   defining a @tt{native type} of the lattice (bottom point excluded).".

lattice_type_symbol(Type):- 
    native_type_symbol(Type), 
    !.
lattice_type_symbol(Type):- 
    em_defined_type_symbol(Type, _Defin).


:- data functor_types/3. 
:- data param_type_depth/2.


create_defined_types_filters :-
    get_preprocessing_unit_types(Types),
    create_defined_types_filters_x(Types).

create_defined_types_filters_x([]).
create_defined_types_filters_x([T|Ts]) :-
    prlb(T,Fs),
    add_to_each_functor(Fs,T),
    create_defined_types_filters_x(Ts).

add_to_each_functor([],_).
add_to_each_functor([F|Fs],T) :-
    ( retract_fact(functor_types(F,Ts,_)) ->
      append(Ts,[T],Ts1)
    ; Ts1 = [T]
    ),
    ( native_type_symbol(F) ->
      M = basic
    ; M = rule
    ),
    assertz_fact(functor_types(F,Ts1,M)),
    add_to_each_functor(Fs,T).


prlb(T,Lab):-
    prlb0(T,L,[],[]),
    sort(L,Lab).
prlb0(T,Lab,L,Seen):-
    em_defined_type_symbol(T,Def),!,
    (   member(T,Seen) ->
        Lab = L
    ;   prlblist(Def,Lab,L,[T|Seen])
    ).
prlb0(T,[Name/Arity |L],L,_Seen):-
    compound_pure_type_term(T,_Term,Name,Arity),!.
prlb0(T,[T|L],L,_Seen).

prlblist([],L,L,_Seen).
prlblist([T|RestT],Lab,L,Seen):-
    prlb0(T,Lab,L1,Seen),
    prlblist(RestT,L1,L,Seen).


match_one_rule_as_parametric(Type, NewType):-
    param_type_symbol_renaming(_,Type),
    !,
    NewType = Type.
match_one_rule_as_parametric(Type, NtypSymbol1):-
    get_type_definition(Type,Def),
    TypeDef = typedef(Type,Def),
    paramtypedef(Head,Body), 
    ParRule = paramtypedef(Head,Body), 
    copy_term(ParRule, Rule),
    non_parametric_type_rule_symbol_def(TypeDef, NTypeSymbol, NDefin),
    parametric_type_rule_symbol_def(Rule, PTypeSymbol, PDefin),
%        order_type_defin(PDefin, OrPDefin), !, 
    match_defin(NDefin, PDefin, PDefin), 
    ground(PTypeSymbol),
    assert_param_type_rule_instance(PTypeSymbol, Cand),
%       display(assert_param_type_rule_instance(PTypeSymbol, Cand)),nl,
    dz_type_included(NTypeSymbol, Cand),
    !,
    assert_and_propagate_type_equivalence(NTypeSymbol, Cand),
    check_max_depth(Cand,3,NtypSymbol1).


match_defin([], RestPDefin, PDefin) :-
    RestPDefin \= PDefin, % some parts of the parametric rule have
                          % been matched
    varset(RestPDefin,FreeParams),
    bind_to_bot(FreeParams).
match_defin([NType|NDefin], PDefin, OrigPDefin):-
    match_with_some_type(PDefin, NType, RestPDefin),
    match_defin(NDefin, RestPDefin, OrigPDefin).

match_with_some_type([PType|PDefin], NType, PDefin):-
    type_match(NType, PType), !.
match_with_some_type([PType|PDefin], NType, [PType|RestPDefin]):-
    match_with_some_type(PDefin, NType, RestPDefin).

type_match(NType, PType):-
    var(PType),
    internal_approx_as_defined(NType,DefType),
    !,
    PType = DefType.
type_match(NType, PType):- 
    NType == PType,
    !.
type_match(NType, PType):-
   compound_pure_type_term(NType, NComp, Name, Arity),
   compound_pure_type_term(PType, PComp, Name, Arity), % PType is not a variable.
   !,
   compound_type_match(Arity, NComp, PComp).
type_match(_NType, PType):-
%   non_par_rule_type_symbol(NType),
   par_rule_type_symbol(PType), !.
type_match(NType, PType):-
   non_par_rule_type_symbol(NType),
   non_par_rule_type_symbol(PType).


compound_type_match(0, _NComp, _PComp):-!.
compound_type_match(ArgNum, NComp, PComp):-
       ArgNum > 0, 
       arg(ArgNum, NComp, NArg),
       arg(ArgNum, PComp, PArg),
       type_match(NArg, PArg),
       NArgNum is ArgNum - 1,
       compound_type_match(NArgNum, NComp, PComp).

bind_to_bot([]).
bind_to_bot([bot|Ps]):-
    bind_to_bot(Ps).

check_max_depth(_,0,term).
check_max_depth(PType,Depth,NewType) :-
    param_type_symbol_renaming(Def,PType),!,
    Def =.. [NDef,NextType|Rest],
    Depth1 is Depth - 1,
    check_max_depth(NextType,Depth1,NewNextType),
    ( NewNextType \= NextType ->
      NewDef =.. [NDef,NewNextType|Rest],
      assert_param_type_rule_instance(NewDef, NewType)
    ; NewType = PType
    ).
check_max_depth(Type,_,Type).

set_param_matching_mode(M) :-
    set_fact(param_matching_mode(M)).

contains_type_param(T) :-
    compute_transitive_closure([T],[],Types),
    member(T0,Types),
    type_parameter(T0),!.

%----------------------------------------------------------------------%
% Generation of source code for storing types from libraries.
%----------------------------------------------------------------------%

:- pred cleanup_lib_type_info

# "Cleans up all facts of lib_* predicates.".

cleanup_lib_type_info:-
    retractall_fact(lib_computed_type_inclusion(_,_)),
    retractall_fact(lib_dz_pair(_,_)),
    retractall_fact(lib_type_name(_,_,_)),
    retractall_fact(lib_typ_name_counter(_)),
    retractall_fact(lib_equiv_name(_,_)),
    retractall_fact(lib_equiv_type(_,_)),
    retractall_fact(lib_typ_sym_counter(_)),
    retractall_fact(lib_param_typ_sym_counter(_)),
    retractall_fact(lib_param_type_symbol_renaming(_,_)),
    retractall_fact(lib_typedef(_,_)),
    retractall_fact(lib_paramtypedef(_,_)),
    retractall_fact(lib_user_type(_)),
    retractall_fact(lib_required_type(_)),
    retractall_fact(lib_types_used_to_colapse_others(_)),
    retractall_fact(lib_type_symbols_used_to_colapse_others(_)).


%% ---------------------------------------------------------------------------

:- use_module(engine(io_basic)).
:- use_module(library(read), [read/2]).

load_lib_type_info(Stream):-
    repeat,
    read(Stream,Fact),
    (
        Fact = end_of_file ->
        true
    ;
        assertz_fact(Fact),
        fail
    ).
    
%% ---------------------------------------------------------------------------

gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_computed_type_inclusion(A,B),
    displayq(Stream,lib_computed_type_inclusion(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_dz_pair(A,B),
    displayq(Stream,lib_dz_pair(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_type_name(A,B,C),
    displayq(Stream,lib_type_name(A,B,C)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    typ_name_counter(A),
    displayq(Stream,lib_typ_name_counter(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_equiv_name(A,B),
    displayq(Stream,lib_equiv_name(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_equiv_type(A,B),
    displayq(Stream,lib_equiv_type(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    typ_sym_counter(A),
    displayq(Stream,lib_typ_sym_counter(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    param_typ_sym_counter(A),
    displayq(Stream,lib_param_typ_sym_counter(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_param_type_symbol_renaming(A,B),
    displayq(Stream,lib_param_type_symbol_renaming(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_typedef(A,B),
    displayq(Stream,lib_typedef(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_paramtypedef(A,B),
    displayq(Stream,lib_paramtypedef(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_user_type(A),
    displayq(Stream,lib_user_type(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    pgm_required_type(A),
    displayq(Stream,lib_required_type(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    types_used_to_colapse_others(A),
    displayq(Stream,lib_types_used_to_colapse_others(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(Stream):-
    nl(Stream),
    type_symbols_used_to_colapse_others(A),
    displayq(Stream,lib_type_symbols_used_to_colapse_others(A)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_type_info(_Stream).     

