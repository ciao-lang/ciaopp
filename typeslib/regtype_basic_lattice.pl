:- module(regtype_basic_lattice,
    [ % type symbols
        base_type_symbol/1,
        basic_lattice_type_symbol/1,
      % type parameters
        new_type_parameter/1,
        undoall_type_parameters/0,
      % type terms
        pure_type_term/1,
        compound_pure_type_term/4,
        construct_compound_pure_type_term/2,
        constant_symbol/2,
      % basic operations
        define_a_ground_type/1,
        dz_subset_lattice/2,
        dz_type_selects/2,
        type_included_in_ground/1,
        type_included_in_numeric/1,
        regtype_basic_type_intersection/3,
        translate_lattice_types/4,
        basic_lattice_type_includes_compound_type_term/1, 
        basic_lattice_type_needs_intersection_with_compound_type_term_args/2,
        gen_lib_param_symbol/1,
        load_lib_param_symbol/1,
        cleanup_lib_param_symbol/0
    ],
    [assertions, basicmodes, regtypes, datafacts]).

:- doc(module, "This module contains the operations required for a basic
    lattice of types (not really regular) formed with the native types.
    The lattice is as follows:
@begin{verbatim}
       term
 ____________|_______________
 |           |               |
var         gnd            struct
     ________|_____________  |
     |               |     | |
    atm             num   gndstr
         ________|________
        |                |
       int              flt
        |
        |
     nnegint
@end{verbatim}
").

%% :- use_module(typeslib(typeslib), [type_intersection/3]). %% Not needed anymore -PLG Oct, 18, 2004
:- use_module(typeslib(typeslib), [insert_rule/2, 
                               retract_rule/1, 
                               param_matching_mode/1,
                               set_param_matching_mode/1,
                               typedef/2,
                               pgm_dz_pair/2]).
:- use_module(domain(eterms), [type_union/3, resetunion/0]).
:- use_module(library(lists), [append/3]).
:- use_module(library(aggregates), [findall/3]).

:- use_module(engine(io_basic)).

:- reexport(typeslib(regtype_basic_lattice_base)).
% Used in type operations
:- pred base_type_symbol(X)
    # "@var{X} is a @tt{base type symbol}.  Different base type symbols
       must define disjoint sets of terms.".

base_type_symbol(X) :-
    var_type(X);
    atom_type(X);
    numeric_type(X);
    int_type(X);
    nnegint_type(X);
    float_type(X);
    struct_type(X);        %% Comented out by PLG
    ground_struct_type(X).

%% % Good definitions:
%% top_or_bot_or_base_type_symbol(Type) :-
%%      top_type(Type);  % Warning: gnd excluded. -PLG Oct, 19, 2004.
%%      bot_type(Type);
%%      base_type_symbol(Type).

% Parameter (or "hidden") types:
new_type_parameter(Type):-
    ( retract_fact(pgm_param_symbol(_Type0,N0)) -> true
    ; N0 = 0 ),
    N is N0+1,
    name(N, NName),
    append("tp", NName, TypeName),
    name(Type, TypeName),
    asserta_fact(pgm_param_symbol(Type,N)).

:- reexport(typeslib(type_parameter)).

:- data pgm_param_symbol/2. %% For user programs.
:- data lib_param_symbol/2. %% For libraries.

% param_symbol(A,B):-
%       pgm_param_symbol(A,B).
% param_symbol(A,B):-
%       lib_param_symbol(A,B).

undoall_type_parameters:-
    retractall_fact(pgm_param_symbol(_Type0,_N0)).

% ========================================================================

% BASIC INCLUSION RELATIONS

type_included_in_ground(Type) :-
    % struct is not included -PLG
    ground_type(Type);  % Redundant if called from dz_type_selects/2. PLG, Dec-3-2003
    type_included_in_numeric(Type);
    type_included_in_atom(Type);
    ground_struct_type(Type).
    % was: type_included_in_ground_struct(Type).
type_included_in_numeric(Type) :-
    numeric_type(Type); % Redundant if called from typeslib:type_intersection/3. -PLG, Oct 19, 2004
    number_constant(Type, _);
    type_included_in_int(Type);
    type_included_in_float(Type).

type_included_in_float(Type) :-
    float_type(Type); % Redundant if called from typeslib:type_intersection/3. -PLG, Oct 19, 2004
    float_constant(Type, _).

type_included_in_int(Type) :-
    int_type(Type); % Redundant if called from typeslib:type_intersection/3. -PLG, Oct 19, 2004
    int_constant(Type, _);
    type_included_in_nnegint(Type).

type_included_in_nnegint(Type) :-
    nnegint_type(Type); % Redundant if called from typeslib:type_intersection/3. -PLG, Oct 19, 2004
    nnegint_constant(Type, _).

type_included_in_atom(Type) :-
    atom_type(Type);
    atom_constant(Type, _).

type_included_in_struct(Type) :-
    struct_type(Type);
    ground_struct_type(Type).
    % ; compound_pure_type_term(Type, _Term, _Name, _Arity). -PLG

type_included_in_ground_struct(Type) :-
    ground_struct_type(Type).
 %%     define_a_ground_struct_type(Type).

% END of BASIC INCLUSION RELATIONS

% ========================================================================

% the symbols for which dz_subset_lattice actually works:
basic_lattice_type_symbol(Type) :- constant_symbol(Type, _).
basic_lattice_type_symbol(Type) :- native_type_symbol(Type).
basic_lattice_type_symbol(Type) :- type_parameter(Type), param_matching_mode(on).
%% PLG: basic_lattice_type_symbol(Type) :- compound_pure_type_term(Type, _Term, _Name, _Arity).

:- pred dz_subset_lattice(Type1, Type2) # "Defines the basic inclusion
    relations in the type lattice: @var{Type1} is included in
    @var{Type2}. However, it does not define inclusion relations
    involving compound type terms nor rule type symbols. These
    relations are defined by other predicates. The reason for this
    separate treatment is that it avoids recursive calls in
    @verb{dz_subset_lattice/2}, making type operations more
    flexible wrt changes in the type lattice and easing
    modifications. However, the separate treatment of compound
    type terms and rule type symbols does not involve a lost in
    generality of type operations, since it is assumed that
    compound type terms and rule type symbols are present in all
    regular type lattices. For example, in order to redefine the
    type inclusion operation for a new regular type lattice, it
    suffices to redefine @verb{dz_subset_lattice/2} and
    additionally
    @verb{basic_lattice_type_includes_compound_type_term/1} (which
    defines the types in the new lattice that include compound
    type terms).".

dz_subset_lattice(Type1, Type2) :-
    dz_subset_fdtypes(Type1, Type2).

dz_subset_fdtypes(Type1, Type2) :-  % Redundant -PLG
    Type1 == Type2,
    !.
dz_subset_fdtypes(Type1, Type2) :- 
    type_parameter(Type2),
    param_matching_mode(on),
    !,
    ( typedef(Type2,_DefSoFar) -> 
      true
    ; insert_rule(Type2,[bot])
    ),
    set_param_matching_mode(off),
    resetunion,  % in eterms
    save_dz_pairs(DZPairs), % type_union/3 calls dz_type_included
                            % and retracts dz_pair/2 collected so far
    type_union(Type2,Type1,UType),
    restore_dz_pairs(DZPairs),
    ( typedef(UType,NewDef) ; NewDef = [UType] ),
    set_param_matching_mode(on),
    retract_rule(Type2),
    insert_rule(Type2,NewDef).
                
dz_subset_fdtypes(_Type1, Type2) :- 
    type_parameter(Type2),
    param_matching_mode(off),!.
              
    
dz_subset_fdtypes(Type1, _Type2) :- % Redundant -PLG
    bot_type(Type1),
    !.
dz_subset_fdtypes(_Type1, Type2) :- % Redundant -PLG
    bot_type(Type2),
    !,
    fail.
dz_subset_fdtypes(_Type1, Type2) :- % Redundant -PLG
    top_type(Type2),
    !.
dz_subset_fdtypes(Type1, _Type2) :- % Redundant -PLG
    top_type(Type1),
    !,
    fail.
%
dz_subset_fdtypes(Type1, Type2) :-
    var_type(Type2),
    !,
    var(Type1).
dz_subset_fdtypes(Type1, _Type2) :-
    var_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, _Type2) :-
    ground_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    ground_type(Type2),
    !,
    type_included_in_ground(Type1).
dz_subset_fdtypes(Type1, Type2) :-
    atom_type(Type2),
    !,
    atom_constant(Type1, _).
dz_subset_fdtypes(Type1, _Type2) :-
    atom_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    numeric_type(Type2),
    !,
    type_included_in_numeric(Type1).
dz_subset_fdtypes(Type1, _Type2) :-
    numeric_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    int_type(Type2),
    !,
    type_included_in_int(Type1).
dz_subset_fdtypes(Type1, _Type2) :-
    int_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    nnegint_type(Type2),
    !,
    type_included_in_nnegint(Type1).
    %% nnegint_constant(Type1, _).
dz_subset_fdtypes(Type1, _Type2) :-
    nnegint_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    float_type(Type2),
    !,
    type_included_in_float(Type1).
    %% float_constant(Type1, _).
dz_subset_fdtypes(Type1, _Type2) :-
    float_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    struct_type(Type2),
    !,
    type_included_in_struct(Type1).
dz_subset_fdtypes(Type1, _Type2) :-
    struct_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    ground_struct_type(Type2),
    !,
    type_included_in_ground_struct(Type1).
dz_subset_fdtypes(Type1, _Type2) :-
    ground_struct_type(Type1),
    !,
    fail.
dz_subset_fdtypes(Type1, Type2) :-
    constant_symbol(Type1, C1),
    constant_symbol(Type2, C2),
    !,
    C1 == C2.
dz_subset_fdtypes(Type1, _Type2) :-
    constant_symbol(Type1, _),
    !,
    fail.
dz_subset_fdtypes(_Type1, Type2) :-
    constant_symbol(Type2, _),
    !,
    fail.

% ---------------------------------------------------------------------------------------------
% T1<=T2| term | bot | f(X) | var | gnd  | atm | num | int |nnegi| flt |struct|gndstr|Const | s
% ---------------------------------------------------------------------------------------------
% term  | T    | F   | F    | F   | F    | F   | F   |  F  | F   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% bot   | T    | T   | T    | T   | T    | T   | T   | T   | T   | T   | T    | T    | T    | s
% ---------------------------------------------------------------------------------------------
% f(X)  | T    | F   | B ?  | F   | A ?  | F   | F   | F   | F   | F   | T    | A ?  | F    | B ?
% ---------------------------------------------------------------------------------------------
% var   | T    | F   |  F*  | T   | A F  | F   | F   | F   | F   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% gnd   | T    | F   |  F*  | F   | T    | F   | F   | F   | F   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% atm   | T    | F   |  F*  | F   | A T  | T   | F   | F   | F   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% num   | T    | F   |  F*  | F   | A T  | F   | T   | F   | F   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% int   | T    | F   |  F*  | F   | A T  | F   | T   | T   | F   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% nnegi | T    | F   |  F*  | F   | A T  | F   | T   | T   | T   | F   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% flt   | T    | F   |  F*  | F   | A T  | F   | T   | F   | F   | T   | F    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% struct| T    | F   |  F*  | F   | A F  | F   | T   | F   | F   | F   | T    | F    | F    | s
% ---------------------------------------------------------------------------------------------
% gndstr| T    | F   |  F*  | F   | A T  | F   | F   | F   | F   | F   | T    | T    | F    | s
% ---------------------------------------------------------------------------------------------
% Const | T    | F   |  F*  | F   | A T  | C ? | C?  | C?  | C?  | C?  | F    | F    | D    | s
% ---------------------------------------------------------------------------------------------
% s     | T    | F   |      | F   | A ?  |     |     |     |     |     |      |      |      | T
% ---------------------------------------------------------------------------------------------
% X     |      |     |      | T   |      |     |     |     |     |     |      |      |      |
% ---------------------------------------------------------------------------------------------

% NOTE: Need to add a variable term (X) to the table.
%
% Here f(X) is a type term (can contain variables, type symbols, ...)
%
% A: T <-> is_ground_type( f(X) ).
%
% B: dz_subset_v([Type1], [[Type2]]).
%
% C: If constant is in type true, else false.
%
% D: If are equal then T of them else F.

dz_type_selects(Type1, Type2) :-
    dz_subset_lattice(Type1, Type2),
    !.
dz_type_selects(Type1, Type2) :-
    compound_pure_type_term(Type1, _Term1, Name1, Arity1),
    !,
    (
        struct_type(Type2)
    ;
        compound_pure_type_term(Type2, _Term2, Name1, Arity1)
    ).

% ========================================================================

:- pred basic_lattice_type_includes_compound_type_term(Type)
# "True iff @var{Type} includes compound type terms.".

basic_lattice_type_includes_compound_type_term(Type) :-
      struct_type(Type).

:- pred basic_lattice_type_needs_intersection_with_compound_type_term_args(
    Type, IntersecWith) # "True iff the intersection of @var{Type}
    and a compound type term requires performing the intersections
    of each of the compound type term arguments with the type
    @var{IntersecWith}. Note that Top type has been considered
    before (in @verb{type_intersection/3} of typeslib module),
    thus it is not considered here.".

basic_lattice_type_needs_intersection_with_compound_type_term_args(Type,
        Intersec_with) :-
    ground_type(Type),
    !,
    Intersec_with = Type.
basic_lattice_type_needs_intersection_with_compound_type_term_args(Type,
        Intersec_with) :-
    ground_struct_type(Type),
    !,
    set_ground_type(GndType),
    Intersec_with = GndType.

% ========================================================================

:- pred regtype_basic_type_intersection(Type1, Type2, Intersec) #
    "Defines the basic intersection operations in the type
    lattice: @var{Intersec} is the intersection of @var{Type1} and
    @var{Type2}. However, it does not define inclusion relations
    involving compound type terms nor rule type symbols. These
    relations are defined by other predicates. The reason for this
    separate treatment is that it avoids recursive calls in
    @verb{regtype_basic_type_intersection/3}, making type
    operations more flexible wrt changes in the type lattice and
    easing modifications. However, the separate treatment of
    compound type terms and rule type symbols does not involve a
    lost in generality of type operations, since it is assumed
    that compound type terms and rule type symbols are present in
    all regular type lattices. For example, in order to redefine
    the type intersection operation for a new regular type
    lattice, it suffices to redefine
    @verb{regtype_basic_type_intersection/2} (which defines basic
    intersection operations between types in the lattice, except
    those involving compound type terms and rule type symbols), and
    @verb{basic_lattice_type_needs_intersection_with_compound_type_term_args/2}.".

% Modified by ASM, 5-09-12 => intersection of two vars should be var
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    var_type(Typ1),
    !,
    ( var_type(Typ2) ->
        set_var_type(Intersec)
    ; set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, TypeInter) :-
    ground_type(Typ1),
    !,
    (
        struct_type(Typ2) ->
        set_ground_struct_type(TypeInter)
    ;
        TypeInter = Typ2
    ).
regtype_basic_type_intersection(Typ1, Typ2, TypeInter) :-
    ground_type(Typ2),
    !,
    (
        struct_type(Typ1) ->
        set_ground_struct_type(TypeInter)
    ;
        TypeInter = Typ1
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    atom_type(Typ1),
    !,
    (
        atom_constant(Typ2, _) ->
        Intersec = Typ2
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    atom_type(Typ2),
    !,
    (
        atom_constant(Typ1, _) ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    numeric_type(Typ1),
    !,
    (
        type_included_in_numeric(Typ2)
    -> Intersec = Typ2
    ; set_bottom_type(Intersec)).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    numeric_type(Typ2),
    !,
    (
        type_included_in_numeric(Typ1) ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    int_type(Typ1),
    !,
    (
        type_included_in_int(Typ2) ->
        Intersec = Typ2
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    int_type(Typ2),
    !,
    (
        type_included_in_int(Typ1) ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    nnegint_type(Typ1),
    !,
    (
        type_included_in_nnegint(Typ2) ->
        Intersec = Typ2
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    nnegint_type(Typ2),
    !,
    (
        type_included_in_nnegint(Typ1) ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    float_type(Typ1),
    !,
    (
        type_included_in_float(Typ2) ->
        Intersec = Typ2
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    float_type(Typ2),
    !,
    (
        type_included_in_float(Typ1) ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    struct_type(Typ1),
    !,
    (
        ground_struct_type(Typ2) ->
        Intersec = Typ2
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    struct_type(Typ2),
    !,
    (
        ground_struct_type(Typ1) ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).
regtype_basic_type_intersection(Typ1, _Typ2, Intersec) :-
    ground_struct_type(Typ1),
    !,
    set_bottom_type(Intersec).
regtype_basic_type_intersection(_Typ1, Typ2, Intersec) :-
    ground_struct_type(Typ2),
    !,
    set_bottom_type(Intersec).
regtype_basic_type_intersection(Typ1, Typ2, Intersec) :-
    constant_symbol(Typ1, C1),
    constant_symbol(Typ2, C2),
    !,
    (
        C1 == C2 ->
        Intersec = Typ1
    ;
        set_bottom_type(Intersec)
    ).

% ========================================================================

% -------------------------------------------------------------------------------------------
% T1 T2 | term | bot | f(X) | var | gnd  | atm | num | int |nnegi| flt |struct|gndstr|Const
% -------------------------------------------------------------------------------------------
% term  | term |     |      |     |      |     |     |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% bot   | bot  | bot |      |     |      |     |     |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% f(X)  | f(X) | bot |  C   |     |      |     |     |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% var   | var  | bot | bot  | var |      |     |     |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% gnd   | gnd  | bot |  A   | bot | gnd  |     |     |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% atm   | atm  | bot | bot  | bot | atm  | atm |     |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% num   | num  | bot | bot  | bot | num  | bot | num |     |     |     |      |      |
% -------------------------------------------------------------------------------------------
% int   | int  | bot | bot  | bot | int  | bot | int | int |     |     |      |      |
% -------------------------------------------------------------------------------------------
% nnegi |nnegi | bot | bot  | bot |nnegi | bot |nnegi|nnegi|nnegi|     |      |      |
% -------------------------------------------------------------------------------------------
% flt   | flt  | bot | bot  | bot | flt  | bot | flt | bot | bot | flt |      |      |
% -------------------------------------------------------------------------------------------
% struct|struct| bot | f(X) | bot |gndstr| bot | bot | bot | bot | bot |struct|      |
% -------------------------------------------------------------------------------------------
% gndstr|gndstr| bot | A    | bot |gndstr| bot | bot | bot | bot | bot |gndstr|gndstr|
% -------------------------------------------------------------------------------------------
% Const |Const | bot | bot  | bot |Const | B   | B   | B   | B   | B   | bot  | bot  | D
% -------------------------------------------------------------------------------------------
%
% A: call compound_pure_type_term_intersection/3
%
% B: If Const is in the type then Const else 0.
%
% C: call arg_typ_inter/4.
%
% D: If are equal then any of them else 0.

 %% Note: Make sure what this clause has to test between the following
 %% alternatives:
 %%  1) At least one of Typ1 or Typ2 is a type symbol defined in the set
 %%     of type rules.
 %%  2) At least one of Typ1 or Typ2 is a type symbol which should be
 %%     defined in the set of type rules, although perhaps, at the
 %%     time the clause is executed, the type rule defining Typ1 or Typ2
 %%     is not yet put in the set of type rules (at the end, such type
 %%     rule is put in the set of type rules).

% ========================================================================

 %% Was
 %% define_a_ground_type(Type) :-
 %%    fdtypes_included_in_ground_type(Type).

% Succeds is Type is a constant or a pure type term which
% do not contain type symbols.

define_a_ground_type(Type) :-
    constant_symbol(Type, _Constant),
    !.
define_a_ground_type(Type) :-
    define_a_ground_struct_type(Type).

define_a_ground_struct_type(Type) :-
    compound_pure_type_term(Type, Term, _Name, Arity),
    define_a_ground_type_aux(Arity, Term).

define_a_ground_type_aux(0, _Term).
define_a_ground_type_aux(A, Term) :-
    A > 0,
    arg(A, Term, Arg),
    define_a_ground_type(Arg),
    NA is A - 1,
    define_a_ground_type_aux(NA, Term).

%% ground_term_2(0, _Type).
 %% ground_term_2(A, Type) :-
 %%       arg(A, Type, Arg),
 %%       functor_pure_type_term(Arg),
 %%       NA is A - 1,
 %%       ground_term_2(NA, Type).


 %
 %% From nftypes:
 %% ground_term(Type) :-
 %%       functor_pure_type_term(Type),
 %%       functor(Type, _F, A),
 %%       ground_term_2(A, Type).
 %%
 %% ground_term_2(0, _Type).
 %% ground_term_2(A, Type) :-
 %%       arg(A, Type, Arg),
 %%       functor_pure_type_term(Arg),
 %%       NA is A - 1,
 %%       ground_term_2(NA, Type).


 %% define_a_ground_type(Type) :-
 %%    current_type_lattice(Lattice),
 %%    define_a_ground_type_lattice(Lattice, Type).
 %%
 %% define_a_ground_type_lattice(regtypes, Type) :-
 %%    !,
 %%    leq_than_ground_type(Type).
 %% define_a_ground_type_lattice(fdtypes, Type) :-
 %%    fdtypes_included_in_ground_type(Type).

%% leq_than_ground_type(Type) :-
%%      numeric_type(Type);
%%      atom_type(Type);
%%      number_constant(Type, _);
%%      atom_constant(Type, _).

% ========================================================================

:- regtype pure_type_term(X)
    # "@var{X} is a term defining a regular type".
:- impl_defined(pure_type_term/1).


:- pred compound_pure_type_term(+Type, -Comp, -Name, -Arity)
    # "@var{Type} represents a pure type term with main functor
       @var{Name} of arity greater than zero @var{Arity}.
       @var{Comp} is the corresponding compound term with main functor
       @var{Name} of arity @var{Arity}. ".

compound_pure_type_term(Type, Term, Name, Arity) :-
    nonvar(Type),
    Type = ^(Term),
    nonvar(Term),
    functor(Term, Name, Arity),
    Arity > 0,
    % \+ Term = [_|_],
    !.
compound_pure_type_term(Type, Type, (.), 2) :-
    nonvar(Type),
    Type = [_|_].

:- pred construct_compound_pure_type_term(+Comp, -Type) # "@var{Comp}
    is a compound term with main functor @var{Name} of arity
    @var{Arity}.  @var{Type} represents a pure type term with main
    functor @var{Name} of arity greater than zero
    @var{Arity}. @var{Type} can have as main functor the scape
    functor @verb{(^)/1}.".

construct_compound_pure_type_term(Comp, ^(Comp) ) :-
    nonvar(Comp),
    functor(Comp, Name, Arity),
    Arity > 0,
    \+ Name/Arity = (.)/2,
    !.
construct_compound_pure_type_term(Comp, Comp) :-
    nonvar(Comp),
    Comp = [_|_].


% CONSTANTS

atom_constant(Type, Type) :-
    nonvar(Type),
    Type = [],
    !.
atom_constant(Type, Term) :-
    nonvar(Type),
    Type = ^(Term),
    atom(Term).

number_constant(Type, Type) :-
    number(Type),
    !.
number_constant(Type, Term) :-
    nonvar(Type),
    Type = ^(Term),
    number(Term).

float_constant(Type, Type) :-
    float(Type),
    !.
float_constant(Type, Term) :-
    nonvar(Type),
    Type = ^(Term),
    float(Term).

% fdtypes

int_constant(Type, Type) :-
    integer(Type),
    !.
int_constant(Type, Term) :-
    nonvar(Type),
    Type = ^(Term),
    integer(Term).

nnegint_constant(Type, Type) :-
    integer(Type),
    Type >= 0, % Changed by PLG Dec-18-98 was Type > 0,
    !.
nnegint_constant(Type, Term) :-
    nonvar(Type),
    Type = ^(Term),
    integer(Term),
    Term >= 0.

%
:- pred constant_symbol(Type, Constant)
    # "@var{Type} is the type representation of the @tt{constant}
       @var{Constant} (numeric or non-numeric).".

constant_symbol(Type, Constant) :-
    atom_constant(Type, Constant);
    number_constant(Type, Constant);
    int_constant(Type, Constant);
    float_constant(Type, Constant);
    nnegint_constant(Type, Constant).

% Define this better?
% Use
% number_constant(Type)
% atom_constant(Type)

% is_numeric_type(X) :- number(X).
% is_atom_type(X) :- atom(X).
% is_var_type(X) :- var(X).

:- pred translate_lattice_types(Functor, Arity, Goal, NGoal)
    # "Some type checking predicates correspond to basic types in
      the lattice but with a different name. This predicate makes
      the conversion from the type check to the basic type. This
      allows using @tt{native_prop(NGoal, regtype(_))} to determine
      whether @var{Goal} is a regular type check.".

translate_lattice_types('term_typing:integer', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:int', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types('term_typing:float', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:flt', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types('term_typing:number', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:num', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types('term_typing:atom', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:atm', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types(_, _, Goal, Goal).

%----------------------------------------------------------------------%
% Generation of source code for storing types from libraries.
%----------------------------------------------------------------------%
:- use_module(library(write), [writeq/2]).
:- use_module(library(read), [read/2]).

:- pred cleanup_lib_param_symbol

# "Cleans up all facts of lib_param_symbol/2 predicate.".

cleanup_lib_param_symbol:-
    retractall_fact(lib_param_symbol(_,_)).

%----------------------------------------------------------------------%

:- pred gen_lib_param_symbol(Stream)

# "Writes the facts for lib_param_symbol/2 to the stream @var{Stream}
  from pgm_param_symbol/2.".

gen_lib_param_symbol(Stream):-
    nl(Stream),
    pgm_param_symbol(A,B),
    writeq(Stream,lib_param_symbol(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
gen_lib_param_symbol(_Stream).  

%----------------------------------------------------------------------%

:- pred load_lib_param_symbol(Stream)

# "Loads the facts for lib_param_symbol/2 from the stream @var{Stream}.".

load_lib_param_symbol(Stream):-
    repeat,
    read(Stream,Fact),
    (
        Fact = end_of_file ->
        true
    ;
        assertz_fact(Fact),
        fail
    ).

save_dz_pairs(Ps) :-
    findall(pgm_dz_pair(A,B),pgm_dz_pair(A,B),Ps).

restore_dz_pairs([pgm_dz_pair(A,B)|Ps]):-
    assertz_fact(pgm_dz_pair(A,B)),
    restore_dz_pairs(Ps).
restore_dz_pairs([]).

