:- module(nfsets, [
    add_item_to_typassign/4,
    change_type_in_typassgn/4,
    create_minset_and_project/4,
    generate_type_annotated_term/4,
    included/2,
    included_ta_term_in_tuple/2,
    remove_item_from_typAss/3,
    simplify_conjunctions/2,
    ta_term_basicset_intersec/3,
    ta_term_empty/1,
    translate_to_bool_format/2,
    closed_var_list/2 % TODO: predicate used outside nfdet (non-local)
], [assertions, isomodes]).

% Local module required by PLAI-based and NFGRAPH-based analyses
:- doc(title, "Manipulation of minsets, and basic and cobasic sets").
:- doc(author, "Pedro L@'{o}pez"). % (original: 3 Aug 1995)

:- use_module(library(lists), [length/2, append/3]).
:- use_module(library(iso_misc), [unify_with_occurs_check/2]).
:- use_module(typeslib(typeslib), [
    set_top_type/1,
    bot_type/1,
    is_empty_type/1,
    set_bottom_type/1,
    create_new_type_rule/2,
    type_intersection_0/3]).
:- use_module(domain(termsd), [
    find_list_entry/3,
    compute_type/3]).

% ---------------------------------------------------------------------------
   
:- pred generate_type_annotated_term(+ModeType, +UseMasc, ?Masc, -Ta_Term)

# "Creates a type-annotated term @var{Ta_Term} of the form (BasicSet,
TypeAss), where BasicSet is a list of distinct variables (each
variable corresponds to an input argument of the predicate, in the
left to right order). TypeAss is a type assigment which assigns the
type expressed in @var{ModeType} to each variable of BasicSet.
e.g. generate_type_annotated_term(p(in:term, in:term, out:term), ([B,
A],[A:term, B:term])).".

generate_type_annotated_term(ModeType, UseMasc, Masc, Ta_Term) :-
    functor(ModeType, _, A),
    ( UseMasc == true ->
        generate_a_type_annotated_term_WITH_masc(1, A, ModeType, Masc, Ta_Term)
    ; generate_a_type_annotated_term_WITHOUT_masc(1, A, ModeType, Ta_Term)
    ).


generate_a_type_annotated_term_WITHOUT_masc(1, A, ModeType, Ta_Term) :-
    generate_basicset_and_typeass(1, A, ModeType, BasicSet, TypeAss),
    construct_ta_term(BasicSet, TypeAss, Ta_Term).

construct_ta_term(BasicSet, TypeAss, (BasicSet, TypeAss)).

generate_a_type_annotated_term_WITH_masc(1, A, ModeType, Masc, OuTa_Term) :-
    copy_term(Masc, NewMasc),
    gen_basic_typeass_mascbasic(1, A, ModeType, NewMasc, BasicSet, TypeAss, MascBasicSet),
    construct_ta_term(BasicSet, TypeAss, Ta_Term),
    ( ta_term_basicset_intersec_0(Ta_Term, MascBasicSet, TmpTa_Term) ->
        OuTa_Term = TmpTa_Term
    ; OuTa_Term = ([], [])
    ).

generate_basicset_and_typeass(N, A, _ModeType, [], []) :- N > A, !.
generate_basicset_and_typeass(N, A, ModeType, BasicSet, TypeAss) :-
    N =< A,
    !,
    arg(N, ModeType, Mode:Type),
    ( Mode = in ->
        BasicSet = [Var|RBasics],
        TypeAss = [Var:Type|RTypeAss]
    ; BasicSet = RBasics,
      TypeAss = RTypeAss
    ),
    N1 is N + 1,
    generate_basicset_and_typeass(N1, A, ModeType, RBasics, RTypeAss).


gen_basic_typeass_mascbasic(N, A, _ModeType, _Masc, [], [], []) :- N > A, !.
gen_basic_typeass_mascbasic(N, A, ModeType, Masc, BasicSet, TypeAss, MascBasicSet) :-
    N =< A,
    !,
    arg(N, ModeType, Mode:Type),
    ( Mode = in ->
        BasicSet = [Var|RBasics],
        TypeAss = [Var:Type|RTypeAss],
        arg(N, Masc, ArgNMasc),
        MascBasicSet = [ArgNMasc|ReMascBasicSet]
    ; BasicSet = RBasics,
      TypeAss = RTypeAss,
      MascBasicSet = ReMascBasicSet
    ),
    N1 is N + 1,
    gen_basic_typeass_mascbasic(N1, A, ModeType, Masc, RBasics, RTypeAss, ReMascBasicSet).


:- pred ta_term_basicset_intersec(+Ta_Term, +Basic_Set, -Out_Ta_term)

# "Creates a type annotated term @var{Out_Ta_term} which is the intersection
of the type annotated term @var{Ta_Term} and the basic set @var{Basic_Set}.
@var{Ta_Term} and @var{Basic_Set} are not modified.  The variables in @var{Out_Ta_term}
are fresh.".

ta_term_basicset_intersec(Ta_Term, Basic_Set, OTa_Term) :-
    ( ta_term_basicset_intersec_0(Ta_Term, Basic_Set, TeTa_Term) ->
        OTa_Term = TeTa_Term
    ; set_ta_term_empty(OTa_Term)
    ).

ta_term_basicset_intersec_0(Ta_Term, Basic_Set, OTa_Term) :-
    Ta_Term = (Term, TypeAss),
    var_list((Term, Basic_Set), Var_List),
    copy_term(Term, New_Term),
    copy_term(Basic_Set, New_Basic_Set),
    var_list((New_Term, New_Basic_Set), New_Var_List),
    unify_with_occurs_check(New_Term, New_Basic_Set),
    compute_types(Var_List, New_Var_List, TypeAss, Types),
    var_list(New_Term, New_Term_Vars),
%% init_typ_symbol_counter, % warning!!
    intersec_types(New_Term_Vars, Types, [], F_TypeAss),
    OTa_Term = (New_Term, F_TypeAss).
%%      Commented 29 Oct 96
%%      normalize(F_TypeAss, [], New_Term, O_TypeAss),
%%      OTa_Term = (New_Term, O_TypeAss).

%% Old version
%% ta_term_basicset_intersec(Ta_Term, Basic_Set, OTa_Term) :-
%%      Ta_Term = (Term, TypeAss),
%%      var_list((Term, Basic_Set), Var_List),
%%      copy_term(Term, New_Term),
%%      copy_term(Basic_Set, New_Basic_Set),
%%      var_list((New_Term, New_Basic_Set), New_Var_List),
%%      unify_with_occurs_check(New_Term, New_Basic_Set),
%%      compute_types(Var_List, New_Var_List, TypeAss, Types),
%%      var_list(New_Term, New_Term_Vars),
%%      %% init_typ_symbol_counter, % warning!!
%%      intersec_types(New_Term_Vars, Types, [], F_TypeAss),
%%      OTa_Term = (New_Term, F_TypeAss). 
%%  %%      Commented 29 Oct 96
%%  %%      normalize(F_TypeAss, [], New_Term, O_TypeAss),
%%  %%      OTa_Term = (New_Term, O_TypeAss).

%% Comme 1_dec-96
%% ta_term_basicset_intersec(Ta_Term, Basic_Set, OTa_Term) :-
%%      Ta_Term = (Term, TypeAss),
%%      var_list((Term, Basic_Set), Var_List),
%%      copy_term(Term, New_Term),
%%      copy_term(Basic_Set, New_Basic_Set),
%%      var_list((New_Term, New_Basic_Set), New_Var_List),
%%      unify_with_occurs_check(New_Term, New_Basic_Set),
%%      compute_types(Var_List, New_Var_List, TypeAss, Types),
%%      var_list(New_Term, New_Term_Vars),
%%      %% init_typ_symbol_counter, % warning!!
%%      intersec_types(New_Term_Vars, Types, [], F_TypeAss),
%%      OTa_Term = (New_Term, F_TypeAss). 
%%  %%      Commented 29 Oct 96
%%  %%      normalize(F_TypeAss, [], New_Term, O_TypeAss),
%%  %%      OTa_Term = (New_Term, O_TypeAss).


%% Old version 14 Nov 96.
%% generate_type_annotated_term(ModeType, (BasicSet, OutTypeAss)) :-
%%    functor(ModeType, _, A),
%%    generate_basicset_and_typeass(1, A, ModeType, BasicSet, TypeAss),
%%    convert_typass(TypeAss, CTypAsg),
%%    normalize(CTypAsg, [], BasicSet, OutTypeAss).

% (was in ppoint.pl)
:- export(compute_types/4).
:- pred compute_types(+Var_List, +Term_List, +Type_Ass, -Types)
   # "Given the substitution which can be represented as subs(@var{Var_List},
      @var{Term_List}), computes the type corresponding to each variable in the
      list of terms @var{Term_List}, and store it in the data structure @var{Types}.
      @var{Types} have the structure [vt(Var1, TypeList1), ..., vt(VarN,
      TypeListN)|_], where TypeListN is the list of types corresponding to
      variable VarN.".

%% Note: we assume that bottom types are removed (and do not have any
%% type rule defining a bottom type), and that type symbols
%% equivalent to top are of the form T -> [top].

compute_types(Var_List, Term_List, _Type_Ass, _Types) :-
    var(Var_List), var(Term_List), !.
compute_types(VL, TL, Type_Ass, Types) :-
    nonvar(VL), nonvar(TL),
    VL = [Var|Var_List], TL = [Term|Term_List],
    ( find_type(Type_Ass, Var, Type) -> true ; set_top_type(Type) ),
    compute_type(Term, Type, Types),
    compute_types(Var_List, Term_List, Type_Ass, Types).

:- export(find_type/3).
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

% TODO: merge with termsd.pl predicates?
% These predicates for eterms:
intersec_types(Var_List, _Var_Types, OTypeAss, OTypeAss) :-
    var(Var_List), !.
intersec_types(Var_List, Var_Types, ITypeAss, OTypeAss) :-
    nonvar(Var_List), 
    Var_List = [Var|List],
    find_list_entry(Var_Types, Var, vt(_, Types)),
    set_top_type(Top),
    intersec_type_list(Types, Top, LType),
    \+ bot_type(LType),
    intersec_types(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).

intersec_type_list(Type_List, Type, Type) :-
    var(Type_List), !.
intersec_type_list(Type_List, InType, OutType) :-
    nonvar(Type_List),
    Type_List = [Type | List],
    type_intersection_0(InType, Type, Intersec),
    ( is_empty_type(Intersec) -> 
        set_bottom_type(OutType) % , retract_1 -PL
    ; intersec_type_list(List, Intersec, OutType)
    ).

%%-----------------------------------------------------------------------------
%% type annotated terms

% Checks that the type annotated term X is empty.

ta_term_empty((_Term, TypAss)) :-
    TypAss == empty_type_assignment.

set_ta_term_empty((_Term, TypAss)) :-
    TypAss = empty_type_assignment.

%% %% normalize(TypeAss, TypeAss1, Subs, NewTypeAss, NewSubs)
%% %% Input: two type assignments TypeAss and TypeAss1, and an idempotent
%% %%      substitution Subs. 
%% %% 
%% %% Output: A pair (NewTypeAss, NewSubs), where: 
%% %%   a) NewTypeAss is a type assignment
%% %%   of the form $(x_1:T_1, \ldots, x_k:T_k)$, where each $T_i$, 
%% %%   $1 \leq i \leq k$ is a type expression which is either, a union type, 
%% %%   or $top$, and b) NewSubs is an idempotent substitution.
%% 
%% normalize_4([], TypeAss, _Term, TypeAss).
%% normalize_4([Var:Type|TypeAss], InTypeAss, Term, OutTypeAss) :-
%%      define_a_ground_type(Type),
%%      !,
%%      Var = Type,
%%      normalize_4(TypeAss, InTypeAss, Term, OutTypeAss).
%% normalize_4([Var:Type|TypeAss], InTypeAss, Term, OutTypeAss) :-
%% % functor(Type, F, A),
%%      compound_pure_type_term(Type, _Term, F, A),
%% % F/A \== '$typedef$'/1, F/A \== '$top$'/0,
%%      !,
%%      functor(NTerm, F, A), Var = NTerm,
%%      normalize_args(A, NTerm, Type, TypeAss, InTypeAss, Term, OutTypeAss).
%% normalize_4([Var:Type|TypeAss], InTypeAss, Term, OutTypeAss) :-
%%      normalize_4(TypeAss, [Var:Type|InTypeAss], Term, OutTypeAss).
%% 
%% normalize_args(0, _NTerm, _Type, TypeAss, InTypeAss, Term, OutTypeAss) :-
%%      normalize_4(TypeAss, InTypeAss, Term, OutTypeAss).
%% normalize_args(A, NTerm, Type, TypeAss, InTypeAss, Term, OutTypeAss) :-
%%      arg(A, NTerm, Var),
%%      arg(A, Type, TypeArg),
%%      NA is A - 1,
%%      normalize_args(NA, NTerm, Type, [Var:TypeArg|TypeAss], InTypeAss,
%%          Term, OutTypeAss).

:- pred create_minset_and_project(+Var_list, +Test_List, -Other_Tests, -PMinset)

# "IMPORTANT NOTE: This procedure needs to be modified to compute the projection over
  the variables in Var_list correctly.

@var{Var_list}: a list containing the input variables of a predicate.
Each variable corresponds to a input argument of the predicate. The
variables are ordered according to the argument number (in left to
right order) they correspond to.  @var{Test_List}: a list of
unification tests.  @var{PMinset}: a minset. @var{PMinset} is
@var{Test_List} in minset format.  The minset is represented as
minset(Term, CoBasicList).".

create_minset_and_project(Var_list, Test_List, Other_Tests, PTest) :-
%% compute the list of variables Eliminable_Vars which are in Test_List
%% and are not in Var_list, i.e. variables that should be elimined,
%% because they are existentally cuantified.
    closed_var_list(Test_List, Test_Vars),
    vset_diff(Test_Vars, Var_list, Eliminable_Vars),
%%
    append(Var_list, Eliminable_Vars, Vars_Tested),
    list_2_minset_test_format(Test_List, Vars_Tested, Other_Tests, Test),
    ( Test == false ->
        PTest = false
    ; project_minset(Var_list, Test, PTest)
    ).

project_minset(Var_list, test(Minset, Others), test(PMinset, Others)) :-
    project_minset_0(Var_list, Minset, PMinset).

project_minset_0(Var_list, minset(BasicSet, CoBasicSets), minset(PBasicSet, PCoBasicSets)) :-
    project_basicset(Var_list, BasicSet, PBasicSet),
    project_cobasicsets(CoBasicSets, Var_list, PCoBasicSets).


project_basicset([], _BasicSet, []) :- !.
project_basicset([_Var|Var_list], [BVar|BasicSet], [BVar|PBasicSet]) :-
    project_basicset(Var_list, BasicSet, PBasicSet).

project_cobasicsets([], _Var_list, []).
project_cobasicsets([CoBasic|CoBasicSets], Var_list, [PCoBasic|PCoBasicSets]) :-
    project_basicset(Var_list, CoBasic, PCoBasic),
    project_cobasicsets(CoBasicSets, Var_list, PCoBasicSets).

simplify_conjunctions([], []).
simplify_conjunctions([Conj|NBTest], OutConj) :-
    ( simplify_conjunction(Conj, SConj) ->
        OutConj = [SConj|SNBTest]
    ; OutConj = SNBTest
    ),
    simplify_conjunctions(NBTest, SNBTest).

%% NBTest is supposed to be non-empty.

simplify_conjunction(NBTest, minset(SBasic, CoBasicList)) :-
    separate_basics_and_cobasics(NBTest, Basic, CoBasic),
    ( Basic = [] ->
        NBTest = [not(CoBset)|_],
        gen_basic_set(CoBset, SBasic)
    ; Basic = [BasicSet|_],
      basic_set_intersection(Basic, BasicSet, SBasic)
    ),
    simp_cobasic_sets(CoBasic, SBasic, CoBasicList).

gen_basic_set(CoBset, SBasic) :-
    length(CoBset, N),
    length(SBasic, N).

separate_basics_and_cobasics([], [], []).
separate_basics_and_cobasics([not(S)|Rest], Bas, [not(S)|CoBas]) :-
    !,
    separate_basics_and_cobasics(Rest, Bas, CoBas).
separate_basics_and_cobasics([S|Rest], [S|Bas], CoBas) :-
    separate_basics_and_cobasics(Rest, Bas, CoBas).

basic_set_intersection([], BasicInt, BasicInt) :- !.
basic_set_intersection([Basic|BList], IBasicInt, OBasicInt) :-
    basic_intersec(IBasicInt, Basic, Int),
    basic_set_intersection(BList, Int, OBasicInt).

basic_intersec(BSet1, BSet2, New_BSet1) :-
    copy_term(BSet1, New_BSet1),
    copy_term(BSet2, New_BSet2),
    unify_with_occurs_check(New_BSet1, New_BSet2).

simp_cobasic_sets([], _Bas, []).
simp_cobasic_sets([not(Cob)|CobList], Bas, OutCoBasicList) :-
    copy_term(Cob, NCob),
    copy_term(Bas, NBas),
    ( unify_with_occurs_check(NCob, NBas) ->
        OutCoBasicList = [NBas|CoBasicList]
    ; OutCoBasicList = CoBasicList
    ),
    simp_cobasic_sets(CobList, Bas, CoBasicList).

%% %% non_empty_intersec(+BSet1, +BSet2):
%% %%   Purpose: Succeeds if the intersection of the basic sets BSet1 and BSet2
%% %%      is not empty (i.e. BSet1 and BSet2 unify).
%% 
%% non_empty_intersec(BSet1, BSet2) :-
%%      copy_term(BSet1, New_BSet1),
%%      copy_term(BSet2, New_BSet2),
%%      unify_with_occurs_check(New_BSet1, New_BSet2).
%% 
%% %% non_empty_intersec_3(+BSet1, +BSet2, -Substitution):
%% %%   Purpose: Succeeds if the intersection of the basic sets BSet1 and BSet2
%% %%      is not empty (i.e. BSet1 and BSet2 unify).
%% %%      "Substitution" is the the mgu of BSet1 and BSet2 projected to the 
%% %%      variables of BSet1.
%% 
%% non_empty_intersec_3(BSet1, BSet2,
%%          subs(BSet1_Var_List, New_BSet1_Var_List)) :-
%%      var_list(BSet1, BSet1_Var_List),
%%      copy_term(BSet1, New_BSet1),
%%      var_list(New_BSet1, New_BSet1_Var_List),
%%      copy_term(BSet2, New_BSet2),
%%      unify_with_occurs_check(New_BSet1, New_BSet2).

%% included(Basic_Set1, Basic_Set):
%% Purpose: Succeeds if Basic_Set subsumes to Basic_Set1.

included(Basic_Set1, Basic_Set) :-
    copy_term(Basic_Set1, New_Basic_Set1),
    var_list(New_Basic_Set1, New_Basic_Set1_Var_List),
    assign_distinct_constants(New_Basic_Set1_Var_List, 1),
    copy_term(Basic_Set, New_Basic_Set),
    unify_with_occurs_check(New_Basic_Set1, New_Basic_Set).

%% included_ta_term_in_tuple(Ta_term, Tuple):
%% Purpose: Succeeds if Tuple subsumes to Ta_term.

included_ta_term_in_tuple(Ta_term, Tuple) :-
    Ta_term = (Tuple1, _TypAss),
    included(Tuple1, Tuple).


%% assign_distinct_constants(Var_List, Num):
%%    Assigns distinct constants (which do not appear in the type assigment nor
%%    in the tests) to the variables in Var_List.

assign_distinct_constants(Var_List, _Num) :-
    var(Var_List), !.
assign_distinct_constants(Var_List, Num) :-
    nonvar(Var_List),
    Var_List = [Var|Rest_Var_List],
    name(Num, Num_List),
    append(Num_List, "!@#$%^&", Constant_List),
    name(Var, Constant_List),
    NNum is Num + 1,
    assign_distinct_constants(Rest_Var_List, NNum).


%%-----------------------------------------------------------------------------
%% Operations on type assignments.

%% add_item_to_typassign(InTypAss, Var, Type, OuTypAss)
%% InTypAss: a type assignment.
%% Var: a variable.
%% Type: a type.
%% OuTypAss: a type assignment.
%% Description: adds the assignment Var:Type at the beginning of InTypAss,
%% obtaining OuTypAss.

add_item_to_typassign(InTypAss, Var, Type, OuTypAss) :-
    OuTypAss = [Var:Type|InTypAss].

%% change_type_in_typassgn(+Types, +Var, +InTypeAss, -OuTypeAss)
%% Types: a list of types.
%% Var: a variable.
%% InTypeAss: a type assignment.
%% OuTypeAss: a type assignment.
%% Description:  OuTypeAss is the result of replacing the type of
%%         variable Var in InTypeAss by Types. If Types is empty,
%%         then OuTypeAss is InTypeAss. If types have more than one
%%         item, then a type rule defining Types is created, and its
%%         type symbol is set as the type of Var in OuTypeAss.


change_type_in_typassgn([], _Var, ITypeAss, ITypeAss) :- !.
change_type_in_typassgn([Type], Var, ITypeAss, OTypeAss) :-
    !,
    replace_type_in_typeass(ITypeAss, Var, Type, OTypeAss).
change_type_in_typassgn([Type|Restypes], Var, ITypeAss, OTypeAss) :-
    !,
    create_new_type_rule([Type|Restypes], TypeSymbol),
    replace_type_in_typeass(ITypeAss, Var, TypeSymbol, OTypeAss).

%% replace_type_in_typeass(+InTypeAss, +Var, +Type, -OuTypAss)
%% InTypeAss: a type assignment.
%% Var: a variable.
%% Type: a type.
%% OuTypAss: a type assignment.
%% Description:  OuTypeAss is the result of replacing the type of
%%         variable Var in InTypeAss by Type.

replace_type_in_typeass([Var:_OldType|Rest], IVar, Type, [Var:Type|Rest]) :- Var == IVar, !.
replace_type_in_typeass([Var:OldType|Rest], IVar, Type, [Var:OldType|RTypass]) :-
    Var \== IVar,
    replace_type_in_typeass(Rest, IVar, Type, RTypass).

%% remove_item_from_typAss(+InTypeAss, +Var, -OuTypAss)
%% InTypeAss: a type assignment. 
%% Var: a variable. 
%% OuTypAss: a type assignment.
%% Description: remove the assignment Var:Type in InTypeAss,
%% obtaining OuTypAss.

remove_item_from_typAss([Var:_Type|Rest], IVar, Rest) :- Var == IVar, !.
remove_item_from_typAss([Var:Type|Rest], IVar, [Var:Type|RTypass]) :-
    Var \== IVar,
    remove_item_from_typAss(Rest, IVar, RTypass).

% ---------------------------------------------------------------------------

:- use_module(library(idlists), [member_0/2]).

% vset_diff(+L1, +L2, -L3) binds L3 to the set difference of L1 and L2,
% i.e., to the set of objects in L1 that are not in L2.

vset_diff(L1, L2, L3) :- vset_diff_4(L1, L2, [], L3).

vset_diff_4([X|L1], L2, L3in, L3out) :-
    ( member_0(X, L2) ->
        L3mid = L3in
    ; L3mid = [X|L3in]
    ),
    vset_diff_4(L1, L2, L3mid, L3out).
vset_diff_4([], _, L, L).

% TODO: use terms_var:varset/2? (note that VarSet is an open list)
% Creates an open list with the set of variables of a term.
var_list(X,VarSet) :- var(X),!,
    ins_without_dup(VarSet,X).
var_list([],_) :- !.
var_list([X|Xs],VarSet) :- !,
    var_list(X,VarSet),
    var_list(Xs,VarSet).
var_list(X,VarSet) :-
    X=..[_|Args],
    var_list(Args,VarSet).

% Insert an item in a list if it isn't in yet.
ins_without_dup(L,I) :- 
    var(L), !,
    L = [I|_].
ins_without_dup(L,I) :- 
    nonvar(L),
    L = [Item|_],
    Item==I, !.
ins_without_dup(L,I) :- 
    nonvar(L),
    L = [Item|List],
    I \== Item,
    ins_without_dup(List,I).

% TODO: similar to term_vars:varset/2 but order is preserved
% TODO: inefficient due to member_0/2
:- export(closed_var_list/2).
% Creates a (closed) list with the set of variables of a term.
closed_var_list(X, OVarSet) :-
    var_list_0(X, [], OVarSet).

var_list_0(X, IVarSet, OVarSet) :-
    var(X),
    !,
    add_variable_not_duplicates(X, IVarSet, OVarSet).
var_list_0([], IVarSet, IVarSet) :- 
    !.
var_list_0([X|Xs], IVarSet, OVarSet) :- 
    !,
    var_list_0(X, IVarSet, TeVarSet),
    var_list_0(Xs, TeVarSet, OVarSet).
var_list_0(X, IVarSet, OVarSet) :-
    X=..[_|Args],
    var_list_0(Args, IVarSet, OVarSet).

add_variable_not_duplicates(Var, List, OuList) :-
    % member_term(Var, List) % PLG May-17-2003 
    ( member_0(Var, List) ->
        OuList = List 
    ; OuList = [Var|List]
    ).

% ===========================================================================
%! # Conversion
%
%  Conversion of data to different formats

%% list_2_minset_test_format(+Test_List, +Vars_Tested, +Other_Tests, -Test)
%% Purpose: rewrites Test_List as a minset Minset. 
%% Test_List: a list of unification tests.
%% Vars_Tested: a list of variables.
%% Other_Tests:
%% Test:

list_2_minset_test_format(Test_List, Vars_Tested, Other_Tests, OutMinset) :-
    separate_eqs_and_diseqs(Test_List, Eqs, DisEqs),
    copy_term(t(Vars_Tested, Other_Tests, Eqs), t(NVars_Tested, NOther_Tests, NEqs)),
    ( solvable_eqs(NEqs) ->
        create_cobasic_sets(DisEqs, Vars_Tested, NVars_Tested, CoBasicList),
        OutMinset = test(minset(NVars_Tested, CoBasicList), NOther_Tests)
    ; OutMinset = false
    ).

create_cobasic_sets([], _Vars_Tested, _NVars_Tested, []).
create_cobasic_sets(['$noteq$'(X, Y)|DisEqList], Vars_Tested, NVars_Tested, OutCoBasicList) :-
    copy_term((Vars_Tested, =(X, Y)), (NVars, NEq)),
    solvable_eqs([NEq]),
    copy_term(NVars_Tested, Cobasic_Set),
    ( unify_with_occurs_check(Cobasic_Set, NVars) ->
        OutCoBasicList = [Cobasic_Set|CoBasicList]
    ; OutCoBasicList = CoBasicList
    ),
    create_cobasic_sets(DisEqList, Vars_Tested, NVars_Tested, CoBasicList).

%% convert_typass([],         []) :- !.
%% convert_typass([X:Type|L], [X:CType|CL]) :-
%%      convert_type(Type, CType),
%%      convert_typass(L, CL).
%% 
%% %% Conversion from Debray's type definition format to my format.  
%% %% Assign to all (anonymous) variables in Type, the type '$top$'.
%% %% It is assumed that a list represents a union, and that there is 
%% %% no union type in none of the items of the list.
%% 
%% %%  convert_type_union([], []).
%% %%  convert_type_union([Type|Typunion], [CType|CTypunion]):-
%% %%          convert_type(Type, CType),
%% %%          convert_type_union(Typunion, CTypunion).
%% 
%% convert_type(Type, '$top$') :-
%%      var(Type), !.
%% convert_type(top,  '$top$') :- !.
%% convert_type(Type, CType) :-
%%      functor(Type,  F, A),
%%      functor(CType, F, A),
%%      convert_type_3(A, Type, CType).
%% 
%% convert_type_3(0, _,    _) :- !.
%% convert_type_3(A, Type, CType) :-
%%      arg(A, Type, Arg),
%%      convert_type(Arg, CArg),
%%      arg(A, CType, CArg),
%%      NA is A - 1,
%%      convert_type_3(NA, Type, CType).

%% translate_to_bool_format(+MinsetList, -Disj):
%% write the list of minsets MinsetList (which represents a disjunction) 
%% into a representation using the functors ';' (disjunction) and 
%% ','(conjunction) .   

translate_to_bool_format([test(Minset, _Others)], Disj) :- !,
    b_trans_minset(Minset, Disj).
translate_to_bool_format([test(Minset, _Others)|Mlist], ';'(Disj, RDisj)) :- !,
    b_trans_minset(Minset, Disj),
    translate_to_bool_format(Mlist, RDisj).

b_trans_minset(minset(BasicSet, CoBasicSets), Conj) :-
    ( CoBasicSets = [] -> Conj = BasicSet
    ; b_trans_cobasicsets(CoBasicSets, PCoBasicSets),
      Conj = ','(BasicSet, PCoBasicSets)
    ).

b_trans_cobasicsets([CoBasicSet], not(CoBasicSet)) :- !.
b_trans_cobasicsets([CoBasic|CoBasicSets], ','(not(CoBasic), PCoBasicSets)) :-
    b_trans_cobasicsets(CoBasicSets, PCoBasicSets).

% ===========================================================================
%! # s_eqsolve
%
%  Solve a set of equations and disequations over the Herbrand domain.
%  (Original author: Saumya Debray, 3 Aug 1995)
%
%  Acknowledgements: The algorithm used is based on that described in
%    "Unification Revisited", by J.-L. Lassez, M. Maher and
%    K. Marriott, in "Foundations of Deductive Databases and Logic
%    Programming, ed. J. Minker, Morgan Kaufman, 1988, but I've made
%    no effort to be efficient.  In particular, when checking whether
%    a disequation is consistent with a set of equations E, this code
%    will reprocess all of E afresh instead of simply looking at its
%    solution.  This could (and should) be improved.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                 %%
%%  DATA REPRESENTATION: A set of equations and disequations is    %%
%%  represented as a list: an equation between t1 and t2 is        %%
%%  represented as a term '='(t1,t2), while a disequation between  %%
%%  t1 and t2 is represented as a term '$noteq$'(t1,t2).           %%
%%                                                                 %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% solvable(+S) is true iff the system of equations and disequations S
% is solvable.
%
% From Theorem 10 of [Lassez, Maher & Marriott 1988] (see above for
% complete citation), a system S consisting of a set of equations E
% and a set of disequations {I_1,...,I_n} is solvable iff each
% {E \union I_j} is solvable.  So it suffices to verify that
%
% (i)  E is solvable; and
% (ii) for each j in [1,...,n], {E \union E_j} has no solution, where
%      the equation E_j is the complement of the disequation I_j.

%% solvable(S) :-
%%      separate_eqs_and_diseqs(S, Eqs, DisEqs),
%%      solvable_eqs(Eqs),
%%      check_diseqs(DisEqs, Eqs).

% solvable_eqs(+Eqs) is true iff the set of equations Eqs is solvable.

solvable_eqs([]).
solvable_eqs(['='(LHS, RHS)|Eqs0]) :-
    rewrite_eq(LHS, RHS, Eqs0, Eqs1),
    solvable_eqs(Eqs1).

rewrite_eq(X, Y, Eqs, Eqs) :-
    var(X),
    var(Y),
    !,
    X = Y.
rewrite_eq(X, Y, Eqs, Eqs) :-
    var(X), /* nonvar(Y) */
    !,
    \+ occurs_in(X, Y),
    X = Y.
rewrite_eq(X, Y, Eqs0, Eqs1) :-
    var(Y), /* nonvar(X) */
    !,
    Eqs1 = ['='(Y, X)|Eqs0].
rewrite_eq(X, Y, Eqs0, Eqs1) :-
    functor(X, F, N),
    functor(Y, F, N),
    unwrap_eqs(N, X, Y, Eqs0, Eqs1).

%% % check_diseqs(+DisEqs, +Eqs) is true iff each disequation in the set
%% % DisEqs is consistent with the equation set Eqs.
%% 
%% check_diseqs([],                       _).
%% check_diseqs(['$noteq$'(X, Y)|DisEqs], Eqs) :-
%%      \+ solvable_eqs(['='(X, Y)|Eqs]),
%%      check_diseqs(DisEqs, Eqs).

%% *********************************************************************
%% *                                                                   *
%% *                             Utilities                             *
%% *                                                                   *
%% *********************************************************************

separate_eqs_and_diseqs([], [], []).
separate_eqs_and_diseqs([Eq|Rest], [Eq|Eqs], DisEqs) :-
    functor(Eq, '=', 2),
    !,
    separate_eqs_and_diseqs(Rest, Eqs, DisEqs).
separate_eqs_and_diseqs([DisEq|Rest], Eqs, [DisEq|DisEqs]) :-
    functor(DisEq, '$noteq$', 2),
    separate_eqs_and_diseqs(Rest, Eqs, DisEqs).


occurs_in(X, Y) :- var(Y), !, X == Y.
occurs_in(X, Y) :- functor(Y, _, N), occ_in_args(N, X, Y).

occ_in_args(N, X, Y) :- N > 0, arg(N, Y, Yn), occurs_in(X, Yn).
occ_in_args(N, X, Y) :- N > 0, N1 is N-1, occ_in_args(N1, X, Y).

% unwrap_eqs/5 "unwraps" an equation f(t1,...,tn) = f(u1,...,un) 
% to yield n equations ti = ui.

unwrap_eqs(I, X, Y, Eqs0, Eqs1) :-
    I > 0,
    !,
    arg(I, X, Xi),
    arg(I, Y, Yi),
    I1 is I-1,
    unwrap_eqs(I1, X, Y, ['='(Xi, Yi)|Eqs0], Eqs1).
unwrap_eqs(0, _, _, Eqs, Eqs).
