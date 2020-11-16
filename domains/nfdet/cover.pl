:- module(cover, [
    covers_check/5,
    % For det domain.
    ta_term_minset_empty_intersec/2,
    is_top_ta_term/1
], [assertions, isomodes]).

% Local module shared by PLAI-based and NFGRAPH-based analyses
:- doc(title, "Cover check").
:- doc(author, "Pedro L@'{o}pez").

:- use_module(library(messages), [debug_message/2]).

:- use_module(library(lists), [append/3]).

:- use_module(typeslib(typeslib), [
    finite_unfold/2,
    not_expandible_type/1,
    find_type_functor/5,
    is_infinite_type/1,
    top_type/1]).
:- use_module(domain(nfdet/nfbool), [
    bool_normalize/2, wff2list/2]).
:- use_module(domain(nfdet/subproblems), [
    create_subproblems/3, equivalent_tuples/2]).
:- use_module(domain(nfdet/nfsets), [
    add_item_to_typassign/4,
    change_type_in_typassgn/4,
    generate_type_annotated_term/4,
    included/2,
    included_ta_term_in_tuple/2,
    remove_item_from_typAss/3,
    simplify_conjunctions/2,
    ta_term_basicset_intersec/3,
    find_type/3,
    ta_term_empty/1,
    translate_to_bool_format/2,
    closed_var_list/2]).

:- use_module(library(iso_misc), [unify_with_occurs_check/2]).

%-----------------------------------------------------------------------

%% covers_check(Type, Test, Res):-
%%   covers_check(Type, false, Masc, Test, Res):-
%% 
%%    debug_message("Generating type annotated term ~q - ~q - ~q ...", [Type, UseMasc, Masc]), 
%%    generate_type_annotated_term(Type, UseMasc, Masc, Ta_term),
%%    debug_message("done = ~q", [Ta_term]), 
%%    (Ta_term == ([],[]) -> Res = true % there are no input arguments
%%         ; 
%%         (herbrand_covered(Test, Ta_term) -> 
%%              create_subproblems(Test, Ta_term, Res)
%%              ; Res = fail
%%         )
%%    ).


% MOVED FROM cover.pl (nf.pl)

covers_check(_Type, _UseMasc, _Masc, Test, true) :-
    Test == true,
    !.
covers_check(_Type, _UseMasc, _Masc, Test, fail) :-
    Test == false,
    !.
covers_check(Type, UseMasc, Masc, Test, Res) :-
    debug_message("Generating type annotated term ~q - ~q - ~q ...", [Type,
            UseMasc, Masc]),
    generate_type_annotated_term(Type, UseMasc, Masc, Ta_term),
    debug_message("done = ~q", [Ta_term]),
    ( Ta_term == ([], []) -> Res = true % there are no input arguments
    ;
        ( herbrand_covered(Test, Ta_term) ->
            create_subproblems(Test, Ta_term, Res)
        ; Res = fail
        )
    ).

% END OF MOVED FROM cover.pl 

herbrand_covered(Test, _Ta_term) :-
% debug_message("test_equivalent_to_true( ~q ) ...", [Test]),
    test_equivalent_to_true(Test), !.
% debug_message("done", []).
herbrand_covered(Test, Ta_term) :-
% debug_message("is_top_ta_term ...", []),
    is_top_ta_term(Ta_term),
    there_are_only_unification_tests(Test),
%debug_message("done", []), 
    !,
    fail.
herbrand_covered(Test, Ta_term) :-
% debug_message("translate_to_bool_format ...", []),
    translate_to_bool_format(Test, BTest),
% debug_message("bool_normalize ...", []),
    bool_normalize(not(BTest), NBTest),
% debug_message("wff2list ...", []),
    wff2list(NBTest, TestList),
% debug_message("simplify_conjunctions ...", []),
    simplify_conjunctions(TestList, STestList),
% debug_message("Performing d_empty check for: ~q - ~q ...", [STestList, Ta_term]),
    d_empty(STestList, Ta_term).
%debug_message("done", []).

test_equivalent_to_true([test(Minset, _Others)|TestList]) :-
    ( true_minset(Minset) -> true
    ; test_equivalent_to_true(TestList)
    ).

true_minset(minset(Tuple, Cobsets)) :-
    Cobsets == [],
    create_true_tuple(Tuple, NTuple),
    equivalent_tuples(Tuple, NTuple).

is_top_ta_term((Tuple, TypAss)) :-
    create_true_tuple(Tuple, NTuple),
    equivalent_tuples(Tuple, NTuple),
    all_types_are_top(TypAss).

all_types_are_top([]).
all_types_are_top([_Var:Type|Rest]) :-
    top_type(Type),
    all_types_are_top(Rest).

create_true_tuple([], []).
create_true_tuple([_|Tuple], [_|NTuple]) :-
    create_true_tuple(Tuple, NTuple).

there_are_only_unification_tests([]).
there_are_only_unification_tests([test(minset(_Tuple, []), _Others)|TestList]) :-
    there_are_only_unification_tests(TestList).

d_empty([], _) :- !.
d_empty([Minset|MList], Ta_term) :-
    ta_term_minset_empty_intersec(Ta_term, Minset),
    d_empty(MList, Ta_term).

%% ta_term_minset_empty_intersec(+Reg_Set, +Minset):
%%  Arguments:
%%   Reg_Set: a regular set.
%%   Minset: a minset.
%%  Purpose: Succeeds if the intersection of Reg_Set and Minset is empty.
%%  Note: implements the function empty(M, S) of the paper.

ta_term_minset_empty_intersec(Ta_Term, Minset) :-
    copy_term(Ta_Term, NTa_Term),
    copy_term(Minset, NMinset),
    NMinset = minset(Basic_Set, Basic_Set_List),
    ta_term_basicset_intersec(NTa_Term, Basic_Set, Ita_term),
    ( ta_term_empty(Ita_term) -> true
    ; select_non_disjoint(Basic_Set_List, Ita_term, NewBSList),
      empty1(NewBSList, Ita_term, [])
    ).

%% rs_disj_cob_conj_empty_intersec(+Ta_Term_List, +Cobasic_Set_List):
%%  Arguments:
%%   Ta_Term_List: a union of regular sets (represented as a list of 
%%                 regular sets).
%%   Cobasic_Set_List: a conjunction of cobasic sets (represented as a list
%%        of cobasic sets, each cobasic set is also represented as a list).
%% Purpose: Succeeds if for each regular set Ta_term in Ta_Term_List, the 
%%  intersection of Ta_term and Cobasic_Set_List is empty. It fails otherwise,
%%  in particular, if Cobasic_Set_List is the empty list.


empty1([], Ta_term, AL) :- !, % the list of cobasic sets is empty.
    create_new_al(AL, Ta_term, NewAL),
    empty2(NewAL, Ta_term).
empty1([BS|BList], (Tuple, _TyAssign), _AL) :-
    test_included([BS|BList], Tuple), !.
empty1([BS|BList], Ta_term, AL) :-
    expand_ta_term(Ta_term, BS, Ta_T1, Rest), !,
    ( included_ta_term_in_tuple(Ta_T1, BS) ->
        all_empty1(Rest, BList, AL)
    ; %% Or NewAL? -> It depends on wether the intersection
      %% performed by create_new_al is or not complete.
      aliased_vars(Ta_T1, BS, Avars),
      ( test_alvars(Avars, Ta_T1) ->
          empty1(BList, Ta_term, AL)
      ; %% Or NewAL? -> It depends on wether the intersection
        %% performed by create_new_al is or not complete.
        empty1(BList, Ta_T1, [tri(Ta_T1, Avars, BS)|AL]),
        all_empty1(Rest, BList, AL)
      )
    ).

empty1([_BS|BList], Ta_term, AL) :-
    % This clause is tried when expand_ta_term(Ta_term, BS, Ta_T1, Rest) fails 
    empty1(BList, Ta_term, AL).

all_empty1([], _BList, _AL) :- !.
all_empty1([Ta_Term|Rest_Ta], BList, AL) :-
    empty1(BList, Ta_Term, AL),
    all_empty1(Rest_Ta, BList, AL).

%% test_included(+BsList,+Tuple)
%% BsList: a list of basic sets.
%% Tuple: a tuple of terms (i.e. a basic set).
%% Purpose: succeeds iff Tuple is "included" in some cobasic set in BsList.

test_included([BS|BSList], Tuple) :-
    ( included(Tuple, BS) -> true
    ; test_included(BSList, Tuple)
    ).

%% create_new_al(+AL, +Ta_term, -NewAL)
%%   AL: a list of triples of the form tri(Ta, Avars, BS), where Ta is a 
%%       type-annotated term, Avars a list of variables, and BS a basic set. 
%%   Ta_term: a type-annotated term.
%%   NewAL: simmilar to AL but with (possibly) less elements.
%% Note: for efficiency reasons we can use a relaxed version of 
%% ta_term_basicset_intersec that only performs the unification of
%% the tuples of terms.

create_new_al(AL, Ta_term, NewAL) :-
    create_new_al_0(AL, Ta_term, [], NewAL).

create_new_al_0([], _, InNewAl, InNewAl) :- !.
create_new_al_0([A|AL], Ta_Term, InNewAl, OuNewAL) :-
    A = tri((_Term, TypAss), Avars, BS),
    ta_term_basicset_intersec(Ta_Term, BS, Intersection),
    ( ta_term_empty(Intersection) ->
        create_new_al_0(AL, Ta_term, InNewAl, OuNewAL)
    ;
        ( test_infinite_vars(Avars, TypAss) ->
            create_new_al_0(AL, Ta_term, InNewAl, OuNewAL)
        ;
            create_new_al_0(AL, Ta_term, [A|InNewAl], OuNewAL)
        )
    ).

test_infinite_vars([Var|Avars], TypAss) :-
    find_type(TypAss, Var, Type),
    ( is_infinite_type(Type) -> true;
        test_infinite_vars(Avars, TypAss) ).

select_non_disjoint([], _, []) :- !.
select_non_disjoint([BS|BSList], Ta_Term, NewBSList) :-
    ta_term_basicset_intersec(Ta_Term, BS, Intersection),
    ( ta_term_empty(Intersection) ->
        % ta_term_empty/1 is defined in low_level.pl
        NewBSList = CL
    ; NewBSList = [BS|CL]
    ),
    select_non_disjoint(BSList, Ta_Term, CL).

%% aliased_vars(+Term, +Tuple, -AlVars)
%% Term: a tuple of terms.
%% Tuple: a tuple of terms.
%% AlVars: AlVars is the list of variables of Term which are aliased with 
%%         some other variable in the mgu of Term and Tuple.
%% Note:  will always succeed because the output of expansion.

aliased_vars(Ta_Term, Tuple, AlVars) :-
    Ta_Term = (Term, _TypAss),
    compute_mgu(Term, Tuple, Vars, Values),
    select_vars_only(Vars, Values, [], [], OVars, OVal),
    compute_alvars(OVars, OVal, OVars, OVal, [], AlVars).

compute_alvars([], [], _MVars, _MValues, AlVars, AlVars) :- !.
compute_alvars([Var|Vars], [Value|Values], MVars, MValues, IAlVars, OAlVars) :-
    alvars1(MVars, MValues, Var, Value, IAlVars, TAlVars),
    compute_alvars(Vars, Values, MVars, MValues, TAlVars, OAlVars).

%% compute_alvars([], [], AlVars, AlVars):-!.
%% compute_alvars([Var|Vars], [Value|Values], IAlVars, OAlVars):-
%%    (member_0(Var, IAlVars) -> 
%%      compute_alvars(Vars, Values, IAlVars, OAlVars);
%%      alvars1(Vars, Values, Var, Value, IAlVars, TAlVars),
%%      compute_alvars(Vars, Values, TAlVars, OAlVars)).

select_vars_only([], [], IVars, IVal, IVars, IVal) :- !.
select_vars_only([Var|Vars], [Value|Values], IVars, IVal, OVars, OVal) :-
    ( var(Value) ->
        select_vars_only(Vars, Values, [Var|IVars], [Value|IVal], OVars, OVal)
    ; select_vars_only(Vars, Values, IVars, IVal, OVars, OVal)
    ).

alvars1([], [], _Var, _Value, IAlVars, IAlVars) :- !.
alvars1([V|_Vars], [Val|_Values], Var,  Value,  IAlVars, [Var|IAlVars]) :-
    V \== Var, Value == Val, !.
alvars1([_V|Vars], [_Val|Values], Var, Value, IAlVars, OAlVars) :-
    alvars1(Vars, Values, Var, Value, IAlVars, OAlVars).

%% alvars1([], [], _Var, _Value, IAlVars, IAlVars):-!.
%% alvars1([V|_Vars], [Val|_Values], Var, Value, IAlVars, [Var, V|IAlVars]):-
%%         Value == Val, !. 
%%         %% add_variable_not_duplicates(V, IAlVars, TeAlVars).
%% alvars1([_V|Vars], [Val|Values], Var, Value, IAlVars, OAlVars):-
%%         Value \== Val, !,
%%         alvars1(Vars, Values, Var, Value, IAlVars, OAlVars).

test_alvars(Avars, (_Term, TypeAss)) :-
    test_alvars_0(Avars, TypeAss).

test_alvars_0([Var|Avars], TypeAss) :-
    find_type(TypeAss, Var, Type),
    ( not_expandible_type(Type) -> true
    ; test_alvars_0(Avars, TypeAss)
    ).

% compute_mgu(Tuple1, Tuple2, Vars, Values)
%   Tuple1 and Tuple2 are tuples of terms.
%   Compute the mgu of Tuple1 and Tuple2. 
%   Vars is a list containing the variables of Tuple1.
%   Values is a list containing the terms to which the variables in 
%   the list Vars are bounded, according to the mgu of Tuple1 and Tuple2.
%   The correspondence between variables in Vars and terms in Values 
%   is done following the order of these two lists.
%   Example: The mgu {X/f(a), Y/b, Z/V} is representes by the lists
%   [X, Y, Z] and [f(a), b, V].   

compute_mgu(Tuple1, Tuple2, Vars, Values) :-
    copy_term(Tuple1, NTuple1),
    copy_term(Tuple2, NTuple2),
    closed_var_list(Tuple1, Vars),
    closed_var_list(NTuple1, Values),
    unify_with_occurs_check(NTuple1, NTuple2).

%%%Begin 5 Nov 1996 

empty2([X|T], (Tuple, _TyAssign)) :-
    test_included_2([X|T], Tuple), !.
empty2([tri(Ta_T, Avars, Cob)|AL], Ta_Term) :-
    select_vars_2(Ta_Term, Cob, SelVars), !,
    finite_expand(SelVars, Ta_Term, Expansion),
    %% select_disjoint_terms(Expansion, Cob, Disjoint),
    %% all_empty_2(Disjoint, AL).   
    all_empty_2(Expansion, [tri(Ta_T, Avars, Cob)|AL]).
empty2([_|AL], Ta_Term) :- % If select_vars_2(Term, Cob, SelVars) fails,
    empty2(AL, Ta_Term). % this means that Cob and Term are disjoint.

all_empty_2([], _AL) :- !.
all_empty_2([Ta_Term|Disjoint], AL) :-
    % Replaced empty_2 by empty2 7-5-98 PLG
    % empty_2(AL, Ta_Term),
    empty2(AL, Ta_Term),
    all_empty_2(Disjoint, AL).

select_vars_2(Ta_Term, BS, AlVars) :-
    Ta_Term = (Term, _TyAssign),
    compute_mgu(Term, BS, Vars, Values),
    select_cross(Vars, Values, Vars, Values, [], AlVars).

select_cross([], [], _MVars, _MValues, AlVars, AlVars) :-
    !.
select_cross([Var|Vars], [Value|Values], MVars, MValues, IAlVars, OAlVars) :-
    select_1(MVars, MValues, Var, Value, IAlVars, TAlVars),
    select_cross(Vars, Values, MVars, MValues, TAlVars, OAlVars).

select_1(_, _, Var, Value, IAlVars, [Var|IAlVars]) :-
    nonvar(Value), !.
select_1([], [], _Var, _Value, IAlVars, IAlVars) :- !.
select_1([V|_Vars], [Val|_Values], Var, Value, IAlVars, [Var|IAlVars]) :-
    V \== Var, Value == Val, !.
select_1([_V|Vars], [_Val|Values], Var, Value, IAlVars, OAlVars) :-
    select_1(Vars, Values, Var, Value, IAlVars, OAlVars).

test_included_2([tri(_Ta_T, _Avars, Cob)|AL], Tuple) :-
    included(Tuple, Cob) -> true;
    test_included_2(AL, Tuple).

%%%End 5 Nov 1996 

%% % decide_expansion/5:
%% %   Succeeds if an expansion of the regular set is going to be performed.  
%% % Input Arguments:
%% %   Var_List: A list with the variables in the tuple of the regular set. 
%% %   Value_List: A list with the values to which the variables in Var_List
%% %               get bounded.
%% %   TypeAss: The type assignment of the regular set.
%% % Output Arguments:
%% %   Selected_Var: variable in Var_List selected to perform the expansion. 
%% %   Selected_Var_Type: Type of the variable in Var_List selected to perform 
%% %                      the expansion.
%%
%% decide_expansion(Var_List, Value_List, TypeAss, Selected_Var,
%%          Selected_Var_Type) :-
%%      nonvar(Var_List), nonvar(Value_List),
%%      Var_List = [Var|Rest_Var_List],
%%      Value_List = [Value|Rest_Value_List],
%%      ( (nonvar(Value) ; var(Rest_Var_List))
%%      -> Var = Selected_Var,
%%          find_type(TypeAss, Var, VarType),
%%          VarType = Selected_Var_Type
%%      ; decide_expansion(Rest_Var_List, Rest_Value_List,
%%              TypeAss, Selected_Var,
%%              Selected_Var_Type)
%%      ).

%% 4 Oct 1996

%------------------------------------------------------------------------%
% Get a type term from a term and a typing of its variables

replace_var_by_term(InTerm, ReplaceVar, ByTerm, ByTerm):-
    InTerm == ReplaceVar, !.
replace_var_by_term(InTerm, ReplaceVar, _ByTerm, InTerm):-
    var(InTerm), InTerm \== ReplaceVar, !.
replace_var_by_term(InTerm, ReplaceVar, ByTerm, OuTerm):-
    nonvar(InTerm), InTerm \== ReplaceVar, !,
    functor(InTerm, F, A),
    functor(OuTerm, F, A),
    arg_replace_var_by_term(A, InTerm, ReplaceVar, ByTerm, OuTerm).

arg_replace_var_by_term(0, _InTerm, _ReplaceVar, _ByTerm, _OuTerm):-!.
arg_replace_var_by_term(Arg_Num, InTerm, ReplaceVar, ByTerm, OuTerm):-
    Arg_Num > 0,
    NArg_Num is Arg_Num - 1,
    arg(Arg_Num, InTerm, InArg),
    arg(Arg_Num, OuTerm, OuArg),
    replace_var_by_term(InArg, ReplaceVar, ByTerm, OuArg),
    arg_replace_var_by_term(NArg_Num, InTerm, ReplaceVar, ByTerm, OuTerm).

% ===========================================================================
%! # Expansion of type annotated terms.

% Expansion of type annotated terms.

:- pred expand_ta_term(+Ta_Term, +BS, -NewTa_Term, -Rest_Ta)

# "Performs the expansion of the type-annotated term @var{Ta_Term}
      respect to @var{BS}, into the type-annotated term
      @var{NewTa_Term} and the list of type-annotated terms
      @var{Rest_Ta}. @var{BS} is syntactically a basic set, but
      represents the cobasic set comp(@var{BS}). @var{NewTa_Term} is
      an instance of @var{Ta_Term}.  The pair @var{NewTa_Term},
      @var{Rest_Ta} is a partition of @var{Ta_Term}. For any variable
      x in @var{NewTa_Term} it holds that its type is an infinite
      function symbol type, or theta(x) is a variable, where theta is
      the mgu of @var{BS} and the tuple of term of @var{Ta_Term}.
      This predicate can fail if @var{Ta_Term} and @var{BS} are
      disjoint (in that case expansion is not possible). The variables
      in @var{Ta_Term} and @var{BS} are not instantiated. This
      predicate corresponds to the function expansion(R, Cob) of the
      paper.".

expand_ta_term(Ta_Term, BS, Ta_T1, Rest_ta) :-
%% type_rule_simplify, %% -PL warning!
    expand_ta_term_0(Ta_Term, BS, Ta_T1, Rest_ta).
% selec_type_rule_simplify, !. %% -PL warning!
% I think is not neccesary because rules are yet simplified.

expand_ta_term_0(Ta_Term, BS, Ta_T1, Rest_ta) :-
    Ta_Term = (Term, _TypeAss),
    copy_term(Term, New_Term),
    copy_term(BS,   New_BS),
    closed_var_list(Term,     Var_List),
    closed_var_list(New_Term, New_Var_List),
    unify_with_occurs_check(New_Term, New_BS),
    ta_expand1(Var_List, New_Var_List, Ta_Term, [], Ta_T1, Rest_ta).

ta_expand1([], [], ITa_Term, InTaList, ITa_Term, InTaList) :-
    !.
ta_expand1([_Var|VList], [Term|TList], ITa_Term, InTaList, OTa_Term, OuTaList) :-
    var(Term),
    !,
    ta_expand1(VList, TList, ITa_Term, InTaList, OTa_Term, OuTaList).
ta_expand1([Var|VList], [Term|TList], ITa_Term, InTaList, OTa_Term, OuTaList) :-
    nonvar(Term),
    ITa_Term = (ITerm, ITypeAss),
    find_type(ITypeAss, Var, Type),
    functor(Term, F, A),
    find_type_functor(F/A, Type, [], Type1, Types2),
% Types2 is a list of types.
    ( Types2 == [] ->
        NewInTaList = InTaList
    ; change_type_in_typassgn(Types2, Var, ITypeAss, TypAss2),
      NewInTaList = [(ITerm, TypAss2)|InTaList]
    ),
    functor(NTerm, F, A),
    remove_item_from_typAss(ITypeAss, Var, ITypAss3),
    actualize_var_term_typass(A, NTerm, Term, Type1,
        VList, TList, ITypAss3,
        OuVList, OuTList, OuTypAss3),
    replace_var_by_term(ITerm, Var, NTerm, Term3),
    ta_expand1(OuVList, OuTList, (Term3, OuTypAss3), NewInTaList,
        OTa_Term, OuTaList).

% not_enpandible_var(Term, Type) :-
%       not_expandible_type(Type) ; var(Term).

:- pred actualize_var_term_typass(+A, +NTerm, +Term, +Type,
        +IVarList, +ITermList, +InTypAss,
        -OVarList, -OTermList, -OuTypAss)

# "Expands the type annotated term 

Ta_T1 and Rest_ta are a partition of Ta_term

@var{Type} is the (compound) type with the same main functor than
@var{Term} (and @var{NTerm}).  @var{NTerm} has the same main functor
than @var{Term}, but its arguments are all variables.  @var{IVarList}
is the list of variables appearing in the tuple of terms (also basic
set) of a type annotated term, and @var{ITermList} is the list of
terms to which variables in @var{IVarList} are bounded to (in
correspondence order). That is, the pair @var{IVarList} and
@var{ITermList} represent a substitution.  @var{InTypAss} is a type
assignment that stores the type of each variable in
@var{IVarList}. The variables in @var{InTypAss} are exactly those
variables in @var{IVarList}. The same explained relation between
@var{IVarList}, @var{ITermList} and @var{InTypAss} holds for
@var{OVarList}, @var{OTermList}, @var{OuTypAss}.".


actualize_var_term_typass(0, _NTerm, _Term, _Type,
        IVarList, ITermList, InTypAss,
        IVarList, ITermList, InTypAss) :- !.
actualize_var_term_typass(A, NTerm,  Term,  Type,
        IVarList, ITermList, InTypAss,
        OVarList, OTermList, OuTypAss) :-
    A > 0, NA is A - 1,
    arg(A, NTerm, NTeArg), % NTeArg is a variable.
    arg(A, Term,  TeArg),
    arg(A, Type,  TyArg),
    add_item_to_typassign(InTypAss, NTeArg, TyArg, NewInTypAss),
    NewIVarList = [NTeArg|IVarList],
    NewITermList = [TeArg|ITermList],
    actualize_var_term_typass(NA, NTerm, Term, Type,
        NewIVarList, NewITermList, NewInTypAss,
        OVarList, OTermList, OuTypAss).


%% Expansion of finite types.

finite_expand(Vars, Ta_Term, Expan) :-
    Ta_Term = (Term, TypAss),
    expand_2(Vars, TypAss, [Term], Expan).

expand_2([], TyAssign, IExpan, OExpan) :- !,
    put_type_assignments(IExpan, TyAssign, [], OExpan).
expand_2([Var|SelVars], TyAssign, IExpan, OExpan) :-
    find_type(TyAssign, Var, Type),
    finite_unfold(Type, Terms),
    create_ta_terms(Terms, Var, IExpan, TExpan),
    remove_item_from_typAss(TyAssign, Var, NTyAssign),
    expand_2(SelVars, NTyAssign, TExpan, OExpan).

create_ta_terms([], _Var, Expan, Expan) :- !.
create_ta_terms([Term|L], Var, IExpan, OExpan) :-
    all_replace_var_by_term(IExpan, Var, Term, [], TExpan),
    create_ta_terms(L, Var, TExpan, OExpan).

all_replace_var_by_term([], _Var, _Term, Expan, Expan) :- !.
all_replace_var_by_term([Term1|ExpanL], Var, Term, IExpan, OExpan) :-
    replace_var_by_term(Term1, Var, Term, NTerm),
    all_replace_var_by_term(ExpanL, Var, Term, [NTerm|IExpan], OExpan).

put_type_assignments([], _TyAssign, Expan, Expan) :- !.
put_type_assignments([Term|L], TyAssign, IExpan, OExpan) :-
    put_type_assignments(L, TyAssign, [(Term, TyAssign)|IExpan], OExpan).
