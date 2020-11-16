:- module(mutexcheck, [
    mutual_exclusion_check/5 % TODO: depends on CLP(R) solver
], [assertions]).

:- doc(title, "Mutual exclusion check").
:- doc(author, "Pedro L@'{o}pez").

% Used as solver for numeric tests
% TODO: Make it optional, see subproblems.pl
% TODO: Use CLP(Q) instead? (via poly_clpq?)
% TODO: Use other numeric solvers if available? (e.g. PPL)
:- use_package(clpr).

:- use_module(engine(hiord_rt), [call/1]).

:- use_module(library(messages), [debug_message/2]).

:- use_module(library(lists), [append/3]).
:- use_module(domain(nfdet/nfsets), [generate_type_annotated_term/4]).

:- use_module(domain(nfdet/cover), [
    ta_term_minset_empty_intersec/2,
    is_top_ta_term/1]).

% TODO: duplicated from nftests (to break dependency with nfgraph-based analysis)
test_is_true(Test) :- Test == true.
test_is_false(Test) :- Test == false ; Test == fail.
% set_test_true(Test) :- Test = true.
set_test_false(Test) :- Test = false.

:- use_module(domain(nfdet/subproblems), [integer_covers/2]).

:- use_module(library(iso_misc), [unify_with_occurs_check/2]).

mutual_exclusion_check(_Type, _UseMasc, _Masc, Test, true):- 
    Test = [_], 
    !.
mutual_exclusion_check(_Type, _UseMasc, _Masc, Test, fail):-
    %% debug_message("Test = ~q", [Test]),
    Test == true, 
    % There are more than one clauses, an the test of at least one of them is true. 
    !. %-> see
mutual_exclusion_check(_Type, _UseMasc, _Masc, Test, true):- 
    Test == false, 
    % There are one or more than one clauses, and the test of at least one of them is false.  
    !. %-> see
%% mutual_exclusion_check(_Type, _UseMasc, _Masc, Test, true):- 
%%    Test == [true], 
%%    % There is only one or more than one clauses, and the test of at least one of them is false.  
%%    !.
mutual_exclusion_check(Type, UseMasc, Masc, Test, Res):- 
    generate_type_annotated_term(Type, UseMasc, Masc, Ta_term),
    %% debug_message("Ta_term = ~q", [Ta_term]), 
    %% debug_message("Test = ~q", [Test]), 
    disjoint_check(Ta_term, Test, Res).
    %% debug_message("Res = ~q", [Res]).

% Delete test equivalent to false (once the intersection of the clause
% test and the type are been done).

%% disjoint_check(Ta_term, Test, Res):-
%%    Ta_term == ([],[]), 
%%    !, 
%%    Test = test(_Minset,others(_Arit, Meta)),
%%    solve_meta_tests(Meta, Res).
%% disjoint_check(Ta_term, _Test, Res):-
%%    Ta_term == ([],[]), 
%%    !, 
%%    Res = fail. % there are no input arguments %-> see

%% Commented out by PLG 3 Aug 99 (ICLP99 demo). 
%% disjoint_check(_Ta_term, Test, Res):-
%%    debug_message("CALL: ~q", [test_equivalent_to_true(Test)]),
%%    test_equivalent_to_true(Test),
%%    debug_message("EXIT: ~q", [test_equivalent_to_true(Test)]), 
%%    !, 
%%    Res = fail.
%% End of commented out by PLG 3 Aug 99 (ICLP99 demo). 
disjoint_check(Ta_term, Test, Res):-
    is_top_ta_term(Ta_term), 
    !,
    %% debug_message("CALL: ~q", [disjoint_check_1(Test, is_any, Ta_term, Res)]),
    disjoint_check_1(Test, is_any, Ta_term, Res).
    %% debug_message("EXIT: ~q", [disjoint_check_1(Test, is_any, Ta_term, Res)]).
disjoint_check(Ta_term, Test, Res):-
    %% debug_message("CALL: ~q", [disjoint_check_1(Test, no_any, Ta_term, Res)]),
    disjoint_check_1(Test, no_any, Ta_term, Res).
    %% debug_message("EXIT: ~q", [disjoint_check_1(Test, no_any, Ta_term, Res)]).

% Assumed that Test is not the empty list in the first call.
disjoint_check_1([], _AnyFlag, _Ta_term, Res):-
    !,
    Res = true.
disjoint_check_1(Test, AnyFlag, Ta_term, Res):-
    Test = [FirsTest|ResTests],
    disjoint_check_2(ResTests, FirsTest, AnyFlag, Ta_term, Res1),
    ( Res1 == true ->
        disjoint_check_1(ResTests, AnyFlag, Ta_term, Res)
    ; Res = fail
    ).

disjoint_check_2([], _Test, _AnyFlag, _Ta_term, Res):-
    !,
    Res = true.
disjoint_check_2([Test1|Testlist], Test, AnyFlag, Ta_term, Res):-
    %% debug_message("CALL: ~q", [tests_are_disjoint(Test1, Test, AnyFlag, Ta_term, Res1)]),
    tests_are_disjoint(Test1, Test, AnyFlag, Ta_term, Res1),
    %% debug_message("EXIT: ~q", [tests_are_disjoint(Test1, Test, AnyFlag, Ta_term, Res1)]),
    ( Res1 == true ->
        disjoint_check_2(Testlist, Test, AnyFlag, Ta_term, Res)
    ; Res = fail
    ).

tests_are_disjoint(Test1, Test, AnyFlag, Ta_term, Res):-
    test_intersection(Test1, Test, TestInter),
    debug_message("CALL: ~q", [disjoint_intersection(TestInter, AnyFlag, Ta_term, Res)]),
    disjoint_intersection(TestInter, AnyFlag, Ta_term, Res),
    debug_message("EXIT: ~q", [disjoint_intersection(TestInter, AnyFlag, Ta_term, Res)]).

disjoint_intersection(TestInter, _AnyFlag, _Ta_term, Res):-
    test_is_empty(TestInter), 
    !,
    Res = true.
disjoint_intersection(test(Minset, Others), AnyFlag, Ta_term, Res):-
    AnyFlag == no_any,
    !,
    ( ta_term_minset_empty_intersec(Ta_term, Minset) ->
        Res = true
    ; debug_message("CALL: ~q", [solve_other_tests(Others, Res)]),
      solve_other_tests(Others, Res),
      debug_message("EXIT: ~q", [solve_other_tests(Others, Res)])
    ).
disjoint_intersection(test(_Minset, Others), _AnyFlag, _Ta_term, Res):-
    !,
    solve_other_tests(Others, Res).
disjoint_intersection(_TestInter, _AnyFlag, _Ta_term, Res):-
    Res = fail.

test_intersection(Test1, Test, TestInter):-
    copy_term(Test1, C_Test1),
    copy_term(Test, C_Test),
    C_Test1 = test(minset(BasicSet1, CoBasicSets1), Others1),
    C_Test  = test(minset(BasicSet,  CoBasicSets ), Others), 
    ( unify_with_occurs_check(BasicSet1, BasicSet) -> 
        append(CoBasicSets, CoBasicSets1, CoBasicInter1),
        simplify_cobasic_sets(CoBasicInter1, BasicSet, CoBasicInter),
        debug_message("CALL ~q", [append(Others, Others1, OthersInt)]), 
        other_tests_conjuncton(Others, Others1, OthersInt),
        debug_message("EXIT ~q", [append(Others, Others1, OthersInt)]), 
        TestInter = test(minset(BasicSet, CoBasicInter), OthersInt),
        debug_message("EXIT ~q", [TestInter = test(minset(BasicSet, CoBasicInter), OthersInt)])  
    ; TestInter = false
    ).


other_tests_conjuncton(Others, Others1, Conj):-
    test_is_true(Others),
    !, 
    Conj = Others1.
other_tests_conjuncton(Others, Others1, Conj):-
    test_is_true(Others1),
    !, 
    Conj = Others.
other_tests_conjuncton(Others, _Others1, Conj):-
    test_is_false(Others),
    !, 
    set_test_false(Conj).
other_tests_conjuncton(_Others, Others1, Conj):-
    test_is_false(Others1),
    !, 
    set_test_false(Conj).
other_tests_conjuncton(Others, Others1, Conj):-
    Others = others(Arith, Meta), 
    Others1 = others(Arith1, Meta1), 
    append(Arith, Arith1, ArithConj),
    append(Meta, Meta1, MetaConj),
    Conj = others(ArithConj, MetaConj).

simplify_cobasic_sets([], _Bas, []).
simplify_cobasic_sets([Cob|CobList], Bas, OutCoBasicList):-
    copy_term(Cob, NCob),
    copy_term(Bas, NBas), 
    ( unify_with_occurs_check(NCob, NBas) ->
        OutCoBasicList = [NBas|CoBasicList]
    ; OutCoBasicList = CoBasicList
    ),
    simplify_cobasic_sets(CobList, Bas, CoBasicList).

 
test_is_empty(TestInter):- TestInter == false.

% MOVED FROM subproblems.pl 

solve_other_tests(true, fail):- !.
solve_other_tests([true], fail):- !.
solve_other_tests([], fail):- !.
solve_other_tests(false, true):- !.
solve_other_tests(fail, true):- !.
solve_other_tests([false], true):- !.
solve_other_tests([fail], true):- !.
solve_other_tests(others(Arith_Tests, Meta_Tests), Res):-
    solve_arithmetic_tests(Arith_Tests, ARes),
    ( ARes == true -> 
        Res = true  
    ; solve_meta_tests(Meta_Tests, Res)
    ).

solve_arithmetic_tests(true, fail):- !.
solve_arithmetic_tests([true], fail):- !.
solve_arithmetic_tests([], fail):- !.
solve_arithmetic_tests(false, true):- !.
solve_arithmetic_tests(fail, true):- !.
solve_arithmetic_tests([false], true):- !.
solve_arithmetic_tests([fail], true):- !.
solve_arithmetic_tests(Arith_Tests, Res):- 
    numeric_covers(num, Arith_Tests, Res).

solve_meta_tests(true, fail):- !.
solve_meta_tests([true], fail):- !.
solve_meta_tests([], fail):- !.
solve_meta_tests(false, true):- !.
solve_meta_tests(fail, true):- !.
solve_meta_tests([false], true):- !.
solve_meta_tests([fail], true):- !.
solve_meta_tests(Meta_Tests, Res):-
    sanitize_tests(Meta_Tests,NTests), % TODO:[new-resources] this should be done in other way (e.g., with builtin tables)
    test_list_to_goal(NTests, Goal),
    ( \+ call(Goal) -> % TODO:[new-resources] meta-interpreted (should it be merged with peval or spec code?)
        Res = true
    ; Res = false
    ).

test_list_to_goal([Test], Test):-
    !. 
test_list_to_goal([Test|Others], ','(Test, Goal)):-
    test_list_to_goal(Others, Goal).

%sanitize_tests(E,E).
sanitize_tests([],[]).
sanitize_tests([TestName|R],[NTestName|T]):-
    take_off_module_name(TestName,NTestName),
    sanitize_tests(R,T).

:- use_module(engine(runtime_control), [module_split/3]).

take_off_module_name(T,N):-
    T =.. [F|Args],
    module_split(F,_,NF),!,
    N =.. [NF|Args].
take_off_module_name(T,T).

%% solve_other_tests(true, fail):- !.
%% solve_other_tests([true], fail):- !.
%% solve_other_tests([], fail):- !.
%% solve_other_tests(false, true):- !.
%% solve_other_tests(fail, true):- !.
%% solve_other_tests([false], true):- !.
%% solve_other_tests([fail], true):- !.
%% solve_other_tests([Other|Rest], Res):-
%%    numeric_covers(num, [Other|Rest], Res).

% TODO: see similar code in subproblems.pl
numeric_covers(num, Other, Res):-
    !,
    num_covers(Other, Res). 
numeric_covers(int, Other, Res):-
    integer_covers(Other, Res).


% Replaced clpr_call/1 by clpr_meta/1 -JFMC
% (Previously: added call to ciao clpr 16-Dec-2002 -PLG)
num_covers(Tests, Res):- 
    copy_term(Tests, NewTests),
    conj2formula_det(NewTests, CIAOTest),
    ( clpr_meta(CIAOTest) -> Res = fail ; Res = true ).

conj2formula_det([Test], CLPRTest):-
    translate_test_to_ciao_clpr(Test, CLPRTest),
    !. 
conj2formula_det([Test|Others], ','(CLPRTest, FOthers)):-
    translate_test_to_ciao_clpr(Test, CLPRTest),
    conj2formula_det(Others, FOthers).

% TODO: generalize to use an abstract domain, e.g., polyhedra -- see poly_clpq bundle (JF)
translate_test_to_ciao_clpr(=(X, Y),         '.=.'(X, Y)):-!.
translate_test_to_ciao_clpr('$noteq$'(X, Y), '.<>.'(X, Y)):-!.
translate_test_to_ciao_clpr(==(X, Y),        '.=.'(X, Y)):-!.
translate_test_to_ciao_clpr(\==(X, Y),       '.<>.'(X, Y)):-!.
translate_test_to_ciao_clpr(is(X, Y),        '.=.'(X, Y)):-!.
translate_test_to_ciao_clpr(=\=(X, Y),       '.<>.'(X, Y)):-!.
translate_test_to_ciao_clpr(=:=(X, Y),       '.=.'(X, Y)):-!.
translate_test_to_ciao_clpr(<(X, Y),         '.<.'(X, Y)):-!.
translate_test_to_ciao_clpr(>(X, Y),         '.>.'(X, Y)):-!.
translate_test_to_ciao_clpr(=<(X, Y),        '.=<.'(X, Y)):-!.
translate_test_to_ciao_clpr(>=(X, Y),        '.>=.'(X, Y)):-!.

% End added call to ciao clpr 16-Dec-2002 -PLG
