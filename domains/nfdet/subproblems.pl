:- module(subproblems, [
    create_subproblems/3, % TODO: depends on CLP(R) solver
    equivalent_tuples/2,
    % For det domain.
    integer_covers/2 % TODO: depends on 'omega' external tool
], [assertions]).

% Local module required by PLAI-based and NFGRAPH-based analyses
:- doc(title, "Solver for cover and mutexcheck").
:- doc(author, "Pedro L@'{o}pez").

% Used as solver for numeric tests
% TODO: Make it optional, see mutexcheck.pl
% TODO: Use CLP(Q) instead? (via poly_clpq?)
% TODO: Use other numeric solvers if available? (e.g. PPL)
:- use_package(clpr).

:- use_module(domain(nfdet/nfbool), [push_conj/2]).
:- use_module(typeslib(typeslib), [
    equivalent_to_numeric/1]).
:- use_module(domain(nfdet/nfsets), [
    included/2,
    ta_term_basicset_intersec/3,
    ta_term_empty/1,
    find_type/3,
    closed_var_list/2]).
         
:- use_module(library(iso_misc), [unify_with_occurs_check/2]).

:- use_module(library(messages), [debug_message/2]).

%-----------------------------------------------------------------------

% Taken out (PBC,Apr,23,98)
%% :- use_module(library(charsio)).

%%Begin Nov 4 1996.
%% differentiate between cobasic and basics.

create_subproblems(TestList, Ta_Term, Res) :-
    colect_tuples_of_terms(TestList, [], [], Tuples, CobTuples),
    subproblems(CobTuples, TestList, Ta_Term, cobasic, Res1),
    ( Res1 == true ->
        subproblems(Tuples, TestList, Ta_Term, basic, Res)
    ; Res = fail
    ).

colect_tuples_of_terms([], Tuples, CobTuples, Tuples, CobTuples).
colect_tuples_of_terms([Minset|MinSetList], InTuples, InCobTuples, OutTuples, OutCobTuples) :-
    Minset = test(minset(Tuple, CobSetList), _Other),
    insert_tuples_no_duplicates(Tuple, InTuples, TemTuples),
    colect_cobasic_tuples(CobSetList, InCobTuples, TemCobTuples),
    colect_tuples_of_terms(MinSetList, TemTuples, TemCobTuples, OutTuples, OutCobTuples).

colect_cobasic_tuples([], CobTuples, CobTuples) :- !.
colect_cobasic_tuples([CobSet|CobSetList], InCobTuples, OuCobTuples) :-
    insert_tuples_no_duplicates(CobSet, InCobTuples, TemCobTuples),
    colect_cobasic_tuples(CobSetList, TemCobTuples, OuCobTuples).

insert_tuples_no_duplicates(Tuple, InTuples, OutTuples) :-
    ( tuple_member(Tuple, InTuples) ->
        OutTuples = InTuples
    ; OutTuples = [Tuple|InTuples]
    ).

tuple_member(X, [Y|_]) :- equivalent_tuples(X, Y), !.
tuple_member(X, [_|L]) :- tuple_member(X, L).

%% See builtin.
equivalent_tuples(X, Y) :- included(X, Y), included(Y, X).


subproblems([], _TestList, _Ta_Term, _Flag, true) :- !.
subproblems([Tuple|List], TestList, Ta_Term, Flag, Res) :-
    solve_subproblem_basic(Tuple, TestList, Ta_Term, Flag, Res1),
% format("~n Tuple: ~q ~n TestList: ~q ~n Ta_Term: ~q ~n Flag: ~q ~n", 
%       [Tuple, TestList, Ta_Term, Flag]),
    ( Res1 == true ->
        subproblems(List, TestList, Ta_Term, Flag, Res)
    ; Res = fail
    ).

%% solve_subproblem_basic(+Tuple, +TestList, +Ta_Term, +Flag)
%% Purpose: creates and solve a subproblem corresponding to Tuple. 
%% Tuple: a tuple of terms, for which a subproblem is created and solved.  
%% Flag: takes the values basic or cobasic, and indicates whether Tuple
%%       is a basic or cobasic set.
%% TestList: the input test of the predicate. Is a list of tests, each of
%%         them corresponding to a clause 
%% Ta_Term: a type annotated term. We already know that TestList covers
%%         Ta_Term (which was the initial problem).

solve_subproblem_basic(Tuple, TestList, Ta_Term, Flag, Res) :-
    ta_term_basicset_intersec(Ta_Term, Tuple, Intersection), !,
    ( ta_term_empty(Intersection) ->
        Res = true
    ; colect_other_tests(TestList, Intersection, Flag, [], Other),
      solve_other_tests(Other, Res)
    ).

%% colect_other_tests(+TestList, +Ta_Term, +Flag, +InOther, -OutOther)
%% If OutOther is [] then there is no test Test in TestList such that
%% Ta_Term is included in Test, in this case, we say the type is not
%% covered.

colect_other_tests([], _Ta_Term, _Flag, InOther, InOther) :- !.
colect_other_tests([Test|TestList], Ta_Term, Flag, InOther, OutOther) :-
    Test = test(minset(MTuple, CobSetList), RTest),
    Ta_Term = (Term, _TypAss),
    ( tuple_included(Flag, Term, minset(MTuple, CobSetList)) ->
        ( RTest == true ->
            OutOther = true
        ; ( select_test(Ta_Term, MTuple, RTest, OuTest) ->
              colect_other_tests(TestList, Ta_Term, Flag, [OuTest|InOther], OutOther)
          ; colect_other_tests(TestList, Ta_Term, Flag, InOther, OutOther)
          )
        )
    ; colect_other_tests(TestList, Ta_Term, Flag, InOther, OutOther)
    ).

tuple_included(cobasic, Term, minset(MTuple, CobSetList)) :- !,
    included(Term, MTuple),
    all_disjoint(CobSetList, Term).
tuple_included(basic, Term, minset(MTuple, _CobSetList)) :-
    included(Term, MTuple).

all_disjoint([], _Term) :- !.
all_disjoint([Cob|L], Term) :-
    tuple_disjoint(Cob, Term),
    all_disjoint(L, Term).

tuple_disjoint(Cob, Term) :-
    \+ unify_with_occurs_check(Cob, Term).

%                 ta_term_intersection((MTuple, TypAss1), Ta_Term, Intersec),
%                 (ta_term_empty(Intersec) 

select_test(Ta_Term, Tuple, InTest, OuTest) :-
    copy_term(Ta_Term, NTa_Term),
    copy_term((Tuple, InTest), (NTuple, NInTest)),
    NTa_Term = (NTerm, NTypAss),
    Ta_Term = (Term, _TypAss),
    closed_var_list(Term, TermVars),
    closed_var_list(NTerm, NTermVars),
    unify_with_occurs_check(NTerm, NTuple),
    check_integer_types(NInTest, TermVars, NTermVars, NTypAss, OuTest).

check_integer_types([], _TermVars, _NTermVars, _NTypAss, []) :- !.
check_integer_types([NInTest|List], TermVars, NTermVars, NTypAss,
        OuTests) :-
    check_integer_type(NInTest, TermVars, NTermVars, NTypAss, OuTest),
    ( OuTest == true -> OuTests = true
    ; OuTests = [OuTest|OuList],
      check_integer_types(List, TermVars, NTermVars, NTypAss, OuList)
    ).

check_integer_type(true, _TermVars, _NTermVars, _NTypAss, true) :- !.
check_integer_type(InTest, TermVars, NTermVars, NTypAss, OuTest) :-
    binary_arithmetic_test(InTest), !,
    InTest =.. [F, Arg1, Arg2],
    have_numeric_type(Arg1, TermVars, NTermVars, NTypAss, TArg1),
    have_numeric_type(Arg2, TermVars, NTermVars, NTypAss, TArg2),
    OuTest =.. [F, TArg1, TArg2].
check_integer_type(InTest, TermVars, NTermVars, NTypAss, true) :-
    unary_arithmetic_test(InTest), !,
    arg(1, InTest, Arg1),
    have_numeric_type(Arg1, TermVars, NTermVars, NTypAss, _TArg1).
check_integer_type((\+(InTest)), TermVars, NTermVars, NTypAss, true) :-
    unary_arithmetic_test(InTest), !,
    arg(1, InTest, Arg1),
    \+ have_numeric_type(Arg1, TermVars, NTermVars, NTypAss, _TArg1).
check_integer_type(InTest, TermVars, NTermVars, NTypAss, OuTest) :-
    functor(InTest, is, 2),
    arg(1, InTest, Arg1),
    arg(2, InTest, Arg2),
    have_numeric_type(Arg1, TermVars, NTermVars, NTypAss, TArg1),
    is_a_numeric_expression(Arg2, TermVars, NTermVars, NTypAss, TArg2),
    OuTest =.. [is, TArg1, TArg2].

%rnum
%% is_a_numeric_expression(Arg, _TermVars, _NTermVars, _NTypAss, Arg):-
%%     integer(Arg), !.
is_a_numeric_expression(Arg, _TermVars, _NTermVars, _NTypAss, Arg) :-
    number(Arg), !.
is_a_numeric_expression(Arg1, TermVars, NTermVars, NTypAss, TArg1) :-
    var(Arg1), !, find_type(NTypAss, Arg1, OutType),
    equivalent_to_numeric(OutType),
%rnum equivalent_to_integer(OutType),
    translate_to_common_vars(TermVars, NTermVars, Arg1, TArg1).
is_a_numeric_expression(Arg, TermVars, NTermVars, NTypAss, TArg) :-
    numeric_operator(Arg),
    Arg =.. [F|List],
    are_numeric_expressions(List, TermVars, NTermVars, NTypAss, TList),
    TArg =.. [F|TList].

%% Commented by PLG 24-Abril-98
%% is_a_numeric_expression(Arg, TermVars, NTermVars, NTypAss, TArg):-
%%     unary_numeric_operator(Arg), 
%%     Arg =.. [F, Arg1],
%%     is_a_numeric_expression(Arg1, TermVars, NTermVars, NTypAss, TArg1),
%%     TArg =.. [F, TArg1].


are_numeric_expressions([Arg1|Rest], TermVars, NTermVars, NTypAss,
        [TArg1|TRest]) :-
    is_a_numeric_expression(Arg1, TermVars, NTermVars, NTypAss, TArg1),
    are_numeric_expressions(Rest, TermVars, NTermVars, NTypAss, TRest).



%rnum
%% have_numeric_type(Arg, _TermVars, _NTermVars, _NTypAss, Arg):-
%%     integer(Arg), !.
have_numeric_type(Arg, _TermVars, _NTermVars, _NTypAss, Arg) :-
    number(Arg), !.
have_numeric_type(Arg1, TermVars, NTermVars, NTypAss, TArg1) :-
    var(Arg1), !, find_type(NTypAss, Arg1, OutType),
    equivalent_to_numeric(OutType),
%rnum equivalent_to_integer(OutType),
    translate_to_common_vars(TermVars, NTermVars, Arg1, TArg1).

translate_to_common_vars([Var|_TermVars], [NVar|_NTermVars], Arg, Var) :-
    Arg == NVar, !.
translate_to_common_vars([_Var|TermVars], [_NVar|NTermVars], Arg, OutArg) :-
    translate_to_common_vars(TermVars, NTermVars, Arg, OutArg).


binary_arithmetic_test(Test) :-
    functor(Test, F, A),
    binary_arithmetic_test_(F, A), !.

binary_arithmetic_test_((=:=), 2).
binary_arithmetic_test_((=\=), 2).
binary_arithmetic_test_((<), 2).
binary_arithmetic_test_((>), 2).
binary_arithmetic_test_((=<), 2).
binary_arithmetic_test_((>=), 2).

% (?=)/2
%rnum 
% unary_arithmetic_test_(integer, 1).

unary_arithmetic_test(Test) :-
    functor(Test, F, A),
    unary_arithmetic_test_(F, A), !.

unary_arithmetic_test_(integer, 1).
unary_arithmetic_test_(number, 1).

numeric_operator(Arg) :-
    functor(Arg, F, A),
    numeric_operator_(F,A), !.

numeric_operator_((+), 2).
numeric_operator_((*), 2).
numeric_operator_((/), 2).
numeric_operator_((-), 2).
numeric_operator_((+), 1).
numeric_operator_((-), 1).

%% Boolean operations.

disj_normal_form_test(Test, DNFTest) :-
    disj2formula(Test, FTest),
    formula_normalize(\+(FTest), DNFTest).

disj2formula([Test], FTest) :- !,
    conj2formula(Test, FTest).
disj2formula([Test|Others], ';'(FTest, FOthers)) :-
    conj2formula(Test, FTest),
    disj2formula(Others, FOthers).


% formula_normalize(+F0, -F1) takes a Boolean formula F0 and transforms it to
% an equivalent formula F1 that is a disjunction of conjunctions.

formula_normalize(Fin, Fout) :-
    formula_push_negation(Fin, F0),
    push_conj(F0, Fout).

% b_push_negation pushes negations inwards using De Morgan's rules.

formula_push_negation(\+(','(F1, F2)), ';'(G1, G2)) :-
    !,
    formula_push_negation(\+(F1), G1),
    formula_push_negation(\+(F2), G2).
formula_push_negation(\+(';'(F1, F2)), ','(G1, G2)) :-
    !,
    formula_push_negation(\+(F1), G1),
    formula_push_negation(\+(F2), G2).
formula_push_negation(\+(\+(F)), G) :-
    !,
    formula_push_negation(F, G).
formula_push_negation(','(F1, F2), ','(G1, G2)) :-
    !,
    formula_push_negation(F1, G1),
    formula_push_negation(F2, G2).
formula_push_negation(';'(F1, F2), ';'(G1, G2)) :-
    !,
    formula_push_negation(F1, G1),
    formula_push_negation(F2, G2).
%
formula_push_negation(\+(=(X, Y)), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(\+('$noteq$'(X, Y)), =(X, Y)) :- !.
formula_push_negation(\+(==(X, Y)), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(\+(\==(X, Y)), =(X, Y)) :- !.
formula_push_negation(\+(is(X, Y)), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(\+(=\=(X, Y)), =(X, Y)) :- !.
formula_push_negation(\+(=:=(X, Y)), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(\+(<(X, Y)), >=(X, Y)) :- !.
formula_push_negation(\+(>(X, Y)), <=(X, Y)) :- !.
formula_push_negation(\+(=<(X, Y)), >(X, Y)) :- !.
formula_push_negation(\+(>=(X, Y)), <(X, Y)) :- !.
%
formula_push_negation(=(X, Y), =(X, Y)) :- !.
formula_push_negation('$noteq$'(X, Y), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(==(X, Y), =(X, Y)) :- !.
formula_push_negation(\==(X, Y), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(is(X, Y), =(X, Y)) :- !.
formula_push_negation(=\=(X, Y), (>(X, Y) ; <(X, Y))) :- !.
formula_push_negation(=:=(X, Y), =(X, Y)) :- !.
formula_push_negation(<(X, Y), <(X, Y)) :- !.
formula_push_negation(>(X, Y), >(X, Y)) :- !.
formula_push_negation(=<(X, Y), <=(X, Y)) :- !.
formula_push_negation(>=(X, Y), >=(X, Y)) :- !.

% MOVED FROM subproblems.pl 

solve_other_tests(true, true) :- !.
solve_other_tests([true], true) :- !.
solve_other_tests([], fail) :- !.
solve_other_tests(false, fail) :- !.
solve_other_tests(fail, fail) :- !.
solve_other_tests([false], fail) :- !.
solve_other_tests([fail], fail) :- !.
solve_other_tests([Other|Rest], Res) :-
    numeric_covers(num, [Other|Rest], Res).

% TODO: see similar code in mutexcheck.pl
numeric_covers(num, Other, Res) :-
    !,
    num_covers(Other, Res).
numeric_covers(int, Other, Res) :- % TODO: unused?
    integer_covers(Other, Res).

% Covering with omega clpr.
% num_covers(_Other, true):-!.

num_covers(Tests, Res) :-
    copy_term(Tests, NewTests),
    disj_normal_form_test(NewTests, CLPRTest),
    debug_message("CALL: ~q", [translate_to_ciaoclpr(CLPRTest, CIAOTest)]),
    translate_to_ciaoclpr(CLPRTest, CIAOTest),
    debug_message("EXIT: ~q", [translate_to_ciaoclpr(CLPRTest, CIAOTest)]),
    ( clpr_meta(CIAOTest) -> Res = fail ; Res = true ),
    debug_message("EXIT: ~q", [num_covers(Tests, Res)]).

%% num_covers(Tests, Res):- 
%%    copy_term(Tests, NewTests),
%%    disj_normal_form_test(NewTests, CLPRTest),
%%    debug_message("CALL: ~q", [translate_to_ciaoclpr(CLPRTest, CIAOTest)]), 
%%    translate_to_ciaoclpr(CLPRTest, CIAOTest),
%%    debug_message("EXIT: ~q", [translate_to_ciaoclpr(CLPRTest, CIAOTest)]), 
%%     debug_message("EXIT: ~q", [translate_to_ciaoclpr(CLPRTest, CIAOTest)]), 
%%    open_output('clpr_ciao.pl', Streams),
%%    write(':- module(clpr_ciao, [go/0], [clpr]).'),
%%    nl,
%%    write('go :- '),
%%    write(CIAOTest),
%%    write('.'),
%%    nl,
%%    close_output(Streams),
%%    use_module(clpr_ciao),
%%    (_:go -> Res = fail ; Res = true).

translate_to_ciaoclpr(','(A, B), ','(A1, B1)) :- !,
    translate_to_ciaoclpr(A, A1),
    translate_to_ciaoclpr(B, B1).
translate_to_ciaoclpr(';'(A, B), ';'(A1, B1)) :- !,
    translate_to_ciaoclpr(A, A1),
    translate_to_ciaoclpr(B, B1).
translate_to_ciaoclpr(=(A, B), .=.(A, B)) :- !.
translate_to_ciaoclpr(>(A, B), .>.(A, B)) :- !.
translate_to_ciaoclpr(>=(A, B), .>=.(A, B)) :- !.
translate_to_ciaoclpr(<=(A, B), .=<.(A, B)) :- !.
translate_to_ciaoclpr(<(A, B), .<.(A, B)) :- !.
translate_to_ciaoclpr(','(A, B), ','(A1, B1)) :- !,
    translate_to_ciaoclpr(A, A1),
    translate_to_ciaoclpr(B, B1).

conj2formula([Test], Test) :- !.
conj2formula([Test|Others], ','(Test, FOthers)) :-
    conj2formula(Others, FOthers).


% END OF MOVED FROM subproblems.pl 

% ===========================================================================
%! # Covering with Omega test
% TODO: make it optional? depends on external 'omega' tool

%% For using OMEGA TEST
:- use_module(library(dec10_io), [see/1, seen/0]).
:- use_module(library(system), [system/1, delete_file/1, file_exists/1]).
:- use_module(engine(stream_basic)).
:- use_module(library(write), [write/1, numbervars/3]).
:- use_module(library(iso_char), [char_code/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(io_basic)).

integer_covers(Other, Res) :-
    convert_format(Other),
    call_omega_test(Res).
% call_omega_test(Other).

convert_format(Tests) :-
    copy_term(Tests, Other),
% vars(Other, Vars),
    varset(Other, Vars),
    numbervars(Other, 0, _),
    open(omega_call, write, Omega_Stream),
    set_output(Omega_Stream),
    write('{forall('),
    (Vars == [] -> write(i) ; write_vars(Vars)),
    write(':'),
    disj2omega(Other),
    write(' )};'),
    close(Omega_Stream).

write_vars([]) :- !.
write_vars([H]) :- !, write(H).
write_vars([H|L]) :- write(H), write(','), write_vars(L).


disj2omega([Test]) :- !,
    write(' ( '),
    conj2omega(Test).
disj2omega([Test|Others]) :-
    write(' ( '),
    conj2omega(Test),
    write(' or '),
    disj2omega(Others).

conj2omega([Test]) :- !,
    test2omega(Test),
    write(' ) ').
conj2omega([Test|Others]) :-
    test2omega(Test),
    write(' and '),
    conj2omega(Others).

test2omega(=:=(X, Y)) :- !,
    write(X),
    write(' = '),
    write(Y).
test2omega(is(X, Y)) :- !,
    write(X),
    write(' = '),
    write(Y).
test2omega(=\=(X, Y)) :- !,
    write(X),
    write(' != '),
    write(Y).
test2omega(<(X, Y)) :- !,
    write(X),
    write(' < '),
    write(Y).
test2omega(>(X, Y)) :- !,
    write(X),
    write(' > '),
    write(Y).
test2omega(=<(X, Y)) :- !,
    write(X),
    write(' <= '),
    write(Y).
test2omega(>=(X, Y)) :- !,
    write(X),
    write(' >= '),
    write(Y).

call_omega_test(Res) :-
    ( nonvar(Res) -> true
    ; ( file_exists(omega_out) ->
          delete_file(omega_out)
      ; true
      ),
      system('omega omega_call > omega_out'), !,
%  open(omega_out, write, Omega_Stream),
%  set_output(Omega_Stream),
%  popen('omega omega_call', write, Omega_Stream), % TODO: zombie process! (use process_call, close, and process_join)
%  close(Omega_Stream),
      omega_test(Res)
    ).

% call_omega_test(X):- nl, writeq(X), nl. % define

omega_test(Res) :-
    ( nonvar(Res) -> true
    ; see(omega_out),
      get_omega_output(N1, N2, N3, N4, N5),
      seen,
      ( true_omega_output(N1, N2, N3, N4, N5) ->
          Res = true
      ; Res = fail
      )
    ).


get_omega_output(N1, N2, N3, N4, N5) :-
% position_output_line(0'{), % Commented by PLG 30-6-99
    get_code(N1),
    get_code(N2),
    get_code(N3),
    get_code(N4),
    get_code(N5).

true_omega_output(N1, N2, N3, N4, N5) :-
    characters_equal(N1, '{'),
    characters_equal(N2, '['),
    characters_equal(N3, ']'),
    characters_equal(N4, ' '),
    characters_equal(N5, '}').

characters_equal(Code, Char) :-
    char_code(Char, C),
    C =:= Code.

%% END COVERING WITH OMEGA TEST.
