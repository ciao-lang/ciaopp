:- module(_, [], [assertions,regtypes]).

:- doc(title, "@tt{nfdet}abs").

:- doc(module, "This module provides common predicates to be used
   accross @tt{nfdet}, @tt{nf}, and @tt{det} domains (referred to as
   @tt{nfdet*} domains as a class).").

:- doc(author, "V@'{i}ctor P@'{e}rez").
:- doc(author, "Francisco Bueno").
:- doc(author, "Pedro Lopez-Garcia").
:- doc(author, "Manuel Hermenegildo").
:- doc(author, "Jose F. Morales").

% TODO: Move more predicates here.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! # Tests

:- export(clause_test/1).

:- doc(clause_test(Test), "@var{Test} represents a conjunction of
   tests in a clause upto a program point. It contains input
   variables, unification tests, arithmetic tests and meta tests.").

:- regtype clause_test(Test)
   # "@var{Test} represents a conjunction of tests in a clause upto a
   program point. It contains input variables, unification tests,
   arithmetic tests and meta tests.".

clause_test(t(InVars,Unif,Arith,Meta)) :-
    list(InVars),
    uniftest_conj(Unif),
    arithtest_conj(Arith),
    metatest_conj(Meta).

:- regtype uniftest_conj(UnifC)
   # "@var{UnifC} represents a conjunction of basic unification tests.".

uniftest_conj(UnifC):-     
    list(uniftest,UnifC).

:- regtype arithtest_conj(ArithC)
   # "@var{ArithC} represents a conjunction of basic arithmetic tests.".

arithtest_conj(ArithC):- 
    list(arithtest,ArithC).

:- regtype metatest_conj(MetaC)
   # "@var{MetaC} represents a conjunction of basic meta tests.".

metatest_conj(MetaC):-
    list(metatest,MetaC).

:- regtype uniftest(Unif)
   # "@var{Unif} represents a basic unification test.".

uniftest('='(X,Y)):- term(X), term(Y).
uniftest('\\='(X,Y)):- term(X), term(Y).
uniftest('=='(X,Y)):- term(X), term(Y).
uniftest('\\=='(X,Y)):- term(X), term(Y).

:- regtype arithtest(Arith)
   # "@var{Arith} represents a basic arithmetic test.".   

arithtest('=:='(X,Y)):- term(X), term(Y). 
arithtest('=\\='(X,Y)):- term(X), term(Y).
arithtest('<'(X,Y)):- term(X), term(Y).
arithtest('>'(X,Y)):- term(X), term(Y).
arithtest('=<'(X,Y)):- term(X), term(Y).
arithtest('>='(X,Y)):- term(X), term(Y).

:- regtype metatest(Meta)
   # "@var{Meta} represents a basic meta test.".

metatest('!').
metatest(number(X)):- term(X).
metatest(integer(X)):- term(X).
metatest(float(X)):- term(X).
metatest(atomic(X)):- term(X).
metatest(atom(X)):- term(X).
metatest(var(X)):- term(X).
metatest(nonvar(X)):- term(X).
metatest(ground(X)):- term(X).

:- export(tests/5).

:- doc(tests(Tests,InVars,Unif,Arith,Meta), "@var{Tests} is the test
   term (see @pred{clause_test/1}) with input variables @var{InVars},
   unification tests @var{Unif}, arithmetic tests @var{Arith} and meta
   tests @var{Meta}.").

:- pred tests(Tests,InVars,Unif,Arith,Meta)
   : ( clause_test(Tests), var(InVars), var(Unif), var(Arith), var(Meta) )
   => ( clause_test(Tests), list(InVars), uniftest_conj(Unif),
        arithtest_conj(Arith), metatest_conj(Meta) ).

:- pred tests(Tests,InVars,Unif,Arith,Meta)
   : ( var(Tests), list(InVars), uniftest_conj(Unif),
       arithtest_conj(Arith), metatest_conj(Meta) )
   => ( clause_test(Tests), list(InVars), uniftest_conj(Unif),
        arithtest_conj(Arith), metatest_conj(Meta)).

tests(t(InVars,Unif,Arith,Meta),InVars,Unif,Arith,Meta).

:- export(pred_test/1).

:- regtype pred_test(Test)
   # "@var{Test} represents a predicate test, i.e., either a single
   @tt{clause test}, or a list of @tt{clause tests}, representing the
   disjunction of them. It is needed for performing the covering and
   mutual exclusion checks.".

pred_test(Test) :-
    clause_test(Test).
pred_test(Test) :-
    clause_test_disj(Test).

:- export(clause_test_disj/1).
:- regtype clause_test_disj(Test)
   # "@var{Test} is a list of @tt{clause tests}, representing the
     disjunction of them.".

clause_test_disj(Test) :-
    list(clause_test, Test).

:- export(unfold_t/1).

:- regtype unfold_t/1.

unfold_t(unfold).
unfold_t(not_unfold).
unfold_t('$bottom').

:- export(mode_types/1).

:- regtype mode_types(ModeTypes)
   # "@var{ModeTypes} is a compact representation of the modes
     (@tt{in}/@tt{out}) and (regular) types for a predicate.".

mode_types(ModeTypes):- term(ModeTypes).

