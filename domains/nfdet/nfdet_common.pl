:- module(_, [], [assertions,regtypes]).

:- doc(title, "@tt{nfdet} Common Operations").

:- doc(module, "This module provides common utilities for @tt{nfdet},
   @tt{nf}, and @tt{det} domains (the so called @tt{nfdet*}
   domains).").

:- doc(author, "V@'{i}ctor P@'{e}rez").
:- doc(author, "Francisco Bueno").
:- doc(author, "Pedro Lopez-Garcia").
:- doc(author, "Manuel Hermenegildo").
:- doc(author, "Jose F. Morales").

:- use_module(domain(nfdet/nfdet), [asub/5]).
:- use_module(domain(nfdet/nfplai), [asub/4]).
:- use_module(domain(nfdet/nfabs), [nfabs_asub/1, asub/5]).
:- use_module(domain(nfdet/detplai), [asub/4]).
:- use_module(domain(nfdet/detabs), [detabs_asub/1, asub/4]).

% TODO: Split. Move "internal" common nfdet operations to a new
% nfdetabs module.

% TODO: Move more operations here.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: Move.
:- doc(bool_t(Bool), "@var{Bool} may be @tt{true} or @tt{false}.").

:- regtype bool_t(Bool)
   # "@var{Bool} may be @tt{true} or @tt{false}.".

bool_t(true).
bool_t(false).

:- doc(nf_det_asub(ASub), "@var{ASub} is a nfdet* abstract
   substitution.").

:- regtype nf_det_asub(ASub)
   # "@var{ASub} is a nfdet* abstract substitution.".

% TODO: Define.
nf_det_asub(ASub) :-
    term(ASub).

:- doc(nfdet_test_class(Class), "@var{Class} is a test class. It can
   be any of:
   @begin{itemize}
   @item @tt{unif}
   @item @tt{arith}
   @item @tt{meta}
   @end{itemize}").

:- regtype nfdet_test_class(Class)
   # "@var{Class} is a test class.".

nfdet_test_class(unif).
nfdet_test_class(arith).
nfdet_test_class(meta).

:- doc(tests_t(Tests), "@var{Tests} represents a set of tests in a
   clause upto a program point. It contains input variables,
   unification tests, arithmetic tests and meta tests.").

:- regtype tests_t(Tests)
   # "@var{Tests} represents a set of tests in a clause upto a program
   point.".

tests_t(t(InVars,Unif,Arith,Meta)) :-
    list(InVars),
    list(Unif),
    list(Arith),
    list(Meta).

:- export(tests/5).

:- doc(tests(Tests,InVars,Unif,Arith,Meta), "@var{Tests} is the test
   term (see @pred{tests_t/1}) with input variables @var{InVars},
   unification tests @var{Unif}, arithmetic tests @var{Arith} and meta
   tests @var{Meta}.").

:- pred tests(Tests,InVars,Unif,Arith,Meta)
   : ( tests_t(Tests), var(InVars), var(Unif), var(Arith), var(Meta) )
   => ( tests_t(Tests), list(InVars), list(Unif), list(Arith), list(Meta) ).

:- pred tests(Tests,InVars,Unif,Arith,Meta)
   : ( var(Tests), list(InVars), list(Unif), list(Arith), list(Meta) )
   => ( tests_t(Tests), list(InVars), list(Unif), list(Arith), list(Meta) ).

tests(t(InVars,Unif,Arith,Meta),InVars,Unif,Arith,Meta).

select_tests([T|_],Select,Tests) :-
    tests(T,_,Unif,Arith,Meta),
    ( Select = unif ->
        Tests = Unif
    ; Select = arith ->
        Tests = Arith
    ; Select = meta ->
        Tests = Meta
    ).

:- export(get_tests_from_asub/3).

:- doc(get_tests_from_asub(ASub,Select,Tests), "Returns in @var{Tests}
   tests of class @var{Select} (see @pred{test_t/1}) in abstract
   substitution @var{ASub}").

:- pred get_tests_from_asub(ASub,Select,Tests)
   : ( nf_det_asub(ASub), nfdet_test_class(Select), var(Tests) )
   => ( nf_det_asub(ASub), nfdet_test_class(Select), list(Tests) )
   # "@var{Tests} are the tests of class @var{Select} in abstract
     substitution @var{ASub}".

get_tests_from_asub(ASub,Select,Tests) :-
    ( nfplai:asub(ASub,_,_,NF) ->
        nfabs:asub(NF,T,_,_,_)
    ; detplai:asub(ASub,_,_,Det) ->
        detabs:asub(Det,T,_,_)
    ; nfdet:asub(ASub,_,_,NF,_),
      nfabs:asub(NF,T,_,_,_)
    ),
    select_tests(T,Select,Tests).

:- export(asub_can_fail/2).

:- doc(asub_can_fail(ASub,CanFail), "Returns @tt{false} in
   @var{CanFail} if @var{ASub} represents non-failure, and
   @tt{true} otherwise.").

:- pred asub_can_fail(ASub,CanFail)
   : ( nfabs_asub(ASub), var(CanFail) )
   => ( nfabs_asub(ASub), bool_t(CanFail) ).

asub_can_fail(ASub,false) :- nfabs:asub(ASub,_,_,_,not_fails), !.
asub_can_fail(_,true).

:- export(asub_is_det/2).

:- doc(asub_is_det(ASub,IsDet), "Returns @tt{true} in @var{IsDet} if
   @var{ASub} represents determinism and @tt{false} otherwise.").

:- pred asub_is_det(ASub,IsDet)
   : ( detabs_asub(ASub), var(IsDet) )
   => ( detabs_asub(ASub), bool_t(IsDet) ).

asub_is_det(ASub,true) :- detabs:asub(ASub,_,_,is_det), !.
asub_is_det(_,false).

:- export(split_self/2).

:- doc(split_self(ASub,SelfASub), "Returns in @var{SelfASub}
   nonfailure/determinism information contained in @var{ASub}.").

split_self(ASub,SelfASub) :- nfplai:asub(ASub,_,_,SelfASub), !.
split_self(ASub,SelfASub) :- detplai:asub(ASub,_,_,SelfASub), !.
split_self(ASub,SelfASub) :- nfdet:asub(ASub,_,_,SelfASub,_).
split_self(ASub,SelfASub) :- nfdet:asub(ASub,_,_,_,SelfASub).
