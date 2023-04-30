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

:- use_module(domain(nfdet/nfdet), [nfdet_asub/1, asub/5]).
:- use_module(domain(nfdet/nfplai), [nf_asub/1, asub/4]).
:- use_module(domain(nfdet/detplai), [det_asub/1, asub/4]).
:- use_module(domain(nfdet/nfabs), [nfabs_asub/1, asub_can_fail/1, get_tests/2]).
:- use_module(domain(nfdet/detabs), [detabs_asub/1, asub_is_det/1, get_tests/2]).
:- use_module(domain(nfdet/nfdetabs), [tests/5, clause_test/1]).

% TODO: Split. Move "internal" common nfdet operations to a new
% nfdetabs module.

% TODO: Move more operations here.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: Move.
:- export(bool_t/1).

:- doc(bool_t(Bool), "@var{Bool} may be @tt{true} or @tt{false}.").

:- regtype bool_t(Bool)
   # "@var{Bool} may be @tt{true} or @tt{false}.".

bool_t(true).
bool_t(false).

:- export(nf_det_asub/1).

:- doc(nf_det_asub(ASub), "@var{ASub} is a nfdet* abstract
   substitution.").

:- regtype nf_det_asub(ASub)
   # "@var{ASub} is a nfdet* abstract substitution.".

nf_det_asub(ASub) :-
    nf_asub(ASub).
nf_det_asub(ASub) :-
    det_asub(ASub).
nf_det_asub(ASub) :-
    nfdet_asub(ASub).

:- export(nf_det_abs_asub/1).

:- doc(nf_det_abs_asub(ASub), "@var{ASub} is either an nf or det
   abstract substitution (see @pred{nfabs_asub/1} and
   @pred{detabs_asub/1}).").

:- regtype nf_det_abs_asub(ASub)
   # "@var{ASub} is an nf or det abstract substitution".

nf_det_abs_asub(ASub) :-
    nfabs_asub(ASub).
nf_det_abs_asub(ASub) :-
    detabs_asub(ASub).

:- export(nfdet_test_class/1).

:- doc(nfdet_test_class(Class), "@var{Class} represents a class of
   tests:
   @begin{description}
   @item{@tt{unif}} Unification tests
   @item{@tt{arith}} Arithmetic tests
   @item{@tt{meta}} Other tests
   @end{description}").

:- regtype nfdet_test_class(Class)
   # "@var{Class} is a test class.".

nfdet_test_class(unif).
nfdet_test_class(arith).
nfdet_test_class(meta).

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
   tests of class @var{Select} (see @pred{clause_test/1}) in abstract
   substitution @var{ASub}").

:- pred get_tests_from_asub(ASub,Select,Tests)
   : ( nf_det_asub(ASub), nfdet_test_class(Select), var(Tests) )
   => ( nf_det_asub(ASub), nfdet_test_class(Select), list(Tests) )
   # "@var{Tests} are the tests of class @var{Select} in abstract
     substitution @var{ASub}".

get_tests_from_asub(ASub,Select,Tests) :-
    ( nfplai:asub(ASub,_,_,NF) ->
        nfabs:get_tests(NF,T)
    ; detplai:asub(ASub,_,_,Det) ->
        detabs:get_tests(Det,T)
    ; nfdet:asub(ASub,_,_,NF,_),
      nfabs:get_tests(NF,T)
    ),
    select_tests(T,Select,Tests).

:- export(asub_can_fail/2).

:- doc(asub_can_fail(ASub,CanFail), "Returns @tt{false} in
   @var{CanFail} if @var{ASub} represents non-failure, and
   @tt{true} otherwise.").

:- pred asub_can_fail(ASub,CanFail)
   : ( nfabs_asub(ASub), var(CanFail) )
   => ( nfabs_asub(ASub), bool_t(CanFail) ).

asub_can_fail(ASub,true) :-
    nfabs:asub_can_fail(ASub), !.
asub_can_fail(_,false).

:- export(asub_is_det/2).

:- doc(asub_is_det(ASub,IsDet), "Returns @tt{true} in @var{IsDet} if
   @var{ASub} represents determinism and @tt{false} otherwise.").

:- pred asub_is_det(ASub,IsDet)
   : ( detabs_asub(ASub), var(IsDet) )
   => ( detabs_asub(ASub), bool_t(IsDet) ).

asub_is_det(ASub,true) :-
    detabs:asub_is_det(ASub), !.
asub_is_det(_,false).

:- export(split_self/2).

:- doc(split_self(ASub,SelfASub), "Returns in @var{SelfASub}
   nonfailure/determinism information contained in @var{ASub}.").

:- pred split_self(ASub,SelfASub)
   : ( nf_asub(ASub), var(SelfASub) )
   => ( nf_asub(ASub), nfabs_asub(SelfASub) ).

:- pred split_self(ASub,SelfASub)
   : ( det_asub(ASub), var(SelfASub) )
   => ( det_asub(ASub), detabs_asub(SelfASub) ).

:- pred split_self(ASub,SelfASub)
   : ( nfdet_asub(ASub), var(SelfASub) )
   => ( nfdet_asub(ASub), nf_det_abs_asub(SelfASub) ).

split_self(ASub,SelfASub) :- nfplai:asub(ASub,_,_,SelfASub), !.
split_self(ASub,SelfASub) :- detplai:asub(ASub,_,_,SelfASub), !.
split_self(ASub,SelfASub) :- nfdet:asub(ASub,_,_,SelfASub,_).
split_self(ASub,SelfASub) :- nfdet:asub(ASub,_,_,_,SelfASub).
