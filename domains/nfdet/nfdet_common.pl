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

:- use_module(ciaopp(plai/domains), [call_to_entry/10]).

:- use_module(domain(nfdet/nfdet), [nfdet_asub/1, asub/5]).
:- use_module(domain(nfdet/nfplai), [nf_asub/1, asub/4]).
:- use_module(domain(nfdet/detplai), [det_asub/1, asub/4]).
:- use_module(domain(nfdet/nfabs), [asub/5, nfabs_asub/1, asub_can_fail/1, get_tests/2]).
:- use_module(domain(nfdet/detabs), [asub/5, detabs_asub/1, asub_is_det/1, get_tests/2]).
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

:- export(nfdet_condition/1).

:- doc(nfdet_condition(Cond), "@var{Cond} is a condition which can be
   verified using nfdet* info.").

:- regtype nfdet_condition(Cond)
   # "@var{Cond} is a condition which can be verified using nfdet*
   info.".

nfdet_condition(det).
nfdet_condition(semidet).
nfdet_condition(multi).
nfdet_condition(fails).
nfdet_condition(multi_min2).

% ------------------------------------------------------------------------

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

:- export(asub_surely_fails/2).

:- doc(asub_surely_fails(ASub,Fails), "Returns @tt{true} in
   @var{Fails} if @var{ASub} represents failure, and @tt{false}
   otherwise.").

:- pred asub_surely_fails(ASub,Fails)
   : ( nfabs_asub(ASub), var(Fails) )
   => ( nfabs_asub(ASub), bool_t(Fails) ).

asub_surely_fails(ASub,true) :- nfabs:asub(ASub,_,_,_,fails), !.
asub_surely_fails(_,false).

:- export(asub_is_surely_non_det/2).

:- doc(asub_is_surely_non_det(ASub,IsNonDet), "Returns @tt{true} in
   @var{IsNonDet} if @var{ASub} contains @tt{non_det}, and @tt{false}
   otherwise.").

:- pred asub_is_surely_non_det(ASub,IsNonDet)
   : ( nfabs_asub(ASub), var(IsNonDet) )
   => ( nfabs_asub(ASub), bool_t(IsNonDet) ).

asub_is_surely_non_det(ASub,true) :- detabs:asub(ASub,_,_,_,non_det), !.
asub_is_surely_non_det(_,false).

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

% (nondet)
split_self(ASub,SelfASub) :- nfplai:asub(ASub,_,_,SelfASub), !.
split_self(ASub,SelfASub) :- detplai:asub(ASub,_,_,SelfASub), !.
split_self(ASub,SelfASub) :- nfdet:asub(ASub,_,_,Nf,Det),
    ( SelfASub = Nf
    ; SelfASub = Det
    ).

:- export(nfdet_cond/2).

:- doc(nfdet_cond(Cond, Info), "Checks whether condition @var{Cond}
   can be verified using info @var{Info}.").

:- pred nfdet_cond(Cond, Info)
   : ( nfdet_condition(Cond), nf_det_asub(Info) )
   # "Condition @var{Cond} can be verified using info @var{Info}.".

% TODO: Change calls to x:asub/N by call x:x_asub/1 when defined.
nfdet_cond(det, Info) :-
    nfdet:asub(Info,_,_,Nf,Det),
    asub_can_fail(Nf, CanFail),
    CanFail = false,
    asub_is_det(Det, true).
nfdet_cond(semidet, Info) :-
    split_self(Info, Self),
    detabs:asub(Self,_,_,_,_), !,
    asub_is_det(Self, true).
nfdet_cond(multi, Info) :-
    split_self(Info, Self),
    nfabs:asub(Self,_,_,_,_), !,
    asub_can_fail(Self, CanFail),
    CanFail = false.
nfdet_cond(fails, Info) :-
    ( Info = '$bottom' ->
        true
    ; split_self(Info, Self),
      nfabs:asub(Self,_,_,_,_), !,
      asub_surely_fails(Self, true)
    ).
nfdet_cond(multi_min2, Info) :-
    split_self(Info, Self),
    detabs:asub(Self,_,_,_,_), !,
    asub_is_surely_non_det(Self, true).

:- export(nfdet_decide_call_to_entry/7).

:- doc(nfdet_decide_call_to_entry(AbsInt,Call_s,Go1v,Goal1,Gov,Goal,Call),
   "Calls @pred{call_to_entry/10} on the types and modes info of
   @var{AbsInt}").

nfdet_decide_call_to_entry(nf, Call_s, Go1v, Goal1, Gov, Goal, Call) :- !,
    nfplai:asub(Call_s, Types_s, Modes_s, Nf),
    nfdet_decide_call_to_entry_(Types_s, Modes_s, Go1v, Goal1, Gov, Goal, Types, Modes),
    nfplai:asub(Call, Types, Modes, Nf).
nfdet_decide_call_to_entry(det, Call_s, Go1v, Goal1, Gov, Goal, Call) :- !,
    detplai:asub(Call_s, Types_s, Modes_s, Det),
    nfdet_decide_call_to_entry_(Types_s, Modes_s, Go1v, Goal1, Gov, Goal, Types, Modes),
    detplai:asub(Call, Types, Modes, Det).
nfdet_decide_call_to_entry(nfdet, Call_s, Go1v, Goal1, Gov, Goal, Call) :-
    nfdet:asub(Call_s, Types_s, Modes_s, Nf, Det),
    nfdet_decide_call_to_entry_(Types_s, Modes_s, Go1v, Goal1, Gov, Goal, Types, Modes),
    nfdet:asub(Call, Types, Modes, Nf, Det).

nfdet_decide_call_to_entry_(Types_s, Modes_s, Go1v, Goal1, Gov, Goal, Types, Modes) :-
    call_to_entry(eterms, Go1v, Goal1, Gov, Goal, not_provided, [], Types_s, Types, _),
    call_to_entry(shfr, Go1v, Goal1, Gov, Goal, not_provided, [], Modes_s, Modes, _).
