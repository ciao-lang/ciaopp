:- module(nfabs, [
    nf_call_to_entry/10,
    nf_exit_to_prime/7,
    nf_project/5,
    nf_extend/5,
    nf_widen/3,
    nf_compute_lub/2,
    nf_compute_covering/3,
    nf_glb/3,
    nf_less_or_equal/2,
    nf_identical_abstract/2,
    nf_abs_sort/2,
    nf_call_to_success_fact/9,
    nf_special_builtin/1,
    nf_success_builtin/6,
    % nf_call_to_success_builtin/6,
    nf_input_interface/4,
    nf_input_user_interface/5,
    nf_asub_to_native/3,
    nf_unknown_call/4,
    nf_unknown_entry/3,
    nf_empty_entry/3,
    nfabs_dom_statistics/1,
    possibly_fail_unif_tests/2
], [assertions,regtypes,basicmodes,hiord]).

:- use_module(domain(nfdet/nfsets), [create_minset_and_project/4]).
:- use_module(domain(nfdet/cover), [covers_check/5]).
:- use_module(domain(nfdet/nfbool), [push_neg_in_test/2, remove_negation/2, translate_test/2]).
:- use_module(domain(sharefree), [shfr_obtain_info/4]).
:- use_module(domain(s_eqs), [peel/4]).
:- use_module(domain(nfdet/nfdet_statistics)).
:- use_module(domain(nfdet/nfdetabs), [pred_test/1, tests/5, unfold_t/1,mode_types/1, clause_test/1, clause_test_disj/1]).
:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(hiordlib), [foldr/4]).
:- use_module(library(sets), [merge/3]).
:- use_module(library(terms_vars), [varset/2]).

:- doc(title,"Nonfailure Abstract Domain").
:- doc(module,"

This module implements the abstract operations of a nonfailure domain
for the PLAI framework of abstract interpretation. Abstract
substitutions for this domain are a pair of (Covered,Fails) elements,
where Covered is @tt{possibly_not_covered}, @tt{not_covered} or
@tt{covered}; and Fails is @tt{possibly_fails}, @tt{fails} or
@tt{not_fails}. Note that the lattice for covering is analogous to the
lattice of nonfailure, but applied to guard tests.

The abstract domain lattices for nonfailure and covering are:

@begin{verbatim}

   possibly_not_covered          possibly_fails
         /     \\                   /     \\
        /       \\                 /       \\
 not_covered  covered           fails   not_fails
        \\      /                 \\       /
         \\    /                   \\     /
         $bottom                    $bottom

@end{verbatim}

").

%------------------------------------------------------------------------%

:- doc(bug,"Think on an adequate treatment for negation.").

% TODO: Convering info may not be very useful for users; we may want to hide it.

%------------------------------------------------------------------------%

:- export(nfabs_asub/1).

:- doc(nfabs_asub(ASub), "@var{ASub} is an abstract substitution term
   used in nf.").

:- regtype nfabs_asub(ASub)
   # "@var{ASub} is an abstract substitution term used in nf.".

nfabs_asub(ASub):- nfabs_par_asub(clause_test,ASub).

:- doc(nfabs_par_asub(TestTyp,ASub), "@var{ASub} is an abstract
   substitution term used in nf with tests of type @var{TestTyp}.").

:- regtype nfabs_par_asub(TestTyp,ASub)
   # "@var{ASub} is an abstract substitution term used in nf with
     tests of type @var{TestTyp}.".

:- meta_predicate nfabs_par_asub(pred(1), ?).

nfabs_par_asub(_, '$bottom').
nfabs_par_asub(TestTyp, nf(Tests,Unfold,Covered,Fails)) :-
    TestTyp(Tests),    
    unfold_t(Unfold),
    covering_t(Covered),
    nonfailure_t(Fails).

:- export(nfabs_pred_asub/1).
:- regtype nfabs_pred_asub(ASub)
   # "@var{ASub} is a compact representation for a set of abstract
     substitutions corresponding to (a subset of) clauses of a
     predicate (the ones that do not fail so far). It gathers together
     the clause tests of those abstract substitutions as a list,
     meaning the disjunction of all of them (named the @tt{predicate
     test}, which is needed for performing the @tt{covering test}).
     If the list of tests is empty, it represents an empty set of
     abstract substitutions.".

nfabs_pred_asub(ASub):- nfabs_par_asub(pred_test,ASub).

:- regtype covering_t(Covering)
   # "@var{Covering} represents covering information for a call pattern.".

covering_t(possibly_not_covered).
covering_t(covered).
covering_t(not_covered).
covering_t('$bottom').

:- regtype nonfailure_t(Nonfailure)
   # "@var{Nonfailure} represents (non-)failure information for a call pattern.".

nonfailure_t(possibly_fails).
nonfailure_t(not_fails).
nonfailure_t(fails).
nonfailure_t('$bottom').

asub(nf(Tests,Unfold_Tests,Covered,Fails),Tests,Unfold_Tests,Covered,Fails).

:- export(get_tests/2).

:- doc(get_tests(ASub,Tests), "Returns in @var{Tests} the tests in
   abstract substitution @var{ASub}.").

:- pred get_tests(ASub,Tests)
   : ( nfabs_asub(ASub), var(Tests) )
   => ( nfabs_asub(ASub), pred_test(Tests) )
   # "@var{Tests} are the tests in abstract substitution @var{ASub}.".

get_tests(ASub,Tests) :-
    asub(ASub,Tests,_,_,_).

:- export(asub_can_fail/1).

:- doc(asub_can_fail(ASub), "Succeeds if and only if abstract
   substitution @var{ASub} represents failure or possible failure.").

:- pred asub_can_fail(ASub)
   : nfabs_asub(ASub)
   => nfabs_asub(ASub)
   # "@var{ASub} represents failure or possible failure.".

asub_can_fail(ASub) :-
    asub(ASub,_,_,_,Fails),
    Fails \= not_fails.

%------------------------------------------------------------------------%
% nf_call_to_entry(+,+,+,+,+,+,+,-,-)                                    %
% nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)              %
%------------------------------------------------------------------------%
% Entering a clause: initialize an asub to start gathering the tests of
% this clause 

nf_call_to_entry(_Sv,Sg,Hv,Head,_K,_Fv,_Proj,InVars,Entry,_Extra):-
    nf_empty_entry(Sg,Hv,Entry0),
    % TODO: Hv is irrelevant here, as the tests of Entry0 are ignored. 
    asub(Entry0,_Tests,Unfold,Covered,Fails),
    asub(Entry,Tests,Unfold,Covered,Fails),
    peel(Sg,Head,Bindings,[]),
    tests(Tests,InVars,Bindings,[],[]).

%------------------------------------------------------------------------%
% nf_exit_to_prime(+,+,+,+,+,-,-)                                        %
% nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                   %
%------------------------------------------------------------------------%
% Exiting a clause: project the tests gathered while traversing the clause 
% onto the variables of the goal

nf_exit_to_prime(Sg,_Hv,Head,_Sv,Exit,GVars,Prime):-
    asub(Exit,Tests,Unfold,Covered,Fails),
    tests(Tests,_InVars,Unif,Arith,Meta),
%%
%%      create_unif_tests(Sg,Type,SgInVars,SgEqs),
%%      create_unif_tests(Head,Type,HeadInVars,HeadEqs),
%%      copy_term((HeadInVars,HeadEqs,Tests),(HeadInVarsC,HeadEqsC,TestsC)),
%%      unify(TestsC),
%%      unify(HeadEqsC),
%%      copy_term((SgInVars,SgEqs),(SgInVarsC,SgEqsC)),
%%      unify(SgEqsC),
%%      SgInVarsC = HeadInVarsC, !,
%%      new_tests(SgInVars,SgInVarsC,PrimeTests),
%%
    peel(Sg,Head,Bindings,Unif), !,
    tests(PrimeTests,GVars,Bindings,Arith,Meta),
    asub(Prime,PrimeTests,Unfold,Covered,Fails).
nf_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_Extra,'$bottom').

% new_tests([],[],[]).
% new_tests([X|Xs],[Y|Ys],[X=Y|Eqs]):-
%       new_tests(Xs,Ys,Eqs).

%------------------------------------------------------------------------%
% nf_project(+,+,+,+,-)                                                  %
% nf_project(Sg,Vars,HvFv_u,ASub,Proj)                                   %
%------------------------------------------------------------------------%
% TODO: Currently Proj = ASub.
%       To project on Vars, leave only tests for Vars.

nf_project(_Sg,Vars,_HvFv_u,ASub,Proj):-
    asub(ASub,Tests0,Unfold,Covered,Fails),
    select_tests(Tests0,Vars,TestsProj),
    asub(Proj,TestsProj,Unfold,Covered,Fails).

select_tests(Tests,_Vars,Tests).

%------------------------------------------------------------------------%
% nf_extend(+,+,+,+,-)                                                   %
% nf_extend(Sg,Prime,Sv,Call,Succ)                                       %
%------------------------------------------------------------------------%
% Return back to the calling clause: merge the tests in Call with the
% tests in Prime

% Unfold tests if the predicate of the body call has only one clause
% and only builtin tests are performed in such clause. 
nf_extend(_Sg,Prime,_Sv,Call,Succ):-
    asub(Prime,Tests0,Unfold0,Covered0,Fails0),
    asub(Call,Tests1,Unfold1,_Covered1,Fails1),
    ( Unfold0 == unfold, Tests0 = t(_,_,_,_) ->
        unfold_tests(Tests0,Tests1,Tests),
        extend_unfold_tests(Unfold0,Unfold1,Unfold)
    ; Unfold = not_unfold,
      Tests = Tests1
    ),
    extend_nonfailure(Fails0,Fails1,Fails),
    asub(Succ,Tests,Unfold,Covered0,Fails).

%% unfold_tests(Tests0,Tests1,Tests) :-
    % TODO: enable this version when test unfolding in directly
    % recursive predicates is solved.
    %% tests(Tests0,InVars0,Unif0,Arith0,Meta0),
    %% tests(Tests1,InVars1,Unif1,Arith1,Meta1),
    %% append(InVars0,InVars1,InVars),
    %% append(Unif0,Unif1,Unif),
    %% append(Arith0,Arith1,Arith),
    %% append(Meta0,Meta1,Meta),
    %% tests(Tests,InVars,Unif,Arith,Meta).
% (dummy version)
unfold_tests(_Tests0,Tests,Tests).

extend_covering('$bottom',_,'$bottom'):-!.
extend_covering(_,'$bottom','$bottom'):-!.
extend_covering(not_covered,_,not_covered):-!.
extend_covering(_,not_covered,not_covered):-!.
extend_covering(possibly_not_covered,_,possibly_not_covered):-!.
extend_covering(_,possibly_not_covered,possibly_not_covered):-!.
extend_covering(_,_,covered).

extend_nonfailure('$bottom',_,'$bottom'):-!.
extend_nonfailure(_,'$bottom','$bottom'):-!.
extend_nonfailure(fails,_,fails):-!.
extend_nonfailure(_,fails,fails):-!.
extend_nonfailure(possibly_fails,_,possibly_fails):-!.
extend_nonfailure(_,possibly_fails,possibly_fails):-!.
extend_nonfailure(_,_,not_fails).

extend_unfold_tests(not_unfold, _, not_unfold):-!.
extend_unfold_tests(_, not_unfold, not_unfold):-!.
extend_unfold_tests(_,_, unfold).

%------------------------------------------------------------------------%
% nf_widen(+,+,-)                                                        %
% nf_widen(Prime0,Prime1,NewPrime)                                       %
%------------------------------------------------------------------------%

nf_widen(Prime0,Prime1,NewPrime) :-
    asub(ASub,[],unfold,covered,not_fails),
    foldr(widen,[Prime0,Prime1],ASub,NewPrime).

widen('$bottom',ASub0,ASub0):- !.
widen(ASub0,'$bottom',ASub0):- !.
widen(ASub,ASub0,NewASub):-
    asub(ASub0,Tests0,Unfold0,Covered0,Fails0),
    asub(ASub,Tests1,Unfold1,Covered1,Fails1),
    tests_union(Tests1,Tests0,Tests), % Tests=[Tests1|Tests0],
    ( Fails0 = not_fails ->
        lub_covering(Covered0,Covered1,Covered),
        lub_nonfailure(Fails0,Fails1,Fails),
        lub_unfold_tests(Unfold0,Unfold1,Unfold)
    ; extend_covering(Covered0,Covered1,Covered),
      extend_nonfailure(Fails0,Fails1,Fails),
      extend_unfold_tests(Unfold0,Unfold1,Unfold)
    ),
    asub(NewASub,Tests,Unfold,Covered,Fails).

%------------------------------------------------------------------------%
% nf_compute_lub(+,-)                                                    %
% nf_compute_lub(ListASub,Lub)                                           %
%------------------------------------------------------------------------%
% Simply put all tests together (this is due to the way this operation
% is called from the fixpoint)

:- pred nf_compute_lub(ListASub,CASub)
   : ( list(nfabs_asub,ListASub),
       var(CASub) )
   => ( list(nfabs_asub,ListASub),
        nfabs_par_asub(clause_test_disj,CASub) )
   # "@var{CASub} is a compact representation for (a subset of)
     abstract substitutions in @var{ListASub} (the ones that do not
     fail so far). It gathers together the clause tests of those
     abstract substitutions as a list, meaning the disjunction of all
     of them (i.e., a @tt{predicate test}, which is needed for
     performing the @tt{covering check}). If the list of tests is
     empty, it represents an empty set of abstract substitutions.".

nf_compute_lub(ListASub,Lub):-
     asub(Asub,[],'$bottom','$bottom','$bottom'),
     foldr(accumulate,ListASub,Asub,Lub).

accumulate('$bottom',ASub0,ASub0):- !.
accumulate(ASub0,'$bottom',ASub0):- !.
accumulate(ASub,ASub0,NewASub):-
    asub(ASub0,Tests0,Unfold0,Covered0,Fails0),
    asub(ASub,Tests1,Unfold1,Covered1,Fails1),
    accumulate_covering(Covered0,Covered1,Covered),
    accumulate_nonfailure(Fails0,Fails1,Fails),
    accumulate_unfold_tests(Unfold0,Unfold1,Unfold),
    % Only the tests of non-failing clauses are accumulated, i.e.,
    % only such tests will be added to the disjunction for the
    % covering check.
    ( Fails1 == not_fails ->
        tests_union(Tests1,Tests0,Tests)
    ; Tests = Tests0 
    ),
    asub(NewASub,Tests,Unfold,Covered,Fails).

tests_union(Tests,Tests0,Tests1) :- ( Tests = [_|_] ; Tests = [] ), !,
    tests_union_(Tests,Tests0,Tests1).
tests_union(Tests,Tests0,[Tests|Tests0]).

tests_union_([],Tests,Tests).
tests_union_([T|Ts],Tests0,Tests1) :- memberchk(T,Tests0), !,
    tests_union_(Ts,Tests0,Tests1).
tests_union_([T|Ts],Tests0,[T|Tests1]) :-
    tests_union_(Ts,Tests0,Tests1).

accumulate_covering(covered,_,covered):- !.
accumulate_covering(_,covered,covered):- !.
accumulate_covering(A,B,C):- lub_covering(A,B,C).

accumulate_nonfailure(not_fails,_,not_fails):- !.
accumulate_nonfailure(_,not_fails,not_fails):- !.
accumulate_nonfailure(A,B,C):- lub_nonfailure(A,B,C).

accumulate_unfold_tests('$bottom',X,X):-!.
accumulate_unfold_tests(_,_,not_unfold).

lub_covering(A,B,C) :-
    ( le_covering(A,B) ->
        C = B
    ; le_covering(B,A) ->
        C = A
    ; C = possibly_not_covered
    ).

lub_nonfailure(A,B,C) :-
    ( le_nonfailure(A,B) ->
        C = B
    ; le_nonfailure(B,A) ->
        C = A
    ; C = possibly_fails
    ).

lub_unfold_tests(A,B,C) :-
    ( le_unfold_tests(A,B) ->
        C = B
    ; le_unfold_tests(B,A) ->
        C = A
    ; C = not_unfold
    ).
    
%------------------------------------------------------------------------%
% nf_compute_covering(+,+,-)                                             %
% nf_compute_covering(ModeTypes,Lub,ASub)                                %
%------------------------------------------------------------------------%
% New operation, has to be called from fixpoint when all clauses of a 
% predicate have been traversed: compute covering information

:- pred nf_compute_covering(ModeTypes,CAsub,ASub)
   :  ( mode_types(ModeTypes), nfabs_pred_asub(CAsub), var(ASub) )
   => ( mode_types(ModeTypes), nfabs_pred_asub(CAsub), nfabs_pred_asub(ASub) )

   # "@var{ASub} represents covering and failure information resulting
     from performing the covering check over @var{CAsub}. ".

nf_compute_covering(ModeTypes,Lub,ASub):-
    % this one is a little tricky: Lub is not a well-formed abstract
    % substitution, it is a collection of tests from compute_lub
    asub(Lub,TestsList,Unfold,_Covered,Fails0),
    ( TestsList = [] -> CoverTest = false %% ???? PLG
    ; TestsList = [[]] -> CoverTest = true %% ???? PLG
    ; TestsList = [_|_] -> 
        test_list_to_cover_test(TestsList, [], CoverTest)
        % if only one asub, lub is not computed, thus, it is not a list:
    ; test_list_to_cover_test([TestsList], [], CoverTest)
    ),
    covers_check(ModeTypes,false,_Masc,CoverTest,Res),
    result_to_covering(Res,Covered),
    covering_to_nonfailure(Covered,Fails1),
    % Fails0 should always be not_fails!
    extend_nonfailure(Fails0,Fails1,Fails),
    asub(ASub,TestsList,Unfold,Covered,Fails).

% covers_check_(ModeTypes,false,_Masc,MinSetTestsList,Res):-
%       covers_check(ModeTypes,false,_Masc,MinSetTestsList,Res), !.
% covers_check_(_ModeTypes,false,_Masc,_MinSetTestsList,true).

result_to_covering(true,covered).
result_to_covering(fail,possibly_not_covered).
result_to_covering(false,possibly_not_covered).

covering_to_nonfailure(covered,not_fails).
covering_to_nonfailure(possibly_not_covered,possibly_fails).

%% Added by PLG.

test_list_to_cover_test([], InTest, InTest):-
    !.
test_list_to_cover_test([T|TList], InTest, OuTest):-
    clause_test_to_minset_test(T, Clause_Test),
    ( Clause_Test == true ->
        OuTest = true
    ; ( Clause_Test == false ->
        TemTest = InTest
      ; TemTest = [Clause_Test|InTest]
      ),
      test_list_to_cover_test(TList, TemTest, OuTest)
    ).

clause_test_to_minset_test(Clause_Test, Clause_Minset_Test):-
    tests(Clause_Test,Var_list,Unification_Tests,Arithm_Tests,_Meta_Tests),
    ( Arithm_Tests == [],
      Unification_Tests == [] -> 
        Clause_Minset_Test = true
    ; ( Arithm_Tests == [] ->
          Others = true
      ; Others = Arithm_Tests
      ),
      create_minset_and_project(Var_list, Unification_Tests, Others, Clause_Minset_Test)
    ).

% End added by PLG

    
%------------------------------------------------------------------------%
% nf_glb(+,+,-)                                                          %
% nf_glb(ASub0,ASub1,Glb)                                                %
%------------------------------------------------------------------------%

nf_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
nf_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
nf_glb(ASub0,ASub1,Glb):-
    asub(ASub0,_Tests0,Unfold0,Covered0,Fails0),
    asub(ASub1,Tests1,Unfold1,Covered1,Fails1),
    % VP: Changed merge_tests/3 to preserve tests of single clause preds.
    %% merge_tests(Tests0,Tests1,Tests),
    Tests = Tests1,
    glb_unfold_tests(Unfold0,Unfold1,Unfold),
    glb_covering(Covered0,Covered1,Covered),
    glb_nonfailure(Fails0,Fails1,Fails),
    asub(Glb,Tests,Unfold,Covered,Fails).

glb_covering(A,B,C) :-
    ( le_covering(A,B) ->
        C = A
    ; le_covering(B,A) ->
        C = B
    ; C = '$bottom'
    ).

glb_nonfailure(A,B,C) :-
    ( le_nonfailure(A,B) ->
        C = A
    ; le_nonfailure(B,A) ->
        C = B
    ; C = '$bottom'
    ).

glb_unfold_tests(A,B,C) :-
    ( le_unfold_tests(A,B) ->
        C = A
    ; le_unfold_tests(B,A) ->
        C = B
    ; C = '$bottom'
    ).

%------------------------------------------------------------------------%
% nf_less_or_equal(+,+)                                                  %
% nf_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%

nf_less_or_equal(ASub0,ASub1):-
    asub(ASub0,_Tests0,Unfold0,Covered0,Fails0),
    asub(ASub1,_Tests1,Unfold1,Covered1,Fails1),
    le_covering(Covered0,Covered1),
    le_nonfailure(Fails0,Fails1),
    le_unfold_tests(Unfold0,Unfold1).

le_covering(A,A):- !.
le_covering('$bottom',_).
le_covering(_,possibly_not_covered).

le_nonfailure(A,A):- !.
le_nonfailure('$bottom',_).
le_nonfailure(_,possibly_fails).

le_unfold_tests(A,A):- !.
le_unfold_tests('$bottom',_):-!.
le_unfold_tests(_,not_unfold).
    
%------------------------------------------------------------------------%
% nf_identical_abstract(+,+)                                             %
% nf_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%

nf_identical_abstract(ASub0,ASub1):-
     asub(ASub0,_Tests0,Unfold,Covered,Fails),
     asub(ASub1,_Tests1,Unfold,Covered,Fails).

%------------------------------------------------------------------------%
% nf_abs_sort(+,-)                                                           %
% nf_abs_sort(ASub0,ASub1)                                                   %
%------------------------------------------------------------------------%

nf_abs_sort(ASub,ASub).

%------------------------------------------------------------------------%
% nf_call_to_success_fact(+,+,+,+,+,+,+,-,-)                             %
% nf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)          %
%-------------------------------------------------------------------------

nf_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,Call,Proj,Prime,Succ):-
    Succ = Call,
    Prime = Proj.

%-------------------------------------------------------------------------
% nf_special_builtin(+)                                                  |
% nf_special_builtin(SgKey)                                              |
%-------------------------------------------------------------------------

nf_special_builtin(SgKey):-
   nf_builtin(SgKey, _Sg, _CallType, _BType, _BSg, _CovNF).                          

% WARNING: use '\\==/2' instead of '\==/2', in the predicate
% nf_builtin/6, i.e. quote the character "\".

nf_builtin('=/2'   , Sg, CallType, Type, Sg, CovNf):- !,
    ( possibly_fails_unif(CallType, Sg) ->
        nf_builtin_trust(CovNf, possibly_not_covered, possibly_fails),
        Type = notest
    ; Type = unif
    ).
nf_builtin('==/2'  , Sg, _CallType, unif, Sg, _CovNf):-!.
nf_builtin('\\==/2' , Sg, _CallType, unif, Sg, _CovNf):-!.
nf_builtin('\\=/2' , Sg, _CallType, unif, Sg, _CovNf):-!.
% 
nf_builtin('is/2', X is E, CallType, notest, X is E, CovNf):-
     is_free_var(X, CallType),
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
nf_builtin('is/2', X is E, _CallType, arit, =:=(X, E), _CovNf):-!.
% Arithmetic tests
nf_builtin('=:=/2', Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('=\\=/2', Sg, _CallType, arit, Sg, _CovNf):-!.
nf_builtin('</2',   Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('>/2',   Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('=</2',  Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('>=/2',  Sg, _CallType, arit, Sg, _CovNf):-!.
% For Sicstus
nf_builtin('number/1',  Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('integer/1', Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('atom/1',    Sg, _CallType, arit, Sg, _CovNf):-!. 
% For CIAO
nf_builtin('num/1',     Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('int/1',     Sg, _CallType, arit, Sg, _CovNf):-!. 
nf_builtin('atm/1',     Sg, _CallType, arit, Sg, _CovNf):-!. 
% Meta-tests
nf_builtin('var/1',     Sg, _CallType, meta, Sg, _CovNf):-!. 
% For Sicstus
nf_builtin('ground/1',  Sg, _CallType, meta, Sg, _CovNf):-!. 
nf_builtin('float/1',   Sg, _CallType, meta, Sg, _CovNf):-!. 
nf_builtin('ground/1',  Sg, _CallType, meta, Sg, _CovNf):-!. 
nf_builtin('atomic/1',  Sg, _CallType, meta, Sg, _CovNf):-!. 
% For CIAO
nf_builtin('gnd/1',     Sg, _CallType, meta, Sg, _CovNf):-!. 
nf_builtin('flt/1',     Sg, _CallType, meta, Sg, _CovNf):-!. 
% Sometimes may act as tests and sometimes succeed. 
nf_builtin('get_code/1', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
nf_builtin('get_code/1', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
nf_builtin('current_op/3', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
nf_builtin('functor/3', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
nf_builtin('findall/3', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
nf_builtin('arg/3', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, covered, not_fails).
% No tests that always succeeds.
nf_builtin('true/0',    Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('nl/0',      Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('ttynl/0',   Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('ttyput/1',  Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('write/1',   Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('tab/1',     Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('writeq/1',  Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('display/1', Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('print/1',   Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('check/1',   Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('!/0',   Sg, _CallType, id, Sg, _CovNf):-!.
nf_builtin('\\+/1', Sg, _CallType, negation, Sg, _CovNf):-!.
nf_builtin('fail/0', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, possibly_not_covered, possibly_fails).
nf_builtin('false/0', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, possibly_not_covered, possibly_fails).
nf_builtin('indep/1', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, possibly_not_covered, possibly_fails).
nf_builtin('indep/2', Sg, _CallType, notest, Sg, CovNf):- 
     !, 
     nf_builtin_trust(CovNf, possibly_not_covered, possibly_fails).

% TODO: This should be an shfr domain operation.
is_free_var(X, CallType):-
     nonvar(CallType),
     shfr_obtain_info(free,[X],CallType,[Y]),
     X == Y.

% TODO: This should be an shfr domain operation.
possibly_fails_unif(CallType, X=Y) :-
    nonvar(CallType),
    \+ is_indep_var(X, CallType),
    \+ is_indep_var(Y, CallType),
    varset(X=Y, Vars),
    CallType = (Sharing,_),
    ( member(Var, Vars), shares(Sharing, Var) ->
        true
    ; fail
    ).

% TODO: This should be an shfr domain operation.
is_indep_var(X, CallType) :-
    is_free_var(X, CallType),
    CallType = (Sharing,_),
    \+ shares(Sharing, X).

% TODO: This should be an shfr domain operation.
shares(Sets, Var) :-
    ( member(Set, Sets), shares_(Var, Set) ->
        true
    ; fail
    ).

shares_(Var, Set) :-
    Set = [_,_|_],
    memberchk(Var, Set).

possibly_fail_unif_tests(ENonF, CallTypes) :-
    asub(ENonF,Tests,_,_,_),
    tests(Tests,_,Unif,_,_),
    ( member(U, Unif), possibly_fails_unif(CallTypes, U) ->
        true
    ; fail
    ).

%-------------------------------------------------------------------------
% nf_success_builtin(+,+,+,+,+,-)                                        |
% nf_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                          |
%-------------------------------------------------------------------------
% Accumulates the tests:

nf_success_builtin(SgKey, CallType,Sg,_HvFv_u,Call,Succ):-
   nf_builtin(SgKey,Sg,CallType,BType,BSg,CovNF),
   nf_success_builtin_(BType,CallType,CovNF,BSg,Call,Succ).
     
nf_success_builtin_(id, _CallType, _CovNF, _BSg, Call, Succ):-  
    % For efficiency (builtins that do not fail).
    !, 
    Succ=Call.
nf_success_builtin_(notest, _CallType, CovNF, _BSg, Call, Succ):-
    !,
    builtin_trust_to_succ(CovNF,Call,Succ).
nf_success_builtin_(negation, CallType, _CovNF, BSg, Call, Succ):-
    remove_negation(BSg, NSg),
    predkey_from_sg(NSg, NSgkey),
    nf_builtin(NSgkey, NSg, CallType, BType, _S, _C),
    ( is_a_test(BType) ->
        push_neg_in_test(BSg, NBSg), 
        nf_success_test(BType, NBSg, Call, Succ)
    ; nf_success_negation(Call, Succ)
    ).
nf_success_builtin_(BType, _CallType, _CovNF, BSg, Call, Succ):-
    is_a_test(BType),
    translate_test(BSg, NewBSg),
    nf_success_test(BType, NewBSg, Call, Succ).

nf_success_test(BType, BSg, Call, Succ):-
    asub(Call,Tests0,Unfold,Covered,Fails),
    tests(Tests0,InVars0,Unif0,Arith0,Meta0),
    add_test(BType,BSg,Unif0,Arith0,Meta0,Unif,Arith,Meta),
    tests(Tests,InVars0,Unif,Arith,Meta),
    asub(Succ,Tests,Unfold,Covered,Fails).
    
nf_success_negation(Call, Succ):-
    asub(Call,Tests,_Unfold,Covered,_Fails),
    asub(Succ,Tests,not_unfold,Covered,possibly_fails).

add_test(unif,Sg,Unif,Arith,Meta,[Sg|Unif],Arith,Meta).
add_test(arit,Sg,Unif,Arith,Meta,Unif,[Sg|Arith],Meta).
add_test(meta,Sg,Unif,Arith,Meta,Unif,Arith,[Sg|Meta]).

is_a_test(Btype):- Btype == unif.
is_a_test(Btype):- Btype == arit.
is_a_test(Btype):- Btype == meta.

builtin_trust_to_succ(CovNF,Call,Succ):-
    asub(Call,Tests,_Unfold,Covered1,Fails1),
    nf_builtin_trust(CovNF, Covered0, Fails0),   
    extend_covering(Covered0,Covered1,Covered),
    extend_nonfailure(Fails0,Fails1,Fails),
    asub(Succ,Tests,not_unfold,Covered,Fails).
 
nf_builtin_trust((Covered, Fails), Covered, Fails).   

%-------------------------------------------------------------------------
% nf_call_to_success_builtin(+,+,+,+,+,-)                                %
% nf_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)                 %
%-------------------------------------------------------------------------
% Not used

%------------------------------------------------------------------------%
% nf_input_interface(+,+,+,-)                                            %
% nf_input_interface(InputUser,Kind,StructI,StructO)                     %
%------------------------------------------------------------------------%
% Something more intelligent should be done with the argument of the props
% than simply ignore them!!!

% TODO: legacy, see old_nfdet
nf_input_interface(not_fails(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[not_fails],Fail1).
nf_input_interface(fails(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[fails],Fail1).
nf_input_interface(possibly_fails(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[possibly_fails],Fail1).
%
nf_input_interface(det(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[not_fails],Fail1).
nf_input_interface(nondet(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[possibly_fails],Fail1).
nf_input_interface(semidet(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[possibly_fails],Fail1).
nf_input_interface(multi(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[not_fails],Fail1).
nf_input_interface(covered(_),perfect,(Cov0,Fail),(Cov1,Fail)):-
    myappend(Cov0,[covered],Cov1).
nf_input_interface(not_covered(_),perfect,(Cov0,Fail),(Cov1,Fail)):-
    myappend(Cov0,[not_covered],Cov1).
nf_input_interface(possibly_not_covered(_),perfect,(Cov0,Fail),(Cov1,Fail)):-
    myappend(Cov0,[possibly_not_covered],Cov1).

myappend(Vs,V0,V):-
    var(Vs), !,
    V=V0.
myappend(Vs,V0,V):-
    merge(Vs,V0,V).

may_be_var(X,X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------%
% nf_input_user_interface(+,+,-,+,+)                                     %
% nf_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)            %
%------------------------------------------------------------------------%

nf_input_user_interface((Cov0,Fail0),Qv,ASub,_Sg,_MaybeCallASub):-
    may_be_var(Cov0,Cov1),
    may_be_var(Fail0,Fail1),
    foldr(glb_covering, Cov1, possibly_not_covered, Covered),
    foldr(glb_nonfailure, Fail1, possibly_fails, Fails),
    nf_empty_entry(sg_not_provided,Qv,Entry),
    asub(Entry,Tests,_Unfold,_Covered,_Fails),
    asub(ASub,Tests,not_unfold,Covered,Fails).

%------------------------------------------------------------------------%
% nf_asub_to_native(+,+,-)                                               %
% nf_asub_to_native(ASub,Qv,ASub_user)                                   %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!
% something has to be done to put the props in the comp part, not the success
% part of the assertion!!!

nf_asub_to_native(ASub,Qv,[PropF,PropC]):-
    asub(ASub,_Tests,_Unfold,Covered,Fails),
    \+ represents_failure(Fails),
    functor(PropF,Fails,1),
    ( Covered = '$bottom' ->
        Covered0 = not_covered
    ; Covered = Covered0
    ),
    functor(PropC,Covered0,1),
    arg(1,PropF,Qv),
    arg(1,PropC,Qv).

represents_failure('$bottom').
represents_failure(fails).

%------------------------------------------------------------------------%
% nf_unknown_call(+,+,+,-)                                               %
% nf_unknown_call(Sg,Vars,Call,Succ)                                     %
%------------------------------------------------------------------------%

nf_unknown_call(_Sg,_Vars,Call,Succ):-
    asub(Call,Tests,_,_,_),
    asub(Succ,Tests,not_unfold,possibly_not_covered,possibly_fails).

%------------------------------------------------------------------------%
% nf_unknown_entry(+,+,-)                                                %
% nf_unknown_entry(Sg,Vars,Entry)                                        %
%------------------------------------------------------------------------%

nf_unknown_entry(Sg,Vars,Entry):-
    nf_empty_entry(Sg,Vars,Entry).

%------------------------------------------------------------------------%
% nf_empty_entry(+,+,-)                                                  %
% nf_empty_entry(Sg,Vars,Entry)                                          %
%------------------------------------------------------------------------%

nf_empty_entry(_Sg,Vars,Entry):-
    tests(Tests,Vars,[],[],[]),
    asub(Entry,Tests,unfold,covered,not_fails).

%-----------------------------------------------------------------------

nfabs_dom_statistics([nfstatistics([total_preds(Total),
                                    preds_not_fail(NF_Preds),
                                    preds_covered(Cov_Preds),
                                    preds_some_variant_not_fail(NF_Variants),
                                    preds_some_variant_covered(Cov_Variants)])]):-
    nfdet_statistics(nf, _S, Total, NF_Preds, Cov_Preds, NF_Variants, Cov_Variants).
