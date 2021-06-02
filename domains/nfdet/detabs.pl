:- module(detabs, [
    det_call_to_entry/10,
    det_exit_to_prime/7,
    det_project/5,
    det_extend/5,
    det_compute_lub/2,
    det_compute_mut_exclusion/3,
    det_glb/3,
    det_less_or_equal/2,
    det_identical_abstract/2,
    det_abs_sort/2,
    det_call_to_success_fact/9,
    det_special_builtin/1,
    det_success_builtin/6,
    % det_call_to_success_builtin/6,
    det_input_interface/4, det_input_user_interface/5,
    det_asub_to_native/3,
    det_unknown_call/4,
    det_unknown_entry/3,
    det_empty_entry/3,
    detabs_dom_statistics/1
], [assertions,regtypes,basicmodes,hiord]).

:- use_module(domain(nfdet/nfsets), [create_minset_and_project/4]).
:- use_module(domain(nfdet/mutexcheck), [mutual_exclusion_check/5]).
:- use_module(domain(nfdet/nfbool), [push_neg_in_test/2, remove_negation/2, translate_test/2]).
:- use_module(domain(sharefree), [shfr_obtain_info/4]).
:- use_module(domain(s_eqs), [peel/4]).
:- use_module(domain(nfdet/nfdet_statistics)).
:- use_module(domain(nfdet/nfdetabs), [pred_test/1, tests/5]).
:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(hiordlib), [foldr/4]).
:- use_module(library(sets), [merge/3]).

:- doc(title,"Determinism Abstract Domain").
:- doc(module,"

This module implements the abstract operations of a determinism domain
for the PLAI framework of abstract interpretation. Abstract
substitutions for this domain are a pair of (MutExclusive,Det)
elements, where MutExclusive is @tt{possibly_not_mut_exclusive},
@tt{not_mut_exclusive} or @tt{mut_exclusive}; and Det is
@tt{possibly_nondet}, @tt{non_det} or @tt{det}. Note that the lattice
for mutual exclusion is analogous to the lattice of determinism, but
applied to guard tests.

The abstract domain lattices for determinism and mutual exclusion are:

@begin{verbatim}

   possibly_not_mut_exclusive       possibly_nondet
            /     \\                     /   \\
           /       \\                   /     \\
not_mut_exclusive  mut_exclusive   non_det   det
           \\       /                   \\     /
            \\     /                     \\   /
            $bottom                    $bottom

@end{verbatim}

").

%------------------------------------------------------------------------%

:- doc(bug,"Think on an adequate treatment for negation.").

%------------------------------------------------------------------------%

:- export(detabs_asub/1).

:- doc(detabs_asub(ASub), "@var{ASub} is an abstract substitution term
   used in det.").

:- regtype detabs_asub(ASub)
   # "@var{ASub} is an abstract substitution term used in det.".

detabs_asub(ASub):- detabs_par_asub(clause_test,ASub).

:- doc(detabs_par_asub(TestTyp,ASub), "@var{ASub} is an abstract
   substitution term used in det with tests of type @var{TestTyp}.").

:- regtype detabs_par_asub(TestTyp,ASub)
   # "@var{ASub} is an abstract substitution term used in det with
     tests of type @var{TestTyp}.".

detabs_par_asub(_, '$bottom').
detabs_par_asub(TestTyp, det(Tests,MutEx,Det)) :-
    TestTyp(Tests),    
    mutexclusion_t(MutEx),
    determinism_t(Det).

:- regtype detabs_pred_asub(ASub)
   # "@var{ASub} is a compact representation for a set of abstract
     substitutions corresponding to the clauses of a predicate. It
     gathers together the clause tests of those abstract substitutions
     as a list, meaning the disjunction of all of them (named the
     @tt{predicate test}, which is needed for performing the
     @tt{mutual exclusion check}).  If the list of tests is empty, it
     represents an empty set of abstract substitutions.".

detabs_pred_asub(ASub):- detabs_par_asub(pred_test,ASub).

:- regtype mutexclusion_t(Mutex)
   # "@var{Mutex} represents whether the clause tests of a predicate
     are pairwise mutually exclusive.".

mutexclusion_t(possibly_not_mut_exclusive).
mutexclusion_t(mut_exclusive).
mutexclusion_t(not_mut_exclusive).
mutexclusion_t('$bottom').

:- regtype determinism_t(Det)
   # "@var{Det} represents determinism information (for call patterns).
@begin{itemize}
@item @tt{is_det}: succeeds at most once or does not terminate. 
@item @tt{non_det}: succeeds at least twice or does not terminate. 
@item @tt{possibly_nondet}: succeeds any times or does not terminate. 
@item @tt{'$bottom'}: unreachable. 
@end{itemize}
".

determinism_t(is_det). 
determinism_t(possibly_nondet).
determinism_t(non_det).
determinism_t('$bottom').

:- export(get_tests/2).

:- doc(get_tests(ASub,Tests), "Returns in @var{Tests} the tests in
   abstract substitution @var{ASub}.").

:- pred get_tests(ASub,Tests)
   : ( detabs_asub(ASub), var(Tests) )
   => ( detabs_asub(ASub), pred_test(Tests) )
   # "@var{Tests} are the tests in abstract substitution @var{ASub}.".

get_tests(ASub,Tests) :-
       asub(ASub,Tests,_,_,_).

:- export(asub_is_det/1).

:- doc(asub_is_det(ASub), "Succeeds if and only if abstract
   substitution @var{ASub} represents that the corresponding call
   pattern succeeds at most once or does not terminate.").

:- pred asub_is_det(ASub)
   : detabs_asub(ASub)
   => detabs_asub(ASub)
   # "Succeeds if and only if abstract substitution @var{ASub}
   represents that the corresponding call pattern succeeds at most
   once or does not terminate.".

asub_is_det(ASub) :-
    asub(ASub,_,_,_,is_det).

asub(det(Tests,Unfold_Tests,MutExclusive,Det),Tests,Unfold_Tests,MutExclusive,Det).

%------------------------------------------------------------------------%
% det_call_to_entry(+,+,+,+,+,+,+,-,-)                                   %
% det_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)             %
%------------------------------------------------------------------------%
% Entering a clause: initialize an asub to start gathering the tests of
% this clause 

det_call_to_entry(_Sv,Sg,Hv,Head,_K,_Fv,_Proj,InVars,Entry,_Extra):-
    det_empty_entry(Sg,Hv,Entry0),
    asub(Entry0,_Tests,Unfold,MutEx,Det),
    asub(Entry,Tests,Unfold,MutEx,Det),
    peel(Sg,Head,Bindings,[]),
    tests(Tests,InVars,Bindings,[],[]).

%------------------------------------------------------------------------%
% det_exit_to_prime(+,+,+,+,+,-,-)                                       %
% det_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                  %
%------------------------------------------------------------------------%
% Exiting a clause: project the tests gathered while traversing the clause 
% onto the variables of the goal

det_exit_to_prime(Sg,_Hv,Head,_Sv,Exit,GVars,Prime):-
    asub(Exit,Tests,Unfold,MutExclusive,Det),
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
    asub(Prime,PrimeTests,Unfold,MutExclusive,Det).
det_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_Extra,'$bottom').

%% new_tests([],[],[]).
%% new_tests([X|Xs],[Y|Ys],[X=Y|Eqs]):-
%%      new_tests(Xs,Ys,Eqs).

%------------------------------------------------------------------------%
% det_project(+,+,+,+,-)                                                 %
% det_project(Sg,Vars,HvFv_u,ASub,Proj)                                  %
%------------------------------------------------------------------------%
% To project on Vars, leave only tests for Vars

det_project(_Sg,Vars,_HvFv_u,ASub,Proj):-
    asub(ASub,Tests0,Unfold,MutExclusive,Det),
    select_tests(Tests0,Vars,TestsProj),
    asub(Proj,TestsProj,Unfold,MutExclusive,Det).

select_tests(Tests,_Vars,Tests).

%------------------------------------------------------------------------%
% det_extend(+,+,+,+,-)                                                  %
% det_extend(Sg,Prime,Sv,Call,Succ)                                      %
%------------------------------------------------------------------------%
% Return back to the calling clause: merge the tests in Call with the
% tests in Prime

det_extend(_Sg,Prime,_Sv,Call,Succ):-
    asub(Prime,Tests0,Unfold0,MutExclusive0,Det0),
    asub(Call,Tests1,Unfold1,_MutExclusive1,Det1),
    ( Unfold0 == unfold, Tests0 = t(_,_,_,_) ->
        unfold_tests(Tests0,Tests1,Tests),
        extend_unfold_tests(Unfold0,Unfold1,Unfold)
    ; Unfold = not_unfold,
      Tests = Tests1
    ),
    extend_determinism(Det0,Det1,Det),
    asub(Succ,Tests,Unfold,MutExclusive0,Det).

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

extend_mut_exclusion('$bottom',_,'$bottom'):-!.
extend_mut_exclusion(_,'$bottom','$bottom'):-!.
extend_mut_exclusion(not_mut_exclusive,_,not_mut_exclusive):-!.
extend_mut_exclusion(_,not_mut_exclusive,not_mut_exclusive):-!.
extend_mut_exclusion(possibly_not_mut_exclusive,_,possibly_not_mut_exclusive):-!.
extend_mut_exclusion(_,possibly_not_mut_exclusive,possibly_not_mut_exclusive):-!.
extend_mut_exclusion(_,_,mut_exclusive).

extend_determinism('$bottom',_,'$bottom'):-!.
extend_determinism(_,'$bottom','$bottom'):-!.
extend_determinism(non_det,_,non_det):-!.
extend_determinism(_,non_det,non_det):-!.
extend_determinism(possibly_nondet,_,possibly_nondet):-!.
extend_determinism(_,possibly_nondet,possibly_nondet):-!.
extend_determinism(_,_,is_det).

extend_unfold_tests(not_unfold, _, not_unfold):-!.
extend_unfold_tests(_, not_unfold, not_unfold):-!.
extend_unfold_tests(_,_, unfold).

%------------------------------------------------------------------------%
% det_widen(+,+,-)                                                       %
% det_widen(Prime0,Prime1,NewPrime)                                      %
%------------------------------------------------------------------------%

det_widen(Prime0,Prime1,NewPrime) :-
    asub(ASub,[],unfold,mut_exclusive,det),
    foldr(widen,[Prime0,Prime1],ASub,NewPrime).

widen('$bottom',ASub0,ASub0):- !.
widen(ASub0,'$bottom',ASub0):- !.
widen(ASub,ASub0,NewASub):-
    asub(ASub0,Tests0,Unfold0,MutEx0,Det0),
    asub(ASub,Tests1,Unfold1,MutEx1,Det1),
    tests_union(Tests1,Tests0,Tests), % Tests=[Tests1|Tests0],
    ( Det0 = det ->
        lub_mut_exclusion(MutEx0,MutEx1,MutEx),
        lub_determinism(Det0,Det1,Det),
        lub_unfold_tests(Unfold0,Unfold1,Unfold)
    ; extend_mut_exclusion(MutEx0,MutEx1,MutEx),
      extend_determinism(Det0,Det1,Det),
      extend_unfold_tests(Unfold0,Unfold1,Unfold)
    ),
    asub(NewASub,Tests,Unfold,MutEx,Det).

%------------------------------------------------------------------------%
% det_compute_lub(+,-)                                                   %
% det_compute_lub(ListASub,Lub)                                          %
%------------------------------------------------------------------------%
% Simply put all tests together (this is due to the way this operation
% is called from the fixpoint)

det_compute_lub(ListASub,Lub):-
    asub(ASub,[],'$bottom','$bottom','$bottom'),
    foldr(accumulate, ListASub, ASub, Lub).

% Differs from nf
accumulate('$bottom',ASub0,ASub0):- !.
accumulate(ASub0,'$bottom',ASub0):- !.
accumulate(ASub,ASub0,NewASub):-
    asub(ASub0,Tests0,Unfold0,MutExclusive0,Det0),
    asub(ASub,Tests1,Unfold1,MutExclusive1,Det1),
    accumulate_mut_exclusion(MutExclusive0,MutExclusive1,MutExclusive),
    accumulate_determinism(Det0,Det1,Det),
    accumulate_unfold_tests(Unfold0,Unfold1,Unfold),
    tests_union(Tests1,Tests0,Tests),
    asub(NewASub,Tests,Unfold,MutExclusive,Det).

tests_union(Tests,Tests0,Tests1):-
    Tests=[_|_], !,
    tests_union_(Tests,Tests0,Tests1).
tests_union(Tests,Tests0,[Tests|Tests0]).

tests_union_([],Tests,Tests).
tests_union_([T|Ts],Tests0,Tests1) :- memberchk(T,Tests0), !,
    tests_union_(Ts,Tests0,Tests1).
tests_union_([T|Ts],Tests0,[T|Tests1]) :-
    tests_union_(Ts,Tests0,Tests1).

accumulate_mut_exclusion(mut_exclusive,_,mut_exclusive):- !.
accumulate_mut_exclusion(_,mut_exclusive,mut_exclusive):- !.
accumulate_mut_exclusion(A,B,C):- lub_mut_exclusion(A,B,C).

accumulate_determinism(det,_,det):- !.
accumulate_determinism(_,det,det):- !.
accumulate_determinism(A,B,C):- lub_determinism(A,B,C).

accumulate_unfold_tests('$bottom',X,X):-!.
accumulate_unfold_tests(_,_,not_unfold).

lub_mut_exclusion(A,B,C) :-
    ( le_mut_exclusion(A,B) ->
        C = B
    ; le_mut_exclusion(B,A) ->
        C = A
    ; C = possibly_not_mut_exclusive
    ).

lub_determinism(A,B,C) :-
    ( le_determinism(A,B) ->
        C = B
    ; le_determinism(B,A) ->
        C = A
    ; C = possibly_nondet
    ).

lub_unfold_tests(A,B,C) :-
    ( le_unfold_tests(A,B) ->
        C = B
    ; le_unfold_tests(B,A) ->
        C = A
    ; C = not_unfold
    ).

%------------------------------------------------------------------------%
% det_compute_mut_exclusion(+,+,-)                                       %
% det_compute_mut_exclusion(ModeTypes,Lub,ASub)                          %
%------------------------------------------------------------------------%
% New operation, has to be called from fixpoint when all clauses of a 
% predicate have been traversed: compute mutual exclusion information

det_compute_mut_exclusion(ModeTypes,Lub,ASub):-
    % this one is a little tricky: Lub is not a well-formed abstract
    % substitution, it is a collection of tests from compute_lub
    asub(Lub,TestsList,Unfold,_MutExclusive,Det0),
    % if only one asub, it is always mutually exclusive:
    ( TestsList = t(_,_,_,_) ->
        MutExclusive = mut_exclusive
    ; ( TestsList = [] -> MutualExclusionTest = true  %% ???? PLG Differs from nf.
      ; TestsList = [[]] -> MutualExclusionTest = true  %% ???? PLG
      ; test_list_to_mutual_exclusion_test(TestsList, [], MutualExclusionTest)
      ),
      mutual_exclusion_check(ModeTypes,false,_Masc,MutualExclusionTest,Res),
      result_to_mut_exclusion(Res,MutExclusive)
    ),
    mut_exclusion_to_determinism(MutExclusive,Det1),
    % Det0 should always be is_det!
    extend_determinism(Det0,Det1,Det),
    foldr_testlist(TestsList,Tests),
    asub(ASub,Tests,Unfold,MutExclusive,Det).


result_to_mut_exclusion(true,mut_exclusive).
result_to_mut_exclusion(fail,possibly_not_mut_exclusive).
result_to_mut_exclusion(false,possibly_not_mut_exclusive).

mut_exclusion_to_determinism(mut_exclusive,is_det).
mut_exclusion_to_determinism(possibly_not_mut_exclusive,possibly_nondet).

foldr_testlist(_TestsList,Tests):-
    det_empty_entry(sg_not_provided,[],Entry),
    asub(Entry,Tests,_Unfold,_MutExclusive,_Det).

% Differs from nf

test_list_to_mutual_exclusion_test([], InTest, InTest):-
    !.
test_list_to_mutual_exclusion_test([T|TList], InTest, OuTest):-
    ( has_a_cut(T) -> 
        test_list_to_mutual_exclusion_test(TList, InTest, OuTest)
    ; clause_test_to_minset_test(T, Clause_Test),
      ( Clause_Test == true ->
          OuTest = true
      ; ( Clause_Test == false ->
            TemTest = InTest
        ; TemTest = [Clause_Test|InTest]
        ),
        test_list_to_mutual_exclusion_test(TList, TemTest, OuTest)
      )
    ).

% has_a_cut(t(_InVars,_Unif,_Arith,Meta)):- member(cut, Meta). 
has_a_cut(t(_InVars,_Unif,_Arith,Meta)):- member((!), Meta). 

%% test_list_to_mutual_exclusion_test([], InTest, InTest):-
%%     !.
%% test_list_to_mutual_exclusion_test([T|TList], InTest, OuTest):-
%%     ( has_a_cut(T) -> 
%%           TemTest = InTest
%%     ; 
%%           clause_test_to_minset_test(T, Clause_Test),
%%           TemTest = [Clause_Test|InTest]
%%     ),
%%     test_list_to_mutual_exclusion_test(TList, TemTest, OuTest).
%% 
%%                     !. 
%% has_a_cut([_H|T]):- has_a_cut(T). 
%% 
%% is_a_cut(_H):- fail.
%% % is_a_cut(H):- functor(H, (!), 0).

%

clause_test_to_minset_test(Clause_Test, Clause_Minset_Test):-
    tests(Clause_Test, Var_list, Unification_Tests, Arithm_Tests, Meta_Tests),
    ( Arithm_Tests == [],
      Unification_Tests == [],
      Meta_Tests == [] -> 
        Clause_Minset_Test = true
    ; clause_test_to_minset_test_(Var_list,Unification_Tests,Arithm_Tests,Meta_Tests,Clause_Minset_Test)
    ).

clause_test_to_minset_test_(Var_list,Unification_Tests,Arithm_Tests,Meta_Tests,Clause_Minset_Test):-
   append(Arithm_Tests, Meta_Tests, Other_Tests),
   ( Other_Tests == [] -> 
       Others = true
   ; Others = others(Arithm_Tests, Meta_Tests) 
   ),
   create_minset_and_project(Var_list, Unification_Tests, Others, Clause_Minset_Test).
       
%% clause_test_to_minset_test(Clause_Test, Clause_Minset_Test):-
%%     tests(Clause_Test,Var_list,Unification_Tests,Arithm_Tests,_Meta_Tests),
%%     ( Arithm_Tests == [], Unification_Tests == [] -> 
%%       Clause_Minset_Test = true
%%     ; ( Arithm_Tests == [] -> Others = true; Others = Arithm_Tests ),
%%       create_minset_and_project(Var_list, Unification_Tests, Others, 
%%                                 Clause_Minset_Test)
%%     ).

% End added by PLG

%------------------------------------------------------------------------%
% det_glb(+,+,-)                                                         %
% det_glb(ASub0,ASub1,Glb)                                               %
%------------------------------------------------------------------------%

det_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
det_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
det_glb(ASub0,ASub1,Glb):-
    asub(ASub0,_Tests0,Unfold0,MutExclusive0,Det0),
    asub(ASub1,Tests1,Unfold1,MutExclusive1,Det1),
    %% merge_tests(Tests0,Tests1,Tests),
    Tests = Tests1,
    glb_unfold_tests(Unfold0,Unfold1,Unfold),
    glb_mut_exclusion(MutExclusive0,MutExclusive1,MutExclusive),
    glb_determinism(Det0,Det1,Det),
    asub(Glb,Tests,Unfold,MutExclusive,Det).

glb_mut_exclusion(A,B,C) :-
    ( le_mut_exclusion(A,B) ->
        C = A
    ; le_mut_exclusion(B,A) ->
        C = B
    ; C = '$bottom'
    ).

glb_determinism(A,B,C) :-
    ( le_determinism(A,B) ->
        C = A
    ; le_determinism(B,A) ->
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
% det_less_or_equal(+,+)                                                  %
% det_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%

det_less_or_equal(ASub0,ASub1):-
    asub(ASub0,_Tests0,Unfold0,MutExclusive0,Det0),
    asub(ASub1,_Tests1,Unfold1,MutExclusive1,Det1),
    le_mut_exclusion(MutExclusive0,MutExclusive1),
    le_determinism(Det0,Det1),
    le_unfold_tests(Unfold0,Unfold1).

le_mut_exclusion(A,A) :- !.
le_mut_exclusion('$bottom',_).
le_mut_exclusion(_,possibly_not_mut_exclusive).

le_determinism(A,A) :- !.
le_determinism('$bottom',_).
le_determinism(_,possibly_nondet).

le_unfold_tests(A,A):- !.
le_unfold_tests('$bottom',_):-!.
le_unfold_tests(_,not_unfold).

%------------------------------------------------------------------------%
% det_identical_abstract(+,+)                                             %
% det_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%

det_identical_abstract(ASub0,ASub1):-
    asub(ASub0,_Tests0,Unfold,MutExclusive,Det),
    asub(ASub1,_Tests1,Unfold,MutExclusive,Det).

%------------------------------------------------------------------------%
% det_abs_sort(+,-)                                                           %
% det_abs_sort(ASub0,ASub1)                                                   %
%------------------------------------------------------------------------%

det_abs_sort(ASub,ASub).

%------------------------------------------------------------------------%
% det_call_to_success_fact(+,+,+,+,+,+,+,-,-)                               %
% det_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)            %
%-------------------------------------------------------------------------

det_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,Call,Proj,Prime,Succ):-
    Succ = Call,
    Prime = Proj.

%-------------------------------------------------------------------------
% det_special_builtin(+)                                                  |
% det_special_builtin(SgKey)                                              |
%-------------------------------------------------------------------------

det_special_builtin(SgKey):-
   det_builtin(SgKey, _Sg, _CallType, _BType, _BSg, _MutExDet).                          

% det_builtin('!/0',   Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('!/0',  Sg, _CallType,  meta, Sg, _MutExDet):-!.
% det_builtin('cut/0',  Sg, _CallType,  meta, Sg, _MutExDet):-!.
%det_builtin('=/2'   , Sg, _CallType, unif, Sg, _MutExDet):-!.
det_builtin('=/2'   , Sg, _CallType, aritunif, Sg, _MutExDet):-!.
det_builtin('==/2'  , Sg, _CallType, unif, Sg, _MutExDet):-!.
det_builtin('\\==/2' , Sg, _CallType, unif, Sg, _MutExDet):-!.
det_builtin('\\=/2' , Sg, _CallType, unif, Sg, _MutExDet):-!.
% 
det_builtin('is/2', 'is'(X, E), _CallType, arit, =:=(X, E), _MutExDet):-!.
% Arithmetic tests
det_builtin('=:=/2', Sg, _CallType, arit, Sg, _MutExDet):-!. 
det_builtin('=\\=/2', Sg, _CallType, arit, Sg, _MutExDet):-!. 
det_builtin('</2',   Sg, _CallType, arit, Sg, _MutExDet):-!. 
det_builtin('>/2',   Sg, _CallType, arit, Sg, _MutExDet):-!. 
det_builtin('=</2',  Sg, _CallType, arit, Sg, _MutExDet):-!. 
det_builtin('>=/2',  Sg, _CallType, arit, Sg, _MutExDet):-!. 
% TODO:[new-resources] why not module qualified?
det_builtin('number/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('integer/1', Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('atom/1',    Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('var/1',     Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('nonvar/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('ground/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('float/1',   Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('ground/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('atomic/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
%
det_builtin('term_typing:number/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:integer/1', Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:atom/1',    Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:var/1',     Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:nonvar/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:ground/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:float/1',   Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:ground/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
det_builtin('term_typing:atomic/1',  Sg, _CallType, meta, Sg, _MutExDet):-!. 
% Sometimes may act as tests and sometimes succeed. 
det_builtin('io_basic:get_code/1', Sg, _CallType, notest, Sg, MutExDet):- 
     !, 
     det_builtin_trust(MutExDet, mut_exclusive, is_det).
det_builtin('io_basic:get_code/1', Sg, _CallType, notest, Sg, MutExDet):- 
     !, 
     det_builtin_trust(MutExDet, mut_exclusive, is_det).
det_builtin('operators:current_op/3', Sg, _CallType, notest, Sg, MutExDet):- 
     !, 
     det_builtin_trust(MutExDet, mut_exclusive, is_det).
det_builtin('functor/3', Sg, _CallType, notest, Sg, MutExDet):- 
     !, 
     det_builtin_trust(MutExDet, mut_exclusive, is_det).
det_builtin('aggregates:findall/3', Sg, _CallType, notest, Sg, MutExDet):- 
     !, 
     det_builtin_trust(MutExDet, mut_exclusive, is_det).
det_builtin('term_basic:arg/3', Sg, _CallType, notest, Sg, MutExDet):- 
     !, 
     det_builtin_trust(MutExDet, mut_exclusive, is_det).
% No tests that always succeeds.
det_builtin('true/0',    Sg, _CallType, id, Sg, _MutExDet):-!. 
det_builtin('io_basic:nl/0', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('ttyout:ttynl/0', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('ttyout:ttyput/1', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('write:write/1', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('io_basic:tab/1', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('write:writeq/1', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('io_basic:display/1', Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('write:print/1', Sg, _CallType, id, Sg, _MutExDet):-!.
% det_builtin('check/1',   Sg, _CallType, id, Sg, _MutExDet):-!.
det_builtin('basiccontrol:\\+/1', Sg, _CallType, negation, Sg, _MutExDet):-!.
det_builtin('fail/0', Sg, _CallType, notest, Sg, MutExDet):-  
    !, 
    det_builtin_trust(MutExDet, possibly_not_mut_exclusive, possibly_nondet).
det_builtin('basiccontrol:false/0', Sg, _CallType, notest, Sg, MutExDet):- 
    !, 
    det_builtin_trust(MutExDet, possibly_not_mut_exclusive, possibly_nondet).
%%det_builtin('indep/1', Sg, _CallType, notest, Sg, MutExDet):- 
%     !, 
%     det_builtin_trust(MutExDet, possibly_not_mut_exclusive, possibly_nondet).
%det_builtin('indep/2', Sg, _CallType, notest, Sg, MutExDet):- 
%     !, 
%     det_builtin_trust(MutExDet, possibly_not_mut_exclusive, possibly_nondet).

is_free_var(X, CallType):-
     nonvar(CallType),
     shfr_obtain_info(free,[X],CallType,[Y]),
     X == Y.

%-------------------------------------------------------------------------
% det_success_builtin(+,+,+,+,+,-)                                        |
% det_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                          |
%-------------------------------------------------------------------------
% Accumulates the tests:

det_success_builtin(SgKey, CallType,Sg,_,Call,Succ):-
    det_builtin(SgKey,Sg,CallType,BType,BSg,MutExDet),
    det_success_builtin_(BType,CallType,MutExDet,BSg,Call,Succ).
     
det_success_builtin_(id, _CallType, _MutExDet, _BSg, Call, Succ):-  
    % For efficiency (builtins that do not fail).
    !, 
    Succ=Call.
det_success_builtin_(notest, _CallType, MutExDet, _BSg, Call, Succ):-
    !,
    builtin_trust_to_succ(MutExDet,Call,Succ).
det_success_builtin_(negation, CallType, _MutExDet, BSg, Call, Succ):-
    remove_negation(BSg, NSg),
    predkey_from_sg(NSg, NSgkey),
    det_builtin(NSgkey, NSg, CallType, BType, _S, _C),
    ( is_a_test(BType) ->
        push_neg_in_test(BSg, NBSg), 
        det_success_test(BType, NBSg, Call, Succ)
    ; det_success_negation(Call, Succ)
    ).
det_success_builtin_(meta, _CallType, _MutExDet, BSg, Call, Succ):- % cut
    det_success_test(meta, BSg, Call, Succ).
det_success_builtin_(BType, _CallType, _MutExDet, BSg, Call, Succ):-
    is_a_test(BType),
    translate_test(BSg, NewBSg),
    det_success_test(BType, NewBSg, Call, Succ).

det_success_test(BType, BSg, Call, Succ):-
    asub(Call,Tests0,Unfold,MutExclusive,Det),
    tests(Tests0,InVars,Unif0,Arith0,Meta0),
    add_test(BType,BSg,Unif0,Arith0,Meta0,Unif,Arith,Meta),
    tests(Tests,InVars,Unif,Arith,Meta),
    asub(Succ,Tests,Unfold,MutExclusive,Det).

det_success_negation(Call, Succ):-
    asub(Call,Tests,_Unfold,MutExclusive,_Det),
    asub(Succ,Tests,not_unfold,MutExclusive,possibly_nondet).


add_test(unif,Sg,Unif,Arith,Meta,[Sg|Unif],Arith,Meta).
add_test(arit,Sg,Unif,Arith,Meta,Unif,[Sg|Arith],Meta).
add_test(aritunif,Sg,Unif,Arith,Meta,[Sg|Unif],[Sg|Arith],Meta).
add_test(meta,Sg,Unif,Arith,Meta,Unif,Arith,[Sg|Meta]).

is_a_test(Btype):- Btype == unif.
is_a_test(Btype):- Btype == arit.
is_a_test(Btype):- Btype == aritunif.
is_a_test(Btype):- Btype == meta.

builtin_trust_to_succ(MutExDet,Call,Succ):-
    asub(Call,Tests,_Unfold,MutExclusive1,Det1),
    det_builtin_trust(MutExDet, MutExclusive0, Det0),   
    extend_mut_exclusion(MutExclusive0,MutExclusive1,MutExclusive),
    extend_determinism(Det0,Det1,Det),
    asub(Succ,Tests,not_unfold,MutExclusive,Det).
 
det_builtin_trust((MutExclusive, Det), MutExclusive, Det).   

%-------------------------------------------------------------------------
% det_call_to_success_builtin(+,+,+,+,+,-)                                %
% det_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)                 %
%-------------------------------------------------------------------------
% Not used

%------------------------------------------------------------------------%
% det_input_interface(+,+,+,-)                                            %
% det_input_interface(InputUser,Kind,StructI,StructO)                     %
%------------------------------------------------------------------------%
% Something more intelligent should be done with the argument of the props
% than simply ignore them!!!

% TODO: legacy, see old_nfdet
det_input_interface(is_det(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[is_det],Det1).
det_input_interface(non_det(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[non_det],Det1).
det_input_interface(possibly_nondet(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[possibly_nondet],Det1).
%
det_input_interface(det(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[is_det],Det1).
det_input_interface(multi(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[possibly_nondet],Det1).
det_input_interface(semidet(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[is_det],Det1).
det_input_interface(nondet(_),perfect,(MutEx,Det0),(MutEx,Det1)):-
    myappend(Det0,[possibly_nondet],Det1).
det_input_interface(mut_exclusive(_),perfect,(MutEx0,Det),(MutEx1,Det)):-
    myappend(MutEx0,[mut_exclusive],MutEx1).
det_input_interface(not_mut_exclusive(_),perfect,(MutEx0,Det),(MutEx1,Det)):-
    myappend(MutEx0,[not_mut_exclusive],MutEx1).
det_input_interface(possibly_not_mut_exclusive(_),perfect,(MutEx0,Det),(MutEx1,Det)):-
    myappend(MutEx0,[possibly_not_mut_exclusive],MutEx1).

myappend(Vs,V0,V):-
    var(Vs), !,
    V=V0.
myappend(Vs,V0,V):-
    merge(Vs,V0,V).

may_be_var(X,X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------%
% det_input_user_interface(+,+,-,+,+)                                    %
% det_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)           %
%------------------------------------------------------------------------%

det_input_user_interface((MutEx0,Det0),Qv,ASub,_Sg,_MaybeCallASub):-
    may_be_var(MutEx0,MutEx1),
    may_be_var(Det0,Det1),
    foldr(glb_mut_exclusion, MutEx1, possibly_not_mut_exclusive, MutExclusive),
    foldr(glb_determinism, Det1, possibly_nondet, Det),
    det_empty_entry(sg_not_provided,Qv,Entry),
    asub(Entry,Tests,_Unfold,_MutExclusive,_Det),
    asub(ASub,Tests,not_unfold,MutExclusive,Det).

%------------------------------------------------------------------------%
% det_asub_to_native(+,+,-)                                              %
% det_asub_to_native(ASub,Qv,ASub_user)                                  %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!
% something has to be done to put the props in the comp part, not the success
% part of the assertion!!!

det_asub_to_native(ASub,Qv,[PropF,PropC]):-
    asub(ASub,_Tests,_Unfold,Mutex,Det),
    functor(PropF,Det,1),
    ( Mutex = '$bottom' ->
        Mutex0 = not_mut_exclusive
    ; Mutex = Mutex0
    ),
    functor(PropC,Mutex0,1),
    arg(1,PropF,Qv),
    arg(1,PropC,Qv).

%------------------------------------------------------------------------%
% det_unknown_call(+,+,+,-)                                              %
% det_unknown_call(Sg,Vars,Call,Succ)                                    %
%------------------------------------------------------------------------%

det_unknown_call(_Sg,_Vars,Call,Succ):-
    asub(Call,Tests,_,_,_),
    asub(Succ,Tests,not_unfold,possibly_not_mut_exclusive,possibly_nondet).

%------------------------------------------------------------------------%
% det_unknown_entry(+,+,-)                                               %
% det_unknown_entry(Sg,Vars,Entry)                                       %
%------------------------------------------------------------------------%

det_unknown_entry(Sg,Vars,Entry):-
    det_empty_entry(Sg,Vars,Entry).

%------------------------------------------------------------------------%
% det_empty_entry(+,+,-)                                                 %
% det_empty_entry(Sg,Vars,Entry)                                         %
%------------------------------------------------------------------------%

det_empty_entry(_Sg,Vars,Entry):-
    tests(Tests,Vars,[],[],[]),
    asub(Entry,Tests,unfold,mut_exclusive,is_det).

%-----------------------------------------------------------------------

detabs_dom_statistics([detstatistics([total_preds(Total),
                                      preds_det(Det_Preds),
                                      preds_mutex(MutEx_Preds),
                                      preds_some_variant_det(Det_Variants),
                                      preds_some_variant_mutex(MutEx_Variants)])]) :-
    nfdet_statistics(det, _S, Total, Det_Preds, MutEx_Preds, Det_Variants, MutEx_Variants).
