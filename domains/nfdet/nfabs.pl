:- module(nfabs, [
    nf_call_to_entry/9,
    nf_exit_to_prime/7,
    nf_project/5,
    nf_extend/5,
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
    nfabs_dom_statistics/1
], [assertions,regtypes,basicmodes,hiord]).

:- use_module(domain(nfdet/nfsets), [create_minset_and_project/4]).
:- use_module(domain(nfdet/cover), [covers_check/5]).
:- use_module(domain(nfdet/nfbool), [push_neg_in_test/2, remove_negation/2, translate_test/2]).
:- use_module(domain(sharefree), [shfr_obtain_info/4]).
:- use_module(domain(s_eqs), [peel/4]).
:- use_module(domain(nfdet/nfdet_statistics)).
:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(library(lists), [append/3]).
:- use_module(library(hiordlib), [foldr/4]).
:- use_module(library(sets), [merge/3]).

%------------------------------------------------------------------------%

:- doc(bug,"Think on an adequate treatment for negation.").

%------------------------------------------------------------------------%

asub(nf(Tests,Covered,Fails),Tests,Covered,Fails).

tests(t(InVars,Unif,Arith,Meta),InVars,Unif,Arith,Meta).

%------------------------------------------------------------------------%
% nf_call_to_entry(+,+,+,+,+,+,+,-,-)                                    %
% nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)              %
%------------------------------------------------------------------------%
% Entering a clause: initialize an asub to start gathering the tests of
% this clause 

nf_call_to_entry(_Sv,Sg,_Hv,_Head,_K,_Fv,_Proj,Entry,_Extra):-
    nf_empty_entry(Sg,_Vars,Entry). % TODO: unbound _Vars! use []? (JF)

%------------------------------------------------------------------------%
% nf_exit_to_prime(+,+,+,+,+,-,-)                                        %
% nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                   %
%------------------------------------------------------------------------%
% Exiting a clause: project the tests gathered while traversing the clause 
% onto the variables of the goal

nf_exit_to_prime(Sg,_Hv,Head,_Sv,Exit,GVars,Prime):-
    asub(Exit,Tests,Covered,Fails),
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
    asub(Prime,PrimeTests,Covered,Fails).
nf_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_Extra,'$bottom').

% new_tests([],[],[]).
% new_tests([X|Xs],[Y|Ys],[X=Y|Eqs]):-
%       new_tests(Xs,Ys,Eqs).

%------------------------------------------------------------------------%
% nf_project(+,+,+,+,-)                                                  %
% nf_project(Sg,Vars,HvFv_u,ASub,Proj)                                   %
%------------------------------------------------------------------------%
% To project on Vars, leave only tests for Vars

nf_project(_Sg,Vars,_HvFv_u,ASub,Proj):-
    asub(ASub,Tests0,Covered,Fails),
    select_tests(Tests0,Vars,TestsProj),
    asub(Proj,TestsProj,Covered,Fails).

select_tests(Tests,_Vars,Tests).

%------------------------------------------------------------------------%
% nf_extend(+,+,+,+,-)                                                   %
% nf_extend(Sg,Prime,Sv,Call,Succ)                                       %
%------------------------------------------------------------------------%
% Return back to the calling clause: merge the tests in Call with the
% tests in Prime

nf_extend(_Sg,Prime,_Sv,Call,Succ):-
    asub(Prime,Tests0,Covered0,Fails0),
    asub(Call,Tests1,Covered1,Fails1),
    merge_tests(Tests0,Tests1,Tests),
    glb_covering(Covered0,Covered1,Covered),
    glb_nonfailure_1(Fails0,Fails1,Fails),
    asub(Succ,Tests,Covered,Fails).

% b) simple tests, do not collect:
merge_tests(_Tests0,Tests,Tests).
% c) collect tests from the body goals
%% merge_tests(Tests0,Tests1,Tests):-
%%      append(Tests0,Tests1,Tests).

glb_nonfailure_1(not_fails,not_fails,not_fails):- !.
glb_nonfailure_1(_,_,possibly_fails).

%------------------------------------------------------------------------%
% nf_compute_lub(+,-)                                                    %
% nf_compute_lub(ListASub,Lub)                                           %
%------------------------------------------------------------------------%
% Simply put all tests together (this is due to the way this operation
% is called from the fixpoint)

nf_compute_lub(ListASub,Lub):-
    asub(ASub,[],covered,not_fails),
    foldr(accumulate, ListASub, ASub, Lub).

accumulate('$bottom',ASub0,ASub0):- !.
accumulate(ASub,ASub0,NewASub):-
    asub(ASub0,Tests0,Covered0,Fails0),
    asub(ASub,Tests,Covered1,Fails1),
    ( Fails1 == not_fails ->
        append_(Tests,Tests0,Tests1),
        % Tests1=[Tests|Tests0],
        lub_covering(Covered0,Covered1,Covered),
        lub_nonfailure(Fails0,Fails1,Fails)
    ; append_(Tests,Tests0,Tests1), % Tests1=[Tests|Tests0],
      Covered=Covered0,
      Fails=Fails0
    ),
    asub(NewASub,Tests1,Covered,Fails).

append_(Tests,Tests0,Tests1):-
    Tests=[_|_], !,
    append(Tests,Tests0,Tests1).
append_(Tests,Tests0,[Tests|Tests0]).

lub_covering(covered,covered,covered):- !.
lub_covering(_,_,possibly_not_covered).

lub_nonfailure(not_fails,not_fails,not_fails):- !.
lub_nonfailure(_,_,possibly_fails).

%------------------------------------------------------------------------%
% nf_compute_covering(+,+,-)                                             %
% nf_compute_covering(ModeTypes,Lub,ASub)                                %
%------------------------------------------------------------------------%
% New operation, has to be called from fixpoint when all clauses of a 
% predicate have been traversed: compute covering information

nf_compute_covering(ModeTypes,Lub,ASub):-
    % this one is a little tricky: Lub is not a well-formed abstract
    % substitution, it is a collection of tests from compute_lub
    asub(Lub,TestsList,_Covered,Fails0),
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
    lub_nonfailure(Fails0,Fails1,Fails),
    foldr_testlist(TestsList,Tests),
    asub(ASub,Tests,Covered,Fails).

% covers_check_(ModeTypes,false,_Masc,MinSetTestsList,Res):-
%       covers_check(ModeTypes,false,_Masc,MinSetTestsList,Res), !.
% covers_check_(_ModeTypes,false,_Masc,_MinSetTestsList,true).

result_to_covering(true,covered).
result_to_covering(fail,possibly_not_covered).
result_to_covering(false,possibly_not_covered).

covering_to_nonfailure(covered,not_fails).
covering_to_nonfailure(possibly_not_covered,possibly_fails).

foldr_testlist(_TestsList,Tests):-
    nf_empty_entry(sg_not_provided,[],Entry),
    asub(Entry,Tests,_Covered,_Fails).

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
    asub(ASub0,Tests0,Covered0,Fails0),
    asub(ASub1,Tests1,Covered1,Fails1),
    merge_tests(Tests0,Tests1,Tests),
    glb_covering(Covered0,Covered1,Covered),
    glb_nonfailure(Fails0,Fails1,Fails),
    asub(Glb,Tests,Covered,Fails).

glb_covering(possibly_not_covered,possibly_not_covered,possibly_not_covered):- !.
glb_covering(_,_,covered).

glb_nonfailure(possibly_fails,possibly_fails,possibly_fails):- !.
glb_nonfailure(_,_,not_fails).

%------------------------------------------------------------------------%
% nf_less_or_equal(+,+)                                                  %
% nf_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%

nf_less_or_equal(ASub0,ASub1):-
    asub(ASub0,_Tests0,Covered0,Fails0),
    asub(ASub1,_Tests1,Covered1,Fails1),
    le_covering(Covered0,Covered1),
    le_nonfailure(Fails0,Fails1).

le_covering(covered,possibly_not_covered).
le_covering(covered,covered).
le_covering(possibly_not_covered,possibly_not_covered).

le_nonfailure(not_fails,possibly_fails).
le_nonfailure(possibly_fails,possibly_fails).
le_nonfailure(not_fails,not_fails).

%------------------------------------------------------------------------%
% nf_identical_abstract(+,+)                                             %
% nf_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%

nf_identical_abstract(ASub0,ASub1):-
    asub(ASub0,_Tests0,Covered,Fails),
    asub(ASub1,_Tests1,Covered,Fails).

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

nf_builtin('=/2'   , Sg, _CallType, unif, Sg, _CovNf):-!.
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

is_free_var(X, CallType):-
     nonvar(CallType),
     shfr_obtain_info(free,[X],CallType,[Y]),
     X == Y.

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
    asub(Call,Tests0,Covered,Fails),
    tests(Tests0,InVars,Unif0,Arith0,Meta0),
    add_test(BType,BSg,Unif0,Arith0,Meta0,Unif,Arith,Meta),
    tests(Tests,InVars,Unif,Arith,Meta),
    asub(Succ,Tests,Covered,Fails).

nf_success_negation(Call, Succ):-
    asub(Call,Tests,Covered,_Fails),
    asub(Succ,Tests,Covered,possibly_fails).

add_test(unif,Sg,Unif,Arith,Meta,[Sg|Unif],Arith,Meta).
add_test(arit,Sg,Unif,Arith,Meta,Unif,[Sg|Arith],Meta).
add_test(meta,Sg,Unif,Arith,Meta,Unif,Arith,[Sg|Meta]).

is_a_test(Btype):- Btype == unif.
is_a_test(Btype):- Btype == arit.
is_a_test(Btype):- Btype == meta.

builtin_trust_to_succ(CovNF,Call,Succ):-
    asub(Call,Tests,Covered1,Fails1),
    nf_builtin_trust(CovNF, Covered0, Fails0),   
    glb_covering(Covered0,Covered1,Covered),
    glb_nonfailure_1(Fails0,Fails1,Fails),
    asub(Succ,Tests,Covered,Fails).
 
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

nf_input_interface(not_fails(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[not_fails],Fail1).
%nf_input_interface(fails(_),approx,(Cov,Fail0),(Cov,Fail1)):-
%       myappend(Fail0,[possibly_fails],Fail1).
nf_input_interface(possibly_fails(_),perfect,(Cov,Fail0),(Cov,Fail1)):-
    myappend(Fail0,[possibly_fails],Fail1).
nf_input_interface(covered(_),perfect,(Cov0,Fail),(Cov1,Fail)):-
    myappend(Cov0,[covered],Cov1).
%nf_input_interface(not_covered(_),approx,(Cov0,Fail),(Cov1,Fail)):-
%       myappend(Cov0,[possibly_not_covered],Cov1).
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
    foldr(glb_covering, Cov1, covered, Covered),
    foldr(glb_nonfailure, Fail1, not_fails, Fails),
    nf_empty_entry(sg_not_provided,Qv,Entry),
    asub(Entry,Tests,_Covered,_Fails),
    asub(ASub,Tests,Covered,Fails).

%------------------------------------------------------------------------%
% nf_asub_to_native(+,+,-)                                               %
% nf_asub_to_native(ASub,Qv,ASub_user)                                   %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!
% something has to be done to put the props in the comp part, not the success
% part of the assertion!!!

nf_asub_to_native(ASub,Qv,[PropF,PropC]):-
    asub(ASub,_Tests,Covered,Fails),
    functor(PropF,Fails,1),
    functor(PropC,Covered,1),
    arg(1,PropF,Qv),
    arg(1,PropC,Qv).

%------------------------------------------------------------------------%
% nf_unknown_call(+,+,+,-)                                               %
% nf_unknown_call(Sg,Vars,Call,Succ)                                     %
%------------------------------------------------------------------------%

nf_unknown_call(_Sg,_Vars,Call,Succ):-
    asub(Call,Tests,_,_),
    asub(Succ,Tests,possibly_not_covered,possibly_fails).

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
    asub(Entry,Tests,covered,not_fails).

%-----------------------------------------------------------------------

nfabs_dom_statistics([nfstatistics([total_preds(Total),
                                    preds_not_fail(NF_Preds),
                                    preds_covered(Cov_Preds),
                                    preds_some_variant_not_fail(NF_Variants),
                                    preds_some_variant_covered(Cov_Variants)])]):-
    nfdet_statistics(nf, _S, Total, NF_Preds, Cov_Preds, NF_Variants, Cov_Variants).
