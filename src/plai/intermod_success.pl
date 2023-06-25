:- module(intermod_success, [get_success_info/7, apply_success_policy/9],
          [assertions, isomodes, datafacts]).

:- include(intermod_options). % intermod compilation options

% ------------------------------------------------------------
:- doc(title, "Intermodular success policy").
% ------------------------------------------------------------

:- doc(module, "This module implements the policies to compute (possibly)
temporary success patterns when modular analysis is performed.").

:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(lists), [member/2]).

:- use_module(library(compiler/p_unit/itf_db), [get_module_from_sg/2]).
:- use_module(library(compiler/p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(ciaopp(plai/intermod_ops), [ may_be_improved_mark/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(plai/domains), 
    [abs_sort/3, compute_lub/3, glb/4, less_or_equal/3, unknown_call/5,
      call_to_entry/10]).
:- use_module(ciaopp(plai/fixpo_ops), [clause_applies/2]).
:- use_module(ciaopp(plai/intermod_db), [registry/3,punit_module/2]).
:- use_module(ciaopp(plai/intermod_punit), [open_mode/3]).

%-----------------------------------------------------------------------------

:- data tmp_success/3.

%-----------------------------------------------------------------------------
:- pred get_success_info(+Call,+SgKey,+Sg,+Sv,+AbsInt,-Prime,-PatternsApplied)
   # "Given a call pattern for an imported predicate defined by @var{Call} call
   and @var{Sg} abstract substitution, @var{Prime} is the success substitution
   resulting from the application of the success policy for imported predicates.
   @var{PatternsApplied} is instatiated to @tt{no} if there are no applicable
   patterns. The predicate is allowed to fail if no patterns are found.".
get_success_info(Call,SgKey,Sg,Sv,AbsInt,Prime,PatternsApplied):-
    get_module_from_sg(Sg,Module),
    punit_module(Base,Module),  !,
    functor(Sg,F,A),
    functor(SgProj,F,A),
    ( open_mode(Base,_,read_only) ->
        findall((SgProj,Proj,Succ), succ_pattern(over_all,AbsInt,SgProj,Proj,Succ), Patterns),
        apply_success_policy(over_all,AbsInt,SgKey,Sg,Sv,Call,Patterns,Prime,PatternsApplied)
    ;
        current_pp_flag(success_policy,SuccessPolicy),
        findall((SgProj,Proj,Succ), succ_pattern(SuccessPolicy,AbsInt,SgProj,Proj,Succ), Patterns),
        apply_success_policy(SuccessPolicy,AbsInt,SgKey,Sg,Sv,Call,Patterns,Prime,PatternsApplied)
    ).

:- pred apply_success_policy(+SuccPolicy,+AbsInt,+SgKey,+Sg,+Sv,+Proj,+Patterns,-Prime,-PatternsApplied)
   # "Applies the success policy given as first argument to the list of triples
   (SgProj,Proj,Succ) @var{Patterns} w.r.t. @var{Proj}. If there are no
   applicable patterns in @var{Patterns}, it returns either @tt{'$bottom'} or
   the topmost substitution, depending on the type of the success policy (either
   it is underapproximating or overapproximating, respectively.)
   @var{PatternsApplied} is instatiated to @tt{no} if there are no applicable
   patterns.".
apply_success_policy(over_first,AbsInt,SgKey,SgCall,Sv,Call,Patterns,Prime,yes) :-
%       functor(SgCall,F,A),
%       functor(SgCopy,F,A),
%       succ_pattern(AbsInt,SgCopy,Proj,Succ),
    member((SgProj,Proj,Succ),Patterns),
    asub_is_applicable(over_first,SgKey,SgCall,Sv,Call,AbsInt,SgProj,Proj,Succ,Prime0), !,
    unknown_call(AbsInt,SgCall,Sv,Call,Prime1),
    glb(AbsInt,Prime0,Prime1,Prime).
apply_success_policy(over_first,AbsInt,_SgKey,Sg,Sv,Call,_Patterns,Prime,no) :-
    %% If there are no applicable succ patterns, unknown_call is used.
    unknown_call(AbsInt,Sg,Sv,Call,Prime).
apply_success_policy(over_best,AbsInt,SgKey,SgCall,Sv,Call,Patterns,_Prime,_PatternsApplied) :-
    %% 'best' policy select those success patterns which are applicable 
    %% and minimal (there is no other pattern which is applicable and has 
    %% a call pattern smaller than the one selected).
    %% Therefore, it depends on the order of the success patterns.
    retractall_fact(tmp_success(_,_,_)),
%       functor(SgCall,F,A),
%       functor(SgCopy,F,A),
%       succ_pattern(AbsInt,SgCopy,Proj,Succ),
    member((SgProj,Proj,Succ),Patterns),
    asub_is_applicable(over_best,SgKey,SgCall,Sv,Call,AbsInt,SgProj,Proj,Succ,Prime),
    ( current_fact(tmp_success(Sv,[Proj0],[_Prime0]),Ref) -> 
        less_or_equal_(over_best,AbsInt,Proj,Proj0),
        erase(Ref),
        asserta_fact(tmp_success(Sv,[Proj],[Prime]))
    ; asserta_fact(tmp_success(Sv,[Proj],[Prime]))
    ),
    fail.
apply_success_policy(over_best,AbsInt,_SgKey,Sg,Sv,Call,_Patterns,Prime,yes) :-
    retract_fact(tmp_success(Sv,_,[Prime0])),
    unknown_call(AbsInt,Sg,Sv,Call,Prime1),
    glb(AbsInt,Prime0,Prime1,Prime).
apply_success_policy(over_best,AbsInt,_SgKey,Sg,Sv,Call,_Patterns,Prime,no) :-
    %% If there are no applicable succ patterns, unknown_call is used.
    unknown_call(AbsInt,Sg,Sv,Call,Prime).
apply_success_policy(over_all,AbsInt,SgKey,SgCall,Sv,Call,Patterns,_Prime,_PatternsApplied) :-
    retractall_fact(tmp_success(_,_,_)),
    member((SgProj,Proj,Succ),Patterns),
    asub_is_applicable(over_all,SgKey,SgCall,Sv,Call,AbsInt,SgProj,Proj,Succ,Prime),
    ( current_fact(tmp_success(Sv,[_Proj0],[Prime0]),Ref) -> 
        glb(AbsInt,Prime0,Prime,Prime1),
        erase(Ref),
        asserta_fact(tmp_success(Sv,[Call],[Prime1]))
    ; asserta_fact(tmp_success(Sv,[Call],[Prime]))
    ),
    fail.
apply_success_policy(over_all,AbsInt,_SgKey,Sg,Sv,Call,_Patterns,Prime,yes) :-
    retract_fact(tmp_success(Sv,_,[Prime0])),
    unknown_call(AbsInt,Sg,Sv,Call,Prime1),
    glb(AbsInt,Prime0,Prime1,Prime).
apply_success_policy(over_all,AbsInt,_SgKey,Sg,Sv,Call,_Patterns,Prime,no) :-
    %% If there are no applicable succ patterns, unknown_call is used.
    unknown_call(AbsInt,Sg,Sv,Call,Prime).
apply_success_policy(top,AbsInt,_SgKey,Sg,Sv,Call,_Patterns,Prime,no) :-
    %% top success policy does not need patterns, PatternsApplied is set to no.
    unknown_call(AbsInt,Sg,Sv,Call,Prime).
apply_success_policy(under_first,AbsInt,SgKey,SgCall,Sv,Call,Patterns,Prime,yes) :-
    member((SgProj,Proj,Succ),Patterns),
    asub_is_applicable(under_first,SgKey,SgCall,Sv,Call,AbsInt,SgProj,Proj,Succ,Prime0), !,
%       unknown_call(AbsInt,SgCall,Sv,Call,Prime1),
%       compute_lub(AbsInt,[Prime0,Prime1],Prime).
    Prime0 = Prime.
apply_success_policy(under_first,_AbsInt,_SgKey,_Sg,_Sv,_Proj,_Patterns,'$bottom',no).
apply_success_policy(under_best,AbsInt,SgKey,SgCall,Sv,Call,Patterns,_Prime,_PatternsApplied):-
    %% 'botbest' policy is just like 'best', but using under-approximations.
    retractall_fact(tmp_success(_,_,_)),
    member((SgProj,Proj,Succ),Patterns),
    asub_is_applicable(under_best,SgKey,SgCall,Sv,Call,AbsInt,SgProj,Proj,Succ,Prime),
    ( current_fact(tmp_success(Sv,[Proj0],[_Prime0]),Ref) -> 
        less_or_equal_(under_best,AbsInt,Proj,Proj0),
        erase(Ref),
        asserta_fact(tmp_success(Sv,[Proj],[Prime]))
    ; asserta_fact(tmp_success(Sv,[Proj],[Prime]))
    ),
    fail.
apply_success_policy(under_best,_AbsInt,_SgKey,_Sg,Sv,_Call,_Patterns,Prime,yes):-
    retract_fact(tmp_success(Sv,_,[Prime])).
apply_success_policy(under_best,_AbsInt,_SgKey,_Sg,_Sv,_Proj,_Patterns,'$bottom',no).
apply_success_policy(under_all,AbsInt,SgKey,SgCall,Sv,Call,Patterns,_Prime,_PatternsApplied):-
    retractall_fact(tmp_success(_,_,_)),
    member((SgProj,Proj,Succ),Patterns),
    asub_is_applicable(under_all,SgKey,SgCall,Sv,Call,AbsInt,SgProj,Proj,Succ,Prime),
    ( current_fact(tmp_success(Sv,[_Call],[Prime0]),Ref) -> 
        compute_lub(AbsInt,[Prime0,Prime],Prime1),
        erase(Ref),
        asserta_fact(tmp_success(Sv,[Call],[Prime1]))
    ; asserta_fact(tmp_success(Sv,[Call],[Prime]))
    ),
    fail.
apply_success_policy(under_all,_AbsInt,_SgKey,_Sg,Sv,_Call,_Patterns,Prime,yes):-
    retract_fact(tmp_success(Sv,_,[Prime])).
apply_success_policy(under_all,_AbsInt,_SgKey,_Sg,_Sv,_Proj,_Patterns,'$bottom',no).
apply_success_policy(bottom,_AbsInt,_SgKey,_Sg,_Sv,_Proj,_Patterns,'$bottom',no).
    %% bottom success policy does not need patterns, PatternsApplied is set to no.
apply_success_policy(bottom_up,AbsInt,SgKey,Sg,Sv,Proj,Patterns,Prime,PatternsApplied):-
    %% this is the bottom-up policy proposed by Maria, Peter, and Kim.
    apply_success_policy(over_all,AbsInt,SgKey,Sg,Sv,Proj,Patterns,Prime0,PatApp),
    ( PatApp == yes ->
        Prime = Prime0,
        PatternsApplied = PatApp
    ;
        Prime = '$bottom',
        PatternsApplied = PatApp
    ).

%% ----------------------------------------

:- pred asub_is_applicable(+SuccessPolicy,+SgKey,+SgCall,+Sv,+Call,+AbsInt,+SgProj,+Proj,+Succ,-Prime) 
   # "Given a call pattern defined by @var{SgCall} and abstract substitution
   @var{Call}, succeeds if @var{SgProj} and (@var{Proj},@var{Succ}) is
   applicable with respect to @var{SuccessPolicy} with success substitution
   @var{Prime}.".
asub_is_applicable(SuccessPolicy,_SgKey,SgCall,_Sv,Call0,AbsInt,SgProj,Proj0,Succ,Prime):-
    variant(SgCall,SgProj), !,
    SgCall=SgProj,
    abs_sort(AbsInt,Call0,Call),
    abs_sort(AbsInt,Proj0,Proj),
    less_or_equal_(SuccessPolicy,AbsInt,Call,Proj),
    abs_sort(AbsInt,Succ,Prime).
asub_is_applicable(SuccessPolicy,_SgKey,SgCall,Sv,Call0,AbsInt,SgProj,Proj0,Succ,Prime):-
    clause_applies(SgProj,SgCall),
    varset(SgProj,Pv),
    \+ Proj0 = '$bottom', \+ Succ = '$bottom',
    % call_to_entry cannot be called with bottom (and it is obviously not applicable)
    call_to_entry(AbsInt,Pv,SgProj,Sv,SgCall,not_provided,[],Proj0,Entry0,_), % TODO: add some ClauseKey? (JF)
    abs_sort(AbsInt,Entry0,Entry),
    abs_sort(AbsInt,Call0,Call),
    less_or_equal_(SuccessPolicy,AbsInt,Call,Entry), 
    %     exit_to_prime(AbsInt,SgCall,Pv,SgProj,Sv,Succ,_,Prime),
    call_to_entry(AbsInt,Pv,SgProj,Sv,SgCall,not_provided,[],Succ,Prime,_). % TODO: add some ClauseKey? (JF)

%%      functor(Sg,F,A),
%%      functor(SgCopy,F,A),
%%      get_predkey(F,A,SgKey),
%%      asub_is_applicable_(AbsInt,SuccessPolicy,SgCopy,Call,Succ,Sg,Sv,Proj,Prime).
%%
%%
%%asub_is_applicable_(AbsInt,SuccessPolicy,SgCopy,Call0,Succ,Sg,_Sv,Proj,Prime):-
%%      variant(SgCopy,Sg), !,
%%      SgCopy=Sg,
%%        abs_sort(AbsInt,Call0,Call),
%%      less_or_equal_(SuccessPolicy,AbsInt,Proj,Call),
%%        abs_sort(AbsInt,Succ,Prime).
%%asub_is_applicable_(AbsInt,SuccessPolicy,SgCopy,Call,Succ,Sg,Sv,Proj,Exit):-
%%      varset(SgCopy,Gv),
%%      call_to_entry(AbsInt,Gv,SgCopy,Sv,Sg,not_provided,[],Call,Entry,_),
%%      less_or_equal_(SuccessPolicy,AbsInt,Proj,Entry), 
%%      call_to_entry(AbsInt,Gv,SgCopy,Sv,Sg,not_provided,[],Succ,Exit,_).

%-----------------------------------------------------------------------------

less_or_equal_(SuccessPolicy,AbsInt,Call,Entry):-
    comparison_criteria(SuccessPolicy,Mode),
    less_or_equal_1(Mode,AbsInt,Call,Entry).

less_or_equal_1(lt,AbsInt,Call,Entry):-
    less_or_equal(AbsInt,Call,Entry).
less_or_equal_1(gt,AbsInt,Call,Entry):-
    less_or_equal(AbsInt,Entry,Call).

%-----------------------------------------------------------------------------

%% Note: the first argument of comparison_criteria/2 must match the 
%% options of success_policy preprocessing flag.
comparison_criteria(over_first,lt).
comparison_criteria(over_best,lt).
comparison_criteria(over_all,lt).
comparison_criteria(top,lt).
comparison_criteria(under_first,gt).
comparison_criteria(under_best,gt).
comparison_criteria(under_all,gt).
comparison_criteria(bottom,gt).
comparison_criteria(bottom_up,lt).

%% ********************************************************************
%% ********************************************************************

:- pred succ_pattern(+SuccessPolicy,+AbsInt,+Sg,-Call,-Succ)
   # "Provides on backtracking the call and success patterns @var{Call} and
   @var{Succ} of exported predicates of a given goal @var{Sg} on a given
   abstract domain @var{AbsInt}. It uses @var{SuccessPolicy} to check which
   marked patterns can be used.

   This predicate is called by the analysis procedure to get info about imported
   predicates. For performance reasons, when an external predicate of an
   imported module is requested, all the exported predicates of the imported
   module are loaded into memory.".
succ_pattern(SP,AbsInt,Sg,Call_s,Succ_s):-
    predkey_from_sg(Sg,SgKey),
    current_fact(registry(SgKey,_,regdata(_,AbsInt,Sg,Call,Succ,_,_,_,Mark))),
    % ..., and get call patterns on backtracking.
    ( Mark = unmarked -> true
    ; may_be_improved_mark(SP,Mark)
    ),
    abs_sort(AbsInt,Call,Call_s),
    abs_sort(AbsInt,Succ,Succ_s).
