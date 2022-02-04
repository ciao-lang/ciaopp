:- module(ctchecks_pred,
          [simplify_assertions_all/1, simplify_assertions_mods/2, ctchecks_log/5],
          [assertions, regtypes, nativeprops, isomodes, datafacts, ciaopp(ciaopp_options)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(title, "Compile-time Assertion Checking").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- use_module(ciaopp(preprocess_flags)).
:- use_module(ciaopp(ctchecks/comp_ctchecks), [abs_execute_comp/5, abs_execute_sizes/5]).
:- use_module(ciaopp(ctchecks/ctchecks_pred_messages), [inform_as_change_to_user/5]).
:- use_module(ciaopp(ctchecks/ctchecks_common), [get_check_assertion/3]).

%% CiaoPP library:
:- use_module(ciaopp(plai/domains), 
   [glb/4, info_to_asub/7, unknown_call/5,
   call_to_entry/10, identical_abstract/3]).

:- use_module(ciaopp(p_unit),
    [predicate_names/1, multifile_predicate_names/1, entry_assertion/3, assertion_set_status/3,
     assertion_set_calls/3, assertion_set_success/3, assertion_set_comp/3,
     get_pred_mod_defined/2]).
:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).
:- use_module(ciaopp(p_unit/p_unit_basic), [type_of_goal/2]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [ref_assertion_read/10]).

:- use_module(ciaopp(infer), [get_completes_lub/6, get_completes/4, get_info/5]).
:- use_module(ciaopp(infer/infer_dom),   [abs_execute/7]).

%% Ciao library:
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(formulae), [list_to_conj/2]).
:- use_module(library(aggregates), [findall/3]).

%[LD] for interval
%:- use_module(ciaopp(preprocess_flags),[current_pp_flag/2]).
:- if(defined(has_ciaopp_cost)).
:- use_module(infercost(algebraic/polynom_comp),[polynom_current_assertion/1]).
:- endif.
%[/LD] for interval

%-------------------------------------------------------------------
% all fixed (PP):
%:- doc(bug,"1. Multivariant analysis is not fully exploited. Multiple
%       versions are collapsed into one before simplifying
%       assertions").
%:- doc(bug,"2. Should be reprogrammed so as to not depend on any AbsInt,
%       but use everything that has been analyzed (i.e., use infer.pl).").
%:- doc(bug,"3. Checks for comp assertions not yet integrated.").
%:- doc(bug,"4. Assertions turn true are not shown.").

:- doc(bug,"5. Compatibility properties are not considered at all.").

%-------------------------------------------------------------------
:- export(decide_get_info/4).
% set of completes
decide_get_info(AbsInt,Key,MGoal,Completes):-
    current_pp_flag(multivariant_ctchecks, on),!,
    get_completes(Key,MGoal,AbsInt,Completes).
% completes lub
decide_get_info(AbsInt,Key,MGoal,[complete(MGoal,MCall,[MSuccess],Key,lub)]):-
%       current_pp_flag(collapse_ai_vers, on),
    current_pp_flag(multivariant_ctchecks, off),
    get_completes_lub(Key,MGoal,AbsInt,yes,MCall,MSuccess),!.
% TODO: is the following unreachable? multivariant_ctchecks can only be on or off.
decide_get_info(AbsInt,Key,MGoal,Info) :-
    get_info(AbsInt,pred,Key,MGoal,Info),!.
decide_get_info(_AbsInt,_Key,_Goal, []).

:- data ctchecks_log/5.
:- pred ctchecks_log(?Abs,?Status,?Type,?Key,?Id) + no_rtcheck # 
    "Returns upon backtracking completes (@var{Key}+@var{Id}+@var{Abs}) 
     which participated during CT checking in giving assertion of 
     type @var{Type} (calls or success) status @var{check}.".

% ---------------------------------------------------------------------------
:- pred simplify_assertions_all(+AbsInts) : list(atm)
   # "Check calls, success and comp assertions with status @tt{check} for all
   the predicates using the domains @var{AbsInts}.".
simplify_assertions_all(AbsInts):-
    simplify_assertions_mods(AbsInts, all).

:- pred simplify_assertions_mods(+AbsInts, +MaybeModList) : list(atm) * atm.
:- pred simplify_assertions_mods(+AbsInts, +MaybeModList) : list(atm) * list(atm)
   + (not_fails, is_det)
   # "Check calls, success and comp assertions with the check status for all
   the predicates in the modules given by @var{MaybeModList} given the domains
   in @var{AbsInts}. If @var{MaybeModList} is the atom @tt{all}, all predicates are
   considered.".
simplify_assertions_mods(AbsInts, ModList):-
    retractall_fact(ctchecks_log(_,_,_,_,_)),
    ( % (failure-driven loop)
      (predicate_names(Preds) ; multifile_predicate_names(Preds)),
      member(F/A, Preds),
        functor(Sg,F,A),
        ( ModList = all -> true
        ; (get_pred_mod_defined(Sg,Mod), member(Mod,ModList)) -> true
        ; fail
        ),
        check_pred_all(Sg, AbsInts),
        fail
    ; true
    ).

:- pred check_pred_all(+Sg, +AbsInts) + (not_fails, is_det)
   # "Execute abstractly assertions for a predicate @var{Sg} over the domains
     @var{AbsInts}".
check_pred_all(Sg, AbsInts) :-
    findall(A-ARef, get_check_assertion(Sg, A, ARef), LA),
    \+ LA = [], !,
    predkey_from_sg(Sg, Key),
    decide_get_info_all(AbsInts, Key, Sg, Info),
    warn_call_assrts(LA,Sg,0), % TODO: gather all call assrts in an body with ';/2'
    abs_execute_ass_predicate_all(LA, Key, Sg, AbsInts, Info, NLA),
    inform_as_changes_to_user(NLA),
    !. % TODO: this cut should not be needed (make sure no choicepoints are left)
check_pred_all(_, _).

% TODO: temporary warning, fix checking several call assertions!!
:- use_module(library(messages), [warning_message/2]).

warn_call_assrts([], Sg, N) :-
    ( N >= 2 ->
      warning_message("More than one call assertion for ~q", [Sg])
    ; true).
warn_call_assrts([A|As], Sg, N) :-
    ( A = as${type=>call} ->
        N1 is N + 1
    ;
        N1 = N
    ),
    warn_call_assrts(As, Sg, N1).

inform_as_changes_to_user([]).
inform_as_changes_to_user([u(Old,OldRef,New,AbsInts,Info)|As]) :-
    inform_as_change_to_user(Old,OldRef,New,AbsInts,Info),
    inform_as_changes_to_user(As).

decide_get_info_all([],_,_,[]).
decide_get_info_all([D|Ds],Key,P,[I|Is]):-
    decide_get_info(D,Key,P,I),
    decide_get_info_all(Ds,Key,P,Is).

:- pred abs_execute_ass_predicate_all(+list,+,+,+list,+,-).

abs_execute_ass_predicate_all([], _Key, _Goal, _AbsInts, _Info, []).
abs_execute_ass_predicate_all([A-ARef|Ass], Key, Goal, AbsInts, Info, Out) :-
    abs_exec_one_assertion_all(AbsInts, Info, A, Key, DomsOut, InfoOut, NA),
    Out = [u(A,ARef,NA,DomsOut,InfoOut)|AsR],
    abs_execute_ass_predicate_all(Ass, Key, Goal, AbsInts, Info, AsR).

abs_exec_one_assertion_all(AbsInts, Info, A, Key, DomsOut, InfoOut, NA) :-
    ( current_pp_flag(ctchecks_intervals, on) -> CheckIntervals = on
    ; CheckIntervals = off
    ),
    % assert fact for interval information % TODO: ugly
    ( CheckIntervals = on -> push_polynom_curr_assrt(A) %%LD
    ; true
    ),
    abs_exec_one_assertion_all_(AbsInts, Info, A, Key, DomsOut, InfoOut, NA, _Status),
    % retract fact for interval information % TODO: ugly
    ( CheckIntervals = on -> pop_polynom_curr_assrt(A) %%LD
    ; true
    ).

:- if(defined(has_ciaopp_cost)).
%%LD
push_polynom_curr_assrt(A) :- asserta_fact(polynom_current_assertion(A)).
pop_polynom_curr_assrt(A) :- retractall_fact(polynom_current_assertion(A)).
:- else.
push_polynom_curr_assrt(_).
pop_polynom_curr_assrt(_).
:- endif.

:- pred abs_exec_one_assertion_all_(AbsInts,Info,A,Key,DomsOut,InfoOut,NewA,-Status).
% TODO: IG: why run abs_exec_size_assertion if there are no domains left?
%%%  At least check if it is a comp assertion?
abs_exec_one_assertion_all_([], [], A, Key, [generic_comp], [AInfoOut], NAOut, StatusOut):-
    abs_exec_comp_assertion(A, Key, AInfo, NA, Status),
    ( Status \== check ->
        AInfoOut = AInfo,
        NAOut = NA,
        StatusOut = Status
    ;
        abs_exec_size_assertion(NA, Key, AInfo1, NAOut, StatusOut),
        append(AInfo, AInfo1, AInfoOut)
    ).
abs_exec_one_assertion_all_([D|Ds], [I|Is], A, Key, DomOut, InfoOut, NewA, Status) :-
    abs_exec_one_assertion(D, I, A, Key, NA ,Flag),
    ( (Flag = false ; Flag = checked) -> DomOut = [D], InfoOut = [I] ; true ),
    ( new_status(Flag,A,_Goal) -> 
        Status = Flag,
        NewA = NA
    ; 
        abs_exec_one_assertion_all_(Ds, Is, NA, Key, DomOut1, InfoOut1, NewA, Status),
        (  Status = check ->
            DomOut = [D|DomOut1], InfoOut = [I|InfoOut1]
        ;
            DomOut = DomOut1, InfoOut = InfoOut1
        )
    ).

% TODO: (check old comment) if expression in abs_execute_one_assertion is reduced and it is different than 'fail', list_to_conj may fail

%------------------------------------------------------------------------------
abs_exec_complete_success(_Goal,_Call,_Succ,_AbsInt,[],nosucc,nosucc,nosucc) :- !.
abs_exec_complete_success(Goal,Call,Succ,AbsInt,
                 [complete(AGoal,ACall,ASuccs,Key,Id)|Cmpls],
                 NCalls,NSuccs,Status):-
    % TODO: infer_dom:abs_execute_with_info/4 works differently for
    % "comp" domains (steps_*, resources, nf, det, etc.). We cannot
    % run checks for calls or success properties using these domains
    % at this stage; NCalls and NSuccs would become "check" when
    % properties properties cannot be verified. Checks for properties
    % belonging to these domains are currently run in later stages of
    % the process (see abs_exec_size_assertion/5 and
    % abs_execute_comp/5).
    \+ buggy_only_comp_dom(AbsInt), !,
    % check if the complete is relevant
    abs_execute_exp(Goal,Call,AbsInt,AGoal,ACall,NCall),
    abs_exec_each_succ(Goal,Call,Succ,AbsInt,AGoal,ASuccs,NCall,
                       LocalNSucc,LocalStatus),
    reduce_compl_fin(LocalStatus,LogStatus),
    assertz_fact(ctchecks_log(AbsInt,LogStatus,success,Key,Id)),               
    ( LocalStatus == true, is_perfect_match(AbsInt,Goal,ACall) ->
        Status = perfect
    ;
        abs_exec_complete_success(Goal,Call,Succ,AbsInt,Cmpls,NCalls0,NSuccs0,Status0),
        reduce_compl(LocalStatus, Status0, Status),
        compose_cs_goals(Status,Call,NCalls0,NCall,NCalls),      % left to prove goals of calls
        compose_cs_goals(Status,Succ,LocalNSucc,NSuccs0,NSuccs)  % left to prove goals of successes
    ).
abs_exec_complete_success(_Goal,Call,Succ,_AbsInt,_Info,NCall,NSucc,dont_know) :-
    % Convert to expected format.
    list_to_conj(Call, NCall),
    list_to_conj(Succ, NSucc).

% checks wether there is an entry exactly matching the precondition,
% in which case the assertion may get status true instaed of checked.
is_perfect_match(Abs,Call,ACall) :- 
    entry_assertion(Call,Entry,_),
    varset(Call,Vs),
    info_to_asub(Abs,_,Entry,Vs,EntryASub,_,no),
    identical_abstract(Abs,ACall,EntryASub).

compose_cs_goals(dont_know,OrigL,G1,G2,Orig) :-
%       G1 \== G2, G2 \== fail, G1 \== fail,!,
    G1 \== G2, G2 \== nosucc, G1 \== nosucc,!,
    list_to_conj(OrigL,Orig).
compose_cs_goals(_Status,Orig,G1,G2,GOut) :-
    synt_compose_disj(Orig,G1,G2,GOut).

:- pred abs_exec_each_succ(+Goal, +AsCall, +AsSucc, +AbsInt, +AGoal, +ComplSuccs, +NCall, -NSucc, -Status).
% IG: ComplSuccs is a list because of multivariant on success

abs_exec_each_succ(_Goal, _Call, _Succ, _AbsInt, _AGoal, _, fail,   true,   true) :- !.
abs_exec_each_succ(_Goal, _Call, _Succ, _AbsInt, _AGoal, [], _NCall, nosucc, nosucc) :- !.
% IG: if '$bottom' in the complete, the predicate never succeeeds and the
% assertion is trivially verified
abs_exec_each_succ(_, _, _, _, _,  ['$bottom'], _NCall, nosucc, nosucc) :- !.
abs_exec_each_succ(Goal, Call, Succ, AbsInt, AGoal, [ASucc|ASuccs], NCall, NSucc, Status):-
    current_pp_flag(pred_ctchecks, Flag), 
    Flag == on_succ, !,
    varset(Goal, Gv),
    varset(ASucc, ASv),
    info_to_asub(AbsInt, _, Call, Gv, Cond, Goal, no), 
    unknown_call(AbsInt, Goal, Gv, Cond, Cond0),
    call_to_entry(AbsInt, Gv, Goal, ASv, AGoal, not_provided, [], Cond0, Cond1, _ExtraInfo), % TODO: add some ClauseKey? (JF)
    glb(AbsInt, Cond1, ASucc, CondASucc),
    ( CondASucc = '$bottom' ->  % no success possible with current Pre, thus this
                                % complete should be "neutral" for the whole assertion
        % TODO: We think this is unreachable; this case is handled
        % before.
        LocalStatus = nosucc,
        NSuccess = fail
    ;
        abs_execute_exp(Goal, Succ, AbsInt, AGoal, CondASucc, NSuccess),
        reduce_success(NCall, NSuccess, LocalStatus0),
        reduce_compl_fin(LocalStatus, LocalStatus0)
    ),
    abs_exec_each_succ(Goal, Call, Succ, AbsInt, AGoal, ASuccs, NCall, NSuccess1, NStatus),  
    reduce_compl_succ(LocalStatus, NStatus ,Status),
    compose_compl_goals(LocalStatus, NStatus, Succ, NSuccess, NSuccess1, NSucc).
abs_exec_each_succ(Goal, Call, Succ, AbsInt, AGoal,  [ASucc|ASuccs], NCall, NSucc, Status):-
    % Case for pred_ctchecks=on. pred_ctchecks=off handled earlier.
    abs_execute_exp(Goal, Succ, AbsInt, AGoal, ASucc, NSuccess),
    reduce_success(NCall, NSuccess, LocalStatus0),
    reduce_compl_fin(LocalStatus, LocalStatus0),
    abs_exec_each_succ(Goal, Call, Succ, AbsInt, AGoal, ASuccs, NCall, NSuccess1, NStatus),  
    reduce_compl_succ(LocalStatus, NStatus ,Status),
    compose_compl_goals(LocalStatus, NStatus, Succ, NSuccess, NSuccess1, NSucc).

compose_compl_goals(S1,S2,Orig,_,_,OrigC):-
    S1 \== S2,
    ( S1 \== dont_know; S2 \== nosucc ),
    ( S2 \== dont_know; S1 \== nosucc ),!,
    list_to_conj(Orig,OrigC).
compose_compl_goals(_,_,Orig,A,B,Out) :-
    synt_compose_disj(Orig,A,B,Out).

%--------------------------------------------------------------------------------
abs_exec_complete_call(_Goal, _Call, res_plai, _, nosucc, nosucc) :- !.  % TODO:[new-resources] avoid to check call for res_plai (temporary MKL) <== remove ad-hoc, add hook if needed (JF)
abs_exec_complete_call(_Goal, _Call, _AbsInt, [], nosucc, nosucc) :- !.
abs_exec_complete_call(Goal, Call, AbsInt, 
                       [complete(AGoal, ACall, _ASuccs,Key,Id)|Cmpls], NCalls, Status):-
    % TODO: infer_dom:abs_execute_with_info/4 works differently for
    % "comp" domains (steps_*, resources, nf, det, etc.). We cannot
    % run checks for calls or success properties (directly) using
    % these domains; NCalls would become "check" when properties
    % cannot be verified. Checks for properties belonging to these
    % domains are currently run in later stages of the process (see
    % abs_exec_size_assertion/5 and abs_execute_comp/5).
    \+ buggy_only_comp_dom(AbsInt), !,
    abs_execute_exp(Goal, Call,  AbsInt, AGoal, ACall, NCall),
    reduce_calls(NCall,SingleStatus0),
    assertz_fact(ctchecks_log(AbsInt,SingleStatus0,calls,Key,Id)),
    reduce_compl_fin(SingleStatus,SingleStatus0),
    abs_exec_complete_call(Goal, Call, AbsInt, Cmpls, NCalls0, Status0),
    synt_compose_disj(Call, NCall,NCalls0,NCalls), 
    reduce_compl(SingleStatus, Status0, Status).
abs_exec_complete_call(_Goal, Call, _AbsInt, _Info, NCall, dont_know) :-
    % Convert to expeced format.
    list_to_conj(Call, NCall).

%--------------------------------------------------------------------------------
:- export(abs_exec_one_assertion/6).
abs_exec_one_assertion(_AbsInt, [], A, _Key, NA, checked) :- !,
    assertion_set_status(A, checked, NA).
% IG: if there are no completes, it means that the predicate is unreachable in
% that domain and everything is trivially checked.
abs_exec_one_assertion(AbsInt, Cmpls, A, _Key, NA, Status) :-
    A = as${status=>check, type=>success, head=>Goal, call=>Call, succ=>Success},
    !,
    abs_exec_complete_success(Goal, Call, Success, AbsInt, Cmpls, NCall, NSuccess, Status0),
    reduce_compl_fin(Status0,Status),
    % We update the assertion with the simplified pre and post to
    % output better messages. For false and checked status, original
    % assertion is output.
    ( Status = check ->
        A = A2
    ; assertion_set_status(A, Status, A2)
    ),
    list_to_conj(OCall, NCall),
    list_to_conj(OSuccess, NSuccess),
    assertion_set_calls(A2, OCall, A3),
    assertion_set_success(A3, OSuccess, NA).
abs_exec_one_assertion(AbsInt, Cmpls, A, _Key, NA, Status) :-
    A = as${ status=>check, type=>calls, head=>Goal,call=>Call},
    !,
    abs_exec_complete_call(Goal, Call, AbsInt, Cmpls, NCall, Status0),
    reduce_compl_fin(Status0, Status1),
    ( current_pp_flag(client_safe_ctchecks, on),
      Status1 = checked, type_of_goal(exported, Goal) ->
        % Do not mark as check calls assertions of exported predicates
        Status = check
    ; Status = Status1
    ),
    ( Status = check ->
        list_to_conj(NNCall, NCall),
        assertion_set_calls(A, NNCall, NA)
    ;
        assertion_set_status(A, Status, NA)
    ).
abs_exec_one_assertion(AbsInt, Cmpls, A, _Key, NA, Status) :-
    A = as${ status=>check, type=>comp, head=>Goal, call=>Call},
    !,
    abs_exec_complete_call(Goal, Call, AbsInt, Cmpls, NCall, _Status0),
    Status = check,
    list_to_conj(NNCall, NCall),
    assertion_set_calls(A, NNCall, NA).

abs_exec_comp_assertion(A, _Key, AComp, NA, Status) :-
    A = as${ status=>check, type=>comp, head=>Goal, call=>Call, comp=>Comp},
%       format("Assertion:~n~p",[A]),nl,nl,
%       displayq([Call,OrigCall,Success,OrigSuccess]),nl,
    abs_execute_comp(Goal, Comp,  AComp, NComp, Status0),
    list_to_conj(Call,CCall),
    reduce_comp(CCall,Status0,Status),
    !, % TODO: where should be this cut?
%       list_to_conj(NNComp,NComp),
    assertion_set_status(A, Status, A2),
    assertion_set_comp(A2, NComp, NA).
abs_exec_comp_assertion(A,_Key,[],A,check).

abs_exec_size_assertion(A, _Key, ASize, NA, Status) :- % TODO: missing cut?
    A = as${ status=>check, type=>success, head=>Goal, call=>Call,succ=>Success},
    abs_execute_sizes(Goal, Success,  ASize, NSuccess, Status0),
    list_to_conj(Call,CCall),
    reduce_comp(CCall,Status0,Status),
%       list_to_conj(NNComp,NComp),
    assertion_set_status(A, Status, A2),
    assertion_set_success(A2, NSuccess, NA).
abs_exec_size_assertion(A,_Key,[],A,check).

abs_execute_exp(Goal, Exp, AbsInt, AGoal, Info_u, NewExp):-
    varset(Goal, Vars),
    abs_execute(AbsInt, Goal, Exp, AGoal, Vars, Info_u, NewExp).

synt_compose_disj(_, Exp1,Exp2,NewExp):-
    Exp1 == Exp2,!,
    NewExp = Exp1.
synt_compose_disj(_,nosucc,A,A) :-!.
synt_compose_disj(_,A,nosucc,A) :-!.
synt_compose_disj(Orig, _NewExp1, _NewExp2, Orig).

new_status(Flag,_,_):-
    Flag \== check,
    !.

buggy_only_comp_dom(nf).
buggy_only_comp_dom(det).
buggy_only_comp_dom(res_plai).

reduce_calls(  true  , checked ) :- !.  % -
reduce_calls(  fail  , false   ) :- !.  % +
reduce_calls( _Calls , check   ).

reduce_success( fail , _Success , check   ) :- !. % -
reduce_success( true , fail     , false   ) :- !. % -
reduce_success( _Call, true     , checked ) :- !. % +
reduce_success( _    , _        , check   ).

% PP: Commented out for a while...
% reduce_comp( fail  , _Comp , check   ) :- !.  % ??? was 'checked' in the old version
reduce_comp( _Call , true  , checked ) :- !.
reduce_comp( _     , fail  , false   ) :- !.
reduce_comp( _Call , Comp  , Comp    ).

reduce_compl(true, true, true) :- !.
reduce_compl(fail , fail, fail) :- !.  
reduce_compl(nosucc, S, S) :- !. 
reduce_compl(S, nosucc, S) :- !. 
reduce_compl(_, _, dont_know).

reduce_compl_succ(true, true, true) :- !. 
reduce_compl_succ(fail, fail, fail) :- !. 
reduce_compl_succ(nosucc, S, S) :- !. 
reduce_compl_succ(S, nosucc, S) :- !. 
reduce_compl_succ(_, _, dont_know).

reduce_compl_fin(perfect, checked) :- !.
reduce_compl_fin(true, checked) :- !.
reduce_compl_fin(fail, false) :- !.
reduce_compl_fin(nosucc, checked) :- !.
reduce_compl_fin(dont_know, check).
