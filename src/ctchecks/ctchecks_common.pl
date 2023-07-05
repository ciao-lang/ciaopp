:- module(ctchecks_common, [
    abs_exec_one_assertion_all/7,
    check_type_calls/2,
    ctchecks_log/5,
    clear_log/0,
    get_check_assertion/3,
%%      num_var_in_goal/4,
    pp_check/2
%       native_props/2  %% GP: exported for use in ctchecks.pl. Is this OK?
], [assertions, regtypes, isomodes, nativeprops, datafacts]).

:- use_package(library(compiler/p_unit/p_unit_argnames)).

:- use_module(library(lists), [append/3]).
:- use_module(library(formulae), [list_to_conj/2, list_to_disj/2]).
:- use_module(library(messages), [debug_message/2]).
:- use_module(library(aggregates), [findall/3]).

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(library(compiler/p_unit), [type_of_goal/2]).
:- use_module(library(compiler/p_unit/p_unit_db), [curr_file/2, ref_assertion_read/10]).
:- use_module(library(compiler/p_unit/unexpand), [transform_metapred/3]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(plai/domains),
              [asub_to_info/5,glb/4,info_to_asub/7,unknown_call/5,
               call_to_entry/10,identical_abstract/3,needs/2,project/6]).
:- use_module(library(assertions/assrt_lib), [prop_unapply/3]).
:- use_module(library(compiler/p_unit),
              [assertion_set_status/3, assertion_set_calls/3,
               assertion_set_success/3, assertion_set_comp/3,
               prop_to_native/2]).
:- use_module(ciaopp(frontend_driver), [entry_assertion/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(ciaopp(ctchecks/comp_ctchecks),
              [abs_execute_comp/5, abs_execute_sizes/5]).
:- use_module(ciaopp(infer/infer_dom),   [abs_execute/7,knows_of/2]).

:- use_module(spec(abs_exec_ops), [adapt_info_to_assrt_head/6]).

:- use_module(typeslib(typeslib), [pretty_type_lit_rules_desimp/2, equiv_type/2]).

%[LD] for interval
%:- use_module(ciaopp(preprocess_flags),[current_pp_flag/2]).
:- if(defined(has_ciaopp_cost)).
:- use_module(infercost(algebraic/polynom_comp),[polynom_current_assertion/1]).
:- endif.
%[/LD] for interval

check_type_calls(Goal,Calls):-
    type_of_goal(imported,Goal),
    get_entrycalls_assertion(calls,Goal,Calls,_),
    nonvar(Calls).

pp_check(CGoal,Props):-
    curr_file( _, M ),
    transform_metapred( CGoal, M, Goal ),
    type_of_goal(builtin(check(Props)),Goal).

% ----------------------------------------------------------------------
%! # Assertion Reading

:- pred get_check_assertion(+Goal,-Assertion,-Refs)
   # "Returns @tt{check} assertion @var{Assertion} of type @var{Type}
     referring to @var{Goal}. @var{Refs} is a list of references to
     the assertion.".

get_check_assertion(Goal,Entry,Refs) :-
    ( type_of_goal(imported,Goal) -> true ),
    get_entrycalls_assertion(entry,Goal,Entry,Refs),
    nonvar(Entry),
    debug_message("entry assertion found ~q",[Entry]).
get_check_assertion(Goal,Calls,Refs) :-
    get_entrycalls_assertion(calls,Goal,Calls,Refs),
    nonvar(Calls),
    debug_message("calls assertion found ~q",[Calls]).
get_check_assertion(Goal,Assertion,Refs) :-
    Status = check,
    ( Type = success
    ; Type = comp
    ),
    ref_assertion_read(Goal, M, Status, Type, Body, Dic, S, LB, LE, ARef),
    rebuild_assertion(M, Status, Type, Body, Dic, S, LB, LE, Assertion),
    Refs = [ARef],
    debug_message("~q assertion found ~q",[Type,Assertion]).

rebuild_assertion(M, Status, Type, Body, Dic, S, LB, LE, A) :-
    A = as(M,Status,Type,Key,Compat,Call,Succ,Comp,Dic,Loc,Comment,_),
    Loc = loc(S, LB, LE),
    assertion_body(Key, Compat, Call, Succ, Comp, Comment, Body).

get_entrycalls_assertion(Type,Goal,Calls,Refs):-
    ref_assertion_read(Goal,_,Status0,Type,_Body,_Dict,_S,_LB,_LE,_),
    % TODO: Why are `true` assertions considered here?
    ( Type = entry ->
        true
    ; current_pp_flag(run_diagnosis,on) ->
        member(Status0,[check, false]), LS = [true,check,trust,false]
    ; member(Status0,[check]), LS = [true,check,trust]
    ),
    !,
    findall( (Assertion,ARef),
             ( ref_assertion_read(Goal, M, Status, Type, Body, Dic, S, LB, LE, ARef),
               ( Type = entry ->
                   true
               ; member(Status,LS)
               ),
               rebuild_assertion(M, Status, Type, Body, Dic, S, LB, LE, Assertion) ),
             Calls0 ),
    group_calls(Calls0,Calls,Refs).

group_calls(Group,A1,Refs):-
    group_calls_(Group,A0,Refs),
    A0 = as(M,Status,Type,Key,Compat,Call0,Succ,Comp,Dic,Loc,Comment,FromWhere),
    list_to_disj_(Call0, Call1),
    ( Call1 = true ->
        Call = []
    ; Call = [Call1]
    ),
    A1 = as(M,Status,Type,Key,Compat,Call,Succ,Comp,Dic,Loc,Comment,FromWhere).

group_calls_([(A0,ARef)],A1,[ARef]):- !,
    A0 = as(M,Status,Type,Key,Compat,Call0,Succ,Comp,Dic,Loc,Comment,FromWhere),
    group_calls__(Call0, [], Call),
    A1 = as(M,Status,Type,Key,Compat,Call,Succ,Comp,Dic,Loc,Comment,FromWhere).
group_calls_([(A,ARef)|More],A1,[ARef|Refs]):-
    group_calls_(More,A0,Refs),
    A0 = as(M,Status,Type,Key,Compat,Call0,Succ,Comp,Dic,Loc,Comment,FromWhere),
    A = as(_M,_Status,_Type,_Key,_Compat,Call1,_Succ,_Comp,Dic,_Loc,_Comment,_FromWhere),
    group_calls__(Call1, Call0, Call),
    A1 = as(M,Status,Type,Key,Compat,Call,Succ,Comp,Dic,Loc,Comment,FromWhere).

group_calls__([],   Calls0, Calls1) :- !, Calls1 = Calls0.
group_calls__(Call, Calls0, Calls1) :-    Calls1 = [Call|Calls0].

list_to_disj_([], true) :- !.
list_to_disj_(L,  Disj) :- list_to_disj(L, Disj).

% ----------------------------------------------------------------------
%! # Abstract Execution

:- data ctchecks_log/5.
:- pred ctchecks_log(?Abs,?Status,?Type,?Key,?Id) + no_rtcheck #
    "Returns upon backtracking completes (@var{Key}+@var{Id}+@var{Abs})
     which participated during CT checking in giving assertion of
     type @var{Type} (calls, success or comp) status @var{check}.".

clear_log :- retractall_fact(ctchecks_log(_,_,_,_,_)).

:- pred abs_exec_one_assertion_all(+AbsInts, +Info, +A, +Key,
                                   -DomsOut, -InfoOut, -NA).

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
% Begin MR !433
% TODO: Factorize with abs_exec_complete_success
abs_exec_complete_comp(_Goal, _Call, _Comp, _AbsInt, [],
                       nosucc, nosucc, nosucc) :- !.
abs_exec_complete_comp(Goal, Call, Comp, AbsInt,
                       [complete(AGoal,ACall,ASuccs,Key,Id)|Cmpls],
                       NCalls, NComp, Status) :- !,
    abs_execute_exp(Goal, Call, AbsInt, AGoal, ACall, NCall),
    abs_exec_each_comp(Goal, Call, Comp, AbsInt, AGoal, ASuccs, NCall,
                       LocalNComp, LocalStatus),
    reduce_compl_fin(LocalStatus, LogStatus),
    assertz_fact(ctchecks_log(AbsInt,LogStatus,comp,Key,Id)),
    ( LocalStatus == true, is_perfect_match(AbsInt, Goal, ACall) ->
        Status = perfect
    ; abs_exec_complete_comp(Goal, Call, Comp, AbsInt, Cmpls, NCalls0, NComp0,
                             Status0),
      reduce_compl(LocalStatus, Status0, Status),
      compose_cs_goals(Status,Call,NCalls0,NCall,NCalls),    % left to prove goals of calls
      compose_cs_goals(Status,Comp,LocalNComp,NComp0,NComp)  % left to prove goals of comp
    ).
abs_exec_complete_comp(_Goal, Call, Comp, _AbsInt, _Info, NCall, NComp, dont_know) :-
    % Convert to expected format.
    list_to_conj(Call, NCall),
    list_to_conj(Comp, NComp).

abs_exec_each_comp(Goal, Call, Comp, AbsInt, AGoal, [AComp|AComps], NCall, NComp, Status):-
    current_pp_flag(pred_ctchecks, Flag), 
    Flag == on_succ, !,
    varset(Goal, Gv),
    varset(AComp, ASv),
    info_to_asub(AbsInt, _, Call, Gv, Cond, Goal, no), 
    unknown_call(AbsInt, Goal, Gv, Cond, Cond0),
    call_to_entry(AbsInt, Gv, Goal, ASv, AGoal, not_provided, [], Cond0, Cond1, _ExtraInfo), % TODO: add some ClauseKey? (JF)
    glb(AbsInt, Cond1, AComp, CondAComp),
    ( CondAComp = '$bottom' ->
        LocalStatus = nosucc,
        NC = fail
    ; abs_execute_exp(Goal, Comp, AbsInt, AGoal, CondAComp, NC),
      reduce_success(NCall, NC, LocalStatus0),
      reduce_compl_fin(LocalStatus, LocalStatus0)
    ),
    abs_exec_each_comp(Goal, Call, Comp, AbsInt, AGoal, AComps, NCall, NC1, NStatus),  
    reduce_compl_succ(LocalStatus, NStatus ,Status),
    compose_compl_goals(LocalStatus, NStatus, Comp, NC, NC1, NComp).
abs_exec_each_comp(Goal, Call, Comp, AbsInt, AGoal, [AComp|AComps], NCall, NComp, Status):-
    abs_execute_exp(Goal, Comp, AbsInt, AGoal, AComp, NC),
    reduce_success(NCall, NC, LocalStatus0),
    reduce_compl_fin(LocalStatus, LocalStatus0),
    abs_exec_each_succ(Goal, Call, Comp, AbsInt, AGoal, AComps, NCall, NC1, NStatus),  
    reduce_compl_succ(LocalStatus, NStatus ,Status),
    compose_compl_goals(LocalStatus, NStatus, Comp, NC, NC1, NComp).
% End MR !433
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
% Begin MR !433    
%   A = as${ status=>check, type=>comp, head=>Goal, call=>Call},
    A = as${ status=>check, type=>comp, head=>Goal, call=>Call, comp=>Comp}, 
    !,
%   abs_exec_complete_call(Goal, Call, AbsInt, Cmpls, NCall, _Status0),
%   Status = check,
%   list_to_conj(NNCall, NCall),
%   assertion_set_calls(A, NNCall, NA).
    abs_exec_complete_comp(Goal, Call, Comp, AbsInt, Cmpls, NCall, NComp, Status0),
    reduce_compl_fin(Status0, Status),
    ( Status = check ->
        list_to_conj(OCall, NCall),
        list_to_conj(OComp, NComp),
        assertion_set_calls(A, OCall, A2),
        assertion_set_comp(A2, OComp, NA)
    ; assertion_set_status(A, Status, NA)
    ).
% End MR !433
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

% Begin MR !433
% TODO: Make res_plai use the default algorithm instead of
% comp_ctchecks one, which should only be used for non-plai domains.
buggy_only_comp_dom(res_plai).
% buggy_only_comp_dom(nf).
% buggy_only_comp_dom(det).
% End MR !433

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

% ----------------------------------------------------------------------
%! # Status Count

:- export(memo_ctcheck_sum/1).
memo_ctcheck_sum(false) :-
    retract_fact(is_any_false(_)),
    asserta_fact(is_any_false(yes)).
memo_ctcheck_sum(check) :-
    retract_fact(is_any_check(_)),
    asserta_fact(is_any_check(yes)).

:- export(is_any_false/1).
:- export(is_any_check/1).

:- data is_any_false/1.
:- data is_any_check/1.

is_any_false(no).
is_any_check(no).

:- export(init_ctcheck_sum/0).
init_ctcheck_sum :-
    retractall_fact(is_any_false(_)),
    retractall_fact(is_any_check(_)),
    asserta_fact(is_any_false(no)),
    asserta_fact(is_any_check(no)),
    cleanup_polynom_message.

% ----------------------------------------------------------------------
%! # Message Formatting

:- if(defined(has_ciaopp_cost)).
:- use_module(ciaopp(ctchecks/ctchecks_intervals), [cleanup_polynom_message/0]).
:- else.
cleanup_polynom_message.
:- endif.

:- export(prepare_output_info/5).
:- pred prepare_output_info(+AbsInts,+,+Head,+Type,-Info)
   : list(AbsInts) => list(Info) + not_fails.
prepare_output_info([],[],_Head,_Type,[]) :-!.
prepare_output_info([D|Ds],[I|Is],H,Type,AInfoOut) :-
    trans_aux(Type,D,H,I,A),
    ( % TODO: Workaround: abstract substitutions from combined domains
      % carry additional information not used to verify types, leading
      % to an error in collect_rules/4.
      \+ needs(D,split_combined_domain),
      knows_of(regtypes,D),
      \+ A = [[bottom]] ->   % (\=)/2 is not a builtin???
        collect_rules(H,A,ReqRules,A1)
    ; ReqRules = [],
      A1 = A
    ),
    ( A1 = [] ->
        AInfoOut = AInfo
    ; AInfoOut = ['$dom'(D,A1,ReqRules)|AInfo]
    ),
    prepare_output_info(Ds,Is,H,Type,AInfo).

% collect type rules for each and every complete
collect_rules(G,Info,Rules,NewInfo):-
    collect_rules_all(G,Info,[],Rules,NewInfo).

collect_rules_all(_G,[],R,R,[]) :- !.
collect_rules_all(G,[I|Is],RIn,ROut,[NewI|NewIs]) :-
    copy_term((G,I),(CG,CI)),
    inline_types(CI),
    pretty_type_lit_rules_desimp(CG,Rules),
    filter_required_rules(Rules,RIn,RInter),
    replace_equiv(I,NewI),
    collect_rules_all(G,Is,RInter,ROut,NewIs).

replace_equiv((A,B),(A1,B1)) :- !,
    replace_equiv(A,A1),
    replace_equiv(B,B1).
replace_equiv(A,B) :-
    A =.. [T,Arg],
    equiv_type(T,ET),
    B =.. [ET,Arg],
%       prop_to_native(B,regtype(_Prop)), % not inferred
    !.
replace_equiv(A,A).

% a bit different from that in ctchecks_pp_messages.pl
filter_required_rules([typedef(::=(T,_))|Ds],Rs,RsOut):-
    ( functor(G,T,1), prop_to_native(G,regtype(_Prop)) % not inferred
    ; equiv_type(T,_)               % an equivalent type will be shown 
    ), 
    !, 
    filter_required_rules(Ds,Rs,RsOut).
filter_required_rules([R|Ds],Rs,RsOut):-
    member(R,Rs),!,                    % already in
    filter_required_rules(Ds,Rs,RsOut).
filter_required_rules([R|Rs],RIn,ROut):-
    filter_required_rules(Rs,[R|RIn],ROut).
filter_required_rules([],Rs,Rs).

trans_aux(comp,generic_comp,_Goal,[],[['No info available']]) :-!.
trans_aux(_ ,_ ,_, [],[]) :-!.
trans_aux(comp,generic_comp,_Goal,I,I):-!. % PLG. To show a message when an assertion
                                           % involving steps_ub/lb/o has been found false.
trans_aux(calls,AbsInt,Head,[complete(G,C,_Ss,_,_)|Completes],[CInfo1|CInfo]):-!,   
    varset(G,Qv),
    adapt_info_to_assrt_head(AbsInt,G,Qv,C,Head,C1),
    my_asub_to_info(AbsInt,C1,Qv,CInfo1,_Comp),
    trans_aux(calls,AbsInt,Head,Completes,CInfo).
% MR !433 -> Generalized to Type (success or comp), was only success. 
trans_aux(Type,AbsInt,Head,[complete(G,_C,Ss,_,_)|Completes],SInfoL):-
    (Type = success ; Type = comp), !,
    collect_succcomp_info(Ss,Type,AbsInt,Head,G,SInfoL1),
    append(SInfoL1,SInfoL2,SInfoL),
    trans_aux(Type,AbsInt,Head,Completes,SInfoL2).
trans_aux(success,_,_Goal,Info,Info):-!.  % for size properties

% Begin MR !433 -> Added a new argument Type.
collect_succcomp_info([],_Type,_AbsInt,_Head,_G,[]).
collect_succcomp_info([S|Ss],Type,AbsInt,Head,G,[SInfo|SInfoTail]):-
    varset(G,Qv),
    adapt_info_to_assrt_head(AbsInt,G,Qv,S,Head,S_tmp),
    varset(Head,Hv),
    project(AbsInt,Head,Hv,[],S_tmp,S1),
    my_asub_to_info(AbsInt,S1,Qv,Succ,Comp), 
    select_most_useful_info(Type,Succ,Comp,SInfo),
    collect_succcomp_info(Ss,Type,AbsInt,Head,G,SInfoTail). 

% No info is no useful.
select_most_useful_info(_,[],Comp,Out) :- !, Out = Comp.
select_most_useful_info(_,Succ,[],Out) :- !, Out = Succ.
% If we have both kinds of info, take into account type.
select_most_useful_info(success,Succ,_Comp,Out) :- !, Out = Succ.
select_most_useful_info(comp,_Succ,Comp,Out) :- Out = Comp.
% End MR !433

% my_asub_to_info(_AbsInt,'$bottom',_Qv,[bottom],_Comp):-!.
my_asub_to_info(_AbsInt,'$bottom',_Qv,[bottom],[bottom]):-!. % Added in MR !433
my_asub_to_info(AbsInt,S1,Qv,SInfo,Comp):-
    asub_to_info(AbsInt,S1,Qv,SInfoL,Comp),!,
    list_to_conj(SInfoL,SInfo).

% TODO: why is that different than ctchecks_pp_messages:inline_types?
inline_types([bottom]) :-!.
inline_types(true) :-!.
inline_types((Prop,Props)):- !,
    inline_types(Prop),
    inline_types(Props).
inline_types(Prop):-
    prop_unapply(Prop,P,P).

:- export(name_vars/1).
name_vars([]).
name_vars([V='$VAR'(V)|Vs]):-
    name_vars(Vs).
