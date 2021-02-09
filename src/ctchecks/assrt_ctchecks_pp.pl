:- module(assrt_ctchecks_pp, [pp_compile_time_prog_types/3], [assertions]).

:- use_module(library(lists), [member/2]).
:- use_module(library(formulae), [list_to_conj/2]).
:- use_module(library(messages), [debug_message/1, debug_message/2]).
:- use_module(library(vndict), [rename/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(runtime_control), [module_split/3]).

:- use_module(library(counters)).

:- use_module(spec(abs_exec_ops), [adapt_info_to_assrt_head/6]).

% CiaoPP library
:- use_module(ciaopp(infer), [get_memo_lub/5]).
:- use_module(ciaopp(infer/infer_dom), [abs_execute_with_info/4]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(spec(s_simpspec), 
              [next_pred/2, body2list/2, next_or_last_key/3]).
%% :- use_module(spec(abs_exec), [cond/4]).

% Own library
:- use_module(ciaopp(ctchecks/assrt_ctchecks_common), 
    [
%%        num_var_in_goal/4,
      get_calls_assertion/4,
      get_entry_assertion/4,
      pp_check/2,
      synt_compose_disj/3,
      synt_compose_conj/3,
      synt_compose_list/3
%%        statically_comp/4
    ]).
:- use_module(ciaopp(ctchecks/ctchecks_messages), 
    [ 
      message_pp_calls/8,
      message_pp_entry/8,
      message_pp_success/9,
      message_pp_check/6,
      message_clause_incompatible/5
    ]).
:- use_module(ciaopp(ctchecks/preproc_errors), [preproc_warning/2]).
:- use_module(ciaopp(ctchecks/diagnosis/diag), [how/6]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

%% :- multifile term_domain/1.

%-------------------------------------------------------------------%
:- doc(bug,"1. When a goal fails, no assertion is shown saying this.
    In 0.8 we had this feature.").
%-------------------------------------------------------------------%

pp_compile_time_prog_types([],[],_).
% Directives do not have program points                       %
pp_compile_time_prog_types([directive(_Dir):_Id|Cs],[_D|Dicts],Abs):-
    pp_compile_time_prog_types(Cs,Dicts,Abs).
pp_compile_time_prog_types([clause(H,Body):Clid|Cs],[Dict|Dicts],Abs):-
    pp_compile_time_check_types(Body,H,Clid,Dict,Abs),
    pp_compile_time_prog_types(Cs,Dicts,Abs).

% call type incompatible with head of the clause
pp_compile_time_check_types(Body,H,Clid,dic(Vars,Names),[Types,_]):-
    (Body = ((_:K),_); Body = (_:K)),
    decide_get_just_info(Types,K,Vars,TypesInfo),
    are_bottom(TypesInfo,none),!,
    message_clause_incompatible(Clid,Types,H,Vars,Names).
% The clause is a fact                                        %
pp_compile_time_check_types(true,_H,_Clid,_Dict,_Abs):- !.
% The body is just a cut                                      %
pp_compile_time_check_types(!,_H,_Clid,_Dict,_Abs):- !.
% Rest of clauses. We try to simplify its body                %
pp_compile_time_check_types(Body,_H,_Clid,dic(Vars,Names),Abs):-
    body2list(Body,Blist),
    next_pred(Blist,Pred),
    pp_ct_body_list_types(Pred,Blist,Vars,Names,Abs).

%-------------------------------------------------------------%
%-------------------------------------------------------------%

prepare_info_pp(_,none,MInfo,Modes,MInfo,Modes) :- !.
prepare_info_pp(TInfo,Types,_,_,TInfo,Types).

pp_ct_body_list_types(none,[],_,_,_).
pp_ct_body_list_types((!/0),[!:_|Goals],Vars,Names,Abs):-!,
    next_pred(Goals,Pred),
    pp_ct_body_list_types(Pred,Goals,Vars,Names,Abs).
% This goal is a program point assertion                      %
pp_ct_body_list_types(_FA,[Goal:K|Goals],Vars,Names,Abs):-
    pp_check(Goal,Prop),!,
    pp_ct_check_assertion(Prop,K,Vars,Names,Abs),
    next_pred(Goals,NPred),
    pp_ct_body_list_types(NPred,Goals,Vars,Names,Abs).
% Goal is a builtin whose call is violated using type info    %
%
% pp_ct_body_list_types(F/A,[(Goal:K)|_],Vars,Names,[Types,Modes]):-
%       functor(Builtin,F,A),
%       check_type_calls(Builtin,Calls),
%       copy_term(Builtin,CopyBuiltin),
%       decide_get_applicable_info(Types,K,Vars,CopyBuiltin,Goal,TypesInfo),
%       decide_get_applicable_info(Modes,K,Vars,CopyBuiltin,Goal,ModesInfo),
%       not_already_bottom(TypesInfo,ModesInfo),
%       decide_abs_execute(Types,Goal,Calls,Goal,TypesInfo,TNewInfo,NCalls),
%       (NCalls == true -> inccounter(pp_checked_c,_), fail; true),
%         ( NCalls == fail ->
%         message_pp_builtin(TNewInfo,Types,Builtin,Calls,dic(Vars,Names),K),
%         inccounter(pp_false_c,_)
%       ;
%       decide_abs_execute(Modes,Goal,NCalls,Goal,ModesInfo,_,Fail),
%         ( Fail == fail ->
%           message_pp_builtin(ModesInfo,Modes,Goal,Calls,dic(Vars,Names),K),
%           inccounter(pp_false_c,_)
%       ;  (Fail == true -> inccounter(pp_checked_c,_) ; inccounter(pp_check_c,_)), 
%           fail
%       )).
%
% Violation of an "entry" assertion                      %
pp_ct_body_list_types(F/A,[(Goal:K)|_],Vars,_Names,[Types,Modes]):-
    curr_file(_,M),
    functor(Head,F,A),
    \+ module_split(F, M, _), % make sure that we have an imported predicate
%       displayq(Head),nl,
    get_entry_assertion(Head,pp,Calls,Dict),
%       get_calls_assertion(Goal,pp,Calls,Dict),
    nonvar(Calls),
    debug_message("calls assertion found ~q",[Calls]),
    copy_term(Head,CopyHead),
    decide_get_applicable_info(Types,K,Vars,CopyHead,Goal,TypesInfo),
    decide_get_applicable_info(Modes,K,Vars,CopyHead,Goal,ModesInfo),
    not_already_bottom(TypesInfo,ModesInfo),
    decide_abs_execute(Types,Goal,Calls,Head,TypesInfo,_TNewInfo,NCalls),
    ( NCalls == true -> 
        message_pp_entry(TypesInfo,Types,Goal,Head,Calls,Dict,K,checked),
        inccounter_cond(pp_checked_c,Calls), 
        fail
    ; 
        true
    ),
    (NCalls == fail ->
        message_pp_entry(TypesInfo,Types,Goal,Head,Calls,Dict,K,false),
        local_inccounter(pp_false_c,_)
    ;
        decide_abs_execute(Modes,Goal,NCalls,Head,ModesInfo,_,Fail),
        ( Fail == fail ->
            message_pp_entry(ModesInfo,Modes,Goal,Head,Calls,Dict,K,false),
            local_inccounter(pp_false_c,_)
        ;
            ( Fail == true -> 
                message_pp_entry(TypesInfo,Types,Goal,Head,Calls,Dict,K,checked),
                inccounter_cond(pp_checked_c,Calls) 
            ; 
                prepare_info_pp(TypesInfo,Types,ModesInfo,Modes,Info,Abs),
                message_pp_entry(Info,Abs,Goal,Head,Calls,Dict,K,check),
                local_inccounter(pp_check_c,_)
            ),
            fail
        )
    ).
%
% Violation of a "check calls" assertion                      %
pp_ct_body_list_types(F/A,[(Goal:K)|_],Vars,_Names,[Types,Modes]):-
    functor(Head,F,A),
    get_calls_assertion(Head,pp,Calls,Dict),
%       get_calls_assertion(Goal,pp,Calls,Dict),
    nonvar(Calls),
    debug_message("calls assertion found ~q",[Calls]),
    copy_term(Head,CopyHead),
    decide_get_applicable_info(Types,K,Vars,CopyHead,Goal,TypesInfo),
    decide_get_applicable_info(Modes,K,Vars,CopyHead,Goal,ModesInfo),
    not_already_bottom(TypesInfo,ModesInfo),
    decide_abs_execute(Types,Goal,Calls,Head,TypesInfo,_TNewInfo,NCalls),
    (NCalls == true -> 
        inccounter_cond(pp_checked_c,Calls), 
        message_pp_calls_diag(TypesInfo,Types,Goal,Head,Calls,Dict,K,checked),
        fail
    ; 
        true),
    (NCalls == fail ->
        message_pp_calls_diag(TypesInfo,Types,Goal,Head,Calls,Dict,K,false),
        local_inccounter(pp_false_c,_)
    ;
         decide_abs_execute(Modes,Goal,NCalls,Head,ModesInfo,_,Fail),
         ( Fail == fail ->
             message_pp_calls_diag(ModesInfo,Modes,Goal,Head,Calls,Dict,K,false),
             local_inccounter(pp_false_c,_)
        ;
           ( Fail == true -> 
               message_pp_calls_diag(ModesInfo,Modes,Goal,Head,Calls,Dict,K,checked),
               inccounter_cond(pp_checked_c,Calls) 
           ; 
               prepare_info_pp(TypesInfo,Types,ModesInfo,Modes,Info,Abs),
               message_pp_calls_diag(Info,Abs,Goal,Head,Calls,Dict,K,check),
               local_inccounter(pp_check_c,_)
           )
        )
    ),
    fail.
%
% Violation of a "check success" assertion                    %
pp_ct_body_list_types(F/A,[(Goal:K)|Goals],Vars,_Names,[Types,Modes]):-
    functor(Head,F,A),
    assertion_read(Head,_M,AStatus,success,Body,Dict,_Source,_LB,_LE),
    member(AStatus,[check]),
    assertion_body(Head,_Compat,Calls0,Succ0,_Comp,_Comm,Body),
    debug_message("success assertion found ~q",[Succ]),
    check_precond([Types,Modes],Head,K,Vars,Goal,Calls0),
    next_or_last_key(Goals,K,K1),
    copy_term(Head,CopyHead),
    decide_get_applicable_info(Types,K1,Vars,CopyHead,Goal,TypesInfo),
    decide_get_applicable_info(Modes,K1,Vars,CopyHead,Goal,ModesInfo),
    not_already_bottom(TypesInfo,ModesInfo),
    list_to_conj(Succ0,Succ),
    decide_abs_execute(Types,Goal,Succ,Head,TypesInfo,_TNewInfo,NSucc),
    ( NSucc == true -> 
        inccounter_cond(pp_checked_s,Succ0), 
        message_pp_success_diag(TypesInfo,Types,Goal,Head,Calls0,Succ0,Dict,K,checked),
        fail
    ; 
        true
    ),
    (NSucc == fail ->
        message_pp_success_diag(TypesInfo,Types,Goal,Head,Calls0,Succ0,Dict,K,false),
        local_inccounter(pp_false_s,_)
    ;
        decide_abs_execute(Modes,Goal,NSucc,Head,ModesInfo,_MNewInfo,Fail),
        (Fail == fail ->
            message_pp_success_diag(ModesInfo,Modes,Goal,Head,Calls0,Succ0,Dict,K,false),
            local_inccounter(pp_false_s,_)
        ;
            debug_message("NO DETECTADO"),
            ( Fail == true -> 
              inccounter_cond(pp_checked_s,Succ0) ,
              message_pp_success_diag(ModesInfo,Modes,Goal,Head,Calls0,
                                 Succ0,Dict,K,checked)
            ; prepare_info_pp(TypesInfo,Types,ModesInfo,Modes,Info,Abs),
              message_pp_success_diag(Info,Abs,Goal,Head,Calls0,Succ0,Dict,K,check),
              local_inccounter(pp_check_s,_)
            )
        )
       ),fail.

% Goal has bottom as success substitution                     %
pp_ct_body_list_types(_P,[(Goal:K)|Goals],Vars,Names,[Types,Modes]):-
    Goal\== 'basiccontrol:fail', Goal\== 'basiccontrol:false',
    debug_message("checking if bottom for ~q",[Goal]),
    decide_get_just_info(Types,K,Vars,TypesInfo),
    decide_get_just_info(Modes,K,Vars,ModesInfo),
    not_already_bottom(TypesInfo,ModesInfo),
    next_or_last_key(Goals,K,K1),
    decide_get_just_info(Types,K1,Vars,TypesInfo1),
    decide_get_just_info(Modes,K1,Vars,ModesInfo1),
    are_bottom(TypesInfo1,ModesInfo1), !,
    copy_term((Goal,dic(Vars,Names)),(NGoal,Dict)),
    rename(NGoal,Dict),
    preproc_warning(always_fails,[NGoal,K]).
% None of the previous                                        %
pp_ct_body_list_types(_,[_|Goals],Vars,Names,Abs):-
    next_pred(Goals,NPred),
    pp_ct_body_list_types(NPred,Goals,Vars,Names,Abs).

% check pre-condition in success P:Pre => Post assertions
check_precond(_Types_Modes,_Head,_K,_Vars,_Goal,[]) :-!.
check_precond([Types,Modes],Head,K,Vars,Goal,Calls) :-
    copy_term(Head,CopyHead),
    decide_get_applicable_info(Types,K,Vars,CopyHead,Goal,TypesInfo),
    decide_get_applicable_info(Modes,K,Vars,CopyHead,Goal,ModesInfo),
    list_to_conj(Calls,CallsC),
% now: if precond is false then backtrack and forget the assertion
    not_already_bottom(TypesInfo,ModesInfo),
    \+ decide_abs_execute(Types,Goal,CallsC,Head,TypesInfo,_TNewInfo,fail),
    \+ decide_abs_execute(Modes,Goal,CallsC,Head,ModesInfo,_TNewInfo,fail).

inccounter_cond(_Counter,[[]]) :-!. % do not increase the counter if the assertion is empty
inccounter_cond(Counter,_) :-
    local_inccounter(Counter,_).

local_inccounter(Counter, Val) :-  % in case the counter is not defined.
    inccounter(Counter, Val),!.
local_inccounter(_, _).

%-------------------------------------------------------------%
% program_point check assertion
%-------------------------------------------------------------%
pp_ct_check_assertion(Prop,K,Vars,Names,[Types,Modes]):-
    Goal =.. [f|Vars],
    decide_get_just_info(Types,K,Vars,TypesInfo),
    decide_get_just_info(Modes,K,Vars,ModesInfo),
    not_already_bottom(TypesInfo,ModesInfo),
    decide_abs_execute(Types,Goal,Prop,Goal,TypesInfo,_,NProp), % check it (Goal)!
    ( ((NProp == true, S = checked); (NProp == fail, S = false)) ->
        message_pp_check(TypesInfo,Types,Prop,K,dic(Vars,Names),S)
    ;
        decide_abs_execute(Modes,Goal,NProp,Goal,ModesInfo,_,NNProp),
        (
            (NNProp == fail, S = false)
        ;   (NNProp == true, S = checked)
        ;    S = check
        ),!,
        prepare_info_pp(TypesInfo,Types,ModesInfo,Modes,Info,Abs),      
        message_pp_check(Info,Abs,Prop,K,dic(Vars,Names),S)
    ).

not_already_bottom('$bottom',_):-!, fail.
not_already_bottom(_,'$bottom'):-!, fail.
not_already_bottom(Type_term,_):-
    arg(1,Type_term,Type),
    Type = bot,!,
    fail.
not_already_bottom(_Type_term,_Modes).

are_bottom('$bottom',_):-!.
are_bottom(_,'$bottom'):-!.
are_bottom(Type_term,_):-
    arg(1,Type_term,Type),
    Type = bot.

%% %-------------------------------------------------------------------%   
%% % pp_ct_abs_ex_body_list_types(+,+,-,+,-,+)                         %
%% % pp_ct_abs_ex_body_list_types(Sense,Goals,NewGoals,Vars,Result,Abs)%
%% %  Special case of pp_ct_body_list when the goal is abstractly      %
%% %  executable                                                       %
%% %-------------------------------------------------------------------%
%% decide_make_list_of_one([P|Ps],LProps):-!,
%%      LProps = [P|Ps].
%% decide_make_list_of_one(Props,[Props]).

decide_abs_execute(none,_Goal,Calls,_Head,Info,Info,Calls):-!.
decide_abs_execute(Domain,Goal,Calls,Head,Info,NewInfo,NCalls):-
%       list_to_conj( Calls , ConjCalls ),
    varset(Goal,Vars),
    adapt_info_to_assrt_head( Domain, Goal, Vars, Info, Head, NewInfo ),
    pp_abs_execute_with_info(Calls,Domain,Head,NewInfo,NCalls).

pp_abs_execute_with_info([],_AbsInt,_Goal,_Info,true) :-!.
pp_abs_execute_with_info((Exp1,Exp2),AbsInt,Goal,Info,NewExp):-!,
    pp_abs_execute_with_info(Exp1,AbsInt,Goal,Info,NewExp1),
    (NewExp1 == fail ->
        NewExp = fail
    ;
        pp_abs_execute_with_info(Exp2,AbsInt,Goal,Info,NewExp2),
        synt_compose_conj(NewExp1,NewExp2,NewExp)).
pp_abs_execute_with_info((Exp1;Exp2),AbsInt,Goal,Info,NewExp):-!,
    pp_abs_execute_with_info(Exp1,AbsInt,Goal,Info,NewExp1),
    (NewExp1 == true ->
        NewExp = true
    ;
        pp_abs_execute_with_info(Exp2,AbsInt,Goal,Info,NewExp2),
        synt_compose_disj(NewExp1,NewExp2,NewExp)).
pp_abs_execute_with_info([Exp],AbsInt,Goal,Info,NewExp):-!,
    pp_abs_execute_with_info(Exp,AbsInt,Goal,Info,NewExp).
pp_abs_execute_with_info([Exp1,Exp2],AbsInt,Goal,Info,NewExp):-!,
    pp_abs_execute_with_info(Exp1,AbsInt,Goal,Info,NewExp1),
    (NewExp1 == fail ->
        NewExp = fail
    ;
        pp_abs_execute_with_info(Exp2,AbsInt,Goal,Info,NewExp2),
        synt_compose_list(NewExp1,NewExp2,NewExp)).
%
pp_abs_execute_with_info(Prop,AbsInt,_,Info,Sense):-
    abs_execute_with_info(AbsInt,Info,Prop,Sense).

decide_get_just_info(none,_K,_Vars,none):-!.
decide_get_just_info(Types,K,Vars,TypesInfo):-
    get_memo_lub(K,Vars,Types,yes,TypesInfo).

decide_get_applicable_info(none,_K,_Vars,_Head,_Goal,none):-!.
decide_get_applicable_info(Modes,K,Vars,Head,Goal,ModesInfo):-
         Head = Goal,
         get_memo_lub(K,Vars,Modes,yes,ModesInfo).

message_pp_calls_diag(Info,Abs,Goal,Head,Calls,Dict,K,Status):-
    message_pp_calls(Info,Abs,Goal,Head,Calls,Dict,K,Status),
    current_pp_flag(run_diagnosis,Diag),
    decide_diag_calls(Diag,Abs,Head,Calls,K,Status).

decide_diag_calls(off,_,_,_,_,_) :-!.
decide_diag_calls(on,Abs,Head,Calls,K,Status) :-
    ( Status \== checked ->
        Calls = [Call|_],
        ( how(Abs,K,calls,Head,Call,_W),fail; true)
    ; true
    ).

message_pp_success_diag(Info,Abs,Goal,Head,Calls,Succ,Dict,K,Status):-
    message_pp_success(Info,Abs,Goal,Head,Calls,Succ,Dict,K,Status),
    current_pp_flag(run_diagnosis,Diag),
    decide_diag_success(Diag,Abs,Head,Succ,K,Status).

decide_diag_success(off,_,_,_,_,_) :-!.
decide_diag_success(on,Abs,Head,Succ,K,Status) :-
    ( Status \== checked ->
        ( how(Abs,K,succ,Head,Succ,_W), fail; true )
    ; true
    ).
