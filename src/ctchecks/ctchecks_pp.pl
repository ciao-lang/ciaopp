:- module(ctchecks_pp, [ctcheck_pp/2], [assertions]).

:- use_module(library(lists), [member/2]).
:- use_module(library(formulae), [list_to_conj/2]).
:- use_module(library(messages), [debug_message/1, debug_message/2]).
:- use_module(library(vndict), [rename/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(runtime_control), [module_split/3]).

:- use_module(library(counters)).
:- use_module(library(hiordlib), [filter/3,maplist/3]).

:- use_module(spec(abs_exec_ops), [adapt_info_to_assrt_head/6]).

% CiaoPP library
:- use_module(ciaopp(infer), [get_memo_lub/5]).
:- use_module(ciaopp(infer/infer_dom), [abs_execute_with_info/4,knows_of/2]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit), [program/2, filtered_program_clauses/3]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(ciaopp(p_unit/program_keys), [first_key/2]).
:- use_module(spec(s_simpspec), 
              [next_pred/2, body2list/2, next_or_last_key/3]).
%% :- use_module(spec(abs_exec), [cond/4]).

% Own library
:- use_module(ciaopp(ctchecks/ctchecks_pp_common)).
:- use_module(ciaopp(ctchecks/ctchecks_pp_messages)).
:- use_module(ciaopp(ctchecks/preproc_errors), [preproc_warning/2]).
:- use_module(ciaopp(ctchecks/diagnosis/diag), [how/6]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

%% :- multifile term_domain/1.

:- pred ctcheck_pp(+AbsInts,+ModList).
ctcheck_pp(AbsInts,ModList) :-
    ( list(ModList) ->
        filtered_program_clauses(ModList,Cls,Ds)
    ; % ModList = all, % IG: sanity check
        program(Cls,Ds)
    ),
    pp_ctcheck_cls(Cls,Ds,AbsInts).

pp_ctcheck_cls([],[],_).
% Directives do not have program points                       %
pp_ctcheck_cls([directive(_Dir):_Id|Cs],[_D|Ds],AbsInts):- !,
    pp_ctcheck_cls(Cs,Ds,AbsInts).
pp_ctcheck_cls([clause(H,Body):Clid|Cs],[D|Ds],AbsInts):-
    pp_compile_time_check_types(Body,H,Clid,D,AbsInts),
    pp_ctcheck_cls(Cs,Ds,AbsInts).

% call type incompatible with head of the clause
pp_compile_time_check_types(Body,H,Clid,dic(Vars,Names),AbsInts):-
    first_key(Body,K),
    filter(knows_of(regtypes),AbsInts,Types), Types \= [],
    maplist(decide_get_just_info(K,Vars),Types,TypesInfo),
    any_is_bottom(TypesInfo),!,
    Types = [Dom|_],  % any domain is valid here.
    message_clause_incompatible(Clid,Dom,H,Vars,Names).
% The clause is a fact                                        %
pp_compile_time_check_types(true:_,_H,_Clid,_Dict,_AbsInts):- !.
% The body is just a cut                                      %
pp_compile_time_check_types(!,_H,_Clid,_Dict,_AbsInts):- !.
% Rest of clauses. We try to simplify its body                %
pp_compile_time_check_types(Body,_H,_Clid,dic(Vars,Names),AbsInts):-
    body2list(Body,Blist),
    next_pred(Blist,Pred),
    pp_ct_body_list_types(Pred,Blist,Vars,Names,AbsInts).

%-------------------------------------------------------------%
%-------------------------------------------------------------%

prepare_info_pp(AbsInts,Info,Dom,In):-
    ( Prop = regtypes ; Prop = sharing ),
    get_domain_knows_of(Prop,AbsInts,Info,Dom,In),!.
prepare_info_pp([Dom|_],[Info|_],Dom,Info).

pp_ct_body_list_types(none,[],_,_,_).
pp_ct_body_list_types((!/0),[!:_|Goals],Vars,Names,AbsInts):-!,
    next_pred(Goals,Pred),
    pp_ct_body_list_types(Pred,Goals,Vars,Names,AbsInts).
% This goal is a program point assertion                      %
pp_ct_body_list_types(_FA,[Goal:K|Goals],Vars,Names,AbsInts):-
    pp_check(Goal,Prop),!,
    pp_ct_check_assertion(Prop,K,Vars,Names,AbsInts),
    next_pred(Goals,NPred),
    pp_ct_body_list_types(NPred,Goals,Vars,Names,AbsInts).
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
pp_ct_body_list_types(F/A,[(Goal:K)|_],Vars,_Names,AbsInts):-
    curr_file(_,M),
    functor(Head,F,A),
    \+ module_split(F, M, _), % make sure that we have an imported predicate
%       displayq(Head),nl,
    get_entry_assertion(Head,pp,Calls,Dict),
%       get_calls_assertion(Goal,pp,Calls,Dict),
    nonvar(Calls),
    debug_message("calls assertion found ~q",[Calls]),
    copy_term(Head,CopyHead),
    maplist(decide_get_applicable_info(K,Vars,CopyHead,Goal),AbsInts,Info),
    \+ any_is_bottom(Info),
    get_domain_knows_of(regtypes,AbsInts,Info,Types,TypesInfo),
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
    ;   get_domain_knows_of(sharing,AbsInts,Info,Modes,ModesInfo),
        decide_abs_execute(Modes,Goal,NCalls,Head,ModesInfo,_,Fail),
        ( Fail == fail ->
            message_pp_entry(ModesInfo,Modes,Goal,Head,Calls,Dict,K,false),
            local_inccounter(pp_false_c,_)
        ;
            ( Fail == true -> 
                message_pp_entry(TypesInfo,Types,Goal,Head,Calls,Dict,K,checked),
                inccounter_cond(pp_checked_c,Calls) 
            ; 
                prepare_info_pp(AbsInts,Info,Dom,In),
                message_pp_entry(In,Dom,Goal,Head,Calls,Dict,K,check),
                local_inccounter(pp_check_c,_)
            ),
            fail
        )
    ).
%
% Violation of a "check calls" assertion                      %
pp_ct_body_list_types(F/A,[(Goal:K)|_],Vars,_Names,AbsInts):-
    functor(Head,F,A),
    get_calls_assertion(Head,pp,Calls,Dict),
%       get_calls_assertion(Goal,pp,Calls,Dict),
    nonvar(Calls),
    debug_message("calls assertion found ~q",[Calls]),
    copy_term(Head,CopyHead),
    maplist(decide_get_applicable_info(K,Vars,CopyHead,Goal),AbsInts,Info),
    \+ any_is_bottom(Info),
    get_domain_knows_of(regtypes,AbsInts,Info,Types,TypesInfo),
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
    ;    get_domain_knows_of(sharing,AbsInts,Info,Modes,ModesInfo),
         decide_abs_execute(Modes,Goal,NCalls,Head,ModesInfo,_,Fail),
         ( Fail == fail ->
             message_pp_calls_diag(ModesInfo,Modes,Goal,Head,Calls,Dict,K,false),
             local_inccounter(pp_false_c,_)
        ;
           ( Fail == true -> 
               message_pp_calls_diag(ModesInfo,Modes,Goal,Head,Calls,Dict,K,checked),
               inccounter_cond(pp_checked_c,Calls) 
           ; 
               prepare_info_pp(AbsInts,Info,Dom,In),
               message_pp_calls_diag(In,Dom,Goal,Head,Calls,Dict,K,check),
               local_inccounter(pp_check_c,_)
           )
        )
    ),
    fail.
%
% Violation of a "check success" assertion                    %
pp_ct_body_list_types(F/A,[(Goal:K)|Goals],Vars,_Names,AbsInts):-
    functor(Head,F,A),
    assertion_read(Head,_M,AStatus,success,Body,Dict,_Source,_LB,_LE),
    member(AStatus,[check]),
    assertion_body(Head,_Compat,Calls0,Succ0,_Comp,_Comm,Body),
    debug_message("success assertion found ~q",[Succ]),
    check_precond(Calls0,AbsInts,Head,K,Vars,Goal),
    next_or_last_key(Goals,K,K1),
    copy_term(Head,CopyHead),
    maplist(decide_get_applicable_info(K1,Vars,CopyHead,Goal),AbsInts,Info),
    \+ any_is_bottom(Info),
    list_to_conj(Succ0,Succ),
    get_domain_knows_of(regtypes,AbsInts,Info,Types,TypesInfo),
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
    ;   get_domain_knows_of(sharing,AbsInts,Info,Modes,ModesInfo),
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
            ; prepare_info_pp(AbsInts,Info,Dom,In),
              message_pp_success_diag(In,Dom,Goal,Head,Calls0,Succ0,Dict,K,check),
              local_inccounter(pp_check_s,_)
            )
        )
       ),fail.

% Goal has bottom as success substitution                     %
pp_ct_body_list_types(_P,[(Goal:K)|Goals],Vars,Names,AbsInts):-
    Goal\== 'basiccontrol:fail', Goal\== 'basiccontrol:false',
    debug_message("checking if bottom for ~q",[Goal]),
    maplist(decide_get_just_info(K,Vars),AbsInts,Info),
    \+ any_is_bottom(Info),
    next_or_last_key(Goals,K,K1),
    maplist(decide_get_just_info(K1,Vars),AbsInts,Info1),
    any_is_bottom(Info1), !,
    copy_term((Goal,dic(Vars,Names)),(NGoal,Dict)),
    rename(NGoal,Dict),
    preproc_warning(always_fails,[NGoal,K]).
% None of the previous                                        %
pp_ct_body_list_types(_,[_|Goals],Vars,Names,AbsInts):-
    next_pred(Goals,NPred),
    pp_ct_body_list_types(NPred,Goals,Vars,Names,AbsInts).

% check pre-condition in success P:Pre => Post assertions
check_precond([],_AbsInts,_Head,_K,_Vars,_Goal) :-!.
check_precond(Calls,AbsInts,Head,K,Vars,Goal) :-
    copy_term(Head,CopyHead),
    maplist(decide_get_applicable_info(K,Vars,CopyHead,Goal),AbsInts,Info),
    list_to_conj(Calls,CallsC),
% now: if precond is false then backtrack and forget the assertion
    \+ any_is_bottom(Info),
    maplist(( ''(Dom,In) :- \+ decide_abs_execute(Dom,Goal,CallsC,Head,In,_,fail) ),
            AbsInts,Info).

inccounter_cond(_Counter,[[]]) :-!. % do not increase the counter if the assertion is empty
inccounter_cond(Counter,_) :-
    local_inccounter(Counter,_).

local_inccounter(Counter, Val) :-  % in case the counter is not defined.
    inccounter(Counter, Val),!.
local_inccounter(_, _).

%-------------------------------------------------------------%
% program_point check assertion
%-------------------------------------------------------------%
pp_ct_check_assertion(Prop,K,Vars,Names,AbsInts):-
    Goal =.. [f|Vars],
    maplist(decide_get_just_info(K,Vars),AbsInts,Info),
    \+ any_is_bottom(Info),
    get_domain_knows_of(regtypes,AbsInts,Info,Types,TypesInfo),
    decide_abs_execute(Types,Goal,Prop,Goal,TypesInfo,_,NProp), % check it (Goal)!
    ( ((NProp == true, S = checked); (NProp == fail, S = false)) ->
        message_pp_check(TypesInfo,Types,Prop,K,dic(Vars,Names),S)
    ;   get_domain_knows_of(sharing,AbsInts,Info,Modes,ModesInfo),
        decide_abs_execute(Modes,Goal,NProp,Goal,ModesInfo,_,NNProp),
        (
            (NNProp == fail, S = false)
        ;   (NNProp == true, S = checked)
        ;    S = check
        ),!,
        prepare_info_pp(AbsInts,Info,Dom,In),
        message_pp_check(In,Dom,Prop,K,dic(Vars,Names),S)
    ).

any_is_bottom(Info) :-
    member(Element,Info),
    is_bottom(Element), !.

is_bottom('$bottom').
is_bottom(regtype(bot)).

get_domain_knows_of(Prop,[Dom|AbsInts],[In|Info],Dom1,In1):-
    ( knows_of(Prop,Dom) ->
        Dom1 = Dom,
        In1 = In
    ; get_domain_knows_of(Prop,AbsInts,Info,Dom1,In1)
    ).

%% %-------------------------------------------------------------------%   
%% % pp_ct_abs_ex_body_list_types(+,+,-,+,-,+)                         %
%% % pp_ct_abs_ex_body_list_types(Sense,Goals,NewGoals,Vars,Result,AbsInts)%
%% %  Special case of pp_ct_body_list when the goal is abstractly      %
%% %  executable                                                       %
%% %-------------------------------------------------------------------%
%% decide_make_list_of_one([P|Ps],LProps):-!,
%%      LProps = [P|Ps].
%% decide_make_list_of_one(Props,[Props]).

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

decide_get_just_info(K,Vars,Dom,Info) :-
    get_memo_lub(K,Vars,Dom,yes,Info),!.

decide_get_applicable_info(K,Vars,Head,Goal,Dom,Info):-
    Head = Goal,
    get_memo_lub(K,Vars,Dom,yes,Info).

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
