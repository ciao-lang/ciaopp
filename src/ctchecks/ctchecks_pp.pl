:- module(ctchecks_pp, [ctcheck_pp/2], [assertions,modes,hiord]).

:- use_package(library(compiler/p_unit/p_unit_argnames)).

:- use_module(library(formulae), [conj_to_list/2]).
:- use_module(library(messages), [debug_message/2]).
:- use_module(library(vndict), [rename/2]).

:- use_module(library(counters)).
:- use_module(library(hiordlib), [filter/3,maplist/3,maplist/4]).

% CiaoPP library
:- use_module(ciaopp(infer), [get_memo_lub/5]).
:- use_module(ciaopp(infer/infer_dom), [abs_execute/7,knows_of/2]).
:- use_module(library(compiler/p_unit), [program/2, filtered_program_clauses/3]).
:- use_module(library(compiler/p_unit/program_keys), [first_key/2,lit_ppkey/3]).
:- use_module(spec(s_simpspec), [next_or_last_key/3]).

% Own library
:- use_module(ciaopp(ctchecks/ctchecks_common)).
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
    conj_to_list(Body,Blist),
    pp_compile_time_check_each(Blist,Vars,Names,AbsInts).

pp_compile_time_check_each([],_Vars,_Names,_AbsInts).
pp_compile_time_check_each([Goal|Goals],Vars,Names,AbsInts):-
    lit_ppkey(Goal,Lit,K),
    pp_ct_body_list_types(Lit,K,Goals,Vars,Names,AbsInts),
    % If a call always fails, do not check next predicate.
    ( pp_ct_body_check_always_fails(Lit,K,Goals,Vars,Names,AbsInts) ->
        true
    ; pp_compile_time_check_each(Goals,Vars,Names,AbsInts)
    ).

%-------------------------------------------------------------%
%-------------------------------------------------------------%

prepare_info_pp(AbsInts,Info,Dom,In):-
    ( Prop = regtypes ; Prop = sharing ),
    get_domain_knows_of(Prop,AbsInts,Info,Dom,In),!.
prepare_info_pp([Dom|_],[Info|_],Dom,Info).

pp_ct_body_list_types(!,_,_Goals,_Vars,_Names,_AbsInts):-!.
% This goal is a program point assertion                      %
pp_ct_body_list_types(Goal,K,_Goals,Vars,Names,AbsInts):-
    pp_check(Goal,Prop),!,
    pp_ct_check_assertion(Prop,K,Vars,Names,AbsInts).
% Goal is a builtin whose call is violated using type info    %
%
% pp_ct_body_list_types(F/A,[(Goal:K)|_],Vars,Names,[Types,Modes]):-
%       functor(Builtin,F,A),
%       check_type_calls(Builtin,Calls),
%       copy_term(Builtin,CopyBuiltin),
%       decide_get_applicable_info(Types,K,Vars,CopyBuiltin,Goal,TypesInfo),
%       decide_get_applicable_info(Modes,K,Vars,CopyBuiltin,Goal,ModesInfo),
%       not_already_bottom(TypesInfo,ModesInfo),
%       abs_execute(Types,Goal,Calls,Goal,Vars,TypesInfo,NCalls),
%       (NCalls == true -> inccounter(pp_checked_c,_), fail; true),
%         ( NCalls == fail ->
%         message_pp_builtin(TNewInfo,Types,Builtin,Calls,dic(Vars,Names),K),
%         inccounter(pp_false_c,_)
%       ;
%       abs_execute(Modes,Goal,NCalls,Goal,Vars,ModesInfo,Fail),
%         ( Fail == fail ->
%           message_pp_builtin(ModesInfo,Modes,Goal,Calls,dic(Vars,Names),K),
%           inccounter(pp_false_c,_)
%       ;  (Fail == true -> inccounter(pp_checked_c,_) ; inccounter(pp_check_c,_)), 
%           fail
%       )).
%
pp_ct_body_list_types(Goal,K,Goals,Vars,_Names,AbsInts):-
    assr_head(Goal,Head),
    % Failure-driven loop to check each relevant assertion.
    % entry and calls assertions are checked independently.
    ( get_check_assertion(Head,Assertion,_Refs),
      check_assertion(Assertion,Goal,K,Vars,Goals,AbsInts),
      fail
    ; true
    ).

check_assertion(A0,Goal,K,Vars,Goals,AbsInts) :-
    A0 = as${type=>Type, head=>Head},
    copy_term(Head, CopyHead),
    maplist(decide_get_applicable_info(K, Vars, CopyHead, Goal), AbsInts, Calls),
    next_or_last_key(Goals, K, K1),
    maplist(decide_get_applicable_info(K1, Vars, CopyHead, Goal), AbsInts, Succ),
    maplist(adapt_to_completes_format(CopyHead, K), Calls, Succ, Info),
    adapt_entry_to_calls(A0, A),
    abs_exec_one_assertion_all(AbsInts, Info, A, K, DomsOut, InfoOut, NA),
    NA = as${status=>Status, dic=>Dict},
    ( Status = checked ->
        ( Type = success ->
            A0 = as${succ=>C}
        ; A0 = as${call=>C} )    
    ; C = not_empty ),
    local_inccounter_split(pp,Status,Type,C),
    ( Type = success ->
        message_pp_success_diag(A0, InfoOut, DomsOut, Head, Dict, K, Status)
    ; Type = calls ->
        message_pp_calls_diag(A0, InfoOut, DomsOut, Head, Dict, K, Status)
    ; Type = entry ->
        message_pp_entry(A0, InfoOut, DomsOut, Head, Dict, K, Status)
    ).

adapt_to_completes_format(AGoal, Key, ACall, ASuccs0, Formatted) :-
    Formatted = [complete(AGoal,ACall,[ASuccs0],Key,lub)].

adapt_entry_to_calls(as(Module,_Status,entry,Head,Compat,Call,Succ,Comp,Dic,
                        Locator,Comment,Fromwhere),
                     Res) :- !,
    Res = as(Module,check,calls,Head,Compat,Call,Succ,Comp,Dic,Locator,Comment,
             Fromwhere).
adapt_entry_to_calls(As, Res) :- As = Res.

assr_head(Goal,Head):-
    functor(Goal,F,A),
    functor(Head,F,A).

% Goal has bottom as success substitution                     %
pp_ct_body_check_always_fails(Goal,K,Goals,Vars,Names,AbsInts):-
    Goal\== 'basiccontrol:fail', Goal\== 'basiccontrol:false',
    debug_message("checking if bottom for ~q",[Goal]),
    maplist(decide_get_just_info(K,Vars),AbsInts,Info),
    \+ any_is_bottom(Info),
    next_or_last_key(Goals,K,K1),
    maplist(decide_get_just_info(K1,Vars),AbsInts,Info1),
    any_is_bottom(Info1),
    copy_term((Goal,dic(Vars,Names)),(NGoal,Dict)),
    rename(NGoal,Dict),
    preproc_warning(always_fails,[NGoal,K]).

local_inccounter_split(Proc,Status,Type,C) :-
    ( Type = calls -> T = c ; T = s),
    counter_name(Proc, Status, T, Counter),
    inccounter_cond(Counter, C).

inccounter_cond(_Counter,[]) :-!. % do not increase the counter if the assertion is empty
inccounter_cond(Counter,_) :-
    local_inccounter(Counter,_).

local_inccounter(Counter, Val) :-  % in case the counter is not defined.
    inccounter(Counter, Val),!.
local_inccounter(_, _).

counter_name(pp, false, c, pp_false_c).
counter_name(pp, false, s, pp_false_s).
counter_name(pp, check, c, pp_check_c).
counter_name(pp, check, s, pp_check_s).
counter_name(pp, checked, c, pp_checked_c).
counter_name(pp, checked, s, pp_checked_s).

%-------------------------------------------------------------%
% program_point check assertion
%-------------------------------------------------------------%
pp_ct_check_assertion(Prop,K,Vars,Names,AbsInts):-
    Goal =.. [f|Vars],
    maplist(decide_get_just_info(K,Vars),AbsInts,Info),
    \+ any_is_bottom(Info),
    get_domain_knows_of(regtypes,AbsInts,Info,Types,TypesInfo),
    abs_execute(Types,Head,Prop,Goal,Vars,TypesInfo,NProp), % check it (Goal)!
    ( ((NProp == true, S = checked); (NProp == fail, S = false)) ->
        message_pp_check(TypesInfo,Types,Prop,K,dic(Vars,Names),S)
    ;   get_domain_knows_of(sharing,AbsInts,Info,Modes,ModesInfo),
        abs_execute(Modes,Head,NProp,Goal,Vars,ModesInfo,NNProp),
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

% TODO: Do not discard all but the first domain before running how/6.

decide_get_just_info(K,Vars,Dom,Info) :-
    get_memo_lub(K,Vars,Dom,yes,Info),!.

decide_get_applicable_info(K,Vars,Head,Goal,Dom,Info):-
    Head = Goal,
    get_memo_lub(K,Vars,Dom,yes,Info), !.

message_pp_calls_diag(A,Info,Abs,Head,Dict,K,Status):-
    A = as${call=>Calls},
    message_pp_calls(A,Info,Abs,Head,Dict,K,Status),
    current_pp_flag(run_diagnosis,Diag),
    Abs = [DiagAbs|_],
    decide_diag_calls(Diag,DiagAbs,Head,Calls,K,Status).

decide_diag_calls(off,_,_,_,_,_) :-!.
decide_diag_calls(on,Abs,Head,Calls,K,Status) :-
    ( Status \== checked ->
        Calls = [Call|_],
        ( how(Abs,K,calls,Head,Call,_W),fail; true)
    ; true
    ).

message_pp_success_diag(A,Info,Abs,Head,Dict,K,Status):-
    A = as${succ=>Succ},
    message_pp_success(A,Info,Abs,Head,Dict,K,Status),
    current_pp_flag(run_diagnosis,Diag),
    Abs = [DiagAbs|_],
    decide_diag_success(Diag,[DiagAbs|_],Head,Succ,K,Status).

decide_diag_success(off,_,_,_,_,_) :-!.
decide_diag_success(on,Abs,Head,Succ,K,Status) :-
    ( Status \== checked ->
        ( how(Abs,K,succ,Head,Succ,_W), fail; true )
    ; true
    ).
