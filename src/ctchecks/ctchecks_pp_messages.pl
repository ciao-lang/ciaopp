:- module(ctchecks_pp_messages, [
    message_pp_calls/8,
    message_pp_entry/8,
    message_pp_success/9,
    message_pp_check/6,
    message_clause_incompatible/5
], [assertions, regtypes]).

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- use_module(library(formulae), [list_to_conj/2]).
:- use_module(library(lists),    [append/3]).
:- use_module(library(messages)).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(vndict), [rename/2]).
:- use_module(library(write),  [numbervars/3, prettyvars/1]).

:- use_module(ciaopp(p_unit/assrt_norm), [denorm_goal_prop/3]).
:- use_module(ciaopp(p_unit/clause_db), [maybe_clause_locator/2]).
%:- use_module(ciaopp(p_unit/clause_db), [clause_locator/2]).
:- use_module(ciaopp(p_unit), [prop_to_native/2]).
:- use_module(ciaopp(p_unit/program_keys),
              [decode_litkey/5, get_predkey/3, get_clkey/4]).

:- use_module(typeslib(typeslib), [pretty_type_lit_rules/4]).
:- use_module(ciaopp(plai/domains), [asub_to_info/5, project/6, abs_sort/3]).
:- use_module(ciaopp(infer), [get_completes_lub/6]).
:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(ciaopp(ctchecks/preproc_errors), [preproc_error/2]).
:- use_module(ciaopp(ctchecks/ctchecks_pred_messages), [memo_ctcheck_sum/1,
    prepare_output_info/5,name_vars/1]).

output_user_interface(AbsInt,ASub,NVars,Props):-
    asub_to_info(AbsInt,ASub,NVars,Props,_NativeComp), !.

display_message_check_pp(_LC,_Str,_Args) :- current_pp_flag(asr_not_stat_eval, off), !.
display_message_check_pp(LC,Str,Args) :- current_pp_flag(asr_not_stat_eval, warning),!,
    warning_message(LC,Str,Args).
display_message_check_pp(LC,Str,Args) :-
    error_message(LC,Str,Args).

display_message_checked_pp(LC,Str,Args) :-
    current_pp_flag(pplog, L),
    member(ctchecks, L), !,
    note_message(LC,Str,Args). % TODO: replace by pplog?
display_message_checked_pp(_,_,_).

update_dict([],H,D):-!,
    varset(H,Hv),
    copy_term(H,CopyH),
    varset(CopyH,CopyVs),
    numbervars(CopyVs,0,_),
    make_dict(CopyVs,Hv,D).
update_dict(D,_,D).

make_dict([],[],[]).
make_dict(['$VAR'(N)|Ns],[V|Vs],[Name=V|NVs]):-
    N1 is N + 65,
    name(Name,[N1]),
    make_dict(Ns,Vs,NVs).

:- pred message_pp_calls/8.
message_pp_calls(_,none,_,_,_,_,_,_):- !.
message_pp_calls(Info,AbsInt,Goal,Head,Calls,Dict,K,Status):-
    As = as(_,check,calls,Head,[],Calls,[],[],Dict,_,_,_),
    prepare_output_info([AbsInt], [Info], Head, calls_pp(Goal), RelInfo),
    copy_term((Head,'$an_results'(RelInfo),Dict),(GoalCopy,RelInfoCopy,DictCopy)),
    name_vars(DictCopy),
    prettyvars((GoalCopy,RelInfoCopy)),
    decode_litkey(K,F,A,C,L),
    get_clkey(F,A,C,ClId),
    maybe_clause_locator(ClId,LC),
    !,
    ( Status == check ->
        display_message_check_pp(LC,
            "At literal ~w could not verify assertion:~n"||
            "~p"||
            "because on call ~p :~n"||
            "~p",
            [L,As,GoalCopy,RelInfoCopy])
    ; Status == false -> 
        error_message(LC,
            "At literal ~w false assertion:~n"||
            "~p"||
            "because on call ~p :~n"||
            "~p",
            [L,As, GoalCopy, RelInfoCopy])
    ; display_message_checked_pp(LC,
          "At literal ~w successfully checked assertion:~n"||
          "~p",
          [L,As])
    ).
%pp%
%pp%message_pp_calls(Info,AbsInt,Goal,Head,Calls,Dict_,K,Status):-
%pp%    update_dict(Dict_,Head,Dict),
%pp%    copy_term((Info,Goal,Head,Calls,Dict),
%pp%              (NInfo,NGoal,NHead,NCall,NVsNNs)),
%pp%    abs_sort(AbsInt,NInfo,Sorted_Info),
%pp%    varset(NGoal,NVars),
%pp%    project(AbsInt,NVars,_,Sorted_Info,Proj),
%pp%    output_user_interface(AbsInt,Proj,NVars,Props0),
%pp%    list_to_conj(Props0,Props),
%pp%    ( knows_of(regtypes,AbsInt)
%pp%    -> copy_term((NGoal,Props0),(TGoal,TProps))
%pp%     ; true
%pp%    ),
%pp%%   ( NVsNNs = [] ->
%pp%%     numbervars(NCall,0,_)
%pp%%   ; infer_unify_vars0(NVsNNs)
%pp%%   ),
%pp%    infer_unify_vars0(NVsNNs),
%pp%    decode_litkey(K,F,A,C,L),
%pp%        get_clkey(F,A,C,ClId),
%pp%        clause_locator(ClId,LC),
%pp%    ( knows_of(regtypes,AbsInt)
%pp%    -> ctchecks_pp_messages:inline_types(TProps),
%pp%       escapify(TGoal,TGoalEsc),
%pp%       typeslib:pretty_type_lit_rules(TGoalEsc,P_Info,_Types,Rules),
%pp%       ctchecks_pp_messages:filter_required_rules(Rules,ReqRules,FormRules),
%pp%       W1='',
%pp%       ( ReqRules = [] -> W2='' ; W2=' with:' )
%pp%     ; ReqRules=[Props],
%pp%       P_Info=NGoal,
%pp%       W1='of ',
%pp%       W2=' :',
%pp%       FormRules="~n  ~w"
%pp%    ),
%pp%    ( Status == false ->
%pp%      memo_ctcheck_sum(false),
%pp%      error_message(LC,"At literal ~w false calls assertion:
%pp%   :- calls ~w : ~w~n because on call ~w~w~w"||FormRules,
%pp%                         [L,NHead,NCall,W1,P_Info,W2|ReqRules]),
%pp%      Expected = calls(NHead:NCall),
%pp%      preproc_error(calls,[lit(F,A,C,L),Expected,Props0,[]])
%pp%    ; ( Status == check -> 
%pp%        memo_ctcheck_sum(check),
%pp%        display_message_check_pp(LC,"At literal ~w could not verify calls assertion:
%pp%   :- calls ~w : ~w~n because on call ~w~w~w"||FormRules,
%pp%                         [L,NHead,NCall,W1,P_Info,W2|ReqRules])
%pp%      ;
%pp%        display_message_checked_pp(LC,
%pp%                "At literal ~w successfully checked calls assertion:
%pp%   :- calls ~w : ~w", [L,NHead,NCall])
%pp%      )
%pp%    ),
%pp%    !.
%
message_pp_calls(Info,AbsInt,Goal,Head,Calls,Dict,K,Status) :-
    throw(bug_failed(message_pp_calls(Info,AbsInt,Goal,Head,Calls,Dict,K,Status))).

:- pred message_pp_entry/8.
message_pp_entry(Info,AbsInt,Goal,Head,Calls,Dict_,K,Status):-
    update_dict(Dict_,Head,Dict),
    copy_term((Info,Goal,Head,Calls,Dict),(NInfo,NGoal,NHead,NCall,NVsNNs)),
    abs_sort(AbsInt,NInfo,Sorted_Info),
    varset(NGoal,NVars),
    project(AbsInt,NGoal,NVars,[],Sorted_Info,Proj),
    output_user_interface(AbsInt,Proj,NVars,Props0),
    list_to_conj(Props0,Props),
    ( knows_of(regtypes,AbsInt) ->
        copy_term((NGoal,Props0),(TGoal,TProps))
    ; true
    ),
    infer_unify_vars0(NVsNNs),
    decode_litkey(K,F,A,C,L),
    get_clkey(F,A,C,ClId),
    maybe_clause_locator(ClId,LC),
    ( knows_of(regtypes,AbsInt) ->
        ctchecks_pp_messages:inline_types(TProps),
        escapify(TGoal,TGoalEsc),
        typeslib:pretty_type_lit_rules(TGoalEsc,P_Info,_Types,Rules),
        ctchecks_pp_messages:filter_required_rules(Rules,ReqRules,FormRules),
        W1='',
        ( ReqRules = [] -> W2='' ; W2=' with:' )
    ;
        ReqRules=[Props],
        P_Info=NGoal,
        W1='of ',
        W2=' :',
        FormRules="~n"||"  ~w"
    ),
    !,
    ( Status == false ->
        memo_ctcheck_sum(false),
        error_message(LC,
            "At literal ~w false entry assertion:~n"||
            "   :- entry ~w : ~w~n"||
            " because on call ~w~w~w"||
            FormRules,
            [L,NHead,NCall,W1,P_Info,W2|ReqRules]),
        Expected = calls(NHead:NCall),
        preproc_error(calls,[lit(F,A,C,L),Expected,Props0,[]])
    ; Status == check -> 
        memo_ctcheck_sum(check),
        display_message_check_pp(LC,
            "At literal ~w could not verify entry assertion:~n"||
            "   :- entry ~w : ~w~n"||
            " because on call ~w~w~w"||
            FormRules,
            [L,NHead,NCall,W1,P_Info,W2|ReqRules])
    ; display_message_checked_pp(LC,
          "At literal ~w successfully checked entry assertion:~n"||
          "   :- entry ~w : ~w",
          [L,NHead,NCall])
    ).
message_pp_entry(Info,AbsInt,Goal,Head,Calls,Dict,K,Status) :-
    throw(bug_failed(message_pp_entry(Info,AbsInt,Goal,Head,Calls,Dict,K,Status))).

message_pp_success(Info,AbsInt,Goal,Head,Calls,Succ,Dict,K,Status):-
    As = as(_,check,success,Head,[],Calls,Succ,[],Dict,_,_,_),
    prepare_output_info([AbsInt], [Info], Head, success_pp(Goal), RelInfo),
    copy_term((Head,'$an_results'(RelInfo),Dict),(GoalCopy,RelInfoCopy,DictCopy)),
    name_vars(DictCopy),
    prettyvars((GoalCopy,RelInfoCopy)),
    decode_litkey(K,F,A,C,L),
    get_clkey(F,A,C,ClId),
    maybe_clause_locator(ClId,LC), !,
    ( Status == check ->
        display_message_check_pp(LC,
            "At literal ~w could not verify assertion:~n"||
            "~p"||
            "because on success ~p :~n"||
            "~p",
            [L,As,GoalCopy,RelInfoCopy])
    ; Status == false ->
        error_message(LC,
            "At literal ~w false assertion:~n"||
            "~p"||
            "because on success ~p :~n"||
            "~p",
            [L,As, GoalCopy, RelInfoCopy])
    ; display_message_checked_pp(LC,
          "At literal ~w successfully verified assertion:~n"||
          "~p",
          [L,As])
    ).
%pp%message_pp_success(Info,AbsInt,Goal,Head,Calls,Succ,Dict0,K,Status):-
%pp%    ( var(Calls) -> Calls = true ; true ),
%pp%    update_dict(Dict0,Head,Dict),
%pp%    copy_term((Info,Goal,Head,Calls,Succ,Dict),
%pp%              (NInfo,NGoal,NHead,NCall,NSucc,NVsNNs)),
%pp%    abs_sort(AbsInt,NInfo,Sorted_Info),
%pp%    varset(NGoal,NVars),
%pp%    project(AbsInt,NVars,_,Sorted_Info,Proj),
%pp%    output_user_interface(AbsInt,Proj,NVars,Props),
%pp%    list_to_conj(Props,Props0),
%pp%    ( knows_of(regtypes,AbsInt)
%pp%    -> copy_term((NGoal,Props),(TGoal,TProps))
%pp%     ; true
%pp%    ),
%pp%    infer_unify_vars0(NVsNNs),
%pp%    decode_litkey(K,F,A,C,L),
%pp%        get_clkey(F,A,C,ClId),
%pp%        clause_locator(ClId,LC),
%pp%    ( knows_of(regtypes,AbsInt)
%pp%    -> ctchecks_pp_messages:inline_types(TProps),
%pp%       escapify(TGoal,TGoalEsc),
%pp%       typeslib:pretty_type_lit_rules(TGoalEsc,P_Info,_Types,Rules),
%pp%       ctchecks_pp_messages:filter_required_rules(Rules,ReqRules,FormRules),
%pp%       W1='',
%pp%       ( ReqRules = [] -> W2='' ; W2=' with:' )
%pp%     ; ReqRules=[Props0],
%pp%       P_Info=NGoal,
%pp%       W1='of ',
%pp%       W2=' :',
%pp%       FormRules="~n  ~w"
%pp%    ),
%pp%
%pp%    ( Status == false ->
%pp%      memo_ctcheck_sum(false),
%pp%      error_message(LC,"At literal ~w false success assertion:
%pp%   :- success ~w : ~w => ~w~n because on success ~w~w~w"||FormRules,
%pp%                      [L,NHead,NCall,NSucc,W1,P_Info,W2|ReqRules]),
%pp%      Expected = success('=>'((NHead:NCall),NSucc)),
%pp%      preproc_error(success,[lit(F,A,C,L),Expected,P_Info,ReqRules])
%pp%
%pp%    ; ( Status == check -> 
%pp%        memo_ctcheck_sum(check),
%pp%        display_message_check_pp(LC,"At literal ~w could not verify assertion:
%pp%   :- success ~w : ~w => ~w~n because on success ~w~w~w"||FormRules,
%pp%                         [L,NHead,NCall,NSucc,W1,P_Info,W2|ReqRules])
%pp%      ;
%pp%          
%pp%                display_message_checked_pp(LC,
%pp%                "At literal ~w successfully checked success assertion:
%pp%   :- success ~w : ~w => ~w~n", [L,NHead,NCall,NSucc])
%pp%      )
%pp%    ),
%pp%    !.
%
message_pp_success(Info,AbsInt,Goal,Head,Calls,Succ,Dict,K,Status):-
    throw(bug_failed(message_pp_success(Info,AbsInt,Goal,Head,Calls,Succ,Dict,K,Status))).

message_pp_check(Info,AbsInt,Prop,Key,Dict,Status):-
    copy_term((Info,Prop,Dict),(NInfo,NProp,NDict)),
    abs_sort(AbsInt,NInfo,Sorted_Info),
    varset(NProp,NVars),
    project(AbsInt,NProp,NVars,[],Sorted_Info,Proj),
    output_user_interface(AbsInt,Proj,NVars,Props0),
    list_to_conj(Props0,Props),
    ( knows_of(regtypes,AbsInt) ->
        copy_term(NProp,TProp),
        copy_term(Props0,TProps)
    ; true
    ),
    rename((NProp,Props),NDict),
    decode_litkey(Key,F,A,C,L),
    get_clkey(F,A,C,ClId),
    maybe_clause_locator(ClId,LC),
    ( knows_of(regtypes,AbsInt) ->
        varset(TProps,TVars),
        ctchecks_pp_messages:inline_types(TProps),
        TGoal =.. [f|TVars],
        escapify(TGoal,TGoalEsc),
        typeslib:pretty_type_lit_rules(TGoalEsc,_P_Info,_Types1,Rules1),
%          typeslib:pretty_type_lit_rules(TGoal,_P_Info,_Types1,Rules1),
        ctchecks_pp_messages:filter_required_rules(Rules1,ReqRules1,FormRules1),
        ( ReqRules1 = [] -> W2='' ; W2=' with:' ),
        % varset(TProp,RVars),
        inline_types2(TProp,RVars),
        RGoal =.. [f|RVars],
        typeslib:pretty_type_lit_rules(RGoal,_R_Info,_Types2,Rules2),
        ctchecks_pp_messages:filter_required_rules(Rules2,ReqRules2,FormRules2),
        ( ReqRules2 = [] -> W4='' ; W4=' with:' )
    ;
        ReqRules1=[''],
        W2='',
        FormRules1="  ~w",
        ReqRules2=[''],
        W4='',
        FormRules2="  ~w"
    ),
    append(ReqRules1,[NProp,W4|ReqRules2],ReqRules),
    append(FormRules1,"~n"||"~4| Expected: ~w~w"||FormRules2,FormRules),
    ( Status == false ->
        memo_ctcheck_sum(false),
        error_message(LC,
            "At literal ~w false program point assertion:~n"||
            "~4| Called:   ~w~w"||
            FormRules,
            [L,Props,W2|ReqRules]),
        preproc_error(pp,[lit(F,A,C,L),Prop,Props0,[]])
    ; Status == check ->
        memo_ctcheck_sum(check),
        display_message_check_pp(LC,
            "At literal ~w could not verify program point assertion:~n"||
            "~4| Called:   ~w~w"||
            FormRules,
            [L,Props,W2|ReqRules])
    ; display_message_checked_pp(LC,
          "At literal ~w successfully verified program point assertion.", [L])
    ),
    !.
%
message_pp_check(Info,AbsInt,Prop,Key,Dict,Stat) :-
    throw(bug_failed(message_pp_check(Info,AbsInt,Prop,Key,Dict,Stat))).

message_clause_incompatible(Clid,Types,H,Vars,Names):-
    functor(H,N,A),
    get_predkey(N,A,Key),
    functor(TGoal,N,A),
    get_completes_lub(Key,TGoal,Types,yes,Call0,_Succ0),
    output_user_interface(Types,Call0,Vars,Props),
    ctchecks_pp_messages:inline_types(Props),
    typeslib:pretty_type_lit_rules(TGoal,P_Call,_TSymbols,Rules0),
    ctchecks_pp_messages:filter_required_rules(Rules0,Rules,Forms),
    copy_term((H,Vars),(NH,NVars)),
    infer_unify_vars(NVars,Names),
    maybe_clause_locator(Clid,LC),
    memo_ctcheck_sum(check), !, %???
    ( Rules = [] -> W1='' ; W1=' with:' ),
    warning_message(LC,"the head of clause ~q is incompatible with its call type~n"||
        "~4| Head:      ~w~n"||
        "~4| Call Type: ~w~w"||
        Forms,
        [Clid,NH,P_Call,W1|Rules]).
%
message_clause_incompatible(Clid,Types,H,Vars,Names) :-
    throw(bug_failed(message_clause_incompatible(Clid,Types,H,Vars,Names))).

% a couple of auxiliary predicates
infer_unify_vars([],[]).
infer_unify_vars([V|Vs],[N|Ns]):-
    V = N,
    infer_unify_vars(Vs,Ns).

infer_unify_vars0([]).
infer_unify_vars0([V=N|VNs]):-
    V = N,
    infer_unify_vars0(VNs).

inline_types([]).
inline_types([Prop|Props]):- !,
    denorm_goal_prop(Prop,P,P),
    ctchecks_pp_messages:inline_types(Props).
inline_types((Prop;Props)):- !,
    ctchecks_pp_messages:inline_types(Prop),
    ctchecks_pp_messages:inline_types(Props).
inline_types((Prop,Props)):- !,
    ctchecks_pp_messages:inline_types(Prop),
    ctchecks_pp_messages:inline_types(Props).
inline_types(Prop):-
    denorm_goal_prop(Prop,P,P).

% PP: New version to cope with multiple occurences of the same variable
inline_types2([],[]).
inline_types2([Prop|Props],[P|Ps]):- !,
    copy_term(Prop,InProp),
    denorm_goal_prop(InProp,P,P),
    inline_types2(Props,Ps).
inline_types2((Prop;Props),Ps):- !,
    inline_types2(Prop,Ps1),
    append(Ps1,Ps2,Ps),
    inline_types2(Props,Ps2).
inline_types2((Prop,Props),Ps):- !,
    inline_types2(Prop,Ps1),
    append(Ps1,Ps2,Ps),
    inline_types2(Props,Ps2).
inline_types2(Prop,[P]):-
    copy_term(Prop,InProp),
    denorm_goal_prop(InProp,P,P).

filter_required_rules([typedef(::=(T,_))|Ds],Rs,Fs) :-
    functor(G,T,1), type(G), !,  % not inferred
    ctchecks_pp_messages:filter_required_rules(Ds,Rs,Fs).
filter_required_rules([typedef(::=(T,D))|Ds],[T,D|Rs],"~n"||"    ~w ::= ~w"||Fs) :-
    ctchecks_pp_messages:filter_required_rules(Ds,Rs,Fs).
filter_required_rules([],[],[]).

% only user types (not inferred!)
type(Goal):- prop_to_native(Goal,regtype(_Prop)).

not_to_escape(A) :- 
    G =.. [A,_],
    type(G),!.
not_to_escape(A) :- number(A),!.
not_to_escape([]) :-!.
not_to_escape([_|_]).

escapify(Goal,EscGoal) :-
    Goal=..[F|Args],
    escapify_list(Args,ArgsEsc),
    EscGoal=..[F|ArgsEsc].
    
escapify_one(A,AEsc) :-
    A=..[F|Args],
    escapify_list(Args,ArgsEsc),
    AEsc0=..[F|ArgsEsc],
%       A1 =.. [F,_],
    ( not_to_escape(A)  ->
        AEsc = AEsc0
    ; AEsc = ^(AEsc0)
    ).

escapify_list([],[]).
escapify_list([A|As],[E|Es]) :-
    escapify_one(A,E),
    escapify_list(As,Es).
