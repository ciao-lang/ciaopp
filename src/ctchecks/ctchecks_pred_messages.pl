:- module(_, [], [assertions, isomodes, regtypes, datafacts, nativeprops, ciaopp(ciaopp_options)]).

:- doc(title, "Messages for predicate compile-time checking").

:- doc(module, "This module prints the messages emitted during
       compile-time checking of predicate-level assertions.").

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- use_module(library(formulae), [list_to_conj/2]).
:- use_module(library(messages), [
    show_message/3, warning_message/2, error_message/2, note_message/2]).

:- use_module(ciaopp(p_unit), [prop_to_native/2]).
:- use_module(ciaopp(p_unit), [
    add_assertion/1,
    assertion_set_status/3,
    assertion_set_calls/3,
    assertion_set_success/3,
    assertion_set_comp/3]).
:- use_module(ciaopp(p_unit/p_unit_basic), [type_of_goal/2]).
:- use_module(ciaopp(frontend_driver), [write_one_type/2]). % TODO: move somewhere else
:- use_module(typeslib(typeslib), [pretty_type_lit_rules_desimp/2, equiv_type/2]).
:- use_module(ciaopp(plai/domains), [asub_to_info/5,needs/2,project/5,project/6]).
:- use_module(ciaopp(p_unit/assrt_norm), [denorm_goal_prop/3]).
:- use_module(ciaopp(preprocess_flags)).

:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).
:- use_module(spec(abs_exec_ops), [adapt_info_to_assrt_head/6]).

:- use_module(library(lists), [member/2, append/3, length/2]).
:- use_module(library(sort)).
:- use_module(library(write)).
:- use_module(library(format)).
:- use_module(library(counters), [inccounter/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(terms), [atom_concat/2]).

:- if(defined(has_ciaopp_cost)).
:- use_module(ciaopp(ctchecks/ctchecks_intervals), [
    cleanup_polynom_message/0,
    get_interval_check/2,
    decide_inform_user_interval/8
]).
:- else.
cleanup_polynom_message.
get_interval_check(_, _) :- fail.
decide_inform_user_interval(_, _, _, _, _, _, _, _).
:- endif.

% ===========================================================================

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

:- export(memo_ctcheck_sum/1).
memo_ctcheck_sum(false) :-
    retract_fact(is_any_false(_)),
    asserta_fact(is_any_false(yes)).
memo_ctcheck_sum(check) :-
    retract_fact(is_any_check(_)),
    asserta_fact(is_any_check(yes)).

% ===========================================================================
% Process assertion level

:- export(inform_as_change_to_user/5).
inform_as_change_to_user(Old,OldRef,New,AbsInts,Info) :-
    current_pp_flag(pplog,L),
    ( member(ctchecks, L) -> VCT = on ; VCT = off ),
    current_pp_flag(asr_not_stat_eval,STAT),
    ( get_interval_check(Old, IvalCheck) ->
        decide_inform_user_interval(VCT, STAT, IvalCheck, Old, OldRef, New, AbsInts, Info)
    ; decide_inform_user(VCT, STAT, Old, OldRef, New, AbsInts, Info)
    ).

% checked assertion, ctchecks pplog
decide_inform_user(VCT, _STAT, Old, OldRef, New, AbsInts, Info) :-
    New = as${status => Status, type => Type},
    checked_or_true(Status),
    !,
    change_assertion_status(Old, OldRef, New),
    local_inccounter_split(simp,checked,Type,_),
    ( VCT = on ->
        inform_checked(Old, New, AbsInts, Info)
    ; true
    ).
% false or check assertions
decide_inform_user(VC, STAT, Old, OldRef, New, AbsInts, Info):-
    New = as(_,Status,Type,Goal,_,_,_,_,_,_,_,_),
    ( Status = check, current_pp_flag(client_safe_ctchecks, on) ->
        % IG: why client_safe_ctchecks not used in the previous clause (checked)?
        % Do not inform on check calls assertions of exported predicates
        ( type_of_goal(exported, Goal) -> fail ; true )
    ; true
    ),
    %
    !,
    local_inccounter_split(simp,Status,Type,_),
    ( Status = false  ->
        change_assertion_status(Old, OldRef, New)
    ; current_pp_flag(simplify_checks, on) ->
        erase(OldRef),
        add_assertion(New)
    ; true
    ),
    ( VC = on ->
        inform_non_checked(STAT, Old, New, AbsInts, Info)
    ; true
    ).
% (otherwise)
decide_inform_user(_Flag1,_Flag2,_Old,_OldRef,_New,_Dom,_Info) :- !.


% By design we preserve original calls/success/comp in the output;
% perhaps we could just update the status in the original assertion.
change_assertion_status(Old, OldRef, New) :-
    Old = as${comp => OldComp, call => OrigCall, succ => OrigSuccess},
    assertion_set_calls(New, OrigCall, A2),
    assertion_set_success(A2, OrigSuccess, A3),
    assertion_set_comp(A3, OldComp, NewToPrint),
    erase(OldRef), %% TODO: [IG] Why erase the assertion when printing the
                   %% message and not when the assertion is checked?
    add_assertion(NewToPrint).

:- export(inform_checked/4).
inform_checked(Old, New, AbsInts, Info) :-
    New = as${type => Type, dic => Dict, call => Call},
    Old = as${head => Goal, locator => Loc},
    %
    prepare_output_info(AbsInts, Info, Goal, Type, RelInfo),
    copy_term((Old,Dict), (OldCopy,DictCopy)),
    name_vars(DictCopy),
    prettyvars(OldCopy),
    Loc = loc(_File, FromL, ToL),
    % TODO: (MH) Simplifying for now the message since presumably
    %       at this point the assertion is totally checked. If
    %       there has been some simplification then we should show
    %       the new assertion (but that should be done in the case
    %       below?)  Old:
    %% note_message("(lns ~d-~d) The assertion:~n~p has been changed to~n~p",
    %%              [FromL, ToL, Old,NewToPrint])
    ( RelInfo = [] ->
        note_message("(lns ~d-~d) Trivially verified assertion:~n"||
            "~p"||
            "because the predicate is unreachable", 
            [FromL, ToL, OldCopy])
    ; member('$dom'(_,[[bottom]],_), RelInfo) ->
        note_message("(lns ~d-~d) Trivially verified assertion:~n"||
            "~p"||
            "because the predicate never succeeds (for the given precondition)",
            [FromL, ToL, OldCopy])
    ; Call == [fail] ->
        note_message("(lns ~d-~d) Trivially verified assertion:~n"||
            "~p"||
            "because the predicate is never called with the given precondition",
            [FromL, ToL, OldCopy])
    ; note_message("(lns ~d-~d) Verified assertion:~n"||
          "~p", 
          [FromL, ToL, OldCopy])
    ).

:- export(inform_non_checked/5).
inform_non_checked(STAT, Old, New, AbsInts, Info) :-
    New = as(_,Status,Type,Goal,_,Call,Success,Comp,Dict,Loc,_,_),
    prepare_output_info(AbsInts, Info, Goal, Type, RelInfo),
    ( Status = check ->
        filter_left_over(Type, Call, Success, Comp, LeftL),
        list_to_conj(LeftL, Left0)
    ; Left0 = [] % dummy, not used if the assertion is false
    ),
    copy_term((Old,RelInfo,Left0,Dict),(OldCopy,RelInfoCopy,Left,DictCopy)),
    name_vars(DictCopy),
    prettyvars((OldCopy,Left,RelInfoCopy)),
    Loc = loc(_File, RFrom, To),
    ( RFrom == To -> From = RFrom ; From is RFrom + 1 ), % ?????
    ( Status = check ->
        %  show_message(STAT, "(lns ~d-~d) Cannot verify assertion:~n~pbecause on ~p ~p :~n~p ~nLeft to prove: ~w~n", 
        %              [From, To, Old, Type, GoalCopy, '$an_results'(RelInfoCopy), Left]),
        % MH: Changed to this message format which seems easier to read. Same with rest of messages.
        show_message(STAT, "(lns ~d-~d) Could not verify assertion:~n"||
            "~p"||
            "because~n"||
            "    ~p~n"||
            "could not be derived from inferred ~p:"||
            "~p", 
            [From, To, OldCopy, Left, Type, '$an_results'(RelInfoCopy)]),
        memo_ctcheck_sum(check)
    ; % error_message("(lns ~d-~d) False assertion:~n~pbecause on ~p ~p :~n~p", 
      %               [From, To, Old, Type, GoalCopy, '$an_results'(RelInfoCopy)]),
      % TODO: (MH) we should get from the partial evaluator the first property that fails!
      error_message("(lns ~d-~d) False assertion:~n"||
          "~p"||
          "because the ~p field is incompatible with inferred ~p:"||
          "~p", 
          [From, To, OldCopy, Type, Type, '$an_results'(RelInfoCopy)]),
      memo_ctcheck_sum(false)
    ).

:- export(local_inccounter_split/4).
local_inccounter_split(Proc,Status,Type,Val) :-
    ( Type = calls -> T = c ; T = s),
    atom_concat([Proc,'_',Status,'_',T], Counter),
    local_inccounter(Counter, Val).

local_inccounter(Counter, Val) :- % in case the counter is not defined
    inccounter(Counter, Val),!.
local_inccounter(_, _).

checked_or_true(checked).
checked_or_true(true).

%----------------------------------------------------------------------
% For '~p' in error_message/2 and related

% TODO: enable/disable with a flag

:- use_module(engine(stream_basic), [current_output/1]).
:- use_module(library(streams), [tab/1, nl/0]).
:- use_module(ciaopp(p_unit/p_printer), [print_assrt/2]).

:- multifile portray/1.

% Assertions
portray(A) :- A = as${}, !,
    current_output(CO),
    print_assrt(A, CO). % (always newline ended)
% Analysis results
portray('$an_results'(Res)) :-
    find_tab(Res,ResT),
    write_results(ResT).
% AbsInt values
portray('$dom'(Dom,Res,Rules,Tab)) :-
    name(Dom,Lst), length(Lst,Len),
    format("~n[~w]",[Dom]),
    TabLen is Tab - Len + 1,
    tab(TabLen),
    % MH Looks better without...
    % format(": ",[]),
    ( Dom == generic_comp ->
        sort(Res, Res2),
        list_to_conj(Res2,ResConj),
        write(ResConj), nl
    ; write_info(Res, Tab)
    ),
    ( Rules = [] ->
        nl
    ; format("~nwith:~n~n",[]),
      % Flag for a format of rules here 
      write_rules(Rules)
    ).

write_results([]).
write_results([R|Rs]) :-
    print(R),
    write_results(Rs).

write_info([],_).
write_info([A|As],Tab) :- 
    format("~w ",[A]),
    ( As \== [] ->
        format(" OR ~n",[]),
        TabLen is Tab + 5,
        tab(TabLen)
    ; true
    ),
    write_info(As,Tab).

write_rules([]).
write_rules([typedef(::=(H,B))|Rules]) :-
    write_one_type(typedef(::=(H,B)), user_output),
%     format("~w ::= ~w~n",[H,B]),
%     ( Rules \== [] ->
%         format("      ",[])
%     ; true
%     ),
    write_rules(Rules).

find_tab(Res,ResT) :-
    find_tab_x(Res,Tab,Tab,ResT).

find_tab_x([],_,0,[]).
find_tab_x(['$dom'(Dom,Res,Rules)|Rs],Tab,MaxTab,['$dom'(Dom,Res,Rules,Tab)|RsT]) :-
    name(Dom,List),
    length(List,Length),
    find_tab_x(Rs,Tab,MaxTab1,RsT),
    find_max(MaxTab1,Length,MaxTab).

find_max(A,B,C) :- A > B, !, C = A.
find_max(_,B,B).

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

%:- export(filter_left_over/5).
filter_left_over(calls, Call, _, _, Call).
filter_left_over(success, _, Succ, _, Succ).
filter_left_over(comp, _, _, Comp, Comp).

:- export(name_vars/1).
name_vars([]).
name_vars([V='$VAR'(V)|Vs]):-
    name_vars(Vs).

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

trans_aux(comp,generic_comp,_Goal,[],[['No info available']]) :-!.
trans_aux(_ ,_ ,_, [],[]) :-!.
trans_aux(calls,AbsInt,Head,[complete(G,C,_Ss,_,_)|Completes],[CInfo1|CInfo]):-!,   
    varset(G,Qv),
    adapt_info_to_assrt_head(AbsInt,G,Qv,C,Head,C1),
    my_asub_to_info(AbsInt,C1,Qv,CInfo1,_Comp),
    trans_aux(calls,AbsInt,Head,Completes,CInfo).
trans_aux(calls_pp(G),AbsInt,Head,Call,[CInfo]):-!,   
    varset(G,Qv),
    adapt_info_to_assrt_head(AbsInt,G,Qv,Call,Head,C1),
    varset(Head,Hv),
    project(AbsInt,Head,Hv,[],C1,C2),
    my_asub_to_info(AbsInt,C2,Qv,CInfo,_Comp).
trans_aux(success,AbsInt,Head,[complete(G,_C,Ss,_,_)|Completes],SInfoL):-!,  
    collect_success_info(Ss,AbsInt,Head,G,SInfoL1),
    append(SInfoL1,SInfoL2,SInfoL),
    trans_aux(success,AbsInt,Head,Completes,SInfoL2).
trans_aux(success_pp(G),AbsInt,Head,Ss,SInfoL):-!,  
    collect_success_info([Ss],AbsInt,Head,G,SInfoL).
%       append(SInfoL1,SInfoL2,SInfoL).
%       trans_aux(success,AbsInt,Goal,Completes,SInfoL2).
trans_aux(success,_,_Goal,Info,Info):-!.  % for size properties
trans_aux(comp,generic_comp,_Goal,Info,Info):-!.
%%      displayq(Info).
trans_aux(comp,_AbsInt,_Goal,_Info,[]).

collect_success_info([],_AbsInt,_Head,_G,[]).
collect_success_info([S|Ss],AbsInt,Head,G,[SInfo|SInfoTail]):-
    varset(G,Qv),
    adapt_info_to_assrt_head(AbsInt,G,Qv,S,Head,S_tmp),
    varset(Head,Hv),
    project(AbsInt,Head,Hv,[],S_tmp,S1),
    my_asub_to_info(AbsInt,S1,Qv,SInfo,_Comp),
    collect_success_info(Ss,AbsInt,Head,G,SInfoTail).

my_asub_to_info(_AbsInt,'$bottom',_Qv,[bottom],_Comp):-!.
my_asub_to_info(AbsInt,S1,Qv,SInfo,Comp):-
    asub_to_info(AbsInt,S1,Qv,SInfoL,Comp),!,
    list_to_conj(SInfoL,SInfo).

inline_types([bottom]) :-!.
inline_types((Prop,Props)):- !,
    inline_types(Prop),
    inline_types(Props).
inline_types(Prop):-
    denorm_goal_prop(Prop,P,P).

