:- module(_, [], [assertions, isomodes, regtypes, datafacts, nativeprops, ciaopp(ciaopp_options)]).

:- doc(title, "Messages for predicate compile-time checking").

:- doc(module, "This module prints the messages emitted during
       compile-time checking of predicate-level assertions.").

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- use_module(library(formulae), [list_to_conj/2]).
:- use_module(library(hiordlib), [maplist/2]).
:- use_module(library(messages), [
    show_message/3, warning_message/2, error_message/2, note_message/2]).

:- use_module(ciaopp(p_unit), [
    add_assertion/1,
    assertion_set_status/3,
    assertion_set_calls/3,
    assertion_set_success/3,
    assertion_set_comp/3]).
:- use_module(ciaopp(p_unit/p_unit_basic), [type_of_goal/2]).
:- use_module(ciaopp(frontend_driver), [write_one_type/2]). % TODO: move somewhere else
:- use_module(ciaopp(preprocess_flags)).

:- use_module(library(lists), [length/2]).
:- use_module(library(sort)).
:- use_module(library(write)).
:- use_module(library(format)).
:- use_module(library(counters), [inccounter/2]).
:- use_module(library(terms), [atom_concat/2]).

:- use_module(ciaopp(ctchecks/ctchecks_common),
              [memo_ctcheck_sum/1,prepare_output_info/5,name_vars/1]).

:- if(defined(has_ciaopp_cost)).
:- use_module(ciaopp(ctchecks/ctchecks_intervals), [
    get_interval_check/2,
    decide_inform_user_interval/8
]).
:- else.
get_interval_check(_, _) :- fail.
decide_inform_user_interval(_, _, _, _, _, _, _, _).
:- endif.

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
        maplist(erase, OldRef),
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
    maplist(erase,OldRef),  %% TODO: [IG] Why erase the assertion when printing the
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
      current_output(CO),
      write_rules(Rules, CO)
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

write_rules([], _S).
write_rules([typedef(::=(H,B))|Rules], S) :-
    write_one_type(typedef(::=(H,B)), S),
%     format("~w ::= ~w~n",[H,B]),
%     ( Rules \== [] ->
%         format("      ",[])
%     ; true
%     ),
    write_rules(Rules, S).

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

%:- export(filter_left_over/5).
filter_left_over(calls, Call, _, _, Call).
filter_left_over(success, _, Succ, _, Succ).
filter_left_over(comp, _, _, Comp, Comp).
