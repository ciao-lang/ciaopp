:- module(ctchecks_common, [
    check_type_calls/2,
    get_check_assertion/3,
%%      num_var_in_goal/4,
    pp_check/2
%       native_props/2  %% GP: exported for use in ctchecks.pl. Is this OK?
], [assertions, regtypes, isomodes, datafacts]).

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [ref_assertion_read/10]).
:- use_module(library(formulae), [list_to_conj/2, list_to_disj/2]).
:- use_module(library(messages), [debug_message/2]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(ciaopp(p_unit/unexpand), [transform_metapred/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

check_type_calls(Goal,Calls):-
    type_of_goal(imported,Goal),
    get_entrycalls_assertion(calls,Goal,Calls,_),
    nonvar(Calls).

pp_check(CGoal,Props):-
    curr_file( _, M ),
    transform_metapred( CGoal, M, Goal ),
    type_of_goal(builtin(check(Props)),Goal).

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
    Type = success,
    ref_assertion_read(Goal, M, Status, Type, Body, Dic, S, LB, LE, ARef),
    rebuild_assertion(M, Status, Type, Body, Dic, S, LB, LE, Assertion),
    Refs = [ARef],
    debug_message("success assertion found ~q",[Assertion]).

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
    Call = [Call1],
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
