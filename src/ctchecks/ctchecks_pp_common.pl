:- module(ctchecks_pp_common, [
    check_type_calls/2,
    get_calls_assertion/3,
    get_entry_assertion/3,
%%      num_var_in_goal/4,
    pp_check/2
%       native_props/2  %% GP: exported for use in ctchecks.pl. Is this OK?
], [assertions, regtypes, isomodes, datafacts]).

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(ciaopp(p_unit/unexpand), [transform_metapred/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

check_type_calls(Goal,Calls):-
    type_of_goal(imported,Goal),
    get_calls_assertion(Goal,Calls,_),
    nonvar(Calls).

pp_check(CGoal,Props):-
    curr_file( _, M ),
    transform_metapred( CGoal, M, Goal ),
    type_of_goal(builtin(check(Props)),Goal).

get_calls_assertion(Goal,Calls,Dict):-
    assertion_read(Goal,_,Status0,calls,_Body,Dict,_S,_LB,_LE),
    % TODO: Why are `true` assertions considered here?
    ( current_pp_flag(run_diagnosis,on) ->
      member(Status0,[check, false]), LS = [true,check,trust,false]
    ; member(Status0,[check]), LS = [true,check,trust]
    ),
%       member(Status,[true,check,trust]),
    !,      
    findall( (Goal,Call),
             ( assertion_read(Goal,_M,Status,calls,Body,_D,_,_,_),
         %      member(Status,[check,checked,false]),
                member(Status,LS),
               assertion_body(Goal,_Compat,Call,_Succ,_Comp,_Comm,Body)
%               ,   assrt_ctchecks_common:native_props(Call0,Call)
             ),
             Calls0 ),
    group_calls(Calls0,Goal,Calls).
get_calls_assertion(_Goal,BA,BA).

get_entry_assertion(Goal,Calls,Dict):-
    assertion_read(Goal,_,_Status,entry,_Body,Dict,_S,_LB,_LE),
%       member(Status,[check]),
%       member(Status,[true,check,trust]),
    !,
    findall( (Goal,Call),
             ( assertion_read(Goal,_M,_,entry,Body,_D,_,_,_),
         %      member(Status,[check,checked,false]),
    %           member(Status,[true,check,trust]),
               assertion_body(Goal,_Compat,Call,_Succ,_Comp,_Comm,Body)
%               ,   assrt_ctchecks_common:native_props(Call0,Call)
             ),
             Calls0 ),
    group_calls(Calls0,Goal,Calls).
get_entry_assertion(_Goal,BA,BA).

group_calls([(Goal,Call)],Goal,[Call]):- !.
group_calls([(Goal,Call)|More],Goal,(Call;Calls)):-
    group_calls(More,Goal,Calls).
