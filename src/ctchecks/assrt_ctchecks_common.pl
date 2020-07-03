:- module(assrt_ctchecks_common, [
    check_type_calls/2,
    get_assertions/3,
    get_calls_assertion/4,
    get_entry_assertion/4,
%%      num_var_in_goal/4,
    pp_check/2,
    recorda_assertion/2,
    synt_compose_disj/3,
    synt_compose_conj/3,
    synt_compose_list/3
%       native_props/2  %% GP: exported for use in ctchecks.pl. Is this OK?
], [assertions, regtypes, isomodes, datafacts]).

:- use_module(library(formulae), [list_to_conj/2]).

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [
    assertion_read/9,
    add_assertion_read/9, 
    remove_assertion_read/9]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(library(lists), [member/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(ciaopp(p_unit/unexpand), [transform_metapred/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

check_type_calls(Goal,Calls):-
    type_of_goal(imported,Goal),
    get_calls_assertion(Goal,pp,Calls,_),
    nonvar(Calls).

% pp_check(Goal,Props):-
%       type_of_goal(builtin(check(Props0)),Goal),
%       assrt_ctchecks_common:native_props(Props0,Props).
% CGoal = Complex goal
pp_check(CGoal,Props):-
    curr_file( _, M ),
    transform_metapred( CGoal, M, Goal ),
    type_of_goal(builtin(check(Props)),Goal).
%       unexpand_meta_calls(Goal,CheckGoal),
%       CheckGoal =.. [_,Props].

%recorda_assertion(_,_):- !.
recorda_assertion(Goal,assert(loc(S,LB,LE),Status,Kind,Body,D)):-
    % supposedly, all assertions are from current module
    current_fact(curr_file(_,M)),
    assertion_body(Goal,Compat0,Call0,Succ0,Comp0,Comm,Body),
%       inverse_native_props(Compat0,Compat),
%       inverse_native_props(Call0,Call),
%       inverse_native_props(Succ0,Succ),
%       inverse_native_props(Comp0,Comp),
    Comp0 = Comp,
    Succ0 = Succ,
    list_to_conj( Call , Call0 ),
    Compat0 = Compat,
    assertion_body(Goal,Compat,Call,Succ,Comp,Comm,NBody),
    add_assertion_read(Goal,M,Status,Kind,NBody,D,S,LB,LE).

:- pred get_assertions(+,+,-) # "Returns the recorded assertions.".
get_assertions([],[],[]).
get_assertions([K|Keys],[P|Preds],AllAss):-
    get_basic_assertions(P,G,Ass),
    (Ass == [] ->
        AllAss = MoreAss
    ;
        AllAss = [(K,G,Ass)|MoreAss]),
    get_assertions(Keys,Preds,MoreAss).

get_basic_assertions(F/A,Goal,BA):-
    functor(Goal,F,A),
    get_calls_assertion(Goal,pred,BA,BA0),
    findall( assert(loc(S,LB,LE),check,Kind,NBody,D),
             ( member(Kind,[success,comp]),
               remove_assertion_read(Goal,_,check,Kind,Body,D,S,LB,LE),
               change_body(Body,NBody)
             ),
             BA0 ).

change_body(Body,Body).

%% change_body(Body,NBody):-
%%      assertion_body(Goal,Compat0,Call0,Success0,Comp0,Comm,Body),
%%      native_props(Compat0,Compat),
%%      native_props(Call0,Call),
%% %%   llist_to_disj(Call0,Call1),
%% %%   null_disj(Call1,Call),
%%      native_props(Success0,Success),
%%      native_props(Comp0,Comp),
%%      assertion_body(Goal,Compat,Call,Success,Comp,Comm,NBody).
%% 
%% null_disj([],true):- !.
%% null_disj(Call,Call).
%% 
%% native_props([I],N):- !,
%%      native_prop_(I,N).
%% native_props([I|Info],(N,Nat)):- !,
%%      native_prop_(I,N),
%%      native_props(Info,Nat).
%% native_props([],true):- !.
%% native_props((I1;I2),(N1;N2)):- !,
%%      native_props(I1,N1),
%%      native_props(I2,N2).
%% native_props((I1,I2),(N1,N2)):- !,
%%      native_props(I1,N1),
%%      native_props(I2,N2).
%% native_props(I,N):-
%%      native_prop_(I,N).
%% 
%% inverse_native_props((I1;I2),[(N1;N2)]):- !,
%%      inverse_native_props(I1,N1),
%%      inverse_native_props(I2,N2).
%% inverse_native_props((I1,I2),[N1|N2]):- !,
%%      inverse_native_props(I1,N1),
%%      inverse_native_props(I2,N2).
%% inverse_native_props(I,[N]):-
%%      native_prop_(N,I).
%% 
%% native_prop_(I,N):- native_to_prop(I,N), !.
%% native_prop_(I,I).

get_calls_assertion(Goal,pred,BA,BA0):-
    assertion_read(Goal,_,check,calls,_Body,D,S,LB,LE), !,
    BA = [ assert(loc(S,LB,LE),check,calls,Bodies,D) |BA0],
    assertion_body(Goal,true,Calls,true,true,[],Bodies),
    findall( (Goal,Call),
             ( % will be asserted by _pred afterwards
               remove_assertion_read(Goal,_,check,calls,Body,_D,_S,_LB,_LE),
               assertion_body(Goal,_Compat,Call0,_Succ,_Comp,_Comm,Body),
               Call0 = Call
%                  assrt_ctchecks_common:native_props(Call0,Call)
             ),
             Calls0 ),
    group_calls(Calls0,Goal,Calls).
get_calls_assertion(Goal,pp,Calls,Dict):-
    assertion_read(Goal,_,Status,calls,_Body,Dict,_S,_LB,_LE),
    ( current_pp_flag(run_diagnosis,on) ->
      member(Status,[check, false]), LS = [true,check,trust,false]
    ; member(Status,[check]), LS = [true,check,trust]
    ),
%       member(Status,[true,check,trust]),
    !,      
    findall( (Goal,Call),
             ( assertion_read(Goal,_M,Status,calls,Body,_D,_S,_LB,_LE),
         %      member(Status,[check,checked,false]),
                member(Status,LS),
               assertion_body(Goal,_Compat,Call,_Succ,_Comp,_Comm,Body)
%               ,   assrt_ctchecks_common:native_props(Call0,Call)
             ),
             Calls0 ),
    group_calls(Calls0,Goal,Calls).
get_calls_assertion(_Goal,_,BA,BA).

get_entry_assertion(Goal,pp,Calls,Dict):-
    assertion_read(Goal,_,Status,entry,_Body,Dict,_S,_LB,_LE),
%       member(Status,[check]),
%       member(Status,[true,check,trust]),
    !,
    findall( (Goal,Call),
             ( assertion_read(Goal,_M,Status,entry,Body,_D,_S,_LB,_LE),
         %      member(Status,[check,checked,false]),
    %           member(Status,[true,check,trust]),
               assertion_body(Goal,_Compat,Call,_Succ,_Comp,_Comm,Body)
%               ,   assrt_ctchecks_common:native_props(Call0,Call)
             ),
             Calls0 ),
    group_calls(Calls0,Goal,Calls).
get_entry_assertion(_Goal,_,BA,BA).

group_calls([(Goal,Call)],Goal,[Call]):- !.
group_calls([(Goal,Call)|More],Goal,(Call;Calls)):-
    group_calls(More,Goal,Calls).

% --------------------------------------------------------------------------

synt_compose_conj(true,NewExp2,NewExp2):-!.
synt_compose_conj(NewExp1,true,NewExp1):-!.
synt_compose_conj(_NewExp1,fail,fail):-!.
synt_compose_conj(NewExp1,NewExp2,[NewExp1,NewExp2]).

synt_compose_list(true,NewExp2,NewExp2):-!.
synt_compose_list(NewExp1,true,NewExp1):-!.
synt_compose_list(_NewExp1,fail,fail):-!.
synt_compose_list(NewExp1,NewExp2,[NewExp1,NewExp2]).

synt_compose_disj(fail,NewExp2,NewExp2):-!.
synt_compose_disj(_NewExp1,true,true):-!.
synt_compose_disj(NewExp1,fail,NewExp1):-!.
synt_compose_disj(NewExp1,NewExp2,(NewExp1;NewExp2)).

%% num_var_in_goal(0,Goal,_Var,_Num):-!,
%%      message("Type for argument not in ~q~n",[Goal]).
%% num_var_in_goal(A,Goal,Var,Num):-
%%      arg(A,Goal,VarGoal),
%%      VarGoal == Var,!,
%%      Num = A.
%% num_var_in_goal(A,Goal,Var,Num):-
%%      A1 is A -1,
%%      A1 > 0,
%%      num_var_in_goal(A1,Goal,Var,Num).
