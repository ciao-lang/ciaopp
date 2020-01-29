:- module(comp_ctchecks, [
    abs_execute_comp/5,
    abs_execute_sizes/5
], [assertions]).

:- use_module(ciaopp(infer/infer), [get_info/5]).
:- use_module(ciaopp(infer/infer_dom), [abs_execute_with_info/4, knows_of/2]).
:- use_module(ciaopp(p_unit/assrt_norm), [denorm_goal_prop/3]).
:- use_module(ciaopp(p_unit), [prop_to_native/2]).
:- use_module(library(lists),      [append/3, list_concat/2]).
:- use_module(library(aggregates)).

 %% :- doc(bug,"1. The success part of cost information (arg sizes) is not
 %%     considered for checks.").
 %% :- doc(bug,"2. Cost expressions have length($(1)) while it should be %
 %%     $(1). This might give problems.").

:- doc(bug,"3. The check assertions with resource-related properties
               should be review in more detail.").


abs_execute_comp(Goal,Comp,AComp,NewComp,Status):-
    get_cost_info(Goal,Cost0,_Succ),
    get_resource_info(Goal,Resource,_Succ2), 
    append(Cost0,Resource,Cost),
    get_nf_info(Goal,_Call0,Nf),
    get_det_info(Goal,_Call1,Det),
    append(Nf,Det,NfDet),
    append(Cost,NfDet,AComp0),     
    append(Resource,AComp0,AComp), 
    check_comp_info(Comp,Cost,Nf,Det,true,Status,NewComp).

% Commented by JNL (06/06/07)
% abs_execute_comp(Goal,Comp,AComp,NewComp,Status):-
% %        display(user,assertion(Comp)), nl(user),
%         get_cost_info(Goal,Cost,_Succ),
%       get_resource_info(Goal,Resource,_Succ2), %EMM
% %        display(user,get_cost_info(Goal,Cost,_Succ)), nl(user),
%         get_nf_info(Goal,_Call0,Nf),
% %        display(user,get_nf_info(Goal,_Call0,Nf)), nl(user),
%         get_det_info(Goal,_Call1,Det),
% %        display(user,get_det_info(Goal,_Call1,Det)), nl(user),
%         append(Nf,Det,NfDet),
%         append(Cost,NfDet,AComp0),     %EMM
%       append(Resource,AComp0,AComp), %EMM
%         % conj_to_list(Comp,LComp),
%         check_comp_info(Comp,Cost,Nf,Det,true,Status,NewComp).
%         % check_comp_info(LComp,Cost,Nf,Det,true,Status,NewLComp),
%         % list_to_conj(NewLComp,NewComp).

% Modified by EMM
abs_execute_sizes(Goal,Size,ASize,NewSize,Status):-
    get_cost_info(Goal,_,Succ0),
    get_resource_info(Goal,_,Succ1),
    append(Succ0,Succ1,Succ2),
    get_size_info(Goal,_,Succ3),
    append(Succ2,Succ3,ASize),
    check_size_info(Size,ASize,true,Status,NewSize).

check_comp_info([],_Cost,_Nf,_Det,Status,Status,[]).
check_comp_info([C|Comp],Cost,Nf,Det,Status0,Status,NewComp):-
    prop_to_native(C,Prop0),
    denorm_goal_prop(Prop0,Prop,_),
    check_comp_info_one(Prop,Cost,Nf,Det,Status1),
    compose_status(Status0,Status1,Status2),
    new_comp(Status1,C,NewComp1,NewComp),
    check_comp_info(Comp,Cost,Nf,Det,Status2,Status,NewComp1).

check_comp_info_one(finite_solutions(P),Cost,Nf,Det,Status):- !,
    check_comp_info_one(terminates(P),Cost,Nf,Det,Status0),
    check_comp_info_one(not_fails(P),Cost,Nf,Det,Status1),
    compose_status(Status0,Status1,Status).
check_comp_info_one(C,Cost,Nf,Det,Status):-
    knows_of(C,Dom),
    select_info(Dom,Cost,Nf,Det,Info),
    abs_execute_with_info(Dom,Info,C,Status0), !,
    new_status(Status0,Status).
check_comp_info_one(_C,_Cost,_Nf,_Det,check).

% 

check_size_info([],_Size,Status,Status,[]).
check_size_info([C|Comp],Size,Status0,Status,NewComp):-
    prop_to_native(C,Prop),
    check_size_info_one(Prop,Size,Status1),
    compose_status(Status0,Status1,Status2),
    new_comp(Status1,C,NewComp1,NewComp),
    check_size_info(Comp,Size,Status2,Status,NewComp1).

check_size_info_one(C,Size,Status):-
    knows_of(C,Dom),
    abs_execute_with_info(Dom,Size,C,Status0), !,
    new_status(Status0,Status).
check_size_info_one(_C,_Size,check).


new_status(fail,false):- !.
new_status(Status,Status).


select_info(steps_ub,Cost,_Nf,_Det,Cost).
select_info(steps_lb,Cost,_Nf,_Det,Cost).
select_info(steps_o,Cost,_Nf,_Det,Cost).
select_info(resources,Cost,_Nf,_Det,Cost).
select_info(nfg,_Cost,Nf,_Det,Nf).
select_info(detg,_Cost,_Nf,Det,Det).
select_info(det,_Cost,_Nf,Det,Det).
select_info(res_plai,Cost,_,_,Cost).

compose_status(true,Status,Status).
compose_status(Status,true,Status).
compose_status(false,_Status,false).
compose_status(_Status,false,false).
compose_status(check,check,check).

new_comp(true,_C,NewComp,NewComp).
new_comp(_any,C,NewComp,[C|NewComp]).

get_cost_info(Goal,Cost,Succ):-
    (  get_info(steps_ub,pred,_Key,Goal,(SuccU,CostU))
    -> append(CostU,CostLO,Cost),
       append(SuccU,SuccLO,Succ)
     ; Cost=CostLO,
       Succ=SuccLO
    ),
    (  get_info(steps_lb,pred,_Key,Goal,(SuccL,CostL))
    -> append(CostL,CostO,CostLO),
       append(SuccL,SuccO,SuccLO)
     ; CostLO=CostO,
       SuccLO=SuccO 
    ),
    (  get_info(steps_o,pred,_Key,Goal,(SuccO,CostO))
    -> true
     ; CostO= [],
       SuccO= []
    ).

get_resource_info(Goal,Cost,[]):-
    ( setof( LRes,
             Key^Succ^get_info(resources,pred,Key,Goal,(Succ,LRes)),
             LLRes) ->
      true
    ; LLRes = []
    ),
    ( setof( LRes,
             Key^Succ^get_info(res_plai,pred,Key,Goal,(Succ,LRes)),
             LLRes_p) ->
      true
    ; LLRes_p = []
    ),
    % ( get_info(res_plai,pred,_,Goal,(SuccR,LResR)), LLRes_p = [[(SuccR,LResR)]]
    % ; LLRes_p = []
    % ),
    append(LLRes_p,LLRes,ListR),list_concat(ListR,Cost).

% get_res_plai_info(Goal,Cost,[]):-
%       ( setof( LRes,
%                Key^Succ^get_info(res_plai,pred,Key,Goal,(Succ,LRes)),
%                LLRes) ->
%         true
%       ; LLRes = []
%       ),
%       list_concat(LLRes,Cost).

get_size_info(Goal,Cost,Succ):-
    (  get_info(size_ub,pred,_Key,Goal,(SuccU,CostU))
    -> append(CostU,CostLO,Cost),
       append(SuccU,SuccLO,Succ)
     ; Cost=CostLO,
       Succ=SuccLO
    ),
    (  get_info(size_lb,pred,_Key,Goal,(SuccL,CostL))
    -> append(CostL,CostO,CostLO),
       append(SuccL,SuccO,SuccLO)
     ; CostLO=CostO,
       SuccLO=SuccO 
    ),
    (  get_info(size_o,pred,_Key,Goal,(SuccO,CostO))
    -> true
     ; CostO= [],
       SuccO= []
    ).


get_nf_info(Goal,Call,Nf):-
%       get_info(nfg,pred,Call,Goal,Nf), !.
    get_info(nonfail,pred,Call,Goal,Nf), !.
get_nf_info(_Goal,_Call,[]).

get_det_info(Goal,Call,Det):-
    get_info(detg,pred,Call,Goal,Det), !.
get_det_info(Goal,Call,Det):-
    get_info(is_det,pred,Call,Goal,(_,Det)), !.
get_det_info(_Goal,_Call,[]).
