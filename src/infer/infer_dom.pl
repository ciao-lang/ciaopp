:- module(infer_dom,
    [ asub_to_info/6,
      asub_to_out/6,
      asub_to_props/4, 
      abs_execute_with_info/4,
      does_not_use_memo_lub/1,
      flag_is/3,
      flag_set/3,
      knows_of/2,
      non_collapsable/1
    ],
    [assertions, regtypes, datafacts, ciaopp(ciaopp_options)]).

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- if(defined(has_ciaopp_cost)).
%[LD] for interval
:- use_module(infercost(algebraic/polynom_comp),
      [
      polynom_root_interval/3,
      difference/3,
      polynomize/2,
      validate_polynom/2,
      polynom_current_assertion/1,
      polynom_message/7, 
      brute_eval_intervals/3,
      eval_arith/3,
      compute_safe_intervals/4
      ]).
%:- use_module(library(format)).
%[/LD] for interval
:- endif.

:- use_module(ciaopp(infer/inferseff), [seff_property/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- if(defined(has_ciaopp_cost)).
:- use_module(infercost(algebraic), 
    [ exp_greater_eq_than/2,
      exp_greater_than/2,
      exp_eq_than/2,
      order_of_function/2,
      complexity_order_greater_than/2,
      complexity_order_greater_eq_than/2
    ]).
:- use_module(infercost(infercost_register), 
    [ is_time_analysis/1,
      is_size_analysis/1,
      is_single_complexity_analysis/1,
      is_ualb_complexity_analysis/3,
      is_complexity_analysis/1
    ]).
:- endif.
%
:- use_module(ciaopp(p_unit), [prop_to_native/2]).
:- use_module(ciaopp(p_unit/assrt_norm), [norm_goal_prop/3]).
:- use_module(spec(abs_exec),      [abs_exec/4, determinable/2]).
:- use_module(spec(abs_exec_cond), [cond/4]).
:- use_module(domain(termsd), [terms_internal_to_native/3]).
:- use_module(typeslib(typeslib), [make_prop_type_unary/2, equivalent_to_top_type/1]).
%
:- use_module(library(keys), [key_lookup/4]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(lists), [member/2,append/3,reverse/2]). %[LD] add reverse
% :- use_module(library(messages),
%     [warning_message/1,warning_message/2]). %[LD] for interval information
% Note and log:
% 31 Aug 2011: bug fix expression_greater_than
% 7 June 2011: polynom_greater_than change into expression_equal_greater_than
%              implementation without equality for computing false intervals
% 12 May 2011: minor reordering predicate for performance on
%              check_cost_interval and check_resource_interval
% 17 Feb 2011: capture small interval occurence as error [LD]
% ------------------------------------------------------------------------
:- doc(bug,"[LD] abs_execute_with_info(steps_o..) is not called when
   steps_o assertion exists, instead abs_execute_with_info(steps_ub..) is 
   called, therefore steps_o with interval gives empty interval").
:- doc(bug,"The role of statically_comp, abs_exec, determinable, etc.
   is a complete mess: should be made more consistent.").

:- doc(bug, "Handling of compatibility types and properties is missing."). 
:- doc(bug, "All references to old resource-related properties should
             be removed.").
% ------------------------------------------------------------------------

asub_to_out(nfg,_Goal,nf(Call0,Succ0,Fail,Cover),Call,Succ,[Fail,Cover]):- !,
    terms_internal_to_native(Call0,yes,Call),
    terms_internal_to_native(Succ0,yes,Succ).
asub_to_out(detg,_Goal,nf(Call0,Succ0,Fail,Cover),Call,Succ,[Fail,Cover]):- !,
    terms_internal_to_native(Call0,yes,Call),
    terms_internal_to_native(Succ0,yes,Succ).
asub_to_out(An,Goal,Abs,Call,Succ,Info):-
    asub_to_info(An,Goal,Abs,Call,Succ,Info0),
    norm_goal_props(Info0,Info,Goal).

norm_goal_props([],[],_).
norm_goal_props([GP|GPs],[NGP|NGPs],NPD) :-
    norm_goal_prop(GP,NGP,NPD),
    norm_goal_props(GPs,NGPs,NPD).

asub_to_info(tp,_Goal,Abs,[],[],[Abs]).
asub_to_info(seff,Goal,Abs,[],[],[Prop]):-
    seff_property(Abs,Goal,Prop).
asub_to_info(nfg,_Goal,nf(Call0,Succ0,Fail,Cover),Call,Succ,[Fail,Cover]):-
    terms_internal_to_native(Call0,no,Call),
    terms_internal_to_native(Succ0,no,Succ).
asub_to_info(detg,_Goal,nf(Call0,Succ0,Fail,Cover),Call,Succ,[Fail,Cover]):-
    terms_internal_to_native(Call0,no,Call),
    terms_internal_to_native(Succ0,no,Succ).
:- if(defined(has_ciaopp_cost)).
asub_to_info(resources,Goal,Abs,Call,Succ,Comp):-
    get_vartypes_from_resource_info(Abs, Call_VarType, Succ_VarType),
    complexity_property(Abs,resources,Goal,Succ0,Comp),
    terms_internal_to_native(Call_VarType,no,Call),
    terms_internal_to_native(Succ_VarType,no,New_Succ_VarType),
    append(New_Succ_VarType, Succ0, Succ).
asub_to_info(An,Goal,Abs,Call,Succ,Comp):-
    is_complexity_analysis(An), % TODO: missing cut?
    get_vartypes_from_complexity_info(Abs, Call_VarType, Succ_VarType),
    complexity_property(Abs,An,Goal,Succ0,Comp),
    terms_internal_to_native(Call_VarType,no,Call),
    terms_internal_to_native(Succ_VarType,no,New_Succ_VarType),
    append(New_Succ_VarType, Succ0, Succ).
:- endif.
asub_to_info(Anal,Goal,Abs,Call,Succ,Comp):-
    inferred_to_property(Anal,Goal,Abs,Call,Succ,Comp).

:- if(defined(has_ciaopp_cost)).
get_vartypes_from_complexity_info([_Abs_Lb, Abs_Ub], Call_VarType, Succ_VarType):-
    !, 
    Abs_Ub = complexity(Call_VarType, Succ_VarType, _Mode, _Measure, _Mutex, 
                        _Solution_Det, _Size, _Relation, _Time, _Domain).
get_vartypes_from_complexity_info(Abs, Call_VarType, Succ_VarType):-
    Abs=complexity(Call_VarType, Succ_VarType, _Mode, _Measure, _Mutex, 
                   _Solution_Det, _Size, _Relation, _Time, _Domain).

get_vartypes_from_resource_info(Abs, Call_VarType, Succ_VarType):-
    Abs=complexity(Call_VarType, Succ_VarType, _Mode, _Measure,
                   _Mutex, _Solution_Det, _Size, _Relation,
                   _Approx, _Resources, _Time, _Domain).

complexity_property([Abs_Lb, Abs_Ub],Cost_An,Goal,Succ,Comp):-
    is_ualb_complexity_analysis(Cost_An, Lower_An, Upper_An),
    !,
    complexity_property(Abs_Lb,Lower_An,Goal,SuccLb,CompLb),
    complexity_property(Abs_Ub,Upper_An,Goal,SuccUb,CompUb),
    append(SuccLb, SuccUb, Succ),
    append(CompLb, CompUb, Comp).
complexity_property(Abs,Cost,Goal,Succ,Comp):-
    asub_to_props(Cost,Goal,Abs,(Succ,Comp)).
:- endif.

:- multifile inferred_to_property/6.

% -------------------------------------------------------------------------

flag_is(_,_,_):- fail. % (default)
% Non-failure
flag_is(nf,not_fails,Flag):-
    Flag == not_fails.
flag_is(nf,possibly_fails,Flag):-
    Flag == possibly_fails.
flag_is(nf,covered,Flag):-
    Flag == covered.
flag_is(nf,not_covered,Flag):-
    Flag == not_covered.
% Determinism
flag_is(det,is_det,Flag):-
    Flag == not_fails.
flag_is(det,non_det,Flag):-
    Flag == possibly_fails.
flag_is(det,mut_exclusive,Flag):-
    Flag == covered.
flag_is(det,not_mut_exclusive,Flag):-
    Flag == not_covered.
:- if(defined(has_ciaopp_cost)).
% Resources
flag_is(res_plai,Prop,Flag) :-
    flag_set(nf,Prop,Flag).
flag_is(res_plai,Prop,Flag) :-
    flag_set(det,Prop,Flag).
% Resources (acc cost)
flag_is(res_plai_stprf,Prop,Flag) :-
    flag_set(nf,Prop,Flag).
flag_is(res_plai_stprf,Prop,Flag) :-
    flag_set(det,Prop,Flag).
% % Sizes
% flag_is(sized_types,Prop,Flag) :-
%       flag_set(nf,Prop,Flag).
% flag_is(sized_types,Prop,Flag) :-
%       flag_set(det,Prop,Flag).
:- endif.

flag_set(_,_,_):- fail. % (default)
% Non-failure
flag_set(nf,not_fails,Flag):-
    Flag = not_fails.
flag_set(nf,possibly_fails,Flag):-
    Flag = possibly_fails.
flag_set(nf,covered,Flag):-
    Flag = covered.
flag_set(nf,not_covered,Flag):-
    Flag = not_covered.
% Determinism
flag_set(det,is_det,Flag):-
    Flag = not_fails.
flag_set(det,non_det,Flag):-
    Flag = possibly_fails.
flag_set(det,mut_exclusive,Flag):-
    Flag = covered.
flag_set(det,not_mut_exclusive,Flag):-
    Flag = not_covered.
:- if(defined(has_ciaopp_cost)).
% Resources
flag_set(res_plai,Prop,Flag) :-
    flag_set(nf,Prop,Flag).
flag_set(res_plai,Prop,Flag) :-
    flag_set(det,Prop,Flag).
% Resources (acc cost)
flag_set(res_plai_stprf,Prop,Flag) :-
    flag_set(nf,Prop,Flag).
flag_set(res_plai_stprf,Prop,Flag) :-
    flag_set(det,Prop,Flag).
% % Size
% flag_set(sized_types,Prop,Flag) :-
%       flag_set(nf,Prop,Flag).
% flag_set(sized_types,Prop,Flag) :-
%       flag_set(det,Prop,Flag).
:- endif.

%-------------------------------------------------------------------------

:- doc(bug, "Unable to determine Approx.  It should be passed
    through the complexity structure.").

asub_to_props(_,_,_,_) :- fail. % (default)
:- if(defined(has_ciaopp_cost)).
asub_to_props(resources,Goal,Abs,Info):-
    !,
    Abs=complexity(_Call_VarType, _Succ_Vatype, Mode, Measure, _Mutex,
                   _Solution_Det, Size, _Relation, Approx, Resources,
                   Time, _Domain),
    Goal=..[_|Args],
    size_exps(Args,Measure,0,Dic),
    SizeName = size,
    decide_complexity_output_list(Size,Out_Size),
    size_bounds(Mode,Out_Size,[Approx],Args,Measure,SizeName,Dic,Succ),
    decide_complexity_output_list(Time,Out_Time),
    resource_bound(Approx, Resources, Goal, Dic, Out_Time, Comp),
    Info=(Succ,Comp),
    !. % no backtracking
asub_to_props(An,Goal,Abs,Info):-
    is_single_complexity_analysis(An),
    !,
    Abs=complexity(_Call_VarType, _Succ_Vatype, Mode, Measure, _Mutex,
                   _Solution_Det, Size, _Relation, Time, _Domain), 
    Goal=..[_|Args],
    size_exps(Args,Measure,0,Dic),
    size_name(An,SizeName),
    decide_complexity_output_list(Size,Out_Size),
    size_bounds(Mode,Out_Size,[],Args,Measure,SizeName,Dic,Succ),
    decide_complexity_output_list(Time,Out_Time),
    comp_to_props(An,Goal,Dic,Out_Time, Comp),
    Info=(Succ,Comp),
    !. % no backtracking
:- endif.
asub_to_props(nfg,_Goal,nf(_Call,_Succ,Fail,Cover),Info):- !,
    Info=[Fail,Cover].
asub_to_props(detg,_Goal,nf(_Call,_Succ,Det,Mut),Info):- !,
    Info=[Det,Mut].
asub_to_props(nf,_Goal,nf(_,_,nf(_,_,Cover,Fail)),[Fail,Cover]):-!.
asub_to_props(det,_Goal,det(_,_,det(_,Mut,Det)),[Det,Mut]).

:- if(defined(has_ciaopp_cost)).
comp_to_props(An,Goal,Dic,Time,[Comp_Time]):-
    is_time_analysis(An),
    !, 
    comp_bound(An,Goal,Dic,Time,Comp_Time).
comp_to_props(An,_Goal,_Dic,_Time,[]):-
    is_size_analysis(An).

size_exps([A|Args],[M|Measure],N0,[N=SizeMeasure|Dic]):-
    N is N0+1,
    SizeMeasure=..[M,A],
    size_exps(Args,Measure,N,Dic).
size_exps([],_,_,[]).

size_bounds([-|Mode],[S|Size],FixedArgs,[A|Args],[M|Measures],SizeName,Dic,
            [SizeExp|Bounds]):-
    key_rename_another_term(S,Dic,Exp),
    append(FixedArgs,[M,A,Exp],SizeExpArgs),
    SizeExp=..[SizeName|SizeExpArgs],
    size_bounds(Mode,Size,FixedArgs,Args,Measures,SizeName,Dic,Bounds).
size_bounds([+|Mode],[_|Size],FixedArgs,[_|Args],[_|Measures],SizeName,Dic,
            Bounds):-
    size_bounds(Mode,Size,FixedArgs,Args,Measures,SizeName,Dic,Bounds).
size_bounds([],[],_FixedArgs,[],[],_,_Dic,[]).

comp_bound(ExpName,_Goal,Dic,Exp0,Comp):-
    ( Exp0 = [Exp] -> true ; Exp = Exp0 ),
    key_rename_another_term(Exp,Dic,Comp_Exp),
    Comp=..[ExpName,Comp_Exp].

resource_bound(Approx, Resources, _Goal, Dic, Exp0, Comp):-
    resource_vector_to_prop(Resources, Exp0, Approx, Exp),
    key_rename_another_term(Exp, Dic, Comp).

resource_vector_to_prop([], [], _, []).
resource_vector_to_prop([Resource|Resources], [Exp|Exps], Approx,
        [cost(Approx, Resource, Exp)|Props]) :-
    resource_vector_to_prop(Resources, Exps, Approx, Props).

size_name(steps_lb, size_lb).
size_name(steps_ub, size_ub).
size_name(steps_o, size_o).
size_name(size_o, size_o).
size_name(size_lb, size_lb).
size_name(size_ub, size_ub).

% This one is (almost) exactly that of aeq_aux.pl
key_rename_another_term('$'(0,X),Dic,Term):- !,
    key_lookup(X,Dic,Term,_).
key_rename_another_term([],_,[]):- !.
key_rename_another_term([X|Xs],Dic,[Name|Names]):- !,
    key_rename_another_term(X,Dic,Name),          
    key_rename_another_term(Xs,Dic,Names).
key_rename_another_term(X,Dic,Term):-
    X=..[F|Args],
    key_rename_another_term(Args,Dic,Names),
    Term=..[F|Names].

decide_complexity_output_list([F|R], [OF|OR]):-
      decide_complexity_output(F, OF),
      decide_complexity_output_list(R, OR).
decide_complexity_output_list([], []).

decide_complexity_output(F, o(OF)):-
   current_pp_flag(complexity_output, big_o),
   !,
   order_of_function(F, OF).
decide_complexity_output(F, F):-   
   current_pp_flag(complexity_output, funct).
:- endif.

%-------------------------------------------------------------------------

% abs_execute_with_info(steps_ub,Info,Prop,Sense):- !,
%       check_cost_info(Prop,Info,Sense).
% abs_execute_with_info(steps_lb,Info,Prop,Sense):- !,
%       check_cost_info(Prop,Info,Sense).
%abs_execute_with_info(steps_o,Info,Prop,Sense):- !,
%       check_cost_info(Prop,Info,Sense).
% abs_execute_with_info(resources,Info,Prop,Sense):- !, %original
%       check_resource_info(Prop,Info,Sense).
%[LD]
%with interval
:- doc(abs_execute_with_info/4, "Check the correctness of assertion
cost function @var{Prop} which states the @var{Measure} (upper/lower 
bound, resources, e.t.c.).
Correctness is concluded by comparing it to the program static analysis 
result @var{Info}. The result is @var{Sense}. When ctcheck_intervals flag
is active, The comparison is carried out using polynom comparison module
that will give the intervals on which the assertion cost function is true,
false, or check. These intervals is pass to other module through 
@var{polynom_message/7}.").
:- pred abs_execute_with_info(Measure,Info,Prop,Sense)# "@var{Prop} is a
cost expression e.g. steps_ub(Arithmetic Expr) and @var{Info} is list
of cost expression".
:- if(defined(has_ciaopp_cost)).
abs_execute_with_info(steps_ub,Info,Prop,Sense):-
    current_pp_flag( ctchecks_intervals , on ),!,
    check_cost_info_byvalue(Prop,Info,Sense),
    check_cost_interval(Prop,Info,IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse),%LD
    build_message(IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse,Prop,Info).%LD
abs_execute_with_info(steps_lb,Info,Prop,Sense):-       
    current_pp_flag( ctchecks_intervals , on ),!,
    check_cost_info_byvalue(Prop,Info,Sense),
    check_cost_interval(Prop,Info,IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse),%LD
    build_message(IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse,Prop,Info).%LD
abs_execute_with_info(res_plai,Info,Prop,Sense):- !,   
    current_pp_flag( ctchecks_intervals , on ),!,
    check_resource_info_byvalue(Prop,Info,Sense),
    check_res_plai_interval(Prop,Info,IntervalsTrueLB,SafeIntervalsTrueLB,IntervalsFalseLB,SafeIntervalsFalseLB,IntervalsTrueUB,SafeIntervalsTrueUB,IntervalsFalseUB,SafeIntervalsFalseUB),
    build_message(lb,IntervalsTrueLB,SafeIntervalsTrueLB,IntervalsFalseLB,SafeIntervalsFalseLB,Prop,Info),
    build_message(ub,IntervalsTrueUB,SafeIntervalsTrueUB,IntervalsFalseUB,SafeIntervalsFalseUB,Prop,Info).
abs_execute_with_info(resources,Info,Prop,Sense):- !,   
    current_pp_flag( ctchecks_intervals , on ),!,
    check_resource_info_byvalue(Prop,Info,Sense),
    check_resource_interval(Prop,Info,IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse),
    build_message(IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse,Prop,Info).
%without interval 
abs_execute_with_info(steps_ub,Info,Prop,Sense):- !,
    current_pp_flag( ctchecks_intervals , off ), %LD
    check_cost_info(Prop,Info,Sense).
abs_execute_with_info(steps_lb,Info,Prop,Sense):- !,    
    current_pp_flag( ctchecks_intervals , off ),%LD
    check_cost_info(Prop,Info,Sense).
abs_execute_with_info(steps_o,Info,Prop,Sense):- !,
    check_cost_info(Prop,Info,Sense).
abs_execute_with_info(res_plai,Info,Prop,Sense):- !,   
    current_pp_flag( ctchecks_intervals , off ),!,
    check_resource_info(Prop,Info,Sense).
abs_execute_with_info(resources,Info,Prop,Sense):- !,   
    current_pp_flag( ctchecks_intervals , off ),!,
    check_resource_info(Prop,Info,Sense).
%[/LD]
abs_execute_with_info(size_ub,Info,Prop,Sense):- !,
    check_size_info(Prop,Info,Sense).
abs_execute_with_info(size_lb,Info,Prop,Sense):- !,
    check_size_info(Prop,Info,Sense).
abs_execute_with_info(size_o,Info,Prop,Sense):- !,
    check_size_info(Prop,Info,Sense).
:- endif.
%
abs_execute_with_info(nfg,Info,Prop,Sense):- !,
    check_nf_info(Prop,Info,Sense).
abs_execute_with_info(nf,Info,Prop,Sense):- !,
    check_nf_info(Prop,Info,Sense).
abs_execute_with_info(detg,Info,Prop,Sense):- !,
    check_det_info(Prop,Info,Sense).
abs_execute_with_info(det,Info,Prop,Sense):- !,
    check_det_info(Prop,Info,Sense).
%
abs_execute_with_info(Dom,Info,'basic_props:compat'(X,_Prop),true):-
    abs_execute_with_info(Dom,Info,var(X),true),!.
abs_execute_with_info(Dom,Info,'basic_props:compat'(X,Prop),Sense):-!,
    Prop =.. [F|Args],
    NewProp =.. [F,X|Args], % TODO: use prop_apply? (JF)
    abs_execute_with_info(Dom,Info,NewProp,Sense0),
    ( Sense0 = NewProp -> 
      Sense = 'basic_props:compat'(X,Prop)
    ; Sense = Sense0
    ).
%% PP: Handle parametric types in assertions (don't know if 
%% this is the best point to plug it...)
abs_execute_with_info(Dom,Info,Prop,Sense):-
    ( knows_of(regtypes, Dom) -> true ; fail ), % leaves choicepoints
    functor(Prop,F,2),
    ( statically_comp(Dom,F/2,Sense,Cond) ->
        make_prop_type_unary(Prop,UProp),
        functor(UProp,UF,1),
        convert_cond(Cond,UF,NewCond),
        cond(NewCond,Dom,UProp,Info)
    ; Sense = Prop
    ),
    !.
abs_execute_with_info(AbsInt,Info,Prop,Sense):-
    functor(Prop,F,A),
    statically_comp(AbsInt,F/A,Sense,Condition),
    cond(Condition,AbsInt,Prop,Info), !.
abs_execute_with_info(_AbsInt,_Info,Prop,Prop).

% IG: this code was duplicating information of the abstract execution table
% (static_abs_exec_table.pl), also it was wrong because it was being called
% without transforming the properties into native form.

%% statically_comp(AbsInt,ground/1,true,ground(1)):-
%%     determinable(AbsInt,ground).
%% statically_comp(AbsInt,ground/1,fail,not_ground(1)):-
%%     determinable(AbsInt,free).
%% statically_comp(AbsInt,var/1,true,free(1)):-
%%     determinable(AbsInt,free).
%% statically_comp(AbsInt,indep/2,true,indep(1,2)):-
%%     determinable(AbsInt,indep).
%% statically_comp(AbsInt,indep/2,fail,not_indep(1,2)):-
%%     determinable(AbsInt,not_indep).
%% statically_comp(AbsInt,F/1,Sense,Condition):-
%%     determinable(AbsInt,free),
%%     functor(FAtom,F,1),
%%     prop_to_native(FAtom,regtype(_)),
%%     \+ (equivalent_to_top_type(F)),
%%     Sense = fail,
%%     Condition = free(1).
statically_comp(AbsInt,F/A,Sense,Condition):-
    abs_exec(AbsInt,F/A,Sense,Condition).

% ------------------------------------------------------------------------

:- if(defined(has_ciaopp_cost)).
check_cost_info(C,Cost,Status):-
    cost_incompatible(C,Cost), !,
    Status=false.
check_cost_info(C,Cost,Status):-
    cost_included(C,Cost), !,
    Status=true.
check_cost_info(_C,_Cost,check).
:- endif.

:- if(defined(has_ciaopp_cost)).
% Added by EMM
check_resource_info(C,Cost,Status):-
    resource_incompatible(C,Cost), !,
    Status=false.
check_resource_info(C,Cost,Status):-
    resource_included(C,Cost), !,
    Status=true.
check_resource_info(_C,_Cost,check).
% End Added by EMM
:- endif.

:- if(defined(has_ciaopp_cost)).
check_size_info(C,Cost,Status):-
    size_incompatible(C,Cost), !,
    Status=false.
check_size_info(C,Cost,Status):-
    size_included(C,Cost), !,
    Status=true.
check_size_info(_C,_Cost,check).
:- endif.

check_nf_info(C,Nf,Status):-
    nf_incompatible(C,Nf), !,
    Status=false.
check_nf_info(C,Nf,Status):-
    nf_included(C,Nf), !,
    Status=true.
check_nf_info(_C,_Nf,check).

check_det_info(C,Det,Status):-
    det_incompatible(C,Det), !,
    Status=false.
check_det_info(C,Det,Status):-
    det_included(C,Det), !,
    Status=true.
check_det_info(_C,_Det,check).

:- if(defined(has_ciaopp_cost)).
cost_incompatible(steps_lb(C),Cost):-
    member(steps_ub(A),Cost),
    infer_dom:exp_greater_than(C,A).
cost_incompatible(steps_ub(C),Cost):-
    member(steps_lb(A),Cost),
    infer_dom:exp_greater_than(A,C).
cost_incompatible(steps_o(C),Cost):-
    member(steps_lb(A),Cost),
    order_of_function_greater_than_function(A, C).
cost_incompatible(steps_o(C),Cost):-
    member(steps_o(A),Cost),
    infer_dom:exp_greater_than(A,C).
cost_incompatible(steps(C),Cost):-
    member(steps_ub(A),Cost),
    infer_dom:exp_greater_than(C,A).
cost_incompatible(steps(C),Cost):-
    member(steps_lb(A),Cost),
    infer_dom:exp_greater_than(A,C).
cost_incompatible(steps(C),Cost):-
    member(steps_o(A),Cost),
    order_of_function_greater_than_function(C, A).
cost_incompatible(terminates,Cost):-
    member(steps_lb(A),Cost),
    A == inf.

cost_included(steps_lb(C),Cost):-
    member(steps_lb(A),Cost),
    infer_dom:exp_greater_eq_than(A,C).
cost_included(steps_ub(C),Cost):-
    member(steps_ub(A),Cost),
    infer_dom:exp_greater_eq_than(C,A).
cost_included(steps_o(C),Cost):-
    member(steps_ub(A),Cost),
    function_greater_eq_than_order_of_function(C, A).
cost_included(steps(C),Cost):-
    member(steps_ub(U),Cost),
    infer_dom:exp_eq_than(C,U),
    member(steps_lb(L),Cost),
    infer_dom:exp_eq_than(C,L).
cost_included(terminates,Cost):-
    member(steps_ub(A),Cost),
    A \== inf.

%%% Added by JNL

% Currently only absolute (abs) cost properties of type (call) can be
% inferred statically:

resource_incompatible(cost(abs,lb,call,Res,C),Cost) :-
    member(cost(ub,Res,A),Cost),
    infer_dom:exp_greater_than(C,A).
resource_incompatible(cost(abs,ub,call,Res,C),Cost) :-
    member(cost(lb,Res,A),Cost),
    infer_dom:exp_greater_than(A,C).

resource_included(cost(abs,lb,call,Res,C),Cost):-
    member(cost(lb,Res,A),Cost),
    infer_dom:exp_greater_eq_than(A,C).
resource_included(cost(abs,ub,call,Res,C),Cost):-
    member(cost(ub,Res,A),Cost),
    infer_dom:exp_greater_eq_than(C,A).

size_incompatible(size_lb(V,C),Cost):-
    find_property_value(size_ub,V,Cost,A),
    infer_dom:exp_greater_than(C,A).
size_incompatible(size_ub(V,C),Cost):-
    find_property_value(size_lb,V,Cost,A),
    infer_dom:exp_greater_than(A,C).
size_incompatible(size_o(V,C),Cost):-
    find_property_value(size_lb,V,Cost,A),
    order_of_function_greater_than_function(A, C).
size_incompatible(size_o(V,C),Cost):-
    find_property_value(size_o,V,Cost,A),
    infer_dom:exp_greater_than(A,C).
size_incompatible(size(V,C),Cost):-
    find_property_value(size_ub,V,Cost,A),
    infer_dom:exp_greater_than(C,A).
size_incompatible(size(V,C),Cost):-
    find_property_value(size_lb,V,Cost,A),
    infer_dom:exp_greater_than(A,C).
size_incompatible(size(V,C),Cost):-
    find_property_value(size_o,V,Cost,A),
    order_of_function_greater_than_function(C, A).

size_included(size_lb(V,C),Cost):-
    find_property_value(size_lb,V,Cost,A),
    infer_dom:exp_greater_eq_than(A,C).
size_included(size_ub(V,C),Cost):-
    find_property_value(size_ub,V,Cost,A),
    infer_dom:exp_greater_eq_than(C,A).
size_included(size_o(V,C),Cost):-
    find_property_value(size_ub,V,Cost,A),
    function_greater_eq_than_order_of_function(C, A).
size_included(size(V,C),Cost):-
     find_property_value(size_ub,V,Cost,U),
     infer_dom:exp_eq_than(C,U),
     find_property_value(size_lb,V,Cost,L),
     infer_dom:exp_eq_than(C,L).

%---- byvalue --------
% Here are several predicates to support expression comparison
% by comparing the evaluation result of the expressions on certain value
% These predicates are only used when interval-based comparison does not
% encounter any interval
% value 1 can be change to arbitrary 
% positive integer, but actually bigger
% number is more sensible to 
% simulate infinity

check_cost_info_byvalue(C,Cost,Status):-
    cost_incompatible_byvalue(C,Cost), !,
    Status=false.
check_cost_info_byvalue(C,Cost,Status):-
    cost_included_byvalue(C,Cost), !,
    Status=true.
check_cost_info_byvalue(_C,_Cost,check).


check_resource_info_byvalue(C,Cost,Status):-
    resource_incompatible_byvalue(C,Cost), !,
    Status=false.
check_resource_info_byvalue(C,Cost,Status):-
    resource_included_byvalue(C,Cost), !,
    Status=true.
check_resource_info_byvalue(_C,_Cost,check).

cost_incompatible_byvalue(steps_lb(C),Cost):-
    member(steps_ub(A),Cost),
    infer_dom:exp_greater_than_byvalue(C,A,1).
cost_incompatible_byvalue(steps_ub(C),Cost):-
    member(steps_lb(A),Cost),
    infer_dom:exp_greater_than_byvalue(A,C,1).

cost_included_byvalue(steps_lb(C),Cost):-
    member(steps_lb(A),Cost),
    infer_dom:exp_greater_eq_than_byvalue(A,C,1).
cost_included_byvalue(steps_ub(C),Cost):-
    member(steps_ub(A),Cost),
    infer_dom:exp_greater_eq_than_byvalue(C,A,1).

resource_incompatible_byvalue(cost(abs,lb,call,Res,C),Cost) :-
    member(cost(ub,Res,A),Cost),
    infer_dom:exp_greater_than_byvalue(C,A,1).
resource_incompatible_byvalue(cost(abs,ub,call,Res,C),Cost) :-
    member(cost(lb,Res,A),Cost),
    infer_dom:exp_greater_than_byvalue(A,C,1).

resource_included_byvalue(cost(abs,lb,call,Res,C),Cost):-
    member(cost(lb,Res,A),Cost),
    infer_dom:exp_greater_eq_than_byvalue(A,C,1).
resource_included_byvalue(cost(abs,ub,call,Res,C),Cost):-
    member(cost(ub,Res,A),Cost),
    infer_dom:exp_greater_eq_than_byvalue(C,A,1).
:- endif.

:- if(defined(has_ciaopp_cost)).
%------------------------------------------------------------------------------
% exp_value_greater_than_byvalue(A, C, X)
% A > C on point X
%------------------------------------------------------------------------------
exp_greater_than_byvalue(A, C, X):-
    copy_term(dummy_func(C,A),dummy_func(C1,A1)), 
    marshall_args_p(f(C1,A1),0,f(CP,AP)),
    remove_size_measures(CP,SC),
    remove_size_measures(AP,SA),
    CostDiff = SA - SC,
    eval_arith(CostDiff, X, Res),
    Res > 0.

%------------------------------------------------------------------------------
% exp_value_greater_than_byvalue(A, C, X)
% A >= C on point X
%------------------------------------------------------------------------------
exp_greater_eq_than_byvalue(A, C, X):-
    copy_term(dummy_func(C,A),dummy_func(C1,A1)), 
    marshall_args_p(f(C1,A1),0,f(CP,AP)),
    remove_size_measures(CP,SC),
    remove_size_measures(AP,SA),
    CostDiff = SA - SC,
    eval_arith(CostDiff, X, Res),
    Res >= 0.

%/---- byvalue --------
find_property_value(PropName, Var, [Prop|_], Value):-
    Prop =.. [PropName,_M,A,V], % TODO: use prop_unapply? (JF)
    A == Var,
    !,
    Value = V.
find_property_value(PropName, Var, [_Prop|R], Value):-
   find_property_value(PropName, Var, R, Value).

exp_eq_than(C,A):-
    \+ \+ ( marshall_args(f(C,A),0),
            remove_size_measures(C,SC),
            remove_size_measures(A,SA),
            algebraic:exp_eq_than(SC,SA)
          ).

exp_greater_eq_than(C,A):-
    order_of_function_greater_than_function(C, A), !. % ?? -PLG
exp_greater_eq_than(C,A):- 
    \+ \+ ( marshall_args(f(C,A),0),
            remove_size_measures(C,SC),
            remove_size_measures(A,SA),
            algebraic:exp_greater_eq_than(SC,SA)
          ).

:- export(exp_greater_than/2).
exp_greater_than(C,A):-
    order_of_function_greater_than_function(C, A), !. % -PLG
exp_greater_than(C,A):-
    \+ \+ ( marshall_args(f(C,A),0),
            remove_size_measures(C,SC),
            remove_size_measures(A,SA),
            algebraic:exp_greater_than(SC,SA)
          ).

size_variable(length(_)).
size_variable(size(_)).
size_variable(depth(_)).
size_variable(int(_)).
size_variable(nnegint(_)).


order_of_function_greater_than_function(OA, C):- 
    \+ \+ ( marshall_args(f(C,OA),0),
            remove_size_measures(C,SC),
            remove_size_measures(OA,SOA),
            order_of_function(SOA, NA),
            % algebraic:exp_greater_than(NA,SC)
            algebraic:complexity_order_greater_than(NA,SC)
          ).

function_greater_eq_than_order_of_function(C, OA):- 
    \+ \+ ( marshall_args(f(C,OA),0),
            remove_size_measures(C,SC),
            remove_size_measures(OA,SOA),
            order_of_function(SOA, NA),
            % algebraic:exp_greater_eq_than(SC,NA)
            algebraic:complexity_order_greater_eq_than(SC,NA)
          ).

remove_size_measures(C,C):-
   var(C),
   !.
remove_size_measures(C,C):-
   C = $(_), 
   !.
remove_size_measures(C,SC):-
   size_variable(C),
   !,
   C =.. [_F,A],
   SC = A.
remove_size_measures(C,SC):-
   functor(C, F, A),
   A > 1,
   !,
   functor(SC, F, A),
   compound_remove_size_measures(A,C,SC).
remove_size_measures(C,C).

compound_remove_size_measures(0,_,_):-
   !.
compound_remove_size_measures(A,C,SC):-
   A > 0,
   arg(A, C, CArg),
   remove_size_measures(CArg,SCArg),
   arg(A, SC, SCArg),
   A1 is A - 1,
   compound_remove_size_measures(A1,C,SC).
:- endif.

:- if(defined(has_ciaopp_cost)).
marshall_args(Term,N):-
    varset(Term,Vars),
    marshall_args_(Vars,N).

marshall_args_([],_).
marshall_args_([$(N1)|Args],N):-
    N1 is N+1,
    marshall_args_(Args,N1).
:- endif.

nf_incompatible(fails,Nf):-
    member(not_fails,Nf).
nf_incompatible(not_fails,Nf):-
    member(fails,Nf).
nf_incompatible(covered,Nf):-
    member(not_covered,Nf).
nf_incompatible(not_covered,Nf):-
    member(covered,Nf).

nf_included(fails,Nf):-
    member(fails,Nf).
nf_included(not_fails,Nf):-
    member(not_fails,Nf).
nf_included(covered,Nf):-
    member(covered,Nf).
nf_included(not_covered,Nf):-
    member(not_covered,Nf).
nf_included(possibly_fails,_Nf).
nf_included(possibly_not_covered,_Nf).

det_incompatible(non_det,Det):-
    member(is_det,Det).
det_incompatible(mut_exclusive,Det):-
    member(not_mut_exclusive,Det).
det_incompatible(not_mut_exclusive,Det):-
    member(mut_exclusive,Det).

det_included(is_det,Det):-
    member(is_det,Det).
det_included(mut_exclusive,Det):-
    member(mut_exclusive,Det).
det_included(possibly_nondet,_Det).

% ------------------------------------------------------------------------

convert_cond(type_incl(N,_),NU,type_incl(N,NU)).
convert_cond(incomp_type(N,_),NU,incomp_type(N,NU)).

% ------------------------------------------------------------------------

non_collapsable(nf).
non_collapsable(det).
non_collapsable(path).
non_collapsable(res_plai).
non_collapsable(sized_types).
non_collapsable(res_plai_stprf).

% TODO: Add more.
does_not_use_memo_lub(nfg).
does_not_use_memo_lub(detg).
does_not_use_memo_lub(resources).

knows_of(regtypes,Dom):- determinable(Dom,types).
knows_of(X,nf):- nf_info(X).
knows_of(X,nf):- knows_of(X,eterms). % PLG
knows_of(X,nf):- knows_of(X,shfr).   % PLG
knows_of(X,nfg):- nf_info(X).
% knows_of(X,nfg):- knows_of(X,eterms). % EMM
% knows_of(X,nfg):- knows_of(X,shfr).   % EMM
knows_of(X,det):- det_info(X).
% knows_of(X,det):- knows_of(X,eterms). % PLG
% knows_of(X,det):- knows_of(X,shfr).   % PLG
knows_of(X,detg):- det_info(X).
knows_of(X,detg):- knows_of(X,eterms).
knows_of(X,detg):- knows_of(X,shfr).
knows_of(X,res_plai) :- knows_of(X,etermsvar).
knows_of(X,res_plai_stprf) :- knows_of(X,etermsvar).
knows_of(X,sized_types) :- knows_of(X,etermsvar).
knows_of(X,sized_types) :- sized_types_info(X).
knows_of(X,res_plai) :- knows_of(X,nf).
knows_of(X,res_plai) :- knows_of(X,det).
knows_of(X,res_plai) :- res_plai_info(X).
knows_of(X,res_plai_stprf) :- knows_of(X,nf).
knows_of(X,res_plai_stprf) :- knows_of(X,det).
knows_of(X,res_plai_stprf) :- res_plai_info(X).
knows_of(X,steps_ub):- cost_info(X).
knows_of(X,steps_lb):- cost_info(X). 
knows_of(X,steps_ualb):- cost_info(X).
knows_of(X,steps_o):- cost_info(X).
knows_of(X,resources):- resource_info(X).    % JNL
knows_of(X,size_ub):- size_info(X).
knows_of(X,size_lb):- size_info(X).
knows_of(X,size_ualb):- size_info(X).
knows_of(X,size_o):- size_info(X).
knows_of(X,Dom):- determinable(Dom,X).
     
nf_info(fails).
nf_info(not_fails).
nf_info(possibly_fails).
nf_info(covered).
nf_info(not_covered).

det_info(is_det).
det_info(possibly_nondet).
det_info(non_det).
det_info(mut_exclusive).
det_info(not_mut_exclusive).

 %% cost_info(size_lb(_)).
 %% cost_info(size_ub(_)).
 %% cost_info(size(_)).
cost_info(terminates).
cost_info(steps_lb(_)).
cost_info(steps_ub(_)).
cost_info(steps_o(_)).
cost_info(steps(_)).

resource_info(cost(_,_,_,_,_)).     % JNL, EMM
resource_info(cost(_,_,_,_,_,_,_)). % EMM

size_info(size_lb(_,_)).
size_info(size_ub(_,_)).
size_info(size_o(_,_)).
size_info(size(_,_)).

sized_types_info(F) :- functor(F,rsize,_).
res_plai_info(F) :- functor(F,rsize,_).
res_plai_info(F) :- functor(F,cardinality,_).
res_plai_info(F) :- functor(F,costb,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%          Below this line is interval information routine [LD]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

obtain_bound(cost(abs, B, call, Res, Alb),B,Res,Alb).
%obtain_bound(cost(abs, , call, Res, Alb),ub,Res,Alb).
obtain_bound(costb(Res,_,Alb),ub,Res,Alb).
obtain_bound(costb(Res,Alb,_),lb,Res,Alb).

:- if(defined(has_ciaopp_cost)).
% Please read this explanation: 
%  1. A denotes Assertion
%     C denotes Cost_analysis
%  2. lb case: Alb =< Clb TRUE
%              Alb >  Cub FALSE

%     ub case: Aub >= Cub TRUE
%              Aub <  Clb FALSE
%     
%     otherwise CHECK
% We write the program a bit inefficiently to improve legibility :(
:- doc(doinclude, [check_resource_interval/6, check_cost_interval/6]).
%------------------------------------------------------------------------------
% check_resource_interval
:- doc(check_resource_interval/6, "analogous to check_cost_interval/6").
%------------------------------------------------------------------------------
% cost analysis for ub and lb are available
% assertion lb case
check_resource_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = cost(abs, lb, call, Res, Alb), % specification
  member(cost(lb, Res, Clb), Info),     % analysis
  member(cost(ub, Res, Cub), Info),     % analysis
  % Alb =< Clb, + TRUE -check
  expression_equal_greater_than(Clb, Alb, IntervalsTrue, SafeIntervalsTrue), 
  % Alb > Cub,  + False -check
  expression_greater_than(Alb, Cub, IntervalsFalse, SafeIntervalsFalse),!. 

% assertion ub case
check_resource_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = cost(abs, ub, call, Res, Aub), % specification
  %Info = [(_,CostInfo)],
  member(cost(ub, Res, Cub),Info),     % analysis
  member(cost(lb, Res, Clb),Info),     % analysis
  % Aub >= Cub, + TRUE -check
  expression_equal_greater_than(Aub, Cub, IntervalsTrue, SafeIntervalsTrue), 
  % Aub < Clb,  + False -check
  expression_greater_than(Clb, Aub, IntervalsFalse, SafeIntervalsFalse),!. 

% ONLY cost analysis for ub is available
% assertion lb case
check_resource_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
 %obtain_bound(Prop,lb,Res,Alb),
 Prop = cost(abs, lb, call, Res, Alb), % specification
  IntervalsTrue=[],SafeIntervalsTrue=[],
  member(cost(ub, Res, Cub), Info),     % analysis
  % Alb > Cub,  + False -check
  expression_greater_than(Alb, Cub, IntervalsFalse, SafeIntervalsFalse),!. 

% assertion ub case
check_resource_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
 %obtain_bound(Prop,ub,Res,Aub), 
 Prop = cost(abs, ub, call, Res, Aub), % specification
  member(cost(ub, Res, Cub), Info),     % analysis
  % Aub >= Cub, + TRUE -check
  expression_equal_greater_than(Aub, Cub, IntervalsTrue, SafeIntervalsTrue),
  IntervalsFalse=[],SafeIntervalsFalse=[],!.

% ONLY cost analysis for lb is available
% assertion lb case
check_resource_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
 %obtain_bound(Prop,lb,Res,Alb), 
 Prop = cost(abs, lb, call, Res, Alb), % specification
  member(cost(lb, Res, Clb), Info),     % analysis
  % Alb =< Clb, + TRUE -check
  expression_equal_greater_than(Clb, Alb, IntervalsTrue, SafeIntervalsTrue), 
  IntervalsFalse=[],SafeIntervalsFalse=[],!.

% assertion ub case
check_resource_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
 %obtain_bound(Prop,ub,Res,Aub), 
 Prop = cost(abs, ub, call, Res, Aub), % specification
  IntervalsTrue=[],SafeIntervalsTrue=[],
  member(cost(lb, Res, Clb), Info),     % analysis
  % Aub < Clb,  + False -check
  expression_greater_than(Clb, Aub, IntervalsFalse, SafeIntervalsFalse),!. 

check_resource_interval(_,_,[],[],[],[]).

%%%%%%Check intervals for res_plai
%This predicate is analogous to check_resource_interval, but
%needs to return intervals for both upper and lower bounds, at the
%same time.

check_res_plai_interval(Prop, Info, IntervalsTrueLB,
  SafeIntervalsTrueLB, IntervalsFalseLB, SafeIntervalsFalseLB, IntervalsTrueUB,
  SafeIntervalsTrueUB, IntervalsFalseUB, SafeIntervalsFalseUB):- 
  obtain_bound(Prop,lb,Res,Alb),
  obtain_bound(Prop,ub,Res,Aub),
  %Prop = cost(abs, lb, call, Res, Alb), % specification
  member(cost(lb, Res, Clb), Info),     % analysis
  member(cost(ub, Res, Cub), Info),     % analysis
  % Alb =< Clb, + TRUE -check
  expression_equal_greater_than(Clb, Alb, IntervalsTrueLB, SafeIntervalsTrueLBV),
  verify_include(Clb, Alb, SafeIntervalsTrueLBV, SafeIntervalsTrueLB),
  % Alb > Cub,  + False -check
  expression_greater_than(Alb, Cub, IntervalsFalseLB, SafeIntervalsFalseLBV),!,
  verify_incompatible(Alb, Cub, SafeIntervalsFalseLBV, SafeIntervalsFalseLB),
  % Aub >= Cub, + TRUE -check
  expression_equal_greater_than(Aub, Cub, IntervalsTrueUB, SafeIntervalsTrueUBV),
  verify_include(Aub, Cub, SafeIntervalsTrueUBV, SafeIntervalsTrueUB),
  % Aub < Clb,  + False -check
  expression_greater_than(Clb, Aub, IntervalsFalseUB, SafeIntervalsFalseUBV),!,
  verify_incompatible(Clb, Aub, SafeIntervalsFalseUBV, SafeIntervalsFalseUB).
  % intersect(IntervalsTrueLB,IntervalsTrueUB,IntervalsTrue),
  % intersect(SafeIntervalsTrueLB,SafeIntervalsTrueUB,SafeIntervalsTrue),
  % intersect(IntervalsFalseLB,IntervalsFalseUB,IntervalsFalse),
  % intersect(SafeIntervalsFalseLB,SafeIntervalsFalseUB,SafeIntervalsFalse).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%------------------------------------------------------------------------------
% sign [] interval, w/ t/f.
%------------------------------------------------------------------------------
verify_include(_C, _A, [], [t]).
verify_include(_C, _A, Intervals, Intervals).

verify_incompatible(_C, _A, [], [f]).
verify_incompatible(_C, _A, Intervals, Intervals).
:- endif.

%------------------------------------------------------------------------------
:- if(defined(has_ciaopp_cost)).
% check_cost_interval
:- doc(check_cost_interval/6, "Compare assertion cost function with
analysis cost function. When there is intersection between them it gives intervals
on which a cost function is greater than the other one. The interval result
is kept in @var{IntervalsTrue},   @var{SafeIntervalsTrue}, @var{IntervalsFalse},
and @var{SafeIntervalsFalse}. However currently we do not use  @var{IntervalsTrue},
and @var{IntervalsFalse}
@begin{verbatim}
Please read this explanation: 
 1. A denotes Assertion
    C denotes Cost_analysis
 2. lb case: Alb =< Clb TRUE
         Alb >  Cub FALSE

    ub case: Aub >= Cub TRUE
         Aub <  Clb FALSE
    
    otherwise CHECK
@end{verbatim}
").
%------------------------------------------------------------------------------
% cost analysis for ub and lb are available
% assertion lb case
check_cost_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = steps_lb(Alb), % specification
  member(steps_lb(Clb), Info),     % analysis
  % Alb =< Clb, + TRUE -check
  expression_equal_greater_than(Clb, Alb, IntervalsTrue, SafeIntervalsTrue), 

  member(steps_ub(Cub), Info),     % analysis
  % Alb > Cub,  + False -check
  expression_greater_than(Alb, Cub, IntervalsFalse, SafeIntervalsFalse),!. 

% assertion ub case
check_cost_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = steps_ub(Aub), % specification
  member(steps_ub(Cub), Info),     % analysis
  % Aub >= Cub, + TRUE -check
  expression_equal_greater_than(Aub, Cub, IntervalsTrue, SafeIntervalsTrue), 

  member(steps_lb(Clb), Info),     % analysis
  % Aub < Clb,  + False -check
  expression_greater_than(Clb, Aub, IntervalsFalse, SafeIntervalsFalse),!. 

% ONLY cost analysis for ub is available
% assertion lb case
check_cost_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = steps_lb(Alb), % specification
  IntervalsTrue=[],SafeIntervalsTrue=[],

  member(steps_ub(Cub), Info),     % analysis
  % Alb > Cub,  + False -check
  expression_greater_than(Alb, Cub, IntervalsFalse, SafeIntervalsFalse),!. 

% assertion ub case
check_cost_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = steps_ub(Aub), % specification
  member(steps_ub(Cub), Info),     % analysis
  % Aub >= Cub, + TRUE -check
  expression_equal_greater_than(Aub, Cub, IntervalsTrue, SafeIntervalsTrue),
  IntervalsFalse=[],SafeIntervalsFalse=[],!.

% ONLY cost analysis for lb is available
% assertion lb case
check_cost_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = steps_lb(Alb), % specification
  member(steps_lb(Clb), Info),     % analysis
  % Alb =< Clb, + TRUE -check
  expression_equal_greater_than(Clb, Alb, IntervalsTrue, SafeIntervalsTrue), 
  IntervalsFalse=[],SafeIntervalsFalse=[],!.

% assertion ub case
check_cost_interval(Prop, Info, IntervalsTrue,
  SafeIntervalsTrue, IntervalsFalse, SafeIntervalsFalse):- 
  Prop = steps_ub(Aub), % specification
  IntervalsTrue=[],SafeIntervalsTrue=[],

  member(steps_lb(Clb), Info),     % analysis
  % Aub < Clb,  + False -check
  expression_greater_than(Clb, Aub, IntervalsFalse, SafeIntervalsFalse),!. 


% assertion steps_o will go here
% this is a tricky approach, because this code is not supposed to be reach
% for steps_o case. But since steps_o case calls steps_ub (don't know why),
% we want to capture it and said no intersection.
check_cost_interval(_,_,[],[],[],[]).
:- endif.

:- if(defined(has_ciaopp_cost)).
:- push_prolog_flag(multi_arity_warnings,off).
%------------------------------------------------------------------------------
% for passing information to ctchecks
%------------------------------------------------------------------------------
build_message(IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse,Prop,Info):-
    polynom_current_assertion(Assertion),
    asserta_fact(polynom_message(Assertion,Prop,Info,IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse)).

build_message(Bound,IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse,Prop,Info):-
    polynom_current_assertion(Assertion),
    Prop =..[H|L],
    PropB =..[H,Bound|L],
    asserta_fact(polynom_message(Assertion,PropB,Info,IntervalsTrue,SafeIntervalsTrue,IntervalsFalse,SafeIntervalsFalse)).

:- pop_prolog_flag(multi_arity_warnings).
%-----------------------------------------------------------------------
%[LD] interval routine
%Routine about valid interval information of complexity function 

% in polynom NormalForm, the order of polynom is sorted descending
% but we need to make it ascending, X^0+...+X^n according to GSL spec

cost_difference([],X,MinusX):-!, %handling global change in library that is already true
    minus_cost(X,MinusX).
cost_difference(X,[],X):-!.
cost_difference(A,B,C):-
    difference(A,B,C).

minus_cost([],[]).
minus_cost([X|Xs],[Y|Ys]) :-
    Y is -X,
    minus_cost(Xs,Ys).

normalize_zero([0.0],[0]):-!.
normalize_zero([0.0|Res],[0|NormalRes]):-
    normalize_zero(Res,NormalRes),!.

normalize_zero([A],[A]).
normalize_zero([X|Res],[X|NormalRes]):-
    normalize_zero(Res,NormalRes).

cost_validate_polynom([],[]):-!. %same reason with cost_difference
cost_validate_polynom(PDiff,PDiffValid):-
    normalize_zero(PDiff,PDiffNormal),%change 0.0 into 0
    validate_polynom(PDiffNormal,PDiffValid).


value_check_greater_than(E1, E2, X):-
    eval_arith(E1, X, V1),!,
    eval_arith(E2, X, V2),!,
    V1 > V2.
%------------------------------------------------------------------------------
% Core function for comparing two cost function
:- doc(doinclude, expression_equal_greater_than/4).
:- doc(expression_equal_greater_than/4, "Core function for comparing two cost function.
This predicate gives only positive intervals, if they exist.
Here is the value of @var{Interval} and @var{SafeInterval} when the algorithm
do not find intersection:
@begin{itemize}
@item Interval=[1] uncovered cost function
@item Interval=[2] unconvergence GSL algorithm
@item Interval=[3] small interval is encountered by safe root search algorithm
@item Interval=[4] unconvergence safe root search algorithm
@item Interval=[] no intersections between functions
@end{itemize}
Note: theres is opposite polynomial representation in this procedure.
 In polynom Normal Form, the order of polynom is sorted descending
 X^n+...+X^0, but we have to make it ascending, X^0+...+X^n 
according to GSL spec, to be solved using GSL.").
:- pred expression_equal_greater_than(F1,F2,Intervals,SafeIntervals)#"Looks for root of
equation @var{F1-F2=0} and gives intervals on which F1 greater/less than F2. 
@var{Intervals} is obtained from the GSL root finding or approximated function,
meanwhile @var{SafeIntervals} is the intervals on the safe side. Even though
@var{Intervals} is not used in current implementation, it might be useful
when computation for @var{SafeIntervals} cannot be performed, e.g. because it
encounters small interval. ".
%------------------------------------------------------------------------------
% This approach is using GSL
expression_equal_greater_than(A,C,Interval,SafeInterval):-
    current_pp_flag(ctchecks_value_evaluation, off),
    copy_term(dummy_func(C,A),dummy_func(C1,A1)), 
    marshall_args_p(f(C1,A1),0,f(CP,AP)),
    remove_size_measures(CP,SC),
    remove_size_measures(AP,SA),
    polynomize(SA,PA),%uncovered cost function will be failed here
    polynomize(SC,PC),%uncovered cost function will be failed here
    reverse(PA,RPA),
    reverse(PC,RPC),
    % in polynom NormalForm, the order of polynom is sorted descending
    % X^n+...+X^0, but we need to make it ascending, X^0+...+X^n 
    %according to GSL spec
    cost_difference(RPA,RPC,PDiff), %PDiff=RPA-RPC
    cost_validate_polynom(PDiff,PDiffValid),
    CostDiff = SA - SC,
    polynom_root_interval(CostDiff, PDiffValid,FullInterval),
%       format(user, "Use GSL. ",[]),
    (
        FullInterval == [] -> %no intersection found, mark whether A >= C
        (
            value_check_greater_than(SA, SC, 0) -> %proving A >= C
            Interval = [],
            SafeInterval = []
        ; % the comparison can't prove A >= C, mark as check interval
            Interval = [c],
            SafeInterval = [c]
        )
    ;
        FullInterval == [2] -> % unconvergence GSL algorithm
        Interval = [2], 
        SafeInterval = [2]
    ;
        cut_negative_roots(FullInterval, PositiveInterval),
        %we use the arithmetic expression for evaluating the safe root
        compute_safe_intervals(CostDiff, PositiveInterval, SafeIntMix, Error),
        %the safe root algorithm may encounter safe negative root
        cut_negative_roots(SafeIntMix, SafeInt),
        (
            Error = 0 ->
            (
                small_intervals(SafeInt) ->
                Interval = [3], 
                SafeInterval = [3]
            ;
                Interval = PositiveInterval, 
                SafeInterval = SafeInt
            )
        ;
            Error = 1 ->
            Interval = [4],
            SafeInterval = [4]
        )
    ), !.
%
%------------------------------------------------------------------------------
% This approach is using interval value enumeration
expression_equal_greater_than(A,C,Interval,SafeInterval):-
    %get user interval
    polynom_current_assertion(Assertion),
    Assertion= as${call => PreCond},
    exist_interval_pred(PreCond),
    remove_interval_precond(PreCond, _CleanPrecond, IntPred), 
    IntPred=[IntPrecond],
    arg(2, IntPrecond, ListUserInterval),
    % intervals(length(A),[i(2,4),i(10,21)])
    %extract_user_intervals(ListUserInterval, ListUserInterval2),
    copy_term(dummy_func(C,A),dummy_func(C1,A1)), 
    marshall_args_p(f(C1,A1),0,f(CP,AP)),
    remove_size_measures(CP,SC),
    remove_size_measures(AP,SA),
    CostDiff = SA - SC,
    %normalized CostDiff in a hope to get simpler for, so faster to evaluate
    %normalization postponed later
    %       
    brute_eval_intervals(CostDiff, ListUserInterval, Interval),
    SafeInterval = Interval,
%       format(user, "Do not use GSL. ", []),
    !.
%------------------------------------------------------------------------------
% This approach is using interval value enumeration event though the user 
% specified interval does not exist. Therefore we fix the interval to be
% evaluated is [0,10000].
expression_equal_greater_than(A,C,Interval,SafeInterval):-
    current_pp_flag(ctchecks_value_evaluation, on),
    % intervals(length(A),[i(2,4),i(10,21)])
    % fix the interval
    ListUserInterval = [i(0,10000)],
    copy_term(dummy_func(C,A),dummy_func(C1,A1)), 
    marshall_args_p(f(C1,A1),0,f(CP,AP)),
    remove_size_measures(CP,SC),
    remove_size_measures(AP,SA),
    CostDiff = SA - SC,
    %normalized CostDiff in a hope to get simpler for, so faster to evaluate
    %normalization postponed later
    %       
    brute_eval_intervals(CostDiff, ListUserInterval, Interval),
    SafeInterval = Interval,
%       format(user, "Do not use GSL. ", []),
    !.
%
expression_equal_greater_than(_,_,[1],[1]). %uncovered cost function


%------------------------------------------------------------------------------
:- pred expression_greater_than(A,C,Interval,SafeInterval)#"".
%------------------------------------------------------------------------------
expression_greater_than(A,C,Interval,SafeInterval):-
    expression_equal_greater_than(A,C,Interval,SafeInterval1),
    %checking error
    check_result_error(SafeInterval1, ErrVal),
    (
        ErrVal == 0 -> %no error occured
        copy_term(dummy_func(C,A),dummy_func(C1,A1)), 
        marshall_args_p(f(C1,A1),0,f(CP,AP)),
        remove_size_measures(CP,SC),
        remove_size_measures(AP,SA),
        CostDiff = SA - SC,
        create_strict_inequality(CostDiff, SafeInterval1, SafeInterval)
    ;
        %error occured, preserves the error code
        SafeInterval = SafeInterval1
    ).

%------------------------------------------------------------------------------
:- pred create_strict_inequality(Expr, SafeInterval1, SafeInterval)#" Create
a new interval where strict disequality holds. Roots in 
@var{SafeInterval1} are safe therefore the evaluation of it should be greater
or equal than 0. Thus we'll check disequality using root>0".
%------------------------------------------------------------------------------
%special case no intersection
create_strict_inequality(_, [], []).
create_strict_inequality(_, [c], [c]).
%base
create_strict_inequality(Expr, [Ival1,R,Ival2], [Ival1,NewR,Ival2]):-!,
    eval_arith(Expr, R, EvalRes),
    (
        EvalRes > 0 ->
        NewR = R
    ;
        (
            Ival1 > Ival2 ->
            NewR is R - 1 %move left
        ;
            NewR is R + 1 %move right
        )
    ).
%recc
create_strict_inequality(Expr, [Ival1,R,Ival2|Is], [Ival1,NewR|SafeInterval]):-
    eval_arith(Expr, R, EvalRes),
    (
        EvalRes > 0 ->
        NewR = R
    ;
        (
            Ival1 > Ival2 ->
            NewR is R - 1 %move left
        ;
            NewR is R + 1 %move right
        )
    ),
    create_strict_inequality(Expr,[Ival2|Is], SafeInterval).

%------------------------------------------------------------------------------
% cut the negative parts of a list of interval
%------------------------------------------------------------------------------
cut_negative_roots([], []).
cut_negative_roots([_], []).
cut_negative_roots([_,_], []).
cut_negative_roots([Ival|Is], CutIntervals):-
    Is=[Iroot|Iss],
    (Iroot < 0 ->
     cut_negative_roots(Iss, CutIntervals)
    ;
     CutIntervals= [Ival|Is]
    ).

:- doc(marshall_args_p/3, "It has side effect of changing the input argument").
%marshall_args_p(f(C1,A1),0,f(CP,AP)),
marshall_args_p(Term,N,TermRes):-
    TermRes=Term,
    varset(Term,Vars),
    varset(TermRes,Vars),
    marshall_args_(Vars,N).


% to check if there is any small interval
small_intervals([_,A,_V,A|_Rest]).
small_intervals([_,A,V,B|Rest]):-
    A \== B,
    small_intervals([V,B|Rest]).


%------------------------------------------------------------------------------
% 
%------------------------------------------------------------------------------
% extract_user_intervals([],[]).
% extract_user_intervals([i(A,B)|Ls],[[A,B]|Rs]):-
%       extract_user_intervals(Ls,Rs).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% remove_interval_precond takes the interval information from precondition
%------------------------------------------------------------------------------
remove_interval_precond([Term|Ps], NewPrecond, IntPrecond):-
    contains_interval(Term),
    append([Term], IP, IntPrecond),
    remove_interval_precond(Ps, NewPrecond, IP),!. 
%                                               
remove_interval_precond([Term|Ps], NewPrecond, IntPrecond):-
    append([Term], NP, NewPrecond),
    remove_interval_precond(Ps, NP, IntPrecond).
%
remove_interval_precond([], [], []).

%------------------------------------------------------------------------------
% the Term interval will only have this following possible form
%               resources_props:intervals(_,_,_,_)
%------------------------------------------------------------------------------
exist_interval_pred([Term|_]):- contains_interval(Term),!.
exist_interval_pred([_|Lst]) :- exist_interval_pred(Lst).

contains_interval(interval(_,_)).
contains_interval('resources_props:intervals'(_, _, _, _)).

%-----------------------------------------------------------------------------
% check_interval_error(List_of_Interval, ErrorCode).
% this is taken from ctchecks_pred_message.pl.
% fundamental code re-organization is mandatory
%-----------------------------------------------------------------------------
check_result_error([ ], 0).    %not error 
check_result_error([1], 1):-!. %error
check_result_error([2], 2):-!. %error
check_result_error([3], 3):-!. %error
check_result_error([4], 4):-!. %error
check_result_error(_, 0). %otherwise not error


%[\LD]
:- endif.
