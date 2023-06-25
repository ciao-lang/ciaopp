/*             Copyright (C)1990-2003 UPM-CLIP                          */

:- module(fixpo_ops_gfp,
    [ 
        top/1,
        singleton/2,
        each_abs_sort/3,
    %    each_concrete/4,
        each_project/6,
        each_extend/6,
        each_exit_to_prime/8,
        each_unknown_call/5,
        each_body_succ_builtin/12,
        body_succ_meta/7,
        applicable/3,
        each_apply_trusted/7,
        reduce_equivalent/3,
        dual_widen_succ/4,
        abs_superset_/3,
        each_identical_abstract/3,
        decide_memo/6,
        eliminate_tops_and_equivalents/3  % JNL
    ],
    [assertions, datafacts]).

:- doc(module,"This module contains operation common to different
    top-down fixpoint algorithms in PLAI, but for the computation
    of greatest fixpoints. The predicates not found here are the
    same that in fixpo_ops.").

:- use_module(ciaopp(plai/domains), [
    exit_to_prime/8,
    abs_sort/3,
    extend/6,
    eliminate_equivalent/3,
    compute_lub/3,
    compute_glb/3,
    dual_widen/4,
    unknown_call/5,
    project/6,
    body_succ_builtin/9,
    special_builtin/6,
    fixpoint_covered_gfp/3,
    abs_subset/3,
    identical_abstract/3]).
:- use_module(ciaopp(plai/apply_assertions_old), [apply_trusted/7, apply_trusted_each/7]).
:- use_module(ciaopp(plai/plai_db), [complete/7, memo_table/6]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(library(compiler/p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(library(sort), [sort/2]).  
:- use_module(library(terms_vars), [varset/2]).

% To go with 'bottom' in fixpo_ops
top([]).
top(['$top']).

%bottom([]).
%bottom(['$bottom']).

% Changed to top
singleton(Prime,[Prime]).
singleton('$top', []).

%singleton(Prime,[Prime]).
%singleton('$bottom',[]).

%-------------------------------------------------------------------------

applicable(ListPrime,_AbsInt,Prime):- singleton(Prime,ListPrime), !.
applicable(ListPrime,AbsInt,Prime):- compute_glb(AbsInt,ListPrime,Prime).

%applicable(ListPrime,_AbsInt,Prime):- singleton(Prime,ListPrime), !.
%applicable(ListPrime,AbsInt,Prime):- compute_lub(AbsInt,ListPrime,Prime).

reduce_equivalent([Prime],_AbsInt,LPrime):- !,
    singleton(Prime,LPrime).
reduce_equivalent(ListPrime0,AbsInt,ListPrime1):-
    eliminate_tops_and_equivalents(AbsInt,ListPrime0,ListPrime1).

%reduce_equivalent([Prime],_AbsInt,LPrime):- !,
%       singleton(Prime,LPrime).
%reduce_equivalent(ListPrime0,AbsInt,ListPrime1):-
%       eliminate_bottoms_and_equivalents(AbsInt,ListPrime0,ListPrime1).

%-------------------------------------------------------------------------

each_exit_to_prime([Exit],AbsInt,Sg,Hv,Head,Sv,ExtraInfo,LPrime):- !,
    exit_to_prime(AbsInt,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime),
    LPrime=[Prime].
each_exit_to_prime(LExit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,LPrime):-
    each_exit_to_prime0(LExit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,TmpLPrime),
    eliminate_tops_and_equivalents(AbsInt,TmpLPrime,LPrime).

each_exit_to_prime0([],_AbsInt,_Sg,_Hv,_Head,_Sv,_ExtraInfo,[]).
each_exit_to_prime0([Exit|LExit],AbsInt,Sg,Hv,Head,Sv,ExtraInfo,[Prime|LPrime]):-
    exit_to_prime(AbsInt,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime),
    each_exit_to_prime0(LExit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,LPrime).

each_abs_sort([ASub_u],AbsInt,LASub):- !,
    abs_sort(AbsInt,ASub_u,ASub),
    LASub=[ASub].
each_abs_sort(LASub_u,AbsInt,LASub):-
    each_abs_sort0(LASub_u,AbsInt,TmpLASub),
    sort(TmpLASub,LASub).

each_abs_sort0([],_AbsInt,[]).
each_abs_sort0([ASub_u|LASub],AbsInt,[ASub|LPrime]):-
    abs_sort(AbsInt,ASub_u,ASub),
    each_abs_sort0(LASub,AbsInt,LPrime).

%% each_concrete([],_,_AbsInt,[]).
%% each_concrete([Call|Calls],X,AbsInt,Concretes):-
%%      concrete(AbsInt,X,Call,Concretes0),
%%      append(Concretes0,Concretes1,Concretes),
%%      each_concrete(Calls,X,AbsInt,Concretes1).

each_project([],_AbsInt,_Sg,_Sv,_HvFv_u,[]).
each_project([Exit|Exits],AbsInt,Sg,Sv,HvFv_u,[Prime|Primes]):-
       project(AbsInt,Sg,Sv,HvFv_u,Exit,Prime),
       each_project(Exits,AbsInt,Sg,Sv,HvFv_u,Primes).

each_extend(Sg,[Prime],AbsInt,Sv,Call,LSucc):- !,
    extend(AbsInt,Sg,Prime,Sv,Call,Succ),
    LSucc=[Succ].
each_extend(Sg,LPrime,AbsInt,Sv,Call,LSucc):-
    each_extend0(Sg,LPrime,AbsInt,Sv,Call,TmpLSucc),
    eliminate_tops_and_equivalents(AbsInt,TmpLSucc,LSucc).

each_extend0(_,[],_AbsInt,_Sv,_Call,[]).
each_extend0(Sg,[Prime|LPrime],AbsInt,Sv,Call,[Succ|LSucc]):-
    extend(AbsInt,Sg,Prime,Sv,Call,Succ),
    each_extend0(Sg,LPrime,AbsInt,Sv,Call,LSucc).

:- pred eliminate_tops_and_equivalents(AbsInt,TmpLSucc,LSucc) # 
     "When multi_success is turned on, @var{TmpLSucc} may contain 
      elements which are top. These can be safely removed from the 
      list of successes. Also, repeated elements in the list can also 
      be safely removed.".

eliminate_tops_and_equivalents(AbsInt,TmpLSucc,LSucc):-
    filter_out_tops(TmpLSucc,LSucc_nb),
    eliminate_equivalent(AbsInt,LSucc_nb,LSucc).

filter_out_tops([],[]).
filter_out_tops(['$top'|LSucc],LSucc_nb):-!,
    filter_out_tops(LSucc,LSucc_nb).
filter_out_tops([Succ|LSucc],LSucc_nb):-
    LSucc_nb = [Succ|MoreSucc],
    filter_out_tops(LSucc,MoreSucc).


each_unknown_call([],_AbsInt,_Sg,_Sv,[]).
each_unknown_call([Call|Calls],AbsInt,Sg,Sv,[Succ|Succs]):-
    unknown_call(AbsInt,Sg,Sv,Call,Succ),
    each_unknown_call(Calls,AbsInt,Sg,Sv,Succs).

each_body_succ_builtin([],_,_T,_Tg,_,_,_Sg,_Sv,_HvFv_u,_F,_N,[]).
each_body_succ_builtin([Call|Calls],AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,
                   F,N,[Succ|Succs]):-
    project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
    body_succ_builtin(AbsInt,T,Tg,Vs,Sv,HvFv_u,Call,Proj,Succ),!,
    project(AbsInt,Sg,Sv,HvFv_u,Succ,Prime),
    singleton(Prime,LPrime),
    asserta_fact(complete(SgKey,AbsInt,Sg,Proj,LPrime,no,[(F,N)])),
    each_body_succ_builtin(Calls,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,
                           F,N,Succs).

%-----------------------------------------------------------------

each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,ListPrime,LPrime):-
    current_pp_flag(multi_success,off), !,
    applicable(ListPrime,AbsInt,Prime0),
    ( apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime0,Prime) -> true
    ; Prime=Prime0
    ),
    singleton(Prime,LPrime).
each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,ListPrime,LPrime):-
    apply_trusted_each(Proj,SgKey,Sg,Sv,AbsInt,ListPrime,LPrime).

%-----------------------------------------------------------------
dual_widen_succ(AbsInt,Prime0,Prime1,LPrime):-
    current_pp_flag(multi_success,on), !,
    reduce_equivalent([Prime0,Prime1],AbsInt,LPrime).
dual_widen_succ(AbsInt,Prime0,Prime1,Prime):-
    current_pp_flag(widen,on), !,
    singleton(P0,Prime0),     % to_see claudio
    singleton(P1,Prime1),     % to_see claudio
    singleton(P,Prime),       % to_see claudio
    dual_widen(AbsInt,P0,P1,P).
dual_widen_succ(AbsInt,Prime0,Prime1,Prime):-
    singleton(P0,Prime0),
    singleton(P1,Prime1),
    singleton(P,Prime),
    compute_glb(AbsInt,[P0,P1],P).

each_identical_abstract([],_,[]).
each_identical_abstract([ASub1|A1s],AbsInt,[ASub2|A2s]):-
    identical_abstract(AbsInt,ASub1,ASub2),
    each_identical_abstract(A1s,_,A2s).

% Checking memoising
%-----------------------------------------------------------------
% have to revise difflsign for recorded_internal!!!
decide_memo(difflsign,Key,NewN,Id,Vars_u,Exit):- !,
    ( top(Exit) -> Exit0 = '$top' ; Exit = p(_,_,Exit0) ),
    asserta_fact(memo_table(Key,difflsign,NewN,Id,Vars_u,Exit0)).
%% ?????????????????
%% decide_memo(AbsInt,Key,NewN,Id,Vars_u,Exit):-
%%      asserta_fact(pragma(Key,NewN,Id,Vars_u,Exit)),!,
%%      asserta_fact(memo_table(Key,AbsInt,NewN,Id,Vars_u,Exit)).
decide_memo(AbsInt,Key,NewN,Id,Vars_u,Exit):-
    asserta_fact(memo_table(Key,AbsInt,NewN,Id,Vars_u,Exit)).

%------------------------------------------------------------------------%

abs_superset_([NewPrime],AbsInt,[TempPrime]):- !,
    fixpoint_covered_gfp(AbsInt,TempPrime,NewPrime).
abs_superset_(AbsInt,NewPrime,TempPrime):-
    abs_subset(AbsInt,TempPrime,NewPrime).

%------------------------------------------------------------------------%

body_succ_meta(apply(F,_),AbsInt,Sv_u,HvFv_u,Call,Exits,Succ):- !,
    call_builtin(AbsInt,'ground/1',ground(F),Sv_u,HvFv_u,Call,Exits,Succ).
body_succ_meta(call(_),AbsInt,_Sv_u,_HvFv,_Call,Exits,[Succ]):- !,
    map_lub(Exits,AbsInt,Succ).
body_succ_meta(not(_),_AbsInt,_Sv_u,_HvFv,Call,_Exits,Succ):- !,
    Succ = Call.
body_succ_meta(Type,_AbsInt,_Sv_u,_HvFv,_Call,_Exits,Succ):-
    meta_call_check(Type), !,
    Succ = ['$bottom'].
body_succ_meta(Sg,AbsInt,Sv_u,HvFv_u,Call,Exits,Succ):-
    predkey_from_sg(Sg,SgKey),
    call_builtin(AbsInt,SgKey,Sg,Sv_u,HvFv_u,Call,Exits,Succ).

call_builtin(AbsInt,SgKey,Sg,Sv_u,HvFv_u,Call,Exits,Succ):-
    special_builtin(AbsInt,SgKey,Sg,Sg,Type,Cvars),
    sort(Sv_u,Sv),
    sort(HvFv_u,HvFv),
    meta_call_to_success(Exits,HvFv,Call,AbsInt,Sg,Type,Cvars,Sv,Succ).

meta_call_to_success([],_,_Call,_AbsInt,_Sg,_Type,_Cvs,_Vars,[]).
meta_call_to_success([Exit|Exits],HvFv,[Call|Calls],AbsInt,Sg,Type,Cvs,Sv,
                 [Succ|Succs]):-
    project(AbsInt,Sg,Sv,HvFv,Exit,Proj),
    body_succ_builtin(AbsInt,Type,Sg,Cvs,Sv,HvFv,Exit,Proj,PseudoSucc),
    extend_meta(Sg,AbsInt,PseudoSucc,HvFv,Call,Succ),
    meta_call_to_success(Exits,HvFv,Calls,AbsInt,Sg,Type,Cvs,Sv,Succs).

extend_meta(findall(X,Y,Z),AbsInt,Prime0,HvFv,Call,Succ):- !,
    varset(Z,Zs),
    project(AbsInt,findall(X,Y,Z),Zs,HvFv,Prime0,Prime),
    extend(AbsInt,findall(X,Y,Z),Prime,Zs,Call,Succ).
extend_meta(_Sg,_AbsInt,Succ,_HvFv,_Call,Succ).

meta_call_check(findall(_,_,Z)):- \+ list_compat(Z).

list_compat(X):- var(X), !.
list_compat([]):- !.
list_compat([_|X]):- list_compat(X).

map_lub([],_AbsInt,'$top').
map_lub([Succ],_AbsInt,Succ).
map_lub([Exit1,Exit2|Exits],AbsInt,Succ):-
    compute_lub(AbsInt,[Exit1,Exit2],Succ0),
    map_lub([Succ0|Exits],AbsInt,Succ).
