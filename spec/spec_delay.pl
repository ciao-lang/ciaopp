:- module(spec_delay,
    [ 
        simp_body_list_del/7,
        reorder_delay/1,
        specialize_blocks/5,
        no_delayed_in_point/2,
        key_after_reordering/3,
        wake_end_of_clause/5,
        reorder_del_body/6,
        perform_reord/1,
        build_each_block/4,
        specialize_blocks/5,
        simplify_block/4,
        simp_when_no_lub_each_info/5,
        simplify_when_false_or_chose/7,
        program_points_not_final/4
    ],
    [assertions, regtypes, datafacts]).
     
:- doc(bug, "this module is not ported to ciaopp-1.0 yet").

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [member/2, append/3, select/3]).
:- use_module(library(terms_vars), [varset/2]). 
:- use_module(library(terms), [copy_args/3]). 
:- use_module(library(sort)).
:- use_module(engine(io_basic)).
:- use_module(library(write), [write/2]).

:- use_module(ciaopp(p_unit/program_keys),
    [null_directive_key/1,get_predkey/3, predkey_from_sg/2]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).

% plai library
:- use_module(spec(s_simpspec)).


% GPS now in pool.pl!
%% :- use_module(ciaopp(plai/fixpo_del),
%%      [ no_instantiate_builtin/1,
%%        no_instantiate_builtin_but_change/1
%%      ]).
:- use_module(ciaopp(pool)).
%%      [ no_instantiate_builtin/1,
%%        no_instantiate_builtin_but_change/1
%%      ]).

:- use_module(spec(abs_exec)).
:- use_module(spec(abs_exec_cond), 
    [
        cond/4,
        indep/4,
        ground/3,
        not_ground/3,
        free/3,
        not_free/3
    ]).
:- use_module(ciaopp(plai/domains)).
:- use_module(ciaopp(infer), [get_memo_lub/5]).

% spec library

:- use_module(spec(spec_support), 
    [simplify_indep/4,
     simplify_ground/4,
     special_simp_indep/4,
     special_simp_ground/4,
     no_repetitions/5,
     group_predicate/8,
     record_latest_replacement/3,
     change_call/3]).

:- use_module(ciaopp(p_unit/program_keys), [decode_litkey/5]).

%-------------------------------------------------------------------%
% simp_body_list_del(+,+,-,+,-,+,-)                                 %
% simp_body_list_del(Pred,Goals,NewGoals,Vars,Result,Abs,DelOut)    %
%  Simplifies the list of goals Goals according to Abs and returns  %
% NewGoals and Result, which is a flag to know if a goal reducible  %
% to fail or error has been found. DelOut contains the literals in  %
% Goals which definitely delay in their original location, together %
% with the literal which can first wake them up and a flag that     %
% indicates whether reordering can be done for this literal or not  %
%-------------------------------------------------------------------%
simp_body_list_del(none,[],[],_,nonerror,_,[]).
simp_body_list_del((!/0),[!:K|Goals],[!:K|NewGoals],Vars,Result,Abs,D):-!,
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,NewGoals,Vars,Result,Abs,D).

 %% %-------------------------------------------------------------%
 %% % Goal is a set of parallel goals                             %
 %% % We temporarily avoid parallel goals. Need some thinking!
 %% %-------------------------------------------------------------%
 %% simp_body_list_del('.'/2,[P_exp|Goals],NewGoals,Vars,Result,Abs,D):-!,
 %%     next_pred(P_exp,Pred),
 %%         simp_body_list_del(Pred,P_exp,P_Goals,Vars,TmpResult,Abs,D,TmpD),
 %%         (TmpResult == fail -> % if one fails they all fail!!
 %%         P_exp = [_:K|_],
 %%             NewGoals = [(fail:K)],
 %%         Result = fail
 %%         ;
 %%             (TmpResult == error ->
 %%                 get_last(P_Goals,Last),
 %%                 NewGoals = [Last,(error:'$bottom')],
 %%             Result = error
 %%             ;
 %%                 NewGoals = [P_Goals|MoreGoals],
 %%                 next_pred(Goals,NPred),
 %%                 simp_body_list_del(NPred,Goals,MoreGoals,Vars,Result,Abs,ND),
 %%                 append(TmpD,ND,D),
 %%             )
 %%         ).
%-------------------------------------------------------------%
% Goal is abstractly executable                               %
%-------------------------------------------------------------%
simp_body_list_del(Pred,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs,D):-
    abs_exec(Abs,Pred,Sense,Cond),
    (Cond \== true ->
        get_memo_lub(K,Vars,Abs,yes,Info)
    ;
        true),
    cond(Cond,Abs,Goal,Info),
    !,
    simp_abs_ex_body_list_del(Sense,[(Goal:K)|Goals],NewGoals,Vars,Result,Abs,D).
 %% %-------------------------------------------------------------%
 %% % Goal has bottom as success substitution                     %
 %% %-------------------------------------------------------------%
 %% simp_body_list_del(_P,[(Goal:K)|_],NewGoal,Vars,Result,Abs,[]):-
 %%     decode_litkey(K,P,A,C,G),
 %%         G1 is G+1,
 %%     make_atom([P,A,C,G1],Key1),
 %%     (get_memo_lub(Key1,Vars,Abs,yes,Info) ->
 %%         Info == '$bottom'
 %%         ;
 %%         make_atom([P,A,C],Key2),
 %%         get_memo_lub(Key2,Vars,Abs,yes,Info),
 %%         Info == '$bottom'),
 %%         
 %%         !,
 %%         NewGoal = [(Goal:K),(error:'$bottom')],
 %%         Result = error.

%-------------------------------------------------------------%
% None of the previous                                        %
%-------------------------------------------------------------%
simp_body_list_del(_,[(Goal:K)|Goals],[(Goal:K)|NewGoals],Vars,
                                                    Result,Abs,D):-
    next_pred(Goals,NPred),
    simp_body_list_del(NPred,Goals,NewGoals,Vars,Result,Abs,D).

%-------------------------------------------------------------------%   
% simp_abs_ex_body_list_del(+,+,-,+,-,+,-)                          %
% simp_abs_ex_body_list_del(Sense,Goals,NewGoals,Vars,Result,Abs,D) %
%  Special case of simp_body_list_del when the goal is abstractly   %
%  executable                                                       %
%-------------------------------------------------------------------%
simp_abs_ex_body_list_del(true,[_|Goals],NewGoals,Vars,Result,Abs,D):-
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,NewGoals,Vars,Result,Abs,D).

simp_abs_ex_body_list_del(fail,[_:K|_],[(fail:K)],_Vars,fail,_Abs,[]).

simp_abs_ex_body_list_del(error,[G|_],[G,(error:'$bottom')],_,error,_,[]).
simp_abs_ex_body_list_del(indep,[indep(L):K|Goals],NewGoals,Vars,Result,Abs,D):-
    get_memo_lub(K,Vars,Abs,yes,Info),
    simplify_indep(L,Abs,Info,NewL),
    !,
    (NewL == [] ->
        NewGoals = NGoals
    ;
        NewGoals = [indep(NewL):K|NGoals],
        special_simp_indep(K,Vars,Abs,NewL)),
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,NGoals,Vars,Result,Abs,D).
simp_abs_ex_body_list_del(indep,[indep(_):K|_],[fail:K],_,fail,_,[]).

simp_abs_ex_body_list_del(ground,[ground(T):K|Goals],NewGoals,Vars,Result,Abs,D):-
    varset(T,L),
    get_memo_lub(K,Vars,Abs,yes,Info),
    simplify_ground(L,Abs,Info,NewL),
    !,
    (NewL == [] ->
        NewGoals = NGoals
    ;
        (NewL = [Var] ->
            Term = Var
        ;
            Term = NewL),
        NewGoals = [ground(Term):K|NGoals],
        special_simp_ground(K,Vars,Abs,NewL)),
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,NGoals,Vars,Result,Abs,D).
simp_abs_ex_body_list_del(ground,[ground(_):K|_],[fail:K],_,fail,_,[]).

%-----------------------------------------------------------------------
% simp_abs_ex_body_list_del(when,+,-,+,+,-,+,-).
% main entry point for optimization of dynamic scheduling.
%-----------------------------------------------------------------------

% The goal definitely does not delay. No need to reorder. 
simp_abs_ex_body_list_del(when,[when(_,Goal):K|Goals],NewGoals,Vars,Result,Abs,D):-
    key_after_reordering(Goals,K,Key),
    no_delayed_in_point(Key,K),!,
    NewGoals = [Goal:K|NGoals],
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,NGoals,Vars,Result,Abs,D).

simp_abs_ex_body_list_del(when,[when(Cond,Goal):K|Goals],NGoals,Vars,Result,Abs,D):-
    findall((_,Vars,Info),(recorded_internal(K,
                    memo_table(_,_,Vars,Info),_)),InfoList),
    no_repetitions(InfoList,[],Abs,Vars,LInfo),
    decide_def_delays(LInfo,Cond,Goal,Abs,K,Goals,NGoals,MoreGoals,D,ND),
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,MoreGoals,Vars,Result,Abs,ND).

% The goal definitely does not delay. No need to reorder. 
simp_abs_ex_body_list_del(block_cond(_),[Goal:K|Goals],NGoals,Vars,Res,Abs,D):-
    key_after_reordering(Goals,K,Key),
    no_delayed_in_point(Key,K),!,
    NGoals = [Goal:K|MoreGoals],
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,MoreGoals,Vars,Res,Abs,D).

simp_abs_ex_body_list_del(block_cond(Cond),[Goal:K|Goals],NGoals,Vars,Result,Abs,D):-!,
    findall((_,Vars,Info),(recorded_internal(K,
                    memo_table(_,_,Vars,Info),_)),InfoList),
    no_repetitions(InfoList,[],Abs,Vars,LInfo),
    decide_block_def_delays(LInfo,Cond,Goal,Abs,K,Goals,NGoals,MoreGoals,D,ND),
    next_pred(Goals,Pred),
    simp_body_list_del(Pred,Goals,MoreGoals,Vars,Result,Abs,ND).

simp_abs_ex_body_list_del(freeze,[freeze(Var,Goal):K|Goals],
                                              NewGoals,Vars,R,Abs,D):-
    simp_abs_ex_body_list_del(when,[when(nonvar(Var),Goal):K|Goals],
                                              NewGoals,Vars,R,Abs,D).

% The goal definitely delays. We try to reorder
decide_def_delays(InfoList,Cond,Goal,Abs,K,Goals,NGoals,MoreGoals,D,ND):-
    when_cond_always_fails_no_lub(InfoList,Cond,Abs),!,
    NGoals = MoreGoals,
    D = [d(K2,Flag,K,NewCond,Goal)|ND],
    first_waking_literal(K,Goals,K2,OtherGoal),
    functor(OtherGoal,Name,Arity),
    program_points_not_final(OtherGoal,Name,Arity,Points),
    decide_reorder(Points,K,Abs,Flag,Cond,Goal,NewCond,Goals,K2,InfoList).
% The goal may or may not delay. We do not try to reorder
decide_def_delays(InfoList,Cond,Goal,Abs,K,_Goals,NGoals,MoreGoals,D,D):-
    NGoals = [when(NewCond,Goal):K|MoreGoals],
    simp_when_no_lub_each_info(Cond,InfoList,Abs,TmpCond,_),
    simplify_when_false_or_chose(TmpCond,Abs,K,Goal,NewCond,_,_).
    

% Reordering is allowed
decide_reorder(Points,K,_Abs,Flag,Cond,_Goal,NewCond,_Goals,_K2,_InfoList):-
    no_waking_in_points(Points,K),!,
 %%     write(user, 'Reord to after'),
 %%     write(user,K),
 %%     nl(user),
    Flag=reord,
    NewCond = Cond.
% Reordering is not allowed
decide_reorder(_Points,K,Abs,no,Cond,Goal,NewCond,Goals,K2,InfoList):-
    (key_after_reordering(Goals,K,K2) ->
        NewInfoList = InfoList
    ;
        write(user, 'Reord to before '),
        write(user,K),
        nl(user),
        findall((_,Vars,Info),(recorded_internal(K,
                          memo_table(_,_,Vars,Info),_)),TmpList),
        no_repetitions(TmpList,[],Abs,Vars,NewInfoList)),
    simp_when_no_lub_each_info(Cond,NewInfoList,Abs,TmpCond,_),
    simplify_when_false_or_chose(TmpCond,Abs,K,Goal,NewCond,_,_).


no_delayed_in_point(Key,K):-
    recorded_internal(Key,memo_table(_,_,_,ac(_,g(Delayed,_,_))),_),
    member(pp(K,_),Delayed),!,
    fail.
no_delayed_in_point(_,_).

first_waking_literal(K,[FirstGoal:Kn|Goals],K2,OtherGoal):-
    key_after_reordering(Goals,K,K3),
    recorded_internal(K3,memo_table(_,_,_,ac(_,g(_,Woken,_))),_),
    member(pp(K,_),Woken),!,
    OtherGoal:K2 = FirstGoal:Kn.
first_waking_literal(K,[_|Goals],K2,OtherGoal):-!,
    first_waking_literal(K,Goals,K2,OtherGoal).
first_waking_literal(_,[],end,none).

when_cond_always_fails_no_lub([],_,_).
when_cond_always_fails_no_lub([(_,Info)|Infos],Cond,Abs):-
    when_cond_always_fails(Cond,Abs,Info),
    when_cond_always_fails_no_lub(Infos,Cond,Abs).

 %% decide_simp_when_no_lub(true,_Goal,_Abs,_K,_Vars,true):-!.
 %% decide_simp_when_no_lub(Cond,Goal,Abs,K,Vars,NCond):-
 %%     simplify_when_no_lub(Cond,Abs,K,Vars,TmpCond,Cs,Nums),
 %%     decide_when_false_or_chose(TmpCond,Goal,Abs,K,Cs,Nums,NCond).

 %% decide_when_false_or_chose(true,_Goal,_Abs,_K,_,_,true):-!.
 %% decide_when_false_or_chose(Cond,Goal,Abs,K,Cs,Nums,NCond):-
 %%     simplify_when_false_or_chose(Cond,Abs,K,Goal,NCond,False,True),
 %%     decide_upd_false_true(NCond,K,False,True,Cs,Nums).

% We do not do multiple specialization for dynamic scheduling by now
 %% decide_upd_false_true(true,_,_False,_True,_,_):-!.
 %% decide_upd_false_true(Cond,K,False,True,Cs,Nums):-
 %%     current_fact(do_spec),!,
 %%     update_false_true(Cs,False,True,NCs),
 %%     store_simp_in_versions_when(NCs,Cond,K,Nums).
 %% decide_upd_false_true(_,_,_,_,_,_).



no_waking_in_points([],_).
no_waking_in_points([Point|_],K):-
    recorded_internal(Point,memo_table(_,_,_,ac(_,g(_,Woken,_))),_),
    member(pp(K,_),Woken),!,
    fail.
no_waking_in_points([_|Points],K):-
    no_waking_in_points(Points,K).

key_after_reordering([],K2,Key):-
    decode_litkey(K2,Name,Arity,Clause,_),
    make_atom([Name,Arity,Clause],Key).
key_after_reordering([_:Key|_],_,Key).

%% nonvar2freeze([],[]).
%% nonvar2freeze([when(nonvar(Var),Goal):K|Whens],NWhens):-!,
%%      NWhens = [freeze(Var,Goal):K|MoreWhens],
%%      nonvar2freeze(Whens,MoreWhens).
%% nonvar2freeze([When|Whens],[When|NWhens]):-
%%      nonvar2freeze(Whens,NWhens).

% The goal definitely delays. We try to reorder
decide_block_def_delays(LInfo,Cond,Goal,Abs,K,Goals,NGoals,MoreGoals,D,ND):-
    block_to_when(Cond,Goal,WCond),
    when_cond_always_fails_no_lub(LInfo,WCond,Abs),!,
    NGoals = MoreGoals,
    D = [b(K2,Flag,K,Goal)|ND],
    first_waking_literal(K,Goals,K2,OtherGoal),
    functor(OtherGoal,Name,Arity),
    program_points_not_final(OtherGoal,Name,Arity,Points),
    decide_block_reorder(Points,K,Flag).
% The goal may or may not delay. We do not try to reorder
decide_block_def_delays(_InfoList,_Cond,Goal,_Abs,K,_Goals,NGoals,MoreGoals,D,D):-
    NGoals = [Goal:K|MoreGoals].

block_to_when([Spec],Goal,Cond):-!,
    spec_to_cond(Spec,Goal,Cond).
block_to_when([Spec|Specs],Goal,(Cond,Conds)):-
    spec_to_cond(Spec,Goal,Cond),
    block_to_when(Specs,Goal,Conds).

spec_to_cond([N],Goal,nonvar(Arg)):-!,
    arg(N,Goal,Arg).
spec_to_cond([N|Ns],Goal,(nonvar(Arg);Cond)):-
    arg(N,Goal,Arg),
    spec_to_cond(Ns,Goal,Cond).

% Reordering is allowed
decide_block_reorder(Points,K,Flag):-
    no_waking_in_points(Points,K),!,
    Flag=reord.
% Reordering is not allowed
decide_block_reorder(_Points,_K,no).
    
    
 %% update_false_true(CondList,[],[],CondList):-!.
 %% update_false_true([],_,_,[]).
 %% update_false_true([C|Conds],False,True,[NC|NConds]):-
 %%     update_false(C,False,_,TmpC),
 %%     update_true(TmpC,True,_,NC,_),
 %%     update_false_true(Conds,False,True,NConds).
 %% 
 %% update_false(C,[],[],C):-!.
 %% update_false((L;R),False,NewFalse,NewC):-
 %%     update_false(L,False,TmpFalse,NL),
 %%     update_false(R,TmpFalse,NewFalse,NR),
 %%     decide_when_false_disj(NL,NR,NewC).
 %% update_false((L,R),False,NewFalse,NewC):-
 %%     update_false(L,False,TmpFalse,NL),
 %%     update_false(R,TmpFalse,NewFalse,NR),
 %%     decide_when_false_conj(NL,NR,NewC).
 %% update_false(C,False,NewFalse,NewC):-
 %%     member_advance(C,False,NewFalse),
 %%     !,
 %%     NewC = false.
 %% update_false(C,False,False,C).
 %% 
 %% update_true(C,[],[],C,false):-!.
 %% update_true((L;R),True,NewTrue,NewC,F):-
 %%     update_true(L,True,TmpTrue,NL,F1),
 %%     update_true(R,TmpTrue,NewTrue,NR,F2),
 %%     decide_when_true_disj(F1,F2,F,NL,NR,NewC).
 %% update_true((L,R),True,NewTrue,(NL,NR),F):-
 %%     update_true(L,True,TmpTrue,NL,F1),
 %%     update_true(R,TmpTrue,NewTrue,NR,F2),
 %%     decide_when_true_conj(F1,F2,F).
 %% update_true(C,True,NewTrue,C,F):-
 %%     member_advance(C,True,NewTrue),
 %%     !,
 %%     F = true.
 %% update_true(C,True,True,C,false).
 %% 

 %% member_advance(C,[C1|NewList],NewList):-
 %% %%  C==C1,!.
 %%     C=C1.
 %% member_advance(C,[_|List],NewList):-
 %%     member_advance(C,List,NewList).


 %% %-------------------------------------------------------------------%
 %% % store_simp_in_versions_when(+,+,+,+)                              %
 %% % store_simp_in_versions_when(CondList,Cond,K,Ns)                   %
 %% %-------------------------------------------------------------------%
 %% store_simp_in_versions_when([],_,_,[]).
 %% store_simp_in_versions_when([Cond|CondList],Cond,K,[_N|Ns]):-!,
 %%     store_simp_in_versions_when(CondList,Cond,K,Ns).
 %% store_simp_in_versions_when([Other|CondList],Cond,K,[N|Ns]):-
 %%     add_simplif(N,K,when(Cond,Other)),
 %%     store_simp_in_versions_when(CondList,Cond,K,Ns).


reorder_del_body(Lits,[],_Abs,_Vars,Lits,[]):-!.
reorder_del_body([],Dels,_Abs,_Vars,[],Dels).
reorder_del_body([Lit:Key|Lits],Dels,Abs,Vars,NewBody,MoreDels):-
    get_before(Dels,Key,Before,TmpDels),
    get_after(TmpDels,Key,After,NDels),!,
    append(Before,Tail,NewBody),
    (After \== [] ->
        key_after_reordering(Lits,Key,NextKey)
    ;
        true),
    simplify_after(After,Abs,Key,NextKey,Vars,NewAfter0),
% Ciao does not has freeze/1, so we keep whens
%       nonvar2freeze(NewAfter0,NewAfter),
    NewAfter = NewAfter0,
%
    append([Lit:Key|NewAfter],MoreLits,Tail),
    reorder_del_body(Lits,NDels,Abs,Vars,MoreLits,MoreDels).

wake_end_of_clause([],_Abs,_Vars,_Clid,[]):-!.
wake_end_of_clause(Dels,Abs,Vars,Key,Wakes):-
    get_before(Dels,Key,Before,TmpDels),
    get_after(TmpDels,Key,After,NDels),!,
 %%     (After \== [] ->
 %%         key_after_reordering(Lits,Key,NextKey)
 %%     ;
 %%         true),
    simplify_after(After,Abs,Key,Key,Vars,NewAfter0),
% Ciao does not has freeze/1, so we keep whens
%       nonvar2freeze(NewAfter0,NewAfter),
    NewAfter = NewAfter0,
%
    convert_dels(NDels,NoWoken),
    (NDels \== [] ->
        write(user, 'Literals not woken in their clause'),
        nl(user)
    ;
        true),
    append(NewAfter,NoWoken,Tail),
    append(Before,Tail,Wakes).

convert_dels([],[]).
convert_dels([d(_,_,K,Cond,Goal)|Dels],[when(Cond,Goal):K|Body]):-
    convert_dels(Dels,Body).
convert_dels([b(_,_,K,Goal)|Dels],[Goal:K|Body]):-
    convert_dels(Dels,Body).

get_before([],_,[],[]).
get_before([b(Lit,no,K,Goal)|Dels],Lit,Before,TmpDels):-!,
    Before = [Goal:K|MoreBefore],
    get_before(Dels,Lit,MoreBefore,TmpDels).
get_before([d(Lit,no,K,Cond,Goal)|Dels],Lit,Before,TmpDels):-
    !,
% We no longer convert nonvar2freeze since it is not
% available in Ciao
%%      ( Cond = nonvar(Var) ->
%%          Head = freeze(Var,Goal):K
%%      ;
    Head = when(Cond,Goal):K,
%)
    Before = [Head|MoreBefore],
    get_before(Dels,Lit,MoreBefore,TmpDels).
get_before([D|Dels],Lit,Before,[D|TmpDels]):-
    get_before(Dels,Lit,Before,TmpDels).

get_after([],_,[],[]).
get_after([b(Lit,reord,K,Goal)|Dels],Lit,After,TmpDels):-!,
    After = [Goal:K|MoreAfter],
    get_after(Dels,Lit,MoreAfter,TmpDels).
get_after([d(Lit,reord,K,Cond,Goal)|Dels],Lit,After,TmpDels):-
    !,
    After = [when(Cond,Goal):K|MoreAfter],
    get_after(Dels,Lit,MoreAfter,TmpDels).
get_after([D|Dels],Lit,After,[D|TmpDels]):-
    get_after(Dels,Lit,After,TmpDels).

simplify_after([],_,_,_,_,[]):-!.
% Only one goal. We can simplify Cond
simplify_after([when(Cond,Goal):K],Abs,_Key,NextKey,Vars,NAfs):-!,
    simplify_delay_condition(NextKey,K,NAfs,Goal,[],Cond,Abs,Vars).
% the delaying literas comes from a block. Nothing to do.
simplify_after([Goal:K],_Abs,_Key,_NextKey,_Vars,NAfs):-!,
    NAfs = [Goal:K].

% if more than one there are two cases:
simplify_after(After,Abs,Key,NextKey,Vars,NAfter):-
    simplify_after_two_or_more(After,Key,NextKey,Abs,Vars,NAfter).
% the analysis stores the flag "top"
simplify_after_two_or_more(After,Key,_NextKey,_Abs,_Vars,NAfter):-
    recorded_internal(order,(pp(Key,_),top),_),!,
    NAfter = After,
    write(user, 'Problematic case for reordering: Top at '),
    write(user, Key),
    nl(user).
% or it stores precedences among literals
simplify_after_two_or_more(Afs,Key,NextKey,Abs,Vars,NAfs):-
    simplify_after_no_top(Afs,Key,NextKey,Abs,Vars,NAfs).

% The last element. Simplify it
simplify_after_no_top([when(Cond,Goal):K],_Key,NextKey,Abs,Vars,NAfs):-!,
    simplify_delay_condition(NextKey,K,NAfs,Goal,[],Cond,Abs,Vars).
% Cond could be eliminated directly in some cases.
simplify_after_no_top(Afs,Key,NextKey,Abs,Vars,NAfs):-
    select(Delayed:K,Afs,TmpAfs),
    member(_:K2,TmpAfs),
    \+ before(K2,K,Key),!,
    (Delayed = when(Cond,Goal) ->
       simplify_delay_condition(NextKey,K,NAfs,Goal,MoreAfs,Cond,Abs,Vars)
    ;
        NAfs = [Delayed:K|MoreAfs]),
    simplify_after_no_top(TmpAfs,Key,NextKey,Abs,Vars,MoreAfs).
        
simplify_after_no_top(Afs,Key,_NextKey,_Abs,_Vars,Afs):-
    write(user, 'Problematic case for reordering: No first at '),
    write(user, Key),
    nl(user).

simplify_delay_condition(NextKey,K,NAfs,Goal,MoreAfs,_Cond,_Abs,_Vars):-
    definitely_wakes(NextKey,K),!,
    NAfs = [Goal:K|MoreAfs].
simplify_delay_condition(NextKey,K,NAfs,Goal,MoreAfs,Cond,Abs,Vars):-
    simplify_when_no_lub(Cond,Abs,NextKey,Vars,NewCond,_,_),
    (NewCond == true ->
        NAfs = [Goal:K|MoreAfs]
    ;
        NAfs = [when(NewCond,Goal):K|MoreAfs]).

before(K2,K,Key):-
    recorded_internal(order,(pp(Key,_),Info),_),
    subterm(fst(pp(K2,N),Order),Info),
    subterm(pp(K,N),Order).

% subterm(X,Y).
% X is a subterm of Y, where Y is a ground term
subterm(X,X).
subterm(X,Y):-
    functor(Y,_,A),
    subterm_0(A,X,Y).

subterm_0(A,X,Y):-
    arg(A,Y,Arg),
    subterm(X,Arg).
subterm_0(A,X,Y):-
    A>1,
    A1 is A -1,
    subterm_0(A1,X,Y).

% If the literal is placed after reordering behind a literal which is
% not the last one in clause, if the information after execution of the
% next literal says that "What" is neither woken nor delayed, that means
% that it was woken and its delay condition can be removed.

definitely_wakes(Where,What):-
    decode_litkey(Where,P,A,C,L),
    L1 is L+1,
    make_atom([P,A,C,L1],NextKey),
    (recorded_internal(NextKey,memo_table(_,_,_,_),_) ->
        make_atom([P,A,C],OtherKey),
        Final_Key = OtherKey
    ;
        Final_Key = NextKey),
    no_delayed_in_point(FinalKey,What),
%% % PBC
%%      no_waking_in_point(FinalKey,What).
    no_waking_in_points([FinalKey],What).

%-------------------------------------------------------------------------
% A handle for the user to select reordering or not
%-------------------------------------------------------------------------

:- doc(reorder_delay/1,
    "This predicate handles a flag that indicates
     whether to reorder delayed goals or not during specialization.").
:- pred reorder_delay/1 : var => ok_ans 
    # "Mode for querying the current flag value" .
:- pred reorder_delay/1 : {ground,ok_ans} => ok_ans 
    # "Mode for setting the current flag value" .

reorder_delay(X):-  var(X),!, perform_reord(X).
reorder_delay(X):-  
    ok_ans(X),
    retractall_fact(perform_reord(_)),
    asserta_fact(perform_reord(X)).

:- regtype ok_ans/1.

ok_ans(on).
ok_ans(off).

:- data perform_reord/1.

perform_reord(on).

%----------------------------------------------------------------------
% First we check is specialization of blocks is needed. Then perform it
specialize_blocks(spec,Prog,Ds,NProg,NDs):-
    there_is_delay,!,
    block_names_and_replacements,
    simplify_blocks(Prog,Ds,NProg,NDs).
specialize_blocks(_,Prog,Ds,Prog,Ds).

block_names_and_replacements:-
    recorded_internal(predicates,Preds,_),
    block_names_and_replacements_each_pred(Preds).

block_names_and_replacements_each_pred([]).
block_names_and_replacements_each_pred([F/A|Preds]):-
    findall((Conds,Lits),
        (
        (recorded_internal(simp_block,s(F/A,Conds,Lits),Ref),erase(Ref)))
            ,Literals),
    Literals \== [],!,
    generate_block_names(Literals,F,A,1,Conditions,Names),
    recorda_internal(simp_block,s(F/A,Conditions,Names),_),
    recorda_internal(gen_block,F/A,_),
    block_names_and_replacements_each_pred(Preds).
block_names_and_replacements_each_pred([_|Preds]):-
    block_names_and_replacements_each_pred(Preds).
%----------------------------------------------------------------------
% simplify_blocks(+,+,-,-)
% simplify_blocks(Program,Dicts,NewProg,NewDicts).
%  All the simplifications have already taken place. 
% We generate specialized versions for predicates with blocks which can 
% be optimized.

simplify_blocks([],[],[],[]).
simplify_blocks([directive(D):Id|Cs],[Dict|Dicts],
                [directive(D):Id|SCs],[Dict|NewDicts]):-
    simplify_blocks(Cs,Dicts,SCs,NewDicts).
simplify_blocks(Cs,Ds,NCs,NDs):-
    group_predicate(Cs,Ds,N,A,Pred,Dict,MoreCs,MoreDs),
    block_no_version(Pred,NBPreds),
    generate_block_versions(N,A,Pred,Dict,BPreds,BDicts),
    append(BPreds,SCs,TmpCs),
    append(BDicts,SDs,TmpDs),
    append(NBPreds,TmpCs,NCs),
    append(Dict,TmpDs,NDs),
    simplify_blocks(MoreCs,MoreDs,SCs,SDs).

generate_block_versions(F,A,Pred,Dict,BPreds,BDicts):-
    recorded_internal(simp_block,s(F/A,Cond,Names),_),!,
    block_versions(Cond,Names,F,A,Pred,Dict,BPreds,BDicts).
generate_block_versions(_,_,_,_,[],[]).

generate_block_names([],_,_,_,[],[]).
generate_block_names([(C,Literals)|Conds],F,A,N,[C|Cs],[Name|Names]):-
    make_atom([F,A,'$b',N],Name),
    N1 is N+1,
    record_block_replacements(Literals,Name),
    generate_block_names(Conds,F,A,N1,Cs,Names).

record_block_replacements([],_).
record_block_replacements([GoalKey|Keys],Name):-
    record_latest_replacement(GoalKey,block,Name),
    record_block_replacements(Keys,Name).

block_versions(Conds,BNames,F,A,Pred,Dict,BPreds,BDicts):-
    recorded_internal(gen_block,F/A,Ref),!,
    erase(Ref),
    block_version_with_dec(Conds,BNames,A,Pred,Dict,BPreds,BDicts).

block_versions(_Conds,BNames,_F,A,Pred,Dict,BPreds,BDicts):-
    block_version_no_dec(BNames,A,Pred,Dict,BPreds,BDicts).

block_version_with_dec([],[],_,_Pred,_Dict,[],[]).
block_version_with_dec([C|Conds],[Name|BNames],A,Pred,Dict,BPreds,BDicts):-
    block_declaration(C,Name,A,Declaration),
    replace_blocks(Pred,Name,A,BPred),
    append(Declaration,BPred,NewPred),
    append(NewPred,SBPreds,BPreds),
    append([dic([],[])|Dict],SBDicts,BDicts),
    block_version_with_dec(Conds,BNames,A,Pred,Dict,SBPreds,SBDicts).

block_version_no_dec([],_,_Pred,_Dict,[],[]).
block_version_no_dec([Name|BNames],A,Pred,Dict,BPreds,BDicts):-
    replace_blocks(Pred,Name,A,BPred),
    append(BPred,SBPreds,BPreds),
    append(Dict,SBDicts,BDicts),
    block_version_no_dec(BNames,A,Pred,Dict,SBPreds,SBDicts).

block_no_version([],[]).
block_no_version([clause(Head,Body):Id|Cs],[clause(Head,NBody):Id|NCs]):-
    replace_blocks_in_body(Body,NBody),
    block_no_version(Cs,NCs).
    
block_declaration([],_,_,[]). % no block needed
block_declaration(C,Name,A,[Declaration]):-
    Declaration = directive(block(L)):DK,
    null_directive_key(DK),
    build_each_block(C,Name,A,L).

build_each_block([List],Name,A,Term):-
    functor(Term,Name,A),
    fill_block_dec(A,Term,List).
build_each_block([List|Lists],Name,A,(Term,Terms)):-
    functor(Term,Name,A),
    fill_block_dec(A,Term,List),
    build_each_block(Lists,Name,A,Terms).

fill_block_dec(0,_Term,_List).
fill_block_dec(A,Term,List):-
    member(A,List),!,
    arg(A,Term,'-'),
    A1 is A-1,
    fill_block_dec(A1,Term,List).
fill_block_dec(A,Term,List):-
    arg(A,Term,'?'),
    A1 is A-1,
    fill_block_dec(A1,Term,List).

replace_blocks([],_,_,[]).
replace_blocks([clause(Head,Body):Id|Cs],Name,A,[clause(NHead,NBody):Id|NCs]):-
    functor(NHead,Name,A),
    copy_args(A,Head,NHead),
    replace_blocks_in_body(Body,NBody),
    replace_blocks(Cs,Name,A,NCs).

replace_blocks_in_body([],[]).
%-------------------------------------------------------------%
% If we have generated a new version, here we call it         %
%-------------------------------------------------------------%
replace_blocks_in_body([(Goal:K)|Goals],[(NewGoal:K)|NewGoals]):-
    recorded_internal(K,replace(block,NewName),_),
    !,
    change_call(Goal,NewGoal,NewName),
    replace_blocks_in_body(Goals,NewGoals).
%-------------------------------------------------------------%
% Goal is a set of parallel goals                             %
%-------------------------------------------------------------%
replace_blocks_in_body([Parall_exp|Goals],[NewParall|MoreGoals]):-
    functor(Parall_exp,'.',2), % it is a list
    !,
    replace_blocks_in_body(Parall_exp,NewParall),
    replace_blocks_in_body(Goals,MoreGoals).
%-------------------------------------------------------------%
% We copy the goal as it is                                   %
%-------------------------------------------------------------%
replace_blocks_in_body([G|Goals],[G|NewGoals]):-      
    replace_blocks_in_body(Goals,NewGoals).
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% %-----------------------------------------------------------------------
%% % Simplification of delay conditions
%% % simplify_when(+,+,+,-)
%% % simplify_when(Cond,Abs,Info,NewCond)
%% % Conditions that are sure to suceed are simplified. Conditions that
%% % are sure to fail cannot be eliminated.
%% simplify_when((L,R),Abs,Info,NewCond):-!,
%%      simplify_when(L,Abs,Info,Simp_L),
%%      simplify_when(R,Abs,Info,Simp_R),
%%      join_conj_when(Simp_L,Simp_R,NewCond).
%% simplify_when((L;R),Abs,Info,NewCond):-!,
%%      simplify_when(L,Abs,Info,Simp_L),
%%      simplify_when(R,Abs,Info,Simp_R),
%%      join_disj_when(Simp_L,Simp_R,NewCond).
%% simplify_when(Cond,Abs,Info,NewCond):-
%%      when_cond_holds(Cond,Abs,Info),!,
%%      NewCond = true.
%% simplify_when(Cond,_,_,Cond).

join_conj_when(true,R,NewCond):-!,
    NewCond = R.
join_conj_when(L,true,NewCond):-!,
    NewCond = L.
join_conj_when(L,R,NewCond):-
    NewCond=(L,R).

join_disj_when(true,_,NewCond):-!,
    NewCond = true.
join_disj_when(_,true,NewCond):-!,
    NewCond = true.
join_disj_when(L,R,NewCond):-
    NewCond=(L;R).

when_cond_holds(ground(X),_Abs,_Info):-
    ground(X),!. % concrete domain!
when_cond_holds(ground(X),Abs,Info):-
    ground(Abs,X,Info).
when_cond_holds(nonvar(X),_Abs,_Info):-
    nonvar(X),!. % concrete domain!
when_cond_holds(nonvar(X),Abs,Info):-
    not_free(Abs,X,Info).
when_cond_holds(?=(X,Y),_Abs,_Info):-
    ground(X),ground(Y),!. % concrete domain!
when_cond_holds(?=(X,Y),_Abs,_Info):-
    X==Y,!. % concrete domain!
when_cond_holds(?=(X,Y),Abs,Info):-
    ground(Abs,X,Info),
    ground(Abs,Y,Info).

when_cond_always_fails((L,R),Abs,Info):-!,
    (when_cond_always_fails(L,Abs,Info)
    ;
    when_cond_always_fails(R,Abs,Info)).
when_cond_always_fails((L;R),Abs,Info):-!,
    when_cond_always_fails(L,Abs,Info),
    when_cond_always_fails(R,Abs,Info).

when_cond_always_fails(Cond,Abs,Info):-
    cond_fails(Cond,Info,Abs).

 %% %-----------------------------------------------------------------------
 %% % simplify_when_no_lub(+,+,+,+)
 %% % As Cond may contain disjunctions, it seems important to try to simplify
 %% % Cond for each memo_table instead of their lub
 %% simplify_when_no_lub(Cond,Abs,K,Vars):-
 %%     findall((Info,Vars),(recorded_internal(K,
 %%                     memo_table(_Num,no,Vars,Info),_)),InfoList),
 %%     simplify_when_no_lub_each_info(InfoList,Vars,Cond,Abs).
 %% 
 %% simplify_when_no_lub_each_info([],_,_,_).
 %% simplify_when_no_lub_each_info([(Info,Vars)|Infos],Vars,Cond,Abs):-
 %%     abs_sort(Abs,Info,S_Info),
 %%     simplify_when(Cond,Abs,S_Info,true),
 %%     simplify_when_no_lub_each_info(Infos,Vars,Cond,Abs).
%-----------------------------------------------------------------------
% simplify_when_no_lub(+,+,+,+,-,-,-)
% simplify_when_no_lub(Cond,Abs,K,Vars,NewCond,CondList,Nums)
% As Cond may contain disjunctions, it seems important to try to simplify
% Cond for each memo_table instead of their lub
simplify_when_no_lub(Cond,Abs,K,Vars,NewCond,CondList,Nums):-
    findall((Num,Vars,Info),(recorded_internal(K,
                    memo_table(Num,_,Vars,Info),_)),InfoList),
    no_repetitions(InfoList,[],Abs,Vars,AccessList),
    nums(AccessList,Nums),
    simp_when_no_lub_each_info(Cond,AccessList,Abs,NewCond,CondList).

simp_when_no_lub_each_info((L;R),AccList,Abs,NewCond,CondList):-!,
    simp_when_no_lub_each_info(L,AccList,Abs,Simp_L,CList_L),
    simp_when_no_lub_each_info(R,AccList,Abs,Simp_R,CList_R),
    (true_in_either_each_info(CList_L,CList_R)->
        NewCond = true,
        make_list_of_true(CList_L,CondList)
    ;
        NewCond = (Simp_L;Simp_R),
        join_disj_when_each_info(CList_L,CList_R,CondList)).
simp_when_no_lub_each_info((L,R),AccList,Abs,NewCond,CondList):-!,
    simp_when_no_lub_each_info(L,AccList,Abs,Simp_L,CList_L),
    simp_when_no_lub_each_info(R,AccList,Abs,Simp_R,CList_R),
    join_conj_when_each_info(CList_L,CList_R,CondList),
    join_conj_when(Simp_L,Simp_R,NewCond).
simp_when_no_lub_each_info(Cond,AccList,Abs,NewCond,CondList):-
    when_cond_holds_each_info(AccList,Cond,Abs,CondList),
    (list_of_true(CondList)->
        NewCond = true
    ;
        NewCond = Cond).

when_cond_holds_each_info([],_Cond,_Abs,[]).
when_cond_holds_each_info([(_,Info)|AccList],Cond,Abs,[NewCond|CondList]):-
    (when_cond_holds(Cond,Abs,Info)->
        NewCond = true
    ;
        NewCond = Cond),
    when_cond_holds_each_info(AccList,Cond,Abs,CondList).

nums([],[]).
nums([(Num,_)|More],[Num|Nums]):-
    nums(More,Nums).

true_in_either_each_info([],[]).
true_in_either_each_info([true|Conds_L],[_|Conds_R]):-!,
    true_in_either_each_info(Conds_L,Conds_R).
true_in_either_each_info([_|Conds_L],[true|Conds_R]):-
    true_in_either_each_info(Conds_L,Conds_R).

make_list_of_true([],[]).
make_list_of_true([_|Cs],[true|Trues]):-
    make_list_of_true(Cs,Trues).

list_of_true([]).
list_of_true([true|Trues]):-
    list_of_true(Trues).

join_disj_when_each_info([],[],[]).
join_disj_when_each_info([CL|CLs],[CR|CRs],[NewCond|Conds]):-
    join_disj_when(CL,CR,NewCond),
    join_disj_when_each_info(CLs,CRs,Conds).

join_conj_when_each_info([],[],[]).
join_conj_when_each_info([CL|CLs],[CR|CRs],[NewCond|Conds]):-
    join_conj_when(CL,CR,NewCond),
    join_conj_when_each_info(CLs,CRs,Conds).

%----------------------------------------------------------------------
% Performs simplifications 3.2 and 3.3. as follows:
%    (3.2) eliminate_when_false: if some condition is known to fail
%          for all awaking contexts of the goal, i.e., for all calling 
%          patterns to the associate predicate corresponding to this 
%          particular goal, i.e. those in which (K,_) is a member of Fs, 
%          then the condition can be eliminated. 
%    (3.3) chose_when_true: if one or more conditions are known to 
%          succeed for all awaking contexts of the goal, then one of such
%          conditions can be chosen and the rest eliminated
simplify_when_false_or_chose(Cond,_Abs,_K,Goal,NewCond,Simp_F,Simp_T):-
    type_of_goal(builtin(_),Goal),
    !,
    Cond=NewCond,
    Simp_F=[],
    Simp_T=[].
simplify_when_false_or_chose(Cond,Abs,Key,Goal,NewCond,Simp_F,Simp_T):-
    predkey_from_sg(Goal,Key),
    findall((Goal,ACns),
 %% simplification below removed for ICLP
 %%      ((recorded_internal(Key,complete(Goal,d(ACns_u,_,_),_,_,Fs),_)),
 %%       member((K,_),Fs),
 %%       abs_sort(Abs,ACns_u,ACns)),Calls),
 %%     ( Calls = [] ->  % the goal definitely delays
 %%         NewCond = nonvar(_), % this is always false
 %%         Simp_F = [],
 %%         Simp_T = []
 %%     ; 
    ((recorded_internal(Key,complete(Goal,d(ACns_u,_,_),_,_,_Fs),_)),
    abs_sort(Abs,ACns_u,ACns)),Calls),
    eliminate_when_false(Cond,Calls,Goal,Abs,TmpCond,Simp_F),
%%        ( Cond \== TmpCond -> write(user,eliminate_when_false),write(user,(Cond,TmpCond)),nl(user); true),
      chose_when_true(TmpCond,Calls,Goal,Abs,NewCond,_,Simp_T),
%%        ( TmpCond \== NewCond -> write(user,chose_when_true),write(user,(TmpCond,NewCond)),nl(user); true),
      true.

eliminate_when_false((C1;C2),Calls,Goal,Abs,NewCond,False):-  !,
    eliminate_when_false(C1,Calls,Goal,Abs,NewCond1,False1),
    eliminate_when_false(C2,Calls,Goal,Abs,NewCond2,False2),
    decide_when_false_disj(NewCond1,NewCond2,NewCond),
    append(False1,False2,False).
eliminate_when_false((C1,C2),Calls,Goal,Abs,NewCond,False):- !,
    eliminate_when_false(C1,Calls,Goal,Abs,NewCond1,False1),
    eliminate_when_false(C2,Calls,Goal,Abs,NewCond2,False2),
    decide_when_false_conj(NewCond1,NewCond2,NewCond),
    append(False1,False2,False).
eliminate_when_false(C,Calls,Goal,Abs,NewCond,False):- 
    is_false_cond(Calls,Goal,C,Abs),
    !,
    NewCond = false,
    False = [C].
eliminate_when_false(Cond,_Calls,_Goal,_Abs,Cond,[]).

is_false_cond([],_,_,_).
is_false_cond([(Goal1,ACns)|Calls],Goal,Cond,Abs):-
    Goal = Goal1,
    cond_fails(Cond,ACns,Abs),
    is_false_cond(Calls,Goal,Cond,Abs).

cond_fails(ground(X),Info,Abs):-
    not_ground(Abs,X,Info).
cond_fails(nonvar(X),Info,Abs):-
    free(Abs,X,Info).
cond_fails(?=(X,Y),Abs,Info):-
    free(Abs,X,Info),
    free(Abs,Y,Info),
    indep(Abs,X,Y,Info).


decide_when_false_disj(false,Cond,Cond):- !.
decide_when_false_disj(Cond,false,Cond):- !.
decide_when_false_disj(Cond1,Cond2,(Cond1;Cond2)).
    
decide_when_false_conj(false,_,false):- !.
decide_when_false_conj(_,false,false):- !.
decide_when_false_conj(Cond1,Cond2,(Cond1,Cond2)).

chose_when_true((C1;C2),Calls,Goal,Abs,NewCond,F,True):-  !,
    chose_when_true(C1,Calls,Goal,Abs,NewCond1,F1,True1),
    chose_when_true(C2,Calls,Goal,Abs,NewCond2,F2,True2),
    decide_when_true_disj(F1,F2,F,NewCond1,NewCond2,NewCond),
    append(True1,True2,True).
chose_when_true((C1,C2),Calls,Goal,Abs,(NewCond1,NewCond2),F,True):- !,
    chose_when_true(C1,Calls,Goal,Abs,NewCond1,F1,True1),
    chose_when_true(C2,Calls,Goal,Abs,NewCond2,F2,True2),
    decide_when_true_conj(F1,F2,F),
    append(True1,True2,True).
chose_when_true(C,Calls,Goal,Abs,C,F,True):- 
    is_true_cond(Calls,Goal,C,Abs),
    !,
    F = true,
    True = [C].
chose_when_true(C,_Calls,_Goal,_Abs,C,false,[]).

is_true_cond([],_,_,_).
is_true_cond([(Goal1,ACns)|Calls],Goal,Cond,Abs):-
    Goal = Goal1,
    when_cond_holds(Cond,Abs,ACns),
    is_true_cond(Calls,Goal,Cond,Abs).

decide_when_true_disj(true,_,true,Cond,_,Cond):- !.
decide_when_true_disj(_,true,true,_,Cond,Cond):- !.
decide_when_true_disj(_,_,false,Cond1,Cond2,(Cond1;Cond2)).

decide_when_true_conj(true,true,true):- !.
decide_when_true_conj(_,_,false).

simplify_block([],_,_,[]).
simplify_block([C|Cond],Abs,InfoList,NCond):-
    block_is_false_each_info(InfoList,C,Abs),!,
    simplify_block(Cond,Abs,InfoList,NCond).
simplify_block([C|Cond],Abs,List,[C|NCond]):-
    simplify_block(Cond,Abs,List,NCond).

block_is_false_each_info([],_,_).
block_is_false_each_info([c(Head,Call,_)|InfoList],C,Abs):-
    block_is_false(C,Head,Abs,Call),!,
    block_is_false_each_info(InfoList,C,Abs).

%% %------------------------------------------------------------------
%% % this predicates are used to check if an individual call to a predicate
%% % with a block declaration make false some of the conditions (and can 
%% % be eliminated from the block declaration
%% :- push_prolog_flag(multi_arity_warnings,off).
%% simplify_block([],_Goal,_Abs,_Info,[]).
%% simplify_block([C|Cond],Goal,Abs,Info,NewCond):-
%%      block_is_false(C,Goal,Abs,Info),!,
%%      simplify_block(Cond,Goal,Abs,Info,NewCond).
%% simplify_block([C|Cond],Goal,Abs,Info,[C|NewCond]):-
%%      simplify_block(Cond,Goal,Abs,Info,NewCond).
%% :- push_prolog_flag(multi_arity_warnings,off).

block_is_false([Num|_],Goal,Abs,Info):-
    arg(Num,Goal,Arg),
    when_cond_holds(nonvar(Arg),Abs,Info).
block_is_false([_|Nums],Goal,Abs,Info):-
    block_is_false(Nums,Goal,Abs,Info).

%% special_block(F,A,Cond,K):-
%%      recorded_internal(simp_block,s(F/A,Cond,List),Ref),!,
%%      erase(Ref),
%%      insert(List,K,List2),
%%      recorda_internal(simp_block,s(F/A,Cond,List2),_).
%% special_block(F,A,Cond,K):-
%%      recorda_internal(simp_block,s(F/A,Cond,[K]),_).

 %% generic2particular_conditions([([],List)],NCond):-
 %%     conjunction_nonvars(List,NCond).
 %% generic2particular_conditions([([],List)|MoreList],(NCond;MoreCond)):-
 %%     conjunction_nonvars(List,NCond),
 %%     generic2particular_conditions(MoreList,MoreCond).
 %% 
 %% conjunction_nonvars([Term],nonvar(Term)).
 %% conjunction_nonvars([Term|Terms],(nonvar(Term),More)):-
 %%     conjunction_nonvars(Terms,More).
    

%----------------------------------------------------------------------
% Auxiliary predicates for reordering in dynamic scheduling
%----------------------------------------------------------------------
% program_points_not_final(+,+,+,-).
% program_points_not_final(Goal,Name,Arity,Points)
%  Points in the list of program points which are possibly not final for
%  the computation of any instance of Goal

program_points_not_final(Goal,_Name,_Arity,Points):-
    type_of_goal(builtin(_),Goal),
    !,
    Points = [].

program_points_not_final(Goal,_,_,Points):-
    type_of_goal(metapred(_,_),Goal),!,
    peel_meta_call(Goal,Call,_,_),
    functor(Call,Name,Arity),
    program_points_not_final(Call,Name,Arity,Points).

program_points_not_final(_Goal,Name,Arity,Points):-
    get_predkey(Name,Arity,Key),
    findall(Body,recorded_internal(Key,clause(_,_,_,_,Body),_),Clauses),
    program_points_clauses_not_final(Clauses,[Key],[],_,_,Points_u),
    sort(Points_u,Points).

program_points_clauses_not_final([],NF,P,NF,P,[]).
program_points_clauses_not_final([C|Cs],NF,P,NNF,NP,Points):-
    program_points_one_clause_not_final(C,NF,P,TmpNF,TmpP,CPoints),
    program_points_clauses_not_final(Cs,TmpNF,TmpP,NNF,NP,CsPoints),
    append(CPoints,CsPoints,Points).

program_points_one_clause_not_final((L,R),NF,P,NNF,NP,Points):-
    L = [_,_,('$builtin',Sk,_)],!,
    ( (no_instantiate_builtin(Sk);no_instantiate_builtin_but_change(Sk)) ->
        Points = MorePoints
    ; key_of_next_literal(R,K),
      Points = [K|MorePoints]),
    program_points_one_clause_not_final(R,NF,P,NNF,NP,MorePoints).
program_points_one_clause_not_final((L,R),NF,P,NNF,NP,Points):-
    L = [_,_,('$meta',_,Call)],!,
    get_predicate_in_meta_call(Call,Pred),
    program_points_one_clause_not_final((Pred,R),NF,P,NNF,NP,Points).
program_points_one_clause_not_final((L,R),NF,P,NNF,NP,Points):-!,
    program_points_one_atom((L,R),P,TmpP,L_Points),
    program_points_one_clause_not_final(R,NF,TmpP,NNF,NP,R_Points),
    append(L_Points,R_Points,Points).
program_points_one_clause_not_final([_,_,('$builtin',_,_)],NF,P,NF,P,[]):-!.
program_points_one_clause_not_final([_,_,('$meta',_,Call)],NF,P,NNF,NP,Points):-!,
    get_predicate_in_meta_call(Call,Pred),
    program_points_one_clause_not_final(Pred,NF,P,NNF,NP,Points).
program_points_one_clause_not_final([_,_,(Key,_,_)],NF,P,NNF,NP,Points):-
    (member(Key,NF);member(Key,P)),!,
    NNF=NF,
    NP = P,
    Points = [].
program_points_one_clause_not_final([_,_,(Key,_,_)],NF,P,NNF,NP,Points):-
    findall(Body,recorded_internal(Key,clause(_,_,_,_,Body),_),Clauses),
    program_points_clauses_not_final(Clauses,[Key|NF],P,NNF,NP,Points).


program_points_one_atom(([_,_,('$builtin',Sk,_)],R),P,P,Points):-
    ( (no_instantiate_builtin(Sk); no_instantiate_builtin_but_change(Sk))->
         Points =[]
    ;
        key_of_next_literal(R,K),
        Points = [K]).
program_points_one_atom(([_,_,('$meta',_,Call)],R),P,NP,Points):-!,
    get_predicate_in_meta_call(Call,Pred),
    program_points_one_atom((Pred,R),P,NP,Points).
program_points_one_atom(([_,_,(Key,_,_)],_),P,NP,Points):-!,
    program_points(Key,P,NP,Points).

get_predicate_in_meta_call(Call,[_,_,Goal]):-
    functor(Call,_,2),!,
    arg(2,Call,Goal).
get_predicate_in_meta_call(Call,[_,_,Goal]):-
    functor(Call,_,1),!,
    arg(1,Call,Goal).
get_predicate_in_meta_call(Call,[_,_,Goal]):-
    functor(Call,_,3),
    arg(2,Call,Goal).

key_of_next_literal([K,_,_],K).
key_of_next_literal(([K,_,_],_),K).

program_points(Key,P,NP,Points):-
    member(Key,P),!,
    NP = P,
    Points = [].
program_points(Key,P,NP,Points):-
    findall((Body,D),
            recorded_internal(Key,clause(_,_,_,D,Body),_),Clauses),
    program_points_clauses(Clauses,[Key|P],NP,Points).

program_points_clauses([],P,P,[]).
program_points_clauses([(C,Id)|Cs],P,NP,Points):-
    program_points_one_clause(C,Id,P,TmpP,CPoints),
    program_points_clauses(Cs,TmpP,NP,CsPoints),
    append(CPoints,CsPoints,Points).

program_points_one_clause((L,R),Id,P,NP,Points):-
    L = [_,_,('$builtin',Sk,_)],!,
    ( (no_instantiate_builtin(Sk);no_instantiate_builtin_but_change(Sk)) ->
        Points = MorePoints
    ; key_of_next_literal(R,K),
      Points = [K|MorePoints]),
    program_points_one_clause(R,Id,P,NP,MorePoints).
program_points_one_clause((L,R),Id,P,NP,Points):-
    L = [_,_,('$meta',_,Call)],!,
    get_predicate_in_meta_call(Call,Pred),
    program_points_one_clause((Pred,R),Id,P,NP,Points).
program_points_one_clause((L,R),Id,P,NP,Points):-!,
    program_points_one_atom((L,R),P,TmpP,L_Points),
    program_points_one_clause(R,Id,TmpP,NP,R_Points),
    append(L_Points,R_Points,Points).
program_points_one_clause(Last,Id,P,NP,Points):-
    program_points_one_atom((Last,[Id,_,_]),P,NP,Points).
