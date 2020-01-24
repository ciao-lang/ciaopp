/*             Copyright (C)1990-94 UPM-CLIP                            */

:- module(inferseff, [
    analyze_side_effects/1, side_effect_builtin/2,
    seff_property/3, cleanup_seff/0
], [assertions, datafacts]).

:- use_module(library(lists), [member/2]).
:- use_module(library(idlists), [memberchk/2]).
:- use_module(engine(messages_basic)).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).

:- use_module(ciaopp(infer/infer_db), [inferred/3]).

:- use_module(ciaopp(pool), [meta_call/1, peel_meta_call/4]).
:- use_module(ciaopp(p_unit), [native_prop/2, type_of_goal/2]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9]).

%====================================================================
%  Copyright(C) 1988, K.Muthukumar, All rights reserved
%====================================================================
% 
%    This program analyzes a given prolog code and annotates 
%    every clause of every predicate as "(pure,pure)", "(soft,pure)",
%    "(soft,soft)", "(hard,pure)", "(hard,soft)", or "(hard,hard)".
%    The first argument in the tuple indicates the nature of the 
%    predicate and the second argument the nature of the clause.
% 
%====================================================================

:- doc(bug, "1 Should be re-entrant! (like plai)").
:- doc(bug, "2 Shouldn't it require a fixpoint?").
:- doc(bug, "3 handling of basiccontrol:true/0 is hardwired!").

%----------------------------------------------------------------------

:- data goal/5, parent/3.

cleanup_seff:- retractall_fact(goal(_,_,_,_,_)).

%----------------------------------------------------------------------

analyze_side_effects(Clauses):-
    pp_statistics(runtime,_),
    retractall_fact(parent(_,_,_)),
    analyze_side_effects_(Clauses),
    pp_statistics(runtime,[_,T1]),
    message(inform, ['{analyzed by seff in ', ~~(T1), ' msec.}']),
    update_info,
    pp_statistics(runtime,[_,T2]),
    message(inform, ['{updated seff info in ', ~~(T2), ' msec.}']).

analyze_side_effects_([Clause:_|List_of_clauses]) :-
    side_effect_analyze(Clause), !,
    analyze_side_effects_(List_of_clauses).
analyze_side_effects_([]).

%----------------------------------------------------------------------

side_effect_analyze(directive(_)).
side_effect_analyze(clause(Head,true)) :- !,
     pure_clause(Head).
side_effect_analyze(clause(Head,!)) :- !,
     pure_clause(Head).
side_effect_analyze(clause(Head,Body)) :-
    check_for_side_effects(Head,Body).

%----------------------------------------------------------------------

pure_clause(Head) :-
    functor(Head,F,A),
    (  current_fact(goal(F,A,Num,X,_)) ->
       Num1 is Num+1,
       asserta_fact(goal(F,A,Num1,X,pure))
    ;  asserta_fact(goal(F,A,1,pure,pure))
    ).

%----------------------------------------------------------------------

check_for_side_effects(Head, Body) :-
    functor(Head,F,A),
    ( current_fact(goal(F,A,Num,X,_)) ->
      Num1 is Num+1
    ; Num1 = 1,
      X = pure
    ),
    recursive_traverse(Body,Y,F/A/Num1),
    decide_side_effect(Y,X,F,A,Num1).

decide_side_effect(pure,X,F,A,Num1):-
    asserta_fact(goal(F,A,Num1,X,pure)).
decide_side_effect(soft,pure,F,A,Num1):- !,
    asserta_fact(goal(F,A,Num1,soft,soft)),
    side_effect_propagate(F/A,soft).
decide_side_effect(soft,X,F,A,Num1):-
    asserta_fact(goal(F,A,Num1,X,soft)).
decide_side_effect(hard,X,F,A,Num1):-
    asserta_fact(goal(F,A,Num1,hard,hard)),
    ( X = hard ->
      true
    ; side_effect_propagate(F/A,hard)
    ).
%----------------------------------------------------------------------

recursive_traverse((A,B),Y,Head) :-
    recursive_traverse(A,Y1,Head),
    recursive_traverse(B,Y2,Head),
    determine_sep_type(Y1,Y2,Y).
recursive_traverse((A;B),Y,Head) :-
    recursive_traverse(A,Y1,Head),
    recursive_traverse(B,Y2,Head),
    determine_sep_type(Y1,Y2,Y).
recursive_traverse((A->B),Y,Head) :-
    recursive_traverse(A,Y1,Head),
    recursive_traverse(B,Y2,Head),
    determine_sep_type(Y1,Y2,Y).
%% recursive_traverse((_=>B),Y,Head) :-
%%      recursive_traverse(B,Y,Head).
%% recursive_traverse((A&B),Y,Head) :-
%%      recursive_traverse(A,Y1,Head),
%%      recursive_traverse(B,Y2,Head),
%%      determine_sep_type(Y1,Y2,Y).
%% recursive_traverse((A\&B),Y,Head) :-
%%      recursive_traverse(A,Y1,Head),
%%      recursive_traverse(B,Y2,Head),
%%      determine_sep_type(Y1,Y2,Y).
recursive_traverse(Sg:_,Y,Head) :-
    functor(Sg,Sgname,A),
    recursive_traverse_call(Sg,Sgname,A,Y),
    add_to_parent_list(Sgname/A,Head).
recursive_traverse(!,Y,Head):-
    recursive_traverse_call(!,!,0,Y),
    add_to_parent_list(!/0,Head).

recursive_traverse_call(Sg,_,_,Y):-
    meta_call(Sg), !, 
    peel_meta_call(Sg,Goal,_,_),
    ( var(Goal) ->
      Y = hard
    ; functor(Goal,Sgname,A),
      recursive_traverse_call(Goal,Sgname,A,Y)
    ).
recursive_traverse_call(_Sg,Sgname,A,Y):-
    side_effect_procedure(Sgname/A,Y), !.
recursive_traverse_call(Sg,Sgname,A,Y):-
    type_of_goal(imported(_M0),Sg),
    side_effect_builtin(Sgname/A,Y), !.
recursive_traverse_call(_Sg,_Sgname,_A,pure).

%----------------------------------------------------------------------

determine_sep_type(X,Y,Type):- sep_type(X,Y,Type), !.

sep_type(hard,_,hard).
sep_type(_,hard,hard).
sep_type(soft,_,soft).
sep_type(_,soft,soft).
sep_type(pure,pure,pure).

%----------------------------------------------------------------------

add_to_parent_list(Sub_goal/A, Goal) :-
    (  current_fact(parent(Sub_goal,A,List),Ref),
       ( memberchk(Goal,List)
       ;  New_list = [Goal|List],
          erase(Ref),
          asserta_fact(parent(Sub_goal,A,New_list))
       )
    ;  asserta_fact(parent(Sub_goal,A,[Goal]))
    ).

%----------------------------------------------------------------------

side_effect_propagate(F/A,SideEffectType) :-
    current_fact(goal(F,A,Num,X,Y),Ref),
    change_clause_info(F/A/Num/(X,Y),SideEffectType,Ref),
    fail.
side_effect_propagate(F/A,SideEffectType) :-
    current_fact(parent(F,A,List)),
    list_propagate(List,SideEffectType).
side_effect_propagate(_,_).

%----------------------------------------------------------------------

change_clause_info(_F/_A/_N/(X,_Y),SideEffectType,_Ref) :-
    X = SideEffectType,!.
change_clause_info(F/A/N/(_X,Y),SideEffectType,Ref) :- 
    erase(Ref),
    asserta_fact(goal(F,A,N,SideEffectType,Y)).

%----------------------------------------------------------------------

list_propagate([],_).
list_propagate([Goal|Goals],X) :-
    list_propagate(Goal,X),!,
    list_propagate(Goals,X).
list_propagate(Goal/A/Num,SideEffectType) :-
    current_fact(goal(Goal,A,Num,X,Y),Ref),
    (  sep_less_than(X,SideEffectType),
       erase(Ref),
       asserta_fact(goal(Goal,A,Num,SideEffectType,SideEffectType)),
       side_effect_propagate(Goal/A,SideEffectType)
    ;  sep_less_than(Y,SideEffectType),
       erase(Ref),
       asserta_fact(goal(Goal,A,Num,X,SideEffectType))
    ;  true
    ).

%----------------------------------------------------------------------

sep_less_than(pure,soft).
sep_less_than(pure,hard).
sep_less_than(soft,hard).

%----------------------------------------------------------------------------

% GP this is a kludge, since true is not module qualified and thus
% the assertions in basiccontrol.pl are not find for this predicate
side_effect_builtin(true/0,pure):-!.
side_effect_builtin(F/A,Type):-
    functor(Goal,F,A),
    Prop=sideff(Goal,_),
    native_prop(Seff,Prop),
    type_of_goal(imported(_M0),Goal),
    % M0 and M do not match!!
    assertion_read(Goal,_M,Status,comp,Body,_Dict,_Source,_LB,_LE),
    ( Status=true ; Status=trust ),
    assertion_body(Goal,_Compat,_Call,_Succ,Comp,_Comm,Body),
    member(Seff,Comp),
    seff_property(Type,_,Prop),
    asserta_fact(goal(F,A,1,Type,Type)).
side_effect_builtin(F/A,hard):-
    asserta_fact(goal(F,A,1,hard,hard)).

side_effect_procedure(F/A,X) :-
    current_fact(goal(F,A,_,soft,_)),
    X = soft.
side_effect_procedure(F/A,X) :-
    current_fact(goal(F,A,_,hard,_)),
    X = hard.

seff_property(pure,G,sideff(G,free)).
seff_property(soft,G,sideff(G,soft)).
seff_property(hard,G,sideff(G,hard)).

update_info:-
    current_fact(goal(F,A,_,X,_)),
    functor(Goal,F,A),
    ( current_fact(inferred(seff,Goal,Y),Ref)
    -> ( X==Y -> true
       ; erase(Ref),
         assertz_fact(inferred(seff,Goal,X))
       )
    ; assertz_fact(inferred(seff,Goal,X))
    ),
    fail.
update_info.
