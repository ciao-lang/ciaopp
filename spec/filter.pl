:- module(filter, [decide_predicate_filter/6], [assertions]).

:- use_package(spec(no_debug)).

:- doc(title,"Filters for Abstraction at the Global Control Level").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module, "This module contains the predicates required in order
   to handle filter assertions which can be interpreted as guides on
   when and how to lose information at the global control level in
   order to guarantee termination.").

:- use_module(spec(unfold_builtins), [execute/1]).

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(library(compiler/p_unit/p_unit_db), [assertion_read/9]).

:- use_module(library(lists), [member/2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Filtering for global control
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
decide_predicate_filter(Sg,Sv,Proj,FSg,FSv,FProj):-
    there_is_filter(Sg,Filter,NGoal),!,
    debug('FILTER'),
    apply_filter(Filter,NGoal,Sg,FSg),
    debug(Sg),
    debug(FSg),
    FSv=Sv,
    FProj=Proj.
decide_predicate_filter(FSg,FSv,FProj,FSg,FSv,FProj).

there_is_filter(Sg,Filter,NGoal):-
    functor(Sg,F,A),
    functor(Goal,F,A),
    assertion_read(Goal,_M,Status,comp,Body,_VarNames,_S,_LB,_LE),
    member(Status,[trust,true]),
    assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
    member('basic_props:filter'(NGoal,Filter),Comp),
    execute(Call),!.

apply_filter([],_,Sg,Sg).
apply_filter([Var|Vars],NGoal,Sg,FSg):-
    find_pos(1,Var,NGoal,Pos),
    abstract(Pos,Sg,NSg),
    apply_filter(Vars,NGoal,NSg,FSg).


find_pos(Arg,Var,NGoal,Pos):-
    arg(Arg,NGoal,Var2),
    Var == Var2,!,
    Pos = Arg.

find_pos(Arg,Var,NGoal,Pos):-
    Arg1 is Arg + 1,
    find_pos(Arg1,Var,NGoal,Pos).
    
abstract(Pos,Sg,NSg):-
    functor(Sg,F,A),
    functor(NSg,F,A),
    copy_some_args(A,Pos,Sg,NSg).

copy_some_args(0,_Pos,_Sg,_NSg):-!.
copy_some_args(Pos,Pos,Sg,NSg):-!,
    Pos1 is Pos - 1,
    copy_some_args(Pos1,Pos,Sg,NSg).
copy_some_args(Arg,Pos,Sg,NSg):-
    arg(Arg,Sg,Value),
    arg(Arg,NSg,Value),
    Arg1 is Arg - 1,
    copy_some_args(Arg1,Pos,Sg,NSg).
