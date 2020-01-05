:- module(unfold_builtins,
    [can_be_evaluated/1,
     pure/3,
     bind_ins/3,
     init_cut_predicates/0,
     decide_has_cuts/3,
     has_cuts/2,
     no_side_effects/1,
     is_memo/1,
     execute/1,
     check_not_ignore/2,
     load_modules_with_eval/0,
     translate_lattice_types/4
    ],
    [assertions, datafacts]).

:- use_package(spec(no_debug)).

:- use_module(ciaopp(p_unit/assrt_db), 
    [assertion_read/9, 
     assertion_body/7]).

:- use_module(ciaopp(p_unit/itf_db), [current_itf/3]).

:- use_module(spec(abs_exec_cond), 
    [
        abs_exec_conj_props/3
    ]).
:- use_module(spec(abs_exec_ops), 
    [adapt_info_to_assrt_head/6]).

:- use_module(spec(spec_support), 
    [
        non_static/1
    ]).
:- use_module(spec(unfold_df_operations), 
    [
        unpack_abs_info/5
    ]).

:- use_module(ciaopp(plai/domains), [call_to_entry/10]).
:- use_module(ciaopp(preprocess_flags)).
:- use_module(engine(hiord_rt), ['$meta_call'/1]).
:- use_module(library(terms_check), [instance/2]).
:- use_module(library(terms_vars), [varset/2]). 
:- use_module(library(sets), [ord_subtract/3]).
:- use_module(library(aggregates), [findnsols/4, findall/3]).
:- use_module(library(lists), [member/2]).
:- use_module(library(sort)).
:- use_module(library(compiler)).


:- doc(can_be_evaluated(Goal), "This predicate succeeds if
     @var(Goal) can be executed at compile-time. This can be useful
     both for specializing and analyzing programs. For this, three
     conditions are required about the execution of the goal: it must
     not contain any side-effect, it has to be sufficiently
     instantiated, and its execution must be finite, i.e., must return
     a finite number of solutions (possibly 0) and fail afterwards.").

% cuts cannot be executed at analysis time
can_be_evaluated(!):-!, fail. 
% literals for non static predicates cannot be executed at analysis time
can_be_evaluated(Goal):-
    non_static(Goal),!, 
    fail. 
% negation as failure can be evaluated if the goal can be
% evaluated and the Goal is ground
can_be_evaluated(\+(Goal)):-
    ground(Goal),
    debug('ground negation'),
    (can_be_evaluated(Goal) ->
        !,
        debug('evaluable negation')
    ;
        debug('not evaluable negation'),fail
    ).
% negation as failure can be evaluated if the goal can be
% evaluated and the Goal is ground
can_be_evaluated(\+(Goal)):-!,
    nonvar(Goal),
    debug('nonvar negation'),
    can_be_evaluated(Goal),
    copy_term(Goal,NGoal),
    findnsols(1,a,'$meta_call'(NGoal),L),
    debug(L),
    L=[],
    debug('evaluable to true').
% the hiord call predicate can be evaluated if the goal is 
% not a variable and it can be evaluated.
can_be_evaluated('hiord_rt:call'(Goal)):-!,
    nonvar(Goal),
    can_be_evaluated(Goal).
can_be_evaluated('arithmetic:is'(_,Exp)):-!,
    ground(Exp).
can_be_evaluated(Goal):-
    no_side_effects(Goal),
    is_evaluable(Goal).

is_evaluable(Goal):-
    current_pp_flag(eval_ignore,PPFlag),
    PPFlag \== all,
    check_property(Goal,'basic_props:eval'(_),PPFlag).

execute([]).
execute([Prop|Props]):-
    copy_term(Prop,NProp),
    '$meta_call'(NProp),!,
    instance(Prop,NProp),
    execute(Props).

no_side_effects(Goal):-
    current_pp_flag(sideff_ignore,PPFlag),
    PPFlag \== all,
    check_property(Goal,'basic_props:sideff'(Goal,free),PPFlag).

is_memo(Goal):-
    current_pp_flag(memo_ignore,PPFlag),
    PPFlag \== all,
    check_property(Goal,'basic_props:memo'(_),PPFlag).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pure(L,Sg,Info):- 
    no_side_effects(L),
    will_be_evaluable(L,Sg,Info).

will_be_evaluable(L,Sg,Info):-
    current_pp_flag(eval_ignore,PPFlag),
    PPFlag \== all,
    unpack_abs_info(Info,AbsInt,OldSg,OldSv,OldProj),
    abs_check_property(L,'basic_props:eval'(_),PPFlag,
                       AbsInt,Sg,OldSg,OldSv,OldProj),!.

will_be_evaluable(L,Sg,Info):-
    is_binding_insensitive(L,Sg,Info),
    is_error_free(L,Sg,Info).
    
is_binding_insensitive(L,_Sg,_Info):-
    ground(L),!.
is_binding_insensitive(L,Sg,Info):-
    current_pp_flag(bind_ins_ignore,PPFlag),
    PPFlag \== all,
    (unpack_abs_info(Info,AbsInt,OldSg,OldSv,OldProj) ->
        abs_check_property(L,'basic_props:bind_ins'(_),PPFlag,
                           AbsInt,Sg,OldSg,OldSv,OldProj)
    ;
        check_property(L,'basic_props:bind_ins'(_),PPFlag)
    ).

is_error_free(L,Sg,Info):- 
    current_pp_flag(error_free_ignore,PPFlag),
    PPFlag \== all,
    unpack_abs_info(Info,AbsInt,OldSg,OldSv,OldProj),
    abs_check_property(L,'basic_props:error_free'(_),PPFlag,
                       AbsInt,Sg,OldSg,OldSv,OldProj),!.

abs_check_property(L,Property,PPFlag,AbsInt,Sg,OldSg,OldSv,OldProj):-
    functor(L,F,A),
    functor(NGoal,F,A),
    assertion_read(NGoal,M,Status,comp,Body,_VarNames,_S,_LB,_LE),
    check_not_ignore(PPFlag,M),
    member(Status,[trust,true]),
    assertion_body(NGoal,_Compat,Call,_Succ,Comp,_Comm,Body),
    member(Property,Comp),
    varset(Sg,Sv),
    varset(L,BodyVars),
    ord_subtract(BodyVars,Sv,Fv),
    call_to_entry(AbsInt,OldSv,OldSg,Sv,Sg,not_provided,Fv,OldProj,Entry,_), % TODO: add some ClauseKey? (JF)
    adapt_info_to_assrt_head(AbsInt,L,BodyVars,Entry,NGoal,NewInfo),
    abs_exec_conj_props(Call,AbsInt,NewInfo),!.

check_property(Goal,Property,PPFlag):-
    assertion_read(Goal,M,Status,comp,Body,_VarNames,_S,_LB,_LE),
    check_not_ignore(PPFlag,M),
    member(Status,[trust,true]),
    assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
    member(Property,Comp),
    execute(Call),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
bind_ins(L,Sg,Info):- 
    no_side_effects(L),
    is_binding_insensitive(L,Sg,Info).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% handling of cuts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- data pred_has_cuts/2.

init_cut_predicates:-
    retractall_fact(pred_has_cuts(_,_)).

decide_has_cuts([],_,_).
decide_has_cuts([!|_],F,A):-!,
    add_cut(F,A).
decide_has_cuts([_|Ls],F,A):-
    decide_has_cuts(Ls,F,A).

add_cut(F,A):-
    pred_has_cuts(F,A),!.
add_cut(F,A):-
    asserta_fact(pred_has_cuts(F,A)).

has_cuts(F,A):-
    pred_has_cuts(F,A).

check_not_ignore(L,M) :-
    list(L,atom),
    member(M,L),!,
    fail.
check_not_ignore(all,_M) :- !,fail.
check_not_ignore(_,_M).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
module_has_eval(M):-
    assertion_read(Goal,M,Status,comp,Body,_VarNames,_S,_LB,_LE),
    member(Status,[trust,true]),
    assertion_body(Goal,_Compat,_Call,_Succ,Comp,_Comm,Body),
    member('basic_props:eval'(_),Comp).

load_modules_with_eval:-
    findall(M,module_has_eval(M),Modules),
    sort(Modules,Modules_s),
    use_all_modules(Modules_s).

use_all_modules([]).
use_all_modules([M|Ms]):-
    current_itf(defines_module,M,File),
    use_module(File),
    use_all_modules(Ms).

% ---------------------------------------------------------------------------
% (moved from typeslib) (JFMC)

:- pred translate_lattice_types(Functor, Arity, Goal, NGoal)
    # "Some type checking predicates correspond to basic types in
      the lattice but with a different name. This predicate makes
      the conversion from the type check to the basic type. This
      allows using @tt{native_prop(NGoal, regtype(_))} to determine
      whether @var{Goal} is a regular type check.".

translate_lattice_types('term_typing:integer', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:int', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types('term_typing:float', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:flt', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types('term_typing:number', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:num', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types('term_typing:atom', 1, Goal, NGoal) :-
    !,
    functor(NGoal, 'basic_props:atm', 1),
    arg(1, Goal, Arg),
    arg(1, NGoal, Arg).
translate_lattice_types(_, _, Goal, Goal).

