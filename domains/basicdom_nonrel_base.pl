% (this is an included file)

% TODO:[merge] merge with 'nonrel_base'?
% TODO:[merge] merge snippet with 'nonrel_base_doc'?

% ---------------------------------------------------------------------------
% (dependencies)

:- include(dominterf(basicdom_base)).

:- use_module(library(sort), [sort/2]).
:- use_module(library(sets), [ord_union/3]).

% ---------------------------------------------------------------------------
%! # Required predicates for this trait
%
% These are the predicates that must be defined by the user in order
% to implement this domain:

% less_or_equal_el/2
% lub_el/3
% widen_el/3
% glb_el/3
% abstract_term/3

% ===========================================================================
%! # basicdom_base implementation
% Non-relational domains are an instance of relational ones.

% ---------------------------------------------------------------------------

:- regtype(asub/1).
asub('$bottom').
asub([_/_|Xs]) :- asub(Xs).

less_or_equal('$bottom', '$bottom').
less_or_equal([], []).
less_or_equal([X/Vx|Xs], [Y/Vy|Ys]) :-
    X == Y, !,
    less_or_equal_el(Vx, Vy),
    less_or_equal(Xs, Ys).
less_or_equal(_, _) :-
    throw(error(variable_mismatch, less_or_equal/2)).

lub('$bottom', ASub, ASub).
lub(ASub, '$bottom',  ASub).
lub('$bottom', '$bottom','$bottom').
lub([], [], []).
lub([X/Vx|Xs], [Y/Vy|Ys], Lub) :-
    X == Y, !,
    lub_el(Vx, Vy, Lub_el),
    Lub = [X/Lub_el|Lub_temp], 
    lub(Xs, Ys, Lub_temp).
lub(_, _, _) :- 
    throw(error(variable_mismatch, lub/3)).

widen('$bottom', '$bottom', '$bottom').
widen([], [], []).
widen([X/Vx|Xs], [Y/Vy|Ys], Lub) :-
    X == Y, !,
    widen_el(Vx, Vy, Lub_el),
    Lub = [X/Lub_el|Lub_temp], 
    widen(Xs, Ys, Lub_temp).
widen(_, _, _) :-
    throw(error(variable_mismatch, widen/3)).

:- push_prolog_flag(multi_arity_warnings, off).
project(_, '$bottom', '$bottom').
project(Vs, ASub, Proj) :- %%% Sanity
    sort(Vs, Vs_s),
    sort(ASub, ASub_s),
    project_(Vs_s, ASub_s, Proj).
:- pop_prolog_flag(multi_arity_warnings).
project_([], _, []).
project_([V|Vs], [X/Vx|ASub], Proj) :- %%% ASub is sorted
    V == X, !,
    Proj = [X/Vx|Proj_temp],
    project_(Vs, ASub, Proj_temp).
project_([V|Vs], [_|ASub], Proj) :- %%% ASub is sorted
    !,
    project_([V|Vs], ASub, Proj).
    
amgu(Var, Term, ASub, ASub_amgu) :-
    var(Term), !,
    project([Var], ASub, [Var/Val_v]),
    project([Term], ASub, [Term/Val_t]),
    glb_el(Val_t, Val_v, Glb),
    replace_value(ASub, Var, Glb, ASub_r),
    replace_value(ASub_r, Term, Glb, ASub_amgu).
amgu(Var, Term, ASub, ASub_amgu) :-
    !,
    project([Var], ASub, [Var/Val]),
    abstract_term(Term, ASub, AbsTerm), 
    glb_el(AbsTerm, Val, Glb),
    replace_value(ASub, Var, Glb, ASub_amgu).
amgu(_, _, _, '$bottom').

:- push_prolog_flag(multi_arity_warnings, off).
extend(_, '$bottom', _, '$bottom').
extend(_, _, '$bottom', '$bottom'). 
extend(_Sv, Prime, Call, Succ) :-
    sort(Prime, Prime_s),
    sort(Call, Call_s),
    extend_(Prime_s, Call_s, Succ).
:- pop_prolog_flag(multi_arity_warnings).

%%% Prime C Call
extend_([], Call, Call).
extend_([X/Xv|Prime], [Y/Yv|Call], Succ) :-
    X == Y, !,
    glb_el(Xv, Yv, Glb),
    Succ = [X/Glb|Succ_t],
    extend_(Prime, Call, Succ_t).
extend_(Prime, [X|Call], Succ) :-
    !,
    Succ = [X|SuccT], 
    extend_(Prime, Call, SuccT).

topmost(Vs, X, TASub) :-
    var(X), !, 
    top(Vs, TASub).
topmost(Vs, not_provided, TASub) :-!,
    top(Vs, TASub).
topmost(Vs, ASub, TASub) :-
    top_vals(Vs, ASub, TASub).
topmost(_, '$bottom', '$bottom').

top([], []).
top([X|Xs], [X/'$top'|TASub]) :-
    top(Xs, TASub).

top_vals([], ASub, ASub).
top_vals([X|Xs], [Y/_|ASub], TASub) :-
    X == Y, !,
    TASub = [Y/'$top'|TASub_t],
    top_vals(Xs, ASub, TASub_t).
top_vals(Xs, [El|ASub], TASub) :-
    !, TASub = [El|TASub_t],
    top_vals(Xs, ASub, TASub_t).

augment(_, '$bottom', '$bottom').
augment(Vs, L1, L2) :-
    sort(Vs, Vs_s), 
    top(Vs_s, TopASub_vs),
    ord_union(L1, TopASub_vs, L2).

% ---------------------------------------------------------------------------
% Auxiliary predicates

replace_value([X/_|ASub], Var, NVal, ASub_new) :-
    X == Var, !,
    ASub_new = [X/NVal|ASub].
replace_value([X/Xv|ASub], Var, NVal, ASub_new) :-
    !,
    ASub_new = [X/Xv|TASub],
    replace_value(ASub, Var, NVal, TASub).

current_value(ASub, Var, Val) :-
    project([Var], ASub, [Var/Val]).
