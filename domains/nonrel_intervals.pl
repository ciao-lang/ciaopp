:- module(_, [], [assertions,regtypes,basicmodes]).

:- doc(title,"Interval Domain (Non Relational)").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(stability, devel).

:- doc(module, "
   A simple @em{intervals} abstract domain derived from @file{nonrel_base.pl}.

   @begin{note}
     This domain only uses closed intervals as abstractions,
     over-approximating the necessary builtins.
   @end{note}
").

:- include(.(nonrel_base)). % (derive nonrel domain)

% ---------------------------------------------------------------------------
% impl domain

:- include(ciaopp(plai/plai_domain)).
:- dom_def(nonrel_intervals).

% (operations expected by nonrel_base that nonrel_intervals must implement)
% E.g., nonrel_init_abstract_domain(nonrel_intervals, PushedFlags) :- !, nonrel_intervals_init_abstract_domain0(PushedFlags).
%
:- dom_deriv_hook(nonrel, init_abstract_domain(PushedFlags), nonrel_intervals, init_abstract_domain0(PushedFlags)).
:- dom_deriv_hook(nonrel, top(X), nonrel_intervals, top(X)).
:- dom_deriv_hook(nonrel, bot(X), nonrel_intervals, bot(X)).
:- dom_deriv_hook(nonrel, var(X), nonrel_intervals, var(X)).
:- dom_deriv_hook(nonrel, amgu(T1,T2,ASub0,NASub), nonrel_intervals, amgu0(T1,T2,ASub0,NASub)).
:- dom_deriv_hook(nonrel, less_or_equal_elem(E1,E2), nonrel_intervals, less_or_equal_elem(E1,E2)).
:- dom_deriv_hook(nonrel, compute_glb_elem(E1,E2,EG), nonrel_intervals, compute_glb_elem(E1,E2,EG)).
:- dom_deriv_hook(nonrel, compute_lub_elem(E1,E2,EL), nonrel_intervals, compute_lub_elem(E1,E2,EL)).
:- dom_deriv_hook(nonrel, widen_elem(E1,E2,EW), nonrel_intervals, widen_elem(E1,E2,EW)).
% :- dom_deriv_hook(nonrel, input_interface(Prop,Kind,Struct0,Struct1), nonrel_intervals, input_interface0(Prop,Kind,Struct0,Struct1)).
:- dom_deriv_hook(nonrel, special_builtin0(SgKey,Sg,Type,Condvars), nonrel_intervals, special_builtin0(SgKey,Sg,Type,Condvars)).
:- dom_deriv_hook(nonrel, call_to_success_builtin0(SgKey,Sg,Sv,Call,Proj,Succ), nonrel_intervals, call_to_success_builtin0(SgKey,Sg,Sv,Call,Proj,Succ)).

:- dom_impl(nonrel_intervals, needs/1).
nonrel_intervals_needs(widen).

% (operations expected by a domain that nonrel_intervals takes from nonrel)
% E.g., :- dom_impl(nonrel_intervals, init_abstract_domain/1).
%       nonrel_intervals_init_abstract_domain(PushedFlags) :- nonrel_init_abstract_domain(nonrel_intervals, PushedFlags).
:- dom_impl_deriv(nonrel_intervals, init_abstract_domain(PushedFlags), nonrel, init_abstract_domain(nonrel_intervals, PushedFlags)).
:- dom_impl_deriv(nonrel_intervals, amgu(Sg,Head,ASub,NewASub), nonrel, amgu(nonrel_intervals,Sg,Head,ASub,NewASub)).
:- dom_impl_deriv(nonrel_intervals, call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo), nonrel, call_to_entry(nonrel_intervals,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)).
:- dom_impl_deriv(nonrel_intervals, exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime), nonrel, exit_to_prime(nonrel_intervals,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)).
:- dom_impl_deriv(nonrel_intervals, project(_Sg,Vars,_HvFv,ASub,Proj), nonrel, project(ASub,Vars,Proj)).
:- dom_impl_deriv(nonrel_intervals, widencall(Prime0,Prime1,NewPrime), nonrel, widencall(nonrel_intervals,Prime0,Prime1,NewPrime)).
:- dom_impl_deriv(nonrel_intervals, widen(Prime0,Prime1,NewPrime), nonrel, widen(nonrel_intervals,Prime0,Prime1,NewPrime)).
:- dom_impl_deriv(nonrel_intervals, compute_lub(ListASub,LubASub), nonrel, compute_lub(nonrel_intervals,ListASub,LubASub)).
:- dom_impl_deriv(nonrel_intervals, identical_abstract(ASub1, ASub2), nonrel, identical_abstract(ASub1, ASub2)).
:- dom_impl_deriv(nonrel_intervals, abs_sort(ASub,ASub_s), nonrel, abs_sort(ASub,ASub_s)).
:- dom_impl_deriv(nonrel_intervals, extend(_Sg,Prime,Sv,Call,Succ), nonrel, extend(nonrel_intervals,Prime,Sv,Call,Succ)).
:- dom_impl_deriv(nonrel_intervals, less_or_equal(ASub0,ASub1), nonrel, less_or_equal(nonrel_intervals,ASub0,ASub1)).
:- dom_impl_deriv(nonrel_intervals, glb(ASub0,ASub1,ASub), nonrel, glb(nonrel_intervals,ASub0,ASub1,ASub)).
:- dom_impl_deriv(nonrel_intervals, call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ), nonrel, call_to_success_fact(nonrel_intervals,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)).
:- dom_impl_deriv(nonrel_intervals, special_builtin(SgKey,Sg,_Subgoal,Type,Condvars), nonrel, special_builtin(nonrel_intervals,SgKey,Sg,Type,Condvars)).
:- dom_impl_deriv(nonrel_intervals, success_builtin(Type,_Sv_uns,Condvars,_HvFv_u,Call,Succ), nonrel, success_builtin(nonrel_intervals,Type,Condvars,Call,Succ)).
:- dom_impl_deriv(nonrel_intervals, call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ), nonrel, call_to_success_builtin(nonrel_intervals,SgKey,Sg,Sv,Call,Proj,Succ)).
:- dom_impl_deriv(nonrel_intervals, input_interface(InputUser,Kind,Struct0,Struct1), nonrel, input_interface(nonrel_intervals,InputUser,Kind,Struct0,Struct1)).
:- dom_impl_deriv(nonrel_intervals, input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub), nonrel, input_user_interface(nonrel_intervals,InputUser,Qv,ASub)).
:- dom_impl_deriv(nonrel_intervals, asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps), nonrel, asub_to_native(nonrel_intervals,ASub,Qv,OutFlag,OutputUser,Comps)).
:- dom_impl_deriv(nonrel_intervals, unknown_call(Sg,Vars,Call,Succ), nonrel, unknown_call(nonrel_intervals,Sg,Vars,Call,Succ)).
:- dom_impl_deriv(nonrel_intervals, unknown_entry(Sg,Qv,Call), nonrel, unknown_entry(nonrel_intervals,Sg,Qv,Call)).
:- dom_impl_deriv(nonrel_intervals, empty_entry(Sg,Qv,Call), nonrel, unknown_entry(nonrel_intervals,Sg,Qv,Call)).

% ---------------------------------------------------------------------------

:- use_module(library(terms_vars), [varset/2]).
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

nonrel_intervals_init_abstract_domain0([widen]) :- push_pp_flag(widen,on).

:- prop interval_avalue/1.
:- doc(interval_avalue/1, "Data structure of the substitution that the intervals
    domain keeps for each variable in the program.").
interval_avalue(X) :- nonrel_intervals_bot(X).
interval_avalue(X) :- nonrel_intervals_top(X).
interval_avalue(i(X,Y)) :-
    limit_point(X),
    limit_point(Y).

:- prop limit_point/1.
limit_point(X) :-
    num(X).
limit_point(X) :-
    nonrel_inf(X).
limit_point(X) :-
    nonrel_neginf(X).

interval_num(i(X,X)) :- number(X).

interval_avalue_get_min(i(Min, _),Min) :- !.
interval_avalue_get_min(I, Min) :-
    nonrel_intervals_top(I), !,
    nonrel_neginf(Min).
interval_avalue_get_min(_, Min) :-
    nonrel_intervals_bot(Min).

interval_avalue_get_max(i(_, Max),Max) :- !.
interval_avalue_get_max(I, Max) :-
    nonrel_intervals_top(I), !,
    nonrel_inf(Max).
interval_avalue_get_max(_, Max) :-
    nonrel_intervals_bot(Max).

% All the predicates in this section whose name starts with "nonrel" need to be
% implemented when developing a new non relational domain.

% In this example an intervals domain is implemented. Each variable in the
% abstract substitution is assigned an abstract value with the shape i(Min,Max)
% that contains the values of the interval.

nonrel_intervals_top('$top').
nonrel_intervals_bot('$bottom').

nonrel_inf('$inf').
nonrel_neginf('$ninf').

% [IG] This looks ugly... This is the abstraction of a free variable. It is
% needed for the predicate "nonrel_empty_entry", that obtains the abstraction
% of a substitution in which all variables are unbound (free and unaliased). At
% this point we do not have an abstraction predicate, that would generate the
% correct value....
nonrel_intervals_var('$top').

nonrel_intervals_amgu0(T1,T2,ASub0,NASub) :-
    var(T1),var(T2), !,
    nonrel_get_value_asub(ASub0,T1,Value1),
    nonrel_get_value_asub(ASub0,T2,Value2),
    nonrel_intervals_compute_glb_elem(Value1,Value2,Glb), % TODO: missing bottom case!
    nonrel_replace_value_asub(ASub0,T1,Glb,ASub1),
    nonrel_replace_value_asub(ASub1,T2,Glb,NASub).
nonrel_intervals_amgu0(T1,T2,ASub0,NASub) :-
    var(T2), !,
    nonrel_intervals_amgu0(T2,T1,ASub0,NASub).
nonrel_intervals_amgu0(T1,T2,ASub0,NASub) :-
    var(T1), !,
    nonrel_intervals_abstract_term(T2,ASub0,NVal),
    nonrel_replace_value_asub(ASub0,T1,NVal,NASub).
nonrel_intervals_amgu0(T1,T2,ASub0,NASub) :-
    functor(T1,F,A),
    functor(T2,F,A), !,
    T1 =.. [F|Args1],
    T2 =.. [F|Args2],
    nonrel_intervals_amgu_args(Args1,Args2,ASub0, NASub).
nonrel_intervals_amgu0(_T1,_T2,_ASub1,ASub2) :-
    nonrel_intervals_bot(ASub2).

nonrel_intervals_amgu_args([],[],ASub, ASub).
nonrel_intervals_amgu_args([A1|As1],[A2|As2],ASub0, NASub) :-
    nonrel_intervals_amgu0(A1,A2,ASub0,ASub1),
    nonrel_intervals_amgu_args(As1,As2,ASub1, NASub).

:- pred nonrel_intervals_abstract_term(+T,+ASubT,-ASub) #"Abstracts term @var{T} possibly
    using information in the abstract substitution @var{ASubT} that describes a
      current abstract state for term T.".
% if it is a number, generate the interval
nonrel_intervals_abstract_term(X,_ASub,i(X,X)) :-
    num(X), !.
% if it is a variable, return the abstraction in the substitution
nonrel_intervals_abstract_term(Var,ASub,Value) :-  % This is generic
       nonrel_get_value_asub(ASub, Var, Value), !.
nonrel_intervals_abstract_term(_,_,Top) :-
    nonrel_intervals_top(Top).

leq(_, I) :- nonrel_inf(I), !.
leq(I, _) :- nonrel_inf(I), !, fail.
leq(NInf, _) :- nonrel_neginf(NInf), !.
leq(_, NInf) :- nonrel_neginf(NInf), !, fail.
leq(N1, N2) :-
    N1 =< N2.

nonrel_intervals_less_or_equal_elem(_,Top) :- nonrel_intervals_top(Top), !.
nonrel_intervals_less_or_equal_elem(Bot,_) :- nonrel_intervals_bot(Bot), !.
nonrel_intervals_less_or_equal_elem(i(N0,N1),i(T0,T1)) :-
    leq(N0, T0),
    leq(N1, T1).

nonrel_intervals_compute_glb_elem(X, Top, X) :- nonrel_intervals_top(Top), !.
nonrel_intervals_compute_glb_elem(Top, X, X) :- nonrel_intervals_top(Top), !.
nonrel_intervals_compute_glb_elem(i(N0,N1), i(T0,T1), i(G0,G1)) :-
    max(N0,T0,G0),
    min(N1,T1,G1),
    leq(G0, G1), !.
nonrel_intervals_compute_glb_elem(_, _, B) :-
    nonrel_intervals_bot(B).

nonrel_intervals_compute_lub_elem(Top, _, Top) :-  nonrel_intervals_top(Top), !.
nonrel_intervals_compute_lub_elem(_, Top, Top) :-  nonrel_intervals_top(Top), !.
nonrel_intervals_compute_lub_elem(Bot, X, X) :-  nonrel_intervals_top(Bot), !.
nonrel_intervals_compute_lub_elem(X, Bot, X) :-  nonrel_intervals_top(Bot), !.
nonrel_intervals_compute_lub_elem(i(N0,N1), i(T0,T1), I) :-
    min(N0,T0,G0),
    max(N1,T1,G1),
    simplify_elem(i(G0,G1), I).

:- pred nonrel_intervals_widen_elem(+V1,+V2,-W) : (interval_avalue(V1), interval_avalue(V2))
    => interval_avalue(W).
nonrel_intervals_widen_elem(Bot, W, W) :-
    nonrel_intervals_bot(Bot), !.
nonrel_intervals_widen_elem(W, Bot, W) :-
    nonrel_intervals_bot(Bot), !.
nonrel_intervals_widen_elem(Top, _, Top) :-
    nonrel_intervals_top(Top), !.
nonrel_intervals_widen_elem(_, Top, Top) :-
    nonrel_intervals_top(Top), !.
nonrel_intervals_widen_elem(V1, V2, W) :-
    interval_num(V1),
    interval_num(V2), !,
    nonrel_intervals_compute_lub_elem(V1,V2,W).
nonrel_intervals_widen_elem(V1, V2, W) :-
    nonrel_intervals_compute_lub_elem(V1,V2,Lub),
    interval_avalue_get_min(Lub,MinLub),
    interval_avalue_get_max(Lub,MaxLub),
    interval_avalue_get_min(V1,MinV1),
    interval_avalue_get_max(V1,MaxV1),
    interval_avalue_get_min(V2,MinV2),
    interval_avalue_get_max(V2,MaxV2),
    % if the lower bound lub is smaller than any of lower bounds, widen
    ( ( \+ leq(MinV1, MinLub) ; \+ leq(MinV2, MinLub)) ->
          nonrel_neginf(W0)
    ;
        W0 = MinLub
    ),
    % if the upper bound lub is bigger than any of the upper bounds, widen
    ( ( \+ leq(MaxLub, MaxV1) ; \+ leq(MaxLub, MaxV2) ) ->
        nonrel_inf(W1)
    ;
        W1 = MaxLub
    ),
    simplify_elem(i(W0, W1), W).

simplify_elem(i(NInf, Inf), Top) :-
    nonrel_neginf(NInf),
    nonrel_inf(Inf), !,
    nonrel_intervals_top(Top).
simplify_elem(E, E).

max(N0,N1,N0) :- leq(N1, N0), !.
max(_,N1,N1).

max_list(L, X) :-
    nonrel_neginf(Min),
    max_list_(L, Min, X).

max_list_([], X, X).
max_list_([X|Xs], Max0,Max) :-
    max(X,Max0,Max1),
    max_list_(Xs, Max1, Max).

min(N0,N1,N1) :- leq(N1, N0), !.
min(N0,_,N0).

min_list(L, X) :-
    nonrel_inf(Max),
    min_list_(L, Max, X).

min_list_([], X, X).
min_list_([X|Xs], Min0, Min) :-
    min(X,Min0,Min1),
    min_list_(Xs, Min1, Min).

add_intervals(i(V0,V1), i(W0,W1), i(N0, N1)) :-
    ( max(V1,W1,Inf), nonrel_inf(Inf) ->
        N1 = Inf
    ;
        N1 is V1 + W1
    ),
    ( min(V0,W0,NInf), nonrel_neginf(NInf) ->
        N0 = NInf
    ;
        N0 is V0 + W0
    ).

substract_intervals(i(V0,V1), i(W0,W1), i(N0, N1)) :-
    ( max(V1,W1,Inf), nonrel_inf(Inf) ->
        N1 = Inf
    ;
        N1 is V1 - W1
    ),
    ( min(V0,W0,NInf), nonrel_neginf(NInf) ->
        N0 = NInf
    ;
        N0 is V0 - W0
    ).

multiply_intervals(i(V0,V1), i(W0,W1), i(N0, N1)) :-
    mult_num(V0,W0,A),
    mult_num(V0,W1,B),
    mult_num(V1,W0,C),
    mult_num(V1,W1,D),
    L = [A,B,C,D],
    min_list(L, N0),
    max_list(L, N1).

mult_num(V0, V1, V0) :-
    (nonrel_intervals_bot(V0) ; nonrel_intervals_bot(V1)), !.
mult_num(V0, V1, 0) :-
    (V0 = 0 ; V1 = 0), !.
mult_num('$inf', V, '$inf') :- leq(0, V), !.
mult_num('$inf', V, '$ninf') :- leq(V, 0), !.
mult_num(V, '$inf', '$inf') :- leq(0, V), !.
mult_num(V, '$inf', '$ninf') :- leq(V, 0), !.
mult_num('$ninf', V, '$ninf') :- leq(0, V), !.
mult_num('$ninf', V, '$inf') :- leq(V, 0), !.
mult_num(V, '$ninf', '$ninf') :- leq(0, V), !.
mult_num(V, '$ninf', '$inf') :- leq(V, 0), !.
mult_num(V0, V1, NV) :-
    NV is V0 * V1.
% divisor is 0
divide_intervals(_, i(0,0), NVal) :- !,
    nonrel_intervals_bot(NVal).
% divisor contains 0
divide_intervals(_, i(W0,W1), Top) :-
    leq(W0, 0), leq(W1, 0), !,
    nonrel_intervals_top(Top).
divide_intervals(i(V0,V1), i(W0,W1), i(N0,N1)) :-
    div_num(V0,W0,A),
    div_num(V0,W1,B),
    div_num(V1,W0,C),
    div_num(V1,W1,D),
    L = [A,B,C,D],
    min_list(L, N0),
    max_list(L, N1).

div_num(V0, V1, V0) :-
    (nonrel_intervals_bot(V0) ; nonrel_intervals_bot(V1)), !.
div_num(_, 0, Bot) :- !,
    nonrel_intervals_bot(Bot).
div_num('$inf', V, '$inf') :- leq(0, V), !.
div_num('$inf', V, '$ninf') :- leq(V, 0), !.
div_num(_, '$inf', 0) :- !.
div_num('$ninf', V, '$ninf') :- leq(0, V), !.
div_num('$ninf', V, '$inf') :- leq(V, 0), !.
div_num(_, '$ninf', 0) :- !.
div_num(V0, V1, NV) :-
    NV is V0 / V1.

% input interface predicates (to translate properties in assertions to their
% representation in the domain)

% For the example of the intervals domain we could reuse the syntax of the
% assertions used in polyhedra

% We are going to build a term that will be processed later by calling the body
% of a clause containing builtins equivalent to the constraints found.
nonrel_intervals_input_interface0(constraint(ListCs),_Kind,Struct0,Struct1) :-
    process_list_constraints(ListCs, Struct0, Struct1).

process_list_constraints([], Struct, Struct).
process_list_constraints([C|Cs], Struct, _Struct1) :-
    varset(C,Vs),
    nonrel_intervals_top(T),
    nonrel_create_asub(Vs,T,_ASub),
    % TODO: use call_to_success_builtin and abs operate to process the constraints.
    process_list_constraints(Cs, Struct, _Struct1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(section, "Builtin operations").

% Note: the following are specific for intervals domain 
% TODO: unbound Type and Condvars? (JF)
nonrel_intervals_special_builtin0('>/2',_,_,_).
nonrel_intervals_special_builtin0('>=/2',_,_,_).
nonrel_intervals_special_builtin0('</2',_,_,_).
nonrel_intervals_special_builtin0('=</2',_,_,_).
nonrel_intervals_special_builtin0('is/2',_,_,_).
% nonrel_intervals_special_builtin0('nnegint/1',_,_,_).

nonrel_intervals_call_to_success_builtin0('=</2','=<'(X,Y),_Sv,Call,_Proj,Succ):-
    nonrel_intervals_abstract_term(X,Call,ValX),
    nonrel_intervals_abstract_term(Y,Call,ValY),
    nonrel_intervals_compute_glb_elem(ValX,ValY,Glb),
    ( nonrel_intervals_bot(Glb) ->    % intervals are disjoint
        ( nonrel_intervals_less_or_equal_elem(ValX, ValY) ->
            Succ = Call
        ;  
            Succ = Glb
        )
    ;
        % TODO: This could be written easier with functional notation
        interval_avalue_get_max(ValX,MaxX),
        interval_avalue_get_max(ValY,MaxY),
        interval_avalue_get_min(ValX,MinX),
        interval_avalue_get_min(ValY,MinY),
        min(MaxX,MaxY,X1),
        max(MinX, MinY, Y0),
        NValX0 = i(MinX, X1),
        NValY0 = i(Y0, MaxY),
        simplify_elem(NValX0, NValX),
        simplify_elem(NValY0, NValY),
        nonrel_replace_value_asub(Call,X,NValX,Succ0),
        nonrel_replace_value_asub(Succ0,Y,NValY,Succ)
    ).
nonrel_intervals_call_to_success_builtin0('>=/2','>='(X,Y),Sv,Call,Proj,Succ):-
    nonrel_intervals_call_to_success_builtin0('=</2','=<'(Y,X),Sv,Call,Proj,Succ).
% For this example domain we over-approximate > and < as >= and =< respectively
nonrel_intervals_call_to_success_builtin0('>/2','>'(X,Y),Sv,Call,Proj,Succ):-
    nonrel_intervals_call_to_success_builtin0('>=/2','>='(X,Y),Sv,Call,Proj,Succ).
nonrel_intervals_call_to_success_builtin0('</2','<'(X,Y),Sv,Call,Proj,Succ):-
    nonrel_intervals_call_to_success_builtin0('=</2','=<'(X,Y),Sv,Call,Proj,Succ).
%
nonrel_intervals_call_to_success_builtin0('is/2','is'(X,Y),_Sv,Call,_Proj,Succ):-
    ( nonrel_is_abs_operate(Y,Call,NVal0) ->
        nonrel_get_value_asub(Call,X,Val0),
        nonrel_intervals_compute_glb_elem(NVal0,Val0,NVal),
        nonrel_replace_value_asub(Call,X,NVal,Succ)
    ;
        nonrel_intervals_amgu0(X,Y,Call,Succ)
    ).

nonrel_is_abs_operate(X, _Call, NVal) :-
    num(X), !,
    NVal = i(X,X).
nonrel_is_abs_operate(X, Call, Val) :-
    var(X), !,
    nonrel_get_value_asub(Call, X, Val).
nonrel_is_abs_operate(+(X,Y), Call, NVal) :-
    nonrel_is_abs_operate(X,Call,NXVal),
    nonrel_is_abs_operate(Y,Call,NYVal),
    add_intervals(NXVal, NYVal, NVal).
nonrel_is_abs_operate(-(X,Y), Call, NVal) :-
    nonrel_is_abs_operate(X,Call,NXVal),
    nonrel_is_abs_operate(Y,Call,NYVal),
    substract_intervals(NXVal, NYVal, NVal).
nonrel_is_abs_operate(*(X,Y), Call, NVal) :-
    nonrel_is_abs_operate(X,Call,NXVal),
    nonrel_is_abs_operate(Y,Call,NYVal),
    multiply_intervals(NXVal, NYVal, NVal).
nonrel_is_abs_operate(/(X,Y), Call, NVal) :-
    nonrel_is_abs_operate(X,Call,NXVal),
    nonrel_is_abs_operate(Y,Call,NYVal),
    divide_intervals(NXVal, NYVal, NVal).

% ---------------------------------------------------------------------------
:- doc(section, "Tests").

:- test nonrel_intervals_amgu0(T1,T2,ASub0,NASub)
    : (T1 = p(X), T2 = p(Y), ASub0 = [X/i(3,3), Y/'$top'])
    => (NASub = [X/i(3,3),Y/i(3,3)]).
:- test nonrel_intervals_amgu0(T1,T2,ASub0,NASub)
    : (T1 = p(3,Y), T2 = p(X,4), ASub0 = [X/'$top', Y/'$top'])
    => (NASub = [X/i(3,3),Y/i(4,4)]).

:- test nonrel_intervals_widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = '$bottom' )
    =>( W = i(2,3) ).
:- test nonrel_intervals_widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = i(2,3) )
    =>( W = i(2,3) ). 
:- test nonrel_intervals_widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = i(2,4) )
    =>( W = i(2,'$inf') ).
:- test nonrel_intervals_widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = i(1,3) )
    =>( W = i('$ninf',3) ).
:- test nonrel_intervals_widen_elem(V1, V2, W)
    : ( V1 = i(2,4), V2 = i(1,3) )
    =>( W = '$top' ).
:- test nonrel_intervals_widen_elem(V1, V2, W)
    : ( V1 = i(2,2), V2 = i(4,4) )
    =>( W = i(2,4) ).
% % TODO: this test should not work (not implemented)
% :- test nonrel_intervals_widen_elem(V1, V2, W)
%         : ( V1 = i(1,2), V2 = i(2,3) )
%         =>( W = i(1,'$inf') ).
% we go to -inf/inf i

:- test divide_intervals(A,B,C)
    : (A = i('$ninf', 3), B = i(4,3) )
    => (C =  i('$ninf',1.0)).
:- test divide_intervals(A,B,C)
    : (A = i('$ninf', 3), B = i(-2,3) )
    => (C =  i('$ninf','$inf')).
:- test divide_intervals(A,B,C)
    : (A = i(-4, 6), B = i(1,'$inf') )
    => (C =  i(-4.0,6.0)).
:- test divide_intervals(A,B,C)
    : (A = i('$ninf', -4), B = i(1,'$inf') )
    => (C = i('$ninf', 0)).
:- test divide_intervals(A,B,C)
    : (A = i(-4, '$inf'), B = i(1,'$inf') )
       => (C = i(-4.0,'$inf')).

% This test depends on how abstract substitutions are represented in the nonrel
% domain.
:- test nonrel_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ) 
    : (Sg = '<'(A,B), Sv = [A,B], Call = [A/i(0,0),B/'$top',C/'$top',D/'$top',E/'$top'],
       Proj = [A/i(0,0),B/'$top'])
    => (Succ = [A/i(0,0),B/i(0,'$inf'),C/'$top',D/'$top',E/'$top'] ).
