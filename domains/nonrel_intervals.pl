:- module(_, [], [assertions,regtypes,basicmodes]).

:- doc(title,"Interval Domain").
:- doc(author, "Isabel Garcia-Contreras").
:- doc(author, "Jose F. Morales").

:- doc(stability, devel).

:- doc(module, "
   A simple @em{intervals} abstract domain (non relational) derived
   from @file{nonrel_base.pl}.

   @begin{note}
     This domain only uses closed intervals as abstractions,
     over-approximating the necessary builtins.
   @end{note}
").

% impl domain
:- include(library(traits/traits_ops)).
:- include(ciaopp(plai/plai_domain)).
:- include(domain(nonrel_base)).
:- dom_def(_, [deriv(nonrel)]).

% ---------------------------------------------------------------------------
:- doc(section, "Value lattice").
% Each variable in the abstract substitution is assigned an abstract
% value with the shape i(Min,Max) that contains the values of the
% interval.

:- prop interval_avalue/1.
:- doc(interval_avalue/1, "Data structure of the substitution that the intervals
    domain keeps for each variable in the program.").
interval_avalue(X) :- bot(X).
interval_avalue(X) :- top(X).
interval_avalue(i(X,Y)) :-
    limit_point(X),
    limit_point(Y).

:- prop limit_point/1.
limit_point(X) :- num(X).
limit_point(X) :- inf(X).
limit_point(X) :- neginf(X).

interval_num(i(X,X)) :- number(X).

interval_avalue_get_min(i(Min, _),Min) :- !.
interval_avalue_get_min(I, Min) :- top(I), !,
    neginf(Min).
interval_avalue_get_min(_, Min) :-
    bot(Min).

interval_avalue_get_max(i(_, Max),Max) :- !.
interval_avalue_get_max(I, Max) :- top(I), !,
    inf(Max).
interval_avalue_get_max(_, Max) :-
    bot(Max).

% ---------------------------------------------------------------------------

:- dom_impl((_ as nonrel), top/1, [noq]).
top('$top').

:- dom_impl((_ as nonrel), bot/1, [noq]).
bot('$bottom').

inf('$inf').
neginf('$ninf').

% TODO: [IG] This looks ugly... This is the abstraction of a free
% variable. It is needed for the predicate "nonrel_empty_entry", that
% obtains the abstraction of a substitution in which all variables are
% unbound (free and unaliased). At this point we do not have an
% abstraction predicate, that would generate the correct value...
:- dom_impl((_ as nonrel), var_elem/1, [noq]).
var_elem('$top').

leq(_, I) :- inf(I), !.
leq(I, _) :- inf(I), !, fail.
leq(NInf, _) :- neginf(NInf), !.
leq(_, NInf) :- neginf(NInf), !, fail.
leq(N1, N2) :-
    N1 =< N2.

:- dom_impl((_ as nonrel), less_or_equal_elem/2, [noq]).
less_or_equal_elem(_,Top) :- top(Top), !.
less_or_equal_elem(Bot,_) :- bot(Bot), !.
less_or_equal_elem(i(N0,N1),i(T0,T1)) :-
    leq(N0, T0),
    leq(N1, T1).

:- dom_impl((_ as nonrel), compute_glb_elem/3, [noq]).
compute_glb_elem(X, Top, X) :- top(Top), !.
compute_glb_elem(Top, X, X) :- top(Top), !.
compute_glb_elem(i(N0,N1), i(T0,T1), i(G0,G1)) :-
    max(N0,T0,G0),
    min(N1,T1,G1),
    leq(G0, G1), !.
compute_glb_elem(_, _, B) :-
    bot(B).

:- dom_impl((_ as nonrel), compute_lub_elem/3, [noq]).
compute_lub_elem(Top, _, Top) :-  top(Top), !.
compute_lub_elem(_, Top, Top) :-  top(Top), !.
compute_lub_elem(Bot, X, X) :-  top(Bot), !.
compute_lub_elem(X, Bot, X) :-  top(Bot), !.
compute_lub_elem(i(N0,N1), i(T0,T1), I) :-
    min(N0,T0,G0),
    max(N1,T1,G1),
    simplify_elem(i(G0,G1), I).

:- dom_impl((_ as nonrel), widen_elem/3, [noq]).
:- pred widen_elem(+V1,+V2,-W) : (interval_avalue(V1), interval_avalue(V2))
    => interval_avalue(W).
widen_elem(Bot, W, W) :- bot(Bot), !.
widen_elem(W, Bot, W) :- bot(Bot), !.
widen_elem(Top, _, Top) :- top(Top), !.
widen_elem(_, Top, Top) :- top(Top), !.
widen_elem(V1, V2, W) :-
    interval_num(V1),
    interval_num(V2), !,
    compute_lub_elem(V1,V2,W).
widen_elem(V1, V2, W) :-
    compute_lub_elem(V1,V2,Lub),
    interval_avalue_get_min(Lub,MinLub),
    interval_avalue_get_max(Lub,MaxLub),
    interval_avalue_get_min(V1,MinV1),
    interval_avalue_get_max(V1,MaxV1),
    interval_avalue_get_min(V2,MinV2),
    interval_avalue_get_max(V2,MaxV2),
    % if the lower bound lub is smaller than any of lower bounds, widen
    ( ( \+ leq(MinV1, MinLub) ; \+ leq(MinV2, MinLub)) ->
          neginf(W0)
    ; W0 = MinLub
    ),
    % if the upper bound lub is bigger than any of the upper bounds, widen
    ( ( \+ leq(MaxLub, MaxV1) ; \+ leq(MaxLub, MaxV2) ) ->
        inf(W1)
    ; W1 = MaxLub
    ),
    simplify_elem(i(W0, W1), W).

simplify_elem(i(NInf, Inf), Top) :-
    neginf(NInf),
    inf(Inf), !,
    top(Top).
simplify_elem(E, E).

max(N0,N1,N0) :- leq(N1, N0), !.
max(_,N1,N1).

max_list(L, X) :-
    neginf(Min),
    max_list_(L, Min, X).

max_list_([], X, X).
max_list_([X|Xs], Max0,Max) :-
    max(X,Max0,Max1),
    max_list_(Xs, Max1, Max).

min(N0,N1,N1) :- leq(N1, N0), !.
min(N0,_,N0).

min_list(L, X) :-
    inf(Max),
    min_list_(L, Max, X).

min_list_([], X, X).
min_list_([X|Xs], Min0, Min) :-
    min(X,Min0,Min1),
    min_list_(Xs, Min1, Min).

add_intervals(i(V0,V1), i(W0,W1), i(N0, N1)) :-
    ( max(V1,W1,Inf), inf(Inf) ->
        N1 = Inf
    ; N1 is V1 + W1
    ),
    ( min(V0,W0,NInf), neginf(NInf) ->
        N0 = NInf
    ; N0 is V0 + W0
    ).

substract_intervals(i(V0,V1), i(W0,W1), i(N0, N1)) :-
    ( max(V1,W1,Inf), inf(Inf) ->
        N1 = Inf
    ; N1 is V1 - W1
    ),
    ( min(V0,W0,NInf), neginf(NInf) ->
        N0 = NInf
    ; N0 is V0 - W0
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
    (bot(V0) ; bot(V1)), !.
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
    bot(NVal).
% divisor contains 0
divide_intervals(_, i(W0,W1), Top) :-
    leq(W0, 0), leq(W1, 0), !,
    top(Top).
divide_intervals(i(V0,V1), i(W0,W1), i(N0,N1)) :-
    div_num(V0,W0,A),
    div_num(V0,W1,B),
    div_num(V1,W0,C),
    div_num(V1,W1,D),
    L = [A,B,C,D],
    min_list(L, N0),
    max_list(L, N1).

div_num(V0, V1, V0) :-
    (bot(V0) ; bot(V1)), !.
div_num(_, 0, Bot) :- !,
    bot(Bot).
div_num('$inf', V, '$inf') :- leq(0, V), !.
div_num('$inf', V, '$ninf') :- leq(V, 0), !.
div_num(_, '$inf', 0) :- !.
div_num('$ninf', V, '$ninf') :- leq(0, V), !.
div_num('$ninf', V, '$inf') :- leq(V, 0), !.
div_num(_, '$ninf', 0) :- !.
div_num(V0, V1, NV) :-
    NV is V0 / V1.

% ---------------------------------------------------------------------------
:- doc(section, "Other domain operations").

:- use_module(library(terms_vars), [varset/2]).
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(_, needs/1, [noq]).
needs(widen).

:- dom_impl(_, init_abstract_domain/1, [noq]).
init_abstract_domain([widen]) :- push_pp_flag(widen,on).

% input interface predicates (to translate properties in assertions to
% their representation in the domain)

% TODO: reuse the syntax of the assertions used in polyhedra?

% :- dom_impl((_ as nonrel), input_interface0/4, [noq]).
% We are going to build a term that will be processed later by calling the body
% of a clause containing builtins equivalent to the constraints found.
input_interface0(constraint(ListCs),_Kind,Struct0,Struct1) :-
    process_list_constraints(ListCs, Struct0, Struct1).

process_list_constraints([], Struct, Struct).
process_list_constraints([C|Cs], Struct, _Struct1) :-
    varset(C,Vs),
    top(T),
    nonrel_create_asub(Vs,T,_ASub),
    % TODO: use call_to_success_builtin and abs operate to process the constraints.
    process_list_constraints(Cs, Struct, _Struct1).

% ---------------------------------------------------------------------------
:- doc(section, "amgu and builtin operations").

:- dom_impl((_ as nonrel), amgu/4, [noq]). % TODO: make nonrel_base call the domain operation instead?
:- dom_impl(_, amgu/4, [noq]).
amgu(T1,T2,ASub0,NASub) :- var(T1), var(T2), !,
    nonrel_get_value_asub(ASub0,T1,Value1),
    nonrel_get_value_asub(ASub0,T2,Value2),
    compute_glb_elem(Value1,Value2,Glb), % TODO: missing bottom case!
    nonrel_replace_value_asub(ASub0,T1,Glb,ASub1),
    nonrel_replace_value_asub(ASub1,T2,Glb,NASub).
amgu(T1,T2,ASub0,NASub) :- var(T2), !,
    amgu(T2,T1,ASub0,NASub).
amgu(T1,T2,ASub0,NASub) :- var(T1), !,
    abstract_term(T2,ASub0,NVal),
    nonrel_replace_value_asub(ASub0,T1,NVal,NASub).
amgu(T1,T2,ASub0,NASub) :-
    functor(T1,F,A),
    functor(T2,F,A), !,
    T1 =.. [F|Args1],
    T2 =.. [F|Args2],
    amgu_args(Args1,Args2,ASub0, NASub).
amgu(_T1,_T2,_ASub1,ASub2) :-
    bot(ASub2).

amgu_args([],[],ASub, ASub).
amgu_args([A1|As1],[A2|As2],ASub0, NASub) :-
    amgu(A1,A2,ASub0,ASub1),
    amgu_args(As1,As2,ASub1, NASub).

:- pred abstract_term(+T,+ASubT,-ASub) #"Abstracts term @var{T} possibly
    using information in the abstract substitution @var{ASubT} that describes a
      current abstract state for term T.".
% if it is a number, generate the interval
abstract_term(X,_ASub,i(X,X)) :-
    number(X), !. % TODO: only integers?
% if it is a variable, return the abstraction in the substitution
abstract_term(Var,ASub,Value) :-  % This is generic
    nonrel_get_value_asub(ASub, Var, Value), !.
abstract_term(_,_,Top) :-
    top(Top).

:- dom_impl((_ as nonrel), special_builtin0/4, [noq]).
% Note: the following are specific for intervals domain 
% TODO: unbound Type and Condvars? (JF)
special_builtin0('>/2',_,_,_).
special_builtin0('>=/2',_,_,_).
special_builtin0('</2',_,_,_).
special_builtin0('=</2',_,_,_).
special_builtin0('is/2',_,_,_).
% special_builtin0('nnegint/1',_,_,_).

:- dom_impl((_ as nonrel), call_to_success_builtin0/6, [noq]).
call_to_success_builtin0('=</2','=<'(X,Y),_Sv,Call,_Proj,Succ):-
    abstract_term(X,Call,ValX),
    abstract_term(Y,Call,ValY),
    compute_glb_elem(ValX,ValY,Glb),
    ( bot(Glb) ->    % intervals are disjoint
        ( less_or_equal_elem(ValX, ValY) ->
            Succ = Call
        ; Succ = Glb
        )
    ; % TODO: This could be written easier with functional notation
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
call_to_success_builtin0('>=/2','>='(X,Y),Sv,Call,Proj,Succ):-
    call_to_success_builtin0('=</2','=<'(Y,X),Sv,Call,Proj,Succ).
% For this example domain we over-approximate > and < as >= and =< respectively
call_to_success_builtin0('>/2','>'(X,Y),Sv,Call,Proj,Succ):-
    call_to_success_builtin0('>=/2','>='(X,Y),Sv,Call,Proj,Succ).
call_to_success_builtin0('</2','<'(X,Y),Sv,Call,Proj,Succ):-
    call_to_success_builtin0('=</2','=<'(X,Y),Sv,Call,Proj,Succ).
%
call_to_success_builtin0('is/2','is'(X,Y),_Sv,Call,_Proj,Succ):-
    ( abs_arith_eval(Y,Call,NVal0) -> true ; top(NVal0) ),
    nonrel_get_value_asub(Call,X,Val0),
    compute_glb_elem(NVal0,Val0,NVal),
    nonrel_replace_value_asub(Call,X,NVal,Succ).

% TODO: be more precise when arith is unknown (e.g., it can be num,int,flt,etc.)
abs_arith_eval(X, _Call, NVal) :- number(X), !,
    NVal = i(X,X).
abs_arith_eval(X, Call, Val) :- var(X), !,
    nonrel_get_value_asub(Call, X, Val).
abs_arith_eval(+(X,Y), Call, NVal) :- !,
    abs_arith_eval(X,Call,NXVal),
    abs_arith_eval(Y,Call,NYVal),
    add_intervals(NXVal, NYVal, NVal).
abs_arith_eval(-(X,Y), Call, NVal) :- !,
    abs_arith_eval(X,Call,NXVal),
    abs_arith_eval(Y,Call,NYVal),
    substract_intervals(NXVal, NYVal, NVal).
abs_arith_eval(*(X,Y), Call, NVal) :- !,
    abs_arith_eval(X,Call,NXVal),
    abs_arith_eval(Y,Call,NYVal),
    multiply_intervals(NXVal, NYVal, NVal).
abs_arith_eval(/(X,Y), Call, NVal) :- !,
    abs_arith_eval(X,Call,NXVal),
    abs_arith_eval(Y,Call,NYVal),
    divide_intervals(NXVal, NYVal, NVal).

% ---------------------------------------------------------------------------
:- doc(section, "Tests").

:- test amgu(T1,T2,ASub0,NASub)
    : (T1 = p(X), T2 = p(Y), ASub0 = [X/i(3,3), Y/'$top'])
    => (NASub = [X/i(3,3),Y/i(3,3)]).
:- test amgu(T1,T2,ASub0,NASub)
    : (T1 = p(3,Y), T2 = p(X,4), ASub0 = [X/'$top', Y/'$top'])
    => (NASub = [X/i(3,3),Y/i(4,4)]).

:- test widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = '$bottom' )
    =>( W = i(2,3) ).
:- test widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = i(2,3) )
    =>( W = i(2,3) ). 
:- test widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = i(2,4) )
    =>( W = i(2,'$inf') ).
:- test widen_elem(V1, V2, W)
    : ( V1 = i(2,3), V2 = i(1,3) )
    =>( W = i('$ninf',3) ).
:- test widen_elem(V1, V2, W)
    : ( V1 = i(2,4), V2 = i(1,3) )
    =>( W = '$top' ).
:- test widen_elem(V1, V2, W)
    : ( V1 = i(2,2), V2 = i(4,4) )
    =>( W = i(2,4) ).
% % TODO: this test should not work (not implemented)
% :- test widen_elem(V1, V2, W)
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
% domain. % TODO: keep it? AbsInt param was missing (JFMC)
:- test nonrel_call_to_success_builtin(_AbsInt,SgKey,Sg,Sv,Call,Proj,Succ) 
    : (Sg = '<'(A,B), Sv = [A,B], Call = [A/i(0,0),B/'$top',C/'$top',D/'$top',E/'$top'],
       Proj = [A/i(0,0),B/'$top'])
    => (Succ = [A/i(0,0),B/i(0,'$inf'),C/'$top',D/'$top',E/'$top'] ).
