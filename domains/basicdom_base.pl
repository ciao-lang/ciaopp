%% (this is an included file)

% TODO:[merge] rename snippet as 'basicdom_base_doc' (like nonrel_base_doc.pl)

% ---------------------------------------------------------------------------
% (dependencies)

:- use_package(assertions).
:- use_package(modes).
:- use_package(regtypes).

:- use_module(library(sort), [sort/2]).
:- use_module(engine(basic_props), [list/1]). 
:- use_module(library(terms_check), [variant/2]).
:- use_module(domain(s_eqs), [peel/4]).

:- include(ciaopp(plai/plai_domain)).

% ---------------------------------------------------------------------------
%! # Required predicates for this trait
%
% These are the predicates that must be defined by the user in order
% to implement this domain:

:- dom_impl(_, less_or_equal/2, [noq]).
:- dom_impl(_, input_interface/4, [noq]).
:- dom_impl(_, input_user_interface/5, [noq]).
:- dom_impl(_, asub_to_native/5, [noq]).
:- dom_impl(_, needs/1, [noq]).
:- dom_impl(_, widen/3, [noq]). 

:- discontiguous(asub/1).
:- discontiguous(project/3).
:- discontiguous(augment/3).
:- discontiguous(extend/4).
:- discontiguous(amgu/3).
:- discontiguous(less_or_equal/2).
:- discontiguous(lub/3).
:- discontiguous(widen/3).
:- discontiguous(topmost/3).
:- discontiguous(known_builtin/1).
:- discontiguous(asub_to_native/5).
:- discontiguous(needs/1).
:- discontiguous(input_user_interface/5).

% ===========================================================================
%! # plai_domain implementation

% ---------------------------------------------------------------------------

:- dom_impl(_, init_abstract_domain/1, [noq]).
init_abstract_domain(_).

% ---------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom', '$bottom').
abs_sort(Elem, SortedElem) :-
    list(Elem), !,
    sort(Elem, SortedElem).
abs_sort(Elem, SortedElem) :-
    functor(Elem, _, _),!,
    Elem =.. [F|Ts],
    abs_sort_it(Ts, Ts_s),
    SortedElem =.. [F|Ts_s].
abs_sort(Elem, Elem) :- !.

abs_sort_it([], []).
abs_sort_it([X|Xs], [X_s|SXs]) :-
    abs_sort(X, X_s),
    abs_sort_it(Xs, SXs).

% ---------------------------------------------------------------------------

:- dom_impl(_, identical_abstract/2, [noq]).

identical_abstract('$bottom', '$bottom').
identical_abstract(ASub1, ASub2) :-
    ASub1 == ASub2.
identical_abstract(ASub1, ASub2) :-
    less_or_equal(ASub1, ASub2),
    less_or_equal(ASub2, ASub1).

% ---------------------------------------------------------------------------
%! ## Call to entry

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv, Sg, Hv, Head, _K, Fv, Proj, Entry, ExtraInfo) :-
    variant(Sg, Head), !, %% If this holds is just a matter of renaming
    ExtraInfo = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj)),
    Head = NewTerm,
    project(not_provided_Sg,Hv,not_provided_HvFv_u,NewProj,NewProj1),
    abs_sort(NewProj1, NewProj2),
    augment(Fv, NewProj2, Entry).
call_to_entry(Sv, Sg, [], Head, _K, [], Proj, Entry, Unifiers) :-
    peel(Head, Sg, Unifiers, []),
    abstract_unif(Unifiers, Proj, Entry0), !,
    project(Sg, Sv, not_provided_HvFv, Entry0, Entry1),
    abs_sort(Entry1, Entry).
call_to_entry(_Sv, Sg, [], Head,  _K, Fv, _Proj, Entry, Unifiers) :-
    peel(Head, Sg, Unifiers, []),!,  %% Head only contains ground
                                     %% terms, I save the unifs to
    %% exit_to_prime
    augment(Fv, not_provided, Entry).
call_to_entry(_Sv, Sg, Hv, Head, _K, Fv, Proj, Entry, Unifiers) :-
    peel(Head, Sg, Unifiers, []),
    augment(Hv, Proj, Proj0),
    copy_term(Unifiers-Proj0-Hv, UnifiersCopy-ProjCopy-Hv),
    abstract_unif(UnifiersCopy, ProjCopy, Entry1),!,
    project(not_provided_Sg, Hv, not_provided_HvFv, Entry1, Entry2),
    abs_sort(Entry2, Entry3),
    augment(Fv, Entry3, Entry).
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

% ---------------------------------------------------------------------------
%! ## Exit to prime

% exit_to_prime(+,+,+,+,+,-,-)                                           %
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                      %
% It computes the prime abstract substitution Prime, i.e.  the result of %
% going from the abstract substitution over the head variables (Exit), to%
% the abstract substitution over the variables in the subgoal. It will:  %
% * If Exit is '$bottom', Prime will be also '$bottom'.                  %
% * If Flag = yes (Head and Sg identical up to renaming) it is just a    %
%   question of renaming Exit                                            %
% * If Hv = [], Prime = []                                               %
% * Otherwise:                                                           %
%      * apply abstract unification with the original equations from     % 
%        the head unification                                            %
%      * then project  over Sv obtaining Prime                           % 

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom').
exit_to_prime(Sg, Hv, Head, _Sv, Exit, yes, Prime) :-
    project(not_provided_Sg, Hv, not_provided, Exit, Prime0),
    copy_term(Head-Prime0, Head_cp-Prime0_cp),
    Sg = Head_cp,
    abs_sort(Prime0_cp, Prime).
exit_to_prime(_Sg,[], _Head, _Sv, _Exit, _ExtraInfo, []).
exit_to_prime(Sg, _Hv, Head, Sv, Exit, _ExtraInfo, Prime) :-
    peel(Sg, Head, Unifiers, []),
    augment(Sv, Exit, Exit0),
    abstract_unif(Unifiers, Exit0, Prime0), !, 
    project(not_provided_Sg, Sv, not_provided_HvFv, Prime0, Prime).

% ---------------------------------------------------------------------------
%! ## ABSTRACT Extend

% extend(+,+,+,+,-)                                                      %
% extend(Sg,Prime,Sv,Call,Succ)                                          %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ. Otherwise,  %
% just add to Prime equs. for variables in Call and not in Prime.        %

:- push_prolog_flag(multi_arity_warnings, off).
:- dom_impl(_, extend/5, [noq]).
extend(_Sg, '$bottom', _Sv, _Call, '$bottom').
extend(_Sg, _, [], Call, Call).
extend(_Sg, Prime, Sv, Call, Succ) :-  %% Sg is useless here since we can always set f(Sv)
    extend(Sv, Prime, Call, Succ).
:- pop_prolog_flag(multi_arity_warnings).

% ---------------------------------------------------------------------------
%! ## Widenings
% NOTE: Disabling of widening cannot be done here but in domains.pl

:- dom_impl(_, widencall/3, [noq]).
widencall('$bottom', '$bottom','$bottom') :-!. 
widencall('$bottom',ASub2,ASub2):-!.
widencall(ASub1,'$bottom',ASub1):-!.
widencall([], [], []) :- !.
widencall(ASub1, ASub2, Widen):-
    widen(ASub1, ASub2, Widen).

% ---------------------------------------------------------------------------

%% :- dom_impl(_, less_or_equal/2, [noq]).
%% less_or_equal(ASub1, ASub2) :-
%%     leq(ASub1, ASub2).

% ---------------------------------------------------------------------------
%! ## LUB

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([Lub], Lub).
compute_lub([L1, '$bottom'|Ls], Lub) :-
    compute_lub([L1|Ls], Lub).
compute_lub(['$bottom', L1|Ls], Lub) :-
    compute_lub([L1|Ls], Lub).
compute_lub([L1, L2|Ls], Lub) :-
    lub(L1, L2, Lub0),
    compute_lub([Lub0|Ls], Lub).

% ---------------------------------------------------------------------------
%! ## Project

:- push_prolog_flag(multi_arity_warnings, off).
:- dom_impl(_, project/5, [noq]).
project(_Sg, [], _HvFv, _ASub, []).
project(_Sg, Vars, _HvFv, ASub, Proj ):-
    abs_sort(ASub, ASub_s), 
    project(Vars, ASub_s, Proj).
:- pop_prolog_flag(multi_arity_warnings).

% ---------------------------------------------------------------------------
%! ## Unknow & Empty Entry,Unknow Call

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Vars,Entry) :-
    topmost(Vars, not_provided, Entry),!.

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg, Vars,Call,Succ):-
    topmost(Vars, Call, Succ).
   
% ---------------------------------------------------------------------------
%! # Handling Builtins

% Special Builtin
:- dom_impl(_, special_builtin/5, [noq]).
special_builtin('true/0',_,_,unchanged,_).
special_builtin('=/2',=(X,Y),_,unification,Condvars):-
    Condvars = (X,Y).
special_builtin(Sg_key, Sg, _Subgoal, other,  (Sg_key, Sg)) :-
    known_builtin(Sg_key), !.
%    known_builtin(Sg_key, Sg, Type, Info).

%known_builtin(Sg_key, Sg, other, (Sg_key, Sg)).

% Success Builtin
:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(Type,Sv,Condv,_HvFv_u,Call,New_Succ):-
    success_builtin0(Type,Sv,Condv,Call,New_Succ).

success_builtin0(Type,Sv,Condv,Call,New_Succ):-
    success_builtin_aux(Type,Sv,Condv,Call,New_Succ). 
success_builtin0(_, _, _, _, '$bottom').

success_builtin_aux(unchanged,_,_,Call,Succ):-
    Call = Succ.
success_builtin_aux(unification,_Sv,Condv,Call,Succ):-
    Condv = (Term1,Term2),
    peel(Term1, Term2, Unifs, []), 
    abstract_unif(Unifs, Call, Succ).
success_builtin_aux(other, Sv, Info, Call, Succ) :-
    Info = (Sg_key, Sg), 
    abstract_literal(Sg_key, Sg, Call, Prime),!,
    extend(Sg, Prime, Sv, Call, Succ).
    %abstract_builtin(Type, Info, Sv, Call, Succ).
success_builtin_aux(other, Sv, _Info, Call, Succ) :-
    topmost(Sv, Call, Succ).

% ---------------------------------------------------------------------------
%! ## Call to Success Fact

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg, Hv, Head, _K, Sv, Call, Proj, Prime, Succ) :-
    peel(Sg, Head, Unifiers, []),
    augment(Hv, Proj, Proj_ext),
    abstract_unif(Unifiers, Proj_ext, Entry0),!,
    project(not_provided_Sg, Sv, not_provided_HvFv_u, Entry0, Prime_us),
    abs_sort(Prime_us, Prime),
    extend(Sg, Prime, Sv, Call, Succ).
call_to_success_fact(_, _, _, _, _, _, _, _, '$bottom').

% ---------------------------------------------------------------------------

% var(Unifiers) C domain(Call)
abstract_unif([], Call, Call).
abstract_unif([X=T|Unifiers], Call, Succ) :-
    amgu(X, T, Call, Call1), !, 
    abstract_unif(Unifiers, Call1, Succ).
abstract_unif(_, _, '$bottom').
