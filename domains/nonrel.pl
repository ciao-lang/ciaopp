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

% Base for simple nonrel domains
:- include(.(nonrel_base)).

% ===========================================================================
% (hook operations for nonrel_base)

nonrel_init_abstract_domain(nonrel_intervals, PushedFlags) :- !, nonrel_intervals_init_abstract_domain0(PushedFlags).
nonrel_top(nonrel_intervals, X) :- !, nonrel_intervals_top(X).
nonrel_bot(nonrel_intervals, X) :- !, nonrel_intervals_bot(X).
nonrel_var(nonrel_intervals, X) :- !, nonrel_intervals_var(X).
nonrel_amgu(nonrel_intervals, T1,T2,ASub0,NASub) :- !, nonrel_intervals_amgu0(T1,T2,ASub0,NASub).
nonrel_less_or_equal_elem(nonrel_intervals,E1,E2) :- !, nonrel_intervals_less_or_equal_elem(E1,E2).
nonrel_compute_glb_elem(nonrel_intervals,E1,E2,EG) :- !, nonrel_intervals_compute_glb_elem(E1,E2,EG).
nonrel_compute_lub_elem(nonrel_intervals,E1,E2,EL) :- !, nonrel_intervals_compute_lub_elem(E1,E2,EL).
nonrel_widen_elem(nonrel_intervals,E1,E2,EW) :- !, nonrel_intervals_widen_elem(E1,E2,EW).
% nonrel_input_interface(nonrel_intervals,Prop,Kind,Struct0,Struct1) :- !, nonrel_intervals_input_interface0(Prop,Kind,Struct0,Struct1).
nonrel_special_builtin0(nonrel_intervals,SgKey,Sg,Type,Condvars) :- !, nonrel_intervals_special_builtin0(SgKey,Sg,Type,Condvars).
nonrel_call_to_success_builtin0(nonrel_intervals,SgKey,Sg,Sv,Call,Proj,Succ) :- !, nonrel_intervals_call_to_success_builtin0(SgKey,Sg,Sv,Call,Proj,Succ).

:- include(nonrel_intervals).

% ---------------------------------------------------------------------------
% impl domain
% TODO: (use traits)

:- include(ciaopp(plai/plai_domain)).
:- dom_def(nonrel_intervals).
:- dom_impl(nonrel_intervals, init_abstract_domain/1).
:- dom_impl(nonrel_intervals, amgu/4).
:- dom_impl(nonrel_intervals, call_to_entry/9).
:- dom_impl(nonrel_intervals, exit_to_prime/7).
:- dom_impl(nonrel_intervals, project/5).
:- dom_impl(nonrel_intervals, widencall/3).
:- dom_impl(nonrel_intervals, needs/1).
:- dom_impl(nonrel_intervals, widen/3).
:- dom_impl(nonrel_intervals, compute_lub/2).
:- dom_impl(nonrel_intervals, identical_abstract/2).
:- dom_impl(nonrel_intervals, abs_sort/2).
:- dom_impl(nonrel_intervals, extend/5).
:- dom_impl(nonrel_intervals, less_or_equal/2).
:- dom_impl(nonrel_intervals, glb/3).
:- dom_impl(nonrel_intervals, call_to_success_fact/9).
:- dom_impl(nonrel_intervals, special_builtin/5).
:- dom_impl(nonrel_intervals, success_builtin/6).
:- dom_impl(nonrel_intervals, call_to_success_builtin/6).
:- dom_impl(nonrel_intervals, input_interface/4).
:- dom_impl(nonrel_intervals, input_user_interface/5).
:- dom_impl(nonrel_intervals, asub_to_native/5).
:- dom_impl(nonrel_intervals, unknown_call/4).
:- dom_impl(nonrel_intervals, unknown_entry/3).
:- dom_impl(nonrel_intervals, empty_entry/3).

%:- export(nonrel_intervals_needs/1).
:- doc(doinclude, nonrel_intervals_needs/1).
nonrel_intervals_needs(widen).

%:- export(nonrel_intervals_init_abstract_domain/1).
:- doc(doinclude, nonrel_intervals_init_abstract_domain/1).
nonrel_intervals_init_abstract_domain(PushedFlags) :- nonrel_init_abstract_domain(nonrel_intervals, PushedFlags).
%:- export(nonrel_intervals_amgu/4).
:- doc(doinclude, nonrel_intervals_amgu/4).
nonrel_intervals_amgu(Sg,Head,ASub,NewASub) :- nonrel_amgu(nonrel_intervals,Sg,Head,ASub,NewASub).
%:- export(nonrel_intervals_call_to_entry/9).
:- doc(doinclude, nonrel_intervals_call_to_entry/9).
nonrel_intervals_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- nonrel_call_to_entry(nonrel_intervals,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
%:- export(nonrel_intervals_exit_to_prime/7).
:- doc(doinclude, nonrel_intervals_exit_to_prime/7).
nonrel_intervals_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- nonrel_exit_to_prime(nonrel_intervals,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
%:- export(nonrel_intervals_project/5).
:- doc(doinclude, nonrel_intervals_project/5).
nonrel_intervals_project(_Sg,Vars,_HvFv,ASub,Proj) :- nonrel_project(ASub,Vars,Proj).
%:- export(nonrel_intervals_widencall/3).
:- doc(doinclude, nonrel_intervals_widencall/3).
nonrel_intervals_widencall(Prime0,Prime1,NewPrime) :- nonrel_widencall(nonrel_intervals,Prime0,Prime1,NewPrime).
%:- export(nonrel_intervals_widen/3).
:- doc(doinclude, nonrel_intervals_widen/3).
nonrel_intervals_widen(Prime0,Prime1,NewPrime) :- nonrel_widen(nonrel_intervals,Prime0,Prime1,NewPrime).
%:- export(nonrel_intervals_compute_lub/2).
:- doc(doinclude, nonrel_intervals_compute_lub/2).
nonrel_intervals_compute_lub(ListASub,LubASub) :- nonrel_compute_lub(nonrel_intervals,ListASub,LubASub).
%:- export(nonrel_intervals_identical_abstract/2).
:- doc(doinclude, nonrel_intervals_identical_abstract/2).
nonrel_intervals_identical_abstract(ASub1, ASub2) :- nonrel_identical_abstract(ASub1, ASub2).
%:- export(nonrel_intervals_abs_sort/2).
:- doc(doinclude, nonrel_intervals_abs_sort/2).
nonrel_intervals_abs_sort(ASub,ASub_s) :- nonrel_abs_sort(ASub,ASub_s).
%:- export(nonrel_intervals_extend/5).
:- doc(doinclude, nonrel_intervals_extend/5).
nonrel_intervals_extend(_Sg,Prime,Sv,Call,Succ) :- nonrel_extend(nonrel_intervals,Prime,Sv,Call,Succ).
%:- export(nonrel_intervals_less_or_equal/2).
:- doc(doinclude, nonrel_intervals_less_or_equal/2).
nonrel_intervals_less_or_equal(ASub0,ASub1) :- nonrel_less_or_equal(nonrel_intervals,ASub0,ASub1).
%:- export(nonrel_intervals_glb/3).
:- doc(doinclude, nonrel_intervals_glb/3).
nonrel_intervals_glb(ASub0,ASub1,ASub) :- nonrel_glb(nonrel_intervals,ASub0,ASub1,ASub).
%:- export(nonrel_intervals_call_to_success_fact/9).
:- doc(doinclude, nonrel_intervals_call_to_success_fact/9).
nonrel_intervals_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- nonrel_call_to_success_fact(nonrel_intervals,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
%:- export(nonrel_intervals_special_builtin/5).
:- doc(doinclude, nonrel_intervals_special_builtin/5).
nonrel_intervals_special_builtin(SgKey,Sg,_Subgoal,Type,Condvars) :- nonrel_special_builtin(nonrel_intervals,SgKey,Sg,Type,Condvars).
%:- export(nonrel_intervals_success_builtin/6).
:- doc(doinclude, nonrel_intervals_success_builtin/6).
nonrel_intervals_success_builtin(Type,_Sv_uns,Condvars,_HvFv_u,Call,Succ) :- nonrel_success_builtin(nonrel_intervals,Type,Condvars,Call,Succ).
%:- export(nonrel_intervals_call_to_success_builtin/6).
:- doc(doinclude, nonrel_intervals_call_to_success_builtin/6).
nonrel_intervals_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ) :- nonrel_call_to_success_builtin(nonrel_intervals,SgKey,Sg,Sv,Call,Proj,Succ).
%:- export(nonrel_intervals_input_interface/4).
:- doc(doinclude, nonrel_intervals_input_interface/4).
nonrel_intervals_input_interface(InputUser,Kind,Struct0,Struct1) :- nonrel_input_interface(nonrel_intervals,InputUser,Kind,Struct0,Struct1).
%:- export(nonrel_intervals_input_user_interface/5).
:- doc(doinclude, nonrel_intervals_input_user_interface/5).
nonrel_intervals_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- nonrel_input_user_interface(nonrel_intervals,InputUser,Qv,ASub).
%:- export(nonrel_intervals_asub_to_native/5).
:- doc(doinclude, nonrel_intervals_asub_to_native/5).
nonrel_intervals_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps) :- nonrel_asub_to_native(nonrel_intervals,ASub,Qv,OutFlag,OutputUser,Comps).
%:- export(nonrel_intervals_unknown_call/4).
:- doc(doinclude, nonrel_intervals_unknown_call/4).
nonrel_intervals_unknown_call(Sg,Vars,Call,Succ) :- nonrel_unknown_call(nonrel_intervals,Sg,Vars,Call,Succ).
%:- export(nonrel_intervals_unknown_entry/3).
:- doc(doinclude, nonrel_intervals_unknown_entry/3).
nonrel_intervals_unknown_entry(Sg,Qv,Call) :- nonrel_unknown_entry(nonrel_intervals,Sg,Qv,Call).
%:- export(nonrel_intervals_empty_entry/3).
:- doc(doinclude, nonrel_intervals_empty_entry/3).
nonrel_intervals_empty_entry(Sg,Qv,Call) :- nonrel_unknown_entry(nonrel_intervals,Sg,Qv,Call).
