% ===========================================================================
% Hooks for domain implementations

% TODO: See analysis.lpdoc for documentation

:- discontiguous(aidomain/1).
:- discontiguous(init_abstract_domain/2).
:- discontiguous(amgu/5).
:- discontiguous(augment_asub/4).
:- discontiguous(augment_two_asub/4).
:- discontiguous(call_to_entry/10).
:- discontiguous(exit_to_prime/8).
:- discontiguous(project/6).
:- discontiguous(widencall/4).
:- discontiguous(widen/4).
:- discontiguous(compute_lub/3).
:- discontiguous(compute_clauses_lub/4).
:- discontiguous(fixpoint_covered/3).
:- discontiguous(fixpoint_covered_gfp/3).
:- discontiguous(identical_abstract/3).
:- discontiguous(abs_sort/3).
:- discontiguous(extend/6).
:- discontiguous(less_or_equal/3).
:- discontiguous(glb/4).
:- discontiguous(eliminate_equivalent/3).
:- discontiguous(abs_subset/3).
:- discontiguous(call_to_success_fact/10).
:- discontiguous(special_builtin/6).
:- discontiguous(combined_special_builtin/3).
:- discontiguous(body_succ_builtin/9).
:- discontiguous(split_combined_domain/4).
:- discontiguous(success_builtin/7).
:- discontiguous(call_to_success_builtin/7).
:- discontiguous(obtain_info/5).
:- discontiguous(input_interface/5).
:- discontiguous(input_user_interface/6).
:- discontiguous(asub_to_native/6).
:- discontiguous(concrete/4).
:- discontiguous(unknown_call/5).
:- discontiguous(unknown_entry/4).
:- discontiguous(empty_entry/4).
%
% :- discontiguous(propagate_downwards_closed/4).
% :- discontiguous(del_real_conjoin/4).
% :- discontiguous(del_hash/4).
% :- discontiguous(more_instantiate/3).
% :- discontiguous(convex_hull/4).
% :- discontiguous(compute_lub_el/4).
% :- discontiguous(extend_free/4).
% :- discontiguous(del_check_cond/6).
% :- discontiguous(del_impose_cond/5).
%
:- discontiguous(part_conc/5).
:- discontiguous(multi_part_conc/4).
:- discontiguous(collect_abstypes_abs/4).
:- discontiguous(rename_abstypes_abs/4).
:- discontiguous(dom_statistics/2).
:- discontiguous(contains_parameters/2). % can succeed only for deftypes

% ===========================================================================
:- doc(section, "Reachability domains"). % TODO: for partial evaluation
% ---------------------------------------------------------------------------
% PD domain
:- use_module(domain(pd)).
aidomain(pd).
call_to_entry(pd,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, pd_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(pd,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, pd_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(pd,Sg,Vars,HvFv,ASub,Proj) :- !, pd_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(pd,ListAsub,LubASub) :- !, pd_compute_lub(ListAsub,LubASub).
abs_sort(pd,ASub,ASub_s) :- !, pd_sort(ASub,ASub_s).
extend(pd,Sg,Prime,Sv,Call,Succ) :- !, pd_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(pd,ASub0,ASub1) :- !, pd_less_or_equal(ASub0,ASub1).
glb(pd,ASub0,ASub1,ASub) :- !, pd_glb(ASub0,ASub1,ASub).
call_to_success_fact(pd,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, pd_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(pd,SgKey,Sg,Subgoal,Type,Condvars) :- !, pd_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(pd,Type,Sv_uns,Condvars,HvFv_u,Call,Succ) :- !, pd_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).
call_to_success_builtin(pd,SgKey,Sg,Sv,Call,Proj,Succ) :- !, pd_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_user_interface(pd,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, pd_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(pd,ASub,Qv,OutFlag,OutputUser,Comps) :- !, pd_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(pd,Sg,Vars,Call,Succ) :- !, pd_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(pd,Sg,Qv,Call) :- !, pd_unknown_entry(Sg,Qv,Call).
empty_entry(pd,Sg,Qv,Call) :- !, pd_empty_entry(Sg,Qv,Call).
% ---------------------------------------------------------------------------
% PD domain with bottom
:- use_module(domain(pdb)).
aidomain(pdb).
call_to_entry(pdb,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, pdb_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(pdb,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, pdb_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(pdb,Sg,Vars,HvFv,ASub,Proj) :- !, pdb_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(pdb,ListAsub,LubASub) :- !, pdb_compute_lub(ListAsub,LubASub).
abs_sort(pdb,ASub,ASub_s) :- !, pdb_sort(ASub,ASub_s).
extend(pdb,Sg,Prime,Sv,Call,Succ) :- !, pdb_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(pdb,ASub0,ASub1) :- !, pdb_less_or_equal(ASub0,ASub1).
glb(pdb,ASub0,ASub1,ASub) :- !, pdb_glb(ASub0,ASub1,ASub).
call_to_success_fact(pdb,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, pdb_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(pdb,SgKey,Sg,Subgoal,Type,Condvars) :- !, pdb_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(pdb,Type,Sv_uns,Condvars,HvFv_u,Call,Succ) :- !, pdb_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).
call_to_success_builtin(pdb,SgKey,Sg,Sv,Call,Proj,Succ) :- !, pdb_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_user_interface(pdb,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, pdb_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(pdb,ASub,Qv,OutFlag,OutputUser,Comps) :- !, pdb_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(pdb,Sg,Vars,Call,Succ) :- !, pdb_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(pdb,Sg,Qv,Call) :- !, pdb_unknown_entry(Sg,Qv,Call).
empty_entry(pdb,Sg,Qv,Call) :- !, pdb_empty_entry(Sg,Qv,Call).
% ===========================================================================
:- doc(section, "Constraint domains").
% ---------------------------------------------------------------------------
:- use_module(domain(fr_top)).
aidomain(fr).
call_to_entry(fr,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, fr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(fr,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, fr_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(fr,Sg,Vars,HvFv,ASub,Proj) :- !, fr_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(fr,ListASub,LubASub) :- !, fr_compute_lub(ListASub,LubASub).
identical_abstract(fr,ASub1,ASub2) :- !, fr_identical_abstract(ASub1,ASub2).
abs_sort(fr,ASub,ASub_s) :- !, fr_sort(ASub,ASub_s).
extend(fr,Sg,Prime,Sv,Call,Succ) :- !, fr_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(fr,ASub0,ASub1) :- !, fr_less_or_equal(ASub0,ASub1).
glb(fr,ASub0,ASub1,ASub) :- !, fr_glb(ASub0,ASub1,ASub).
call_to_success_fact(fr,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, fr_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(fr,SgKey,Sg,Subgoal,Type,Condvars) :- !, fr_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(fr,Type,Sv_uns,Condvars,HvFv_u,Call,Succ) :- !, fr_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).
input_interface(fr,InputUser,Kind,Struct0,Struct1) :- !, fr_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(fr,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, fr_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(fr,ASub,Qv,OutFlag,OutputUser,Comps) :- !, fr_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(fr,Sg,Vars,Call,Succ) :- !, fr_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(fr,Sg,Qv,Call) :- !, fr_unknown_entry(Sg,Qv,Call).
empty_entry(fr,Sg,Qv,Call) :- !, fr_empty_entry(Sg,Qv,Call).
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef
% ---------------------------------------------------------------------------
:- use_module(domain(fd)).
aidomain(frdef).
call_to_entry(frdef,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, fd_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(frdef,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, fd_exit_to_prime(Exit,Sg,Hv,Head,Sv,ExtraInfo,Prime).
project(frdef,_Sg,Vars,_HvFv,ASub,Proj) :- !, fd_project(ASub,Vars,Proj).
compute_lub(frdef,ListASub,LubASub) :- !, fd_compute_lub(ListASub,LubASub).
identical_abstract(frdef,ASub1,ASub2) :- !, fd_identical_abstract(ASub1,ASub2).
abs_sort(frdef,ASub,ASub_s) :- !, fd_sort(ASub,ASub_s).
extend(frdef,Sg,Prime,Sv,Call,Succ) :- !, fd_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(frdef,ASub0,ASub1) :- !, fd_less_or_equal(ASub0,ASub1).
glb(frdef,ASub0,ASub1,ASub) :- !, fd_glb(ASub0,ASub1,ASub).
call_to_success_fact(frdef,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, fd_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(frdef,SgKey,Sg,Subgoal,(TypeF,TypeD),(CondF,CondD)) :- !, def_special_builtin(SgKey,Sg,TypeD,CondD), fr_special_builtin(SgKey,Sg,Subgoal,TypeF,CondF).
success_builtin(frdef,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, fd_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
input_interface(frdef,InputUser,Kind,Struct0,Struct1) :- !, fd_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(frdef,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, fd_input_user_interface(InputUser,Qv,ASub).
asub_to_native(frdef,ASub,Qv,OutFlag,OutputUser,Comps) :- !, fd_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(frdef,Sg,Vars,Call,Succ) :- !, fd_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(frdef,Sg,Qv,Call) :- !, fd_unknown_entry(Sg,Qv,Call).
empty_entry(frdef,Sg,Qv,Call) :- !, fd_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
fd_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef
% ---------------------------------------------------------------------------
% lsign
:- use_module(domain(lsign)).
aidomain(lsign).
init_abstract_domain(lsign,PushedFlags) :- !, lsign_init_abstract_domain(PushedFlags).
call_to_entry(lsign,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(lsign,Sg,Hv,Head,_Sv,Exit,ExtraInfo,Prime) :- !, lsign_exit_to_prime(Sg,Hv,Head,Exit,ExtraInfo,Prime).
project(lsign,_Sg,Vars,HvFv,ASub,Proj) :- !, lsign_project(ASub,Vars,HvFv,Proj).
compute_lub(lsign,ListASub,LubASub) :- !, lsign_compute_lub(ListASub,LubASub).
abs_sort(lsign,ASub,ASub_s) :- !, lsign_sort(ASub,ASub_s).
extend(lsign,Sg,Prime,Sv,Call,Succ) :- !, lsign_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(lsign,ASub0,ASub1) :- !, lsign_less_or_equal(ASub0,ASub1).
glb(lsign,ASub0,ASub1,ASub) :- !, lsign_glb(ASub0,ASub1,ASub).
eliminate_equivalent(lsign,TmpLSucc,LSucc) :- !, lsign_eliminate_equivalent(TmpLSucc,LSucc).
abs_subset(lsign,LASub1,LASub2) :- !, lsign_is_subset(LASub1,LASub2).
call_to_success_fact(lsign,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, lsign_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(lsign,SgKey,Sg,_Subgoal,Type,Condvars) :- !, lsign_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(lsign,Type,Sv_uns,Condvars,HvFv_u,Call,Succ) :- !, lsign_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).
input_interface(lsign,InputUser,Kind,Struct0,Struct1) :- !, lsign_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(lsign,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, lsign_input_user_interface(InputUser,Qv,ASub).
asub_to_native(lsign,ASub,Qv,OutFlag,OutputUser,Comps) :- !, lsign_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(lsign,Sg,Vars,Call,Succ) :- !, lsign_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(lsign,Sg,Qv,Call) :- !, lsign_unknown_entry(Sg,Qv,Call).
empty_entry(lsign,Sg,Qv,Call) :- !, lsign_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
lsign_init_abstract_domain([normalize,variants]) :-
	push_pp_flag(normalize,on),
	push_pp_flag(variants,off).
lsign_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
lsign_asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :- lsign_output_interface(ASub,OutputUser).
% ----------
aidomain(difflsign).
call_to_entry(difflsign,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, simple_lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(difflsign,Sg,Hv,Head,_Sv,Exit,ExtraInfo,Prime) :- !, simple_lsign_exit_to_prime(Sg,Hv,Head,Exit,ExtraInfo,Prime).
project(difflsign,Sg,Vars,HvFv,ASub,Proj) :- !, simple_lsign_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(difflsign,ListASub,LubASub) :- !, lsign_compute_lub(ListASub,LubASub).
abs_sort(difflsign,ASub,ASub_s) :- !, simple_lsign_sort(ASub,ASub_s).
extend(difflsign,Sg,Prime,Sv,Call,Succ) :- !, simple_lsign_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(difflsign,ASub0,ASub1) :- !, simple_lsign_less_or_equal(ASub0,ASub1).
glb(difflsign,ASub0,ASub1,ASub) :- !, simple_lsign_glb(ASub0,ASub1,ASub).
call_to_success_fact(difflsign,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, lsign_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(difflsign,SgKey,Sg,_Subgoal,Type,Condvars) :- !, lsign_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(difflsign,Type,Sv_uns,Condvars,HvFv_u,Call,Succ) :- !, simple_lsign_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).
input_interface(difflsign,InputUser,Kind,Struct0,Struct1) :- !, lsign_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(difflsign,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, simple_lsign_input_user_interface(InputUser,Qv,ASub).
asub_to_native(difflsign,ASub,Qv,OutFlag,OutputUser,Comps) :- !, simple_lsign_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(difflsign,Sg,Vars,Call,Succ) :- !, simple_lsign_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(difflsign,Sg,Qv,Call) :- !, simple_lsign_unknown_entry(Sg,Qv,Call).
empty_entry(difflsign,Sg,Qv,Call) :- !, simple_lsign_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
simple_lsign_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
simple_lsign_asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :- simple_lsign_output_interface(ASub,OutputUser).
% ----------
% aidomain(lsigndef). % TODO: empty, why?
call_to_entry(lsigndef,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, lsigndef_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(lsigndef,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, lsigndef_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(lsigndef,Sg,Vars,HvFv,ASub,Proj) :- !, lsigndef_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(lsigndef,ListASub,LubASub) :- !, lsigndef_compute_lub(ListASub,LubASub).
abs_sort(lsigndef,ASub,ASub_s) :- !, lsigndef_sort(ASub,ASub_s).
extend(lsigndef,Sg,Prime,Sv,Call,Succ) :- !, lsigndef_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(lsigndef,ASub0,ASub1) :- !, lsigndef_less_or_equal(ASub0,ASub1).
glb(lsigndef,ASub0,ASub1,ASub) :- !, lsigndef_glb(ASub0,ASub1,ASub).
call_to_success_fact(lsigndef,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, lsigndef_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
input_interface(lsigndef,InputUser,Kind,_Struct0,Struct1) :- !, lsigndef_input_interface(InputUser,Kind,Struct1).
input_user_interface(lsigndef,InputUser,_Qv,ASub,_Sg,_MaybeCallASub) :- !, lsigndef_input_user_interface(InputUser,ASub).
asub_to_native(lsigndef,ASub,Qv,OutFlag,OutputUser,Comps) :- !, lsigndef_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(lsigndef,Sg,Vars,Call,Succ) :- !, lsigndef_unknown_call(Sg,Call,Vars,Succ).
unknown_entry(lsigndef,Sg,Qv,Call) :- !, lsigndef_unknown_entry(Sg,Qv,Call).
empty_entry(lsigndef,Sg,Qv,Call) :- !, lsigndef_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
% lsigndef_body_succ_builtin(_,_,_,_,_,_). % TODO: be careful (old comment)
lsigndef_call_to_entry(_,_,_,_,_,_,_,_,_). 
lsigndef_call_to_success_fact(_,_,_,_,_,_,_,_,_).
lsigndef_compute_lub(_,_).
lsigndef_exit_to_prime(_,_,_,_,_,_,_).
lsigndef_extend(_,_,_,_,_).  
lsigndef_input_user_interface(_,_).
lsigndef_input_interface(_,_,_).
lsigndef_less_or_equal(_,_). 
lsigndef_asub_to_native(_,_,_,[],[]).
lsigndef_project(_,_,_,_,_). 
lsigndef_sort(_,_).    
% lsigndef_success_builtin(_,_,_,_,_,_).
lsigndef_unknown_call(_,_,_,_).  
lsigndef_unknown_entry(_,_,_).
lsigndef_empty_entry(_,_,_). 
lsigndef_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ----------
% aidomain(lsignshfr). % TODO: empty, why?
call_to_entry(lsignshfr,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, lsignshfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(lsignshfr,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, lsignshfr_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(lsignshfr,Sg,Vars,HvFv,ASub,Proj) :- !, lsignshfr_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(lsignshfr,ListASub,LubASub) :- !, lsignshfr_compute_lub(ListASub,LubASub).
abs_sort(lsignshfr,ASub,ASub_s) :- !, lsignshfr_sort(ASub,ASub_s).
extend(lsignshfr,Sg,Prime,Sv,Call,Succ) :- !, lsignshfr_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(lsignshfr,ASub0,ASub1) :- !, lsignshfr_less_or_equal(ASub0,ASub1).
glb(lsignshfr,ASub0,ASub1,ASub) :- !, lsignshfr_glb(ASub0,ASub1,ASub).
call_to_success_fact(lsignshfr,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, lsignshfr_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
input_interface(lsignshfr,InputUser,Kind,Struct0,Struct1) :- !, lsignshfr_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(lsignshfr,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, lsignshfr_input_user_interface(InputUser,Qv,ASub).
asub_to_native(lsignshfr,ASub,Qv,OutFlag,OutputUser,Comps) :- !, lsignshfr_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(lsignshfr,Sg,Vars,Call,Succ) :- !, lsignshfr_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(lsignshfr,Sg,Qv,Call) :- !, lsignshfr_unknown_entry(Sg,Qv,Call).
empty_entry(lsignshfr,Sg,Qv,Call) :- !, lsignshfr_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
% lsignshfr_body_succ_builtin(_,_,_,_,_,_). % TODO: be careful (old comment)
lsignshfr_call_to_entry(_,_,_,_,_,_,_,_,_).  
lsignshfr_call_to_success_fact(_,_,_,_,_,_,_,_,_).
lsignshfr_compute_lub(_,_).
lsignshfr_exit_to_prime(_,_,_,_,_,_,_).  
lsignshfr_extend(_,_,_,_,_). 
lsignshfr_input_user_interface(_,_,_). 
lsignshfr_input_interface(_,_,_,_). 
lsignshfr_less_or_equal(_,_). 
lsignshfr_asub_to_native(_,_,_,[],[]).
lsignshfr_project(_,_,_,_,_).
lsignshfr_sort(_,_).   
lsignshfr_unknown_call(_,_,_,_). 
lsignshfr_unknown_entry(_,_,_). 
lsignshfr_empty_entry(_,_,_). 
lsignshfr_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ----------
% aidomain(sha). % TODO: empty, why?
call_to_entry(sha,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, sha_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(sha,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, sha_exit_to_prime(Exit,Hv,Head,Sv,Sg,Prime,ExtraInfo).
project(sha,Sg,Vars,HvFv,ASub,Proj) :- !, sha_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(sha,ListASub,LubASub) :- !, sha_compute_lub(ListASub,LubASub).
abs_sort(sha,ASub,ASub_s) :- !, sha_abs_sort(ASub,ASub_s).
extend(sha,Sg,Prime,Sv,Call,Succ) :- !, sha_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(sha,ASub0,ASub1) :- !, sha_less_or_equal(ASub0,ASub1).
glb(sha,ASub0,ASub1,ASub) :- !, sha_glb(ASub0,ASub1,ASub).
eliminate_equivalent(sha,TmpLSucc,LSucc) :- !, sha_eliminate_equivalent(TmpLSucc,LSucc).
abs_subset(sha,LASub1,LASub2) :- !, sha_abs_subset(LASub1,LASub2).
call_to_success_fact(sha,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, sha_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(sha,SgKey,Sg,_Subgoal,Type,Condvars) :- !, sha_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(sha,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, sha_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(sha,SgKey,Sg,Sv,Call,Proj,Succ) :- !, sha_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(sha,InputUser,Kind,Struct0,Struct1) :- !, sha_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(sha,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, sha_input_user_interface(InputUser,Qv,ASub).
asub_to_native(sha,ASub,Qv,OutFlag,OutputUser,Comps) :- !, sha_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(sha,Sg,Vars,Call,Succ) :- !, sha_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(sha,Sg,Qv,Call) :- !, sha_unknown_entry(Sg,Qv,Call).
empty_entry(sha,Sg,Qv,Call) :- !, sha_empty_entry(Sg,Qv,Call).
%% compute_lub_el(sha,ASub1,ASub2,ASub) :- !, sha_lub(ASub1,ASub2,ASub).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
sha_call_to_entry(_,_,_,_,_,_,_,_,_).
sha_call_to_success_builtin(_,_,_,_,_,_). 
sha_call_to_success_fact(_,_,_,_,_,_,_,_,_). 
sha_compute_lub(_,_).  
sha_abs_sort(_,_).     
% sha_body_succ_builtin(_,_,_,_,_,_). % TODO: be careful (old comment)
sha_exit_to_prime(_,_,_,_,_,_,_).
sha_extend(_,_,_,_,_).       
sha_eliminate_equivalent(TmpLSucc,LSucc) :- absub_eliminate_equivalent(TmpLSucc,sha,LSucc).
sha_abs_subset(LASub1,LASub2) :- absub_is_subset(LASub1,sha,LASub2).
sha_input_user_interface(_,_,_). 
sha_input_interface(_,_,_,_). 
sha_less_or_equal(_,_).
% sha_lub(_,_,_).        
% sha_output_interface(_,_).
sha_asub_to_native(_,_,_,[],[]).
sha_project(_,_,_,_,_).      
sha_special_builtin(_,_,_,_).
sha_success_builtin(_,_,_,_,_).
sha_unknown_call(_,_,_,_).
sha_unknown_entry(_,_,_).
sha_empty_entry(_,_,_).
sha_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ----------
% aidomain(typeshfr). % TODO: empty, why?
call_to_entry(typeshfr,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo). % AADEBUG
compute_lub(typeshfr,ListASub,LubASub) :- !, shfr_compute_lub(ListASub,LubASub). %% AADEBUG added
identical_abstract(typeshfr,ASub1,ASub2) :- !, identical_abstract(shfr,ASub1,ASub2). %% AADEBUG
abs_sort(typeshfr,ASub,ASub_s) :- !, abs_sort(shfr,ASub,ASub_s). %% AADEBUG
glb(typeshfr,ASub0,ASub1,ASub) :- !, glb(shfr,ASub0,ASub1,ASub).
% ===========================================================================
:- doc(section, "Groundness and sharing").
% ---------------------------------------------------------------------------
% Example groundness domain
:- use_module(domain(gr)).
aidomain(gr).
call_to_entry(gr,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, gr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(gr,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, gr_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(gr,_Sg,Vars,_HvFv,ASub,Proj) :- !, gr_project(ASub,Vars,Proj).
compute_lub(gr,ListAsub,LubASub) :- !, gr_compute_lub(ListAsub,LubASub).
abs_sort(gr,ASub,ASub_s) :- !, gr_sort(ASub,ASub_s).
extend(gr,_Sg,Prime,Sv,Call,Succ) :- !, gr_extend(Prime,Sv,Call,Succ).
less_or_equal(gr,ASub0,ASub1) :- !, gr_less_or_equal(ASub0,ASub1).
glb(gr,ASub0,ASub1,ASub) :- !, gr_glb(ASub0,ASub1,ASub).
call_to_success_fact(gr,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, gr_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(gr,SgKey,Sg,_Subgoal,Type,Condvars) :- !, gr_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(gr,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, gr_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(gr,SgKey,Sg,Sv,Call,Proj,Succ) :- !, gr_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(gr,InputUser,Kind,Struct0,Struct1) :- !, gr_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(gr,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, gr_input_user_interface(InputUser,Qv,ASub).
asub_to_native(gr,ASub,Qv,OutFlag,OutputUser,Comps) :- !, gr_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(gr,Sg,Vars,Call,Succ) :- !, gr_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(gr,Sg,Qv,Call) :- !, gr_unknown_entry(Sg,Qv,Call).
empty_entry(gr,Sg,Qv,Call) :- !, gr_empty_entry(Sg,Qv,Call).
%% %% compute_lub_el(gr,ASub1,ASub2,ASub) :- !, gr_compute_lub_el(ASub1,ASub2,ASub).
%% %% extend_free(gr,ASub1,Vars,ASub) :- !, gr_extend_free(ASub1,Vars,ASub).
% ---------------------------------------------------------------------------
:- use_module(domain(def)).
aidomain(def).
call_to_entry(def,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, def_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(def,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, def_exit_to_prime(Exit,ExtraInfo,Hv,Sv,Head,Sg,Prime).
project(def,_Sg,Vars,_HvFv,ASub,Proj) :- !, def_project(ASub,Vars,Proj).
compute_lub(def,ListASub,LubASub) :- !, def_compute_lub(ListASub,LubASub).
abs_sort(def,ASub,ASub_s) :- !, def_sort(ASub,ASub_s).
extend(def,_Sg,Prime,_Sv,Call,Succ) :- !, def_extend(Prime,Call,Succ).
less_or_equal(def,ASub0,ASub1) :- !, def_less_or_equal(ASub0,ASub1).
glb(def,ASub0,ASub1,ASub) :- !, def_glb(ASub0,ASub1,ASub).
call_to_success_fact(def,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, def_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(def,SgKey,Sg,_Subgoal,Type,Condvars) :- !, def_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(def,Type,_Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, def_success_builtin(Type,Condvars,Call,Succ).
input_interface(def,InputUser,Kind,Struct0,Struct1) :- !, def_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(def,InputUser,_Qv,ASub,_Sg,_MaybeCallASub) :- !, def_input_user_interface(InputUser,ASub).
asub_to_native(def,ASub,Qv,OutFlag,OutputUser,Comps) :- !, def_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(def,Sg,Vars,Call,Succ) :- !, def_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(def,Sg,Qv,Call) :- !, def_unknown_entry(Sg,Qv,Call).
empty_entry(def,Sg,Qv,Call) :- !, def_empty_entry(Sg,Qv,Call).
%% propagate_downwards_closed(def,ASub1,ASub2,ASub) :- !, def_downwards_closed(ASub1,ASub2,ASub).
%% del_real_conjoin(def,ASub1,ASub2,ASub) :- !, def_real_conjoin(ASub1,ASub2,ASub).
%% del_hash(def,ASub,Vars,N) :- !, def_hash(ASub,Vars,N).
%% more_instantiate(def,ASub1,ASub2) :- !, def_less_or_equal(ASub2,ASub1).
%% convex_hull(def,Old,_,Old) :- !.
%% compute_lub_el(def,ASub1,ASub2,ASub) :- !, def_compute_lub_el(ASub1,ASub2,ASub).
%% extend_free(def,ASub,_,ASub) :- !.
%% del_check_cond(def,Cond,ASub,Sv,Flag,WConds) :- !, def_check_cond(Cond,ASub,Sv,Flag,WConds).
%% del_impose_cond(def,LCond,Sv,ASub,LASub) :- !, def_impose_cond(LCond,Sv,ASub,LASub).
%
def_empty_entry(Sg,Qv,Call) :- def_unknown_entry(Sg,Qv,Call). % TODO: move to def.pl
%% def_check_cond(_,_,_,_,_). 
%% def_downwards_closed(_,_,_).
%% def_hash(_,_,_).
%% def_impose_cond(_,_,_,_).
%% def_real_conjoin(_,_,_).
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef
% ---------------------------------------------------------------------------
:- use_module(domain(sharing)).
aidomain(share).
amgu(share,Sg,Head,ASub,NewASub) :- !, share_amgu(Sg,Head,ASub,NewASub).
augment_asub(share,ASub,Vars,ASub0) :- !, share_amgu_extend_asub(ASub,Vars,ASub0).
augment_two_asub(share,ASub0,ASub1,ASub) :- !, share_amgu_extend_two_asub(ASub0,ASub1,ASub).
call_to_entry(share,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, share_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(share,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, share_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(share,_Sg,Vars,_HvFv,ASub,Proj) :- !, share_project(Vars,ASub,Proj).
compute_lub(share,ListAsub,LubASub) :- !, share_compute_lub(ListAsub,LubASub).
abs_sort(share,ASub,ASub_s) :- !, share_sort(ASub,ASub_s).
extend(share,_Sg,Prime,Sv,Call,Succ) :- !, share_extend(Prime,Sv,Call,Succ).
less_or_equal(share,ASub0,ASub1) :- !, share_less_or_equal(ASub0,ASub1).
glb(share,ASub0,ASub1,ASub) :- !, share_glb(ASub0,ASub1,ASub).
call_to_success_fact(share,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, share_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(share,SgKey,Sg,_Subgoal,Type,Condvars) :- !, share_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(share,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, share_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(share,SgKey,Sg,Sv,Call,Proj,Succ) :- !, share_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(share,InputUser,Kind,Struct0,Struct1) :- !, share_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(share,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, share_input_user_interface(InputUser,Qv,ASub).
asub_to_native(share,ASub,Qv,OutFlag,OutputUser,Comps) :- !, share_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(share,Sg,Vars,Call,Succ) :- !, share_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(share,Sg,Qv,Call) :- !, share_unknown_entry(Sg,Qv,Call).
empty_entry(share,Sg,Qv,Call) :- !, share_empty_entry(Sg,Qv,Call).
%% compute_lub_el(share,ASub1,ASub2,ASub) :- !, share_lub(ASub1,ASub2,ASub).
% ----------
:- use_module(domain(sharefree)).
aidomain(shfr).
amgu(shfr,Sg,Head,ASub,NewASub) :- !, sharefree_amgu(Sg,Head,ASub,NewASub).
augment_asub(shfr,ASub,Vars,ASub0) :- !, sharefree_amgu_extend_asub(ASub,Vars,ASub0).
call_to_entry(shfr,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(shfr,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, shfr_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(shfr,_Sg,Vars,_HvFv,ASub,Proj) :- !, shfr_project(ASub,Vars,Proj).
compute_lub(shfr,ListAsub,LubASub) :- !, shfr_compute_lub(ListAsub,LubASub).
abs_sort(shfr,ASub,ASub_s) :- !, shfr_sort(ASub,ASub_s).
extend(shfr,_Sg,Prime,Sv,Call,Succ) :- !, shfr_extend(Prime,Sv,Call,Succ).
less_or_equal(shfr,ASub0,ASub1) :- !, shfr_less_or_equal(ASub0,ASub1).
glb(shfr,ASub0,ASub1,ASub) :- !, shfr_glb(ASub0,ASub1,ASub).
call_to_success_fact(shfr,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, shfr_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(shfr,SgKey,Sg,_Subgoal,Type,Condvars) :- !, shfr_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(shfr,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, shfr_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(shfr,SgKey,Sg,Sv,Call,Proj,Succ) :- !, shfr_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(shfr,Prop,Vars,ASub,Info) :- !, shfr_obtain(Prop,Vars,ASub,Info).
input_interface(shfr,InputUser,Kind,Struct0,Struct1) :- !, shfr_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(shfr,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shfr_input_user_interface(InputUser,Qv,ASub).
asub_to_native(shfr,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shfr_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(shfr,Sg,Vars,Call,Succ) :- !, shfr_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(shfr,Sg,Qv,Call) :- !, shfr_unknown_entry(Sg,Qv,Call).
empty_entry(shfr,Sg,Qv,Call) :- !, shfr_empty_entry(Sg,Qv,Call).
%% propagate_downwards_closed(shfr,ASub1,ASub2,ASub) :- !, shfr_downwards_closed(ASub1,ASub2,ASub).
%% del_real_conjoin(shfr,ASub1,ASub2,ASub) :- !, shfr_real_conjoin(ASub1,ASub2,ASub).
%% del_hash(shfr,ASub,Vars,N) :- !, shfr_hash(ASub,Vars,N).
%% more_instantiate(shfr,ASub1,ASub2) :- !, shfr_more_instantiate(ASub1,ASub2).
%% convex_hull(shfr,Old,New,Hull) :- !, shfr_convex_hull(Old,New,Hull).
%% compute_lub_el(shfr,ASub1,ASub2,ASub) :- !, shfr_compute_lub_el(ASub1,ASub2,ASub).
%% extend_free(shfr,ASub1,Vars,ASub) :- !, shfr_extend_free(ASub1,Vars,ASub).
%% del_check_cond(shfr,Cond,ASub,Sv,Flag,WConds) :- !, shfr_check_cond(Cond,ASub,Sv,Flag,WConds).
%% del_impose_cond(shfr,LCond,Sv,ASub,LASub) :- !, shfr_impose_cond(LCond,Sv,ASub,LASub).
%
%% shfr_check_cond(_,_,_,_,_).
%% % shfr_compute_lub_el(_,_,_). %% commented out by JNL
%% shfr_convex_hull(_,_,_).
%% shfr_downwards_closed(_,_,_).
%% shfr_extend_free(_,_,_).
%% shfr_hash(_,_,_).
%% shfr_impose_cond(_,_,_,_).
%% shfr_more_instantiate(_,_).
%% shfr_real_conjoin(_,_,_).
% ----------
:- use_module(domain(sharefree_non_var)).
aidomain(shfrnv).
call_to_entry(shfrnv,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfrnv_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(shfrnv,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, shfrnv_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(shfrnv,_Sg,Vars,_HvFv,ASub,Proj) :- !, shfr_project(ASub,Vars,Proj).
compute_lub(shfrnv,ListAsub,LubASub) :- !, shfrnv_compute_lub(ListAsub,LubASub).
abs_sort(shfrnv,ASub,ASub_s) :- !, shfr_sort(ASub,ASub_s).
extend(shfrnv,_Sg,Prime,Sv,Call,Succ) :- !, shfrnv_extend(Prime,Sv,Call,Succ).
less_or_equal(shfrnv,ASub0,ASub1) :- !, shfrnv_less_or_equal(ASub0,ASub1).
glb(shfrnv,ASub0,ASub1,ASub) :- !, shfrnv_glb(ASub0,ASub1,ASub).
call_to_success_fact(shfrnv,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, shfrnv_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(shfrnv,SgKey,Sg,_Subgoal,Type,Condvars) :- !, shfr_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(shfrnv,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, shfrnv_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(shfrnv,SgKey,Sg,Sv,Call,Proj,Succ) :- !, shfrnv_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(shfrnv,InputUser,Kind,Struct0,Struct1) :- !, shfrnv_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(shfrnv,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shfrnv_input_user_interface(InputUser,Qv,ASub).
asub_to_native(shfrnv,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shfrnv_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(shfrnv,Sg,Vars,Call,Succ) :- !, shfr_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(shfrnv,Sg,Qv,Call) :- !, shfr_unknown_entry(Sg,Qv,Call).
empty_entry(shfrnv,Sg,Qv,Call) :- !, shfr_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
%% propagate_downwards_closed(shfrnv,ASub1,ASub2,ASub) :- !, shfrnv_downwards_closed(ASub1,ASub2,ASub).
%% del_real_conjoin(shfrnv,ASub1,ASub2,ASub) :- !, shfrnv_real_conjoin(ASub1,ASub2,ASub).
%% del_hash(shfrnv,ASub,Vars,N) :- !, shfrnv_hash(ASub,Vars,N).
%% more_instantiate(shfrnv,ASub1,ASub2) :- !, shfrnv_more_instantiate(ASub1,ASub2).
%% convex_hull(shfrnv,Old,New,Hull) :- !, shfrnv_convex_hull(Old,New,Hull).
%% compute_lub_el(shfrnv,ASub1,ASub2,ASub) :- !, shfrnv_compute_lub_el(ASub1,ASub2,ASub).
%% extend_free(shfrnv,ASub1,Vars,ASub) :- !, shfr_extend_free(ASub1,Vars,ASub).
%% del_check_cond(shfrnv,Cond,ASub,Sv,Flag,WConds) :- !, shfrnv_check_cond(Cond,ASub,Sv,Flag,WConds).
%% del_impose_cond(shfrnv,LCond,Sv,ASub,LASub) :- !, shfrnv_impose_cond(LCond,Sv,ASub,LASub).
%
%% shfrnv_check_cond(_,_,_,_,_).
%% shfrnv_compute_lub_el(_,_,_).  
%% shfrnv_convex_hull(_,_,_).
%% shfrnv_downwards_closed(_,_,_). 
%% shfrnv_hash(_,_,_).    
%% shfrnv_impose_cond(_,_,_,_).
%% shfrnv_more_instantiate(_,_). 
%% shfrnv_real_conjoin(_,_,_).
shfrnv_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ---------------------------------------------------------------------------
:- use_module(domain(shfret)).
%aidomain(shfret). % TODO: it was missing, disabled?
init_abstract_domain(shfret,PushedFlags) :- !, shfret_init_abstract_domain(PushedFlags).
call_to_entry(shfret,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfret_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(shfret,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, shfret_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(shfret,_Sg,Vars,_HvFv,ASub,Proj) :- !, shfret_project(ASub,Vars,Proj).
widencall(shfret,Prime0,Prime1,NewPrime) :- !, shfret_widencall(Prime0,Prime1,NewPrime).
widen(shfret,Prime0,Prime1,NewPrime) :- !, shfret_widen(Prime0,Prime1,NewPrime).
compute_lub(shfret,ListAsub,LubASub) :- !, shfret_compute_lub(ListAsub,LubASub).
identical_abstract(shfret,ASub1,ASub2) :- !, shfret_identical_abstract(ASub1,ASub2).
abs_sort(shfret,ASub,ASub_s) :- !, shfret_sort(ASub,ASub_s).
extend(shfret,_Sg,Prime,Sv,Call,Succ) :- !, shfret_extend(Prime,Sv,Call,Succ).
less_or_equal(shfret,ASub0,ASub1) :- !, shfret_less_or_equal(ASub0,ASub1).
glb(shfret,ASub0,ASub1,ASub) :- !, shfret_glb(ASub0,ASub1,ASub).
eliminate_equivalent(shfret,TmpLSucc,LSucc) :- !, shfret_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(shfret,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, shfret_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
combined_special_builtin(shfret,SgKey,Domains) :- !, shfret_combined_special_builtin(SgKey,Domains).
split_combined_domain(shfret,ASub,ASubs,Doms) :- !, shfret_split_combined_domain(ASub,ASubs,Doms).
input_interface(shfret,InputUser,Kind,Struct0,Struct1) :- !, shfret_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(shfret,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shfret_input_user_interface(InputUser,Qv,ASub).
asub_to_native(shfret,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shfret_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(shfret,Sg,Vars,Call,Succ) :- !, shfret_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(shfret,Sg,Qv,Call) :- !, shfret_unknown_entry(Sg,Qv,Call).
empty_entry(shfret,Sg,Qv,Call) :- !, shfret_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
shfret_init_abstract_domain([variants,widen]) :-
	push_pp_flag(variants,off),
	push_pp_flag(widen,on).
shfret_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)
shfret_combined_special_builtin(SgKey,Domains) :-
	% TODO: refactor (define a nondet pred with combined domains instead)
	( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr]
	; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr]
	; fail
	).
% ---------------------------------------------------------------------------
:- use_module(domain(shareson)).
aidomain(shareson).
call_to_entry(shareson,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shareson_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(shareson,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, shareson_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(shareson,_Sg,Vars,_HvFv,ASub,Proj) :- !, shareson_project(Vars,ASub,Proj).
compute_lub(shareson,ListAsub,LubASub) :- !, shareson_compute_lub(ListAsub,LubASub).
abs_sort(shareson,ASub,ASub_s) :- !, shareson_sort(ASub,ASub_s).
extend(shareson,_Sg,Prime,Sv,Call,Succ) :- !, shareson_extend(Prime,Sv,Call,Succ).
less_or_equal(shareson,ASub0,ASub1) :- !, shareson_less_or_equal(ASub0,ASub1).
glb(shareson,ASub0,ASub1,ASub) :- !, shareson_glb(ASub0,ASub1,ASub).
call_to_success_fact(shareson,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, shareson_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(shareson,SgKey,Sg,_Subgoal,(TypeSon,TypeSh),(CondSon,CondSh)) :- !, share_special_builtin(SgKey,Sg,TypeSh,CondSh), son_special_builtin(SgKey,Sg,TypeSon,CondSon).
body_succ_builtin(shareson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- !, shareson_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
input_interface(shareson,InputUser,Kind,Struct0,Struct1) :- !, shareson_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(shareson,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shareson_input_user_interface(InputUser,Qv,ASub).
asub_to_native(shareson,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shareson_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(shareson,Sg,Vars,Call,Succ) :- !, shareson_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(shareson,Sg,Qv,Call) :- !, shareson_unknown_entry(Sg,Qv,Call).
empty_entry(shareson,Sg,Qv,Call) :- !, shareson_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
% TODO: These do have special(_), special care (old comment)
shareson_body_succ_builtin((TSon,TSh),Sg,(CSon,CSh),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_son,Call_sh),
	Proj=(Proj_son,Proj_sh),
	body_succ_builtin(son,TSon,Sg,CSon,Sv,HvFv,Call_son,Proj_son,Succ_son),
	body_succ_builtin(share,TSh,Sg,CSh,Sv,HvFv,Call_sh,Proj_sh,Succ_sh),
	shareson_compose(Call,Succ_sh,Succ_son,Succ).
shareson_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
	body_builtin(shareson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
shareson_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ---------------------------------------------------------------------------
:- use_module(domain(shfrson)).
aidomain(shfrson).
call_to_entry(shfrson,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfrson_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(shfrson,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, shfrson_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(shfrson,_Sg,Vars,_HvFv,ASub,Proj) :- !, shfrson_project(Vars,ASub,Proj).
compute_lub(shfrson,ListAsub,LubASub) :- !, shfrson_compute_lub(ListAsub,LubASub).
abs_sort(shfrson,ASub,ASub_s) :- !, shfrson_sort(ASub,ASub_s).
extend(shfrson,_Sg,Prime,Sv,Call,Succ) :- !, shfrson_extend(Prime,Sv,Call,Succ).
less_or_equal(shfrson,ASub0,ASub1) :- !, shfrson_less_or_equal(ASub0,ASub1).
glb(shfrson,ASub0,ASub1,ASub) :- !, shfrson_glb(ASub0,ASub1,ASub).
call_to_success_fact(shfrson,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, shfrson_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(shfrson,SgKey,Sg,_Subgoal,(TypeSon,TypeSh),(CondSon,CondSh)) :- !, shfr_special_builtin(SgKey,Sg,TypeSh,CondSh), son_special_builtin(SgKey,Sg,TypeSon,CondSon).
body_succ_builtin(shfrson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- !, shfrson_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
input_interface(shfrson,InputUser,Kind,Struct0,Struct1) :- !, shfrson_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(shfrson,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shfrson_input_user_interface(InputUser,Qv,ASub).
asub_to_native(shfrson,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shfrson_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(shfrson,Sg,Vars,Call,Succ) :- !, shfrson_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(shfrson,Sg,Qv,Call) :- !, shfrson_unknown_entry(Sg,Qv,Call).
empty_entry(shfrson,Sg,Qv,Call) :- !, shfrson_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
% TODO: These do have special(_), special care (old comment)
shfrson_body_succ_builtin((TSon,TSh),Sg,(CSon,CSh),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_son,Call_sh),
	Proj=(Proj_son,Proj_sh),
	body_succ_builtin(son,TSon,Sg,CSon,Sv,HvFv,Call_son,Proj_son,Succ_son),
	body_succ_builtin(shfr,TSh,Sg,CSh,Sv,HvFv,Call_sh,Proj_sh,Succ_sh),
	shfrson_compose(Call,Succ_sh,Succ_son,Succ).
shfrson_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
	body_builtin(shfrson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
shfrson_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ---------------------------------------------------------------------------
:- use_module(domain(sondergaard)).
aidomain(son).
call_to_entry(son,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, son_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(son,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, son_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(son,_Sg,Vars,_HvFv,ASub,Proj) :- !, son_project(Vars,ASub,Proj).
compute_lub(son,ListAsub,LubASub) :- !, son_compute_lub(ListAsub,LubASub).
abs_sort(son,ASub,ASub_s) :- !, son_sort(ASub,ASub_s).
extend(son,_Sg,Prime,Sv,Call,Succ) :- !, son_extend(Prime,Sv,Call,Succ).
less_or_equal(son,ASub0,ASub1) :- !, son_less_or_equal(ASub0,ASub1).
glb(son,ASub0,ASub1,ASub) :- !, son_glb(ASub0,ASub1,ASub).
call_to_success_fact(son,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, son_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(son,SgKey,Sg,_Subgoal,Type,Condvars) :- !, son_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(son,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, son_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(son,SgKey,Sg,Sv,Call,Proj,Succ) :- !, son_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(son,InputUser,Kind,Struct0,Struct1) :- !, son_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(son,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, son_input_user_interface(InputUser,Qv,ASub).
asub_to_native(son,ASub,Qv,OutFlag,OutputUser,Comps) :- !, son_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(son,Sg,Vars,Call,Succ) :- !, son_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(son,Sg,Qv,Call) :- !, son_unknown_entry(Sg,Qv,Call).
empty_entry(son,Sg,Qv,Call) :- !, son_empty_entry(Sg,Qv,Call).
%% compute_lub_el(son,ASub1,ASub2,ASub) :- !, son_lub(ASub1,ASub2,ASub).
% ---------------------------------------------------------------------------
:- use_module(domain(sharing_amgu)).
aidomain(share_amgu).
amgu(share_amgu,Sg,Head,ASub,NewASub) :- !, share_amgu(Sg,Head,ASub,NewASub).
augment_asub(share_amgu,ASub,Vars,ASub0) :- !, share_amgu_extend_asub(ASub,Vars,ASub0).
augment_two_asub(share_amgu,ASub0,ASub1,ASub) :- !, share_amgu_extend_two_asub(ASub0,ASub1,ASub).
call_to_entry(share_amgu,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, share_amgu_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(share_amgu,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, share_amgu_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(share_amgu,_Sg,Vars,_HvFv,ASub,Proj) :- !, share_project(Vars,ASub,Proj).
compute_lub(share_amgu,ListAsub,LubASub) :- !, share_compute_lub(ListAsub,LubASub).
abs_sort(share_amgu,ASub,ASub_s) :- !, share_sort(ASub,ASub_s).
extend(share_amgu,_Sg,Prime,Sv,Call,Succ) :- !, share_extend(Prime,Sv,Call,Succ).
less_or_equal(share_amgu,ASub0,ASub1) :- !, share_less_or_equal(ASub0,ASub1).
glb(share_amgu,ASub0,ASub1,ASub) :- !, share_glb(ASub0,ASub1,ASub).
call_to_success_fact(share_amgu,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, share_amgu_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(share_amgu,SgKey,Sg,_Subgoal,Type,Condvars) :- !, share_amgu_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(share_amgu,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, share_amgu_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(share_amgu,SgKey,Sg,Sv,Call,Proj,Succ) :- !, share_amgu_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(share_amgu,InputUser,Kind,Struct0,Struct1) :- !, share_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(share_amgu,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, share_input_user_interface(InputUser,Qv,ASub).
asub_to_native(share_amgu,ASub,Qv,OutFlag,OutputUser,Comps) :- !, share_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(share_amgu,Sg,Vars,Call,Succ) :- !, share_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(share_amgu,Sg,Qv,Call) :- !, share_unknown_entry(Sg,Qv,Call).
empty_entry(share_amgu,Sg,Qv,Call) :- !, share_empty_entry(Sg,Qv,Call).
%% compute_lub_el(share_amgu,ASub1,ASub2,ASub) :- !, share_lub(ASub1,ASub2,ASub).
% ----------
:- use_module(domain(sharefree_amgu)).
aidomain(sharefree_amgu).
amgu(sharefree_amgu,Sg,Head,ASub,NewASub) :- !, sharefree_amgu(Sg,Head,ASub,NewASub).
augment_asub(sharefree_amgu,ASub,Vars,ASub0) :- !, sharefree_amgu_extend_asub(ASub,Vars,ASub0).
call_to_entry(sharefree_amgu,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, sharefree_amgu_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(sharefree_amgu,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, sharefree_amgu_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(sharefree_amgu,_Sg,Vars,_HvFv,ASub,Proj) :- !, shfr_project(ASub,Vars,Proj).
compute_lub(sharefree_amgu,ListAsub,LubASub) :- !, shfr_compute_lub(ListAsub,LubASub).
abs_sort(sharefree_amgu,ASub,ASub_s) :- !, shfr_sort(ASub,ASub_s).
extend(sharefree_amgu,_Sg,Prime,Sv,Call,Succ) :- !, shfr_extend(Prime,Sv,Call,Succ).
less_or_equal(sharefree_amgu,ASub0,ASub1) :- !, shfr_less_or_equal(ASub0,ASub1).
glb(sharefree_amgu,ASub0,ASub1,ASub) :- !, shfr_glb(ASub0,ASub1,ASub).
call_to_success_fact(sharefree_amgu,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, sharefree_amgu_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(sharefree_amgu,SgKey,Sg,_Subgoal,Type,Condvars) :- !, sharefree_amgu_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(sharefree_amgu,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, sharefree_amgu_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(sharefree_amgu,SgKey,Sg,Sv,Call,Proj,Succ) :- !, sharefree_amgu_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(sharefree_amgu,Prop,Vars,ASub,Info) :- !, shfr_obtain(Prop,Vars,ASub,Info).
input_interface(sharefree_amgu,InputUser,Kind,Struct0,Struct1) :- !, shfr_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(sharefree_amgu,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shfr_input_user_interface(InputUser,Qv,ASub).
asub_to_native(sharefree_amgu,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shfr_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(sharefree_amgu,Sg,Vars,Call,Succ) :- !, shfr_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(sharefree_amgu,Sg,Qv,Call) :- !, shfr_unknown_entry(Sg,Qv,Call).
empty_entry(sharefree_amgu,Sg,Qv,Call) :- !, shfr_empty_entry(Sg,Qv,Call).
% ----------
:- use_module(domain(shfrlin_amgu)).
aidomain(shfrlin_amgu).
amgu(shfrlin_amgu,Sg,Head,ASub,NewASub) :- !, shfrlin_amgu(Sg,Head,ASub,NewASub).
augment_asub(shfrlin_amgu,ASub,Vars,ASub0) :- !, shfrlin_extend_asub(ASub,Vars,ASub0).
call_to_entry(shfrlin_amgu,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfrlin_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(shfrlin_amgu,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, shfrlin_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(shfrlin_amgu,_Sg,Vars,_HvFv,ASub,Proj) :- !, shfrlin_project(ASub,Vars,Proj).
compute_lub(shfrlin_amgu,ListAsub,LubASub) :- !, shfrlin_compute_lub(ListAsub,LubASub).
abs_sort(shfrlin_amgu,ASub,ASub_s) :- !, shfrlin_sort(ASub,ASub_s).
extend(shfrlin_amgu,_Sg,Prime,Sv,Call,Succ) :- !, shfrlin_extend(Prime,Sv,Call,Succ).
less_or_equal(shfrlin_amgu,ASub0,ASub1) :- !, shfrlin_less_or_equal(ASub0,ASub1).
glb(shfrlin_amgu,ASub0,ASub1,ASub) :- !, shfrlin_glb(ASub0,ASub1,ASub).
call_to_success_fact(shfrlin_amgu,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, shfrlin_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(shfrlin_amgu,SgKey,Sg,_Subgoal,Type,Condvars) :- !, shfrlin_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(shfrlin_amgu,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, shfrlin_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(shfrlin_amgu,SgKey,Sg,Sv,Call,Proj,Succ) :- !, shfrlin_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(shfrlin_amgu,Prop,Vars,(Sh,Fr,_Lin),Info) :- !, shfr_obtain(Prop,Vars,(Sh,Fr),Info).
input_interface(shfrlin_amgu,InputUser,Kind,Struct0,Struct1) :- !, shfrlin_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(shfrlin_amgu,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, shfrlin_input_user_interface(InputUser,Qv,ASub).
asub_to_native(shfrlin_amgu,ASub,Qv,OutFlag,OutputUser,Comps) :- !, shfrlin_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(shfrlin_amgu,Sg,Vars,Call,Succ) :- !, shfrlin_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(shfrlin_amgu,Sg,Qv,Call) :- !, shfrlin_unknown_entry(Sg,Qv,Call).
empty_entry(shfrlin_amgu,Sg,Qv,Call) :- !, shfrlin_empty_entry(Sg,Qv,Call).
% ---------------------------------------------------------------------------
:- use_module(domain(sharing_clique)).
aidomain(share_clique).
amgu(share_clique,Sg,Head,ASub,NewASub) :- !, share_clique_amgu(Sg,Head,ASub,NewASub).
augment_asub(share_clique,ASub,Vars,ASub0) :- !, share_clique_extend_asub(ASub,Vars,ASub0).
call_to_entry(share_clique,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, share_clique_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(share_clique,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, share_clique_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(share_clique,_Sg,Vars,_HvFv,ASub,Proj) :- !, share_clique_project(Vars,ASub,Proj).
compute_lub(share_clique,ListAsub,LubASub) :- !, share_clique_compute_lub(ListAsub,LubASub).
identical_abstract(share_clique,ASub1,ASub2) :- !, share_clique_identical_abstract(ASub1,ASub2).
abs_sort(share_clique,ASub,ASub_s) :- !, share_clique_sort(ASub,ASub_s).
extend(share_clique,_Sg,Prime,Sv,Call,Succ) :- !, share_clique_extend(Prime,Sv,Call,Succ).
less_or_equal(share_clique,ASub0,ASub1) :- !, share_clique_less_or_equal(ASub0,ASub1).
glb(share_clique,ASub0,ASub1,ASub) :- !, share_clique_glb(ASub0,ASub1,ASub).
eliminate_equivalent(share_clique,TmpLSucc,LSucc) :- !, share_clique_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(share_clique,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, share_clique_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(share_clique,SgKey,Sg,_Subgoal,Type,Condvars) :- !, share_clique_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(share_clique,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, share_clique_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(share_clique,SgKey,Sg,Sv,Call,Proj,Succ) :- !, share_clique_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(share_clique,InputUser,Kind,Struct0,Struct1) :- !, share_clique_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(share_clique,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, share_clique_input_user_interface(InputUser,Qv,ASub).
asub_to_native(share_clique,ASub,Qv,OutFlag,OutputUser,Comps) :- !, share_clique_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(share_clique,Sg,Vars,Call,Succ) :- !, share_clique_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(share_clique,Sg,Qv,Call) :- !, share_clique_unknown_entry(Sg,Qv,Call).
empty_entry(share_clique,Sg,Qv,Call) :- !, share_clique_empty_entry(Sg,Qv,Call).
%% compute_lub_el(share_clique,ASub1,ASub2,ASub) :- !, share_clique_lub_cl(ASub1,ASub2,ASub).
% ----------
:- use_module(domain(sharing_clique_1)).
aidomain(share_clique_1).
call_to_entry(share_clique_1,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, share_clique_1_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(share_clique_1,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, share_clique_1_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(share_clique_1,_Sg,Vars,_HvFv,ASub,Proj) :- !, share_clique_1_project(Vars,ASub,Proj).
compute_lub(share_clique_1,ListAsub,LubASub) :- !, share_clique_1_compute_lub(ListAsub,LubASub).
identical_abstract(share_clique_1,ASub1,ASub2) :- !, share_clique_1_identical_abstract(ASub1,ASub2).
abs_sort(share_clique_1,ASub,ASub_s) :- !, share_clique_sort(ASub,ASub_s).
extend(share_clique_1,_Sg,Prime,Sv,Call,Succ) :- !, share_clique_1_extend(Prime,Sv,Call,Succ).
less_or_equal(share_clique_1,ASub0,ASub1) :- !, share_clique_1_less_or_equal(ASub0,ASub1).
glb(share_clique_1,ASub0,ASub1,ASub) :- !, share_clique_1_glb(ASub0,ASub1,ASub).
eliminate_equivalent(share_clique_1,TmpLSucc,LSucc) :- !, share_clique_1_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(share_clique_1,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, share_clique_1_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(share_clique_1,SgKey,Sg,_Subgoal,Type,Condvars) :- !, share_clique_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(share_clique_1,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, share_clique_1_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(share_clique_1,SgKey,Sg,Sv,Call,Proj,Succ) :- !, share_clique_1_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(share_clique_1,InputUser,Kind,Struct0,Struct1) :- !, share_clique_1_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(share_clique_1,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, share_clique_input_user_interface(InputUser,Qv,ASub).
asub_to_native(share_clique_1,ASub,Qv,OutFlag,OutputUser,Comps) :- !, share_clique_1_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(share_clique_1,Sg,Vars,Call,Succ) :- !, share_clique_1_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(share_clique_1,Sg,Qv,Call) :- !, share_clique_1_unknown_entry(Sg,Qv,Call).
empty_entry(share_clique_1,Sg,Qv,Call) :- !, share_clique_empty_entry(Sg,Qv,Call).
%% compute_lub_el(share_clique_1,ASub1,ASub2,ASub) :- !, share_clique_1_lub_cl(ASub1,ASub2,ASub).
% ----------
:- use_module(domain(sharefree_clique)).
aidomain(sharefree_clique).
amgu(sharefree_clique,Sg,Head,ASub,NewASub) :- !, sharefree_clique_amgu(Sg,Head,ASub,NewASub).
augment_asub(sharefree_clique,ASub,Vars,ASub0) :- !, sharefree_clique_extend_asub(ASub,Vars,ASub0).
call_to_entry(sharefree_clique,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, sharefree_clique_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(sharefree_clique,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, sharefree_clique_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(sharefree_clique,_Sg,Vars,_HvFv,ASub,Proj) :- !, sharefree_clique_project(ASub,Vars,Proj).
compute_lub(sharefree_clique,ListAsub,LubASub) :- !, sharefree_clique_compute_lub(ListAsub,LubASub).
identical_abstract(sharefree_clique,ASub1,ASub2) :- !, sharefree_clique_identical_abstract(ASub1,ASub2).
abs_sort(sharefree_clique,ASub,ASub_s) :- !, sharefree_clique_sort(ASub,ASub_s).
extend(sharefree_clique,_Sg,Prime,Sv,Call,Succ) :- !, sharefree_clique_extend(Prime,Sv,Call,Succ).
less_or_equal(sharefree_clique,ASub0,ASub1) :- !, sharefree_clique_less_or_equal(ASub0,ASub1).
glb(sharefree_clique,ASub0,ASub1,ASub) :- !, sharefree_clique_glb(ASub0,ASub1,ASub).
eliminate_equivalent(sharefree_clique,TmpLSucc,LSucc) :- !, sharefree_clique_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(sharefree_clique,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, sharefree_clique_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(sharefree_clique,SgKey,Sg,_Subgoal,Type,Condvars) :- !, sharefree_clique_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(sharefree_clique,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, sharefree_clique_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(sharefree_clique,SgKey,Sg,Sv,Call,Proj,Succ) :- !, sharefree_clique_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(sharefree_clique,Prop,Vars,ASub,Info) :- !, shfr_obtain(Prop,Vars,ASub,Info).
input_interface(sharefree_clique,InputUser,Kind,Struct0,Struct1) :- !, sharefree_clique_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(sharefree_clique,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, sharefree_clique_input_user_interface(InputUser,Qv,ASub).
asub_to_native(sharefree_clique,ASub,Qv,OutFlag,OutputUser,Comps) :- !, sharefree_clique_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(sharefree_clique,Sg,Vars,Call,Succ) :- !, sharefree_clique_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(sharefree_clique,Sg,Qv,Call) :- !, sharefree_clique_unknown_entry(Sg,Qv,Call).
empty_entry(sharefree_clique,Sg,Qv,Call) :- !, sharefree_clique_empty_entry(Sg,Qv,Call).
%% compute_lub_el(sharefree_clique,ASub1,ASub2,ASub) :- !, sharefree_clique_compute_lub_el(ASub1,ASub2,ASub).
% ----------
:- use_module(domain(sharing_clique_def)).
aidomain(share_clique_def).
call_to_entry(share_clique_def,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, share_clique_def_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(share_clique_def,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, share_clique_def_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(share_clique_def,_Sg,Vars,_HvFv,ASub,Proj) :- !, share_clique_def_project(Vars,ASub,Proj).
compute_lub(share_clique_def,ListAsub,LubASub) :- !, share_clique_def_compute_lub(ListAsub,LubASub).
identical_abstract(share_clique_def,ASub1,ASub2) :- !, share_clique_def_identical_abstract(ASub1,ASub2).
abs_sort(share_clique_def,ASub,ASub_s) :- !, share_clique_def_sort(ASub,ASub_s).
extend(share_clique_def,_Sg,Prime,Sv,Call,Succ) :- !, share_clique_def_extend(Prime,Sv,Call,Succ).
less_or_equal(share_clique_def,ASub0,ASub1) :- !, share_clique_def_less_or_equal(ASub0,ASub1).
glb(share_clique_def,ASub0,ASub1,ASub) :- !, share_clique_def_glb(ASub0,ASub1,ASub).
eliminate_equivalent(share_clique_def,TmpLSucc,LSucc) :- !, share_clique_def_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(share_clique_def,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, share_clique_def_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(share_clique_def,SgKey,Sg,_Subgoal,Type,Condvars) :- !, share_clique_def_special_builtin(SgKey,Sg,Type,Condvars).
body_succ_builtin(share_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- !, share_clique_def_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
input_interface(share_clique_def,InputUser,Kind,Struct0,Struct1) :- !, share_clique_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(share_clique_def,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, share_clique_def_input_user_interface(InputUser,Qv,ASub).
asub_to_native(share_clique_def,ASub,Qv,OutFlag,OutputUser,Comps) :- !, share_clique_def_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(share_clique_def,Sg,Vars,Call,Succ) :- !, share_clique_def_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(share_clique_def,Sg,Qv,Call) :- !, share_clique_def_unknown_entry(Sg,Qv,Call).
empty_entry(share_clique_def,Sg,Qv,Call) :- !, share_clique_def_empty_entry(Sg,Qv,Call).
%% compute_lub_el(share_clique_def,ASub1,ASub2,ASub) :- !, share_clique_def_lub_cl(ASub1,ASub2,ASub).
%
share_clique_def_body_succ_builtin((TSH,not_defined),Sg,(CSH,_),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_SH,Call_def),
	Proj=(Proj_SH,_Proj_def),
	body_succ_builtin(share_clique,TSH,Sg,CSH,Sv,HvFv,Call_SH,Proj_SH,Succ_SH),
	Succ = (Succ_SH,Call_def).
share_clique_def_body_succ_builtin((TSH,Tdef),Sg,(CSH,Cdef),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_SH,Call_def),
	Proj=(Proj_SH,Proj_def),
	body_succ_builtin(def,Tdef,Sg,Cdef,Sv,HvFv,Call_def,Proj_def,Succ_def),
	share_clique_def_compose((Call_SH,Succ_def),NewCall_SH),
	share_clique_def_compose((Proj_SH,Succ_def),NewProj_SH),
	body_succ_builtin(share_clique,TSH,Sg,CSH,Sv,HvFv,NewCall_SH,NewProj_SH,Succ_SH),
	Succ = (Succ_SH,Succ_def).
share_clique_def_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
	body_builtin(share_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
% ----------
:- use_module(domain(sharefree_clique_def)).
aidomain(sharefree_clique_def).
call_to_entry(sharefree_clique_def,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, sharefree_clique_def_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(sharefree_clique_def,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, sharefree_clique_def_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(sharefree_clique_def,_Sg,Vars,_HvFv,ASub,Proj) :- !, sharefree_clique_def_project(Vars,ASub,Proj).
compute_lub(sharefree_clique_def,ListAsub,LubASub) :- !, sharefree_clique_def_compute_lub(ListAsub,LubASub).
identical_abstract(sharefree_clique_def,ASub1,ASub2) :- !, sharefree_clique_def_identical_abstract(ASub1,ASub2).
abs_sort(sharefree_clique_def,ASub,ASub_s) :- !, sharefree_clique_def_sort(ASub,ASub_s).
extend(sharefree_clique_def,_Sg,Prime,Sv,Call,Succ) :- !, sharefree_clique_def_extend(Prime,Sv,Call,Succ).
less_or_equal(sharefree_clique_def,ASub0,ASub1) :- !, sharefree_clique_def_less_or_equal(ASub0,ASub1).
glb(sharefree_clique_def,ASub0,ASub1,ASub) :- !, sharefree_clique_def_glb(ASub0,ASub1,ASub).
eliminate_equivalent(sharefree_clique_def,TmpLSucc,LSucc) :- !, sharefree_clique_def_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(sharefree_clique_def,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, sharefree_clique_def_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(sharefree_clique_def,SgKey,Sg,_Subgoal,Type,Condvars) :- !, sharefree_clique_def_special_builtin(SgKey,Sg,Type,Condvars).
body_succ_builtin(sharefree_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- !, sharefree_clique_def_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
input_interface(sharefree_clique_def,InputUser,Kind,Struct0,Struct1) :- !, sharefree_clique_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(sharefree_clique_def,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, sharefree_clique_def_input_user_interface(InputUser,Qv,ASub).
asub_to_native(sharefree_clique_def,ASub,Qv,OutFlag,OutputUser,Comps) :- !, sharefree_clique_def_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(sharefree_clique_def,Sg,Vars,Call,Succ) :- !, sharefree_clique_def_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(sharefree_clique_def,Sg,Qv,Call) :- !, sharefree_clique_def_unknown_entry(Sg,Qv,Call).
empty_entry(sharefree_clique_def,Sg,Qv,Call) :- !, sharefree_clique_def_empty_entry(Sg,Qv,Call).
%% compute_lub_el(sharefree_clique_def,ASub1,ASub2,ASub) :- !, sharefree_clique_def_lub_cl(ASub1,ASub2,ASub).
%
sharefree_clique_def_body_succ_builtin((TSHF,not_defined),Sg,(CSHF,_),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_SHF,Call_def),
	Proj=(Proj_SHF,_Proj_def),
	body_succ_builtin(sharefree_clique,TSHF,Sg,CSHF,Sv,HvFv,Call_SHF,Proj_SHF,Succ_SHF),
	Succ = (Succ_SHF,Call_def).
sharefree_clique_def_body_succ_builtin((TSHF,Tdef),Sg,(CSHF,Cdef),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_SHF,Call_def),
	Proj=(Proj_SHF,Proj_def),
	body_succ_builtin(def,Tdef,Sg,Cdef,Sv,HvFv,Call_def,Proj_def,Def_succ),
	sharefree_clique_def_compose(Call_SHF,Def_succ,NewCall_SHF),
	sharefree_clique_def_compose(Proj_SHF,Def_succ,NewProj_SHF),
	body_succ_builtin(sharefree_clique,TSHF,Sg,CSHF,Sv,HvFv,NewCall_SHF,NewProj_SHF,Succ_SHF),
	unify_asub_if_bottom((Succ_SHF,Def_succ),Succ),!.
sharefree_clique_def_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
	body_builtin(sharefree_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(bshare/bshare)).
aidomain(bshare).
amgu(bshare,Sg,Head,ASub,NewASub) :- !, bshare_amgu(Sg,Head,ASub,NewASub).
augment_asub(bshare,ASub,Vars,ASub0) :- !, bshare_extend_asub(ASub,Vars,ASub0).
augment_two_asub(bshare,ASub0,ASub1,ASub) :- !, bshare_augment_two_asub(ASub0,ASub1,ASub).
call_to_entry(bshare,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, bshare_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
project(bshare,_Sg,Vars,_HvFv,ASub,Proj) :- !, bshare_project(Vars,ASub,Proj).
compute_lub(bshare,ListAsub,LubASub) :- !, bshare_compute_lub(ListAsub,LubASub).
identical_abstract(bshare,ASub1,ASub2) :- !, bshare_identical_abstract(ASub1,ASub2).
abs_sort(bshare,ASub,ASub_s) :- !, bshare_sort(ASub,ASub_s).
call_to_success_fact(bshare,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, bshare_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(bshare,SgKey,Sg,_Subgoal,Type,Condvars) :- !, bshare_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(bshare,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, bshare_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(bshare,SgKey,Sg,Sv,Call,Proj,Succ) :- !, bshare_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
asub_to_native(bshare,ASub,Qv,OutFlag,OutputUser,Comps) :- !, bshare_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_entry(bshare,Sg,Qv,Call) :- !, bshare_unknown_entry(Sg,Qv,Call).
empty_entry(bshare,Sg,Qv,Call) :- !, bshare_empty_entry(Sg,Qv,Call).
%% compute_lub_el(bshare,ASub1,ASub2,ASub) :- !, bshare_compute_lub_el(ASub1,ASub2,ASub).
:- endif.
% ===========================================================================
:- doc(section, "Structure domains"). % TODO: shape also?
% ---------------------------------------------------------------------------
:- use_module(domain(aeq_top)).
aidomain(aeq).
call_to_entry(aeq,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, aeq_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(aeq,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, aeq_exit_to_prime(Exit,Sg,Hv,Head,Sv,ExtraInfo,Prime).
project(aeq,_Sg,Vars,_HvFv,ASub,Proj) :- !, aeq_project(ASub,Vars,Proj).
compute_lub(aeq,ListASub,LubASub) :- !, aeq_compute_lub(ListASub,LubASub).
identical_abstract(aeq,ASub1,ASub2) :- !, aeq_identical_abstract(ASub1,ASub2).
abs_sort(aeq,ASub,ASub_s) :- !, aeq_sort(ASub,ASub_s).
extend(aeq,_Sg,Prime,_Sv,Call,Succ) :- !, aeq_extend(Prime,Call,Succ).
less_or_equal(aeq,ASub0,ASub1) :- !, aeq_less_or_equal(ASub0,ASub1).
glb(aeq,ASub0,ASub1,ASub) :- !, aeq_glb(ASub0,ASub1,ASub).
eliminate_equivalent(aeq,TmpLSucc,LSucc) :- !, aeq_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(aeq,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, aeq_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(aeq,Sg_key,Sg,_Subgoal,Type,Condvars) :- !, aeq_special_builtin(Sg_key,Sg,Type,Condvars).
success_builtin(aeq,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, aeq_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
input_interface(aeq,InputUser,Kind,Struct0,Struct1) :- !, aeq_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(aeq,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, aeq_input_user_interface(InputUser,Qv,ASub).
asub_to_native(aeq,ASub,Qv,OutFlag,OutputUser,Comps) :- !, aeq_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(aeq,Sg,Vars,Call,Succ) :- !, aeq_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(aeq,Sg,Qv,Call) :- !, aeq_unknown_entry(Sg,Qv,Call).
empty_entry(aeq,Sg,Qv,Call) :- !, aeq_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
%% propagate_downwards_closed(aeq,ASub1,ASub2,ASub) :- !, aeq_downwards_closed(ASub1,ASub2,ASub).
%% del_real_conjoin(aeq,ASub1,ASub2,ASub) :- !, aeq_real_conjoin(ASub1,ASub2,ASub).
%% del_hash(aeq,ASub,Vars,N) :- !, aeq_hash(ASub,Vars,N).
%% more_instantiate(aeq,ASub1,ASub2) :- !, aeq_more_instantiate(ASub1,ASub2).
%% convex_hull(aeq,Old,New,Hull) :- !, aeq_convex_hull(Old,New,Hull).
%% compute_lub_el(aeq,ASub1,ASub2,ASub) :- !, aeq_lub(ASub1,ASub2,ASub).
%% extend_free(aeq,ASub1,Vars,ASub) :- !, aeq_extend_free(ASub1,Vars,ASub).
%% del_check_cond(aeq,Cond,ASub,Sv,Flag,WConds) :- !, aeq_check_cond(Cond,ASub,Sv,Flag,WConds).
%% del_impose_cond(aeq,LCond,Sv,ASub,LASub) :- !, aeq_impose_cond(LCond,Sv,ASub,LASub).
%
%% aeq_check_cond(_,_,_,_,_). 
%% aeq_convex_hull(_,_,_).
%% aeq_downwards_closed(_,_,_).
%% aeq_extend_free(_,_,_).
%% aeq_hash(_,_,_).       
%% aeq_impose_cond(_,_,_,_).
%% aeq_lub(_,_,_).        
%% aeq_more_instantiate(_,_). 
%% aeq_real_conjoin(_,_,_).
aeq_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
aeq_eliminate_equivalent(TmpLSucc,LSucc) :- absub_eliminate_equivalent(TmpLSucc,aeq,LSucc).
% ---------------------------------------------------------------------------
:- use_module(domain(depthk)).
aidomain(depth).
call_to_entry(depth,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, depthk_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(depth,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, depthk_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(depth,_Sg,Vars,_HvFv,ASub,Proj) :- !, depthk_project(Vars,ASub,Proj).
compute_lub(depth,ListASub,LubASub) :- !, depthk_compute_lub(ListASub,LubASub).
identical_abstract(depth,ASub1,ASub2) :- !, depthk_identical_abstract(ASub1,ASub2).
abs_sort(depth,ASub,ASub_s) :- !, depthk_sort(ASub,ASub_s).
extend(depth,_Sg,Prime,Sv,Call,Succ) :- !, depthk_extend(Prime,Sv,Call,Succ).
less_or_equal(depth,ASub0,ASub1) :- !, depthk_less_or_equal(ASub0,ASub1).
glb(depth,ASub0,ASub1,ASub) :- !, depthk_glb(ASub0,ASub1,ASub).
eliminate_equivalent(depth,TmpLSucc,LSucc) :- !, depthk_eliminate_equivalent(TmpLSucc,LSucc).
abs_subset(depth,LASub1,LASub2) :- !, depthk_abs_subset(LASub1,LASub2).
call_to_success_fact(depth,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, depthk_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(depth,SgKey,Sg,_Subgoal,Type,Condvars) :- !, depthk_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(depth,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, depthk_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(depth,_SgKey,Sg,Sv,Call,_Proj,Succ) :- !, depthk_call_to_success_builtin(Sg,Sv,Call,Succ).
input_interface(depth,InputUser,Kind,Struct0,Struct1) :- !, depthk_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(depth,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, depthk_input_user_interface(InputUser,Qv,ASub).
asub_to_native(depth,ASub,Qv,OutFlag,OutputUser,Comps) :- !, depthk_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(depth,Sg,Vars,Call,Succ) :- !, depthk_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(depth,Sg,Qv,Call) :- !, depthk_unknown_entry(Sg,Qv,Call).
empty_entry(depth,Sg,Qv,Call) :- !, depthk_empty_entry(Sg,Qv,Call).
%
depthk_eliminate_equivalent(TmpLSucc,LSucc) :- absub_eliminate_equivalent(TmpLSucc,depth,LSucc).
depthk_abs_subset(LASub1,LASub2) :- absub_is_subset(LASub1,depth,LASub2).
% ---------------------------------------------------------------------------
:- use_module(domain(top_path_sharing)).
aidomain(path).
init_abstract_domain(path,PushedFlags) :- !, path_init_abstract_domain(PushedFlags).
call_to_entry(path,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, path_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(path,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, path_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(path,_Sg,Vars,_HvFv,ASub,Proj) :- !, path_project(Vars,ASub,Proj).
compute_lub(path,ListAsub,LubASub) :- !, path_compute_lub(ListAsub,LubASub).
abs_sort(path,ASub,ASub_s) :- !, path_sort(ASub,ASub_s).
extend(path,_Sg,Prime,Sv,Call,Succ) :- !, path_extend(Prime,Sv,Call,Succ).
less_or_equal(path,ASub0,ASub1) :- !, path_less_or_equal(ASub0,ASub1).
glb(path,ASub0,ASub1,ASub) :- !, path_glb(ASub0,ASub1,ASub).
call_to_success_fact(path,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, path_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(path,SgKey,Sg,_Subgoal,Type,Condvars) :- !, path_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(path,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, path_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
input_interface(path,InputUser,Kind,Struct0,Struct1) :- !, path_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(path,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, path_input_user_interface(InputUser,Qv,ASub).
asub_to_native(path,ASub,Qv,OutFlag,OutputUser,Comps) :- !, path_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(path,Sg,Vars,Call,Succ) :- !, path_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(path,Sg,Qv,Call) :- !, path_unknown_entry(Sg,Qv,Call).
empty_entry(path,Sg,Qv,Call) :- !, path_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
path_init_abstract_domain([variants,multi_success]) :-
	push_pp_flag(variants,off),
	push_pp_flag(multi_success,on).
path_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ===========================================================================
:- doc(section, "Type domains"). % TODO: shape/structure?
% ---------------------------------------------------------------------------
:- use_module(domain(termsd)).
aidomain(terms).
init_abstract_domain(terms,PushedFlags) :- !, terms_init_abstract_domain(PushedFlags).
call_to_entry(terms,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, terms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(terms,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, terms_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(terms,_Sg,Vars,_HvFv,ASub,Proj) :- !, terms_project(Vars,ASub,Proj).
widencall(terms,Prime0,Prime1,NewPrime) :- !, terms_widencall(Prime0,Prime1,NewPrime).
widen(terms,Prime0,Prime1,NewPrime) :- !, terms_widen(Prime0,Prime1,NewPrime).
compute_lub(terms,ListASub,LubASub) :- !, terms_compute_lub(ListASub,LubASub).
identical_abstract(terms,ASub1,ASub2) :- !, terms_identical_abstract(ASub1,ASub2).
abs_sort(terms,ASub,ASub_s) :- !, terms_sort(ASub,ASub_s).
extend(terms,_Sg,Prime,Sv,Call,Succ) :- !, terms_extend(Prime,Sv,Call,Succ).
less_or_equal(terms,ASub0,ASub1) :- !, terms_less_or_equal(ASub0,ASub1).
glb(terms,ASub0,ASub1,ASub) :- !, terms_glb(ASub0,ASub1,ASub).
call_to_success_fact(terms,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, terms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(terms,SgKey,Sg,_Subgoal,Type,Condvars) :- !, terms_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(terms,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, terms_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(terms,SgKey,Sg,Sv,Call,Proj,Succ) :- !, terms_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(terms,InputUser,Kind,Struct0,Struct1) :- !, terms_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(terms,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, terms_input_user_interface(InputUser,Qv,ASub).
asub_to_native(terms,ASub,Qv,OutFlag,OutputUser,Comps) :- !, terms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
concrete(terms,Var,ASub,List) :- !, terms_concret(Var,ASub,List).
unknown_call(terms,Sg,Vars,Call,Succ) :- !, terms_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(terms,Sg,Qv,Call) :- !, terms_unknown_entry(Sg,Qv,Call).
empty_entry(terms,Sg,Qv,Call) :- !, terms_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(terms,ASub,Types0,Types) :- !, terms_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(terms,ASub,(Types,Names),RenASub) :- !, terms_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
terms_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on).
% ---------------------------------------------------------------------------
:- use_module(domain(ptypes)).
aidomain(ptypes).
init_abstract_domain(ptypes,PushedFlags) :- !, ptypes_init_abstract_domain(PushedFlags).
call_to_entry(ptypes,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, terms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(ptypes,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, terms_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
widencall(ptypes,Prime0,Prime1,NewPrime) :- !, ptypes_widencall(Prime0,Prime1,NewPrime).
widen(ptypes,Prime0,Prime1,NewPrime) :- !, ptypes_widen(Prime0,Prime1,NewPrime).
compute_lub(ptypes,ListASub,LubASub) :- !, terms_compute_lub(ListASub,LubASub).
identical_abstract(ptypes,ASub1,ASub2) :- !, terms_identical_abstract(ASub1,ASub2).
abs_sort(ptypes,ASub,ASub_s) :- !, terms_sort(ASub,ASub_s).
extend(ptypes,_Sg,Prime,Sv,Call,Succ) :- !, terms_extend(Prime,Sv,Call,Succ).
less_or_equal(ptypes,ASub0,ASub1) :- !, terms_less_or_equal(ASub0,ASub1).
glb(ptypes,ASub0,ASub1,ASub) :- !, terms_glb(ASub0,ASub1,ASub).
call_to_success_fact(ptypes,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, terms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(ptypes,SgKey,Sg,_Subgoal,Type,Condvars) :- !, terms_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(ptypes,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, terms_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(ptypes,SgKey,Sg,Sv,Call,Proj,Succ) :- !, terms_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(ptypes,InputUser,Kind,Struct0,Struct1) :- !, terms_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(ptypes,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, terms_input_user_interface(InputUser,Qv,ASub).
asub_to_native(ptypes,ASub,Qv,OutFlag,OutputUser,Comps) :- !, terms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
concrete(ptypes,Var,ASub,List) :- !, terms_concret(Var,ASub,List).
unknown_call(ptypes,Sg,Vars,Call,Succ) :- !, terms_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(ptypes,Sg,Qv,Call) :- !, terms_unknown_entry(Sg,Qv,Call).
empty_entry(ptypes,Sg,Qv,Call) :- !, terms_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(ptypes,ASub,Types0,Types) :- !, terms_collect_abstypes(ASub,Types0,Types).
% rename_abstypes_abs(ptypes,ASub,(Types,Names),RenASub) :- !, terms_rename_abs(ASub,Types,Names,RenASub). % TODO: missing, why?
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
ptypes_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on).
% ---------------------------------------------------------------------------
:- use_module(domain(eterms)).
aidomain(eterms).
init_abstract_domain(eterms,PushedFlags) :- !, eterms_init_abstract_domain(PushedFlags).
call_to_entry(eterms,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(eterms,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, eterms_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(eterms,_Sg,Vars,_HvFv,ASub,Proj) :- !, eterms_project(Vars,ASub,Proj).
widencall(eterms,Prime0,Prime1,NewPrime) :- !, eterms_widencall(Prime0,Prime1,NewPrime).
widen(eterms,Prime0,Prime1,NewPrime) :- !, eterms_widen(Prime0,Prime1,NewPrime).
compute_lub(eterms,ListASub,LubASub) :- !, eterms_compute_lub(ListASub,LubASub).
identical_abstract(eterms,ASub1,ASub2) :- !, eterms_identical_abstract(ASub1,ASub2).
abs_sort(eterms,ASub,ASub_s) :- !, eterms_sort(ASub,ASub_s).
extend(eterms,_Sg,Prime,Sv,Call,Succ) :- !, eterms_extend(Prime,Sv,Call,Succ).
less_or_equal(eterms,ASub0,ASub1) :- !, eterms_less_or_equal(ASub0,ASub1).
glb(eterms,ASub0,ASub1,ASub) :- !, eterms_glb(ASub0,ASub1,ASub).
call_to_success_fact(eterms,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(eterms,SgKey,Sg,Subgoal,Type,Condvars) :- !, eterms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(eterms,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, eterms_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(eterms,SgKey,Sg,Sv,Call,Proj,Succ) :- !, eterms_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(eterms,_Prop,Vars,ASub,Info) :- !, asub_to_info(eterms,ASub,Vars,Info,_CompProps).
input_interface(eterms,InputUser,Kind,Struct0,Struct1) :- !, eterms_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(eterms,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, eterms_input_user_interface(InputUser,Qv,ASub).
asub_to_native(eterms,ASub,Qv,OutFlag,OutputUser,Comps) :- !, eterms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
concrete(eterms,Var,ASub,List) :- !, eterms_concret(Var,ASub,List).
unknown_call(eterms,Sg,Vars,Call,Succ) :- !, eterms_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(eterms,Sg,Qv,Call) :- !, eterms_unknown_entry(Sg,Qv,Call).
empty_entry(eterms,Sg,Qv,Call) :- !, eterms_empty_entry(Sg,Qv,Call).
part_conc(eterms,Sg,Subs,NSg,NSubs) :- !, eterms_part_conc(Sg,Subs,NSg,NSubs).
multi_part_conc(eterms,Sg,Subs,List) :- !, eterms_multi_part_conc(Sg,Subs,List).
collect_abstypes_abs(eterms,ASub,Types0,Types) :- !, eterms_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(eterms,ASub,(Types,Names),RenASub) :- !, eterms_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
eterms_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on).
% ---------------------------------------------------------------------------
:- use_module(domain(etermsvar)).
aidomain(etermsvar).
init_abstract_domain(etermsvar,PushedFlags) :- !, etermsvar_init_abstract_domain(PushedFlags).
call_to_entry(etermsvar,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, etermsvar_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(etermsvar,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, etermsvar_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(etermsvar,_Sg,Vars,_HvFv,ASub,Proj) :- !, etermsvar_project(Vars,ASub,Proj).
widencall(etermsvar,Prime0,Prime1,NewPrime) :- !, etermsvar_widencall(Prime0,Prime1,NewPrime).
widen(etermsvar,Prime0,Prime1,NewPrime) :- !, etermsvar_widen(Prime0,Prime1,NewPrime).
compute_lub(etermsvar,ListASub,LubASub) :- !, etermsvar_compute_lub(ListASub,LubASub).
identical_abstract(etermsvar,ASub1,ASub2) :- !, etermsvar_identical_abstract(ASub1,ASub2).
abs_sort(etermsvar,ASub,ASub_s) :- !, etermsvar_sort(ASub,ASub_s).
extend(etermsvar,_Sg,Prime,Sv,Call,Succ) :- !, etermsvar_extend(Prime,Sv,Call,Succ).
less_or_equal(etermsvar,ASub0,ASub1) :- !, etermsvar_less_or_equal(ASub0,ASub1).
glb(etermsvar,ASub0,ASub1,ASub) :- !, etermsvar_glb(ASub0,ASub1,ASub).
call_to_success_fact(etermsvar,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, etermsvar_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(etermsvar,SgKey,Sg,Subgoal,Type,Condvars) :- !, etermsvar_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(etermsvar,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, etermsvar_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(etermsvar,SgKey,Sg,Sv,Call,Proj,Succ) :- !, etermsvar_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(etermsvar,_Prop,Vars,ASub,Info) :- !, asub_to_info(etermsvar,ASub,Vars,Info,_CompProps).
input_interface(etermsvar,InputUser,Kind,Struct0,Struct1) :- !, etermsvar_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(etermsvar,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, etermsvar_input_user_interface(InputUser,Qv,ASub).
asub_to_native(etermsvar,ASub,Qv,OutFlag,OutputUser,Comps) :- !, etermsvar_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
%concrete(etermsvar,Var,ASub,List) :- !, etermsvar_concret(Var,ASub,List).
unknown_call(etermsvar,Sg,Vars,Call,Succ) :- !, etermsvar_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(etermsvar,Sg,Qv,Call) :- !, etermsvar_unknown_entry(Sg,Qv,Call).
empty_entry(etermsvar,Sg,Qv,Call) :- !, etermsvar_empty_entry(Sg,Qv,Call).
part_conc(etermsvar,Sg,Subs,NSg,NSubs) :- !, etermsvar_part_conc(Sg,Subs,NSg,NSubs).
multi_part_conc(etermsvar,Sg,Subs,List) :- !, etermsvar_multi_part_conc(Sg,Subs,List).
collect_abstypes_abs(etermsvar,ASub,Types0,Types) :- !, etermsvar_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(etermsvar,ASub,(Types,Names),RenASub) :- !, etermsvar_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
etermsvar_init_abstract_domain([type_eval,widen]) :-
	push_pp_flag(type_eval,on),
	push_pp_flag(widen,on).
% ---------------------------------------------------------------------------
:- use_module(domain(svterms)).
aidomain(svterms).
init_abstract_domain(svterms,PushedFlags) :- !, svterms_init_abstract_domain(PushedFlags).
call_to_entry(svterms,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, svterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(svterms,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, svterms_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(svterms,_Sg,Vars,_HvFv,ASub,Proj) :- !, svterms_project(Vars,ASub,Proj).
widencall(svterms,Prime0,Prime1,NewPrime) :- !, svterms_widencall(Prime0,Prime1,NewPrime).
widen(svterms,Prime0,Prime1,NewPrime) :- !, svterms_widen(Prime0,Prime1,NewPrime).
compute_lub(svterms,ListASub,LubASub) :- !, svterms_compute_lub(ListASub,LubASub).
identical_abstract(svterms,ASub1,ASub2) :- !, svterms_identical_abstract(ASub1,ASub2).
abs_sort(svterms,ASub,ASub_s) :- !, svterms_sort(ASub,ASub_s).
extend(svterms,_Sg,Prime,Sv,Call,Succ) :- !, svterms_extend(Prime,Sv,Call,Succ).
less_or_equal(svterms,ASub0,ASub1) :- !, svterms_less_or_equal(ASub0,ASub1).
glb(svterms,ASub0,ASub1,ASub) :- !, svterms_glb(ASub0,ASub1,ASub).
call_to_success_fact(svterms,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, svterms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(svterms,SgKey,Sg,Subgoal,Type,Condvars) :- !, svterms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(svterms,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, svterms_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(svterms,SgKey,Sg,Sv,Call,Proj,Succ) :- !, svterms_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(svterms,InputUser,Kind,Struct0,Struct1) :- !, svterms_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(svterms,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, svterms_input_user_interface(InputUser,Qv,ASub).
asub_to_native(svterms,ASub,Qv,OutFlag,OutputUser,Comps) :- !, svterms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
concrete(svterms,Var,ASub,List) :- !, svterms_concret(Var,ASub,List).
unknown_call(svterms,Sg,Vars,Call,Succ) :- !, svterms_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(svterms,Sg,Qv,Call) :- !, svterms_unknown_entry(Sg,Qv,Call).
empty_entry(svterms,Sg,Qv,Call) :- !, svterms_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(svterms,ASub,Types0,Types) :- !, svterms_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(svterms,ASub,(Types,Names),RenASub) :- !, svterms_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
svterms_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on).
% ---------------------------------------------------------------------------
:- use_module(domain(deftypes)).
aidomain(deftypes).
init_abstract_domain(deftypes,PushedFlags) :- !, deftypes_init_abstract_domain(PushedFlags).
call_to_entry(deftypes,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, deftypes_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(deftypes,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, deftypes_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(deftypes,_Sg,Vars,_HvFv,ASub,Proj) :- !, deftypes_project(Vars,ASub,Proj).
widencall(deftypes,Prime0,Prime1,NewPrime) :- !, deftypes_widencall(Prime0,Prime1,NewPrime).
widen(deftypes,Prime0,Prime1,NewPrime) :- !, deftypes_widen(Prime0,Prime1,NewPrime).
compute_lub(deftypes,ListASub,LubASub) :- !, deftypes_compute_lub(ListASub,LubASub).
identical_abstract(deftypes,ASub1,ASub2) :- !, deftypes_identical_abstract(ASub1,ASub2).
abs_sort(deftypes,ASub,ASub_s) :- !, terms_sort(ASub,ASub_s).
extend(deftypes,_Sg,Prime,Sv,Call,Succ) :- !, deftypes_extend(Prime,Sv,Call,Succ).
less_or_equal(deftypes,ASub0,ASub1) :- !, deftypes_less_or_equal(ASub0,ASub1).
glb(deftypes,ASub0,ASub1,ASub) :- !, deftypes_glb(ASub0,ASub1,ASub).
call_to_success_fact(deftypes,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, deftypes_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(deftypes,SgKey,Sg,_Subgoal,Type,Condvars) :- !, terms_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(deftypes,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, terms_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(deftypes,SgKey,Sg,Sv,Call,Proj,Succ) :- !, deftypes_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(deftypes,InputUser,Kind,Struct0,Struct1) :- !, deftypes_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(deftypes,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, deftypes_input_user_interface(InputUser,Qv,ASub).
asub_to_native(deftypes,ASub,Qv,OutFlag,OutputUser,Comps) :- !, deftypes_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
concrete(deftypes,Var,ASub,List) :- !, terms_concret(Var,ASub,List).
unknown_call(deftypes,Sg,Vars,Call,Succ) :- !, terms_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(deftypes,Sg,Qv,Call) :- !, terms_unknown_entry(Sg,Qv,Call).
empty_entry(deftypes,Sg,Qv,Call) :- !, terms_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(deftypes,ASub,Types0,Types) :- !, deftypes_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(deftypes,ASub,(Types,Names),RenASub) :- !, terms_rename_abs(ASub,Types,Names,RenASub).
contains_parameters(deftypes,Subst) :-!, deftypes_contains_parameters(Subst).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
deftypes_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on).
% ===========================================================================
:- doc(section, "Numeric domains").
% ---------------------------------------------------------------------------
% intervals domain % [IG] new, simplified nonrelational domain
:- use_module(domain(nonrel)).
% (simpler domain interface, only for non-relational domains)
aidomain(nonrel_intervals).
init_abstract_domain(nonrel_intervals,PushedFlags) :- !, nonrel_intervals_init_abstract_domain(PushedFlags).
amgu(nonrel_intervals,Sg,Head,ASub,NewASub) :- !, nonrel_intervals_amgu(Sg,Head,ASub,NewASub).
call_to_entry(nonrel_intervals,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, nonrel_intervals_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(nonrel_intervals,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, nonrel_intervals_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(nonrel_intervals,Sg,Vars,HvFv,ASub,Proj) :- !, nonrel_intervals_project(Sg,Vars,HvFv,ASub,Proj).
widencall(nonrel_intervals,Prime0,Prime1,NewPrime) :- !, nonrel_intervals_widencall(Prime0,Prime1,NewPrime).
widen(nonrel_intervals, Prime0, Prime1, NewPrime) :- !, nonrel_intervals_widen(Prime0,Prime1,NewPrime).
compute_lub(nonrel_intervals,ListASub,LubASub) :- !, nonrel_intervals_compute_lub(ListASub,LubASub).
identical_abstract(nonrel_intervals, ASub1, ASub2) :- !, nonrel_intervals_identical_abstract(ASub1, ASub2).
abs_sort(nonrel_intervals,ASub,ASub_s) :- !, nonrel_intervals_abs_sort(ASub,ASub_s).
extend(nonrel_intervals,Sg,Prime,Sv,Call,Succ) :- !, nonrel_intervals_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(nonrel_intervals,ASub0,ASub1) :- !, nonrel_intervals_less_or_equal(ASub0,ASub1).
glb(nonrel_intervals,ASub0,ASub1,ASub) :- !, nonrel_intervals_glb(ASub0,ASub1,ASub).
call_to_success_fact(nonrel_intervals,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, nonrel_intervals_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(nonrel_intervals,SgKey,Sg,Subgoal,Type,Condvars) :- !, nonrel_intervals_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(nonrel_intervals,Type,Sv_uns,Condvars,HvFv_u,Call,Succ) :- !, nonrel_intervals_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).
call_to_success_builtin(nonrel_intervals,SgKey,Sg,Sv,Call,Proj,Succ) :- !, nonrel_intervals_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(nonrel_intervals,InputUser,Kind,Struct0,Struct1) :- !, nonrel_intervals_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(nonrel_intervals,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, nonrel_intervals_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(nonrel_intervals,ASub,Qv,OutFlag,OutputUser,Comps) :- !, nonrel_intervals_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(nonrel_intervals,Sg,Vars,Call,Succ) :- !, nonrel_intervals_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(nonrel_intervals,Sg,Qv,Call) :- !, nonrel_intervals_unknown_entry(Sg,Qv,Call).
empty_entry(nonrel_intervals,Sg,Qv,Call) :- !, nonrel_intervals_empty_entry(Sg,Qv,Call).
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(polyhedra)).
aidomain(polyhedra).
init_abstract_domain(polyhedra,PushedFlags) :- !,  polyhedra_init_abstract_domain(PushedFlags).
call_to_entry(polyhedra,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, polyhedra_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(polyhedra,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, polyhedra_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(polyhedra,_Sg,Vars,_HvFv,ASub,Proj) :- !, polyhedra_project(ASub,Vars,Proj).
widencall(polyhedra,Prime0,Prime1,NewPrime) :- !, polyhedra_widencall(Prime0,Prime1,NewPrime). 
widen(polyhedra,Prime0,Prime1,NewPrime) :- !, polyhedra_widen(Prime0,Prime1,NewPrime).
compute_lub(polyhedra,ListASub,LubASub) :- !, polyhedra_compute_lub(ListASub,LubASub).
identical_abstract(polyhedra,ASub1,ASub2) :- !, polyhedra_identical_abstract(ASub1,ASub2).
abs_sort(polyhedra,ASub,ASub_s) :- !, polyhedra_sort(ASub,ASub_s).
extend(polyhedra,_Sg,Prime,Sv,Call,Succ) :- !, polyhedra_extend(Prime,Sv,Call,Succ).
less_or_equal(polyhedra,ASub0,ASub1) :- !, polyhedra_less_or_equal(ASub0,ASub1).
glb(polyhedra,ASub0,ASub1,ASub) :- !, polyhedra_glb(ASub0,ASub1,ASub).
eliminate_equivalent(polyhedra,TmpLSucc,LSucc) :- !, polyhedra_sort(TmpLSucc,LSucc).
call_to_success_fact(polyhedra,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, polyhedra_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(polyhedra,SgKey,Sg,_Subgoal,Type,Condvars) :- !, polyhedra_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(polyhedra,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, polyhedra_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(polyhedra,SgKey,Sg,Sv,Call,Proj,Succ) :- !, polyhedra_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(polyhedra,InputUser,Kind,Struct0,Struct1) :- !, polyhedra_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(polyhedra,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, polyhedra_input_user_interface(InputUser,Qv,ASub).
asub_to_native(polyhedra,ASub,Qv,OutFlag,OutputUser,Comps) :- !, polyhedra_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(polyhedra,Sg,Vars,Call,Succ) :- !, polyhedra_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(polyhedra,Sg,Qv,Call) :- !, polyhedra_unknown_entry(Sg,Qv,Call).
empty_entry(polyhedra,Sg,Qv,Call) :- !, polyhedra_empty_entry(Sg,Qv,Call).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
polyhedra_init_abstract_domain([widen]) :- 
        push_pp_flag(widen,on).
:- endif.
% ===========================================================================
:- doc(section, "OO/Java domains"). % TODO: imperative? points-to? nullity?
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(java_nullity)). % for java programs
aidomain(java_nullity).
call_to_entry(java_nullity,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, java_nullity_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(java_nullity,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, java_nullity_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(java_nullity,_Sg,Vars,_HvFv,ASub,Proj) :- !, java_nullity_project(ASub,Vars,Proj).
compute_lub(java_nullity,ListAsub,LubASub) :- !, java_nullity_compute_lub(ListAsub,LubASub).
abs_sort(java_nullity,ASub,ASub_s) :- !, java_nullity_sort(ASub,ASub_s).
extend(java_nullity,_Sg,Prime,Sv,Call,Succ) :- !, java_nullity_extend(Prime,Sv,Call,Succ).
less_or_equal(java_nullity,ASub0,ASub1) :- !, java_nullity_less_or_equal(ASub0,ASub1).
glb(java_nullity,ASub0,ASub1,ASub) :- !, java_nullity_glb(ASub0,ASub1,ASub).
call_to_success_fact(java_nullity,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, java_nullity_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(java_nullity,SgKey,Sg,_Subgoal,Type,Condvars) :- !, java_nullity_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(java_nullity,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, java_nullity_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
input_interface(java_nullity,InputUser,Kind,Struct0,Struct1) :- !, java_nullity_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(java_nullity,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, java_nullity_input_user_interface(InputUser,Qv,ASub).
asub_to_native(java_nullity,ASub,Qv,OutFlag,OutputUser,Comps) :- !, java_nullity_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(java_nullity,Sg,Vars,Call,Succ) :- !, java_nullity_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(java_nullity,Sg,Qv,Call) :- !, java_nullity_unknown_entry(Sg,Qv,Call).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_son)).
aidomain(oo_son).
call_to_entry(oo_son,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, oo_son_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(oo_son,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, oo_son_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(oo_son,_Sg,Vars,_HvFv,ASub,Proj) :- !, oo_son_project(ASub,Vars,Proj).
compute_lub(oo_son,ListAsub,LubASub) :- !, oo_son_compute_lub(ListAsub,LubASub).
identical_abstract(oo_son,ASub1,ASub2) :- !, oo_son_identical_abstract(ASub1,ASub2).
abs_sort(oo_son,ASub,ASub_s) :- !, oo_son_sort(ASub,ASub_s).
extend(oo_son,_Sg,Prime,Sv,Call,Succ) :- !, oo_son_extend(Prime,Sv,Call,Succ).
less_or_equal(oo_son,ASub0,ASub1) :- !, oo_son_less_or_equal(ASub0,ASub1).
glb(oo_son,ASub0,ASub1,ASub) :- !, oo_son_glb(ASub0,ASub1,ASub).
call_to_success_fact(oo_son,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, oo_son_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(oo_son,SgKey,Sg,_Subgoal,Type,Condvars) :- !, oo_son_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(oo_son,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, oo_son_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(oo_son,SgKey,Sg,Sv,Call,Proj,Succ) :- !, oo_son_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(oo_son,InputUser,Kind,Struct0,Struct1) :- !, oo_son_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(oo_son,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, oo_son_input_user_interface(InputUser,Qv,ASub).
asub_to_native(oo_son,ASub,Qv,OutFlag,OutputUser,Comps) :- !, oo_son_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(oo_son,Sg,Vars,Call,Succ) :- !, oo_son_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(oo_son,Sg,Qv,Call) :- !, oo_son_unknown_entry(Sg,Qv,Call).
empty_entry(oo_son,Sg,Qv,Call) :- !, oo_son_empty_entry(Sg,Qv,Call).
%% compute_lub_el(oo_son,ASub1,ASub2,ASub) :- !, oo_son_lub(ASub1,ASub2,ASub).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_shnltau)).
aidomain(oo_shnltau).
% init_abstract_domain(oo_shnltau,PushedFlags) :- !, oo_shnltau_init_abstract_domain(PushedFlags).
call_to_entry(oo_shnltau,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, oo_shnltau_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(oo_shnltau,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, oo_shnltau_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(oo_shnltau,_Sg,Vars,_HvFv,ASub,Proj) :- !, oo_shnltau_project(ASub,Vars,Proj).
compute_lub(oo_shnltau,ListAsub,LubASub) :- !, oo_shnltau_compute_lub(ListAsub,LubASub).
abs_sort(oo_shnltau,ASub,ASub_s) :- !, oo_shnltau_sort(ASub,ASub_s).
extend(oo_shnltau,_Sg,Prime,Sv,Call,Succ) :- !, oo_shnltau_extend(Prime,Sv,Call,Succ).
less_or_equal(oo_shnltau,ASub0,ASub1) :- !, oo_shnltau_less_or_equal(ASub0,ASub1).
glb(oo_shnltau,ASub0,ASub1,ASub) :- !, oo_shnltau_glb(ASub0,ASub1,ASub).
call_to_success_fact(oo_shnltau,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, oo_shnltau_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(oo_shnltau,SgKey,Sg,_Subgoal,Type,Condvars) :- !, oo_shnltau_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(oo_shnltau,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, oo_shnltau_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(oo_shnltau,SgKey,Sg,Sv,Call,Proj,Succ) :- !, oo_shnltau_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(oo_shnltau,InputUser,Kind,Struct0,Struct1) :- !, oo_shnltau_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(oo_shnltau,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, oo_shnltau_input_user_interface(InputUser,Qv,ASub).
asub_to_native(oo_shnltau,ASub,Qv,OutFlag,OutputUser,Comps) :- !, oo_shnltau_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(oo_shnltau,Sg,Vars,Call,Succ) :- !, oo_shnltau_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(oo_shnltau,Sg,Qv,Call) :- !, oo_shnltau_unknown_entry(Sg,Qv,Call).
empty_entry(oo_shnltau,Sg,Qv,Call) :- !, oo_shnltau_empty_entry(Sg,Qv,Call).
%% compute_lub_el(oo_shnltau,ASub1,ASub2,ASub) :- !, oo_shnltau_lub(ASub1,ASub2,ASub).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_types)).
aidomain(oo_types).
% init_abstract_domain(oo_types,PushedFlags) :- !, oo_types_init_abstract_domain(PushedFlags).
call_to_entry(oo_types,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, oo_types_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(oo_types,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, oo_types_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(oo_types,_Sg,Vars,_HvFv,ASub,Proj) :- !, oo_types_project(ASub,Vars,Proj).
compute_lub(oo_types,ListAsub,LubASub) :- !, oo_types_compute_lub(ListAsub,LubASub).
abs_sort(oo_types,ASub,ASub_s) :- !, oo_types_sort(ASub,ASub_s).
extend(oo_types,_Sg,Prime,Sv,Call,Succ) :- !, oo_types_extend(Prime,Sv,Call,Succ).
less_or_equal(oo_types,ASub0,ASub1) :- !, oo_types_less_or_equal(ASub0,ASub1).
glb(oo_types,ASub0,ASub1,ASub) :- !, oo_types_glb(ASub0,ASub1,ASub).
call_to_success_fact(oo_types,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, oo_types_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(oo_types,SgKey,Sg,_Subgoal,Type,Condvars) :- !, oo_types_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(oo_types,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, oo_types_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(oo_types,SgKey,Sg,Sv,Call,Proj,Succ) :- !, oo_types_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(oo_types,InputUser,Kind,Struct0,Struct1) :- !, oo_types_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(oo_types,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, oo_types_input_user_interface(InputUser,Qv,ASub).
asub_to_native(oo_types,ASub,Qv,OutFlag,OutputUser,Comps) :- !, oo_types_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(oo_types,Sg,Vars,Call,Succ) :- !, oo_types_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(oo_types,Sg,Qv,Call) :- !, oo_types_unknown_entry(Sg,Qv,Call).
empty_entry(oo_types,Sg,Qv,Call) :- !, oo_types_empty_entry(Sg,Qv,Call).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(java_cha)).
aidomain(java_cha).
call_to_entry(java_cha,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, java_cha_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(java_cha,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, java_cha_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(java_cha,_Sg,Vars,_HvFv,ASub,Proj) :- !, java_cha_project(ASub,Vars,Proj).
compute_lub(java_cha,ListAsub,LubASub) :- !, java_cha_compute_lub(ListAsub,LubASub).
abs_sort(java_cha,ASub,ASub_s) :- !, java_cha_sort(ASub,ASub_s).
extend(java_cha,_Sg,Prime,Sv,Call,Succ) :- !, java_cha_extend(Prime,Sv,Call,Succ).
less_or_equal(java_cha,ASub0,ASub1) :- !, java_cha_less_or_equal(ASub0,ASub1).
glb(java_cha,ASub0,ASub1,ASub) :- !, java_cha_glb(ASub0,ASub1,ASub).
call_to_success_fact(java_cha,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, java_cha_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(java_cha,SgKey,Sg,_Subgoal,Type,Condvars) :- !, java_cha_special_builtin(SgKey,Sg,Type,Condvars).
success_builtin(java_cha,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, java_cha_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
input_interface(java_cha,InputUser,Kind,Struct0,Struct1) :- !, java_cha_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(java_cha,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, java_cha_input_user_interface(InputUser,Qv,ASub).
asub_to_native(java_cha,ASub,Qv,OutFlag,OutputUser,Comps) :- !, java_cha_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).
unknown_call(java_cha,Sg,Vars,Call,Succ) :- !, java_cha_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(java_cha,Sg,Qv,Call) :- !, java_cha_unknown_entry(Sg,Qv,Call).
:- endif.
% ===========================================================================
:- doc(section, "Computation domains").
% ---------------------------------------------------------------------------
% nonfailure
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(nfplai)).
aidomain(nf).
init_abstract_domain(nf,PushedFlags) :- !, nf_init_abstract_domain(PushedFlags).
call_to_entry(nf,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(nf,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(nf,_Sg,Vars,_HvFv,ASub,Proj) :- !, nf_project(ASub,Vars,Proj).
widencall(nf,Prime0,Prime1,NewPrime) :- !, nf_widencall(Prime0,Prime1,NewPrime).
widen(nf,Prime0,Prime1,NewPrime) :- !, nf_widen(Prime0,Prime1,NewPrime).
compute_lub(nf,ListASub,LubASub) :- !, nf_compute_lub(ListASub,LubASub). 
compute_clauses_lub(nf,Proj,ASub,Lub) :- !, nf_compute_clauses_lub(ASub,Proj,Lub).
identical_abstract(nf,ASub1,ASub2) :- !, nf_identical_abstract(ASub1,ASub2).
fixpoint_covered(nf,Prime0,Prime1) :- !, nf_less_or_equal(Prime0,Prime1).
abs_sort(nf,ASub,ASub_s) :- !, nf_sort(ASub,ASub_s).
extend(nf,_Sg,Prime,Sv,Call,Succ) :- !, nf_extend(Prime,Sv,Call,Succ).
less_or_equal(nf,ASub0,ASub1) :- !, nf_less_or_equal(ASub0,ASub1).
glb(nf,ASub0,ASub1,ASub) :- !, nf_glb(ASub0,ASub1,ASub).
eliminate_equivalent(nf,TmpLSucc,LSucc) :- !, nf_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(nf,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, nf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(nf,SgKey,Sg,_Subgoal,Type,Condvars) :- !, nf_special_builtin(SgKey,Sg,Type,Condvars).
combined_special_builtin(nf,SgKey,Domains) :- !, nf_combined_special_builtin(SgKey,Domains).
split_combined_domain(nf,ASub,ASubs,Doms) :- !, nf_split_combined_domain(ASub,ASubs,Doms).
success_builtin(nf,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, nf_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
input_interface(nf,InputUser,Kind,Struct0,Struct1) :- !, nf_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(nf,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, nf_input_user_interface(InputUser,Qv,ASub).
asub_to_native(nf,ASub,Qv,OutFlag,OutputUser,Comp) :- !, nf_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comp).
unknown_call(nf,Sg,Vars,Call,Succ) :- !, nf_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(nf,Sg,Qv,Call) :- !, nf_unknown_entry(Sg,Qv,Call).
empty_entry(nf,Sg,Qv,Call) :- !, nf_empty_entry(Sg,Qv,Call).
dom_statistics(nf, Info) :- !, nf_statistics(Info).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
nf_init_abstract_domain([variants,widen]) :-
	push_pp_flag(variants,off),
	push_pp_flag(widen,on).
nf_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)
nf_combined_special_builtin(SgKey,Domains) :-
	% TODO: refactor (define a nondet pred with combined domains instead)
	( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr,nf]
	; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr,nf]
	; special_builtin(nf,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr,nf]
	; fail
	).
:- endif.
% ---------------------------------------------------------------------------
% determinism
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(detplai)).
aidomain(det).
init_abstract_domain(det,PushedFlags) :- !, det_init_abstract_domain(PushedFlags).
call_to_entry(det,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, det_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(det,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, det_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(det,_Sg,Vars,_HvFv,ASub,Proj) :- !, det_project(ASub,Vars,Proj).
widencall(det,Prime0,Prime1,NewPrime) :- !, det_widencall(Prime0,Prime1,NewPrime).
widen(det,Prime0,Prime1,NewPrime) :- !, det_widen(Prime0,Prime1,NewPrime).
compute_lub(det,ListASub,LubASub) :- !, det_compute_lub(ListASub,LubASub).
compute_clauses_lub(det,Proj,ASub,Lub) :- !, det_compute_clauses_lub(ASub,Proj,Lub).
identical_abstract(det,ASub1,ASub2) :- !, det_identical_abstract(ASub1,ASub2).
fixpoint_covered(det,Prime0,Prime1) :- !, det_less_or_equal(Prime0,Prime1).
abs_sort(det,ASub,ASub_s) :- !, det_sort(ASub,ASub_s).
extend(det,_Sg,Prime,Sv,Call,Succ) :- !, det_extend(Prime,Sv,Call,Succ).
less_or_equal(det,ASub0,ASub1) :- !, det_less_or_equal(ASub0,ASub1).
glb(det,ASub0,ASub1,ASub) :- !, det_glb(ASub0,ASub1,ASub).
eliminate_equivalent(det,TmpLSucc,LSucc) :- !, det_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(det,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, det_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(det,SgKey,Sg,_Subgoal,Type,Condvars) :- !, det_special_builtin(SgKey,Sg,Type,Condvars).
combined_special_builtin(det,SgKey,Domains) :- !, det_combined_special_builtin(SgKey,Domains).
split_combined_domain(det,ASub,ASubs,Doms) :- !, det_split_combined_domain(ASub,ASubs,Doms).
success_builtin(det,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, det_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
% obtain_info(det,Prop,Vars,ASub,Info) :- !, 
% 	asub_to_info(det,ASub,Vars,_OutputUser,CompProps),
% 	CompProps = Info.
obtain_info(det,Prop,Vars,ASub,Info) :- !, det_obtain(Prop,Vars,ASub,Info).
input_interface(det,InputUser,Kind,Struct0,Struct1) :- !, det_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(det,InputUser,Qv,ASub,_Sg,_MaybeCallASub) :- !, det_input_user_interface(InputUser,Qv,ASub).
asub_to_native(det,ASub,Qv,OutFlag,OutputUser,Comp) :- !, det_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comp).
unknown_call(det,Sg,Vars,Call,Succ) :- !, det_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(det,Sg,Qv,Call) :- !, det_unknown_entry(Sg,Qv,Call).
empty_entry(det,Sg,Qv,Call) :- !, det_empty_entry(Sg,Qv,Call).
dom_statistics(det, Info) :- !, det_statistics(Info).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
det_init_abstract_domain([variants,widen]) :-
	push_pp_flag(variants,off),
	push_pp_flag(widen,on).
det_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)
det_combined_special_builtin(SgKey,Domains) :-
	% TODO: refactor (define a nondet pred with combined domains instead)
	( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr,det]
	; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr,det]
	; special_builtin(det,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr,det]
	; fail
	).
:- endif.
% ===========================================================================
:- doc(section, "Resources domains").
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/res_plai)).
aidomain(res_plai).
init_abstract_domain(res_plai,PushedFlags) :- !, res_plai_init_abstract_domain(PushedFlags).
call_to_entry(res_plai,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, res_plai_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(res_plai,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, res_plai_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(res_plai,Sg,Vars,_HvFv,ASub,Proj) :- !, res_plai_project(ASub,Sg,Vars,Proj).
%widencall(res_plai,Prime0,Prime1,NewPrime) :- !, res_plai_widencall(Prime0,Prime1,NewPrime).
widen(res_plai,Prime0,Prime1,NewPrime) :- !, res_plai_widen(Prime0,Prime1,NewPrime).
compute_lub(res_plai,ListASub,GlbASub) :- !, res_plai_compute_lub(ListASub,GlbASub).
compute_clauses_lub(res_plai,Proj,ASub,Lub) :- !, res_plai_compute_clauses_lub(ASub,Proj,Lub).
%compute_clauses_glb(res_plai,Proj,ASub,Lub) :- !, res_plai_compute_clauses_lub(ASub,Proj,Lub).
identical_abstract(res_plai,ASub1,ASub2) :- !, res_plai_identical_abstract(ASub1,ASub2).
abs_sort(res_plai,ASub,ASub_s) :- !, res_plai_sort(ASub,ASub_s).
extend(res_plai,Sg,Prime,Sv,Call,Succ) :- !, res_plai_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(res_plai,ASub0,ASub1) :- !, res_plai_less_or_equal(ASub0,ASub1).
glb(res_plai,ASub0,ASub1,ASub) :- !, res_plai_glb(ASub0,ASub1,ASub).
eliminate_equivalent(res_plai,TmpLSucc,LSucc) :- !, res_plai_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(res_plai,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, res_plai_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(res_plai,SgKey,Sg,_Subgoal,Type,Condvars) :- !, res_plai_special_builtin(SgKey,Sg,Type,Condvars).
combined_special_builtin(res_plai,SgKey,Domains) :- !, res_plai_combined_special_builtin(SgKey,Domains).
split_combined_domain(res_plai,ASub,ASubs,Doms) :- !, res_plai_split_combined_domain(ASub,ASubs,Doms).
% success_builtin(res_plai,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, res_plai_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(res_plai,SgKey,Sg,Sv,Call,Proj,Succ) :- !, res_plai_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(res_plai,_Prop,Vars,ASub,Info) :- !, asub_to_info(res_plai,ASub,Vars,_Info,Info).
input_interface(res_plai,InputUser,Kind,Struct0,Struct1) :- !, res_plai_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(res_plai,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, res_plai_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(res_plai,ASub,Qv,OutFlag,OutputUser,Comp) :- !, res_plai_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comp).
unknown_call(res_plai,Sg,Vars,Call,Succ) :- !, res_plai_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(res_plai,Sg,Qv,Call) :- !, res_plai_unknown_entry(Sg,Qv,Call).
empty_entry(res_plai,Sg,Qv,Call) :- !, res_plai_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(res_plai,ASub,Types0,Types) :- !, res_plai_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(res_plai,ASub,(Types,Names),RenASub) :- !, res_plai_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
res_plai_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on),
%	res_plai:load_resources_modules.
	res_plai:init_abstract_domain.
res_plai_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)
res_plai_combined_special_builtin(SgKey,Domains) :-
	% TODO: missing check for special_builtin(res_plai, ...)? (see nf_combined_special_builtin)
	% TODO: (if the TODO above works) refactor (define a nondet pred with combined domains instead)
	( special_builtin(etermsvar,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[etermsvar,res_plai]
	; fail
	).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/res_plai_stprf)).
aidomain(res_plai_stprf).
init_abstract_domain(res_plai_stprf,PushedFlags) :- !, res_plai_stprf_init_abstract_domain(PushedFlags).
call_to_entry(res_plai_stprf,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, res_plai_stprf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(res_plai_stprf,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, res_plai_stprf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(res_plai_stprf,Sg,Vars,_HvFv,ASub,Proj) :- !, res_plai_stprf_project(ASub,Sg,Vars,Proj).
widen(res_plai_stprf,Prime0,Prime1,NewPrime) :- !, res_plai_stprf_widen(Prime0,Prime1,NewPrime).
compute_lub(res_plai_stprf,ListASub,GlbASub) :- !, res_plai_stprf_compute_lub(ListASub,GlbASub).
compute_clauses_lub(res_plai_stprf,Proj,ASub,Lub) :- !, res_plai_stprf_compute_clauses_lub(ASub,Proj,Lub).
identical_abstract(res_plai_stprf,ASub1,ASub2) :- !, res_plai_stprf_identical_abstract(ASub1,ASub2).
abs_sort(res_plai_stprf,ASub,ASub_s) :- !, res_plai_stprf_sort(ASub,ASub_s).
extend(res_plai_stprf,Sg,Prime,Sv,Call,Succ) :- !, res_plai_stprf_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(res_plai_stprf,ASub0,ASub1) :- !, res_plai_stprf_less_or_equal(ASub0,ASub1).
glb(res_plai_stprf,ASub0,ASub1,ASub) :- !, res_plai_stprf_glb(ASub0,ASub1,ASub).
eliminate_equivalent(res_plai_stprf,TmpLSucc,LSucc) :- !, res_plai_stprf_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(res_plai_stprf,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, res_plai_stprf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(res_plai_stprf,SgKey,Sg,_Subgoal,Type,Condvars) :- !, res_plai_stprf_special_builtin(SgKey,Sg,Type,Condvars).
combined_special_builtin(res_plai_stprf,SgKey,Domains) :- !, res_plai_stprf_combined_special_builtin(SgKey,Domains).
split_combined_domain(res_plai_stprf,ASub,ASubs,Doms) :- !, res_plai_stprf_split_combined_domain(ASub,ASubs,Doms).
call_to_success_builtin(res_plai_stprf,SgKey,Sg,Sv,Call,Proj,Succ) :- !, res_plai_stprf_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(res_plai_stprf,_Prop,Vars,ASub,Info) :- !, asub_to_info(res_plai_stprf,ASub,Vars,_Info,Info).
input_interface(res_plai_stprf,InputUser,Kind,Struct0,Struct1) :- !, res_plai_stprf_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(res_plai_stprf,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, res_plai_stprf_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(res_plai_stprf,ASub,Qv,OutFlag,OutputUser,Comp) :- !, res_plai_stprf_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comp).
unknown_call(res_plai_stprf,Sg,Vars,Call,Succ) :- !, res_plai_stprf_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(res_plai_stprf,Sg,Qv,Call) :- !, res_plai_stprf_unknown_entry(Sg,Qv,Call).
empty_entry(res_plai_stprf,Sg,Qv,Call) :- !, res_plai_stprf_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(res_plai_stprf,ASub,Types0,Types) :- !, res_plai_stprf_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(res_plai_stprf,ASub,(Types,Names),RenASub) :- !, res_plai_stprf_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
res_plai_stprf_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on),
%	res_plai:load_resources_modules.
	res_plai_stprf:init_abstract_domain.
res_plai_stprf_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)
res_plai_stprf_combined_special_builtin(SgKey,Domains) :-
	% TODO: missing check for special_builtin(res_plai, ...)? (see nf_combined_special_builtin)
	% TODO: (if the TODO above works) refactor (define a nondet pred with combined domains instead)
	( special_builtin(etermsvar,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[etermsvar,res_plai_stprf]
	; fail
	).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/sized_types)).
aidomain(sized_types).
init_abstract_domain(sized_types,PushedFlags) :- !, sized_types_init_abstract_domain(PushedFlags).
call_to_entry(sized_types,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, sized_types_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(sized_types,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, sized_types_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(sized_types,Sg,Vars,_HvFv,ASub,Proj) :- !, sized_types_project(ASub,Sg,Vars,Proj).
widen(sized_types,Prime0,Prime1,NewPrime) :- !, sized_types_widen(Prime0,Prime1,NewPrime).
compute_lub(sized_types,ListASub,GlbASub) :- !, sized_types_compute_lub(ListASub,GlbASub).
compute_clauses_lub(sized_types,Proj,ASub,Lub) :- !, sized_types_compute_clauses_lub(ASub,Proj,Lub).
identical_abstract(sized_types,ASub1,ASub2) :- !, sized_types_identical_abstract(ASub1,ASub2).
abs_sort(sized_types,ASub,ASub_s) :- !, sized_types_sort(ASub,ASub_s).
extend(sized_types,Sg,Prime,Sv,Call,Succ) :- !, sized_types_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(sized_types,ASub0,ASub1) :- !, sized_types_less_or_equal(ASub0,ASub1).
glb(sized_types,ASub0,ASub1,ASub) :- !, sized_types_glb(ASub0,ASub1,ASub).
eliminate_equivalent(sized_types,TmpLSucc,LSucc) :- !, sized_types_eliminate_equivalent(TmpLSucc,LSucc).
call_to_success_fact(sized_types,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, sized_types_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
special_builtin(sized_types,SgKey,Sg,_Subgoal,Type,Condvars) :- !, sized_types_special_builtin(SgKey,Sg,Type,Condvars).
combined_special_builtin(sized_types,SgKey,Domains) :- !, sized_types_combined_special_builtin(SgKey,Domains).
split_combined_domain(sized_types,ASub,ASubs,Doms) :- !, sized_types_split_combined_domain(ASub,ASubs,Doms).
call_to_success_builtin(sized_types,SgKey,Sg,Sv,Call,Proj,Succ) :- !, sized_types_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
obtain_info(sized_types,_Prop,Vars,ASub,Info) :- !, asub_to_info(sized_types,ASub,Vars,_Info,Info).
input_interface(sized_types,InputUser,Kind,Struct0,Struct1) :- !, sized_types_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(sized_types,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, sized_types_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
asub_to_native(sized_types,ASub,Qv,OutFlag,OutputUser,Comp) :- !, sized_types_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comp).
unknown_call(sized_types,Sg,Vars,Call,Succ) :- !, sized_types_unknown_call(Sg,Vars,Call,Succ).
unknown_entry(sized_types,Sg,Qv,Call) :- !, sized_types_unknown_entry(Sg,Qv,Call).
empty_entry(sized_types,Sg,Qv,Call) :- !, sized_types_empty_entry(Sg,Qv,Call).
collect_abstypes_abs(sized_types,ASub,Types0,Types) :- !, sized_types_collect_abstypes(ASub,Types0,Types).
rename_abstypes_abs(sized_types,ASub,(Types,Names),RenASub) :- !, sized_types_rename_abs(ASub,Types,Names,RenASub).
%
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
sized_types_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on),
%	sized_types:load_resources_modules.
	sized_types:init_abstract_domain.
sized_types_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)
sized_types_combined_special_builtin(SgKey,Domains) :-
	% TODO: missing check for special_builtin(sized_types, ...)? (see nf_combined_special_builtin)
	% TODO: (if the TODO above works) refactor (define a nondet pred with combined domains instead)
	( special_builtin(etermsvar,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[etermsvar,sized_types]
	; fail
	).
:- endif.
% ===========================================================================

% ---------------------------------------------------------------------------
% (common)

:- use_module(library(lists), [member/2]).

absub_eliminate_equivalent([],_AbsInt,[]).
absub_eliminate_equivalent([ASub],_AbsInt,[ASub]) :- !.
absub_eliminate_equivalent([ASub|LASub],AbsInt,[ASub|NLASub]) :-
	take_equivalent_out(LASub,ASub,AbsInt,TmpLASub),
	absub_eliminate_equivalent(TmpLASub,AbsInt,NLASub).

take_equivalent_out([],_ASub,_AbsInt,[]).
take_equivalent_out([ASub0|LASub],ASub,AbsInt,NLASub) :-
	equivalent_or_not(ASub0,ASub,AbsInt,NLASub,Tail),
	take_equivalent_out(LASub,ASub,AbsInt,Tail).

equivalent_or_not(ASub0,ASub,AbsInt,NLASub,Tail) :-
	identical_abstract(AbsInt,ASub0,ASub), !,
	NLASub=Tail.
equivalent_or_not(ASub0,_ASub,_AbsInt,[ASub0|Tail],Tail).

% TODO: leaves choicepoints!
absub_is_subset([],_AbsInt,_LASub2).
absub_is_subset([Sub1|Subs1],AbsInt,LASub2) :-
	member(ASub2,LASub2),
	identical_abstract(AbsInt,Sub1,ASub2),
% OR:
%	fixpoint_covered(AbsInt,Sub1,ASub2),
	absub_is_subset(Subs1,AbsInt,LASub2).

absub_fixpoint_covered(AbsInt,Prime0,Prime1) :-
	( current_pp_flag(multi_call,on) ->
	    identical_abstract(AbsInt,Prime0,Prime1)
	; current_pp_flag(multi_call,off) ->
	    less_or_equal(AbsInt,Prime0,Prime1)
	; fail % TODO: anything else?
	).

body_builtin(AbsInt,special(SgKey),Sg,_Condvs,Sv,_HvFv_u,Call,Proj,Succ) :- !,
	call_to_success_builtin(AbsInt,SgKey,Sg,Sv,Call,Proj,Succ).
body_builtin(AbsInt,Type,_Sg,Condvs,Sv,HvFv_u,Call,_Proj,Succ) :-
	success_builtin(AbsInt,Type,Sv,Condvs,HvFv_u,Call,Succ), !.
body_builtin(AbsInt,Type,_Sg,_Condvs,_Sv,_HvFv_u,_Call,_Proj,'$bottom') :-
	warning_message("body_builtin: the builtin key ~q is not defined in domain ~w",
	                [Type,AbsInt]).

undef_call_to_success_builtin(AbsInt,SgKey) :-
        warning_message("call_to_success_builtin: the builtin key ~q is not defined in domain ~w",
	                [special(SgKey),AbsInt]).

% ===========================================================================
:- doc(section, "(Default domain definitions)").

:- use_module(library(sets), [ord_subset/2]).
:- use_module(library(messages), [warning_message/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
:- use_module(library(sort)).

% NOTE: This must be the last part of this file
init_abstract_domain(_AbsInt,[variants]) :-
        % TODO: [IG] for all domains variants=off??
        push_pp_flag(variants,off).
%amgu(_AbsInt,_T0,_T1,_ASub,_NewASub):- throw(not_implemented(amgu)).
%augment_asub(_AbsInt,_ASub,_Vars,_ASub0) :- throw(not_implemented(extend_asub)).
%augment_two_asub(_AbsInt,_ASub0,_ASub1,_ASub) :- throw(not_implemented(extend_two_asub)).
%% widencall(AbsInt,Prime0,Prime1,NewPrime) :- % TODO: [IG] why is this commented?
%% 	compute_lub(AbsInt,[Prime0,Prime1],NewPrime).
widen(AbsInt,Prime0,Prime1,NewPrime) :- % TODO: [IG] define in domain?
	compute_lub(AbsInt,[Prime0,Prime1],NewPrime).
compute_clauses_lub(_AbsInt,_Proj,Lub,Lub).
compute_clauses_glb(_AbsInt,_Proj,Lub,Lub).
identical_abstract(_AbsInt,ASub1,ASub2) :- ASub1==ASub2.
fixpoint_covered(AbsInt,Prime0,Prime1) :-
	absub_fixpoint_covered(AbsInt,Prime0,Prime1).
fixpoint_covered_gfp(AbsInt,Prime0,Prime1) :-
	absub_fixpoint_covered(AbsInt,Prime0,Prime1).
eliminate_equivalent(_AbsInt,TmpLSucc,LSucc) :- sort(TmpLSucc,LSucc). % TODO: valid if ASub1==ASub2 means equivalent
abs_subset(_AbsInt,LASub1,LASub2) :-
	ord_subset(LASub1,LASub2).
body_succ_builtin(AbsInt,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :-
	body_builtin(AbsInt,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).
call_to_success_builtin(AbsInt,SgKey,_Sg,_Sv,_Call,_Proj,'$bottom') :-
	undef_call_to_success_builtin(AbsInt,SgKey).
part_conc(_AbsInt,Sg,Subs,Sg,Subs).
multi_part_conc(_AbsInt,Sg,Subs,[(Sg,Subs)]).
rename_abstypes_abs(_,ASub,_Rens,ASub).
dom_statistics(_AbsInt, []).
% contains_parameters(_AbsInt,_) :- fail.


