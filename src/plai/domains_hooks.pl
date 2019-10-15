% ===========================================================================
% Hooks for domain implementations

:- use_package(aidomain).

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
:- discontiguous(combined_special_builtin0/3).
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
:- dom_def(pd).
:- dom_op(pd, call_to_entry/9).
:- dom_op(pd, exit_to_prime/7).
:- dom_op(pd, project/5).
:- dom_op(pd, compute_lub/2).
:- dom_op(pd, abs_sort/2).
:- dom_op(pd, extend/5).
:- dom_op(pd, less_or_equal/2).
:- dom_op(pd, glb/3).
:- dom_op(pd, call_to_success_fact/9).
:- dom_op(pd, special_builtin/5).
:- dom_op(pd, success_builtin/6).
:- dom_op(pd, call_to_success_builtin/6).
:- dom_op(pd, input_user_interface/5).
:- dom_op(pd, asub_to_native/5).
:- dom_op(pd, unknown_call/4).
:- dom_op(pd, unknown_entry/3).
:- dom_op(pd, empty_entry/3).
% ---------------------------------------------------------------------------
% PD domain with bottom
:- use_module(domain(pdb)).
:- dom_def(pdb).
:- dom_op(pdb, call_to_entry/9).
:- dom_op(pdb, exit_to_prime/7).
:- dom_op(pdb, project/5).
:- dom_op(pdb, compute_lub/2).
:- dom_op(pdb, abs_sort/2).
:- dom_op(pdb, extend/5).
:- dom_op(pdb, less_or_equal/2).
:- dom_op(pdb, glb/3).
:- dom_op(pdb, call_to_success_fact/9).
:- dom_op(pdb, special_builtin/5).
:- dom_op(pdb, success_builtin/6).
:- dom_op(pdb, call_to_success_builtin/6).
:- dom_op(pdb, input_user_interface/5).
:- dom_op(pdb, asub_to_native/5).
:- dom_op(pdb, unknown_call/4).
:- dom_op(pdb, unknown_entry/3).
:- dom_op(pdb, empty_entry/3).
% ===========================================================================
:- doc(section, "Constraint domains").
% ---------------------------------------------------------------------------
:- use_module(domain(fr_top)).
:- dom_def(fr).
:- dom_op(fr, call_to_entry/9).
:- dom_op(fr, exit_to_prime/7).
:- dom_op(fr, project/5).
:- dom_op(fr, compute_lub/2).
:- dom_op(fr, identical_abstract/2).
:- dom_op(fr, abs_sort/2).
:- dom_op(fr, extend/5).
:- dom_op(fr, less_or_equal/2).
:- dom_op(fr, glb/3).
:- dom_op(fr, call_to_success_fact/9).
:- dom_op(fr, special_builtin/5).
:- dom_op(fr, success_builtin/6).
:- dom_op(fr, input_interface/4).
:- dom_op(fr, input_user_interface/5).
:- dom_op(fr, asub_to_native/5).
:- dom_op(fr, unknown_call/4).
:- dom_op(fr, unknown_entry/3).
:- dom_op(fr, empty_entry/3).
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef
% ---------------------------------------------------------------------------
:- use_module(domain(fd)).
:- dom_def(frdef).
:- dom_op(frdef, call_to_entry/9).
:- dom_op(frdef, exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime), exit_to_prime(Exit,Sg,Hv,Head,Sv,ExtraInfo,Prime)).
:- dom_op(frdef, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(frdef, compute_lub/2).
:- dom_op(frdef, identical_abstract/2).
:- dom_op(frdef, abs_sort/2).
:- dom_op(frdef, extend/5).
:- dom_op(frdef, less_or_equal/2).
:- dom_op(frdef, glb/3).
:- dom_op(frdef, call_to_success_fact/9).
:- dom_op(frdef, special_builtin/5).
:- dom_op(frdef, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(frdef, input_interface/4).
:- dom_op(frdef, input_user_interface/5).
:- dom_op(frdef, asub_to_native/5).
:- dom_op(frdef, unknown_call/4).
:- dom_op(frdef, unknown_entry/3).
:- dom_op(frdef, empty_entry/3).
% ---------------------------------------------------------------------------
% lsign
:- use_module(domain(lsign)).
:- dom_def(lsign).
:- dom_op(lsign, init_abstract_domain/1).
:- dom_op(lsign, call_to_entry/9).
:- dom_op(lsign, exit_to_prime(Sg,Hv,Head,_Sv,Exit,ExtraInfo,Prime), exit_to_prime(Sg,Hv,Head,Exit,ExtraInfo,Prime)).
:- dom_op(lsign, project(_Sg,Vars,HvFv,ASub,Proj), project(ASub,Vars,HvFv,Proj)).
:- dom_op(lsign, compute_lub/2).
:- dom_op(lsign, abs_sort/2).
:- dom_op(lsign, extend/5).
:- dom_op(lsign, less_or_equal/2).
:- dom_op(lsign, glb/3).
:- dom_op(lsign, eliminate_equivalent/2).
:- dom_op(lsign, abs_subset/2).
:- dom_op(lsign, call_to_success_fact/9).
:- dom_op(lsign, special_builtin/5).
:- dom_op(lsign, success_builtin/6).
:- dom_op(lsign, input_interface/4).
:- dom_op(lsign, input_user_interface/5).
:- dom_op(lsign, asub_to_native/5).
:- dom_op(lsign, unknown_call/4).
:- dom_op(lsign, unknown_entry/3).
:- dom_op(lsign, empty_entry/3).
% ---------------------------------------------------------------------------
% lsigndiff
:- use_module(domain(lsigndiff)).
:- dom_def(difflsign).
:- dom_op(difflsign, call_to_entry/9).
:- dom_op(difflsign, exit_to_prime(Sg,Hv,Head,_Sv,Exit,ExtraInfo,Prime), exit_to_prime(Sg,Hv,Head,Exit,ExtraInfo,Prime)).
:- dom_op(difflsign, project/5).
:- dom_op(difflsign, compute_lub/2).
:- dom_op(difflsign, abs_sort/2).
:- dom_op(difflsign, extend/5).
:- dom_op(difflsign, less_or_equal/2).
:- dom_op(difflsign, glb/3).
:- dom_op(difflsign, call_to_success_fact/9).
:- dom_op(difflsign, special_builtin/5).
:- dom_op(difflsign, success_builtin/6).
:- dom_op(difflsign, input_interface/4).
:- dom_op(difflsign, input_user_interface/5).
:- dom_op(difflsign, asub_to_native/5).
:- dom_op(difflsign, unknown_call/4).
:- dom_op(difflsign, unknown_entry/3).
:- dom_op(difflsign, empty_entry/3).
% ===========================================================================
:- doc(section, "Groundness and sharing").
% ---------------------------------------------------------------------------
% Example groundness domain
:- use_module(domain(gr)).
:- dom_def(gr).
:- dom_op(gr, call_to_entry/9).
:- dom_op(gr, exit_to_prime/7).
:- dom_op(gr, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(gr, compute_lub/2).
:- dom_op(gr, abs_sort/2).
:- dom_op(gr, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(gr, less_or_equal/2).
:- dom_op(gr, glb/3).
:- dom_op(gr, call_to_success_fact/9).
:- dom_op(gr, special_builtin/5).
:- dom_op(gr, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(gr, call_to_success_builtin/6).
:- dom_op(gr, input_interface/4).
:- dom_op(gr, input_user_interface/5).
:- dom_op(gr, asub_to_native/5).
:- dom_op(gr, unknown_call/4).
:- dom_op(gr, unknown_entry/3).
:- dom_op(gr, empty_entry/3).
% :- dom_op(gr, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_op(gr, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% ---------------------------------------------------------------------------
:- use_module(domain(def)).
:- dom_def(def).
:- dom_op(def, call_to_entry/9).
:- dom_op(def, exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime), exit_to_prime(Exit,ExtraInfo,Hv,Sv,Head,Sg,Prime)).
:- dom_op(def, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(def, compute_lub/2).
:- dom_op(def, abs_sort/2).
:- dom_op(def, extend(_Sg,Prime,_Sv,Call,Succ), extend(Prime,Call,Succ)).
:- dom_op(def, less_or_equal/2).
:- dom_op(def, glb/3).
:- dom_op(def, call_to_success_fact/9).
:- dom_op(def, special_builtin/5).
:- dom_op(def, success_builtin(Type,_Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Condvars,Call,Succ)).
:- dom_op(def, input_interface/4).
:- dom_op(def, input_user_interface/5).
:- dom_op(def, asub_to_native/5).
:- dom_op(def, unknown_call/4).
:- dom_op(def, unknown_entry/3).
:- dom_op(def, empty_entry/3).
% :- dom_op(def, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_op(def, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_op(def, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_op(def, more_instantiate(ASub1,ASub2), less_or_equal(ASub2,ASub1)).
% :- dom_op(def, convex_hull(Old,_,Old)).
% :- dom_op(def, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_op(def, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_op(def, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
%
%% def_check_cond(_,_,_,_,_). 
%% def_downwards_closed(_,_,_).
%% def_hash(_,_,_).
%% def_impose_cond(_,_,_,_).
%% def_real_conjoin(_,_,_).
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef
% ---------------------------------------------------------------------------
:- use_module(domain(sharing)).
:- dom_def(share).
:- dom_op(share, amgu/4, from(share_amgu)).
:- dom_op(share, augment_asub/3, from(share_amgu)).
:- dom_op(share, augment_two_asub/3, from(share_amgu)).
:- dom_op(share, call_to_entry/9).
:- dom_op(share, exit_to_prime/7).
:- dom_op(share, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(share, compute_lub/2).
:- dom_op(share, abs_sort/2).
:- dom_op(share, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(share, less_or_equal/2).
:- dom_op(share, glb/3).
:- dom_op(share, call_to_success_fact/9).
:- dom_op(share, special_builtin/5).
:- dom_op(share, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(share, call_to_success_builtin/6).
:- dom_op(share, input_interface/4).
:- dom_op(share, input_user_interface/5).
:- dom_op(share, asub_to_native/5).
:- dom_op(share, unknown_call/4).
:- dom_op(share, unknown_entry/3).
:- dom_op(share, empty_entry/3).
% :- dom_op(share, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharefree)).
:- dom_def(shfr).
:- dom_op(shfr, amgu/4, from(sharefree_amgu)).
:- dom_op(shfr, augment_asub/3, from(sharefree_amgu)).
:- dom_op(shfr, call_to_entry/9).
:- dom_op(shfr, exit_to_prime/7).
:- dom_op(shfr, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(shfr, compute_lub/2).
:- dom_op(shfr, abs_sort/2).
:- dom_op(shfr, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(shfr, less_or_equal/2).
:- dom_op(shfr, glb/3).
:- dom_op(shfr, call_to_success_fact/9).
:- dom_op(shfr, special_builtin/5).
:- dom_op(shfr, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(shfr, call_to_success_builtin/6).
:- dom_op(shfr, obtain_info/4).
:- dom_op(shfr, input_interface/4).
:- dom_op(shfr, input_user_interface/5).
:- dom_op(shfr, asub_to_native/5).
:- dom_op(shfr, unknown_call/4).
:- dom_op(shfr, unknown_entry/3).
:- dom_op(shfr, empty_entry/3).
% :- dom_op(shfr, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_op(shfr, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_op(shfr, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_op(shfr, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_op(shfr, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_op(shfr, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_op(shfr, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% :- dom_op(shfr, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_op(shfr, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
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
:- dom_def(shfrnv).
:- dom_op(shfrnv, call_to_entry/9).
:- dom_op(shfrnv, exit_to_prime/7).
:- dom_op(shfrnv, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj), from(shfr)).
:- dom_op(shfrnv, compute_lub/2).
:- dom_op(shfrnv, abs_sort/2, from(shfr)).
:- dom_op(shfrnv, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(shfrnv, less_or_equal/2).
:- dom_op(shfrnv, glb/3).
:- dom_op(shfrnv, call_to_success_fact/9).
:- dom_op(shfrnv, special_builtin/5, from(shfr)).
:- dom_op(shfrnv, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(shfrnv, call_to_success_builtin/6).
:- dom_op(shfrnv, input_interface/4).
:- dom_op(shfrnv, input_user_interface/5).
:- dom_op(shfrnv, asub_to_native/5).
:- dom_op(shfrnv, unknown_call/4, from(shfr)).
:- dom_op(shfrnv, unknown_entry/3, from(shfr)).
:- dom_op(shfrnv, empty_entry/3, from(shfr)).
%
% :- dom_op(shfrnv, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_op(shfrnv, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_op(shfrnv, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_op(shfrnv, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_op(shfrnv, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_op(shfrnv, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_op(shfrnv, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub), from(shfr)).
% :- dom_op(shfrnv, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_op(shfrnv, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
%
%% shfrnv_check_cond(_,_,_,_,_).
%% shfrnv_compute_lub_el(_,_,_).  
%% shfrnv_convex_hull(_,_,_).
%% shfrnv_downwards_closed(_,_,_). 
%% shfrnv_hash(_,_,_).    
%% shfrnv_impose_cond(_,_,_,_).
%% shfrnv_more_instantiate(_,_). 
%% shfrnv_real_conjoin(_,_,_).
% ---------------------------------------------------------------------------
:- use_module(domain(shfret)). % TODO: this domain was not registerd in aidomain/1
:- dom_def(shfret).
:- dom_op(shfret, init_abstract_domain/1).
:- dom_op(shfret, call_to_entry/9).
:- dom_op(shfret, exit_to_prime/7).
:- dom_op(shfret, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(shfret, widencall/3).
:- dom_op(shfret, widen/3).
:- dom_op(shfret, compute_lub/2).
:- dom_op(shfret, identical_abstract/2).
:- dom_op(shfret, abs_sort/2).
:- dom_op(shfret, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(shfret, less_or_equal/2).
:- dom_op(shfret, glb/3).
:- dom_op(shfret, eliminate_equivalent/2).
:- dom_op(shfret, call_to_success_fact/9).
:- dom_op(shfret, combined_special_builtin0/2).
:- dom_op(shfret, split_combined_domain/3).
:- dom_op(shfret, input_interface/4).
:- dom_op(shfret, input_user_interface/5).
:- dom_op(shfret, asub_to_native/5).
:- dom_op(shfret, unknown_call/4).
:- dom_op(shfret, unknown_entry/3).
:- dom_op(shfret, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(shareson)).
:- dom_def(shareson).
:- dom_op(shareson, call_to_entry/9).
:- dom_op(shareson, exit_to_prime/7).
:- dom_op(shareson, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(shareson, compute_lub/2).
:- dom_op(shareson, abs_sort/2).
:- dom_op(shareson, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(shareson, less_or_equal/2).
:- dom_op(shareson, glb/3).
:- dom_op(shareson, call_to_success_fact/9).
:- dom_op(shareson, special_builtin/5).
:- dom_op(shareson, body_succ_builtin/8).
:- dom_op(shareson, input_interface/4).
:- dom_op(shareson, input_user_interface/5).
:- dom_op(shareson, asub_to_native/5).
:- dom_op(shareson, unknown_call/4).
:- dom_op(shareson, unknown_entry/3).
:- dom_op(shareson, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(shfrson)).
:- dom_def(shfrson).
:- dom_op(shfrson, call_to_entry/9).
:- dom_op(shfrson, exit_to_prime/7).
:- dom_op(shfrson, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(shfrson, compute_lub/2).
:- dom_op(shfrson, abs_sort/2).
:- dom_op(shfrson, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(shfrson, less_or_equal/2).
:- dom_op(shfrson, glb/3).
:- dom_op(shfrson, call_to_success_fact/9).
:- dom_op(shfrson, special_builtin/5).
:- dom_op(shfrson, body_succ_builtin/8).
:- dom_op(shfrson, input_interface/4).
:- dom_op(shfrson, input_user_interface/5).
:- dom_op(shfrson, asub_to_native/5).
:- dom_op(shfrson, unknown_call/4).
:- dom_op(shfrson, unknown_entry/3).
:- dom_op(shfrson, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(sondergaard)).
:- dom_def(son).
:- dom_op(son, call_to_entry/9).
:- dom_op(son, exit_to_prime/7).
:- dom_op(son, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(son, compute_lub/2).
:- dom_op(son, abs_sort/2).
:- dom_op(son, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(son, less_or_equal/2).
:- dom_op(son, glb/3).
:- dom_op(son, call_to_success_fact/9).
:- dom_op(son, special_builtin/5).
:- dom_op(son, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(son, call_to_success_builtin/6).
:- dom_op(son, input_interface/4).
:- dom_op(son, input_user_interface/5).
:- dom_op(son, asub_to_native/5).
:- dom_op(son, unknown_call/4).
:- dom_op(son, unknown_entry/3).
:- dom_op(son, empty_entry/3).
% :- dom_op(son, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% ---------------------------------------------------------------------------
:- use_module(domain(sharing_amgu)).
:- dom_def(share_amgu).
:- dom_op(share_amgu, amgu/4).
:- dom_op(share_amgu, augment_asub/3).
:- dom_op(share_amgu, augment_two_asub/3).
:- dom_op(share_amgu, call_to_entry/9).
:- dom_op(share_amgu, exit_to_prime/7).
:- dom_op(share_amgu, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj), from(share)).
:- dom_op(share_amgu, compute_lub/2, from(share)).
:- dom_op(share_amgu, abs_sort/2, from(share)).
:- dom_op(share_amgu, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ), from(share)).
:- dom_op(share_amgu, less_or_equal/2, from(share)).
:- dom_op(share_amgu, glb/3, from(share)).
:- dom_op(share_amgu, call_to_success_fact/9).
:- dom_op(share_amgu, special_builtin/5).
:- dom_op(share_amgu, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(share_amgu, call_to_success_builtin/6).
:- dom_op(share_amgu, input_interface/4, from(share)).
:- dom_op(share_amgu, input_user_interface/5, from(share)).
:- dom_op(share_amgu, asub_to_native/5, from(share)).
:- dom_op(share_amgu, unknown_call/4, from(share)).
:- dom_op(share_amgu, unknown_entry/3, from(share)).
:- dom_op(share_amgu, empty_entry/3, from(share)).
% :- dom_op(share_amgu, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub), from(share)).
% ----------
:- use_module(domain(sharefree_amgu)).
:- dom_def(sharefree_amgu).
:- dom_op(sharefree_amgu, amgu/4).
:- dom_op(sharefree_amgu, augment_asub/3).
:- dom_op(sharefree_amgu, call_to_entry/9).
:- dom_op(sharefree_amgu, exit_to_prime/7).
:- dom_op(sharefree_amgu, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj), from(shfr)).
:- dom_op(sharefree_amgu, compute_lub/2, from(shfr)).
:- dom_op(sharefree_amgu, abs_sort/2, from(shfr)).
:- dom_op(sharefree_amgu, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ), from(shfr)).
:- dom_op(sharefree_amgu, less_or_equal/2, from(shfr)).
:- dom_op(sharefree_amgu, glb/3, from(shfr)).
:- dom_op(sharefree_amgu, call_to_success_fact/9).
:- dom_op(sharefree_amgu, special_builtin/5).
:- dom_op(sharefree_amgu, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(sharefree_amgu, call_to_success_builtin/6).
:- dom_op(sharefree_amgu, obtain_info/4, from(shfr)).
:- dom_op(sharefree_amgu, input_interface/4, from(shfr)).
:- dom_op(sharefree_amgu, input_user_interface/5, from(shfr)).
:- dom_op(sharefree_amgu, asub_to_native/5, from(shfr)).
:- dom_op(sharefree_amgu, unknown_call/4, from(shfr)).
:- dom_op(sharefree_amgu, unknown_entry/3, from(shfr)).
:- dom_op(sharefree_amgu, empty_entry/3, from(shfr)).
% ----------
:- use_module(domain(shfrlin_amgu)).
:- dom_def(shfrlin_amgu).
:- dom_op(shfrlin_amgu, amgu/4).
:- dom_op(shfrlin_amgu, augment_asub/3).
:- dom_op(shfrlin_amgu, call_to_entry/9).
:- dom_op(shfrlin_amgu, exit_to_prime/7).
:- dom_op(shfrlin_amgu, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(shfrlin_amgu, compute_lub/2).
:- dom_op(shfrlin_amgu, abs_sort/2).
:- dom_op(shfrlin_amgu, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(shfrlin_amgu, less_or_equal/2).
:- dom_op(shfrlin_amgu, glb/3).
:- dom_op(shfrlin_amgu, call_to_success_fact/9).
:- dom_op(shfrlin_amgu, special_builtin/5).
:- dom_op(shfrlin_amgu, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(shfrlin_amgu, call_to_success_builtin/6).
:- dom_op(shfrlin_amgu, obtain_info/4).
:- dom_op(shfrlin_amgu, input_interface/4).
:- dom_op(shfrlin_amgu, input_user_interface/5).
:- dom_op(shfrlin_amgu, asub_to_native/5).
:- dom_op(shfrlin_amgu, unknown_call/4).
:- dom_op(shfrlin_amgu, unknown_entry/3).
:- dom_op(shfrlin_amgu, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(sharing_clique)).
:- dom_def(share_clique).
:- dom_op(share_clique, amgu/4).
:- dom_op(share_clique, augment_asub/3).
:- dom_op(share_clique, call_to_entry/9).
:- dom_op(share_clique, exit_to_prime/7).
:- dom_op(share_clique, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(share_clique, compute_lub/2).
:- dom_op(share_clique, identical_abstract/2).
:- dom_op(share_clique, abs_sort/2).
:- dom_op(share_clique, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(share_clique, less_or_equal/2).
:- dom_op(share_clique, glb/3).
:- dom_op(share_clique, eliminate_equivalent/2).
:- dom_op(share_clique, call_to_success_fact/9).
:- dom_op(share_clique, special_builtin/5).
:- dom_op(share_clique, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(share_clique, call_to_success_builtin/6).
:- dom_op(share_clique, input_interface/4).
:- dom_op(share_clique, input_user_interface/5).
:- dom_op(share_clique, asub_to_native/5).
:- dom_op(share_clique, unknown_call/4).
:- dom_op(share_clique, unknown_entry/3).
:- dom_op(share_clique, empty_entry/3).
% :- dom_op(share_clique, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharing_clique_1)).
:- dom_def(share_clique_1).
:- dom_op(share_clique_1, call_to_entry/9).
:- dom_op(share_clique_1, exit_to_prime/7).
:- dom_op(share_clique_1, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(share_clique_1, compute_lub/2).
:- dom_op(share_clique_1, identical_abstract/2).
:- dom_op(share_clique_1, abs_sort/2, from(share_clique)).
:- dom_op(share_clique_1, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(share_clique_1, less_or_equal/2).
:- dom_op(share_clique_1, glb/3).
:- dom_op(share_clique_1, eliminate_equivalent/2).
:- dom_op(share_clique_1, call_to_success_fact/9).
:- dom_op(share_clique_1, special_builtin/5, from(share_clique)).
:- dom_op(share_clique_1, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(share_clique_1, call_to_success_builtin/6).
:- dom_op(share_clique_1, input_interface/4).
:- dom_op(share_clique_1, input_user_interface/5, from(share_clique)).
:- dom_op(share_clique_1, asub_to_native/5).
:- dom_op(share_clique_1, unknown_call/4).
:- dom_op(share_clique_1, unknown_entry/3).
:- dom_op(share_clique_1, empty_entry/3, from(share_clique)).
% :- dom_op(share_clique_1, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharefree_clique)).
:- dom_def(sharefree_clique).
:- dom_op(sharefree_clique, amgu/4).
:- dom_op(sharefree_clique, augment_asub/3).
:- dom_op(sharefree_clique, call_to_entry/9).
:- dom_op(sharefree_clique, exit_to_prime/7).
:- dom_op(sharefree_clique, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(sharefree_clique, compute_lub/2).
:- dom_op(sharefree_clique, identical_abstract/2).
:- dom_op(sharefree_clique, abs_sort/2).
:- dom_op(sharefree_clique, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(sharefree_clique, less_or_equal/2).
:- dom_op(sharefree_clique, glb/3).
:- dom_op(sharefree_clique, eliminate_equivalent/2).
:- dom_op(sharefree_clique, call_to_success_fact/9).
:- dom_op(sharefree_clique, special_builtin/5).
:- dom_op(sharefree_clique, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(sharefree_clique, call_to_success_builtin/6).
:- dom_op(sharefree_clique, obtain_info/4, from(shfr)).
:- dom_op(sharefree_clique, input_interface/4).
:- dom_op(sharefree_clique, input_user_interface/5).
:- dom_op(sharefree_clique, asub_to_native/5).
:- dom_op(sharefree_clique, unknown_call/4).
:- dom_op(sharefree_clique, unknown_entry/3).
:- dom_op(sharefree_clique, empty_entry/3).
% :- dom_op(sharefree_clique, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharing_clique_def)).
:- dom_def(share_clique_def).
:- dom_op(share_clique_def, call_to_entry/9).
:- dom_op(share_clique_def, exit_to_prime/7).
:- dom_op(share_clique_def, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(share_clique_def, compute_lub/2).
:- dom_op(share_clique_def, identical_abstract/2).
:- dom_op(share_clique_def, abs_sort/2).
:- dom_op(share_clique_def, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(share_clique_def, less_or_equal/2).
:- dom_op(share_clique_def, glb/3).
:- dom_op(share_clique_def, eliminate_equivalent/2).
:- dom_op(share_clique_def, call_to_success_fact/9).
:- dom_op(share_clique_def, special_builtin/5).
:- dom_op(share_clique_def, body_succ_builtin/8).
:- dom_op(share_clique_def, input_interface/4, from(share_clique)).
:- dom_op(share_clique_def, input_user_interface/5).
:- dom_op(share_clique_def, asub_to_native/5).
:- dom_op(share_clique_def, unknown_call/4).
:- dom_op(share_clique_def, unknown_entry/3).
:- dom_op(share_clique_def, empty_entry/3).
% :- dom_op(share_clique_def, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
%
% ----------
:- use_module(domain(sharefree_clique_def)).
:- dom_def(sharefree_clique_def).
:- dom_op(sharefree_clique_def, call_to_entry/9).
:- dom_op(sharefree_clique_def, exit_to_prime/7).
:- dom_op(sharefree_clique_def, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(sharefree_clique_def, compute_lub/2).
:- dom_op(sharefree_clique_def, identical_abstract/2).
:- dom_op(sharefree_clique_def, abs_sort/2).
:- dom_op(sharefree_clique_def, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(sharefree_clique_def, less_or_equal/2).
:- dom_op(sharefree_clique_def, glb/3).
:- dom_op(sharefree_clique_def, eliminate_equivalent/2).
:- dom_op(sharefree_clique_def, call_to_success_fact/9).
:- dom_op(sharefree_clique_def, special_builtin/5).
:- dom_op(sharefree_clique_def, body_succ_builtin/8).
:- dom_op(sharefree_clique_def, input_interface/4, from(sharefree_clique)).
:- dom_op(sharefree_clique_def, input_user_interface/5).
:- dom_op(sharefree_clique_def, asub_to_native/5).
:- dom_op(sharefree_clique_def, unknown_call/4).
:- dom_op(sharefree_clique_def, unknown_entry/3).
:- dom_op(sharefree_clique_def, empty_entry/3).
% :- dom_op(sharefree_clique_def, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(bshare/bshare)).
:- dom_def(bshare).
:- dom_op(bshare, amgu/4).
:- dom_op(bshare, augment_asub/3).
:- dom_op(bshare, augment_two_asub/3).
:- dom_op(bshare, call_to_entry/9).
:- dom_op(bshare, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(bshare, compute_lub/2).
:- dom_op(bshare, identical_abstract/2).
:- dom_op(bshare, abs_sort/2).
:- dom_op(bshare, call_to_success_fact/9).
:- dom_op(bshare, special_builtin/5).
:- dom_op(bshare, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(bshare, call_to_success_builtin/6).
:- dom_op(bshare, asub_to_native/5).
:- dom_op(bshare, unknown_entry/3).
:- dom_op(bshare, empty_entry/3).
% :- dom_op(bshare, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
:- endif.
% ===========================================================================
:- doc(section, "Structure domains"). % TODO: shape also?
% ---------------------------------------------------------------------------
:- use_module(domain(aeq_top)).
:- dom_def(aeq).
:- dom_op(aeq, call_to_entry/9).
:- dom_op(aeq, exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime), exit_to_prime(Exit,Sg,Hv,Head,Sv,ExtraInfo,Prime)).
:- dom_op(aeq, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(aeq, compute_lub/2).
:- dom_op(aeq, identical_abstract/2).
:- dom_op(aeq, abs_sort/2).
:- dom_op(aeq, extend(_Sg,Prime,_Sv,Call,Succ), extend(Prime,Call,Succ)).
:- dom_op(aeq, less_or_equal/2).
:- dom_op(aeq, glb/3).
:- dom_op(aeq, eliminate_equivalent/2).
:- dom_op(aeq, call_to_success_fact/9).
:- dom_op(aeq, special_builtin/5).
:- dom_op(aeq, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(aeq, input_interface/4).
:- dom_op(aeq, input_user_interface/5).
:- dom_op(aeq, asub_to_native/5).
:- dom_op(aeq, unknown_call/4).
:- dom_op(aeq, unknown_entry/3).
:- dom_op(aeq, empty_entry/3).
%
% :- dom_op(aeq, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_op(aeq, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_op(aeq, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_op(aeq, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_op(aeq, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_op(aeq, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% :- dom_op(aeq, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% :- dom_op(aeq, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_op(aeq, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
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
% ---------------------------------------------------------------------------
:- use_module(domain(depthk)).
:- dom_def(depthk).
:- dom_op(depthk, call_to_entry/9).
:- dom_op(depthk, exit_to_prime/7).
:- dom_op(depthk, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(depthk, compute_lub/2).
:- dom_op(depthk, identical_abstract/2).
:- dom_op(depthk, abs_sort/2).
:- dom_op(depthk, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(depthk, less_or_equal/2).
:- dom_op(depthk, glb/3).
:- dom_op(depthk, eliminate_equivalent/2).
:- dom_op(depthk, abs_subset/2).
:- dom_op(depthk, call_to_success_fact/9).
:- dom_op(depthk, special_builtin/5).
:- dom_op(depthk, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(depthk, call_to_success_builtin(_SgKey,Sg,Sv,Call,_Proj,Succ), call_to_success_builtin(Sg,Sv,Call,Succ)).
:- dom_op(depthk, input_interface/4).
:- dom_op(depthk, input_user_interface/5).
:- dom_op(depthk, asub_to_native/5).
:- dom_op(depthk, unknown_call/4).
:- dom_op(depthk, unknown_entry/3).
:- dom_op(depthk, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(top_path_sharing)).
:- dom_def(path).
:- dom_op(path, init_abstract_domain/1).
:- dom_op(path, call_to_entry/9).
:- dom_op(path, exit_to_prime/7).
:- dom_op(path, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(path, compute_lub/2).
:- dom_op(path, abs_sort/2).
:- dom_op(path, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(path, less_or_equal/2).
:- dom_op(path, glb/3).
:- dom_op(path, call_to_success_fact/9).
:- dom_op(path, special_builtin/5).
:- dom_op(path, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(path, input_interface/4).
:- dom_op(path, input_user_interface/5).
:- dom_op(path, asub_to_native/5).
:- dom_op(path, unknown_call/4).
:- dom_op(path, unknown_entry/3).
:- dom_op(path, empty_entry/3).
% ===========================================================================
:- doc(section, "Type domains"). % TODO: shape/structure?
% ---------------------------------------------------------------------------
:- use_module(domain(termsd)).
:- dom_def(terms).
:- dom_op(terms, init_abstract_domain/1).
:- dom_op(terms, call_to_entry/9).
:- dom_op(terms, exit_to_prime/7).
:- dom_op(terms, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(terms, widencall/3).
:- dom_op(terms, widen/3).
:- dom_op(terms, compute_lub/2).
:- dom_op(terms, identical_abstract/2).
:- dom_op(terms, abs_sort/2).
:- dom_op(terms, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(terms, less_or_equal/2).
:- dom_op(terms, glb/3).
:- dom_op(terms, call_to_success_fact/9).
:- dom_op(terms, special_builtin/5).
:- dom_op(terms, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(terms, call_to_success_builtin/6).
:- dom_op(terms, input_interface/4).
:- dom_op(terms, input_user_interface/5).
:- dom_op(terms, asub_to_native/5).
:- dom_op(terms, concrete/3).
:- dom_op(terms, unknown_call/4).
:- dom_op(terms, unknown_entry/3).
:- dom_op(terms, empty_entry/3).
:- dom_op(terms, collect_abstypes_abs/3).
:- dom_op(terms, rename_abstypes_abs/3).
% ---------------------------------------------------------------------------
:- use_module(domain(ptypes)).
:- dom_def(ptypes).
:- dom_op(ptypes, init_abstract_domain/1).
:- dom_op(ptypes, call_to_entry/9).
:- dom_op(ptypes, exit_to_prime/7).
:- dom_op(ptypes, widencall/3).
:- dom_op(ptypes, widen/3).
:- dom_op(ptypes, compute_lub/2).
:- dom_op(ptypes, identical_abstract/2).
:- dom_op(ptypes, abs_sort/2).
:- dom_op(ptypes, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(ptypes, less_or_equal/2).
:- dom_op(ptypes, glb/3).
:- dom_op(ptypes, call_to_success_fact/9).
:- dom_op(ptypes, special_builtin/5).
:- dom_op(ptypes, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(ptypes, call_to_success_builtin/6).
:- dom_op(ptypes, input_interface/4).
:- dom_op(ptypes, input_user_interface/5).
:- dom_op(ptypes, asub_to_native/5).
:- dom_op(ptypes, concrete/3).
:- dom_op(ptypes, unknown_call/4).
:- dom_op(ptypes, unknown_entry/3).
:- dom_op(ptypes, empty_entry/3).
:- dom_op(ptypes, collect_abstypes_abs/3).
% :- dom_op(ptypes, rename_abstypes_abs/3). % TODO: missing, why?
%
% ---------------------------------------------------------------------------
:- use_module(domain(eterms)).
:- dom_def(eterms).
:- dom_op(eterms, init_abstract_domain/1).
:- dom_op(eterms, call_to_entry/9).
:- dom_op(eterms, exit_to_prime/7).
:- dom_op(eterms, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(eterms, widencall/3).
:- dom_op(eterms, widen/3).
:- dom_op(eterms, compute_lub/2).
:- dom_op(eterms, identical_abstract/2).
:- dom_op(eterms, abs_sort/2).
:- dom_op(eterms, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(eterms, less_or_equal/2).
:- dom_op(eterms, glb/3).
:- dom_op(eterms, call_to_success_fact/9).
:- dom_op(eterms, special_builtin/5).
:- dom_op(eterms, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(eterms, call_to_success_builtin/6).
:- dom_op(eterms, obtain_info/4).
:- dom_op(eterms, input_interface/4).
:- dom_op(eterms, input_user_interface/5).
:- dom_op(eterms, asub_to_native/5).
:- dom_op(eterms, concrete/3).
:- dom_op(eterms, unknown_call/4).
:- dom_op(eterms, unknown_entry/3).
:- dom_op(eterms, empty_entry/3).
:- dom_op(eterms, part_conc/4).
:- dom_op(eterms, multi_part_conc/3).
:- dom_op(eterms, collect_abstypes_abs/3).
:- dom_op(eterms, rename_abstypes_abs/3).
%
% ---------------------------------------------------------------------------
:- use_module(domain(etermsvar)).
:- dom_def(etermsvar).
:- dom_op(etermsvar, init_abstract_domain/1).
:- dom_op(etermsvar, call_to_entry/9).
:- dom_op(etermsvar, exit_to_prime/7).
:- dom_op(etermsvar, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(etermsvar, widencall/3).
:- dom_op(etermsvar, widen/3).
:- dom_op(etermsvar, compute_lub/2).
:- dom_op(etermsvar, identical_abstract/2).
:- dom_op(etermsvar, abs_sort/2).
:- dom_op(etermsvar, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(etermsvar, less_or_equal/2).
:- dom_op(etermsvar, glb/3).
:- dom_op(etermsvar, call_to_success_fact/9).
:- dom_op(etermsvar, special_builtin/5).
:- dom_op(etermsvar, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(etermsvar, call_to_success_builtin/6).
:- dom_op(etermsvar, obtain_info/4).
:- dom_op(etermsvar, input_interface/4).
:- dom_op(etermsvar, input_user_interface/5).
:- dom_op(etermsvar, asub_to_native/5).
% :- dom_op(etermsvar, concrete/3).
:- dom_op(etermsvar, unknown_call/4).
:- dom_op(etermsvar, unknown_entry/3).
:- dom_op(etermsvar, empty_entry/3).
:- dom_op(etermsvar, part_conc/4).
:- dom_op(etermsvar, multi_part_conc/3).
:- dom_op(etermsvar, collect_abstypes_abs/3).
:- dom_op(etermsvar, rename_abstypes_abs/3).
% ---------------------------------------------------------------------------
:- use_module(domain(svterms)).
:- dom_def(svterms).
:- dom_op(svterms, init_abstract_domain/1).
:- dom_op(svterms, call_to_entry/9).
:- dom_op(svterms, exit_to_prime/7).
:- dom_op(svterms, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(svterms, widencall/3).
:- dom_op(svterms, widen/3).
:- dom_op(svterms, compute_lub/2).
:- dom_op(svterms, identical_abstract/2).
:- dom_op(svterms, abs_sort/2).
:- dom_op(svterms, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(svterms, less_or_equal/2).
:- dom_op(svterms, glb/3).
:- dom_op(svterms, call_to_success_fact/9).
:- dom_op(svterms, special_builtin/5).
:- dom_op(svterms, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(svterms, call_to_success_builtin/6).
:- dom_op(svterms, input_interface/4).
:- dom_op(svterms, input_user_interface/5).
:- dom_op(svterms, asub_to_native/5).
:- dom_op(svterms, concrete/3).
:- dom_op(svterms, unknown_call/4).
:- dom_op(svterms, unknown_entry/3).
:- dom_op(svterms, empty_entry/3).
:- dom_op(svterms, collect_abstypes_abs/3).
:- dom_op(svterms, rename_abstypes_abs/3).
% ---------------------------------------------------------------------------
:- use_module(domain(deftypes)).
:- dom_def(deftypes).
:- dom_op(deftypes, init_abstract_domain/1).
:- dom_op(deftypes, call_to_entry/9).
:- dom_op(deftypes, exit_to_prime/7).
:- dom_op(deftypes, project(_Sg,Vars,_HvFv,ASub,Proj), project(Vars,ASub,Proj)).
:- dom_op(deftypes, widencall/3).
:- dom_op(deftypes, widen/3).
:- dom_op(deftypes, compute_lub/2).
:- dom_op(deftypes, identical_abstract/2).
:- dom_op(deftypes, abs_sort/2).
:- dom_op(deftypes, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(deftypes, less_or_equal/2).
:- dom_op(deftypes, glb/3).
:- dom_op(deftypes, call_to_success_fact/9).
:- dom_op(deftypes, special_builtin/5).
:- dom_op(deftypes, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(deftypes, call_to_success_builtin/6).
:- dom_op(deftypes, input_interface/4).
:- dom_op(deftypes, input_user_interface/5).
:- dom_op(deftypes, asub_to_native/5).
:- dom_op(deftypes, concrete/3).
:- dom_op(deftypes, unknown_call/4).
:- dom_op(deftypes, unknown_entry/3).
:- dom_op(deftypes, empty_entry/3).
:- dom_op(deftypes, collect_abstypes_abs/3).
:- dom_op(deftypes, rename_abstypes_abs/3).
:- dom_op(deftypes, contains_parameters/1).
%
% ===========================================================================
:- doc(section, "Numeric domains").
% ---------------------------------------------------------------------------
% intervals domain % [IG] new, simplified nonrelational domain
:- use_module(domain(nonrel)).
% (simpler domain interface, only for non-relational domains)
:- dom_def(nonrel_intervals).
:- dom_op(nonrel_intervals, init_abstract_domain/1).
:- dom_op(nonrel_intervals, amgu/4).
:- dom_op(nonrel_intervals, call_to_entry/9).
:- dom_op(nonrel_intervals, exit_to_prime/7).
:- dom_op(nonrel_intervals, project/5).
:- dom_op(nonrel_intervals, widencall/3).
:- dom_op(nonrel_intervals, widen/3).
:- dom_op(nonrel_intervals, compute_lub/2).
:- dom_op(nonrel_intervals, identical_abstract/2).
:- dom_op(nonrel_intervals, abs_sort/2).
:- dom_op(nonrel_intervals, extend/5).
:- dom_op(nonrel_intervals, less_or_equal/2).
:- dom_op(nonrel_intervals, glb/3).
:- dom_op(nonrel_intervals, call_to_success_fact/9).
:- dom_op(nonrel_intervals, special_builtin/5).
:- dom_op(nonrel_intervals, success_builtin/6).
:- dom_op(nonrel_intervals, call_to_success_builtin/6).
:- dom_op(nonrel_intervals, input_interface/4).
:- dom_op(nonrel_intervals, input_user_interface/5).
:- dom_op(nonrel_intervals, asub_to_native/5).
:- dom_op(nonrel_intervals, unknown_call/4).
:- dom_op(nonrel_intervals, unknown_entry/3).
:- dom_op(nonrel_intervals, empty_entry/3).
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(polyhedra)).
:- dom_def(polyhedra).
:- dom_op(polyhedra, init_abstract_domain/1).
:- dom_op(polyhedra, call_to_entry/9).
:- dom_op(polyhedra, exit_to_prime/7).
:- dom_op(polyhedra, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(polyhedra, widencall/3). 
:- dom_op(polyhedra, widen/3).
:- dom_op(polyhedra, compute_lub/2).
:- dom_op(polyhedra, identical_abstract/2).
:- dom_op(polyhedra, abs_sort/2).
:- dom_op(polyhedra, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(polyhedra, less_or_equal/2).
:- dom_op(polyhedra, glb/3).
:- dom_op(polyhedra, eliminate_equivalent/2).
:- dom_op(polyhedra, call_to_success_fact/9).
:- dom_op(polyhedra, special_builtin/5).
:- dom_op(polyhedra, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(polyhedra, call_to_success_builtin/6).
:- dom_op(polyhedra, input_interface/4).
:- dom_op(polyhedra, input_user_interface/5).
:- dom_op(polyhedra, asub_to_native/5).
:- dom_op(polyhedra, unknown_call/4).
:- dom_op(polyhedra, unknown_entry/3).
:- dom_op(polyhedra, empty_entry/3).
:- endif.
% ===========================================================================
:- doc(section, "OO/Java domains"). % TODO: imperative? points-to? nullity?
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(java_nullity)). % for java programs
:- dom_def(java_nullity).
:- dom_op(java_nullity, call_to_entry/9).
:- dom_op(java_nullity, exit_to_prime/7).
:- dom_op(java_nullity, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(java_nullity, compute_lub/2).
:- dom_op(java_nullity, abs_sort/2).
:- dom_op(java_nullity, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(java_nullity, less_or_equal/2).
:- dom_op(java_nullity, glb/3).
:- dom_op(java_nullity, call_to_success_fact/9).
:- dom_op(java_nullity, special_builtin/5).
:- dom_op(java_nullity, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(java_nullity, input_interface/4).
:- dom_op(java_nullity, input_user_interface/5).
:- dom_op(java_nullity, asub_to_native/5).
:- dom_op(java_nullity, unknown_call/4).
:- dom_op(java_nullity, unknown_entry/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_son)).
:- dom_def(oo_son).
:- dom_op(oo_son, call_to_entry/9).
:- dom_op(oo_son, exit_to_prime/7).
:- dom_op(oo_son, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(oo_son, compute_lub/2).
:- dom_op(oo_son, identical_abstract/2).
:- dom_op(oo_son, abs_sort/2).
:- dom_op(oo_son, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(oo_son, less_or_equal/2).
:- dom_op(oo_son, glb/3).
:- dom_op(oo_son, call_to_success_fact/9).
:- dom_op(oo_son, special_builtin/5).
:- dom_op(oo_son, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(oo_son, call_to_success_builtin/6).
:- dom_op(oo_son, input_interface/4).
:- dom_op(oo_son, input_user_interface/5).
:- dom_op(oo_son, asub_to_native/5).
:- dom_op(oo_son, unknown_call/4).
:- dom_op(oo_son, unknown_entry/3).
:- dom_op(oo_son, empty_entry/3).
% :- dom_op(oo_son, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_shnltau)).
:- dom_def(oo_shnltau).
% :- dom_op(oo_shnltau, init_abstract_domain/1).
:- dom_op(oo_shnltau, call_to_entry/9).
:- dom_op(oo_shnltau, exit_to_prime/7).
:- dom_op(oo_shnltau, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(oo_shnltau, compute_lub/2).
:- dom_op(oo_shnltau, abs_sort/2).
:- dom_op(oo_shnltau, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(oo_shnltau, less_or_equal/2).
:- dom_op(oo_shnltau, glb/3).
:- dom_op(oo_shnltau, call_to_success_fact/9).
:- dom_op(oo_shnltau, special_builtin/5).
:- dom_op(oo_shnltau, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(oo_shnltau, call_to_success_builtin/6).
:- dom_op(oo_shnltau, input_interface/4).
:- dom_op(oo_shnltau, input_user_interface/5).
:- dom_op(oo_shnltau, asub_to_native/5).
:- dom_op(oo_shnltau, unknown_call/4).
:- dom_op(oo_shnltau, unknown_entry/3).
:- dom_op(oo_shnltau, empty_entry/3).
% :- dom_op(oo_shnltau, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_types)).
:- dom_def(oo_types).
% :- dom_op(oo_types, init_abstract_domain/1).
:- dom_op(oo_types, call_to_entry/9).
:- dom_op(oo_types, exit_to_prime/7).
:- dom_op(oo_types, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(oo_types, compute_lub/2).
:- dom_op(oo_types, abs_sort/2).
:- dom_op(oo_types, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(oo_types, less_or_equal/2).
:- dom_op(oo_types, glb/3).
:- dom_op(oo_types, call_to_success_fact/9).
:- dom_op(oo_types, special_builtin/5).
:- dom_op(oo_types, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(oo_types, call_to_success_builtin/6).
:- dom_op(oo_types, input_interface/4).
:- dom_op(oo_types, input_user_interface/5).
:- dom_op(oo_types, asub_to_native/5).
:- dom_op(oo_types, unknown_call/4).
:- dom_op(oo_types, unknown_entry/3).
:- dom_op(oo_types, empty_entry/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(java_cha)).
:- dom_def(java_cha).
:- dom_op(java_cha, call_to_entry/9).
:- dom_op(java_cha, exit_to_prime/7).
:- dom_op(java_cha, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(java_cha, compute_lub/2).
:- dom_op(java_cha, abs_sort/2).
:- dom_op(java_cha, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(java_cha, less_or_equal/2).
:- dom_op(java_cha, glb/3).
:- dom_op(java_cha, call_to_success_fact/9).
:- dom_op(java_cha, special_builtin/5).
:- dom_op(java_cha, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(java_cha, input_interface/4).
:- dom_op(java_cha, input_user_interface/5).
:- dom_op(java_cha, asub_to_native/5).
:- dom_op(java_cha, unknown_call/4).
:- dom_op(java_cha, unknown_entry/3).
:- endif.
% ===========================================================================
:- doc(section, "Computation domains").
% ---------------------------------------------------------------------------
% nonfailure
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(nfplai)).
:- dom_def(nf).
:- dom_op(nf, init_abstract_domain/1).
:- dom_op(nf, call_to_entry/9).
:- dom_op(nf, exit_to_prime/7).
:- dom_op(nf, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(nf, widencall/3).
:- dom_op(nf, widen/3).
:- dom_op(nf, compute_lub/2). 
:- dom_op(nf, compute_clauses_lub(Proj,ASub,Lub), compute_clauses_lub(ASub,Proj,Lub)).
:- dom_op(nf, identical_abstract/2).
:- dom_op(nf, fixpoint_covered/2).
:- dom_op(nf, abs_sort/2).
:- dom_op(nf, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(nf, less_or_equal/2).
:- dom_op(nf, glb/3).
:- dom_op(nf, eliminate_equivalent/2).
:- dom_op(nf, call_to_success_fact/9).
:- dom_op(nf, special_builtin/5).
:- dom_op(nf, combined_special_builtin0/2).
:- dom_op(nf, split_combined_domain/3).
:- dom_op(nf, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(nf, input_interface/4).
:- dom_op(nf, input_user_interface/5).
:- dom_op(nf, asub_to_native/5).
:- dom_op(nf, unknown_call/4).
:- dom_op(nf, unknown_entry/3).
:- dom_op(nf, empty_entry/3).
:- dom_op(nf, dom_statistics/1).
:- endif.
% ---------------------------------------------------------------------------
% determinism
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(detplai)).
:- dom_def(det).
:- dom_op(det, init_abstract_domain/1).
:- dom_op(det, call_to_entry/9).
:- dom_op(det, exit_to_prime/7).
:- dom_op(det, project(_Sg,Vars,_HvFv,ASub,Proj), project(ASub,Vars,Proj)).
:- dom_op(det, widencall/3).
:- dom_op(det, widen/3).
:- dom_op(det, compute_lub/2).
:- dom_op(det, compute_clauses_lub(Proj,ASub,Lub), compute_clauses_lub(ASub,Proj,Lub)).
:- dom_op(det, identical_abstract/2).
:- dom_op(det, fixpoint_covered/2).
:- dom_op(det, abs_sort/2).
:- dom_op(det, extend(_Sg,Prime,Sv,Call,Succ), extend(Prime,Sv,Call,Succ)).
:- dom_op(det, less_or_equal/2).
:- dom_op(det, glb/3).
:- dom_op(det, eliminate_equivalent/2).
:- dom_op(det, call_to_success_fact/9).
:- dom_op(det, special_builtin/5).
:- dom_op(det, combined_special_builtin0/2).
:- dom_op(det, split_combined_domain/3).
:- dom_op(det, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(det, obtain_info/4).
:- dom_op(det, input_interface/4).
:- dom_op(det, input_user_interface/5).
:- dom_op(det, asub_to_native/5).
:- dom_op(det, unknown_call/4).
:- dom_op(det, unknown_entry/3).
:- dom_op(det, empty_entry/3).
:- dom_op(det, dom_statistics/1).
:- endif.
% ===========================================================================
:- doc(section, "Resources domains").
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/res_plai)).
:- dom_def(res_plai).
:- dom_op(res_plai, init_abstract_domain/1).
:- dom_op(res_plai, call_to_entry/9).
:- dom_op(res_plai, exit_to_prime/7).
:- dom_op(res_plai, project(Sg,Vars,_HvFv,ASub,Proj), project(ASub,Sg,Vars,Proj)).
% :- dom_op(res_plai, widencall/3).
:- dom_op(res_plai, widen/3).
:- dom_op(res_plai, compute_lub/2).
:- dom_op(res_plai, compute_clauses_lub(Proj,ASub,Lub), compute_clauses_lub(ASub,Proj,Lub)).
% :- dom_op(res_plai, compute_clauses_glb(Proj,ASub,Lub), compute_clauses_lub(ASub,Proj,Lub)).
:- dom_op(res_plai, identical_abstract/2).
:- dom_op(res_plai, abs_sort/2).
:- dom_op(res_plai, extend/5).
:- dom_op(res_plai, less_or_equal/2).
:- dom_op(res_plai, glb/3).
:- dom_op(res_plai, eliminate_equivalent/2).
:- dom_op(res_plai, call_to_success_fact/9).
:- dom_op(res_plai, special_builtin/5).
:- dom_op(res_plai, combined_special_builtin0/2).
:- dom_op(res_plai, split_combined_domain/3).
% :- dom_op(res_plai, success_builtin(Type,Sv_uns,Condvars,_HvFv_u,Call,Succ), success_builtin(Type,Sv_uns,Condvars,Call,Succ)).
:- dom_op(res_plai, call_to_success_builtin/6).
:- dom_op(res_plai, obtain_info/4).
:- dom_op(res_plai, input_interface/4).
:- dom_op(res_plai, input_user_interface/5).
:- dom_op(res_plai, asub_to_native/5).
:- dom_op(res_plai, unknown_call/4).
:- dom_op(res_plai, unknown_entry/3).
:- dom_op(res_plai, empty_entry/3).
:- dom_op(res_plai, collect_abstypes_abs/3).
:- dom_op(res_plai, rename_abstypes_abs/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/res_plai_stprf)).
:- dom_def(res_plai_stprf).
:- dom_op(res_plai_stprf, init_abstract_domain/1).
:- dom_op(res_plai_stprf, call_to_entry/9).
:- dom_op(res_plai_stprf, exit_to_prime/7).
:- dom_op(res_plai_stprf, project(Sg,Vars,_HvFv,ASub,Proj), project(ASub,Sg,Vars,Proj)).
:- dom_op(res_plai_stprf, widen/3).
:- dom_op(res_plai_stprf, compute_lub/2).
:- dom_op(res_plai_stprf, compute_clauses_lub(Proj,ASub,Lub), compute_clauses_lub(ASub,Proj,Lub)).
:- dom_op(res_plai_stprf, identical_abstract/2).
:- dom_op(res_plai_stprf, abs_sort/2).
:- dom_op(res_plai_stprf, extend/5).
:- dom_op(res_plai_stprf, less_or_equal/2).
:- dom_op(res_plai_stprf, glb/3).
:- dom_op(res_plai_stprf, eliminate_equivalent/2).
:- dom_op(res_plai_stprf, call_to_success_fact/9).
:- dom_op(res_plai_stprf, special_builtin/5).
:- dom_op(res_plai_stprf, combined_special_builtin0/2).
:- dom_op(res_plai_stprf, split_combined_domain/3).
:- dom_op(res_plai_stprf, call_to_success_builtin/6).
:- dom_op(res_plai_stprf, obtain_info/4).
:- dom_op(res_plai_stprf, input_interface/4).
:- dom_op(res_plai_stprf, input_user_interface/5).
:- dom_op(res_plai_stprf, asub_to_native/5).
:- dom_op(res_plai_stprf, unknown_call/4).
:- dom_op(res_plai_stprf, unknown_entry/3).
:- dom_op(res_plai_stprf, empty_entry/3).
:- dom_op(res_plai_stprf, collect_abstypes_abs/3).
:- dom_op(res_plai_stprf, rename_abstypes_abs/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/sized_types)).
:- dom_def(sized_types).
:- dom_op(sized_types, init_abstract_domain/1).
:- dom_op(sized_types, call_to_entry/9).
:- dom_op(sized_types, exit_to_prime/7).
:- dom_op(sized_types, project(Sg,Vars,_HvFv,ASub,Proj), project(ASub,Sg,Vars,Proj)).
:- dom_op(sized_types, widen/3).
:- dom_op(sized_types, compute_lub/2).
:- dom_op(sized_types, compute_clauses_lub(Proj,ASub,Lub), compute_clauses_lub(ASub,Proj,Lub)).
:- dom_op(sized_types, identical_abstract/2).
:- dom_op(sized_types, abs_sort/2).
:- dom_op(sized_types, extend/5).
:- dom_op(sized_types, less_or_equal/2).
:- dom_op(sized_types, glb/3).
:- dom_op(sized_types, eliminate_equivalent/2).
:- dom_op(sized_types, call_to_success_fact/9).
:- dom_op(sized_types, special_builtin/5).
:- dom_op(sized_types, combined_special_builtin0/2).
:- dom_op(sized_types, split_combined_domain/3).
:- dom_op(sized_types, call_to_success_builtin/6).
:- dom_op(sized_types, obtain_info/4).
:- dom_op(sized_types, input_interface/4).
:- dom_op(sized_types, input_user_interface/5).
:- dom_op(sized_types, asub_to_native/5).
:- dom_op(sized_types, unknown_call/4).
:- dom_op(sized_types, unknown_entry/3).
:- dom_op(sized_types, empty_entry/3).
:- dom_op(sized_types, collect_abstypes_abs/3).
:- dom_op(sized_types, rename_abstypes_abs/3).
:- endif.
% ===========================================================================

% ---------------------------------------------------------------------------
% (common)

:- use_module(library(lists), [member/2]).

:- export(absub_eliminate_equivalent/3).
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

absub_fixpoint_covered(AbsInt,Prime0,Prime1) :-
	( current_pp_flag(multi_call,on) ->
	    identical_abstract(AbsInt,Prime0,Prime1)
	; current_pp_flag(multi_call,off) ->
	    less_or_equal(AbsInt,Prime0,Prime1)
	; fail % TODO: anything else?
	).

:- export(body_builtin/9).
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
%augment_asub(_AbsInt,_ASub,_Vars,_ASub0) :- throw(not_implemented(augment_asub)).
%augment_two_asub(_AbsInt,_ASub0,_ASub1,_ASub) :- throw(not_implemented(augment_two_asub)).
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


