% ===========================================================================
% Hooks for domain implementations

:- use_package(aidomain).

% TODO: See analysis.lpdoc for documentation

:- dom_op(init_abstract_domain/1).
:- dom_op(amgu/4).
:- dom_op(augment_asub/3).
:- dom_op(augment_two_asub/3).
:- dom_op(call_to_entry/9).
:- dom_op(exit_to_prime/7).
:- dom_op(project/5).
:- dom_op(widencall/3).
:- dom_op(widen/3).
:- dom_op(compute_lub/2).
:- dom_op(compute_clauses_lub/3).
:- dom_op(compute_clauses_glb/3).
:- dom_op(fixpoint_covered/2).
:- dom_op(fixpoint_covered_gfp/2).
:- dom_op(identical_abstract/2).
:- dom_op(abs_sort/2).
:- dom_op(extend/5).
:- dom_op(less_or_equal/2).
:- dom_op(glb/3).
:- dom_op(eliminate_equivalent/2).
:- dom_op(abs_subset/2).
:- dom_op(call_to_success_fact/9).
:- dom_op(special_builtin/5).
:- dom_op(combined_special_builtin0/2).
:- dom_op(body_succ_builtin/8).
:- dom_op(split_combined_domain/3).
:- dom_op(success_builtin/6).
:- dom_op(call_to_success_builtin/6).
:- dom_op(obtain_info/4).
:- dom_op(input_interface/4).
:- dom_op(input_user_interface/5).
:- dom_op(asub_to_native/5).
:- dom_op(concrete/3).
:- dom_op(unknown_call/4).
:- dom_op(unknown_entry/3).
:- dom_op(empty_entry/3).
%
% :- dom_op(propagate_downwards_closed/3).
% :- dom_op(del_real_conjoin/3).
% :- dom_op(del_hash/3).
% :- dom_op(more_instantiate/2).
% :- dom_op(convex_hull/3).
% :- dom_op(compute_lub_el/3).
% :- dom_op(extend_free/3).
% :- dom_op(del_check_cond/5).
% :- dom_op(del_impose_cond/4).
%
:- dom_op(part_conc/4).
:- dom_op(multi_part_conc/3).
:- dom_op(collect_abstypes_abs/3).
:- dom_op(rename_abstypes_abs/3).
:- dom_op(dom_statistics/1).
:- dom_op(contains_parameters/1). % can succeed only for deftypes

:- use_module(library(sets), [ord_subset/2]).
:- use_module(library(sort), [sort/2]).
:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_base(init_abstract_domain/1).
% NOTE: This must be the last part of this file
basedom_init_abstract_domain(_AbsInt,[variants]) :-
        % TODO: [IG] for all domains variants=off??
        push_pp_flag(variants,off).

%:- dom_base(amgu/4).
%basedom_amgu(_AbsInt,_T0,_T1,_ASub,_NewASub):- throw(not_implemented(amgu)).

%:- dom_base(augment_asub/3).
%basedom_augment_asub(_AbsInt,_ASub,_Vars,_ASub0) :- throw(not_implemented(augment_asub)).

%:- dom_base(augment_two_asub/3).
%basedom_augment_two_asub(_AbsInt,_ASub0,_ASub1,_ASub) :- throw(not_implemented(augment_two_asub)).

%:- dom_base(widencall/3).
% basedom_widencall(AbsInt,Prime0,Prime1,NewPrime) :- % TODO: [IG] why is this commented?
% 	compute_lub(AbsInt,[Prime0,Prime1],NewPrime).

:- dom_base(widen/3).
basedom_widen(AbsInt,Prime0,Prime1,NewPrime) :- % TODO: [IG] define in domain?
	compute_lub(AbsInt,[Prime0,Prime1],NewPrime).

:- dom_base(compute_clauses_lub/3).
basedom_compute_clauses_lub(_AbsInt,Lub,_Proj,Lub).

:- dom_base(compute_clauses_glb/3).
basedom_compute_clauses_glb(_AbsInt,Lub,_Proj,Lub).

:- dom_base(identical_abstract/2).
basedom_identical_abstract(_AbsInt,ASub1,ASub2) :- ASub1==ASub2.

:- dom_base(fixpoint_covered/2).
basedom_fixpoint_covered(AbsInt,Prime0,Prime1) :-
	absub_fixpoint_covered(AbsInt,Prime0,Prime1).

:- dom_base(fixpoint_covered_gfp/2).
basedom_fixpoint_covered_gfp(AbsInt,Prime0,Prime1) :-
	absub_fixpoint_covered(AbsInt,Prime0,Prime1).

:- dom_base(eliminate_equivalent/2).
basedom_eliminate_equivalent(_AbsInt,TmpLSucc,LSucc) :- sort(TmpLSucc,LSucc). % TODO: valid if ASub1==ASub2 means equivalent

:- dom_base(abs_subset/2).
basedom_abs_subset(_AbsInt,LASub1,LASub2) :-
	ord_subset(LASub1,LASub2).

:- dom_base(body_succ_builtin/8).
basedom_body_succ_builtin(AbsInt,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :-
	body_builtin(AbsInt,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

:- dom_base(call_to_success_builtin/6).
basedom_call_to_success_builtin(AbsInt,SgKey,_Sg,_Sv,_Call,_Proj,'$bottom') :-
	undef_call_to_success_builtin(AbsInt,SgKey).

:- dom_base(part_conc/4).
basedom_part_conc(_AbsInt,Sg,Subs,Sg,Subs).

:- dom_base(multi_part_conc/3).
basedom_multi_part_conc(_AbsInt,Sg,Subs,[(Sg,Subs)]).

:- dom_base(rename_abstypes_abs/3).
basedom_rename_abstypes_abs(_AbsInt,ASub,_Rens,ASub).

:- dom_base(dom_statistics/1).
basedom_dom_statistics(_AbsInt, []).

%:- dom_base(contains_parameters/1).
% basedom_contains_parameters(_AbsInt,_) :- fail.

% ===========================================================================
:- doc(section, "Reachability domains"). % TODO: for partial evaluation
% ---------------------------------------------------------------------------
% PD domain
:- use_module(domain(pd)).
:- dom_def(pd).
:- dom_impl(pd, call_to_entry/9).
:- dom_impl(pd, exit_to_prime/7).
:- dom_impl(pd, project/5).
:- dom_impl(pd, compute_lub/2).
:- dom_impl(pd, abs_sort/2).
:- dom_impl(pd, extend/5).
:- dom_impl(pd, less_or_equal/2).
:- dom_impl(pd, glb/3).
:- dom_impl(pd, call_to_success_fact/9).
:- dom_impl(pd, special_builtin/5).
:- dom_impl(pd, success_builtin/6).
:- dom_impl(pd, call_to_success_builtin/6).
:- dom_impl(pd, input_user_interface/5).
:- dom_impl(pd, asub_to_native/5).
:- dom_impl(pd, unknown_call/4).
:- dom_impl(pd, unknown_entry/3).
:- dom_impl(pd, empty_entry/3).
% ---------------------------------------------------------------------------
% PD domain with bottom
:- use_module(domain(pdb)).
:- dom_def(pdb).
:- dom_impl(pdb, call_to_entry/9).
:- dom_impl(pdb, exit_to_prime/7).
:- dom_impl(pdb, project/5).
:- dom_impl(pdb, compute_lub/2).
:- dom_impl(pdb, abs_sort/2).
:- dom_impl(pdb, extend/5).
:- dom_impl(pdb, less_or_equal/2).
:- dom_impl(pdb, glb/3).
:- dom_impl(pdb, call_to_success_fact/9).
:- dom_impl(pdb, special_builtin/5).
:- dom_impl(pdb, success_builtin/6).
:- dom_impl(pdb, call_to_success_builtin/6).
:- dom_impl(pdb, input_user_interface/5).
:- dom_impl(pdb, asub_to_native/5).
:- dom_impl(pdb, unknown_call/4).
:- dom_impl(pdb, unknown_entry/3).
:- dom_impl(pdb, empty_entry/3).
% ===========================================================================
:- doc(section, "Constraint domains").
% ---------------------------------------------------------------------------
:- use_module(domain(fr_top)).
:- dom_def(fr).
:- dom_impl(fr, call_to_entry/9).
:- dom_impl(fr, exit_to_prime/7).
:- dom_impl(fr, project/5).
:- dom_impl(fr, compute_lub/2).
:- dom_impl(fr, identical_abstract/2).
:- dom_impl(fr, abs_sort/2).
:- dom_impl(fr, extend/5).
:- dom_impl(fr, less_or_equal/2).
:- dom_impl(fr, glb/3).
:- dom_impl(fr, call_to_success_fact/9).
:- dom_impl(fr, special_builtin/5).
:- dom_impl(fr, success_builtin/6).
:- dom_impl(fr, input_interface/4).
:- dom_impl(fr, input_user_interface/5).
:- dom_impl(fr, asub_to_native/5).
:- dom_impl(fr, unknown_call/4).
:- dom_impl(fr, unknown_entry/3).
:- dom_impl(fr, empty_entry/3).
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef
% ---------------------------------------------------------------------------
:- use_module(domain(fd)).
:- dom_def(frdef).
:- dom_impl(frdef, call_to_entry/9).
:- dom_impl(frdef, exit_to_prime/7).
:- dom_impl(frdef, project/5).
:- dom_impl(frdef, compute_lub/2).
:- dom_impl(frdef, identical_abstract/2).
:- dom_impl(frdef, abs_sort/2).
:- dom_impl(frdef, extend/5).
:- dom_impl(frdef, less_or_equal/2).
:- dom_impl(frdef, glb/3).
:- dom_impl(frdef, call_to_success_fact/9).
:- dom_impl(frdef, special_builtin/5).
:- dom_impl(frdef, success_builtin/6).
:- dom_impl(frdef, input_interface/4).
:- dom_impl(frdef, input_user_interface/5).
:- dom_impl(frdef, asub_to_native/5).
:- dom_impl(frdef, unknown_call/4).
:- dom_impl(frdef, unknown_entry/3).
:- dom_impl(frdef, empty_entry/3).
% ---------------------------------------------------------------------------
% lsign
:- use_module(domain(lsign)).
:- dom_def(lsign).
:- dom_impl(lsign, init_abstract_domain/1).
:- dom_impl(lsign, call_to_entry/9).
:- dom_impl(lsign, exit_to_prime/7).
:- dom_impl(lsign, project/5).
:- dom_impl(lsign, compute_lub/2).
:- dom_impl(lsign, abs_sort/2).
:- dom_impl(lsign, extend/5).
:- dom_impl(lsign, less_or_equal/2).
:- dom_impl(lsign, glb/3).
:- dom_impl(lsign, eliminate_equivalent/2).
:- dom_impl(lsign, abs_subset/2).
:- dom_impl(lsign, call_to_success_fact/9).
:- dom_impl(lsign, special_builtin/5).
:- dom_impl(lsign, success_builtin/6).
:- dom_impl(lsign, input_interface/4).
:- dom_impl(lsign, input_user_interface/5).
:- dom_impl(lsign, asub_to_native/5).
:- dom_impl(lsign, unknown_call/4).
:- dom_impl(lsign, unknown_entry/3).
:- dom_impl(lsign, empty_entry/3).
% ---------------------------------------------------------------------------
% lsigndiff
:- use_module(domain(lsigndiff)).
:- dom_def(difflsign).
:- dom_impl(difflsign, call_to_entry/9).
:- dom_impl(difflsign, exit_to_prime/7).
:- dom_impl(difflsign, project/5).
:- dom_impl(difflsign, compute_lub/2).
:- dom_impl(difflsign, abs_sort/2).
:- dom_impl(difflsign, extend/5).
:- dom_impl(difflsign, less_or_equal/2).
:- dom_impl(difflsign, glb/3).
:- dom_impl(difflsign, call_to_success_fact/9).
:- dom_impl(difflsign, special_builtin/5).
:- dom_impl(difflsign, success_builtin/6).
:- dom_impl(difflsign, input_interface/4).
:- dom_impl(difflsign, input_user_interface/5).
:- dom_impl(difflsign, asub_to_native/5).
:- dom_impl(difflsign, unknown_call/4).
:- dom_impl(difflsign, unknown_entry/3).
:- dom_impl(difflsign, empty_entry/3).
% ===========================================================================
:- doc(section, "Groundness and sharing").
% ---------------------------------------------------------------------------
% Example groundness domain
:- use_module(domain(gr)).
:- dom_def(gr).
:- dom_impl(gr, call_to_entry/9).
:- dom_impl(gr, exit_to_prime/7).
:- dom_impl(gr, project/5).
:- dom_impl(gr, compute_lub/2).
:- dom_impl(gr, abs_sort/2).
:- dom_impl(gr, extend/5).
:- dom_impl(gr, less_or_equal/2).
:- dom_impl(gr, glb/3).
:- dom_impl(gr, call_to_success_fact/9).
:- dom_impl(gr, special_builtin/5).
:- dom_impl(gr, success_builtin/6).
:- dom_impl(gr, call_to_success_builtin/6).
:- dom_impl(gr, input_interface/4).
:- dom_impl(gr, input_user_interface/5).
:- dom_impl(gr, asub_to_native/5).
:- dom_impl(gr, unknown_call/4).
:- dom_impl(gr, unknown_entry/3).
:- dom_impl(gr, empty_entry/3).
% :- dom_impl(gr, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_impl(gr, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% ---------------------------------------------------------------------------
:- use_module(domain(def)).
:- dom_def(def).
:- dom_impl(def, call_to_entry/9).
:- dom_impl(def, exit_to_prime/7).
:- dom_impl(def, project/5).
:- dom_impl(def, compute_lub/2).
:- dom_impl(def, abs_sort/2).
:- dom_impl(def, extend/5).
:- dom_impl(def, less_or_equal/2).
:- dom_impl(def, glb/3).
:- dom_impl(def, call_to_success_fact/9).
:- dom_impl(def, special_builtin/5).
:- dom_impl(def, success_builtin/6).
:- dom_impl(def, input_interface/4).
:- dom_impl(def, input_user_interface/5).
:- dom_impl(def, asub_to_native/5).
:- dom_impl(def, unknown_call/4).
:- dom_impl(def, unknown_entry/3).
:- dom_impl(def, empty_entry/3).
% :- dom_impl(def, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(def, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(def, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(def, more_instantiate(ASub1,ASub2), less_or_equal(ASub2,ASub1)).
% :- dom_impl(def, convex_hull(Old,_,Old)).
% :- dom_impl(def, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_impl(def, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(def, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
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
:- dom_impl(share, amgu/4, from(share_amgu)).
:- dom_impl(share, augment_asub/3, from(share_amgu)).
:- dom_impl(share, augment_two_asub/3, from(share_amgu)).
:- dom_impl(share, call_to_entry/9).
:- dom_impl(share, exit_to_prime/7).
:- dom_impl(share, project/5).
:- dom_impl(share, compute_lub/2).
:- dom_impl(share, abs_sort/2).
:- dom_impl(share, extend/5).
:- dom_impl(share, less_or_equal/2).
:- dom_impl(share, glb/3).
:- dom_impl(share, call_to_success_fact/9).
:- dom_impl(share, special_builtin/5).
:- dom_impl(share, success_builtin/6).
:- dom_impl(share, call_to_success_builtin/6).
:- dom_impl(share, input_interface/4).
:- dom_impl(share, input_user_interface/5).
:- dom_impl(share, asub_to_native/5).
:- dom_impl(share, unknown_call/4).
:- dom_impl(share, unknown_entry/3).
:- dom_impl(share, empty_entry/3).
% :- dom_impl(share, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharefree)).
:- dom_def(shfr).
:- dom_impl(shfr, amgu/4, from(sharefree_amgu)).
:- dom_impl(shfr, augment_asub/3, from(sharefree_amgu)).
:- dom_impl(shfr, call_to_entry/9).
:- dom_impl(shfr, exit_to_prime/7).
:- dom_impl(shfr, project/5).
:- dom_impl(shfr, compute_lub/2).
:- dom_impl(shfr, abs_sort/2).
:- dom_impl(shfr, extend/5).
:- dom_impl(shfr, less_or_equal/2).
:- dom_impl(shfr, glb/3).
:- dom_impl(shfr, call_to_success_fact/9).
:- dom_impl(shfr, special_builtin/5).
:- dom_impl(shfr, success_builtin/6).
:- dom_impl(shfr, call_to_success_builtin/6).
:- dom_impl(shfr, obtain_info/4).
:- dom_impl(shfr, input_interface/4).
:- dom_impl(shfr, input_user_interface/5).
:- dom_impl(shfr, asub_to_native/5).
:- dom_impl(shfr, unknown_call/4).
:- dom_impl(shfr, unknown_entry/3).
:- dom_impl(shfr, empty_entry/3).
% :- dom_impl(shfr, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(shfr, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(shfr, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(shfr, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_impl(shfr, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_impl(shfr, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_impl(shfr, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% :- dom_impl(shfr, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(shfr, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
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
:- dom_impl(shfrnv, call_to_entry/9).
:- dom_impl(shfrnv, exit_to_prime/7).
:- dom_impl(shfrnv, project/5, from(shfr)).
:- dom_impl(shfrnv, compute_lub/2).
:- dom_impl(shfrnv, abs_sort/2, from(shfr)).
:- dom_impl(shfrnv, extend/5).
:- dom_impl(shfrnv, less_or_equal/2).
:- dom_impl(shfrnv, glb/3).
:- dom_impl(shfrnv, call_to_success_fact/9).
:- dom_impl(shfrnv, special_builtin/5, from(shfr)).
:- dom_impl(shfrnv, success_builtin/6).
:- dom_impl(shfrnv, call_to_success_builtin/6).
:- dom_impl(shfrnv, input_interface/4).
:- dom_impl(shfrnv, input_user_interface/5).
:- dom_impl(shfrnv, asub_to_native/5).
:- dom_impl(shfrnv, unknown_call/4, from(shfr)).
:- dom_impl(shfrnv, unknown_entry/3, from(shfr)).
:- dom_impl(shfrnv, empty_entry/3, from(shfr)).
%
% :- dom_impl(shfrnv, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(shfrnv, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(shfrnv, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(shfrnv, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_impl(shfrnv, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_impl(shfrnv, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_impl(shfrnv, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub), from(shfr)).
% :- dom_impl(shfrnv, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(shfrnv, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
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
:- dom_impl(shfret, init_abstract_domain/1).
:- dom_impl(shfret, call_to_entry/9).
:- dom_impl(shfret, exit_to_prime/7).
:- dom_impl(shfret, project/5).
:- dom_impl(shfret, widencall/3).
:- dom_impl(shfret, widen/3).
:- dom_impl(shfret, compute_lub/2).
:- dom_impl(shfret, identical_abstract/2).
:- dom_impl(shfret, abs_sort/2).
:- dom_impl(shfret, extend/5).
:- dom_impl(shfret, less_or_equal/2).
:- dom_impl(shfret, glb/3).
:- dom_impl(shfret, eliminate_equivalent/2).
:- dom_impl(shfret, call_to_success_fact/9).
:- dom_impl(shfret, combined_special_builtin0/2).
:- dom_impl(shfret, split_combined_domain/3).
:- dom_impl(shfret, input_interface/4).
:- dom_impl(shfret, input_user_interface/5).
:- dom_impl(shfret, asub_to_native/5).
:- dom_impl(shfret, unknown_call/4).
:- dom_impl(shfret, unknown_entry/3).
:- dom_impl(shfret, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(shareson)).
:- dom_def(shareson).
:- dom_impl(shareson, call_to_entry/9).
:- dom_impl(shareson, exit_to_prime/7).
:- dom_impl(shareson, project/5).
:- dom_impl(shareson, compute_lub/2).
:- dom_impl(shareson, abs_sort/2).
:- dom_impl(shareson, extend/5).
:- dom_impl(shareson, less_or_equal/2).
:- dom_impl(shareson, glb/3).
:- dom_impl(shareson, call_to_success_fact/9).
:- dom_impl(shareson, special_builtin/5).
:- dom_impl(shareson, body_succ_builtin/8).
:- dom_impl(shareson, input_interface/4).
:- dom_impl(shareson, input_user_interface/5).
:- dom_impl(shareson, asub_to_native/5).
:- dom_impl(shareson, unknown_call/4).
:- dom_impl(shareson, unknown_entry/3).
:- dom_impl(shareson, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(shfrson)).
:- dom_def(shfrson).
:- dom_impl(shfrson, call_to_entry/9).
:- dom_impl(shfrson, exit_to_prime/7).
:- dom_impl(shfrson, project/5).
:- dom_impl(shfrson, compute_lub/2).
:- dom_impl(shfrson, abs_sort/2).
:- dom_impl(shfrson, extend/5).
:- dom_impl(shfrson, less_or_equal/2).
:- dom_impl(shfrson, glb/3).
:- dom_impl(shfrson, call_to_success_fact/9).
:- dom_impl(shfrson, special_builtin/5).
:- dom_impl(shfrson, body_succ_builtin/8).
:- dom_impl(shfrson, input_interface/4).
:- dom_impl(shfrson, input_user_interface/5).
:- dom_impl(shfrson, asub_to_native/5).
:- dom_impl(shfrson, unknown_call/4).
:- dom_impl(shfrson, unknown_entry/3).
:- dom_impl(shfrson, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(sondergaard)).
:- dom_def(son).
:- dom_impl(son, call_to_entry/9).
:- dom_impl(son, exit_to_prime/7).
:- dom_impl(son, project/5).
:- dom_impl(son, compute_lub/2).
:- dom_impl(son, abs_sort/2).
:- dom_impl(son, extend/5).
:- dom_impl(son, less_or_equal/2).
:- dom_impl(son, glb/3).
:- dom_impl(son, call_to_success_fact/9).
:- dom_impl(son, special_builtin/5).
:- dom_impl(son, success_builtin/6).
:- dom_impl(son, call_to_success_builtin/6).
:- dom_impl(son, input_interface/4).
:- dom_impl(son, input_user_interface/5).
:- dom_impl(son, asub_to_native/5).
:- dom_impl(son, unknown_call/4).
:- dom_impl(son, unknown_entry/3).
:- dom_impl(son, empty_entry/3).
% :- dom_impl(son, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% ---------------------------------------------------------------------------
:- use_module(domain(sharing_amgu)).
:- dom_def(share_amgu).
:- dom_impl(share_amgu, amgu/4).
:- dom_impl(share_amgu, augment_asub/3).
:- dom_impl(share_amgu, augment_two_asub/3).
:- dom_impl(share_amgu, call_to_entry/9).
:- dom_impl(share_amgu, exit_to_prime/7).
:- dom_impl(share_amgu, project/5, from(share)).
:- dom_impl(share_amgu, compute_lub/2, from(share)).
:- dom_impl(share_amgu, abs_sort/2, from(share)).
:- dom_impl(share_amgu, extend/5, from(share)).
:- dom_impl(share_amgu, less_or_equal/2, from(share)).
:- dom_impl(share_amgu, glb/3, from(share)).
:- dom_impl(share_amgu, call_to_success_fact/9).
:- dom_impl(share_amgu, special_builtin/5).
:- dom_impl(share_amgu, success_builtin/6).
:- dom_impl(share_amgu, call_to_success_builtin/6).
:- dom_impl(share_amgu, input_interface/4, from(share)).
:- dom_impl(share_amgu, input_user_interface/5, from(share)).
:- dom_impl(share_amgu, asub_to_native/5, from(share)).
:- dom_impl(share_amgu, unknown_call/4, from(share)).
:- dom_impl(share_amgu, unknown_entry/3, from(share)).
:- dom_impl(share_amgu, empty_entry/3, from(share)).
% :- dom_impl(share_amgu, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub), from(share)).
% ----------
:- use_module(domain(sharefree_amgu)).
:- dom_def(sharefree_amgu).
:- dom_impl(sharefree_amgu, amgu/4).
:- dom_impl(sharefree_amgu, augment_asub/3).
:- dom_impl(sharefree_amgu, call_to_entry/9).
:- dom_impl(sharefree_amgu, exit_to_prime/7).
:- dom_impl(sharefree_amgu, project/5, from(shfr)).
:- dom_impl(sharefree_amgu, compute_lub/2, from(shfr)).
:- dom_impl(sharefree_amgu, abs_sort/2, from(shfr)).
:- dom_impl(sharefree_amgu, extend/5, from(shfr)).
:- dom_impl(sharefree_amgu, less_or_equal/2, from(shfr)).
:- dom_impl(sharefree_amgu, glb/3, from(shfr)).
:- dom_impl(sharefree_amgu, call_to_success_fact/9).
:- dom_impl(sharefree_amgu, special_builtin/5).
:- dom_impl(sharefree_amgu, success_builtin/6).
:- dom_impl(sharefree_amgu, call_to_success_builtin/6).
:- dom_impl(sharefree_amgu, obtain_info/4, from(shfr)).
:- dom_impl(sharefree_amgu, input_interface/4, from(shfr)).
:- dom_impl(sharefree_amgu, input_user_interface/5, from(shfr)).
:- dom_impl(sharefree_amgu, asub_to_native/5, from(shfr)).
:- dom_impl(sharefree_amgu, unknown_call/4, from(shfr)).
:- dom_impl(sharefree_amgu, unknown_entry/3, from(shfr)).
:- dom_impl(sharefree_amgu, empty_entry/3, from(shfr)).
% ----------
:- use_module(domain(shfrlin_amgu)).
:- dom_def(shfrlin_amgu).
:- dom_impl(shfrlin_amgu, amgu/4).
:- dom_impl(shfrlin_amgu, augment_asub/3).
:- dom_impl(shfrlin_amgu, call_to_entry/9).
:- dom_impl(shfrlin_amgu, exit_to_prime/7).
:- dom_impl(shfrlin_amgu, project/5).
:- dom_impl(shfrlin_amgu, compute_lub/2).
:- dom_impl(shfrlin_amgu, abs_sort/2).
:- dom_impl(shfrlin_amgu, extend/5).
:- dom_impl(shfrlin_amgu, less_or_equal/2).
:- dom_impl(shfrlin_amgu, glb/3).
:- dom_impl(shfrlin_amgu, call_to_success_fact/9).
:- dom_impl(shfrlin_amgu, special_builtin/5).
:- dom_impl(shfrlin_amgu, success_builtin/6).
:- dom_impl(shfrlin_amgu, call_to_success_builtin/6).
:- dom_impl(shfrlin_amgu, obtain_info/4).
:- dom_impl(shfrlin_amgu, input_interface/4).
:- dom_impl(shfrlin_amgu, input_user_interface/5).
:- dom_impl(shfrlin_amgu, asub_to_native/5).
:- dom_impl(shfrlin_amgu, unknown_call/4).
:- dom_impl(shfrlin_amgu, unknown_entry/3).
:- dom_impl(shfrlin_amgu, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(sharing_clique)).
:- dom_def(share_clique).
:- dom_impl(share_clique, amgu/4).
:- dom_impl(share_clique, augment_asub/3).
:- dom_impl(share_clique, call_to_entry/9).
:- dom_impl(share_clique, exit_to_prime/7).
:- dom_impl(share_clique, project/5).
:- dom_impl(share_clique, compute_lub/2).
:- dom_impl(share_clique, identical_abstract/2).
:- dom_impl(share_clique, abs_sort/2).
:- dom_impl(share_clique, extend/5).
:- dom_impl(share_clique, less_or_equal/2).
:- dom_impl(share_clique, glb/3).
:- dom_impl(share_clique, eliminate_equivalent/2).
:- dom_impl(share_clique, call_to_success_fact/9).
:- dom_impl(share_clique, special_builtin/5).
:- dom_impl(share_clique, success_builtin/6).
:- dom_impl(share_clique, call_to_success_builtin/6).
:- dom_impl(share_clique, input_interface/4).
:- dom_impl(share_clique, input_user_interface/5).
:- dom_impl(share_clique, asub_to_native/5).
:- dom_impl(share_clique, unknown_call/4).
:- dom_impl(share_clique, unknown_entry/3).
:- dom_impl(share_clique, empty_entry/3).
% :- dom_impl(share_clique, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharing_clique_1)).
:- dom_def(share_clique_1).
:- dom_impl(share_clique_1, call_to_entry/9).
:- dom_impl(share_clique_1, exit_to_prime/7).
:- dom_impl(share_clique_1, project/5).
:- dom_impl(share_clique_1, compute_lub/2).
:- dom_impl(share_clique_1, identical_abstract/2).
:- dom_impl(share_clique_1, abs_sort/2, from(share_clique)).
:- dom_impl(share_clique_1, extend/5).
:- dom_impl(share_clique_1, less_or_equal/2).
:- dom_impl(share_clique_1, glb/3).
:- dom_impl(share_clique_1, eliminate_equivalent/2).
:- dom_impl(share_clique_1, call_to_success_fact/9).
:- dom_impl(share_clique_1, special_builtin/5, from(share_clique)).
:- dom_impl(share_clique_1, success_builtin/6).
:- dom_impl(share_clique_1, call_to_success_builtin/6).
:- dom_impl(share_clique_1, input_interface/4).
:- dom_impl(share_clique_1, input_user_interface/5, from(share_clique)).
:- dom_impl(share_clique_1, asub_to_native/5).
:- dom_impl(share_clique_1, unknown_call/4).
:- dom_impl(share_clique_1, unknown_entry/3).
:- dom_impl(share_clique_1, empty_entry/3, from(share_clique)).
% :- dom_impl(share_clique_1, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharefree_clique)).
:- dom_def(sharefree_clique).
:- dom_impl(sharefree_clique, amgu/4).
:- dom_impl(sharefree_clique, augment_asub/3).
:- dom_impl(sharefree_clique, call_to_entry/9).
:- dom_impl(sharefree_clique, exit_to_prime/7).
:- dom_impl(sharefree_clique, project/5).
:- dom_impl(sharefree_clique, compute_lub/2).
:- dom_impl(sharefree_clique, identical_abstract/2).
:- dom_impl(sharefree_clique, abs_sort/2).
:- dom_impl(sharefree_clique, extend/5).
:- dom_impl(sharefree_clique, less_or_equal/2).
:- dom_impl(sharefree_clique, glb/3).
:- dom_impl(sharefree_clique, eliminate_equivalent/2).
:- dom_impl(sharefree_clique, call_to_success_fact/9).
:- dom_impl(sharefree_clique, special_builtin/5).
:- dom_impl(sharefree_clique, success_builtin/6).
:- dom_impl(sharefree_clique, call_to_success_builtin/6).
:- dom_impl(sharefree_clique, obtain_info/4, from(shfr)).
:- dom_impl(sharefree_clique, input_interface/4).
:- dom_impl(sharefree_clique, input_user_interface/5).
:- dom_impl(sharefree_clique, asub_to_native/5).
:- dom_impl(sharefree_clique, unknown_call/4).
:- dom_impl(sharefree_clique, unknown_entry/3).
:- dom_impl(sharefree_clique, empty_entry/3).
% :- dom_impl(sharefree_clique, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% ----------
:- use_module(domain(sharing_clique_def)).
:- dom_def(share_clique_def).
:- dom_impl(share_clique_def, call_to_entry/9).
:- dom_impl(share_clique_def, exit_to_prime/7).
:- dom_impl(share_clique_def, project/5).
:- dom_impl(share_clique_def, compute_lub/2).
:- dom_impl(share_clique_def, identical_abstract/2).
:- dom_impl(share_clique_def, abs_sort/2).
:- dom_impl(share_clique_def, extend/5).
:- dom_impl(share_clique_def, less_or_equal/2).
:- dom_impl(share_clique_def, glb/3).
:- dom_impl(share_clique_def, eliminate_equivalent/2).
:- dom_impl(share_clique_def, call_to_success_fact/9).
:- dom_impl(share_clique_def, special_builtin/5).
:- dom_impl(share_clique_def, body_succ_builtin/8).
:- dom_impl(share_clique_def, input_interface/4, from(share_clique)).
:- dom_impl(share_clique_def, input_user_interface/5).
:- dom_impl(share_clique_def, asub_to_native/5).
:- dom_impl(share_clique_def, unknown_call/4).
:- dom_impl(share_clique_def, unknown_entry/3).
:- dom_impl(share_clique_def, empty_entry/3).
% :- dom_impl(share_clique_def, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
%
% ----------
:- use_module(domain(sharefree_clique_def)).
:- dom_def(sharefree_clique_def).
:- dom_impl(sharefree_clique_def, call_to_entry/9).
:- dom_impl(sharefree_clique_def, exit_to_prime/7).
:- dom_impl(sharefree_clique_def, project/5).
:- dom_impl(sharefree_clique_def, compute_lub/2).
:- dom_impl(sharefree_clique_def, identical_abstract/2).
:- dom_impl(sharefree_clique_def, abs_sort/2).
:- dom_impl(sharefree_clique_def, extend/5).
:- dom_impl(sharefree_clique_def, less_or_equal/2).
:- dom_impl(sharefree_clique_def, glb/3).
:- dom_impl(sharefree_clique_def, eliminate_equivalent/2).
:- dom_impl(sharefree_clique_def, call_to_success_fact/9).
:- dom_impl(sharefree_clique_def, special_builtin/5).
:- dom_impl(sharefree_clique_def, body_succ_builtin/8).
:- dom_impl(sharefree_clique_def, input_interface/4, from(sharefree_clique)).
:- dom_impl(sharefree_clique_def, input_user_interface/5).
:- dom_impl(sharefree_clique_def, asub_to_native/5).
:- dom_impl(sharefree_clique_def, unknown_call/4).
:- dom_impl(sharefree_clique_def, unknown_entry/3).
:- dom_impl(sharefree_clique_def, empty_entry/3).
% :- dom_impl(sharefree_clique_def, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(bshare/bshare)).
:- dom_def(bshare).
:- dom_impl(bshare, amgu/4).
:- dom_impl(bshare, augment_asub/3).
:- dom_impl(bshare, augment_two_asub/3).
:- dom_impl(bshare, call_to_entry/9).
:- dom_impl(bshare, project/5).
:- dom_impl(bshare, compute_lub/2).
:- dom_impl(bshare, identical_abstract/2).
:- dom_impl(bshare, abs_sort/2).
:- dom_impl(bshare, call_to_success_fact/9).
:- dom_impl(bshare, special_builtin/5).
:- dom_impl(bshare, success_builtin/6).
:- dom_impl(bshare, call_to_success_builtin/6).
:- dom_impl(bshare, asub_to_native/5).
:- dom_impl(bshare, unknown_entry/3).
:- dom_impl(bshare, empty_entry/3).
% :- dom_impl(bshare, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
:- endif.
% ===========================================================================
:- doc(section, "Structure domains"). % TODO: shape also?
% ---------------------------------------------------------------------------
:- use_module(domain(aeq_top)).
:- dom_def(aeq).
:- dom_impl(aeq, call_to_entry/9).
:- dom_impl(aeq, exit_to_prime/7).
:- dom_impl(aeq, project/5).
:- dom_impl(aeq, compute_lub/2).
:- dom_impl(aeq, identical_abstract/2).
:- dom_impl(aeq, abs_sort/2).
:- dom_impl(aeq, extend/5).
:- dom_impl(aeq, less_or_equal/2).
:- dom_impl(aeq, glb/3).
:- dom_impl(aeq, eliminate_equivalent/2).
:- dom_impl(aeq, call_to_success_fact/9).
:- dom_impl(aeq, special_builtin/5).
:- dom_impl(aeq, success_builtin/6).
:- dom_impl(aeq, input_interface/4).
:- dom_impl(aeq, input_user_interface/5).
:- dom_impl(aeq, asub_to_native/5).
:- dom_impl(aeq, unknown_call/4).
:- dom_impl(aeq, unknown_entry/3).
:- dom_impl(aeq, empty_entry/3).
%
% :- dom_impl(aeq, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(aeq, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(aeq, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(aeq, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_impl(aeq, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_impl(aeq, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% :- dom_impl(aeq, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% :- dom_impl(aeq, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(aeq, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
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
:- dom_impl(depthk, call_to_entry/9).
:- dom_impl(depthk, exit_to_prime/7).
:- dom_impl(depthk, project/5).
:- dom_impl(depthk, compute_lub/2).
:- dom_impl(depthk, identical_abstract/2).
:- dom_impl(depthk, abs_sort/2).
:- dom_impl(depthk, extend/5).
:- dom_impl(depthk, less_or_equal/2).
:- dom_impl(depthk, glb/3).
:- dom_impl(depthk, eliminate_equivalent/2).
:- dom_impl(depthk, abs_subset/2).
:- dom_impl(depthk, call_to_success_fact/9).
:- dom_impl(depthk, special_builtin/5).
:- dom_impl(depthk, success_builtin/6).
:- dom_impl(depthk, call_to_success_builtin/6).
:- dom_impl(depthk, input_interface/4).
:- dom_impl(depthk, input_user_interface/5).
:- dom_impl(depthk, asub_to_native/5).
:- dom_impl(depthk, unknown_call/4).
:- dom_impl(depthk, unknown_entry/3).
:- dom_impl(depthk, empty_entry/3).
% ---------------------------------------------------------------------------
:- use_module(domain(top_path_sharing)).
:- dom_def(path).
:- dom_impl(path, init_abstract_domain/1).
:- dom_impl(path, call_to_entry/9).
:- dom_impl(path, exit_to_prime/7).
:- dom_impl(path, project/5).
:- dom_impl(path, compute_lub/2).
:- dom_impl(path, abs_sort/2).
:- dom_impl(path, extend/5).
:- dom_impl(path, less_or_equal/2).
:- dom_impl(path, glb/3).
:- dom_impl(path, call_to_success_fact/9).
:- dom_impl(path, special_builtin/5).
:- dom_impl(path, success_builtin/6).
:- dom_impl(path, input_interface/4).
:- dom_impl(path, input_user_interface/5).
:- dom_impl(path, asub_to_native/5).
:- dom_impl(path, unknown_call/4).
:- dom_impl(path, unknown_entry/3).
:- dom_impl(path, empty_entry/3).
% ===========================================================================
:- doc(section, "Type domains"). % TODO: shape/structure?
% ---------------------------------------------------------------------------
:- use_module(domain(termsd)).
:- dom_def(terms).
:- dom_impl(terms, init_abstract_domain/1).
:- dom_impl(terms, call_to_entry/9).
:- dom_impl(terms, exit_to_prime/7).
:- dom_impl(terms, project/5).
:- dom_impl(terms, widencall/3).
:- dom_impl(terms, widen/3).
:- dom_impl(terms, compute_lub/2).
:- dom_impl(terms, identical_abstract/2).
:- dom_impl(terms, abs_sort/2).
:- dom_impl(terms, extend/5).
:- dom_impl(terms, less_or_equal/2).
:- dom_impl(terms, glb/3).
:- dom_impl(terms, call_to_success_fact/9).
:- dom_impl(terms, special_builtin/5).
:- dom_impl(terms, success_builtin/6).
:- dom_impl(terms, call_to_success_builtin/6).
:- dom_impl(terms, input_interface/4).
:- dom_impl(terms, input_user_interface/5).
:- dom_impl(terms, asub_to_native/5).
:- dom_impl(terms, concrete/3).
:- dom_impl(terms, unknown_call/4).
:- dom_impl(terms, unknown_entry/3).
:- dom_impl(terms, empty_entry/3).
:- dom_impl(terms, collect_abstypes_abs/3).
:- dom_impl(terms, rename_abstypes_abs/3).
% ---------------------------------------------------------------------------
:- use_module(domain(ptypes)).
:- dom_def(ptypes).
:- dom_impl(ptypes, init_abstract_domain/1).
:- dom_impl(ptypes, call_to_entry/9).
:- dom_impl(ptypes, exit_to_prime/7).
:- dom_impl(ptypes, widencall/3).
:- dom_impl(ptypes, widen/3).
:- dom_impl(ptypes, compute_lub/2).
:- dom_impl(ptypes, identical_abstract/2).
:- dom_impl(ptypes, abs_sort/2).
:- dom_impl(ptypes, extend/5).
:- dom_impl(ptypes, less_or_equal/2).
:- dom_impl(ptypes, glb/3).
:- dom_impl(ptypes, call_to_success_fact/9).
:- dom_impl(ptypes, special_builtin/5).
:- dom_impl(ptypes, success_builtin/6).
:- dom_impl(ptypes, call_to_success_builtin/6).
:- dom_impl(ptypes, input_interface/4).
:- dom_impl(ptypes, input_user_interface/5).
:- dom_impl(ptypes, asub_to_native/5).
:- dom_impl(ptypes, concrete/3).
:- dom_impl(ptypes, unknown_call/4).
:- dom_impl(ptypes, unknown_entry/3).
:- dom_impl(ptypes, empty_entry/3).
:- dom_impl(ptypes, collect_abstypes_abs/3).
% :- dom_impl(ptypes, rename_abstypes_abs/3). % TODO: missing, why?
%
% ---------------------------------------------------------------------------
:- use_module(domain(eterms)).
:- dom_def(eterms).
:- dom_impl(eterms, init_abstract_domain/1).
:- dom_impl(eterms, call_to_entry/9).
:- dom_impl(eterms, exit_to_prime/7).
:- dom_impl(eterms, project/5).
:- dom_impl(eterms, widencall/3).
:- dom_impl(eterms, widen/3).
:- dom_impl(eterms, compute_lub/2).
:- dom_impl(eterms, identical_abstract/2).
:- dom_impl(eterms, abs_sort/2).
:- dom_impl(eterms, extend/5).
:- dom_impl(eterms, less_or_equal/2).
:- dom_impl(eterms, glb/3).
:- dom_impl(eterms, call_to_success_fact/9).
:- dom_impl(eterms, special_builtin/5).
:- dom_impl(eterms, success_builtin/6).
:- dom_impl(eterms, call_to_success_builtin/6).
:- dom_impl(eterms, obtain_info/4).
:- dom_impl(eterms, input_interface/4).
:- dom_impl(eterms, input_user_interface/5).
:- dom_impl(eterms, asub_to_native/5).
:- dom_impl(eterms, concrete/3).
:- dom_impl(eterms, unknown_call/4).
:- dom_impl(eterms, unknown_entry/3).
:- dom_impl(eterms, empty_entry/3).
:- dom_impl(eterms, part_conc/4).
:- dom_impl(eterms, multi_part_conc/3).
:- dom_impl(eterms, collect_abstypes_abs/3).
:- dom_impl(eterms, rename_abstypes_abs/3).
%
% ---------------------------------------------------------------------------
:- use_module(domain(etermsvar)).
:- dom_def(etermsvar).
:- dom_impl(etermsvar, init_abstract_domain/1).
:- dom_impl(etermsvar, call_to_entry/9).
:- dom_impl(etermsvar, exit_to_prime/7).
:- dom_impl(etermsvar, project/5).
:- dom_impl(etermsvar, widencall/3).
:- dom_impl(etermsvar, widen/3).
:- dom_impl(etermsvar, compute_lub/2).
:- dom_impl(etermsvar, identical_abstract/2).
:- dom_impl(etermsvar, abs_sort/2).
:- dom_impl(etermsvar, extend/5).
:- dom_impl(etermsvar, less_or_equal/2).
:- dom_impl(etermsvar, glb/3).
:- dom_impl(etermsvar, call_to_success_fact/9).
:- dom_impl(etermsvar, special_builtin/5).
:- dom_impl(etermsvar, success_builtin/6).
:- dom_impl(etermsvar, call_to_success_builtin/6).
:- dom_impl(etermsvar, obtain_info/4).
:- dom_impl(etermsvar, input_interface/4).
:- dom_impl(etermsvar, input_user_interface/5).
:- dom_impl(etermsvar, asub_to_native/5).
% :- dom_impl(etermsvar, concrete/3).
:- dom_impl(etermsvar, unknown_call/4).
:- dom_impl(etermsvar, unknown_entry/3).
:- dom_impl(etermsvar, empty_entry/3).
:- dom_impl(etermsvar, part_conc/4).
:- dom_impl(etermsvar, multi_part_conc/3).
:- dom_impl(etermsvar, collect_abstypes_abs/3).
:- dom_impl(etermsvar, rename_abstypes_abs/3).
% ---------------------------------------------------------------------------
:- use_module(domain(svterms)).
:- dom_def(svterms).
:- dom_impl(svterms, init_abstract_domain/1).
:- dom_impl(svterms, call_to_entry/9).
:- dom_impl(svterms, exit_to_prime/7).
:- dom_impl(svterms, project/5).
:- dom_impl(svterms, widencall/3).
:- dom_impl(svterms, widen/3).
:- dom_impl(svterms, compute_lub/2).
:- dom_impl(svterms, identical_abstract/2).
:- dom_impl(svterms, abs_sort/2).
:- dom_impl(svterms, extend/5).
:- dom_impl(svterms, less_or_equal/2).
:- dom_impl(svterms, glb/3).
:- dom_impl(svterms, call_to_success_fact/9).
:- dom_impl(svterms, special_builtin/5).
:- dom_impl(svterms, success_builtin/6).
:- dom_impl(svterms, call_to_success_builtin/6).
:- dom_impl(svterms, input_interface/4).
:- dom_impl(svterms, input_user_interface/5).
:- dom_impl(svterms, asub_to_native/5).
:- dom_impl(svterms, concrete/3).
:- dom_impl(svterms, unknown_call/4).
:- dom_impl(svterms, unknown_entry/3).
:- dom_impl(svterms, empty_entry/3).
:- dom_impl(svterms, collect_abstypes_abs/3).
:- dom_impl(svterms, rename_abstypes_abs/3).
% ---------------------------------------------------------------------------
:- use_module(domain(deftypes)).
:- dom_def(deftypes).
:- dom_impl(deftypes, init_abstract_domain/1).
:- dom_impl(deftypes, call_to_entry/9).
:- dom_impl(deftypes, exit_to_prime/7).
:- dom_impl(deftypes, project/5).
:- dom_impl(deftypes, widencall/3).
:- dom_impl(deftypes, widen/3).
:- dom_impl(deftypes, compute_lub/2).
:- dom_impl(deftypes, identical_abstract/2).
:- dom_impl(deftypes, abs_sort/2).
:- dom_impl(deftypes, extend/5).
:- dom_impl(deftypes, less_or_equal/2).
:- dom_impl(deftypes, glb/3).
:- dom_impl(deftypes, call_to_success_fact/9).
:- dom_impl(deftypes, special_builtin/5).
:- dom_impl(deftypes, success_builtin/6).
:- dom_impl(deftypes, call_to_success_builtin/6).
:- dom_impl(deftypes, input_interface/4).
:- dom_impl(deftypes, input_user_interface/5).
:- dom_impl(deftypes, asub_to_native/5).
:- dom_impl(deftypes, concrete/3).
:- dom_impl(deftypes, unknown_call/4).
:- dom_impl(deftypes, unknown_entry/3).
:- dom_impl(deftypes, empty_entry/3).
:- dom_impl(deftypes, collect_abstypes_abs/3).
:- dom_impl(deftypes, rename_abstypes_abs/3).
:- dom_impl(deftypes, contains_parameters/1).
%
% ===========================================================================
:- doc(section, "Numeric domains").
% ---------------------------------------------------------------------------
% intervals domain % [IG] new, simplified nonrelational domain
:- use_module(domain(nonrel)).
% (simpler domain interface, only for non-relational domains)
:- dom_def(nonrel_intervals).
:- dom_impl(nonrel_intervals, init_abstract_domain/1).
:- dom_impl(nonrel_intervals, amgu/4).
:- dom_impl(nonrel_intervals, call_to_entry/9).
:- dom_impl(nonrel_intervals, exit_to_prime/7).
:- dom_impl(nonrel_intervals, project/5).
:- dom_impl(nonrel_intervals, widencall/3).
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
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(polyhedra)).
:- dom_def(polyhedra).
:- dom_impl(polyhedra, init_abstract_domain/1).
:- dom_impl(polyhedra, call_to_entry/9).
:- dom_impl(polyhedra, exit_to_prime/7).
:- dom_impl(polyhedra, project/5).
:- dom_impl(polyhedra, widencall/3). 
:- dom_impl(polyhedra, widen/3).
:- dom_impl(polyhedra, compute_lub/2).
:- dom_impl(polyhedra, identical_abstract/2).
:- dom_impl(polyhedra, abs_sort/2).
:- dom_impl(polyhedra, extend/5).
:- dom_impl(polyhedra, less_or_equal/2).
:- dom_impl(polyhedra, glb/3).
:- dom_impl(polyhedra, eliminate_equivalent/2).
:- dom_impl(polyhedra, call_to_success_fact/9).
:- dom_impl(polyhedra, special_builtin/5).
:- dom_impl(polyhedra, success_builtin/6).
:- dom_impl(polyhedra, call_to_success_builtin/6).
:- dom_impl(polyhedra, input_interface/4).
:- dom_impl(polyhedra, input_user_interface/5).
:- dom_impl(polyhedra, asub_to_native/5).
:- dom_impl(polyhedra, unknown_call/4).
:- dom_impl(polyhedra, unknown_entry/3).
:- dom_impl(polyhedra, empty_entry/3).
:- endif.
% ===========================================================================
:- doc(section, "OO/Java domains"). % TODO: imperative? points-to? nullity?
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(java_nullity)). % for java programs
:- dom_def(java_nullity).
:- dom_impl(java_nullity, call_to_entry/9).
:- dom_impl(java_nullity, exit_to_prime/7).
:- dom_impl(java_nullity, project/5).
:- dom_impl(java_nullity, compute_lub/2).
:- dom_impl(java_nullity, abs_sort/2).
:- dom_impl(java_nullity, extend/5).
:- dom_impl(java_nullity, less_or_equal/2).
:- dom_impl(java_nullity, glb/3).
:- dom_impl(java_nullity, call_to_success_fact/9).
:- dom_impl(java_nullity, special_builtin/5).
:- dom_impl(java_nullity, success_builtin/6).
:- dom_impl(java_nullity, input_interface/4).
:- dom_impl(java_nullity, input_user_interface/5).
:- dom_impl(java_nullity, asub_to_native/5).
:- dom_impl(java_nullity, unknown_call/4).
:- dom_impl(java_nullity, unknown_entry/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_son)).
:- dom_def(oo_son).
:- dom_impl(oo_son, call_to_entry/9).
:- dom_impl(oo_son, exit_to_prime/7).
:- dom_impl(oo_son, project/5).
:- dom_impl(oo_son, compute_lub/2).
:- dom_impl(oo_son, identical_abstract/2).
:- dom_impl(oo_son, abs_sort/2).
:- dom_impl(oo_son, extend/5).
:- dom_impl(oo_son, less_or_equal/2).
:- dom_impl(oo_son, glb/3).
:- dom_impl(oo_son, call_to_success_fact/9).
:- dom_impl(oo_son, special_builtin/5).
:- dom_impl(oo_son, success_builtin/6).
:- dom_impl(oo_son, call_to_success_builtin/6).
:- dom_impl(oo_son, input_interface/4).
:- dom_impl(oo_son, input_user_interface/5).
:- dom_impl(oo_son, asub_to_native/5).
:- dom_impl(oo_son, unknown_call/4).
:- dom_impl(oo_son, unknown_entry/3).
:- dom_impl(oo_son, empty_entry/3).
% :- dom_impl(oo_son, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_shnltau)).
:- dom_def(oo_shnltau).
% :- dom_impl(oo_shnltau, init_abstract_domain/1).
:- dom_impl(oo_shnltau, call_to_entry/9).
:- dom_impl(oo_shnltau, exit_to_prime/7).
:- dom_impl(oo_shnltau, project/5).
:- dom_impl(oo_shnltau, compute_lub/2).
:- dom_impl(oo_shnltau, abs_sort/2).
:- dom_impl(oo_shnltau, extend/5).
:- dom_impl(oo_shnltau, less_or_equal/2).
:- dom_impl(oo_shnltau, glb/3).
:- dom_impl(oo_shnltau, call_to_success_fact/9).
:- dom_impl(oo_shnltau, special_builtin/5).
:- dom_impl(oo_shnltau, success_builtin/6).
:- dom_impl(oo_shnltau, call_to_success_builtin/6).
:- dom_impl(oo_shnltau, input_interface/4).
:- dom_impl(oo_shnltau, input_user_interface/5).
:- dom_impl(oo_shnltau, asub_to_native/5).
:- dom_impl(oo_shnltau, unknown_call/4).
:- dom_impl(oo_shnltau, unknown_entry/3).
:- dom_impl(oo_shnltau, empty_entry/3).
% :- dom_impl(oo_shnltau, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(oo_types)).
:- dom_def(oo_types).
% :- dom_impl(oo_types, init_abstract_domain/1).
:- dom_impl(oo_types, call_to_entry/9).
:- dom_impl(oo_types, exit_to_prime/7).
:- dom_impl(oo_types, project/5).
:- dom_impl(oo_types, compute_lub/2).
:- dom_impl(oo_types, abs_sort/2).
:- dom_impl(oo_types, extend/5).
:- dom_impl(oo_types, less_or_equal/2).
:- dom_impl(oo_types, glb/3).
:- dom_impl(oo_types, call_to_success_fact/9).
:- dom_impl(oo_types, special_builtin/5).
:- dom_impl(oo_types, success_builtin/6).
:- dom_impl(oo_types, call_to_success_builtin/6).
:- dom_impl(oo_types, input_interface/4).
:- dom_impl(oo_types, input_user_interface/5).
:- dom_impl(oo_types, asub_to_native/5).
:- dom_impl(oo_types, unknown_call/4).
:- dom_impl(oo_types, unknown_entry/3).
:- dom_impl(oo_types, empty_entry/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(java_cha)).
:- dom_def(java_cha).
:- dom_impl(java_cha, call_to_entry/9).
:- dom_impl(java_cha, exit_to_prime/7).
:- dom_impl(java_cha, project/5).
:- dom_impl(java_cha, compute_lub/2).
:- dom_impl(java_cha, abs_sort/2).
:- dom_impl(java_cha, extend/5).
:- dom_impl(java_cha, less_or_equal/2).
:- dom_impl(java_cha, glb/3).
:- dom_impl(java_cha, call_to_success_fact/9).
:- dom_impl(java_cha, special_builtin/5).
:- dom_impl(java_cha, success_builtin/6).
:- dom_impl(java_cha, input_interface/4).
:- dom_impl(java_cha, input_user_interface/5).
:- dom_impl(java_cha, asub_to_native/5).
:- dom_impl(java_cha, unknown_call/4).
:- dom_impl(java_cha, unknown_entry/3).
:- endif.
% ===========================================================================
:- doc(section, "Computation domains").
% ---------------------------------------------------------------------------
% nonfailure
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(nfplai)).
:- dom_def(nf).
:- dom_impl(nf, init_abstract_domain/1).
:- dom_impl(nf, call_to_entry/9).
:- dom_impl(nf, exit_to_prime/7).
:- dom_impl(nf, project/5).
:- dom_impl(nf, widencall/3).
:- dom_impl(nf, widen/3).
:- dom_impl(nf, compute_lub/2). 
:- dom_impl(nf, compute_clauses_lub/3).
:- dom_impl(nf, identical_abstract/2).
:- dom_impl(nf, fixpoint_covered/2).
:- dom_impl(nf, abs_sort/2).
:- dom_impl(nf, extend/5).
:- dom_impl(nf, less_or_equal/2).
:- dom_impl(nf, glb/3).
:- dom_impl(nf, eliminate_equivalent/2).
:- dom_impl(nf, call_to_success_fact/9).
:- dom_impl(nf, special_builtin/5).
:- dom_impl(nf, combined_special_builtin0/2).
:- dom_impl(nf, split_combined_domain/3).
:- dom_impl(nf, success_builtin/6).
:- dom_impl(nf, input_interface/4).
:- dom_impl(nf, input_user_interface/5).
:- dom_impl(nf, asub_to_native/5).
:- dom_impl(nf, unknown_call/4).
:- dom_impl(nf, unknown_entry/3).
:- dom_impl(nf, empty_entry/3).
:- dom_impl(nf, dom_statistics/1).
:- endif.
% ---------------------------------------------------------------------------
% determinism
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(detplai)).
:- dom_def(det).
:- dom_impl(det, init_abstract_domain/1).
:- dom_impl(det, call_to_entry/9).
:- dom_impl(det, exit_to_prime/7).
:- dom_impl(det, project/5).
:- dom_impl(det, widencall/3).
:- dom_impl(det, widen/3).
:- dom_impl(det, compute_lub/2).
:- dom_impl(det, compute_clauses_lub/3).
:- dom_impl(det, identical_abstract/2).
:- dom_impl(det, fixpoint_covered/2).
:- dom_impl(det, abs_sort/2).
:- dom_impl(det, extend/5).
:- dom_impl(det, less_or_equal/2).
:- dom_impl(det, glb/3).
:- dom_impl(det, eliminate_equivalent/2).
:- dom_impl(det, call_to_success_fact/9).
:- dom_impl(det, special_builtin/5).
:- dom_impl(det, combined_special_builtin0/2).
:- dom_impl(det, split_combined_domain/3).
:- dom_impl(det, success_builtin/6).
:- dom_impl(det, obtain_info/4).
:- dom_impl(det, input_interface/4).
:- dom_impl(det, input_user_interface/5).
:- dom_impl(det, asub_to_native/5).
:- dom_impl(det, unknown_call/4).
:- dom_impl(det, unknown_entry/3).
:- dom_impl(det, empty_entry/3).
:- dom_impl(det, dom_statistics/1).
:- endif.
% ===========================================================================
:- doc(section, "Resources domains").
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/res_plai)).
:- dom_def(res_plai).
:- dom_impl(res_plai, init_abstract_domain/1).
:- dom_impl(res_plai, call_to_entry/9).
:- dom_impl(res_plai, exit_to_prime/7).
:- dom_impl(res_plai, project/5).
% :- dom_impl(res_plai, widencall/3).
:- dom_impl(res_plai, widen/3).
:- dom_impl(res_plai, compute_lub/2).
:- dom_impl(res_plai, compute_clauses_lub/3).
% :- dom_impl(res_plai, compute_clauses_glb/3).
:- dom_impl(res_plai, identical_abstract/2).
:- dom_impl(res_plai, abs_sort/2).
:- dom_impl(res_plai, extend/5).
:- dom_impl(res_plai, less_or_equal/2).
:- dom_impl(res_plai, glb/3).
:- dom_impl(res_plai, eliminate_equivalent/2).
:- dom_impl(res_plai, call_to_success_fact/9).
:- dom_impl(res_plai, special_builtin/5).
:- dom_impl(res_plai, combined_special_builtin0/2).
:- dom_impl(res_plai, split_combined_domain/3).
% :- dom_impl(res_plai, success_builtin/6).
:- dom_impl(res_plai, call_to_success_builtin/6).
:- dom_impl(res_plai, obtain_info/4).
:- dom_impl(res_plai, input_interface/4).
:- dom_impl(res_plai, input_user_interface/5).
:- dom_impl(res_plai, asub_to_native/5).
:- dom_impl(res_plai, unknown_call/4).
:- dom_impl(res_plai, unknown_entry/3).
:- dom_impl(res_plai, empty_entry/3).
:- dom_impl(res_plai, collect_abstypes_abs/3).
:- dom_impl(res_plai, rename_abstypes_abs/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/res_plai_stprf)).
:- dom_def(res_plai_stprf).
:- dom_impl(res_plai_stprf, init_abstract_domain/1).
:- dom_impl(res_plai_stprf, call_to_entry/9).
:- dom_impl(res_plai_stprf, exit_to_prime/7).
:- dom_impl(res_plai_stprf, project/5).
:- dom_impl(res_plai_stprf, widen/3).
:- dom_impl(res_plai_stprf, compute_lub/2).
:- dom_impl(res_plai_stprf, compute_clauses_lub/3).
:- dom_impl(res_plai_stprf, identical_abstract/2).
:- dom_impl(res_plai_stprf, abs_sort/2).
:- dom_impl(res_plai_stprf, extend/5).
:- dom_impl(res_plai_stprf, less_or_equal/2).
:- dom_impl(res_plai_stprf, glb/3).
:- dom_impl(res_plai_stprf, eliminate_equivalent/2).
:- dom_impl(res_plai_stprf, call_to_success_fact/9).
:- dom_impl(res_plai_stprf, special_builtin/5).
:- dom_impl(res_plai_stprf, combined_special_builtin0/2).
:- dom_impl(res_plai_stprf, split_combined_domain/3).
:- dom_impl(res_plai_stprf, call_to_success_builtin/6).
:- dom_impl(res_plai_stprf, obtain_info/4).
:- dom_impl(res_plai_stprf, input_interface/4).
:- dom_impl(res_plai_stprf, input_user_interface/5).
:- dom_impl(res_plai_stprf, asub_to_native/5).
:- dom_impl(res_plai_stprf, unknown_call/4).
:- dom_impl(res_plai_stprf, unknown_entry/3).
:- dom_impl(res_plai_stprf, empty_entry/3).
:- dom_impl(res_plai_stprf, collect_abstypes_abs/3).
:- dom_impl(res_plai_stprf, rename_abstypes_abs/3).
:- endif.
% ---------------------------------------------------------------------------
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(resources/sized_types)).
:- dom_def(sized_types).
:- dom_impl(sized_types, init_abstract_domain/1).
:- dom_impl(sized_types, call_to_entry/9).
:- dom_impl(sized_types, exit_to_prime/7).
:- dom_impl(sized_types, project/5).
:- dom_impl(sized_types, widen/3).
:- dom_impl(sized_types, compute_lub/2).
:- dom_impl(sized_types, compute_clauses_lub/3).
:- dom_impl(sized_types, identical_abstract/2).
:- dom_impl(sized_types, abs_sort/2).
:- dom_impl(sized_types, extend/5).
:- dom_impl(sized_types, less_or_equal/2).
:- dom_impl(sized_types, glb/3).
:- dom_impl(sized_types, eliminate_equivalent/2).
:- dom_impl(sized_types, call_to_success_fact/9).
:- dom_impl(sized_types, special_builtin/5).
:- dom_impl(sized_types, combined_special_builtin0/2).
:- dom_impl(sized_types, split_combined_domain/3).
:- dom_impl(sized_types, call_to_success_builtin/6).
:- dom_impl(sized_types, obtain_info/4).
:- dom_impl(sized_types, input_interface/4).
:- dom_impl(sized_types, input_user_interface/5).
:- dom_impl(sized_types, asub_to_native/5).
:- dom_impl(sized_types, unknown_call/4).
:- dom_impl(sized_types, unknown_entry/3).
:- dom_impl(sized_types, empty_entry/3).
:- dom_impl(sized_types, collect_abstypes_abs/3).
:- dom_impl(sized_types, rename_abstypes_abs/3).
:- endif.

% ===========================================================================

