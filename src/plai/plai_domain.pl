% (included file)

% Definition of aidomain in PLAI
:- use_package(aidomain).

% TODO: See part_domains.pl for documentation

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
:- use_module(ciaopp(plai/domains), [
    compute_lub/3,
    absub_fixpoint_covered/3,
    body_builtin/9,
    undef_call_to_success_builtin/2]).

% NOTE: keep dom_base definitions as short as possible (they are
% duplicated for each implementation)
% TODO: Do not materialize them for the dom_itf module

:- dom_base(init_abstract_domain/1).
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
%       domains:compute_lub(AbsInt,[Prime0,Prime1],NewPrime).

:- dom_base(widen/3).
basedom_widen(AbsInt,Prime0,Prime1,NewPrime) :- % TODO: [IG] define in domain?
    domains:compute_lub(AbsInt,[Prime0,Prime1],NewPrime).

:- dom_base(compute_clauses_lub/3).
basedom_compute_clauses_lub(_AbsInt,Lub,_Proj,Lub).

:- dom_base(compute_clauses_glb/3).
basedom_compute_clauses_glb(_AbsInt,Lub,_Proj,Lub).

:- dom_base(identical_abstract/2).
basedom_identical_abstract(_AbsInt,ASub1,ASub2) :- ASub1==ASub2.

:- dom_base(fixpoint_covered/2).
basedom_fixpoint_covered(AbsInt,Prime0,Prime1) :-
    domains:absub_fixpoint_covered(AbsInt,Prime0,Prime1).

:- dom_base(fixpoint_covered_gfp/2).
basedom_fixpoint_covered_gfp(AbsInt,Prime0,Prime1) :-
    domains:absub_fixpoint_covered(AbsInt,Prime0,Prime1).

:- dom_base(eliminate_equivalent/2).
basedom_eliminate_equivalent(_AbsInt,TmpLSucc,LSucc) :- sort(TmpLSucc,LSucc). % TODO: valid if ASub1==ASub2 means equivalent

:- dom_base(abs_subset/2).
basedom_abs_subset(_AbsInt,LASub1,LASub2) :-
    ord_subset(LASub1,LASub2).

:- dom_base(body_succ_builtin/8).
basedom_body_succ_builtin(AbsInt,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :-
    domains:body_builtin(AbsInt,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

:- dom_base(call_to_success_builtin/6).
basedom_call_to_success_builtin(AbsInt,SgKey,_Sg,_Sv,_Call,_Proj,'$bottom') :-
    domains:undef_call_to_success_builtin(AbsInt,SgKey).

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

