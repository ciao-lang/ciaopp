% ----------
% aidomain(lsigndef). % TODO: MOVE TO ATTIC
call_to_entry(lsigndef,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, lsigndef_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo).
exit_to_prime(lsigndef,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :- !, lsigndef_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).
project(lsigndef,Sg,Vars,HvFv,ASub,Proj) :- !, lsigndef_project(Sg,Vars,HvFv,ASub,Proj).
compute_lub(lsigndef,ListASub,LubASub) :- !, lsigndef_compute_lub(ListASub,LubASub).
abs_sort(lsigndef,ASub,ASub_s) :- !, lsigndef_sort(ASub,ASub_s).
extend(lsigndef,Sg,Prime,Sv,Call,Succ) :- !, lsigndef_extend(Sg,Prime,Sv,Call,Succ).
less_or_equal(lsigndef,ASub0,ASub1) :- !, lsigndef_less_or_equal(ASub0,ASub1).
glb(lsigndef,ASub0,ASub1,ASub) :- !, lsigndef_glb(ASub0,ASub1,ASub).
call_to_success_fact(lsigndef,Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- !, lsigndef_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).
input_interface(lsigndef,InputUser,Kind,Struct0,Struct1) :- !, lsigndef_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(lsigndef,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, lsigndef_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
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
lsigndef_input_user_interface(_,_,_,_,_).
lsigndef_input_interface(_,_,_,_).
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
% aidomain(lsignshfr). % TODO: MOVE TO ATTIC
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
input_user_interface(lsignshfr,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, lsignshfr_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
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
lsignshfr_input_user_interface(_,_,_,_,_). 
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
% aidomain(sha). % TODO: MOVE TO ATTIC
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
special_builtin(sha,SgKey,Sg,Subgoal,Type,Condvars) :- !, sha_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
success_builtin(sha,Type,Sv_uns,Condvars,_HvFv_u,Call,Succ) :- !, sha_success_builtin(Type,Sv_uns,Condvars,Call,Succ).
call_to_success_builtin(sha,SgKey,Sg,Sv,Call,Proj,Succ) :- !, sha_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).
input_interface(sha,InputUser,Kind,Struct0,Struct1) :- !, sha_input_interface(InputUser,Kind,Struct0,Struct1).
input_user_interface(sha,InputUser,Qv,ASub,Sg,MaybeCallASub) :- !, sha_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub).
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
sha_input_user_interface(_,_,_,_,_). 
sha_input_interface(_,_,_,_). 
sha_less_or_equal(_,_).
% sha_lub(_,_,_).        
% sha_output_interface(_,_).
sha_asub_to_native(_,_,_,[],[]).
sha_project(_,_,_,_,_).      
sha_special_builtin(_,_,_,_,_).
sha_success_builtin(_,_,_,_,_).
sha_unknown_call(_,_,_,_).
sha_unknown_entry(_,_,_).
sha_empty_entry(_,_,_).
sha_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.
% ----------
% aidomain(typeshfr). % TODO: MOVE TO ATTIC
call_to_entry(typeshfr,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :- !, shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo). % AADEBUG
compute_lub(typeshfr,ListASub,LubASub) :- !, shfr_compute_lub(ListASub,LubASub). %% AADEBUG added
identical_abstract(typeshfr,ASub1,ASub2) :- !, identical_abstract(shfr,ASub1,ASub2). %% AADEBUG
abs_sort(typeshfr,ASub,ASub_s) :- !, abs_sort(shfr,ASub,ASub_s). %% AADEBUG
glb(typeshfr,ASub0,ASub1,ASub) :- !, glb(shfr,ASub0,ASub1,ASub).
