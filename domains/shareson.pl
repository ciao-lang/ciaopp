:- module(shareson,
    [ shareson_call_to_entry/9,
      shareson_call_to_success_fact/9, 
      shareson_special_builtin/5,
      shareson_body_succ_builtin/8,
      shareson_compute_lub/2,
      shareson_exit_to_prime/7,  
      shareson_extend/5,  
      shareson_input_user_interface/5,
      shareson_input_interface/4,
      shareson_less_or_equal/2, 
      shareson_glb/3,
      shareson_asub_to_native/5,
      shareson_project/5, 
      shareson_abs_sort/2,    
      shareson_unknown_call/4,  
      shareson_unknown_entry/3, 
      shareson_empty_entry/3,
    %
      shareson_compose/4
    ],
    [ ]).

:- include(ciaopp(plai/plai_domain)).
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

:- use_module(domain(sharing), [
    share_call_to_entry/9,
    share_exit_to_prime/7,
    share_extend/5,
    share_call_to_prime_fact/6,
    share_special_builtin/5,
    share_unknown_call/4,
    share_unknown_entry/3,
    share_empty_entry/3,
    share_project/5,
    share_lub/3,
    share_abs_sort/2,
    share_input_user_interface/5,
    share_less_or_equal/2
]).
:- use_module(domain(sondergaard)).
:- use_module(domain(s_grshfr), [projected_gvars/3]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- use_module(library(llists), [collect_singletons/2]).
:- use_module(library(lsets), [merge_list_of_lists/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(terms_vars), [varset/2]).

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 22/10/92                             %
%                       programmer: M.J. Garcia de la Banda              %
%                                                                        %
% Function: combined analysis using the Sondergaard and the Sharing      %
%           domain                                                       %
%------------------------------------------------------------------------%
%                    Meanning of the Program Variables                   %
%                                                                        %
%  _son    : Suffix added to abstract subsitutions (Prime,Exit,Proj,...) %
%            for the part corresponding to Sondergaard domain            %
%  _sh     : Suffix added to abstract subsitutions (Prime,Exit,Proj,...) %
%            for the part corresponding to Sharing domain                %
%  GSon    : First argument in substitutions of Sondergaard domain (set  %
%            of ground variables)                                        %
%  SSon    : Second argument in substitutions of Sondergaard domain (set %
%            for singletons and couples of variables)                    %
%  Sh      : Sharing domain (second component of the combination)        %
%  Rest are as in domain_dependent.pl                                    %
%-------------------------------------------------------------------------
% All abstract functions for the combined domain "shareson" first compute%
% the results for the corresponding to the "share" and "son" functions   %
% and then compose the information of both, eliminating redundancies.    %
% See compose function.                                                  %
%-------------------------------------------------------------------------

shareson_call_to_entry(Sv,Sg,Hv,Head,K,Fv,(Proj_son,Proj_sh),Entry,ExtraInfo):-
    son_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_son,Entry_son,ExtraInfo_son),
    share_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_sh,Entry_sh,ExtraInfo_sh),
    compose(Entry_son,Entry_sh,Hv,Entry),
    ExtraInfo = (ExtraInfo_son,ExtraInfo_sh).

%-------------------------------------------------------------------------

shareson_exit_to_prime(_,_,_,_,'$bottom',_,Prime):- !,
    Prime = '$bottom'.
shareson_exit_to_prime(Sg,Hv,Head,Sv,(Exit_son,Exit_sh),ExtraInfo,Prime):- 
    ExtraInfo = (ExtraInfo_son,ExtraInfo_sh),
    share_exit_to_prime(Sg,Hv,Head,Sv,Exit_sh,ExtraInfo_sh,Prime_sh),
    son_exit_to_prime(Sg,Hv,Head,Sv,Exit_son,ExtraInfo_son,Prime_son),
    compose(Prime_son,Prime_sh,Sv,Prime).
    
%-------------------------------------------------------------------------

shareson_extend(_Sg,'$bottom',_,_,Succ):- !,Succ = '$bottom'.
shareson_extend(_Sg,_Prime,[],Call,Succ):- !, Call = Succ.
shareson_extend(Sg,(Prime_son,Prime_sh),Sv,(Call_son,Call_sh),Succ):-
    share_extend(Sg,Prime_sh,Sv,Call_sh,Succ_sh),
    son_extend(Sg,Prime_son,Sv,Call_son,Succ_son),
    merge_list_of_lists(Call_sh,Vars),
    compose(Succ_son,Succ_sh,Vars,Succ).

%-------------------------------------------------------------------------

shareson_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    Proj = (Proj_son,Proj_sh),
    son_call_to_prime_fact(Sg,Hv,Head,Sv,Proj_son,Prime_son),
    share_call_to_prime_fact(Sg,Hv,Head,Sv,Proj_sh,Prime_sh),
    compose(Prime_son,Prime_sh,Sv,Prime),
    shareson_extend(Sg,Prime,Sv,Call,Succ).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
shareson_special_builtin(SgKey,Sg,Subgoal,(TypeSon,TypeSh),(CondSon,CondSh)) :-
    share_special_builtin(SgKey,Sg,Subgoal,TypeSh,CondSh),
    son_special_builtin(SgKey,Sg,Subgoal,TypeSon,CondSon).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [body_succ_builtin/9, body_builtin/9]).

% TODO: These do have special(_), special care (old comment)
shareson_body_succ_builtin((TSon,TSh),Sg,(CSon,CSh),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_son,Call_sh),
    Proj=(Proj_son,Proj_sh),
    body_succ_builtin(son,TSon,Sg,CSon,Sv,HvFv,Call_son,Proj_son,Succ_son),
    body_succ_builtin(share,TSh,Sg,CSh,Sv,HvFv,Call_sh,Proj_sh,Succ_sh),
    shareson_compose(Call,Succ_sh,Succ_son,Succ).
shareson_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
    body_builtin(shareson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%-------------------------------------------------------------------------

shareson_compose((_,Call_sh),Succ_sh,Succ_son,Succ):-
    merge_list_of_lists(Call_sh,Vars),
    compose(Succ_son,Succ_sh,Vars,Succ).

%-------------------------------------------------------------------------

shareson_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
shareson_unknown_call(Sg,Vars,(Call_son,Call_sh),Succ):-
    share_unknown_call(Sg,Vars,Call_sh,Succ_sh),
    son_unknown_call(Sg,Vars,Call_son,Succ_son),
    merge_list_of_lists(Call_sh,AllVars),
    compose(Succ_son,Succ_sh,AllVars,Succ).

%-------------------------------------------------------------------------

shareson_unknown_entry(Sg,Qv,Call):-
    share_unknown_entry(Sg,Qv,Call_sh),
    son_unknown_entry(Sg,Qv,Call_son),
    compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

shareson_empty_entry(Sg,Qv,Call):-
    share_empty_entry(Sg,Qv,Call_sh),
    son_empty_entry(Sg,Qv,Call_son),
    compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

shareson_project(_Sg,_Vars,_HvFv_u,'$bottom',Proj):- !,
    Proj = '$bottom'.
shareson_project(_Sg,[],_HvFv_u,_,Proj):- !,
    Proj = (([],[]),[]).
shareson_project(Sg,Vars,HvFv_u,(Call_son,Call_sh),(Proj_son,Proj_sh)):-
    son_project(Sg,Vars,HvFv_u,Call_son,Proj_son),
    share_project(Sg,Vars,HvFv_u,Call_sh,Proj_sh).

%-------------------------------------------------------------------------

shareson_compute_lub([ASub1,ASub2|Rest],Lub) :-
    ASub1 == ASub2,!,
    shareson_compute_lub([ASub1|Rest],Lub).
shareson_compute_lub(['$bottom',ASub|Rest],Lub) :- !,
    shareson_compute_lub([ASub|Rest],Lub).
shareson_compute_lub([ASub,'$bottom'|Rest],Lub) :- !,
    shareson_compute_lub([ASub|Rest],Lub).
shareson_compute_lub([(ASub_son1,ASub_sh1),(ASub_son2,ASub_sh2)|Rest],Lub) :-
    son_lub(ASub_son1,ASub_son2,ASub_son3),
    share_lub(ASub_sh1,ASub_sh2,ASub_sh3),
    shareson_compute_lub([(ASub_son3,ASub_sh3)|Rest],Lub).
shareson_compute_lub([ASub],ASub).

%---------------------------------------------------------------------------

shareson_abs_sort('$bottom','$bottom').
shareson_abs_sort((ASub_son,ASub_sh),(ASub_son_s,ASub_sh_s)):-
    son_abs_sort(ASub_son,ASub_son_s),
    share_abs_sort(ASub_sh,ASub_sh_s).

%--------------------------------------------------------------------------

shareson_input_user_interface(Struct,Qv,(Son,Sh),Sg,MaybeCallASub):-
    Struct = (Sharing,_Lin),
    son_input_user_interface(Struct,Qv,Son,Sg,MaybeCallASub),
    share_input_user_interface(Sharing,Qv,Sh,Sg,MaybeCallASub).

shareson_input_interface(Info,Kind,Struct0,Struct):-
    % already calls share_input_...
    son_input_interface(Info,Kind,Struct0,Struct).

%--------------------------------------------------------------------------

shareson_asub_to_native(((Gr,SSon),Sh),Qv,_OutFlag,ASub_user,[]):-
    collect_singletons(SSon,Singletons),
    varset(Singletons,NonLinearVars),
    ord_subtract(Qv,NonLinearVars,LinearVars),
    if_not_nil(Gr,ground(Gr),ASub_user,ASub_user0),
    if_not_nil(LinearVars,linear(LinearVars),ASub_user0,ASub_user1),
    if_not_nil(Sh,sharing(Sh),ASub_user1,[]).

%------------------------------------------------------------------------%
% shareson_less_or_equal(+,+)                                            %
% shareson_less_or_equal(ASub0,ASub1)                                    %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

shareson_less_or_equal(ASub0,ASub1):-
    ASub0 == ASub1.
shareson_less_or_equal((Son0,Sh0),(Son1,Sh1)):-
    share_less_or_equal(Sh0,Sh1),
    son_less_or_equal(Son0,Son1).

%-------------------------------------------------------------------------

shareson_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

%-------------------------------------------------------------------------
% compose(+,+,+,-)                                                       |
% compose(ASub_son,ASub_sh,Sv,(NewASub_son,NewASub_sh))                  |
% It composes the two abstract substitutions in order to eliminate       |
% redundancies. In doing this, it performs the folowing steps:           |
% (1) propagates the sharing info from SSon to ASub_sh (NewASub_sh)      |
% (2) collects in  Gv the ground variables w.r.t. NewASub_sh             |
% (3) NewGSon  is the result of merging Gv and GSon                      |
% (4) NewSSon is the result of eliminating the pairs not allowed by      |
%     NewASub_sh                                                         |
%-------------------------------------------------------------------------


compose((GSon,SSon),ASub_sh,Sv,((NewGSon,NewSSon),NewASub_sh)):-
    propagate_to_sh(ASub_sh,SSon,NewASub_sh,Allowed_sh),
    projected_gvars(NewASub_sh,Sv,Gv),
    merge(GSon,Gv,NewGSon),
    propagate_to_son(SSon,Allowed_sh,NewGSon,NewSSon),!.
compose(_,_,_,'$bottom').
