:- module(shfrson,
	[ shfrson_call_to_entry/9,
	  shfrson_call_to_success_fact/9, 
	  shfrson_special_builtin/5,
	  shfrson_body_succ_builtin/8,
	  shfrson_compute_lub/2,
	  shfrson_exit_to_prime/7,
	  shfrson_extend/5,   
	  shfrson_input_user_interface/5, 
	  shfrson_input_interface/4, 
	  shfrson_less_or_equal/2,  
	  shfrson_glb/3,
	  shfrson_asub_to_native/5,
	  shfrson_project/5,  
	  shfrson_abs_sort/2,     
	  shfrson_unknown_call/4,
	  shfrson_unknown_entry/3,  
	  shfrson_empty_entry/3,
	%
	  shfrson_compose/4
	],
	[ ]).

%------------------------------------------------------------------------%
%                                                                        %
%                          Started: 22/10/92                             %
%                       programmer: M.J. Garcia de la Banda              %
%                                                                        %
% Function: combined analysis using the Sondergaard and the Sharing      %
%           domain                                                       %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                    Meanning of the Program Variables                   %
%                                                                        %
%  _son    : Suffix added to abstract subsitutions (Prime,Exit,Proj,...) %
%            for the part corresponding to Sondergaard domain            %
%  _shfr   : Suffix added to abstract subsitutions (Prime,Exit,Proj,...) %
%            for the part corresponding to Sharing+Freeness domain       %
%  GSon    : First argument in substitutions of Sondergaard domain (set  %
%            of ground variables)                                        %
%  SSon    : Second argument in substitutions of Sondergaard domain (set %
%            for singletons and couples of variables)                    %
%  Sh      : First argument in substitutions of Sharing+Freeness domain  %
%            (set sharing for variables)                                 %
%  Fr      : Second argument in substitutions of Sharing+Freeness domain %
%            (list of variable/value assignments)                        %
%  Rest are as in domain_dependent.pl                                    %
%-------------------------------------------------------------------------
% All abstract functions for the combined domain "shfrson" first compute %
% the results for the corresponding to the "shfr" and "son" functions    %
% and then compose the information of both, eliminating redundancies.    %
% See compose function.                                                  %
%-------------------------------------------------------------------------

:- use_module(domain(sharefree)).
:- use_module(domain(sondergaard)).
:- use_module(domain(s_grshfr), [change_values_if_differ/5, projected_gvars/3]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- use_module(library(llists), [collect_singletons/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(terms_vars), [varset/2]).

%-------------------------------------------------------------------------

shfrson_call_to_entry(Sv,Sg,Hv,Head,K,Fv,(Proj_son,Proj_shfr),Entry,Extra):-
	son_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_son,Entry_son,Extra_son),
	shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_shfr,Entry_shfr,Extra_shfr),
	compose(Entry_son,Entry_shfr,Hv,Entry),
	Extra = (Extra_son,Extra_shfr).

%-------------------------------------------------------------------------

shfrson_exit_to_prime(_,_,_,_,'$bottom',_,Prime):- !,
	Prime = '$bottom'.
shfrson_exit_to_prime(Sg,Hv,Head,Sv,(Exit_son,Exit_shfr),ExtraInfo,Prime):- 
	ExtraInfo = (Extra_son,Extra_shfr),
	shfr_exit_to_prime(Sg,Hv,Head,Sv,Exit_shfr,Extra_shfr,Prime_shfr),
	son_exit_to_prime(Sg,Hv,Head,Sv,Exit_son,Extra_son,Prime_son),
	compose(Prime_son,Prime_shfr,Sv,Prime).

%-------------------------------------------------------------------------

shfrson_extend(_Sg,'$bottom',_,_,Succ):- !,Succ = '$bottom'.
shfrson_extend(_Sg,(_,_),[],Call,Succ):- !, Call = Succ.
shfrson_extend(Sg,(Prime_son,Prime_shfr),Sv,(Call_son,Call_shfr),Succ):-
	shfr_extend(Sg,Prime_shfr,Sv,Call_shfr,Succ_shfr),
	son_extend(Sg,Prime_son,Sv,Call_son,Succ_son),
	Call_shfr = (_,Fr),
	collect_vars_freeness(Fr,Vars),
	compose(Succ_son,Succ_shfr,Vars,Succ).

%-------------------------------------------------------------------------

shfrson_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
	Proj = (Proj_son,Proj_shfr),
	son_call_to_prime_fact(Sg,Hv,Head,Sv,Proj_son,Prime_son),
	shfr_call_to_prime_fact(Sg,Hv,Head,Sv,Proj_shfr,Prime_shfr),
	compose(Prime_son,Prime_shfr,Sv,Prime),
	shfrson_extend(Sg,Prime,Sv,Call,Succ).

% ---------------------------------------------------------------------------

shfrson_special_builtin(SgKey,Sg,Subgoal,(TypeSon,TypeSh),(CondSon,CondSh)) :-
	shfr_special_builtin(SgKey,Sg,Subgoal,TypeSh,CondSh),
	son_special_builtin(SgKey,Sg,Subgoal,TypeSon,CondSon).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [body_succ_builtin/9, body_builtin/9]).

% TODO: These do have special(_), special care (old comment)
shfrson_body_succ_builtin((TSon,TSh),Sg,(CSon,CSh),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_son,Call_sh),
	Proj=(Proj_son,Proj_sh),
	body_succ_builtin(son,TSon,Sg,CSon,Sv,HvFv,Call_son,Proj_son,Succ_son),
	body_succ_builtin(shfr,TSh,Sg,CSh,Sv,HvFv,Call_sh,Proj_sh,Succ_sh),
	shfrson_compose(Call,Succ_sh,Succ_son,Succ).
shfrson_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
	body_builtin(shfrson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%-------------------------------------------------------------------------

shfrson_compose((_Son,(_Sh,Fr)),Succ_shfr,Succ_son,Succ):-
	collect_vars_freeness(Fr,Vars),
	compose(Succ_son,Succ_shfr,Vars,Succ).

%-------------------------------------------------------------------------

shfrson_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
shfrson_unknown_call(Sg,Vars,(Call_son,Call_shfr),Succ):-
	shfr_unknown_call(Sg,Vars,Call_shfr,Succ_shfr),
	son_unknown_call(Sg,Vars,Call_son,Succ_son),
	Call_shfr = (_,Fr),
	collect_vars_freeness(Fr,AllVars),
	compose(Succ_son,Succ_shfr,AllVars,Succ).

%-------------------------------------------------------------------------

shfrson_unknown_entry(Sg,Qv,Call):-
	shfr_unknown_entry(Sg,Qv,Call_shfr),
	son_unknown_entry(Sg,Qv,Call_son),
	compose(Call_son,Call_shfr,Qv,Call).

%-------------------------------------------------------------------------

shfrson_empty_entry(Sg,Qv,Call):-
	shfr_empty_entry(Sg,Qv,Call_sh),
	son_empty_entry(Sg,Qv,Call_son),
	compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

shfrson_project(_,_,_,'$bottom',Proj):- !,
	Proj = '$bottom'.
shfrson_project(_Sg,[],_HvFv_u,_,Proj) :- !,
	Proj = (([],[]),([],[])).
shfrson_project(Sg,Vars,HvFv_u,(Call_son,Call_shfr),(Proj_son,Proj_shfr)):-
	son_project(Sg,Vars,HvFv_u,Call_son,Proj_son),
	shfr_project(Sg,Vars,HvFv_u,Call_shfr,Proj_shfr).

%-------------------------------------------------------------------------

shfrson_compute_lub([ASub],ASub) :- !.
shfrson_compute_lub([ASub1,ASub2|Rest],Lub) :-
	ASub1 == ASub2,!,
	shfrson_compute_lub([ASub1|Rest],Lub).
shfrson_compute_lub(['$bottom',ASub|Rest],Lub) :- !,
	shfrson_compute_lub([ASub|Rest],Lub).
shfrson_compute_lub([ASub,'$bottom'|Rest],Lub) :- !,
	shfrson_compute_lub([ASub|Rest],Lub).
shfrson_compute_lub([(ASub_son1,ASub_shfr1),(ASub_son2,ASub_shfr2)|Rest],Lub):-
	son_lub(ASub_son1,ASub_son2,ASub_son3),
	shfr_compute_lub([ASub_shfr1,ASub_shfr2],ASub_shfr3),
	shfrson_compute_lub([(ASub_son3,ASub_shfr3)|Rest],Lub).

%-------------------------------------------------------------------------

shfrson_abs_sort('$bottom','$bottom').
shfrson_abs_sort((ASub_son,ASub_shfr),(ASub_son_s,ASub_shfr_s)):-
	son_abs_sort(ASub_son,ASub_son_s),
	shfr_abs_sort(ASub_shfr,ASub_shfr_s).

%--------------------------------------------------------------------------

shfrson_input_user_interface((Son,Shfr),Qv,ASub,Sg,MaybeCallASub):-
	son_input_user_interface(Son,Qv,ASubSon,Sg,MaybeCallASub),
	shfr_input_user_interface(Shfr,Qv,ASubShfr,Sg,MaybeCallASub),
	compose(ASubSon,ASubShfr,Qv,ASub).

shfrson_input_interface(Info,Kind,(Son0,Shfr0),(Son,Shfr)):-
	% both of them already call share_input_...
	son_input_interface(Info,KindSon,Son0,Son),
	shfr_input_interface(Info,KindShfr,Shfr0,Shfr),
	compose_kind(KindSon,KindShfr,Kind).

compose_kind(approx,approx,approx):- !.
compose_kind(_Kind0,_Kind1,perfect).

%--------------------------------------------------------------------------

shfrson_asub_to_native(((_Gr,SSon),ShFr),Qv,OutFlag,ASub_user,Comps):-
	collect_singletons(SSon,Singletons),
	varset(Singletons,NonLinearVars),
	ord_subtract(Qv,NonLinearVars,LinearVars),
	shfr_asub_to_native(ShFr,Qv,OutFlag,ASub_user0,Comps),
	if_not_nil(LinearVars,linear(LinearVars),ASub_user,ASub_user0).

%------------------------------------------------------------------------%
% shfrson_less_or_equal(+,+)                                             %
% shfrson_less_or_equal(ASub0,ASub1)                                     %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%
shfrson_less_or_equal(ASub0,ASub1):-
	ASub0 == ASub1.
shfrson_less_or_equal((Son0,Sh0),(Son1,Sh1)):-
	shfr_less_or_equal(Sh0,Sh1),
	son_less_or_equal(Son0,Son1).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
shfrson_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

%-------------------------------------------------------------------------
% compose(+,+,+,-)                                               |
% compose((GSon,SSon),(Sh,Fr),Sv,((NewGSon,NewSon),(NewSh,NewFr))|
% It composes the two abstract substitutions in order to eliminate       |
% redundancies. In doing this, it performs the folowing steps:           |
% (1) propagates the sharing info from SSon to Sh (NewSh)                |
% (2) collects in Gv the ground variables w.r.t. NewSh                   |
% (3) NewGSon  is the result of merging Gv and GSon                      |
% (4) Changes the freeness value of all variables in Gv to g (checking   |
%     that the old freeness value is different from "f", since if so, it |
%     is an error and '$bottom' must be returned) obtaining NewFr        |
% (5) NewSSon is the result of eliminating the pairs not allowed by      |
%     NewSh                                                              |
%-------------------------------------------------------------------------
compose((GSon,SSon),(Sh,Fr),Sv,((NewGSon,NewSon),(NewSh,NewFr))):-
	propagate_to_sh(Sh,SSon,NewSh,Allowed_sh), 
	projected_gvars(NewSh,Sv,Gv),
	merge(GSon,Gv,NewGSon),
	change_values_if_differ(Gv,Fr,NewFr,g,f),
	propagate_to_son(SSon,Allowed_sh,NewGSon,NewSon),!.
compose(_,_,_,'$bottom').

% auxiliary: identical to that in sharefree.pl
collect_vars_freeness([],[]).
collect_vars_freeness([X/_|Rest],[X|Vars]):-
	collect_vars_freeness(Rest,Vars).
