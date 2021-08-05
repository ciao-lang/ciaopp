:- module(shfrson, [], []).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shfrson, [default]).

%------------------------------------------------------------------------%
%                                                                        %
%                          Started: 22/10/92                             %
%                       programmer: M.J. Garcia de la Banda              %
%                                                                        %
% Function: combined analysis using the Sondergaard and the Sharing      %
%           domain                                                       %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
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

:- use_module(domain(sharefree), [
    call_to_entry/9,
    exit_to_prime/7,
    extend/5,
    call_to_prime_fact/6,
    special_builtin/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3,
    project/5,
    compute_lub/2,
    abs_sort/2,
    input_user_interface/5,
    input_interface/4,
    asub_to_native/5,
    less_or_equal/2
]).
:- use_module(domain(sondergaard), [
    call_to_entry/9,
    exit_to_prime/7,
    extend/5,
    call_to_prime_fact/6,
    special_builtin/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3,
    project/5,
    lub/3,
    abs_sort/2,
    input_user_interface/5,
    input_interface/4,
    less_or_equal/2
]).
:- use_module(domain(sondergaard), [
    propagate_to_sh/4,
    propagate_to_son/4
]).
:- use_module(domain(s_grshfr), [change_values_if_differ/5, projected_gvars/3]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- use_module(library(llists), [collect_singletons/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(terms_vars), [varset/2]).

%-------------------------------------------------------------------------

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(Sv,Sg,Hv,Head,K,Fv,(Proj_son,Proj_shfr),Entry,Extra):-
    sondergaard:call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_son,Entry_son,Extra_son),
    sharefree:call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_shfr,Entry_shfr,Extra_shfr),
    compose(Entry_son,Entry_shfr,Hv,Entry),
    Extra = (Extra_son,Extra_shfr).

%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,Prime):- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,Sv,(Exit_son,Exit_shfr),ExtraInfo,Prime):- 
    ExtraInfo = (Extra_son,Extra_shfr),
    sharefree:exit_to_prime(Sg,Hv,Head,Sv,Exit_shfr,Extra_shfr,Prime_shfr),
    sondergaard:exit_to_prime(Sg,Hv,Head,Sv,Exit_son,Extra_son,Prime_son),
    compose(Prime_son,Prime_shfr,Sv,Prime).

%-------------------------------------------------------------------------

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_,_,Succ):- !,Succ = '$bottom'.
extend(_Sg,(_,_),[],Call,Succ):- !, Call = Succ.
extend(Sg,(Prime_son,Prime_shfr),Sv,(Call_son,Call_shfr),Succ):-
    sharefree:extend(Sg,Prime_shfr,Sv,Call_shfr,Succ_shfr),
    sondergaard:extend(Sg,Prime_son,Sv,Call_son,Succ_son),
    Call_shfr = (_,Fr),
    collect_vars_freeness(Fr,Vars),
    compose(Succ_son,Succ_shfr,Vars,Succ).

%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    Proj = (Proj_son,Proj_shfr),
    sondergaard:call_to_prime_fact(Sg,Hv,Head,Sv,Proj_son,Prime_son),
    sharefree:call_to_prime_fact(Sg,Hv,Head,Sv,Proj_shfr,Prime_shfr),
    compose(Prime_son,Prime_shfr,Sv,Prime),
    shfrson:extend(Sg,Prime,Sv,Call,Succ).

% ---------------------------------------------------------------------------

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,(TypeSon,TypeSh),(CondSon,CondSh)) :-
    sharefree:special_builtin(SgKey,Sg,Subgoal,TypeSh,CondSh),
    sondergaard:special_builtin(SgKey,Sg,Subgoal,TypeSon,CondSon).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [body_succ_builtin/9, body_builtin/9]).

:- dom_impl(_, body_succ_builtin/8, [noq]).
% TODO: These do have special(_), special care (old comment)
body_succ_builtin((TSon,TSh),Sg,(CSon,CSh),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_son,Call_shfr),
    Proj=(Proj_son,Proj_shfr),
    body_succ_builtin(son,TSon,Sg,CSon,Sv,HvFv,Call_son,Proj_son,Succ_son),
    body_succ_builtin(shfr,TSh,Sg,CSh,Sv,HvFv,Call_shfr,Proj_shfr,Succ_shfr),
    Call_shfr = (_,Fr),
    collect_vars_freeness(Fr,Vars),
    compose(Succ_son,Succ_shfr,Vars,Succ).
body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
    body_builtin(shfrson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
unknown_call(Sg,Vars,(Call_son,Call_shfr),Succ):-
    sharefree:unknown_call(Sg,Vars,Call_shfr,Succ_shfr),
    sondergaard:unknown_call(Sg,Vars,Call_son,Succ_son),
    Call_shfr = (_,Fr),
    collect_vars_freeness(Fr,AllVars),
    compose(Succ_son,Succ_shfr,AllVars,Succ).

%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(Sg,Qv,Call):-
    sharefree:unknown_entry(Sg,Qv,Call_shfr),
    sondergaard:unknown_entry(Sg,Qv,Call_son),
    compose(Call_son,Call_shfr,Qv,Call).

%-------------------------------------------------------------------------

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(Sg,Qv,Call):-
    sharefree:empty_entry(Sg,Qv,Call_sh),
    sondergaard:empty_entry(Sg,Qv,Call_son),
    compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
project(_,_,_,'$bottom',Proj):- !,
    Proj = '$bottom'.
project(_Sg,[],_HvFv_u,_,Proj) :- !,
    Proj = (([],[]),([],[])).
project(Sg,Vars,HvFv_u,(Call_son,Call_shfr),(Proj_son,Proj_shfr)):-
    sondergaard:project(Sg,Vars,HvFv_u,Call_son,Proj_son),
    sharefree:project(Sg,Vars,HvFv_u,Call_shfr,Proj_shfr).

%-------------------------------------------------------------------------

:- redefining(compute_lub/2).
:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([ASub],ASub) :- !.
compute_lub([ASub1,ASub2|Rest],Lub) :-
    ASub1 == ASub2,!,
    compute_lub([ASub1|Rest],Lub).
compute_lub(['$bottom',ASub|Rest],Lub) :- !,
    compute_lub([ASub|Rest],Lub).
compute_lub([ASub,'$bottom'|Rest],Lub) :- !,
    compute_lub([ASub|Rest],Lub).
compute_lub([(ASub_son1,ASub_shfr1),(ASub_son2,ASub_shfr2)|Rest],Lub):-
    sondergaard:lub(ASub_son1,ASub_son2,ASub_son3),
    sharefree:compute_lub([ASub_shfr1,ASub_shfr2],ASub_shfr3),
    compute_lub([(ASub_son3,ASub_shfr3)|Rest],Lub).

%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom').
abs_sort((ASub_son,ASub_shfr),(ASub_son_s,ASub_shfr_s)):-
    sondergaard:abs_sort(ASub_son,ASub_son_s),
    sharefree:abs_sort(ASub_shfr,ASub_shfr_s).

%--------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface((Son,Shfr),Qv,ASub,Sg,MaybeCallASub):-
    sondergaard:input_user_interface(Son,Qv,ASubSon,Sg,MaybeCallASub),
    sharefree:input_user_interface(Shfr,Qv,ASubShfr,Sg,MaybeCallASub),
    compose(ASubSon,ASubShfr,Qv,ASub).

:- dom_impl(_, input_interface/4, [noq]).
input_interface(Info,Kind,(Son0,Shfr0),(Son,Shfr)):-
    % both of them already call share_input_...
    sondergaard:input_interface(Info,KindSon,Son0,Son),
    sharefree:input_interface(Info,KindShfr,Shfr0,Shfr),
    compose_kind(KindSon,KindShfr,Kind).

compose_kind(approx,approx,approx):- !.
compose_kind(_Kind0,_Kind1,perfect).

%--------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native(((_Gr,SSon),ShFr),Qv,OutFlag,ASub_user,Comps):-
    collect_singletons(SSon,Singletons),
    varset(Singletons,NonLinearVars),
    ord_subtract(Qv,NonLinearVars,LinearVars),
    sharefree:asub_to_native(ShFr,Qv,OutFlag,ASub_user0,Comps),
    if_not_nil(LinearVars,linear(LinearVars),ASub_user,ASub_user0).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                             %
% less_or_equal(ASub0,ASub1)                                     %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%
:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal(ASub0,ASub1):-
    ASub0 == ASub1.
less_or_equal((Son0,Sh0),(Son1,Sh1)):-
    sharefree:less_or_equal(Sh0,Sh1),
    sondergaard:less_or_equal(Son0,Son1).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- dom_impl(_, glb/3, [noq]).
glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

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
