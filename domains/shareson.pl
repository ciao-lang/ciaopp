:- module(shareson, [], []).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shareson, [default]).

:- use_module(domain(sharing), [
    call_to_entry/9,
    exit_to_prime/7,
    extend/5,
    call_to_prime_fact/6,
    special_builtin/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3,
    project/5,
    lub/3, % TODO: add domain op?
    abs_sort/2,
    input_user_interface/5,
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
%                    Meaning of the Program Variables                    %
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

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(Sv,Sg,Hv,Head,K,Fv,(Proj_son,Proj_sh),Entry,ExtraInfo):-
    sondergaard:call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_son,Entry_son,ExtraInfo_son),
    sharing:call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_sh,Entry_sh,ExtraInfo_sh),
    compose(Entry_son,Entry_sh,Hv,Entry),
    ExtraInfo = (ExtraInfo_son,ExtraInfo_sh).

%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,Prime):- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,Sv,(Exit_son,Exit_sh),ExtraInfo,Prime):- 
    ExtraInfo = (ExtraInfo_son,ExtraInfo_sh),
    sharing:exit_to_prime(Sg,Hv,Head,Sv,Exit_sh,ExtraInfo_sh,Prime_sh),
    sondergaard:exit_to_prime(Sg,Hv,Head,Sv,Exit_son,ExtraInfo_son,Prime_son),
    compose(Prime_son,Prime_sh,Sv,Prime).
    
%-------------------------------------------------------------------------

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_,_,Succ):- !,Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !, Call = Succ.
extend(Sg,(Prime_son,Prime_sh),Sv,(Call_son,Call_sh),Succ):-
    sharing:extend(Sg,Prime_sh,Sv,Call_sh,Succ_sh),
    sondergaard:extend(Sg,Prime_son,Sv,Call_son,Succ_son),
    merge_list_of_lists(Call_sh,Vars),
    compose(Succ_son,Succ_sh,Vars,Succ).

%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    Proj = (Proj_son,Proj_sh),
    sondergaard:call_to_prime_fact(Sg,Hv,Head,Sv,Proj_son,Prime_son),
    sharing:call_to_prime_fact(Sg,Hv,Head,Sv,Proj_sh,Prime_sh),
    compose(Prime_son,Prime_sh,Sv,Prime),
    shareson:extend(Sg,Prime,Sv,Call,Succ).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,(TypeSon,TypeSh),(CondSon,CondSh)) :-
    sharing:special_builtin(SgKey,Sg,Subgoal,TypeSh,CondSh),
    sondergaard:special_builtin(SgKey,Sg,Subgoal,TypeSon,CondSon).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [body_succ_builtin/9, body_builtin/9]).

% TODO: These do have special(_), special care (old comment)
:- dom_impl(_, body_succ_builtin/8, [noq]).
body_succ_builtin((TSon,TSh),Sg,(CSon,CSh),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_son,Call_sh),
    Proj=(Proj_son,Proj_sh),
    body_succ_builtin(son,TSon,Sg,CSon,Sv,HvFv,Call_son,Proj_son,Succ_son),
    body_succ_builtin(share,TSh,Sg,CSh,Sv,HvFv,Call_sh,Proj_sh,Succ_sh),
    merge_list_of_lists(Call_sh,Vars),
    compose(Succ_son,Succ_sh,Vars,Succ).
body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
    body_builtin(shareson,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
unknown_call(Sg,Vars,(Call_son,Call_sh),Succ):-
    sharing:unknown_call(Sg,Vars,Call_sh,Succ_sh),
    sondergaard:unknown_call(Sg,Vars,Call_son,Succ_son),
    merge_list_of_lists(Call_sh,AllVars),
    compose(Succ_son,Succ_sh,AllVars,Succ).

%-------------------------------------------------------------------------

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(Sg,Qv,Call):-
    sharing:unknown_entry(Sg,Qv,Call_sh),
    sondergaard:unknown_entry(Sg,Qv,Call_son),
    compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(Sg,Qv,Call):-
    sharing:empty_entry(Sg,Qv,Call_sh),
    sondergaard:empty_entry(Sg,Qv,Call_son),
    compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

:- dom_impl(_, project/5, [noq]).
project(_Sg,_Vars,_HvFv_u,'$bottom',Proj):- !,
    Proj = '$bottom'.
project(_Sg,[],_HvFv_u,_,Proj):- !,
    Proj = (([],[]),[]).
project(Sg,Vars,HvFv_u,(Call_son,Call_sh),(Proj_son,Proj_sh)):-
    sondergaard:project(Sg,Vars,HvFv_u,Call_son,Proj_son),
    sharing:project(Sg,Vars,HvFv_u,Call_sh,Proj_sh).

%-------------------------------------------------------------------------

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([ASub1,ASub2|Rest],Lub) :-
    ASub1 == ASub2,!,
    compute_lub([ASub1|Rest],Lub).
compute_lub(['$bottom',ASub|Rest],Lub) :- !,
    compute_lub([ASub|Rest],Lub).
compute_lub([ASub,'$bottom'|Rest],Lub) :- !,
    compute_lub([ASub|Rest],Lub).
compute_lub([(ASub_son1,ASub_sh1),(ASub_son2,ASub_sh2)|Rest],Lub) :-
    sondergaard:lub(ASub_son1,ASub_son2,ASub_son3),
    sharing:lub(ASub_sh1,ASub_sh2,ASub_sh3),
    compute_lub([(ASub_son3,ASub_sh3)|Rest],Lub).
compute_lub([ASub],ASub).

%---------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom').
abs_sort((ASub_son,ASub_sh),(ASub_son_s,ASub_sh_s)):-
    sondergaard:abs_sort(ASub_son,ASub_son_s),
    sharing:abs_sort(ASub_sh,ASub_sh_s).

%--------------------------------------------------------------------------

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface(Struct,Qv,(Son,Sh),Sg,MaybeCallASub):-
    Struct = (Sharing,_Lin),
    sondergaard:input_user_interface(Struct,Qv,Son,Sg,MaybeCallASub),
    sharing:input_user_interface(Sharing,Qv,Sh,Sg,MaybeCallASub).

:- dom_impl(_, input_interface/4, [noq]).
input_interface(Info,Kind,Struct0,Struct):-
    % already calls sharing:input_...
    sondergaard:input_interface(Info,Kind,Struct0,Struct).

%--------------------------------------------------------------------------

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native(((Gr,SSon),Sh),Qv,_OutFlag,ASub_user,[]):-
    collect_singletons(SSon,Singletons),
    varset(Singletons,NonLinearVars),
    ord_subtract(Qv,NonLinearVars,LinearVars),
    if_not_nil(Gr,ground(Gr),ASub_user,ASub_user0),
    if_not_nil(LinearVars,linear(LinearVars),ASub_user0,ASub_user1),
    if_not_nil(Sh,sharing(Sh),ASub_user1,[]).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                            %
% less_or_equal(ASub0,ASub1)                                    %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal(ASub0,ASub1):-
    ASub0 == ASub1.
less_or_equal((Son0,Sh0),(Son1,Sh1)):-
    sharing:less_or_equal(Sh0,Sh1),
    sondergaard:less_or_equal(Son0,Son1).

%-------------------------------------------------------------------------

:- dom_impl(_, glb/3, [noq]).
glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

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
