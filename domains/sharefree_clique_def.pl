:- module(sharefree_clique_def, [], [assertions, isomodes]).

:- doc(title, "CLIQUE-Sharing+Freeness+Def domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

:- include(ciaopp(plai/plai_domain)).
:- dom_def(sharefree_clique_def, [default]).
:- dom_impl(_, input_interface/4, [from(sharefree_clique), noq]).

%------------------------------------------------------------------------%
% This file contains the domain dependent abstract functions for the     |
% clique-sharing+Freeness domain combined with the definiteness abstract | 
% domain.                                                                |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharing_clique.pl and      |
% def.pl                                                                 |
%------------------------------------------------------------------------% 
% This domain is represented by a pair (SHF,D) where SHF is the original |
% clique-sharing+freeness domain and D is the definiteness domain.       |
% The combination of the clique-sharing+freeness domain with Def is the  |
% simplest possible. For any operation of the analysis, abstract amgu in |
% particular, the Def component is evaluated first. All sharing groups   |
% containing at least one variable that is definitely ground according   |
% to the resulting Def formula are removed from the sharing component.   | 
% For the clique groups the intersection between the clique groups and   |
% those ground variables are removed.                                    |
%------------------------------------------------------------------------%

:- doc(bug,"1. In case of success multivariance the predicate
       eliminate_equivalent/2 must be redefined.").
:- doc(bug,"2. The following builtins: =../2, ==/2 and copy_term/2 
       are not defined for the domain def").

%------------------------------------------------------------------------%

:- use_module(library(sort), [sort/2]). 

:- use_module(domain(s_grshfr), [
    member_value_freeness/3,
    change_values_insert/4,
    create_values/3]).
:- use_module(domain(share_clique_aux), [irrel_w/3]).
:- use_module(domain(share_aux), [
    eliminate_couples/4,
    handle_each_indep/4,
    eliminate_if_not_possible/3,
    test_temp/2,
    if_not_nil/4,
    eliminate_if_not_possible/4]).

:- use_module(domain(sharefree_clique), [
    call_to_entry/9,
    exit_to_prime/7,
    extend/5,
    project/5,
    abs_sort/2,
    glb/3,
    identical_abstract/2,
    less_or_equal/2,
    call_to_success_fact/9,
    compute_lub_el/3,
    input_interface/4,
    input_user_interface/5,
    unknown_call/4,
    empty_entry/3,
    special_builtin/5
]).
:- use_module(domain(def), [
    call_to_entry/9,
    exit_to_prime/7,
    extend/5,
    project/5,
    abs_sort/2,
    glb/3,
    call_to_success_fact/9,
    compute_lub_el/3,
    unknown_entry/3,
    special_builtin/5
]).

:- use_module(library(messages), [warning_message/1, warning_message/2]).

%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,?)                  |
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,(BothEntry,ExtraInfo)):-
    Proj = (SHF_Proj,Def_Proj),
    def:call_to_entry(Sv,Sg,Hv,Head,K,Fv,Def_Proj,Def_entry,BothEntry),
    compose(SHF_Proj,Def_entry,NewSHF_Proj),
    sharefree_clique:call_to_entry(Sv,Sg,Hv,Head,K,Fv,NewSHF_Proj,(SH_Entry,Fr_Entry),ExtraInfo),
    Entry = ((SH_Entry,Fr_Entry),Def_entry),!.
call_to_entry(_,_,_,_,_,_,_,'$bottom',_):- !.

%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)                      |
%------------------------------------------------------------------------%
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
exit_to_prime(Sg,Hv,Head,Sv,Exit,(BothEntry,ExtraInfo),Prime):-!,
    Exit = (SHF_Exit,Def_Exit),
    def:exit_to_prime(Sg,Hv,Head,Sv,Def_Exit,BothEntry,Def_prime),
    compose(SHF_Exit,Def_prime,NewSHF_Exit),
    sharefree_clique:exit_to_prime(Sg,Hv,Head,Sv,NewSHF_Exit,ExtraInfo,(SH_Pr,Fr_Pr)),
    Prime = ((SH_Pr,Fr_Pr),Def_prime).

%------------------------------------------------------------------------%
% extend(+,+,+,+,-)                                 |
% extend(Sg,Prime,Sv,Call,Succ)                     |
%------------------------------------------------------------------------%
:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Hv,_Call,'$bottom') :- !.
extend(Sg,(SHF_Prime,Def_Prime),Sv,(SHF_Call,Def_Call),Succ):-
    def:extend(Sg,Def_Prime,Sv,Def_Call,Def_succ),
    compose(SHF_Prime,Def_succ,NewSHF_Prime),
    compose(SHF_Call,Def_succ,NewSHF_Call),
    sharefree_clique:extend(Sg,NewSHF_Prime,Sv,NewSHF_Call,(SH_Succ,Fr_Succ)),
    Succ = ((SH_Succ,Fr_Succ),Def_succ),!.

%------------------------------------------------------------------------%
% project(+,+,+,+,-)                                |
% project(Sg,Vars,HvFv_u,ASub,Proj)                 |
%------------------------------------------------------------------------%
:- dom_impl(_, project/5, [noq]).
project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
project(Sg,Vars,HvFv_u,(SHF_ASub,Def_ASub),Proj) :-
    def:project(Sg,Vars,HvFv_u,Def_ASub,Def_Proj),
    sharefree_clique:project(Sg,Vars,HvFv_u,SHF_ASub,SHF_Proj),
    Proj = (SHF_Proj,Def_Proj).

%------------------------------------------------------------------------%
% abs_sort(+,-)                                         |
% abs_sort(Asub,Asub_s)                                 |
%------------------------------------------------------------------------%

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom'):- !.
abs_sort((SHF_ASub,Def_ASub),ASub_s ):-
    def:abs_sort(Def_ASub,Def_ASub_s),
    sharefree_clique:abs_sort(SHF_ASub,SHF_ASub_s),
    ASub_s = (SHF_ASub_s,Def_ASub_s).


%------------------------------------------------------------------------%
% glb(+,+,-)                                        |
% glb(ASub0,ASub1,Lub)                              |
%------------------------------------------------------------------------%

:- dom_impl(_, glb/3, [noq]).
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb((SHF_ASub0,Def_ASub0),(SHF_ASub1,Def_ASub1),Lub):- 
    def:glb(Def_ASub0,Def_ASub1,Def_lub),
    compose(SHF_ASub0,Def_lub,NewSHF_ASub0),
    compose(SHF_ASub1,Def_lub,NewSHF_ASub1),
    sharefree_clique:glb(NewSHF_ASub0,NewSHF_ASub1,SHF_lub),
    Lub = (SHF_lub,Def_lub),!.

%------------------------------------------------------------------------%
% identical_abstract(+,+)                           |
% identical_abstract(ASub0,ASub1)                   |
%------------------------------------------------------------------------%
:- dom_impl(_, identical_abstract/2, [noq]).
identical_abstract('$bottom','$bottom'):-!.
identical_abstract((SHF0,_),(SHF1,_)):-!,
    sharefree_clique:identical_abstract(SHF0,SHF1).

%------------------------------------------------------------------------%
% eliminate_equivalent(+,-)                         |
% eliminate_equivalent(TmpLSucc,LSucc)              |
%------------------------------------------------------------------------%
:- dom_impl(_, eliminate_equivalent/2, [noq]).
eliminate_equivalent(TmpLSucc,Succ):-
    sort(TmpLSucc,Succ).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                |
% less_or_equal(ASub0,ASub1)                        |
%------------------------------------------------------------------------%
:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal('$bottom',_ASub):- !.
less_or_equal((SHF0,_),(SHF1,_)):-!,
    sharefree_clique:less_or_equal(SHF0,SHF1).
            
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    Call = (SHF_Call,Def_Call),
    Proj = (_,Def_Proj),
    def:call_to_success_fact(Sg,Hv,Head,K,Sv,Def_Call,Def_Proj,Def_Prime,Def_succ),
    compose(SHF_Call,Def_succ,NewSHF_Call),
    sharefree_clique:call_to_success_fact(Sg,Hv,Head,K,Sv,NewSHF_Call,_Proj,(SH_Prime,Fr_Prime),(SH_Succ,Fr_Succ)),
    Prime = ((SH_Prime,Fr_Prime),Def_Prime),
    Succ = ((SH_Succ,Fr_Succ),Def_succ),!.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom'):- !.

%------------------------------------------------------------------------%
% compute_lub(+,-)                                  |
% compute_lub(ListASub,Lub)                         |
%------------------------------------------------------------------------%
:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([ASub1,ASub2|Rest],Lub) :- !,
    lub_cl(ASub1,ASub2,ASub3),
    compute_lub([ASub3|Rest],Lub).
compute_lub([ASub],ASub).

% :- dom_impl(_, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub), [noq]).
lub_cl('$bottom',ASub,ASub):-!.
lub_cl(ASub,'$bottom',ASub):-!.
lub_cl((SHF_ASub1,Def_ASub1),(SHF_ASub2,Def_ASub2),Lub):-
    def:compute_lub_el(Def_ASub1,Def_ASub2,Def_lub),
    compose(SHF_ASub1,Def_lub,NewSHF_ASub1),
    compose(SHF_ASub2,Def_lub,NewSHF_ASub2),
    sharefree_clique:compute_lub_el(NewSHF_ASub1,NewSHF_ASub2,SHF_lub),
    Lub = (SHF_lub,Def_lub),!.

%------------------------------------------------------------------------%
% input_user_interface(+,+,-,+,+)                   |
% input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub) |
%------------------------------------------------------------------------%
:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface((SH,Fv),Qv,Call,Sg,MaybeCallASub):-
    sharefree_clique:input_user_interface((SH,Fv),Qv,(SH_call,Fr_call),Sg,MaybeCallASub),
    member_value_freeness(Fr_call,Gv,g),
    Def_call = a(Gv,[]),
    Call = ((SH_call,Fr_call),Def_call).

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)                         |
% asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)   |
%------------------------------------------------------------------------%

% TODO: def:asub_to_native/5 is not used here (if done, ignore ground/1 from Def asub, keep only covered/2, etc.)
:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
asub_to_native(((SH,Fr),a(_G,_SS)),_Qv,_OutFlag,Info,[]):-!,
    SH = (Cl,Sh),
    if_not_nil(Cl,clique(Cl),Info,Info0),
    if_not_nil(Sh,sharing(Sh),Info0,Info1),
    member_value_freeness(Fr,Fv,f),
    if_not_nil(Fv,free(Fv),Info1,Info2),
    member_value_freeness(Fr,Gv,g),
    if_not_nil(Gv,ground(Gv),Info2,[]).
%         ( Gv == G -> true
%         ; warning_message("The set of ground variables are different")).
    
%------------------------------------------------------------------------%
% unknown_call(+,+,+,-)                             |
% unknown_call(Sg,Vars,Call,Succ)                   |
% Note that def does not define this operation.                          |
%------------------------------------------------------------------------%

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
unknown_call(Sg,Vars,(SHF_Call,Def_Call),Succ):-   
    sharefree_clique:unknown_call(Sg,Vars,SHF_Call,SHF_Succ),
    Succ = (SHF_Succ,Def_Call).

%------------------------------------------------------------------------%
% empty_entry(+,+,-)                                |
% empty_entry(Sg,Vars,Entry)                        |
%------------------------------------------------------------------------%

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(Sg,Vars,Entry):-
    def:unknown_entry(Sg,Vars,Def_Entry),
    sharefree_clique:empty_entry(Sg,Vars,SHF_Entry),
    Entry = (SHF_Entry,Def_Entry).

%------------------------------------------------------------------------%
% unknown_entry(+,+,-)                              |
% unknown_entry(Sg,Qv,Call)                         |
%------------------------------------------------------------------------%
:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Qv,(SHF_Call,a([],[]))):-
    sort(Qv,QvS),
    create_values(Qv,Call_fr,nf),
    SHF_Call = (([QvS],[]),Call_fr).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              |
%------------------------------------------------------------------------%
% special_builtin(+,+,+,-,-)                        |
% special_builtin(SgKey,Sg,Subgoal,Type,Condvars)   |
%------------------------------------------------------------------------%
:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
    sharefree_clique:special_builtin(SgKey,Sg,Subgoal,SHF_Type,SHF_Condvars),!,
    ( def:special_builtin(SgKey,Sg,Subgoal,Def_Type,Def_Condvars) ->
      Type = (SHF_Type,Def_Type),
      Condvars = (SHF_Condvars,Def_Condvars)
    ;
      warning_message("The builtin ~w is not defined in def",
                      [SgKey]),    
      Type = (SHF_Type,not_defined),
      Condvars = (SHF_Condvars,_)
    ).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [body_succ_builtin/9, body_builtin/9]).

:- dom_impl(_, body_succ_builtin/8, [noq]).
body_succ_builtin((TSHF,not_defined),Sg,(CSHF,_),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_SHF,Call_def),
    Proj=(Proj_SHF,_Proj_def),
    body_succ_builtin(sharefree_clique,TSHF,Sg,CSHF,Sv,HvFv,Call_SHF,Proj_SHF,Succ_SHF),
    Succ = (Succ_SHF,Call_def).
body_succ_builtin((TSHF,Tdef),Sg,(CSHF,Cdef),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_SHF,Call_def),
    Proj=(Proj_SHF,Proj_def),
    body_succ_builtin(def,Tdef,Sg,Cdef,Sv,HvFv,Call_def,Proj_def,Def_succ),
    compose(Call_SHF,Def_succ,NewCall_SHF),
    compose(Proj_SHF,Def_succ,NewProj_SHF),
    body_succ_builtin(sharefree_clique,TSHF,Sg,CSHF,Sv,HvFv,NewCall_SHF,NewProj_SHF,Succ_SHF),
    unify_asub_if_bottom((Succ_SHF,Def_succ),Succ),!.
body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
    body_builtin(sharefree_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%------------------------------------------------------------------------%
% compose(+,-)                                      | 
% compose(SHF,Gv,New_SHF)                           |
%------------------------------------------------------------------------%
compose('$bottom',_,'$bottom'):- !.
compose(SHF,'$bottom',SHF):- !.
compose(SHF,a(Gv,_),((NewCl,NewSh),Newfr)):-!,
    SHF = ((Cl,Sh),Fr),
    irrel_w(Gv,(Cl,Sh),(NewCl,NewSh)),
    change_values_insert(Gv,Fr,Newfr,g).

unify_asub_if_bottom(('$bottom',_Def),'$bottom'):-!.
unify_asub_if_bottom(ASub,ASub):-!.

