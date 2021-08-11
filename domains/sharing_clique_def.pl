:- module(sharing_clique_def, [], [assertions, isomodes]).

:- doc(title, "CLIQUE-Sharing+Def domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

:- use_module(domain(sharing_clique), [
    input_interface/4
]).
:- include(ciaopp(plai/plai_domain)).
:- dom_def(share_clique_def, [default]).
:- dom_impl(_, input_interface/4, [from(sharing_clique:share_clique), noq]).

%------------------------------------------------------------------------%
% This file contains the domain dependent abstract functions for the     |
% clique-sharing domain combined with the definiteness abstract domain.  |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharing_clique.pl and      |
% def.pl                                                                 |
%------------------------------------------------------------------------% 
% This domain is represented by a pair (SH,D) where SH is the original   |
% clique-sharing domain and D is the definiteness domain.                |
% The combination of the clique-sharing domain with Def is the simplest  |
% possible. For any operation of the analysis, abstract amgu in          |
% particular, the Def component is evaluated first. All sharing groups   |
% containing at least one variable that is definitely ground according   |
% to the resulting Def formula are removed from the sharing component.   | 
% For the clique groups the intersection between the clique groups and   |
% those ground variables are removed.                                    |
%------------------------------------------------------------------------%

:- doc(bug,"1. In case of success multivariance the predicate
       eliminate_equivalent/2 must be redefined.").
:- doc(bug,"2. The following builtins: ==../2, ==/2 and copy_term/2 
       are not defined for the domain def").

%------------------------------------------------------------------------%

:- use_module(library(messages), [warning_message/1, warning_message/2]).

:- use_module(domain(def), [
    call_to_entry/9,
    call_to_success_fact/9,
    compute_lub_el/3,
    exit_to_prime/7,
    extend/5,
    glb/3,
    project/5,
    abs_sort/2,
    special_builtin/5,
    unknown_entry/3]).
:- use_module(domain(sharing_clique), [
    call_to_entry/9,
    call_to_success_fact/9,
    empty_entry/3,
    exit_to_prime/7,
    extend/5,
    glb/3,
    identical_abstract/2,
    input_user_interface/5,
    less_or_equal/2,
    project/5,
    abs_sort/2,
    special_builtin/5,
    unknown_call/4]).

:- use_module(domain(share_clique_aux), [irrel_w/3]).
:- use_module(domain(s_grshfr), [projected_gvars/3]).
:- use_module(domain(sharing_clique), [
    may_be_var/2,
    share_clique_lub_cl/3
]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- use_module(library(sets), [ord_union/3]).
:- use_module(library(sort), [sort/2]). 

%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,?)                      |
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,(BothEntry,ExtraInfo)):-
    Proj = (SH_Proj,Def_Proj),
    def:call_to_entry(Sv,Sg,Hv,Head,K,Fv,Def_Proj,Def_Entry,BothEntry),
    compose((SH_Proj,Def_Entry),NewSH_Proj),
    sharing_clique:call_to_entry(Sv,Sg,Hv,Head,K,Fv,NewSH_Proj,(Cl_Entry,Sh_Entry),ExtraInfo),
    Entry = ((Cl_Entry,Sh_Entry),Def_Entry),!.
call_to_entry(_,_,_,_,_,_,_,'$bottom',_).

%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)                          |
%------------------------------------------------------------------------%
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
exit_to_prime(Sg,Hv,Head,Sv,Exit,(BothEntry,ExtraInfo),Prime):-
    Exit = (SH_Exit,Def_Exit),
    def:exit_to_prime(Sg,Hv,Head,Sv,Def_Exit,BothEntry,Def_Prime),
    compose((SH_Exit,Def_Prime),NewSH_Exit),
    sharing_clique:exit_to_prime(Sg,Hv,Head,Sv,NewSH_Exit,ExtraInfo,(Cl_Pr,Sh_Pr)),
    Prime = ((Cl_Pr,Sh_Pr),Def_Prime),!.
exit_to_prime(_,_,_,_,_,_,'$bottom').

%------------------------------------------------------------------------%
% extend(+,+,+,+,-)                                     |
% extend(Sg,Prime,Sv,Call,Succ)                         |
%------------------------------------------------------------------------%
:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Hv,_Call,'$bottom').
extend(Sg,(SH_Prime,Def_Prime),Sv,(SH_Call,Def_Call),Succ):-
    def:extend(Sg,Def_Prime,Sv,Def_Call,Def_Succ),
    compose((SH_Prime,Def_Succ),NewSH_Prime),
    compose((SH_Call,Def_Succ),NewSH_Call),
    sharing_clique:extend(Sg,NewSH_Prime,Sv,NewSH_Call,(Cl_Succ,Sh_Succ)),
    Succ = ((Cl_Succ,Sh_Succ),Def_Succ),!.
extend(_Sg,_Prime,_Sv,_Call,'$bottom').

%------------------------------------------------------------------------%
% project(+,+,+,+,-)                                    |
% project(Sg,Vars,HvFv_u,ASub,Proj)                     |
%------------------------------------------------------------------------%
:- dom_impl(_, project/5, [noq]).
project(_,_,_,'$bottom','$bottom'):- !.
project(Sg,Vars,HvFv_u,(SH_ASub,Def_ASub),Proj) :-
    def:project(Sg,Vars,HvFv_u,Def_ASub,Def_Proj),
    sharing_clique:project(Sg,Vars,HvFv_u,SH_ASub,SH_Proj),
    Proj = (SH_Proj,Def_Proj).

%------------------------------------------------------------------------%
% abs_sort(+,-)                                             |
% abs_sort(Asub,Asub_s)                                     |
%------------------------------------------------------------------------%

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom'):- !.
abs_sort((SH_ASub,Def_ASub),ASub_s ):-
    def:abs_sort(Def_ASub,Def_ASub_s),
    sharing_clique:abs_sort(SH_ASub,SH_ASub_s),
    ASub_s = (SH_ASub_s,Def_ASub_s).

%------------------------------------------------------------------------%
% glb(+,+,-)                                            |
% glb(ASub0,ASub1,Lub)                                  |
%------------------------------------------------------------------------%

:- dom_impl(_, glb/3, [noq]).
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb((SH_ASub0,Def_ASub0),(SH_ASub1,Def_ASub1),Glb):- 
    def:glb(Def_ASub0,Def_ASub1,Def_glb),
    compose((SH_ASub0,Def_glb),NewSH_ASub0),
    compose((SH_ASub1,Def_glb),NewSH_ASub1),
    sharing_clique:glb(NewSH_ASub0,NewSH_ASub1,SH_Glb),
    Glb = (SH_Glb,Def_glb).

%------------------------------------------------------------------------%
% identical_abstract(+,+)                               |
% identical_abstract(ASub0,ASub1)                       |
%------------------------------------------------------------------------%
:- dom_impl(_, identical_abstract/2, [noq]).
identical_abstract('$bottom','$bottom'):-!.
identical_abstract((SH0,_),(SH1,_)):-!,
    sharing_clique:identical_abstract(SH0,SH1).

%------------------------------------------------------------------------%
% eliminate_equivalent(+,-)                             |
% eliminate_equivalent(TmpLSucc,LSucc)                  |
%------------------------------------------------------------------------%

:- dom_impl(_, eliminate_equivalent/2, [noq]).
eliminate_equivalent(TmpLSucc,Succ):-
    sort(TmpLSucc,Succ).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                    |
% less_or_equal(ASub0,ASub1)                            |
%------------------------------------------------------------------------%

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal('$bottom',_ASub):- !.
less_or_equal((SH0,_),(SH1,_)):-!,
    sharing_clique:less_or_equal(SH0,SH1).
            
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    Call = (SH_Call,Def_Call),
    Proj = (_,Def_Proj),
    def:call_to_success_fact(Sg,Hv,Head,K,Sv,Def_Call,Def_Proj,Def_Prime,Def_Succ),
    compose((SH_Call,Def_Succ),NewSH_Call),
    sharing_clique:call_to_success_fact(Sg,Hv,Head,K,Sv,NewSH_Call,_Proj,(Cl_Prime,Sh_Prime),(Cl_Succ,Sh_Succ)),
    Prime = ((Cl_Prime,Sh_Prime),Def_Prime),
    Succ = ((Cl_Succ,Sh_Succ),Def_Succ),!.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').


%------------------------------------------------------------------------%
% compute_lub(+,-)                                      |
% compute_lub(ListASub,Lub)                             |
%------------------------------------------------------------------------%

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([ASub1,ASub2|Rest],Lub) :-
    lub_cl(ASub1,ASub2,ASub3),
    compute_lub([ASub3|Rest],Lub).
compute_lub([ASub],ASub).

% :- dom_impl(_, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).
lub_cl('$bottom',ASub,ASub):-!.
lub_cl(ASub,'$bottom',ASub):-!.
lub_cl((SH_ASub1,Def_ASub1),(SH_ASub2,Def_ASub2),ASub3):-
    def:compute_lub_el(Def_ASub1,Def_ASub2,Def_ASub3),
    compose((SH_ASub1,Def_ASub3),NewSH_ASub1),
    compose((SH_ASub2,Def_ASub3),NewSH_ASub2),
    share_clique_lub_cl(NewSH_ASub1,NewSH_ASub2,SH_ASub3),
    ASub3 = (SH_ASub3,Def_ASub3).

%------------------------------------------------------------------------%
% input_user_interface(+,+,-,+,+)                       |
% input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub) |
%------------------------------------------------------------------------%

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface((Gv,Sh,Cl,I),Qv,Call,Sg,MaybeCallASub):-
    sharing_clique:input_user_interface((Gv,Sh,Cl,I),Qv,SH_Call,Sg,MaybeCallASub),
    may_be_var(Gv,Gv0),
    Def_Call = a(Gv0,[]),
    Call = (SH_Call,Def_Call).

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)                             |
% asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)       |
%------------------------------------------------------------------------%

% TODO: def:asub_to_native/5 is not used here (if done, ignore ground/1 from Def asub, keep only covered/2, etc.)
:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
asub_to_native(((Cl,Sh),a(G,_SS)),Qv,_OutFlag,Info,[]):-
    ord_union(Sh,Cl,All),
    projected_gvars(All,Qv,Gv),     
    if_not_nil(Cl,clique(Cl),Info,Info0),
    if_not_nil(Sh,sharing(Sh),Info0,Info1),
    if_not_nil(Gv,ground(Gv),Info1,[]),
    ( Gv == G -> true
    ; warning_message("The set of ground variables are different")
    ).
    
%------------------------------------------------------------------------%
% unknown_call(+,+,+,-)                                 |
% unknown_call(Sg,Vars,Call,Succ)                       |
% Note that def does not define this operation.                          |
%------------------------------------------------------------------------%

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,'$bottom','$bottom').
unknown_call(Sg,Vars,(SH_Call,Def_Call),Succ):-        
    sharing_clique:unknown_call(Sg,Vars,SH_Call,SH_Succ),
    Succ = (SH_Succ,Def_Call).

%------------------------------------------------------------------------%
% empty_entry(+,+,-)                                    |
% empty_entry(Sg,Vars,Entry)                            |
%------------------------------------------------------------------------%

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(Sg,Vars,Entry):-
    def:unknown_entry(Sg,Vars,Def_Entry), % TODO: why not def:empty_entry/3?
    sharing_clique:empty_entry(Sg,Vars,SH_Entry),
    Entry = (SH_Entry,Def_Entry).

%------------------------------------------------------------------------%
% unknown_entry(+,+,-)                                  |
% unknown_entry(Sg,Qv,Call)                             |
%------------------------------------------------------------------------%

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Qv,((Qv,[]),a([],[]))).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              |
%------------------------------------------------------------------------%
% special_builtin(+,+,+,-,-)                            |
% special_builtin(SgKey,Sg,Subgoal,Type,Condvars)       |
%------------------------------------------------------------------------%

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
    sharing_clique:special_builtin(SgKey,Sg,Subgoal,SH_Type,SH_Condvars),!,
    ( def:special_builtin(SgKey,Sg,Subgoal,Def_Type,Def_Condvars) ->
      Type = (SH_Type,Def_Type),
      Condvars = (SH_Condvars,Def_Condvars)
    ;
      warning_message("The builtin ~w is not defined in def",
                      [SgKey]),    
      Type = (SH_Type,not_defined),
      Condvars = (SH_Condvars,_)
    ).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [body_succ_builtin/9, body_builtin/9]).

:- dom_impl(_, body_succ_builtin/8, [noq]).
body_succ_builtin((TSH,not_defined),Sg,(CSH,_),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_SH,Call_def),
    Proj=(Proj_SH,_Proj_def),
    body_succ_builtin(share_clique,TSH,Sg,CSH,Sv,HvFv,Call_SH,Proj_SH,Succ_SH),
    Succ = (Succ_SH,Call_def).
body_succ_builtin((TSH,Tdef),Sg,(CSH,Cdef),Sv,HvFv,Call,Proj,Succ) :- !,
    Call=(Call_SH,Call_def),
    Proj=(Proj_SH,Proj_def),
    body_succ_builtin(def,Tdef,Sg,Cdef,Sv,HvFv,Call_def,Proj_def,Succ_def),
    compose((Call_SH,Succ_def),NewCall_SH),
    compose((Proj_SH,Succ_def),NewProj_SH),
    body_succ_builtin(share_clique,TSH,Sg,CSH,Sv,HvFv,NewCall_SH,NewProj_SH,Succ_SH),
    Succ = (Succ_SH,Succ_def).
body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
    body_builtin(share_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%------------------------------------------------------------------------%
% compose(+,-)                                                           
% compose(((Cl,Sh),a(G,SS)),((NewCl,NewSh),a(NewG,NewSS)))     
%------------------------------------------------------------------------%
% The clique-sharing and def domains are combined in the simplest        | 
% possible way and this is as follows:                                   |
% - All sharing groups containing at least one variable that is          |
%   definitely ground according to the resulting def formula are removed |
%   from the sharing component.                                          |
% - The intersection between every clique group and the definite ground  |
%   variables are removed too.                                           |
% Note that for any abstract function, the def component is evaluated    |
% first.                                                                 |
%------------------------------------------------------------------------%

compose(((Cl,Sh),a(G,_)),(NewCl,NewSh)):-
    irrel_w(G,(Cl,Sh),(NewCl,NewSh)),!.
compose(_,'$bottom'):-!.

