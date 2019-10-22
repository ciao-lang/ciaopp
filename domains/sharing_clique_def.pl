:- module(sharing_clique_def, [], [assertions, isomodes]).

:- doc(title, "CLIQUE-Sharing+Def domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

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
	def_call_to_entry/9,
	def_call_to_success_fact/9,
	def_compute_lub_el/3,
	def_exit_to_prime/7,
	def_extend/5,
	def_glb/3,
	def_project/5,
	def_abs_sort/2,
	def_special_builtin/5,
	def_unknown_entry/3]).
:- use_module(domain(sharing_clique), [
	share_clique_call_to_entry/9,
	share_clique_call_to_success_fact/9,
	share_clique_empty_entry/3,
	share_clique_exit_to_prime/7,
	share_clique_extend/5,
	share_clique_glb/3,
	share_clique_identical_abstract/2,
	share_clique_input_user_interface/5,
	share_clique_less_or_equal/2,
	share_clique_lub_cl/3,
	share_clique_project/5,
	share_clique_abs_sort/2,
	share_clique_special_builtin/5,
	share_clique_unknown_call/4]).

:- use_module(domain(share_clique_aux), [irrel_w/3]).
:- use_module(domain(s_grshfr), [projected_gvars/3]).
:- use_module(domain(sharing_clique), [may_be_var/2]).
:- use_module(domain(share_aux), [if_not_nil/4]).

:- use_module(library(sets), [ord_union/3]).
:- use_module(library(sort), [sort/2]).	

%------------------------------------------------------------------------%
% share_clique_def_call_to_entry(+,+,+,+,+,+,+,-,?)                      |
%------------------------------------------------------------------------%
:- export(share_clique_def_call_to_entry/9).
share_clique_def_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,(BothEntry,ExtraInfo)):-
	Proj = (SH_Proj,Def_Proj),
	def_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Def_Proj,Def_Entry,BothEntry),
	share_clique_def_compose((SH_Proj,Def_Entry),NewSH_Proj),
	share_clique_call_to_entry(Sv,Sg,Hv,Head,K,Fv,NewSH_Proj,(Cl_Entry,Sh_Entry),ExtraInfo),
	Entry = ((Cl_Entry,Sh_Entry),Def_Entry),!.
share_clique_def_call_to_entry(_,_,_,_,_,_,_,'$bottom',_).

%------------------------------------------------------------------------%
% share_clique_def_exit_to_prime(+,+,+,+,+,-,-)                          |
%------------------------------------------------------------------------%
:- export(share_clique_def_exit_to_prime/7).
share_clique_def_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
share_clique_def_exit_to_prime(Sg,Hv,Head,Sv,Exit,(BothEntry,ExtraInfo),Prime):-
	Exit = (SH_Exit,Def_Exit),
	def_exit_to_prime(Sg,Hv,Head,Sv,Def_Exit,BothEntry,Def_Prime),
	share_clique_def_compose((SH_Exit,Def_Prime),NewSH_Exit),
	share_clique_exit_to_prime(Sg,Hv,Head,Sv,NewSH_Exit,ExtraInfo,(Cl_Pr,Sh_Pr)),
	Prime = ((Cl_Pr,Sh_Pr),Def_Prime),!.
share_clique_def_exit_to_prime(_,_,_,_,_,_,'$bottom').

%------------------------------------------------------------------------%
% share_clique_def_extend(+,+,+,+,-)                                     |
% share_clique_def_extend(Sg,Prime,Sv,Call,Succ)                         |
%------------------------------------------------------------------------%
:- export(share_clique_def_extend/5).
share_clique_def_extend(_Sg,'$bottom',_Hv,_Call,'$bottom').
share_clique_def_extend(Sg,(SH_Prime,Def_Prime),Sv,(SH_Call,Def_Call),Succ):-
	def_extend(Sg,Def_Prime,Sv,Def_Call,Def_Succ),
	share_clique_def_compose((SH_Prime,Def_Succ),NewSH_Prime),
	share_clique_def_compose((SH_Call,Def_Succ),NewSH_Call),
        share_clique_extend(Sg,NewSH_Prime,Sv,NewSH_Call,(Cl_Succ,Sh_Succ)),
	Succ = ((Cl_Succ,Sh_Succ),Def_Succ),!.
share_clique_def_extend(_Sg,_Prime,_Sv,_Call,'$bottom').

%------------------------------------------------------------------------%
% share_clique_def_project(+,+,+,+,-)                                    |
% share_clique_def_project(Sg,Vars,HvFv_u,ASub,Proj)                     |
%------------------------------------------------------------------------%
:- export(share_clique_def_project/5).
share_clique_def_project(_,_,_,'$bottom','$bottom'):- !.
share_clique_def_project(Sg,Vars,HvFv_u,(SH_ASub,Def_ASub),Proj) :-
	def_project(Sg,Vars,HvFv_u,Def_ASub,Def_Proj),
	share_clique_project(Sg,Vars,HvFv_u,SH_ASub,SH_Proj),
	Proj = (SH_Proj,Def_Proj).

%------------------------------------------------------------------------%
% share_clique_def_abs_sort(+,-)                                             |
% share_clique_def_abs_sort(Asub,Asub_s)                                     |
%------------------------------------------------------------------------%

:- export(share_clique_def_abs_sort/2).
share_clique_def_abs_sort('$bottom','$bottom'):- !.
share_clique_def_abs_sort((SH_ASub,Def_ASub),ASub_s ):-
	def_abs_sort(Def_ASub,Def_ASub_s),
	share_clique_abs_sort(SH_ASub,SH_ASub_s),
	ASub_s = (SH_ASub_s,Def_ASub_s).

%------------------------------------------------------------------------%
% share_clique_def_glb(+,+,-)                                            |
% share_clique_def_glb(ASub0,ASub1,Lub)                                  |
%------------------------------------------------------------------------%

:- export(share_clique_def_glb/3).
share_clique_def_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
share_clique_def_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
share_clique_def_glb((SH_ASub0,Def_ASub0),(SH_ASub1,Def_ASub1),Glb):- 
	def_glb(Def_ASub0,Def_ASub1,Def_glb),
	share_clique_def_compose((SH_ASub0,Def_glb),NewSH_ASub0),
	share_clique_def_compose((SH_ASub1,Def_glb),NewSH_ASub1),
	share_clique_glb(NewSH_ASub0,NewSH_ASub1,SH_Glb),
	Glb = (SH_Glb,Def_glb).

%------------------------------------------------------------------------%
% share_clique_def_identical_abstract(+,+)                               |
% share_clique_def_identical_abstract(ASub0,ASub1)                       |
%------------------------------------------------------------------------%
:- export(share_clique_def_identical_abstract/2).
share_clique_def_identical_abstract('$bottom','$bottom'):-!.
share_clique_def_identical_abstract((SH0,_),(SH1,_)):-!,
	share_clique_identical_abstract(SH0,SH1).

%------------------------------------------------------------------------%
% share_clique_def_eliminate_equivalent(+,-)                             |
% share_clique_def_eliminate_equivalent(TmpLSucc,LSucc)                  |
%------------------------------------------------------------------------%

:- export(share_clique_def_eliminate_equivalent/2).
share_clique_def_eliminate_equivalent(TmpLSucc,Succ):-
	sort(TmpLSucc,Succ).

%------------------------------------------------------------------------%
% share_clique_def_less_or_equal(+,+)                                    |
% share_clique_def_less_or_equal(ASub0,ASub1)                            |
%------------------------------------------------------------------------%

:- export(share_clique_def_less_or_equal/2).
share_clique_def_less_or_equal('$bottom',_ASub):- !.
share_clique_def_less_or_equal((SH0,_),(SH1,_)):-!,
	share_clique_less_or_equal(SH0,SH1).
		
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%

:- export(share_clique_def_call_to_success_fact/9).
share_clique_def_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
	Call = (SH_Call,Def_Call),
	Proj = (_,Def_Proj),
	def_call_to_success_fact(Sg,Hv,Head,K,Sv,Def_Call,Def_Proj,Def_Prime,Def_Succ),
	share_clique_def_compose((SH_Call,Def_Succ),NewSH_Call),
	share_clique_call_to_success_fact(Sg,Hv,Head,K,Sv,NewSH_Call,_Proj,(Cl_Prime,Sh_Prime),(Cl_Succ,Sh_Succ)),
	Prime = ((Cl_Prime,Sh_Prime),Def_Prime),
	Succ = ((Cl_Succ,Sh_Succ),Def_Succ),!.
share_clique_def_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').


%------------------------------------------------------------------------%
% share_clique_def_compute_lub(+,-)                                      |
% share_clique_def_compute_lub(ListASub,Lub)                             |
%------------------------------------------------------------------------%

:- export(share_clique_def_compute_lub/2).
share_clique_def_compute_lub([ASub1,ASub2|Rest],Lub) :-
	share_clique_def_lub_cl(ASub1,ASub2,ASub3),
	share_clique_def_compute_lub([ASub3|Rest],Lub).
share_clique_def_compute_lub([ASub],ASub).

:- export(share_clique_def_lub_cl/3).
share_clique_def_lub_cl('$bottom',ASub,ASub):-!.
share_clique_def_lub_cl(ASub,'$bottom',ASub):-!.
share_clique_def_lub_cl((SH_ASub1,Def_ASub1),(SH_ASub2,Def_ASub2),ASub3):-
	def_compute_lub_el(Def_ASub1,Def_ASub2,Def_ASub3),
	share_clique_def_compose((SH_ASub1,Def_ASub3),NewSH_ASub1),
	share_clique_def_compose((SH_ASub2,Def_ASub3),NewSH_ASub2),
	share_clique_lub_cl(NewSH_ASub1,NewSH_ASub2,SH_ASub3),
	ASub3 = (SH_ASub3,Def_ASub3).
%------------------------------------------------------------------------%
% share_clique_def_input_user_interface(+,+,-,+,+)                       |
% share_clique_def_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub) |
%------------------------------------------------------------------------%

:- export(share_clique_def_input_user_interface/5).
share_clique_def_input_user_interface((Gv,Sh,Cl,I),Qv,Call,Sg,MaybeCallASub):-
	share_clique_input_user_interface((Gv,Sh,Cl,I),Qv,SH_Call,Sg,MaybeCallASub),
	may_be_var(Gv,Gv0),
	Def_Call = a(Gv0,[]),
	Call = (SH_Call,Def_Call).

%------------------------------------------------------------------------%
% share_clique_def_asub_to_native(+,+,+,-,-)                             |
% share_clique_def_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)       |
%------------------------------------------------------------------------%

:- export(share_clique_def_asub_to_native/5).
share_clique_def_asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
share_clique_def_asub_to_native(((Cl,Sh),a(G,_SS)),Qv,_OutFlag,Info,[]):-
 	ord_union(Sh,Cl,All),
	projected_gvars(All,Qv,Gv),	
	if_not_nil(Cl,clique(Cl),Info,Info0),
	if_not_nil(Sh,sharing(Sh),Info0,Info1),
	if_not_nil(Gv,ground(Gv),Info1,[]),
        ( Gv == G -> true
        ; warning_message("The set of ground variables are different")
	).
	
%------------------------------------------------------------------------%
% share_clique_def_unknown_call(+,+,+,-)                                 |
% share_clique_def_unknown_call(Sg,Vars,Call,Succ)                       |
% Note that def does not define this operation.                          |
%------------------------------------------------------------------------%

:- export(share_clique_def_unknown_call/4).
share_clique_def_unknown_call(_Sg,_Vars,'$bottom','$bottom').
share_clique_def_unknown_call(Sg,Vars,(SH_Call,Def_Call),Succ):-	
	share_clique_unknown_call(Sg,Vars,SH_Call,SH_Succ),
	Succ = (SH_Succ,Def_Call).

%------------------------------------------------------------------------%
% share_clique_def_empty_entry(+,+,-)                                    |
% share_clique_def_empty_entry(Sg,Vars,Entry)                            |
%------------------------------------------------------------------------%

:- export(share_clique_def_empty_entry/3).
share_clique_def_empty_entry(Sg,Vars,Entry):-
	def_unknown_entry(Sg,Vars,Def_Entry), % TODO: why not def_empty_entry/3?
	share_clique_empty_entry(Sg,Vars,SH_Entry),
	Entry = (SH_Entry,Def_Entry).

%------------------------------------------------------------------------%
% share_clique_def_unknown_entry(+,+,-)                                  |
% share_clique_def_unknown_entry(Sg,Qv,Call)                             |
%------------------------------------------------------------------------%

:- export(share_clique_def_unknown_entry/3).
share_clique_def_unknown_entry(_Sg,Qv,((Qv,[]),a([],[]))).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              |
%------------------------------------------------------------------------%
% share_clique_def_special_builtin(+,+,+,-,-)                            |
% share_clique_def_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)       |
%------------------------------------------------------------------------%

:- export(share_clique_def_special_builtin/5).
share_clique_def_special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
	share_clique_special_builtin(SgKey,Sg,Subgoal,SH_Type,SH_Condvars),!,
	( def_special_builtin(SgKey,Sg,Subgoal,Def_Type,Def_Condvars) ->
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

:- export(share_clique_def_body_succ_builtin/8).
share_clique_def_body_succ_builtin((TSH,not_defined),Sg,(CSH,_),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_SH,Call_def),
	Proj=(Proj_SH,_Proj_def),
	body_succ_builtin(share_clique,TSH,Sg,CSH,Sv,HvFv,Call_SH,Proj_SH,Succ_SH),
	Succ = (Succ_SH,Call_def).
share_clique_def_body_succ_builtin((TSH,Tdef),Sg,(CSH,Cdef),Sv,HvFv,Call,Proj,Succ) :- !,
	Call=(Call_SH,Call_def),
	Proj=(Proj_SH,Proj_def),
	body_succ_builtin(def,Tdef,Sg,Cdef,Sv,HvFv,Call_def,Proj_def,Succ_def),
	share_clique_def_compose((Call_SH,Succ_def),NewCall_SH),
	share_clique_def_compose((Proj_SH,Succ_def),NewProj_SH),
	body_succ_builtin(share_clique,TSH,Sg,CSH,Sv,HvFv,NewCall_SH,NewProj_SH,Succ_SH),
	Succ = (Succ_SH,Succ_def).
share_clique_def_body_succ_builtin(Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ) :- % TODO: for \+Type=(_,_), is it OK?
	body_builtin(share_clique_def,Type,Sg,Condvs,Sv,HvFv_u,Call,Proj,Succ).

%------------------------------------------------------------------------%
% share_clique_def_compose(+,-)                                                           
% share_clique_def_compose(((Cl,Sh),a(G,SS)),((NewCl,NewSh),a(NewG,NewSS)))     
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

:- export(share_clique_def_compose/2).
share_clique_def_compose(((Cl,Sh),a(G,_)),(NewCl,NewSh)):-
	irrel_w(G,(Cl,Sh),(NewCl,NewSh)),!.
share_clique_def_compose(_,'$bottom'):-!.

