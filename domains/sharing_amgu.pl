:- module(sharing_amgu, [], [assertions, isomodes]).

:- doc(title, "amgu-based sharing domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the same functions than sharing.pl but the        |
% functions call_to_entry and exit_to_prime are developed based on the   |
% amgu.                                                                  |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Non-Redundant: the non-redundant version is not working because the    |
% semantics of the builtins must be redefined.                           |
%------------------------------------------------------------------------
% The meaning of the variables are defined in sharing.pl                 |
%------------------------------------------------------------------------%

:- doc(bug,"1. The builtin ==/2 is defined but it is not used. For 
	   its use, comment it out in special_builtin.").
:- doc(bug,"2. The builtins read/2 and length/2 are used in a simple
	   way. In order to use more complex definitions, comment it in 
	   special_builtin.").
:- doc(bug,"3. The non-redundant version is not working because the 
	   semantics of the builtins has not been defined yet.").

:- use_module(library(terms_vars),     [varset/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(library(sets)).
:- use_module(library(lsets)).
:- use_module(domain(s_grshfr),        [projected_gvars/3]).
:- use_module(domain(share_amgu_sets), [delete_vars_from_list_of_lists/3]).

:- use_module(library(lists), [list_to_list_of_lists/2, append/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(domain(sharing)).
:- use_module(domain(share_amgu_aux)).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_amgu_call_to_entry(+,+,+,+,+,+,+,-,?)                            %
%-------------------------------------------------------------------------
:- export(share_amgu_call_to_entry/9).
share_amgu_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
     variant(Sg,Head),!,
     ExtraInfo = yes,
     copy_term((Sg,Proj),(NewSg,NewProj)),
     Head = NewSg,
     share_abs_sort(NewProj,Temp),
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp,Entry).
share_amgu_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,ExtraInfo):- !,
     ExtraInfo = no,
     list_to_list_of_lists(Fv,Entry).
share_amgu_call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
     projected_gvars(Proj,Sv,Gv_Call),
     share_amgu_augment_asub(Proj,Hv,ASub),     
     peel_equations(Sg,Head,Eqs),
     share_amgu_iterate(Eqs,star,ASub,Result),
     share_project(Hv,Result,Entry0),
     share_amgu_augment_asub(Entry0,Fv,Entry),
     ExtraInfo = (Eqs,Gv_Call),!.
share_amgu_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).


%------------------------------------------------------------------------%
%                            ABSTRACT Iterate                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_amgu_iterate(+,+,+,-)                                            %
% share_amgu_iterate(Eqs,Flag,ASub0,ASub)                                %
% For each equation in Eqs, it performs the amgu.                        %
%------------------------------------------------------------------------%

:- export(share_amgu_iterate/4).
share_amgu_iterate([],_,ASub, ASub).
share_amgu_iterate([(X,Ts)|Eqs],Flag,ASub, ASub2):-
     amgu(X,Ts,Flag,ASub,ASub1),
     share_amgu_iterate(Eqs,Flag,ASub1, ASub2).

%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_amgu_amgu(+,+,+,-)                                               %
% share_amgu_amgu(Sg,Head,ASub,AMGU)                                     %
% @var{AMGU} is the abstract unification between @var{Sg} and @var{Head}.%
%------------------------------------------------------------------------%
:- export(share_amgu_amgu/4).
share_amgu_amgu(Sg,Head,ASub,AMGU):-
	peel_equations(Sg,Head,Eqs),
	share_amgu_iterate(Eqs,star,ASub,AMGU),!.

%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_amgu_augment_asub(+,+,-)                                          %
%-------------------------------------------------------------------------

:- export(share_amgu_augment_asub/3).
share_amgu_augment_asub(ASub,[],ASub).
share_amgu_augment_asub(ASub,Vars,ASub1):-
	share_abs_sort(ASub,SASub),
	sort(Vars,SVars),
	share_amgu_augment_asub_(SASub,SVars,ASub0),
	share_abs_sort(ASub0,ASub1).

share_amgu_augment_asub_(ASub,[],ASub).
share_amgu_augment_asub_(ASub,[H|T],[[H]|ASub0]):-
	share_amgu_augment_asub_(ASub,T,ASub0).

%------------------------------------------------------------------------%
%                      ABSTRACT Extend_two_asub                          %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_amgu_augment_two_asub(+,+,-)                                      %
%-------------------------------------------------------------------------
:- export(share_amgu_augment_two_asub/3).
share_amgu_augment_two_asub([],ASub1,ASub1):-!.
share_amgu_augment_two_asub(ASub0,[],ASub0):-!.
share_amgu_augment_two_asub(ASub0,ASub1,ASub):-
        append(ASub0,ASub1,ASub_u),
	share_abs_sort(ASub_u,ASub),!.
	
       
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,-)                                                 %
%-------------------------------------------------------------------------

:- export(share_amgu_exit_to_prime/7).
share_amgu_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
share_amgu_exit_to_prime(Sg,Hv,Head,_Sv,Exit,Flag,Prime):-  
	Flag == yes, !,
	share_project(Hv,Exit,BPrime),
	copy_term((Head,BPrime),(NewHead,NewPrime)),
	Sg = NewHead,
	share_abs_sort(NewPrime,Prime).
share_amgu_exit_to_prime(_,[],_,_,_,_,[]):- !.
share_amgu_exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
	ExtraInfo= (Equations,Gv_Call),
	share_amgu_augment_asub(Exit,Sv,ASub),     
        share_amgu_iterate(Equations,star, ASub, Prime0),
        share_project(Sv,Prime0,Prime1),
	% groundness propagation from call_to_entry
	ord_split_lists_from_list(Gv_Call,Prime1,_,Prime).

%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%

:- export(share_amgu_call_to_success_fact/9).
share_amgu_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ) :-
% exit_to_prime
	share_amgu_augment_asub(Call,Hv,ASub),
	peel_equations(Sg, Head,Equations),
	share_amgu_iterate(Equations,star,ASub,ASub1),
	share_project(Sv,ASub1,Prime),
% extend
	delete_vars_from_list_of_lists(Hv,ASub1,Succ0),
	sort_list_of_lists(Succ0,Succ),!.	
share_amgu_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom').	

%-------------------------------------------------------------------------
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%-------------------------------------------------------------------------
:- export(share_amgu_call_to_prime_fact/6).
share_amgu_call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime
	share_amgu_augment_asub(Call,Hv,ASub),
	peel_equations(Sg, Head,Equations),
	share_amgu_iterate(Equations,star,ASub,ASub1),
	share_project(Sv,ASub1,Prime).	


%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%
% share_special_builtin(+,+,+,-,-)                                       |
% share_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                  |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) ground : if the builtin makes all variables ground whithout        |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) bottom : if the abstract execution of the builtin returns bottom   |
% (3) unchanged : if we cannot infer anything from the builtin, the      |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previous freeness values of the variables.                  |
% (4) some: if it makes some variables ground without imposing conditions|
% (5) Sgkey: special handling of some particular builtins                |
%-------------------------------------------------------------------------
:- export(share_amgu_special_builtin/5).
share_amgu_special_builtin('read/2',read(X,Y),_,'recorded/3',p(Y,X)).
share_amgu_special_builtin('length/2',length(_X,Y),_,some,[Y]).
share_amgu_special_builtin('==/2',_,_,_,_):- !, fail.
share_amgu_special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
	share_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
	

%-------------------------------------------------------------------------
% share_amgu_success_builtin(+,+,+,+,+,-)                                |
% share_amgu_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                  |
% Obtains the success for some particular builtins:                      |
%  * If Type = ground, it updates Call making all vars in Sv_u ground    |
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%-------------------------------------------------------------------------

:- export(share_amgu_success_builtin/6).
share_amgu_success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
	varset(X,Varsx),
	projected_gvars(Call,Varsx,Vars),Vars == Varsx,!,
	varset(Y,Varsy),
	ord_split_lists_from_list(Varsy,Call,_Intersect,Succ).
share_amgu_success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
	nonvar(Y),
	Y = [Z|W],
	varset(W,Varsy),
	projected_gvars(Call,Varsy,Vars),Vars == Varsy,!,
	varset((X,Z),Varsx),
	ord_split_lists_from_list(Varsx,Call,_Intersect,Succ).
share_amgu_success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
	var(X), var(Y),!,
	sort(Sv_u,Sv),
	share_extend([Sv],Sv,Call,Succ).
share_amgu_success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
%%	( var(Y) ; Y = [_|_] ), !,
%%	( var(X) -> Term=[g|X] ; X=..Term ),
	( var(Y) -> G=g ; Y = [G|_] ), !,
	( var(X) -> Term=[G|X] ; X=..Term ),
	sort(Sv_u,Sv),
	share_project(Sv,Call,Proj),
	share_amgu_call_to_success_builtin('=/2','='(Term,Y),Sv,Call,Proj,Succ).
share_amgu_success_builtin('=../2',_Sv_u,_,_,_Call,'$bottom'):- !.
share_amgu_success_builtin(copy_term,_Sv_u,p(X,Y),_,Call,Succ):-
	varset(X,VarsX),
	share_project(VarsX,Call,ProjectedX),
	copy_term((X,ProjectedX),(NewX,NewProjectedX)),
	sort_list_of_lists(NewProjectedX,ProjectedNewX),
	varset(NewX,VarsNewX),
	varset(Y,VarsY),
	merge(VarsNewX,VarsY,TempSv),
	share_project(VarsY,Call,ProjectedY),
	merge(ProjectedY,ProjectedNewX,TempProjected),
	merge(ProjectedNewX,Call,TempCall),
	share_amgu_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                                TempCall,TempProjected,Temp_success),
	merge_list_of_lists(Call,VarsCall),
	share_project(VarsCall,Temp_success,Succ),
	!. % TODO: move cut somewhere else? (JF)
share_amgu_success_builtin(findall,_Sv_u,p(X,Z),HvFv_u,Call,Succ):-
	varset(X,Varsx),
	projected_gvars(Call,Varsx,Vars),Vars == Varsx,!,
	varset(Z,Varsz),
	share_amgu_success_builtin(ground,Varsz,_any,HvFv_u,Call,Succ).
share_amgu_success_builtin(findall,_Sv_u,_,_HvFv_u,Call,Call):- !.
%
share_amgu_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ):-
	share_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ).

%-------------------------------------------------------------------------
% share_amgu_call_to_success_builtin(+,+,+,+,+,-)                        %
% share_amgu_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)         %
% Handles those builtins for which computing Prime is easier than Succ   %
%-------------------------------------------------------------------------
:- export(share_amgu_call_to_success_builtin/6).
share_amgu_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,!,
	varset(Xterm,Vars),
	share_amgu_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
share_amgu_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom').
share_amgu_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
	share_amgu_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
share_amgu_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	share_amgu_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
share_amgu_call_to_success_builtin('expand_term/2',expand_term(X,Y),Sv,Call,Proj,Succ):- 
	share_amgu_call_to_success_builtin('arg/3',arg(1,Y,X),Sv,Call,Proj,Succ).
share_amgu_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
	share_amgu_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
share_amgu_call_to_success_builtin('arg/3',arg(X,Y,Z),_,Call,Proj,Succ):- 
	varset(X,OldG),
	ord_split_lists_from_list(OldG,Call,_Intersect,TempCall),
	Sg = p(Y,Z),
	Head = p(f(A,_B),A),
	varset(Sg,Sv),
	varset(Head,Hv),
	share_project(Sv,TempCall,Proj),
	share_amgu_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempCall,Proj,_Prime,Succ). % TODO: add some ClauseKey?

%------------------------------------------------------------------------%
%            Intermediate Functions                                      |
%------------------------------------------------------------------------%

%% obtain_groundness_call(Proj,Sv,Gv):-
%%      merge_list_of_lists(Proj,Vars_Proj),
%%      ord_subtract(Sv,Vars_Proj,Gv).

