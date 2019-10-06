:- module(shfrlin_amgu, [], [assertions, isomodes]).

:- doc(title, "amgu-based sharing+freeness+linearity domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2006-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the domain dependent abstract functions           |
% sharing+freeness+linearity. The functions call2entry and exit2prime are|
% defined based on amgu.                                                 |
%------------------------------------------------------------------------%
% The meaning of the variables are partially defined in sharefree.pl     |
%------------------------------------------------------------------------%

:- doc(bug,"1. The builtins do not use the linearity info."). 
:- doc(bug,"2. The extend function does not use linearity info."). 
     
:- use_module(library(terms_vars),     [varset/2, varset0/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(library(sets)).
:- use_module(library(lists), [list_to_list_of_lists/2]).
:- use_module(library(terms_check), [variant/2]).

:- use_module(domain(sharefree), [
	shfr_compute_lub_el/3,
	shfr_empty_entry/3,
	shfr_extend/4,
	shfr_glb/3,
	shfr_input_interface/4,
	shfr_input_user_interface/5,
	shfr_less_or_equal/2,
	shfr_project/3,
	shfr_abs_sort/2,
	shfr_unknown_call/4,
	shfr_unknown_entry/3,
	%
	update_lambda_sf/5,
	values_equal/3,
	change_values_if_f/4,
	obtain_prime_var_var/3,
	product/8]).
:- use_module(domain(sharefree_amgu), [
	sharefree_amgu_call_to_success_builtin/6,
	sharefree_amgu_augment_asub/3,
	sharefree_amgu_special_builtin/5,
	sharefree_amgu_success_builtin/5,
	sharefree_delete_variables/3]).
:- use_module(domain(share_aux), [if_not_nil/4,list_ground/2]).
:- use_module(domain(sharefree_amgu_aux), [
	filter_freeness_with_call/3,
	peel_equations_frl/3,
	unmap_freeness_list/2]).

:- use_module(domain(s_grshfr), [
	member_value_freeness/3,
	change_values_insert/4,
	var_value/3]).
:- use_module(domain(shfrlin_amgu_aux),
        [shfrlin_amgu_iterate/3, shfrlin_update_fr_lin/3]).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_call_to_entry(+,+,+,+,+,+,+,-,?)                               |
%------------------------------------------------------------------------%
:- export(shfrlin_call_to_entry/9).
shfrlin_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
     variant(Sg,Head),!,
     Flag = yes,
     copy_term((Sg,Proj),(NewTerm,NewProj)),
     Head = NewTerm,
     shfrlin_sort(NewProj,(Temp_sh,Temp_fr,Temp_lin)),
     change_values_insert(Fv,Temp_fr,Entry_fr,f),	
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp_sh,Entry_sh),
     merge(Temp_lin,Fv,Entry_lin),
     Entry = (Entry_sh,Entry_fr,Entry_lin).
shfrlin_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
     list_to_list_of_lists(Fv,Entry_sh),
     change_values_insert(Fv,[],Entry_fr,f),
     member_value_freeness(Entry_fr,Entry_lin,f),
     Entry = (Entry_sh,Entry_fr,Entry_lin).
shfrlin_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Project,Entry,ExtraInfo):-
     Project = (_,F2,_),
     peel_equations_frl(Sg, Head,Equations),
     shfrlin_augment_asub(Project,Hv,ASub),     
     shfrlin_amgu_iterate(Equations,ASub,ASub0),
     shfrlin_update_fr_lin(ASub0,Hv,ASub1),
     shfrlin_project(ASub1,Hv,Entry0),
     shfrlin_augment_asub(Entry0,Fv,Entry),
     ExtraInfo = (Equations,F2),!.
shfrlin_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).
     
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_exit_to_prime(+,+,+,+,+,-)                                     |            
%------------------------------------------------------------------------%
:- export(shfrlin_exit_to_prime/7).
shfrlin_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
shfrlin_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
     shfrlin_project(Exit,Hv,(BPrime_sh,BPrime_fr,BPrime_lin)),
     copy_term((Head,(BPrime_sh,BPrime_fr,BPrime_lin)),(NewTerm,NewPrime)),
     Sg = NewTerm,
     shfrlin_sort(NewPrime,Prime).	
shfrlin_exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
     list_ground(Sv,Prime_fr),
     member_value_freeness(Prime_fr,Prime_lin,f),
     Prime = ([],Prime_fr,Prime_lin).
shfrlin_exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Freeness_Call),	
     filter_freeness_with_call(Sv,Freeness_Call,New_Sv),
     shfrlin_augment_asub(Exit,New_Sv,ASub),     
     shfrlin_amgu_iterate(Equations,ASub,ASub0),
     shfrlin_update_fr_lin(ASub0,Sv,ASub1),
     shfrlin_project(ASub1,Sv,Prime).
%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_extend(+,+,+,-)                                                |
% shfrlin_extend(Prime,Sv,Call,Succ)                                     |
%------------------------------------------------------------------------%
:- export(shfrlin_extend/4).
shfrlin_extend('$bottom',_Sv,_Call,Succ):- !,
	Succ = '$bottom'.
shfrlin_extend(_Prime,[],Call,Succ):- !,
	Call = Succ.
shfrlin_extend(Prime,Sv,Call,(Succ_sh,Succ_fr,Succ_lin)):-
	Call = (Call_sh,Call_fr,Call_lin),
	Prime = (Prime_sh,Prime_fr,Prime_lin),
        %% sharing + freeeness
	shfr_extend((Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),(Succ_sh,Succ_fr)),
        %% linearity
        ord_subtract(Call_lin,Sv,Call_lin_not_rel),
	member_value_freeness(Succ_fr,Succ_gr,g),
	ord_subtract(Call_lin_not_rel,Succ_gr,Call_lin_not_rel0),
	ord_union(Prime_lin,Call_lin_not_rel0,Succ_lin).

%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_amgu_amgu(+,+,+,-)                                             %
% shfrlin_amgu_amgu(Sg,Head,ASub,AMGU)                                   %
% @var{AMGU} is the abstract unification between @var{Sg} and @var{Head}.%
%------------------------------------------------------------------------%
:- export(shfrlin_amgu_amgu/4).
shfrlin_amgu_amgu(Sg,Head,ASub,AMGU):-
	peel_equations_frl(Sg, Head,Eqs),
	shfrlin_amgu_iterate(Eqs,ASub,AMGU),!.
	
%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_augment_asub(+,+,-)                                             |
%------------------------------------------------------------------------%
:- export(shfrlin_augment_asub/3).
shfrlin_augment_asub('$bottom',_,'$bottom'):-!.
shfrlin_augment_asub(SHFL,[],SHFL):-!.
shfrlin_augment_asub((Sh,F,L),Vars,(NewSh,NewF,NewL)):-
	ord_union(L,Vars,NewL),
	sharefree_amgu_augment_asub((Sh,F),Vars,(NewSh,NewF)).

%------------------------------------------------------------------------%
%                      ABSTRACT Project                                  |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_project(+,+,-)                                                 |
%------------------------------------------------------------------------%
:- export(shfrlin_project/3).
shfrlin_project('$bottom',_,'$bottom').
shfrlin_project((Sh,F,L),Vars,(Sh_proj,F_proj,L_proj)):-
	shfr_project((Sh,F),Vars,(Sh_proj,F_proj)),
	ord_intersection(L,Vars,L_proj).

%------------------------------------------------------------------------%
%                      ABSTRACT Sort                                     |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_sort(+,-)                                                      |
%------------------------------------------------------------------------%
:- export(shfrlin_sort/2).
shfrlin_sort('$bottom','$bottom').
shfrlin_sort((Sh,F,L),(Sh_s,F_s,L_s)):-
	shfr_abs_sort((Sh,F),(Sh_s,F_s)),
	sort(L,L_s).

%------------------------------------------------------------------------%
% shfrlin_glb(+,+,-)                                                     |
% shfrlin_glb(ASub0,ASub1,Glb)                                           |
%------------------------------------------------------------------------%
:- export(shfrlin_glb/3).
shfrlin_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
shfrlin_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
shfrlin_glb((Sh1,Fr1,Lin1),(Sh2,Fr2,Lin2),Glb):-
	shfr_glb((Sh1,Fr1),(Sh2,Fr2),Glb0),
	( Glb0 == '$bottom' 
        -> 
          Glb = '$bottom'
        ;
	  ord_union(Lin1,Lin2,Lin),
	  Glb0= (Sh,Fr),
	  Glb = (Sh,Fr,Lin)
        ).

%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%
:- export(shfrlin_call_to_success_fact/9).
shfrlin_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ) :-
% exit_to_prime   -------------------------------------------------------
	shfrlin_augment_asub(Call,Hv,ASub),  
	peel_equations_frl(Sg, Head,Equations),
	shfrlin_amgu_iterate(Equations,ASub,ASub0),
	ASub = (_,Vars,_),        
	unmap_freeness_list(Vars,Vars0),
	shfrlin_update_fr_lin(ASub0,Vars0,ASub1),
	shfrlin_project(ASub1,Sv,Prime),
% extend    --------------------------------------------------------------
	shfrlin_delete_variables(Hv,ASub1,Succ),!.
shfrlin_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom').

shfrlin_delete_variables(Vars,(Sh,Fr,L),(New_Sh,New_Fr,NewL)):-
	sharefree_delete_variables(Vars,(Sh,Fr),(New_Sh,New_Fr)),
	delete_variables_lin(L,Vars,NewL).

delete_variables_lin([],_,[]).
delete_variables_lin([X|Xs],Vars,Res):-
	ord_member(X,Vars),!,
	delete_variables_lin(Xs,Vars,Res).
delete_variables_lin([X|Xs],Vars,[X|Res]):-
	delete_variables_lin(Xs,Vars,Res).

%------------------------------------------------------------------------%
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%------------------------------------------------------------------------%
:- export(shfrlin_call_to_prime_fact/6).
shfrlin_call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime    -------------------------------------------------------
	shfrlin_augment_asub(Call,Hv,Exit),
	Call = (_Sh,Extra_Info,_),
	shfrlin_exit_to_prime(Sg,Hv,Head,Sv,Exit,Extra_Info,Prime), !.
shfrlin_call_to_prime_fact(_Sg,_Hv,_Head,_Sv,'$bottom','$bottom').

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% shfrlin_special_builtin(+,+,+,-,-)                                     |
% shfrlin_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                |
%------------------------------------------------------------------------%
:- export(shfrlin_special_builtin/5).
shfrlin_special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
	sharefree_amgu_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
	
%------------------------------------------------------------------------%
% shfrlin_success_builtin(+,+,+,+,-)                                     |
% shfrlin_success_builtin(Type,Sv_u,Condv,Call,Succ)                     |
%------------------------------------------------------------------------%
:- export(shfrlin_success_builtin/5).
% shfrlin_success_builtin(arg,_,p(X,Y,Z),Call,Succ):-
% 	Call = (Call_sh,Call_fr,Call_lin),
% 	varset(X,OldG),
% 	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
% 	var_value(Temp_fr,Y,Value),
% 	Value \== f,!,
% 	Sg = p(Y,Z),
% 	Head = p(f(A,_B),A),
% 	varset(Sg,Sv),
% 	varset(Head,Hv),
% 	TempASub = (Temp_sh,Temp_fr),
% 	shfr_project(TempASub,Sv,Proj),
%  	shfrlin_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
% shfrlin_success_builtin(arg,_,_,_,'$bottom').
shfrlin_success_builtin(exp,_,Sg,Call,Succ):- !,
	Head = p(A,f(A,_B)),
	varset(Sg,Sv),
	varset(Head,Hv),
	shfrlin_project(Call,Sv,Proj),
	shfrlin_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
shfrlin_success_builtin(exp,_,_,_,'$bottom') :- !.
% shfrlin_success_builtin(copy_term,_,p(X,Y),Call,Succ):-
% 	varset(X,VarsX),
% 	shfr_project(Call,VarsX,ProjectedX),
% 	copy_term((X,ProjectedX),(NewX,NewProjectedX)),
% 	shfr_abs_sort(NewProjectedX,ProjectedNewX),
% 	varset(NewX,VarsNewX),
% 	varset(Y,VarsY),
% 	merge(VarsNewX,VarsY,TempSv),
% 	shfr_project(Call,VarsY,ProjectedY),
% 	ProjectedY = (ShY,FrY),
% 	ProjectedNewX = (ShNewX,FrNewX),
% 	merge(ShY,ShNewX,TempSh),
% 	merge(FrY,FrNewX,TempFr),
% 	Call = (ShCall,FrCall),
% 	merge(ShNewX,ShCall,TempCallSh),
% 	merge(FrNewX,FrCall,TempCallFr),
% 	shfrlin_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
%                     (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
% 	collect_vars_freeness(FrCall,VarsCall),
% 	shfr_project(Temp_success,VarsCall,Succ).
shfrlin_success_builtin(Type,Sv_u,Condv,Call,Succ):-
	Call = (Sh,Fr,Lin),
	ord_subtract(Lin,Sv_u,Lin_not_rel),	
	sharefree_amgu_success_builtin(Type,Sv_u,Condv,(Sh,Fr),Succ0),
        ( Succ0 == '$bottom' 
        ->
	  Succ = '$bottom'
        ;
          Succ0 = (Sh_succ,Fr_succ),
  	  member_value_freeness(Fr_succ,L_succ0,f),
	  ord_union(L_succ0,Lin_not_rel,L_succ),
	  Succ= (Sh_succ,Fr_succ,L_succ)
        ).

%------------------------------------------------------------------------%
% shfrlin_call_to_success_builtin(+,+,+,+,+,-)                           |
% shfrlin_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)            |
% Handles those builtins for which computing Prime is easier than Succ   |
%------------------------------------------------------------------------%
:- export(shfrlin_call_to_success_builtin/6).
shfrlin_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr,_),Succ):-
	varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
	Call = (Call_sh,Call_fr,Call_lin),
	ord_subtract(Call_lin,Sv,Call_lin_not_rel),
	ord_subtract(Sv,VarsX,VarsY),
	update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
	member_value_freeness(Succ_fr,Succ_lin0,f),
	ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin),
	Succ = (Succ_sh,Succ_fr,Succ_lin).
shfrlin_call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr,_),Succ):-
	varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
	Call = (Call_sh,Call_fr,Call_lin),
	ord_subtract(Call_lin,Sv,Call_lin_not_rel),
	ord_subtract(Sv,VarsY,VarsX),
	update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
	member_value_freeness(Succ_fr,Succ_lin0,f),
	ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin),
	Succ = (Succ_sh,Succ_fr,Succ_lin).
shfrlin_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	var(X),var(Y), !,
	Proj = (_,Proj_fr,_),	
	Call = (Sh_call,Fr_call,Call_lin),
	ord_subtract(Call_lin,Sv,Call_lin_not_rel),
	obtain_prime_var_var(Proj_fr,(Sh_call,Fr_call),(Succ_sh,Succ_fr)),
	member_value_freeness(Succ_fr,Succ_lin0,f),
	ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin),
	Succ = (Succ_sh,Succ_fr,Succ_lin).
shfrlin_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
	var(X), !,
	Proj = (Proj_sh,Proj_fr,_),	
	ord_subtract(Sv,[X],VarsY),
	var_value(Proj_fr,X,ValueX),
	product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
        member_value_freeness(Prime_fr,Prime_lin,f),
	shfrlin_extend((Prime_sh,Prime_fr,Prime_lin),Sv,Call,Succ).
shfrlin_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,!,
	varset(Xterm,Vars),
	shfrlin_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
shfrlin_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom') :- !.
shfrlin_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
	shfrlin_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ), % TODO: add some ClauseKey?
	!. % TODO: move cut? (JF)
shfrlin_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
	shfrlin_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ),
	!. % TODO: move cut? (JF)
shfrlin_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	var(X), !,
	Proj = (_Sh,Fr,_),
	var_value(Fr,X,Val),
	( Val = f ->
	  Succ = '$bottom'
	; varset([X,Y],Sv),
	  copy_term(Y,Yterm),
	  varset(Yterm,Vars),
	  shfrlin_call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),not_provided,Sv,Call,Proj,_Prime,Succ) % TODO: add some ClauseKey?
	).
shfrlin_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	functor(X,'.',_), !,
	varset0(X,[Z|_]),
	Call = (Call_Sh,Call_fr,_),
	change_values_if_f([Z],Call_fr,Temp_fr,nf),
	varset([X,Y],Sv),
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,
	varset(Xterm,Vars),
	Proj = (Sh,Fr,_),
	change_values_if_f([Z],Fr,TFr,nf),
	member_value_freeness(Temp_fr,Temp_lin,f),
	member_value_freeness(TFr,Lin,f),
	shfrlin_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_Sh,Temp_fr,Temp_lin),(Sh,TFr,Lin),_Prime,Succ). % TODO: add some ClauseKey? 
shfrlin_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,(Succ_sh,Succ_fr,Succ_lin)):- 
	Call = (Call_sh,Call_fr,Call_lin),
	ord_subtract(Call_lin,Sv,Call_lin_not_rel),
	Proj = (Proj_sh,Proj_fr,_),
	sharefree_amgu_call_to_success_builtin(SgKey,Sg,Sv,(Call_sh,Call_fr),
	                                       (Proj_sh,Proj_fr),(Succ_sh,Succ_fr)),
	member_value_freeness(Succ_fr,Succ_lin0,f),
	ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin).

%------------------------------------------------------------------------%
% compute_lub(+,-)                                                       |
%------------------------------------------------------------------------%
:- export(shfrlin_compute_lub/2).
shfrlin_compute_lub([X],X):- !.
shfrlin_compute_lub([ASub1,ASub2|Xs],Lub):-
	shfrlin_compute_lub_el(ASub1,ASub2,ASubLub),
	shfrlin_compute_lub([ASubLub|Xs],Lub).

%------------------------------------------------------------------------%
% compute_lub_el(+,-)                                                    |
%------------------------------------------------------------------------%
:- export(shfrlin_compute_lub_el/3).
shfrlin_compute_lub_el('$bottom',ASub,ASub):-!.
shfrlin_compute_lub_el(ASub,'$bottom',ASub):-!.
shfrlin_compute_lub_el((Sh1,Fr1,Lin1),(Sh2,Fr2,Lin2),ASub):-
	shfr_compute_lub_el((Sh1,Fr1),(Sh2,Fr2),(Sh_ASub,Fr_ASub)),
	ord_intersection(Lin1,Lin2,Lin_ASub),
	ASub = (Sh_ASub,Fr_ASub,Lin_ASub).

%------------------------------------------------------------------------%
% less_or_equa(+,+)                                                      |
% Succeeds if ASub1 is more general or equal to ASub0                    |
%------------------------------------------------------------------------%
:- export(shfrlin_less_or_equal/2).
shfrlin_less_or_equal('$bottom',_ASub):- !.
shfrlin_less_or_equal((Sh0,Fr0,Lin0),(Sh1,Fr1,Lin1)):-
        shfr_less_or_equal((Sh0,Fr0),(Sh1,Fr1)),!,
	ord_subset(Lin0,Lin1).


%------------------------------------------------------------------------%
% shfrlin_input_user_interface(+,+,-,+,+)                                |
% shfrlin_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)       |
% Obtaining the abstract substitution for Sh+Fr+lin from the user        |
% supplied information just consists in taking the Sharing first and the |
% var(Fv) element of InputUser, and construct from them the Freeness and |
% the Linearity.                                                         |
%------------------------------------------------------------------------%
:- export(shfrlin_input_user_interface/5).
shfrlin_input_user_interface((Sh,Vars,_),Qv,(Call_sh,Call_fr,Call_lin),Sg,MaybeCallASub):-
	shfr_input_user_interface((Sh,Vars),Qv,(Call_sh,Call_fr),Sg,MaybeCallASub),
	member_value_freeness(Call_fr,Call_lin,f).

%------------------------------------------------------------------------%
% shfrlin_input_interface(+,+,+,-)                                       |
% shfrlin_input_interface(InputUser,Kind,ASub0,ASub)                     |
%------------------------------------------------------------------------%
:- export(shfrlin_input_interface/4).
shfrlin_input_interface(linear(X),perfect,(Sh,Fr,Lin0),(Sh,Fr,Lin)):-
	myunion(Lin0,X,Lin).
shfrlin_input_interface(free(X),perfect,(Sh,Fr0,Lin0),(Sh,Fr,Lin)):-
	var(X),
	myinsert(Fr0,X,Fr),
        myinsert(Lin0,X,Lin).
shfrlin_input_interface(Info,Kind,(Sh0,Fr0,Lin),(Sh,Fr,Lin)):-
	shfr_input_interface(Info,Kind,(Sh0,Fr0),(Sh,Fr)).

myunion(Lin0,X,Lin):-
	var(Lin0),!,
	sort(X,Lin).
myunion(Lin0,X,Lin):-
	sort(X,Xs),
	ord_union(Lin0,Xs,Lin).
myinsert(Fr0,X,Fr):-
	var(Fr0), !,
	Fr = [X].
myinsert(Fr0,X,Fr):-
	insert(Fr0,X,Fr).

%------------------------------------------------------------------------%
% shfrlin_asub_to_native(+,+,+,-,-)                                      |
% shfrlin_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                |
% The user friendly format consists in extracting the ground variables,  |
% free variables, and linear variables.                                  |
%------------------------------------------------------------------------%
:- export(shfrlin_asub_to_native/5).
shfrlin_asub_to_native((Sh,Fr,L),_Qv,_OutFlag,Info,[]):-
	if_not_nil(Sh,sharing(Sh),Info,Info0),
	member_value_freeness(Fr,Fv,f),
	if_not_nil(Fv,free(Fv),Info0,Info1),
	member_value_freeness(Fr,Gv,g),
	if_not_nil(Gv,ground(Gv),Info1,Info2),
	if_not_nil(L,linear(L),Info2,[]).

% shfrlin_asub_to_native((Sh,Fr,_L),_Qv,Info):-
% 	if_not_nil(Sh,sharing(Sh),Info,Info0),
% 	member_value_freeness(Fr,Fv,f),
% 	if_not_nil(Fv,free(Fv),Info0,Info1),
% 	member_value_freeness(Fr,Gv,g),
% 	if_not_nil(Gv,ground(Gv),Info1,[]).

%------------------------------------------------------------------------%
% shfrlin_unknown_call(+,+,+,-)                                          |
% shfrlin_unknown_call(Sg,Vars,Call,Succ)                                |  
% Obtained by selecting those sets in Call for which at least a variable |
% in Vars appears, making the star of those sets, and adding the sets    |
% with empty intersection with Vars. In freeness, all variables related  |
% to Vars are nf, and in linearity, subtract from Call_lin all variables |
% not related to Vars and make the union between the related Call_lin    |
% with free variables returned by freeness.                              |
%------------------------------------------------------------------------%
:- export(shfrlin_unknown_call/4).
shfrlin_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
shfrlin_unknown_call(Sg,Vars,(Call_sh,Call_fr,Call_lin),Succ):-
	shfr_unknown_call(Sg,Vars,(Call_sh,Call_fr),(Succ_sh,Succ_fr)),
	ord_subtract(Call_lin,Vars,Call_lin_not_rel),
	member_value_freeness(Succ_fr,Succ_lin0,f),
	ord_intersection(Succ_lin0,Vars,Succ_lin1),
	ord_union(Call_lin_not_rel,Succ_lin1,Succ_lin),
	Succ = (Succ_sh,Succ_fr,Succ_lin).

%------------------------------------------------------------------------%
% shfrlin_unknown_entry(+,+,-)                                           |
% shfrlin_unknown_entry(Sg,Qv,Call)                                      |
% The top value in Sh for a set of variables is the powerset, in Fr is   |
% X/nf forall X in the set of variables, and in no variable is linear.   |
%------------------------------------------------------------------------%
:- export(shfrlin_unknown_entry/3).
shfrlin_unknown_entry(Sg,Qv,(Call_sh,Call_fr,[])):-
	shfr_unknown_entry(Sg,Qv,(Call_sh,Call_fr)).

%------------------------------------------------------------------------%
% shfrlin_empty_entry(+,+,-)                                             |
% The empty value in Sh for a set of variables is the list of singletons,|
% in Fr is X/f forall X in the set of variables, and these variables are |
% all linear.                                                            |
%------------------------------------------------------------------------%
:- export(shfrlin_empty_entry/3).
shfrlin_empty_entry(Sg,Qv,(Call_sh,Call_fr,Qv)):-
        shfr_empty_entry(Sg,Qv,(Call_sh,Call_fr)).

