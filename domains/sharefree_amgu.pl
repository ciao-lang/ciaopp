:- module(sharefree_amgu, [], [assertions, isomodes]).

:- doc(title, "amgu-based sharing+freeness domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the same domain dependent abstract functions than |
% sharefree.pl but the functions call_to_entry and exit_to_prime are     |
% defined based on amgu.                                                 |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharefree.pl               |
%------------------------------------------------------------------------%

:- doc(bug,"1. The builtin ==/2 is defined but it is not used because
           of benchmarks. For its use, comment it out in special_builtin.").
:- doc(bug,"2. The builtins read/2 and length/2 are used in a simple
	   way. In order to use more complex definitions, comment it in 
	   special_builtin.").
:- doc(bug,"3. The non-redundant version is not working because the 
	   semantics of the builtins has not been defined yet.").

:- use_module(library(terms_vars),     [varset/2, varset0/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(library(sets)).
:- use_module(library(lists), [
	list_to_list_of_lists/2
   ]).
:- use_module(library(lsets), [
	closure_under_union/2,
	sort_list_of_lists/2,
	merge_each/3
   ]).
:- use_module(library(terms_check), [variant/2]).

:- use_module(domain(share_amgu_sets), [delete_vars_from_list_of_lists/3]).
:- use_module(domain(s_grshfr),
	[ change_values_if_differ/5,
	  collect_vars_freeness/2,
	  var_value/3,
	  change_values_insert/4]).
:- use_module(domain(share_aux), [list_ground/2]).

:- use_module(domain(sharing), [share_project/3]).
:- use_module(domain(sharing_amgu), [share_amgu_extend_asub/3]).
:- use_module(domain(sharefree), [
	shfr_call_to_success_builtin/6,
	shfr_extend/4,
	shfr_project/3,
	shfr_sort/2,
	shfr_special_builtin/5,
	shfr_success_builtin/5]).
:- use_module(domain(sharefree_amgu_aux)).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_amgu_call_to_entry(+,+,+,+,+,+,+,-,?)                        %
%------------------------------------------------------------------------%
:- export(sharefree_amgu_call_to_entry/9).
sharefree_amgu_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
     variant(Sg,Head),!,
     Flag = yes,
     copy_term((Sg,Proj),(NewTerm,NewProj)),
     Head = NewTerm,
     shfr_sort(NewProj,(Temp_sh,Temp_fr)),
     change_values_insert(Fv,Temp_fr,Entry_fr,f),	
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp_sh,Entry_sh),
     Entry = (Entry_sh,Entry_fr).
sharefree_amgu_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
     list_to_list_of_lists(Fv,Entry_sh),
     change_values_insert(Fv,[],Entry_fr,f),
     Entry = (Entry_sh,Entry_fr).
sharefree_amgu_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Project,Entry,ExtraInfo):-
     Project = (_,F2),
     peel_equations_frl(Sg, Head,Equations),
     sharefree_amgu_extend_asub(Project,Hv,ASub),     
     sharefree_amgu_iterate(Equations,ASub,(Sh,F)),
     shfr_update_freeness(Sh,F,Hv,F1),
     shfr_project((Sh,F1),Hv,Entry0),
     sharefree_amgu_extend_asub(Entry0,Fv,Entry),
     ExtraInfo = (Equations,F2),!.
sharefree_amgu_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).
    
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-)                                             %
%-------------------------------------------------------------------------
:- export(sharefree_amgu_exit_to_prime/7).
sharefree_amgu_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
sharefree_amgu_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
     shfr_project(Exit,Hv,(BPrime_sh,BPrime_fr)),
     copy_term((Head,(BPrime_sh,BPrime_fr)),(NewTerm,NewPrime)),
     Sg = NewTerm,
     shfr_sort(NewPrime,Prime).	
sharefree_amgu_exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
     list_ground(Sv,Prime_fr),
     Prime = ([],Prime_fr).
sharefree_amgu_exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Freeness_Call),	
     filter_freeness_with_call(Sv,Freeness_Call,New_Sv),
     sharefree_amgu_extend_asub(Exit,New_Sv,ASub),     
     sharefree_amgu_iterate(Equations,ASub,(Sh,F)),
     shfr_update_freeness(Sh,F,Sv,F1),
     shfr_project((Sh,F1),Sv,Prime).

%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_amgu(+,+,+,-)                                                %
% sharefree_amgu(Sg,Head,ASub,AMGU)                                      %
% @var{AMGU} is the abstract unification between @var{Sg} and @var{Head}.%
%------------------------------------------------------------------------%
:- export(sharefree_amgu/4).
sharefree_amgu(Sg,Head,ASub,AMGU):-
	peel_equations_frl(Sg, Head,Eqs),
	sharefree_amgu_iterate(Eqs,ASub,AMGU),!.
	
%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_amgu_extend_asub(+,+,-)                                      %
%-------------------------------------------------------------------------
:- export(sharefree_amgu_extend_asub/3).
sharefree_amgu_extend_asub(SHF,[],SHF) :- !.
sharefree_amgu_extend_asub((Sh,F),Vars,(Sh0,F0)):-
	share_amgu_extend_asub(Sh,Vars,Sh0),
	sharefree_amgu_extend_asub0(F,Vars,F0).

:- export(sharefree_amgu_extend_asub0/3).
sharefree_amgu_extend_asub0(F,[],F) :- !.
sharefree_amgu_extend_asub0(F,Vars,F1):-
	sort(F,SF),
	sort(Vars,SVars),
	sharefree_amgu_extend_asub1(SF,SVars,F1).

sharefree_amgu_extend_asub1(F,[],F) :- !.
sharefree_amgu_extend_asub1(F,[H|T],F1):-
	sharefree_amgu_extend_asub1(F,T,F0),
	ord_union(F0,[H/f],F1).

%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%
:- export(sharefree_amgu_call_to_success_fact/9).
sharefree_amgu_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ) :-
% exit_to_prime    -------------------------------------------------------
	sharefree_amgu_extend_asub(Call,Hv,ASub),  
	peel_equations_frl(Sg, Head,Equations),
	sharefree_amgu_iterate(Equations,ASub,(Sh,F)),
	ASub = (_,Vars),
	unmap_freeness_list(Vars,Vars0),
	shfr_update_freeness(Sh,F,Vars0,F1),
	ASub1= (Sh,F1),
	shfr_project(ASub1,Sv,Prime),
% extend   ---------------------------------------------------------------
	sharefree_delete_variables(Hv,ASub1,Succ),!.
sharefree_amgu_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom').

:- export(sharefree_delete_variables/3).
sharefree_delete_variables(Vars,(Sh,Fr),(New_Sh,New_Fr)):-
	delete_vars_from_list_of_lists(Vars,Sh,Sh0),
	sort_list_of_lists(Sh0,New_Sh),
	delete_variables_freeness(Fr,Vars,New_Fr).

delete_variables_freeness([],_,[]).
delete_variables_freeness([X/_|Xs],Vars,Res):-
	ord_member(X,Vars),!,
	delete_variables_freeness(Xs,Vars,Res).
delete_variables_freeness([X/V|Xs],Vars,[X/V|Res]):-
	delete_variables_freeness(Xs,Vars,Res).

%------------------------------------------------------------------------%
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%------------------------------------------------------------------------%
:- export(sharefree_amgu_call_to_prime_fact/6).
sharefree_amgu_call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime   --------------------------------------------------------
	sharefree_amgu_extend_asub(Call,Hv,Exit),
	Call = (_Sh,Extra_Info),
	sharefree_amgu_exit_to_prime(Sg,Hv,Head,Sv,Exit,Extra_Info,Prime).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% sharefree_special_builtin(+,+,+,-,-)                                   |
% sharefree_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)              |
%------------------------------------------------------------------------%
:- export(sharefree_amgu_special_builtin/5).
sharefree_amgu_special_builtin('read/2',read(X,Y),_,'recorded/3',p(Y,X)).
sharefree_amgu_special_builtin('length/2',length(_X,Y),_,some,[Y]).
sharefree_amgu_special_builtin('==/2',_,_,_,_):- !, fail.
sharefree_amgu_special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
	shfr_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
	
%------------------------------------------------------------------------%
% sharefree_amgu_success_builtin(+,+,+,+,-)                              |
% sharefree_amgu_success_builtin(Type,Sv_u,Condv,Call,Succ)              |
%------------------------------------------------------------------------%

:- export(sharefree_amgu_success_builtin/5).
sharefree_amgu_success_builtin(arg,_,p(X,Y,Z),Call,Succ):-
	Call = (Call_sh,Call_fr),
	varset(X,OldG),
	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
	var_value(Temp_fr,Y,Value),
	Value \== f,
	!,
	Sg = p(Y,Z),
	Head = p(f(A,_B),A),
	varset(Sg,Sv),
	varset(Head,Hv),
	TempASub = (Temp_sh,Temp_fr),
	shfr_project(TempASub,Sv,Proj),
 	sharefree_amgu_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
sharefree_amgu_success_builtin(arg,_,_,_,'$bottom') :- !.
sharefree_amgu_success_builtin(exp,_,Sg,Call,Succ):-
	Head = p(A,f(A,_B)),
	varset(Sg,Sv),
	varset(Head,Hv),
	shfr_project(Call,Sv,Proj),
	sharefree_amgu_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ), % TODO: add some ClauseKey?
	!. % TODO: move cut somewhere else? (JF)
sharefree_amgu_success_builtin(exp,_,_,_,'$bottom') :- !.
% there is a new case (general case) in '../2' that should be implemented 
% in this module because it calls call_to_success_builtin 
sharefree_amgu_success_builtin(copy_term,_,p(X,Y),Call,Succ):-
	varset(X,VarsX),
	shfr_project(Call,VarsX,ProjectedX),
	copy_term((X,ProjectedX),(NewX,NewProjectedX)),
	shfr_sort(NewProjectedX,ProjectedNewX),
	varset(NewX,VarsNewX),
	varset(Y,VarsY),
	merge(VarsNewX,VarsY,TempSv),
	shfr_project(Call,VarsY,ProjectedY),
	ProjectedY = (ShY,FrY),
	ProjectedNewX = (ShNewX,FrNewX),
	merge(ShY,ShNewX,TempSh),
	merge(FrY,FrNewX,TempFr),
	Call = (ShCall,FrCall),
	merge(ShNewX,ShCall,TempCallSh),
	merge(FrNewX,FrCall,TempCallFr),
	sharefree_amgu_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                    (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
	collect_vars_freeness(FrCall,VarsCall),
	shfr_project(Temp_success,VarsCall,Succ),
	!. % TODO: move cut somewhere else? (JF)
sharefree_amgu_success_builtin(Type,Sv_u,Condv,Call,Succ):-
	shfr_success_builtin(Type,Sv_u,Condv,Call,Succ).

%------------------------------------------------------------------------%
% sharefree_amgu_call_to_success_builtin(+,+,+,+,+,-)                    |
% sharefree_amgu_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)     |
% Handles those builtins for which computing Prime is easier than Succ   |
%-------------------------------------------------------------------------
:- export(sharefree_amgu_call_to_success_builtin/6).
sharefree_amgu_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr),Succ):-
	varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
	Call = (Call_sh,Call_fr),
	ord_subtract(Sv,VarsX,VarsY),
	update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
sharefree_amgu_call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr),Succ):-
	varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
	Call = (Call_sh,Call_fr),
	ord_subtract(Sv,VarsY,VarsX),
	update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
sharefree_amgu_call_to_success_builtin('=/2','='(X,Y),_Sv,Call,Proj,Succ):-
	var(X),var(Y), !,
	Proj = (_,Proj_fr),	
	obtain_prime_var_var(Proj_fr,Call,Succ).
sharefree_amgu_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
	var(X), !,
	Proj = (Proj_sh,Proj_fr),	
	ord_subtract(Sv,[X],VarsY),
	var_value(Proj_fr,X,ValueX),
	product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
	Prime= (Prime_sh,Prime_fr),
	shfr_extend(Prime,Sv,Call,Succ).
sharefree_amgu_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,!,
	varset(Xterm,Vars),
	sharefree_amgu_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
sharefree_amgu_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom') :- !.
sharefree_amgu_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
	sharefree_amgu_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ), % TODO: add some ClauseKey?
	!. % TODO: move cut? (JF)
sharefree_amgu_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
	sharefree_amgu_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ),
	!. % TODO: move cut? (JF)
sharefree_amgu_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	var(X), !,
	Proj = (_Sh,Fr),
	var_value(Fr,X,Val),
	( Val = f ->
	  Succ = '$bottom'
	; varset([X,Y],Sv),
	  copy_term(Y,Yterm),
	  varset(Yterm,Vars),
	  sharefree_amgu_call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),not_provided,Sv,Call,Proj,_Prime,Succ) % TODO: add some ClauseKey?
	).
sharefree_amgu_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	functor(X,'.',_), !,
	varset0(X,[Z|_]),
	Call = (Call_Sh,Call_fr),
	change_values_if_f([Z],Call_fr,Temp_fr,nf),
	varset([X,Y],Sv),
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,
	varset(Xterm,Vars),
	Proj = (Sh,Fr),
	change_values_if_f([Z],Fr,TFr,nf),
	sharefree_amgu_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_Sh,Temp_fr),(Sh,TFr),_Prime,Succ). % TODO: add some ClauseKey?
sharefree_amgu_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ):- 
	shfr_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).

%------------------------------------------------------------------------%
%            Intermediate Functions                                      |
%------------------------------------------------------------------------%

:- use_module(domain(sharefree), [
	update_lambda_non_free/5,
	values_equal/3,
	change_values/4,
	change_values_if_f/4,
	update_lambda_sf/5,
	insert_each/3,
	take_coupled/3,
	obtain_prime_var_var/3
	]).

%-------------------------------------------------------------------------

product(f,X,VarsY,_,Sh,Lda_fr,Prime_sh,Prime_fr):-
	share_project(VarsY,Sh,Temp), % TODO: why not project_share/3 like in sharefree.pl?
	insert_each(Temp,X,Temp1),
	sort_list_of_lists(Temp1,Prime_sh),
	take_coupled(Sh,[X],Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
product(nf,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
	share_project(VarsY,Sh,Temp), % TODO: why not project_share/3 like in sharefree.pl?
	closure_under_union(Temp,Temp1),
	merge_each([X],Temp1,Temp2),
	sort(Temp2,Prime_sh),
	take_coupled(Sh,Sv,Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
