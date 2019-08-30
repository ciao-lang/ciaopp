/*             Copyright (C)2004-2005 UNM-CLIP				*/

:- doc(author,"Jorge Navas").

:- use_module(domain(s_grshfr),
	[ change_values_if_differ/5,
	  collect_vars_freeness/2,
	  var_value/3,
	  change_values_insert/4]).

:- use_module(domain(sharefree_amgu_aux)).

%------------------------------------------------------------------------%
% This file implements the same domain dependent abstract functions than |
% sharefree.pl but the functions call_to_entry and exit_to_prime are     |
% defined based on amgu.                                                 |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharefree.pl               |
%------------------------------------------------------------------------%
%                                                                        |
%        programmer: J. Navas                                            |
%                                                                        |
%------------------------------------------------------------------------%

:- doc(bug,"1. The builtin ==/2 is defined but it is not used because
           of benchmarks. For its use, comment it out in special_builtin.").
:- doc(bug,"2. The builtins read/2 and length/2 are used in a simple
	   way. In order to use more complex definitions, comment it in 
	   special_builtin.").
:- doc(bug,"3. The non-redundant version is not working because the 
	   semantics of the builtins has not been defined yet.").

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_amgu_call_to_entry(+,+,+,+,+,+,+,-,?)                        %
%------------------------------------------------------------------------%
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
sharefree_amgu(Sg,Head,ASub,AMGU):-
	peel_equations_frl(Sg, Head,Eqs),
	sharefree_amgu_iterate(Eqs,ASub,AMGU),!.
	
%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_amgu_extend_asub(+,+,-)                                      %
%-------------------------------------------------------------------------
sharefree_amgu_extend_asub(SHF,[],SHF) :- !.
sharefree_amgu_extend_asub((Sh,F),Vars,(Sh0,F0)):-
	share_amgu_extend_asub(Sh,Vars,Sh0),
	sharefree_amgu_extend_asub0(F,Vars,F0).

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
sharefree_amgu_call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime   --------------------------------------------------------
	sharefree_amgu_extend_asub(Call,Hv,Exit),
	Call = (_Sh,Extra_Info),
	sharefree_amgu_exit_to_prime(Sg,Hv,Head,Sv,Exit,Extra_Info,Prime).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% sharefree_special_builtin(+,+,-,-)                                     |
% sharefree_special_builtin(SgKey,Sg,Type,Condvars)                      |
%------------------------------------------------------------------------%
sharefree_amgu_special_builtin('read/2',read(X,Y),'recorded/3',p(Y,X)).
sharefree_amgu_special_builtin('length/2',length(_X,Y),some,[Y]).
sharefree_amgu_special_builtin('==/2',_,_,_):- !, fail.
sharefree_amgu_special_builtin(SgKey,Sg,Type,Condvars):-
	shfr_special_builtin(SgKey,Sg,Type,Condvars).
	
%------------------------------------------------------------------------%
% sharefree_amgu_success_builtin(+,+,+,+,-)                              |
% sharefree_amgu_success_builtin(Type,Sv_u,Condv,Call,Succ)              |
%------------------------------------------------------------------------%
 % TODO: missing cuts in all the following clauses
sharefree_amgu_success_builtin(arg,_,p(X,Y,Z),Call,Succ):-
	Call = (Call_sh,Call_fr),
	varset(X,OldG),
	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
	var_value(Temp_fr,Y,Value),
	Value \== f,!,
	Sg = p(Y,Z),
	Head = p(f(A,_B),A),
	varset(Sg,Sv),
	varset(Head,Hv),
	TempASub = (Temp_sh,Temp_fr),
	shfr_project(TempASub,Sv,Proj),
 	sharefree_amgu_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
sharefree_amgu_success_builtin(arg,_,_,_,'$bottom').
sharefree_amgu_success_builtin(exp,_,Sg,Call,Succ):-
	Head = p(A,f(A,_B)),
	varset(Sg,Sv),
	varset(Head,Hv),
	shfr_project(Call,Sv,Proj),
	sharefree_amgu_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
sharefree_amgu_success_builtin(exp,_,_,_,'$bottom').
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
	shfr_project(Temp_success,VarsCall,Succ).
sharefree_amgu_success_builtin(Type,Sv_u,Condv,Call,Succ):-
	shfr_success_builtin(Type,Sv_u,Condv,Call,Succ).

%------------------------------------------------------------------------%
% sharefree_amgu_call_to_success_builtin(+,+,+,+,+,-)                    |
% sharefree_amgu_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)     |
% Handles those builtins for which computing Prime is easier than Succ   |
%-------------------------------------------------------------------------
 % TODO: missing cuts in all the following clauses
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
sharefree_amgu_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom').
sharefree_amgu_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
	sharefree_amgu_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
sharefree_amgu_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
	sharefree_amgu_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
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

%------------------------------------------------------------------------%
% change_values_if_f(+,+,-,+)                                            |
% change_values_if_f(Vars,Fr,NewFr,Value)                                |
% Forall X in Vars, there must exist an X/V in Fr. If so:                |
%    * if V is f or nf(_,_), X/V is replaced by X/Value                  |
%    * else, X/V remains unchanged                                       |
% Otherwise (X/V not in Fr) it fails                                     |
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).
change_values_if_f([],Xs,Xs,_).
change_values_if_f([Y|Ys],[X/V|Xs],Z,Value):- 
	compare(D,Y,X),
	change_values_if_f(D,Y,Ys,X/V,Xs,Z,Value).

change_values_if_f(=,Y,Ys,_X/V,Xs,[Y/V1|Zs],Value):-
	( (V = f; V = nf(_,_)) ->
	    V1 = Value
	;   V1 = V
        ),
	change_values_if_f(Ys,Xs,Zs,Value).
change_values_if_f(>,Y,Ys,Elem,[X/V|Xs],[Elem|Zs],Value):- 
	compare(D,Y,X),
	change_values_if_f(D,Y,Ys,X/V,Xs,Zs,Value).
:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% update_lambda_non_free(+,+,+,-,-)                                      |
% update_lambda_non_free(Gv,Fr,Sh,NewFr,NewSh)                           |
% Identical to update_lambda_sf but:                                     |
% *  it tests that the variables that become ground are not free.        |
%    The reason is that Ground should be ground already, and therefore   |
%    they cannot make a definitely free variable to become ground        |
% *  it does not change the freeness value of any variable from f to nf  |
%    The same reason                                                     |
%-------------------------------------------------------------------------
update_lambda_non_free([],Fr,Sh,Fr,Sh).
update_lambda_non_free([X|Xs],Fr,Sh,Fr1,Sh1):-
	ord_split_lists_from_list([X|Xs],Sh,Intersect,Sh1),
	merge_list_of_lists(Intersect,Coupled),
	merge_list_of_lists(Sh1,NotCoupled),
	ord_subtract(Coupled,NotCoupled,NewGv),
	change_values_if_differ(NewGv,Fr,Fr1,g,f).

%-------------------------------------------------------------------------
% values_equal(+,+,+)                                                    |
% values_equal(Vars,Fr,Value)                                            |
% Satisfied if the freeness values of all variables in Vars is equal to  |
% Value.                                                                 |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

values_equal([],_,_).
values_equal([X|Xs],[Y/V|Ys],Value):-
	compare(D,X,Y),
	values_equal(D,X,Xs,V,Ys,Value).

values_equal(=,_X,Xs,Value,Ys,Value):-
	values_equal(Xs,Ys,Value).
values_equal(>,X,Xs,_,[Y/V|Ys],Value):-
	compare(D,X,Y),
	values_equal(D,X,Xs,V,Ys,Value).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% update_lambda_sf(+,+,+,-,-)                                            |
% update_lambda_sf(Gv,Fr,Sh,NewFr,NewSh)                                 |
% Identical to decide_update_lambda but since it is not call from the    |
% abstract unification, no test on the Hv is needed                      |
%-------------------------------------------------------------------------
update_lambda_sf([],Fr,Sh,Fr,Sh):- !.
update_lambda_sf(Gv,Fr,Sh,Fr1,Sh1):-
	ord_split_lists_from_list(Gv,Sh,Intersect,Sh1),
	merge_list_of_lists(Intersect,Coupled),
	merge_list_of_lists(Sh1,NotCoupled),
	ord_intersection_diff(Coupled,NotCoupled,NonFv,NewGv),
	change_values(NewGv,Fr,Temp_Fr,g),
	change_values_if_f(NonFv,Temp_Fr,Fr1,nf).

%-------------------------------------------------------------------------
% obtain_prime_var_var(+,+,-)                                            |
% obtain_prime_var_var([X/V,Y/V],Call,Success)                           |
% handles the case X = Y where both X,Y are variables which freeness     |
% value \== g                                                            |
%-------------------------------------------------------------------------
obtain_prime_var_var([X/f,Y/f],(Call_sh,Call_fr),Succ):- !,
	ord_split_lists(Call_sh,X,Intersect,Disjoint),
	ord_split_lists(Disjoint,Y,OnlyY,NonXY),
	ord_split_lists(Intersect,Y,XY,OnlyX),
	merge_lists(OnlyY,OnlyX,BothXY),
	merge(XY,NonXY,Succ1),
	merge(BothXY,Succ1,Succ_sh),
	Succ = (Succ_sh,Call_fr).
obtain_prime_var_var([X/_,Y/_],Call,Succ):-
	Prime = ([[X,Y]],[X/nf,Y/nf]),
	shfr_extend(Prime,[X,Y],Call,Succ).

%-------------------------------------------------------------------------

product(f,X,VarsY,_,Sh,Lda_fr,Prime_sh,Prime_fr):-
	share_project(VarsY,Sh,Temp),
	insert_each(Temp,X,Temp1),
	sort_list_of_lists(Temp1,Prime_sh),
	take_coupled(Sh,[X],Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
product(nf,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
	share_project(VarsY,Sh,Temp),
	closure_under_union(Temp,Temp1),
	merge_each([X],Temp1,Temp2),
	sort(Temp2,Prime_sh),
	take_coupled(Sh,Sv,Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
	
insert_each([],_,[]).
insert_each([L|Ls],X,[[X|L]|Rest]):-
	insert_each(Ls,X,Rest).

%-------------------------------------------------------------------------
% take_coupled(+,+,-)                                                    |
% take_coupled(Sh,Vars,Coupled)                                          |
% Sh is a list of lists of variables, Vars is a list of variables        |
% Returns in Coupled the list of variables X s.t. exists at least        |
% one list in Sh containing X and at least one element in Vars.          |
%-------------------------------------------------------------------------
take_coupled(Sh,Vars_u,Coupled):-
	sort(Vars_u,Vars),
	ord_split_lists_from_list(Vars,Sh,Intersect,_),
	merge_list_of_lists(Intersect,IntVars),
	merge(Vars,IntVars,Coupled).

%-------------------------------------------------------------------------
% change_values(+,+,-,+)                                                 %
% change_values(Vars,Fr,NewFr,Value)                                     %
% Forall X in Vars, there must exist an X/V in Fr. If so, it             %
% changes V to Value. Otherwise it fails                                 %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

change_values([],Ys,Ys,_).
change_values([X|Xs],[Y/V|Ys],Z,Value):-
	compare(D,X,Y),
	change_values(D,X,Y/V,Xs,Ys,Z,Value).

change_values(=,X,_,Xs,Ys,[X/Value|Z],Value):-
	change_values(Xs,Ys,Z,Value).
change_values(>,X,Y/Val,Xs,[Y1/V|Ys],[Y/Val|Z],Value):-
	compare(D,X,Y1),
	change_values(D,X,Y1/V,Xs,Ys,Z,Value).

:- pop_prolog_flag(multi_arity_warnings).
