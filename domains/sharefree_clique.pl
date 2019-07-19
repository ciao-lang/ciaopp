/*             Copyright (C)2004-2005 UNM-CLIP				*/

:- doc(author,"Jorge Navas").

:- use_module(domain(s_grshfr), 
        [change_values_insert/4,
	 create_values/3,
	 change_values_if_differ/5,
	 var_value/3,
	 projected_gvars/3]).
:- use_module(library(lists), [list_to_list_of_lists/2]).
:- use_module(library(terms_vars), [varset0/2,varset/2]).
:- use_module(domain(share_amgu)).
:- use_module(domain(s_grshfr),
        [collect_vars_freeness/2, member_value_freeness/3]).
:- use_module(library(lsets), [ord_intersect_lists/2, ord_split_lists/4]).
:- use_module(domain(sharefree_clique_aux)).
:- use_module(domain(sharefree_amgu_aux)).

%------------------------------------------------------------------------%
%                       CLIQUE-Sharing+Freeness domain                   % 
%------------------------------------------------------------------------%
% This file contains an extension (freeness) of the domain dependent     |
% abstract functions for the clique-sharing domain.                      |
%------------------------------------------------------------------------%
% The representation of this domain augments the Clique-sharing domain   |
% with a third component that keep track of freeness.                    |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharefree.pl                 
%------------------------------------------------------------------------%
%                                                                        |
%        programmer: J. Navas                                            |
%                                                                        |
%------------------------------------------------------------------------%

:- doc(bug,"1. In case of success multivariance the predicate
           eliminate_equivalent/2 must de redefined.").
:- doc(bug,"2. The builtin ==/2 is not defined.").
:- doc(bug,"3. The builtins read/2 and length/2 are defined in a 
           simple way.").
:- doc(bug,"4. The non-redundant version is not working because the 
	   semantics of the builtins has not been defined yet.").
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_call_to_entry(+,+,+,+,+,+,-,?)                        %
%-------------------------------------------------------------------------
sharefree_clique_call_to_entry(_,Sg,_Hv,Head,Fv,Proj,Entry,Flag):-
     variant(Sg,Head),!,
     Flag = yes,
     copy_term((Sg,Proj),(NewTerm,NewProj)),
     Head = NewTerm,
     sharefree_clique_sort(NewProj,((Temp_cl,Temp_sh),Temp_fr)),
     change_values_insert(Fv,Temp_fr,Entry_fr,f),	
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp_sh,New_Temp_sh),
     share_clique_normalize((Temp_cl,New_Temp_sh),Entry_SH),
     Entry = (Entry_SH,Entry_fr).
sharefree_clique_call_to_entry(_,_Sv,[],_Head,Fv,_Proj,Entry,no):- !,
     list_to_list_of_lists(Fv,Entry_sh),
     change_values_insert(Fv,[],Entry_fr,f),
     share_clique_normalize(([],Entry_sh),Entry_SH),
     Entry = (Entry_SH,Entry_fr).
sharefree_clique_call_to_entry(_Sv,Sg,Hv,Head,Fv,Proj,Entry,ExtraInfo):-
     peel_equations_frl(Sg,Head,Equations),
     sharefree_clique_extend_asub(Proj,Hv,ASub),     
     sharefree_clique_iterate(Equations,ASub,(ASub_SH,F)),
     share_clique_widen(plai_op,ASub_SH,_,SH),
     sharefree_clique_update_freeness(SH,F,Hv,F1),
     sharefree_clique_project((SH,F1),Hv,Entry0),
     sharefree_clique_extend_asub(Entry0,Fv,(Entry_SH0,Entry_Fr)),
     share_clique_normalize(Entry_SH0,Entry_SH),
     Entry = (Entry_SH,Entry_Fr),
     Proj = (_,F2),
     ExtraInfo = (Equations,F2),!.
sharefree_clique_call_to_entry(_Sv,_Sg,_Hv,_Head,_Fv,_Proj,'$bottom',_):-!.

%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_exit_to_prime(+,+,+,+,+,+,-)                          %
%-------------------------------------------------------------------------
sharefree_clique_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
sharefree_clique_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
     sharefree_clique_project(Exit,Hv,(BPrime_sh,BPrime_fr)),
     copy_term((Head,(BPrime_sh,BPrime_fr)),(NewTerm,NewPrime)),
     Sg = NewTerm,
     sharefree_clique_sort(NewPrime,(SH_Prime,Fr_Prime)),
     %eliminate_redundancies(SH_Prime,SH_Prime_N),
     %share_clique_normalize(SH_Prime,SH_Prime_N),
     SH_Prime = SH_Prime_N,
     Prime = (SH_Prime_N,Fr_Prime).
sharefree_clique_exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
     list_ground(Sv,Prime_fr),
     Prime = (([],[]),Prime_fr).
sharefree_clique_exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Call_Fr),	
     filter_freeness_with_call(Sv,Call_Fr,New_Sv),
     sharefree_clique_extend_asub(Exit,New_Sv,ASub),     
     sharefree_clique_iterate(Equations,ASub, (ASub_SH,F)),
     share_clique_widen(plai_op,ASub_SH,_,SH),
     sharefree_clique_update_freeness(SH,F,Sv,F1),
     sharefree_clique_project((SH,F1),Sv,(SH_Prime,Prime_Fr)),
     %eliminate_redundancies(SH_Prime,SH_Prime_N),
     %share_clique_normalize(SH_Prime,SH_Prime_N),
     SH_Prime = SH_Prime_N,
     Prime = (SH_Prime_N,Prime_Fr).

%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_amgu(+,+,+,-)                                         %
% sharefree_clique_amgu(Sg,Head,ASub,AMGU)                               %
% @var{AMGU} is the abstract unification between @var{Sg} and @var{Head}.%
%------------------------------------------------------------------------%
sharefree_clique_amgu(Sg,Head,ASub,AMGU):-
	peel_equations_frl(Sg, Head,Eqs),
	sharefree_clique_iterate(Eqs,ASub,AMGU),!.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_extend_asub(+,+,-)                                    %
%-------------------------------------------------------------------------
sharefree_clique_extend_asub(ASub,[],ASub).
sharefree_clique_extend_asub((SH,F),Vars,(SH1,F1)):-
	share_clique_extend_asub(SH,Vars,SH1),
	sharefree_amgu_extend_asub0(F,Vars,F1).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_extend(+,+,+,-)                                       |
% sharefree_clique_extend(Prime,Sv,Call,Succ)                            |
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ.             |
% Otherwise, Succ_sh is computed as in share_clique_extend/4,            |
% Call_fr is computed by:                                                |
%   * obtainig in NewGv the set of variables which have becomed ground   |
%   * adding this NewGv variables to Prime_fr, obtaining Temp1_fr        |
%   * obtaining in BVars the set of nonground variables in Succ which do |
%     not belong to Sg (ar not in Sv)                                    |
%   * Then it obtains in BVarsf the subset of BVars which are free w.r.t |
%     Call_fr, and in Temp2_fr, the result of adding X/nf to Temp1_fr    |
%     for the rest of variables in BVars                                 |
%   * If BVarsf = [],                                                    |
%------------------------------------------------------------------------%
sharefree_clique_extend('$bottom',_Sv,_Call,Succ):- !,
	Succ = '$bottom'.
sharefree_clique_extend(_Prime,[],Call,Succ):- !,
	Call = Succ.
sharefree_clique_extend((Prime_SH,Prime_fr),Sv,(Call_SH,Call_fr),(Succ_SH_N,Succ_fr)):-
%extend_SH
	share_clique_extend(Prime_SH,Sv,Call_SH,Succ_SH),
	Succ_SH = Succ_SH_N,
	%eliminate_redundancies(Succ_SH,Succ_SH_N),
        %share_clique_normalize(Succ_SH,Succ_SH_N),
%extend_fr
	member_value_freeness_differ(Call_fr,NonGvCall,g),
	Succ_SH_N = (Succ_Cl,Succ_Sh),
	merge_list_of_lists(Succ_Cl,NonGvSucc_Cl),
	merge_list_of_lists(Succ_Sh,NonGvSucc_Sh),
	ord_union(NonGvSucc_Cl,NonGvSucc_Sh,NonGvSucc),
	ord_subtract(NonGvCall,NonGvSucc,NewGv),
	change_values_insert(NewGv,Prime_fr,Temp1_fr,g),
	ord_subtract(NonGvSucc,Sv,BVars),
	non_free_vars(BVars,Call_fr,Temp1_fr,BVarsf,Temp2_fr),
	( BVarsf = [] ->
	  Temp3_fr = Temp2_fr
	; 
	  member_value_freeness(Prime_fr,NonFree,nf),
	  propagate_clique_non_freeness(BVarsf,NonFree,Succ_SH_N,Temp2_fr,Temp3_fr)
	),
	add_environment_vars(Temp3_fr,Call_fr,Succ_fr).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% sharefree_clique_project(+,+,-)                                        |
% sharefree_clique_project(ASub,Vars,Proj)                               |
%------------------------------------------------------------------------%
sharefree_clique_project('$bottom',_,'$bottom'):- !.
sharefree_clique_project((SH,F),Vars,(Proj_SH,Proj_F)) :-
	share_clique_project(Vars,SH,Proj_SH),
	project_freeness(Vars,F,Proj_F).

%------------------------------------------------------------------------%
% project_freeness(+,+,-)                                                %
% project_freeness(Vars,ListFreenessValues,Proj)                         %
% Defined in sharefree.pl, it should be exported by share.pl             %
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).

project_freeness([],_,Proj):- !,
	Proj = [].
project_freeness(_,[],Proj):- !,
	Proj = [].
project_freeness([Head1|Tail1],[Head2/Val|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	project_freeness(Order,Head1,Tail1,Head2/Val,Tail2,Proj).

project_freeness(=,_,Tail1,Head1,Tail2,[Head1|Proj]) :-
	project_freeness(Tail1,Tail2,Proj).
project_freeness(>,Head1,Tail1,_,[Head2/Val|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	project_freeness(Order,Head1,Tail1,Head2/Val,Tail2,Proj).

:- pop_prolog_flag(multi_arity_warnings).


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT SORT                                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_sort(+,-)                                             |
% sharefree_clique_sort(Asub,Asub_s)                                     |
% sorts the set of set of variables ASub to obtaint the Asub_s           |
%-------------------------------------------------------------------------
sharefree_clique_sort('$bottom','$bottom'):- !.
sharefree_clique_sort((SH,F),(Sorted_SH,Sorted_F) ):-
	share_clique_sort(SH,Sorted_SH),
	sort(F,Sorted_F).

%------------------------------------------------------------------------%
% sharefree_clique_identical_abstract(+,+)                               |
% sharefree_clique_less_or_equal(ASub0,ASub1)                            |
% Succeeds if the two abstract substitutions are defined on the same     |
% variables and are equivalent                                           |
%------------------------------------------------------------------------%
sharefree_clique_identical_abstract('$bottom','$bottom'):-!.
sharefree_clique_identical_abstract('$bottom',_):- !,fail.
sharefree_clique_identical_abstract(_,'$bottom'):- !,fail.
sharefree_clique_identical_abstract(ASub0,ASub1):-
	ASub0 == ASub1,!.
sharefree_clique_identical_abstract((SH0,Fr0),(SH1,Fr1)):-
	Fr0  == Fr1,!,
	share_clique_normalize(SH0,100,1,NSH0),!,
	( NSH0 == SH1 ->
	  true
        ;
	  share_clique_normalize(SH1,100,1,NSH1),
	  NSH0 == NSH1
        ).
%------------------------------------------------------------------------%
% sharefre_clique_eliminate_equivalent(+,-)                              |
% sharefre_clique_eliminate_equivalent(TmpLSucc,LSucc)                   |
% The list LSucc is reduced wrt the list TmpLSucc  in that it            | 
% does not contain abstract substitutions which are equivalent.          |
%------------------------------------------------------------------------%
sharefree_clique_eliminate_equivalent(TmpLSucc,Succ):-
	sort(TmpLSucc,Succ).

% sharefree_clique_eliminate_equivalent(TmpLSucc,Succ):-
% 	sort(TmpLSucc,TmpLSucc1),
% 	normalize_fr_abstract_substitutions(TmpLSucc1,Succ).

% normalize_fr_abstract_substitutions([],[]).
% normalize_fr_abstract_substitutions([(SH,Fr)|Ss],[(NSH,NFr)|Res]):-
% 	share_clique_normalize(SH,100,1,NSH),
% 	sort(Fr,NFr),
%         normalize_fr_abstract_substitutions(Ss,Res).

%------------------------------------------------------------------------%
% sharefree_clique_less_or_equal(+,+)                                    |
% sharefree_clique_less_or_equal(ASub0,ASub1)                            |
% Succeeds if ASub1 is more general or equal to ASub0                    |
%------------------------------------------------------------------------%
sharefree_clique_less_or_equal('$bottom',_ASub):- !.
sharefree_clique_less_or_equal((SH0,Fr0),(SH1,Fr1)):-
	share_clique_less_or_equal(SH0,SH1),
	member_value_freeness(Fr0,ListFr0,f),
	member_value_freeness(Fr1,ListFr1,f),
	ord_subset(ListFr1,ListFr0).
	
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts|
%------------------------------------------------------------------------%

%% sharefree_call_to_success_fact(_Sg,[],_Head,Sv,Call,_Proj,Prime,Succ) :- 
%% 	Call = (Call_SH,Call_fr),!,
%% 	update_lambda_cf(Sv,Call_fr,Call_SH,Succ_fr,Succ_SH),
%% 	list_ground(Sv,Prime_fr),
%% 	Prime = ([],Prime_fr),
%% 	%share_clique_normalize(Succ_SH,Succ_SH_R),
%% 	Succ_SH = Succ_SH_R,
%% 	Succ = (Succ_SH_R,Succ_fr).

sharefree_clique_call_to_success_fact(Sg,Hv,Head,Sv,Call,_Proj,Prime,Succ):-
% exit_to_prime
	sharefree_clique_extend_asub(Call,Hv,ASub),	
	peel_equations_frl(Sg, Head,Equations),
	sharefree_clique_iterate(Equations,ASub,(ASub_SH,F)),
	share_clique_widen(plai_op,ASub_SH,_,SH),
	%share_clique_normalize(SH,SH_N),
	SH = SH_N,
	ASub = (_,Vars), % Vars has both Sv and Hv
	unmap_freeness_list(Vars,Vars1),
	sharefree_clique_update_freeness(SH_N,F,Vars1,F1),
        ASub1=(SH_N,F1),
	sharefree_clique_project(ASub1,Sv,Prime),
% extend
	sharefree_clique_delete_variables(Hv,ASub1,Succ),!.
sharefree_clique_call_to_success_fact(_Sg,_Hv,_Head,_Sv,_Call,_Proj, '$bottom','$bottom').

sharefree_clique_delete_variables(Vars,((Cl,Sh),Fr),((New_Cl,New_Sh),New_Fr)):-
	delete_vars_from_list_of_lists(Vars,Sh,Sh0),
	sort_list_of_lists(Sh0,New_Sh),
	delete_vars_from_list_of_lists(Vars,Cl,Cl0),
	sort_list_of_lists(Cl0,New_Cl),	
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
sharefree_clique_call_to_prime_fact(Sg,Hv,Head,Sv,(_SH,Extra_Info),Prime) :-
	sharefree_clique_extend_asub((_SH,Extra_Info),Hv,Exit),
	sharefree_clique_exit_to_prime(Sg,Hv,Head,Sv,Exit,Extra_Info,Prime).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT LUB                                      %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% sharefree_clique_compute_lub(+,-)                                      |
% sharefree_clique_compute_lub(ListASub,Lub)                             |
% It computes the lub of a set of Asub. For each two abstract            |
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   |
% merging the ASub1 and ASub2.                                           |
%------------------------------------------------------------------------%
sharefree_clique_compute_lub([ASub1,ASub2|Rest],Lub) :- !,
	sharefree_clique_compute_lub_el(ASub1,ASub2,ASub3),
	sharefree_clique_compute_lub([ASub3|Rest],Lub).
sharefree_clique_compute_lub([ASub],ASub).

sharefree_clique_compute_lub_el('$bottom',ASub,ASub):- !.
sharefree_clique_compute_lub_el(ASub,'$bottom',ASub):- !.
sharefree_clique_compute_lub_el((Cl1,Fr1),(Cl2,Fr2),(Lub_cl,Lub_fr)):- !,
	share_clique_lub_cl(Cl1,Cl2,Lub_cl),
	compute_lub_fr(Fr1,Fr2,Lub_fr).
sharefree_clique_compute_lub_el(ASub,_,ASub).

% defined in sharefree.pl, it should be exported by share.pl
compute_lub_fr(Fr1,Fr2,Lub):- 
	Fr1 == Fr2, !,
	Lub = Fr1.
compute_lub_fr([Xv|Fr1],[Yv|Fr2],Lub):- 
	Xv == Yv, !,
	Lub = [Xv|Lub_fr],
	compute_lub_fr(Fr1,Fr2,Lub_fr).
compute_lub_fr([X/_|Fr1],[X/_|Fr2],[X/nf|Lub_fr]):-
	compute_lub_fr(Fr1,Fr2,Lub_fr).

%------------------------------------------------------------------------%
% sharefree_clique_glb(+,+,-)                                            |
% sharefree_clique_glb(ASub0,ASub1,Lub)                                  |
% Glb is just intersection.                                              |
%------------------------------------------------------------------------%
sharefree_clique_glb((SH1,Fr1),(SH2,Fr2),Glb):-
	member_value_freeness(Fr1,FVars1,f),
	member_value_freeness(Fr2,FVars2,f),
	member_value_freeness(Fr1,GVars1,g),
	member_value_freeness(Fr2,GVars2,g),
	ord_intersection(FVars1,GVars2,Empty1),
	ord_intersection(FVars2,GVars1,Empty2),
	( (Empty1 \== []; Empty2 \== [])
	-> Glb = '$bottom'
	 ; merge(FVars1,FVars2,FVars),
	   merge(GVars1,GVars2,GVars0),
	   share_clique_glb(SH1,SH2,Glb_SH),
	   varset(Fr1,All),
	   Glb_SH = (Gb_Cl,Gb_Sh),
	   varset(Gb_Cl,Gb_ClVx),
	   varset(Gb_Sh,Gb_ShVx),
	   ord_union(Gb_ClVx,Gb_ShVx,Now),
	   ord_subtract(All,Now,NewGVars),
	   merge(GVars0,NewGVars,GVars),
	   ord_intersection(FVars,GVars,Empty),
	   ( Empty \== []
	   -> Glb = '$bottom'
	    ; Glb = (Glb_SH,Glb_fr),
	      change_values_insert(FVars,Fr1,TmpFr,f),
	      change_values_insert(GVars,TmpFr,Glb_fr,g)
	)  ).

%------------------------------------------------------------------------%
% sharefree_clique_input_user_interface(+,+,-)                           |
% sharefree_clique_input_user_interface(InputUser,Qv,ASub)               |
% Obtaining the abstract substitution for Cl+Fr from the user supplied   |
% information just consists in taking th Cliques first and the var(Fv)   |
% element of InputUser, and construct from them the Freeness.            |
%------------------------------------------------------------------------%
sharefree_clique_input_user_interface((SH,Fv0),Qv,(Call_SH,Call_fr)):-
	share_clique_input_user_interface(SH,Qv,Call_SH),
%% freeness  
	may_be_var(Fv0,Fv),
	Call_SH = (Cl,Sh),
	merge_list_of_lists(Cl,SH1v),						
	merge_list_of_lists(Sh,SH2v),
	ord_union(SH1v,SH2v,SHv),
	ord_subtract(Qv,SHv,Gv),
	ord_subtract(SHv,Fv,NonFv),
	create_values(Fv,Temp1,f),
	change_values_insert(NonFv,Temp1,Temp2,nf),
	change_values_insert(Gv,Temp2,Call_fr,g).

sharefree_clique_input_interface(free(X),perfect,(SH,Fr0),(SH,Fr)):-
	var(X),
	myinsert(Fr0,X,Fr).
sharefree_clique_input_interface(Prop,Any,(SH0,Fr),(SH,Fr)):-
	share_clique_input_interface(Prop,Any,SH0,SH), !.

myinsert(Fr0,X,Fr):-
	var(Fr0), !,
	Fr = [X].
myinsert(Fr0,X,Fr):-
	insert(Fr0,X,Fr).

%------------------------------------------------------------------------%
% sharefree_clique_asub_to_native(+,+,-)                                 |
% sharefree_clique_asub_to_native(ASub,Qv,ASub_user)                     |
% The user friendly format consists in extracting the ground variables   |
% and the free variables                                                 |
%------------------------------------------------------------------------%
sharefree_clique_asub_to_native((SH,Fr),_Qv,Info):-
	SH = (Cl,Sh),
	if_not_nil(Cl,clique(Cl),Info,Info0),
	if_not_nil(Sh,sharing(Sh),Info0,Info1),
	member_value_freeness(Fr,Fv,f),
	if_not_nil(Fv,free(Fv),Info1,Info2),
	member_value_freeness(Fr,Gv,g),
	if_not_nil(Gv,ground(Gv),Info2,[]).

%------------------------------------------------------------------------%
% sharefree_clique_unknown_call(+,+,-)                                   |
% sharefree_clique_unknown_call(Call,Vars,Succ)                          |
%------------------------------------------------------------------------%
sharefree_clique_unknown_call('$bottom',_Vars,'$bottom').
sharefree_clique_unknown_call((Call_SH,Call_fr),Vars,(Succ_SH,Succ_fr)):-
        rel_w(Vars,Call_SH,Intersect),
	irrel_w(Vars,Call_SH,Rest),
	star_w(Intersect,Star),
	ord_union_w(Star,Rest,Succ_SH),
	Intersect = (Int_Cl,Int_Sh),
	ord_union(Int_Cl,Int_Sh,Int_All),	
	merge_list_of_lists(Int_All,Nonfree_vars),
	change_values_if_f(Nonfree_vars,Call_fr,Succ_fr,nf).

%------------------------------------------------------------------------%
% sharefree_clique_empty_entry(+,-)                                      |
% sharefree_clique_empty_entry(Vars,Entry)                               |
% The empty value in Sh for a set of variables is the list of singletons,|
% in Fr is X/f forall X in the set of variables                          |            
%------------------------------------------------------------------------%
sharefree_clique_empty_entry(Qv,Entry):-
	list_to_list_of_lists(Qv,Entry_sh),	
	create_values(Qv,Entry_fr,f),
	Entry=(([],Entry_sh),Entry_fr).

%------------------------------------------------------------------------%
% sharecli_unknown_entry(+,-)                                            |
% sharecli_unknown_entry(Qv,Call)                                        |
% The top value in Sharing for a set of variables is the powerset, in Fr |
% X/nf forall X in the set of variables.                                 |    
%------------------------------------------------------------------------%
sharefree_clique_unknown_entry(Qv,Call):-
	sort(Qv,QvS),
	create_values(Qv,Call_fr,nf),
	Call = (([QvS],[]),Call_fr).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              |
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% sharefree_clique_special_builtin(+,+,-,-)                              |
% sharefree_clique_special_builtin(SgKey,Sg,Type,Condvars)               |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
% (1) new_ground if the builtin makes all variables ground whithout      |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) old_ground if the builtin requires the variables to be ground      |
% (3) old_new_ground" if the builtin requires some variables to be       |
%     ground and grounds the rest                                        |
% (4) unchanged if we cannot infer anything from the builtin, the        |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previo
% (5) some if it makes some variables ground without imposing conditions |
% (6) all_nonfree if the builtin makes all variables possible non free   |
% (6) Sgkey, special handling of some particular builtins                |
%------------------------------------------------------------------------%
% list/1 is not defined
%------------------------------------------------------------------------%
% TODO: add cuts?
sharefree_clique_special_builtin('read/2',read(X,Y),'recorded/3',p(Y,X)).
sharefree_clique_special_builtin('length/2',length(_X,Y),some,[Y]).
sharefree_clique_special_builtin('==/2',_,_,_):- !, fail.
sharefree_clique_special_builtin(SgKey,Sg,Type,Condvars):-
	shfr_special_builtin(SgKey,Sg,Type,Condvars).
	
%------------------------------------------------------------------------%
% sharefree_clique_success_builtin(+,+,+,+,-)                            |
% sharefree_clique_success_builtin(Type,Sv_u,Condv,Call,Succ)            |
% Obtains the success for some particular builtins:                      |
%  * If Type = new_ground, it updates Call making all vars in Sv_u ground|
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * If Type = old_ground, if grouds all variables in Sv and checks that |
%              no free variables has becomed ground                      |
%  * If Type = old_ground, if grounds all variables in OldG and checks   |
%              thatno free variables has becomed ground. If so, it       |
%              grounds all variables in NewG                             |
%  * If Type = all_non_free it projects Call onto this variables,        |
%              obatins the closure under union for the Sh, changes in    |
%              Fr all f to nf and later extends the result               |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%------------------------------------------------------------------------%
% NOTE: In comparison with shfr, the following builtins are not defined: |
% - list/1                                                               |
%------------------------------------------------------------------------%
sharefree_clique_success_builtin(new_ground,Sv_u,_,Call,Succ):-
	sort(Sv_u,Sv),
	Call = (Lda_SH,Lda_fr),
	update_lambda_cf(Sv,Lda_fr,Lda_SH,Succ_fr,Succ_SH), 
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin(bottom,_,_,_,'$bottom').
sharefree_clique_success_builtin(unchanged,_,_,Lda,Lda).
sharefree_clique_success_builtin(some,_Sv,NewGr,Call,Succ):-
	Call = (Call_SH,Call_fr),
	update_lambda_cf(NewGr,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin(old_ground,Sv_u,_,Call,Succ):-
	sort(Sv_u,Sv),
	Call = (Call_SH,Call_fr),
	update_lambda_clique_non_free(Sv,Call_fr,Call_SH,Succ_fr,Succ_SH),!,
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin(old_ground,_,_,_,'$bottom').
sharefree_clique_success_builtin(old_new_ground,_,(OldG,NewG),Call,Succ):-
	Call = (Call_SH,Call_fr),
	update_lambda_clique_non_free(OldG,Call_fr,Call_SH,Temp_fr,Temp_SH),!,
	update_lambda_cf(NewG,Temp_fr,Temp_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin(old_new_ground,_,_,_,'$bottom').
sharefree_clique_success_builtin(all_nonfree,Sv_u,_,Call,Succ):- !,
	sort(Sv_u,Sv),
	sharefree_clique_project(Call,Sv,(Proj_SH,Proj_fr)),!,
	star_w(Proj_SH,Prime_SH),
	change_values_if_f(Sv,Proj_fr,Prime_fr,nf),
	sharefree_clique_extend((Prime_SH,Prime_fr),Sv,Call,Succ).
% special builtins
sharefree_clique_success_builtin(arg,_,p(X,Y,Z),Call,Succ):-
	Call = (Call_SH,Call_fr),
	varset(X,OldG),
	update_lambda_clique_non_free(OldG,Call_fr,Call_SH,Temp_fr,Temp_SH),
	var_value(Temp_fr,Y,Value),
	Value \== f,!,
	Sg = p(Y,Z),
	Head = p(f(A,_B),A),
	varset(Sg,Sv),
	varset(Head,Hv),
	TempASub = (Temp_SH,Temp_fr),
	sharefree_clique_project(TempASub,Sv,Proj),
	sharefree_clique_call_to_success_fact(Sg,Hv,Head,Sv,TempASub,Proj,_,Succ).
sharefree_clique_success_builtin(arg,_,_,_,'$bottom').
sharefree_clique_success_builtin(exp,_,Sg,Call,Succ):-
	Head = p(A,f(A,_B)),
	varset(Sg,Sv),
	varset(Head,Hv),
	sharefree_clique_project(Call,Sv,Proj),
	sharefree_clique_call_to_success_fact(Sg,Hv,Head,Sv,Call,Proj,_,Succ).
sharefree_clique_success_builtin(exp,_,_,_,'$bottom').
sharefree_clique_success_builtin('=../2',_,p(X,Y),(Call_SH,Call_fr),Succ):-
	varset(X,Varsx),
	values_equal(Varsx,Call_fr,g),!,
	varset(Y,VarsY),
	update_lambda_cf(VarsY,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('=../2',_,p(X,Y),(Call_SH,Call_fr),Succ):-
	varset(Y,VarsY),
	values_equal(VarsY,Call_fr,g),!,
	varset(X,VarsX),
	update_lambda_cf(VarsX,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('=../2',Sv_uns,p(X,Y),Call,Succ):-
	var(X), var(Y),!,
	sort(Sv_uns,Sv),
	Call = (_,Call_fr),
	project_freeness(Sv,Call_fr,[A/Val1,B/Val2]),
	( obtain_freeness(Val1,Val2) ->
	    sharefree_clique_extend((([],[Sv]),[A/nf,B/nf]),Sv,Call,Succ)
	; Succ = '$bottom'
        ).
sharefree_clique_success_builtin('=../2',Sv_uns,p(X,Y),Call,Succ):-
	var(X), !,
	sort(Sv_uns,Sv),
	Call = (Call_SH,Call_fr),	
	project_freeness(Sv,Call_fr,Proj_fr),
	Y = [Z|_],
	var_value(Proj_fr,X,ValueX),
	( var(Z) ->
	    var_value(Proj_fr,Z,ValueZ),
	    ( ValueZ = f , ValueX = f ->
		Succ = '$bottom'
	    ; ord_subtract(Sv,[Z],NewVars),
	      share_clique_project(NewVars,Call_SH,Proj_SH),
	      ord_subtract(NewVars,[X],VarsY),
	      product_clique(ValueX,X,VarsY,Sv,Proj_SH,Proj_fr,Prime_SH,Prime_fr),
	      sharefree_clique_extend((Prime_SH,Prime_fr),Sv,Call,Succ)
	    )
	; share_clique_project(Sv,Call_SH,Proj_SH),
	  ord_subtract(Sv,[X],VarsY),
	  product_clique(ValueX,X,VarsY,Sv,Proj_SH,Proj_fr,Prime_SH,Prime_fr),
	  sharefree_clique_extend((Prime_SH,Prime_fr),Sv,Call,Succ)
        ).
sharefree_clique_success_builtin('=../2',Sv_uns,p(X,Y),Call,Succ):-
	X =.. T,
	sort(Sv_uns,Sv),
	sharefree_clique_project(Call,Sv,Proj),
	sharefree_clique_call_to_success_builtin('=/2','='(T,Y),Sv,Call,Proj,Succ).
sharefree_clique_success_builtin(recorded,_,p(Y,Z),Call,Succ):-
        varset(Z,NewG),
	varset(Y,VarsY),
	merge(NewG,VarsY,Vars),
	sharefree_clique_project(Call,Vars,(SH,Fr)),
	update_lambda_cf(NewG,Fr,SH,TempPrime_fr,TempPrime_SH),
	make_clique_dependence(TempPrime_SH,VarsY,TempPrime_fr,Prime_fr,Prime_SH),
	Prime = (Prime_SH,Prime_fr),
	sharefree_clique_extend(Prime,Vars,Call,Succ).
sharefree_clique_success_builtin(copy_term,_,p(X,Y),Call,Succ):-
	varset(X,VarsX),
	sharefree_clique_project(Call,VarsX,ProjectedX),
	copy_term((X,ProjectedX),(NewX,NewProjectedX)),
	sharefree_clique_sort(NewProjectedX,ProjectedNewX),
	varset(NewX,VarsNewX),
	varset(Y,VarsY),
	merge(VarsNewX,VarsY,TempSv),
	sharefree_clique_project(Call,VarsY,ProjectedY),
	ProjectedY = (SHY,FrY),
	ProjectedNewX = (SHNewX,FrNewX),
        ord_union_w(SHY,SHNewX,TempSH), 
	merge(FrY,FrNewX,TempFr),
	Call = (SHCall,FrCall),
        ord_union_w(SHNewX,SHCall,TempCallSH),
	merge(FrNewX,FrCall,TempCallFr),
	sharefree_clique_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                    (TempCallSH,TempCallFr),(TempSH,TempFr),Temp_success),
	collect_vars_freeness(FrCall,VarsCall),
	sharefree_clique_project(Temp_success,VarsCall,Succ).
sharefree_clique_success_builtin('current_key/2',_,p(X),Call,Succ):-
	varset(X,NewG),
	Call = (Call_SH,Call_fr),
	update_lambda_cf(NewG,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('current_predicate/2',_,p(X,Y),Call,Succ):-
	var(Y),!,
	Call = (Call_SH,Call_fr),
	change_values_if_f([Y],Call_fr,Temp_fr,nf), 
	varset(X,NewG),
	update_lambda_cf(NewG,Temp_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('current_predicate/2',_,p(X,_Y),Call,Succ):- !,
	Call = (Call_SH,Call_fr),
	varset(X,NewG),
	update_lambda_cf(NewG,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin(findall,_,p(X,Z),(Call_SH,Call_fr),(Succ_SH,Succ_fr)):-
	varset(X,Xs),
	member_value_freeness(Call_fr,GVars,g),
	ord_subset(Xs,GVars), !,
	varset(Z,Zs),
	update_lambda_cf(Zs,Call_fr,Call_SH,Succ_fr,Succ_SH).
sharefree_clique_success_builtin(findall,_,_,Call,Call).
%
sharefree_clique_success_builtin('functor/3',_,p(X,Y,Z),Call,Succ):-
	var(X),
	Call = (Call_SH,Call_fr),
	var_value(Call_fr,X,f),!,
	change_values([X],Call_fr,Temp_fr,nf), 
	varset([Y,Z],OldG),
	( update_lambda_clique_non_free(OldG,Temp_fr,Call_SH,Succ_fr,Succ_SH) ->
	  Succ = (Succ_SH,Succ_fr)
	; Succ = '$bottom'
	).
sharefree_clique_success_builtin('functor/3',_,p(_X,Y,Z),Call,Succ):- !,
	Call = (Call_SH,Call_fr),
	varset([Y,Z],NewG),
	update_lambda_cf(NewG,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('name/2',_,p(X,Y),Call,Succ):-
        varset(X,OldG),
	Call = (Call_SH,Call_fr),
	update_lambda_clique_non_free(OldG,Call_fr,Call_SH,Temp_fr,Temp_SH),!,
        varset(Y,NewG),
	update_lambda_cf(NewG,Temp_fr,Temp_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('name/2',_,p(X,Y),Call,Succ):-
        varset(Y,OldG),
	Call = (Call_SH,Call_fr),
	update_lambda_clique_non_free(OldG,Call_fr,Call_SH,Temp_fr,Temp_SH),!,
        varset(X,NewG),
	update_lambda_cf(NewG,Temp_fr,Temp_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('name/2',_,_,_,'$bottom').
sharefree_clique_success_builtin('nonvar/1',_,p(X),Call,Succ):-
        var(X), !,
	Call = (_Call_SH,Call_fr),
	var_value(Call_fr,X,Val),
	( Val = f ->
	  Succ = '$bottom'
	; Succ = Call
	).
sharefree_clique_success_builtin('nonvar/1',_,_,Call,Call):- !.
sharefree_clique_success_builtin('numbervars/3',_,p(X,Y,Z),Call,Succ):-
	Call = (Call_SH,Call_fr),
	varset(Y,OldG),
	update_lambda_clique_non_free(OldG,Call_fr,Call_SH,Temp_fr,Temp_SH),!,
	varset(p(X,Z),NewG),
	update_lambda_cf(NewG,Temp_fr,Temp_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('numbervars/3',_,_,_,'$bottom').
sharefree_clique_success_builtin('compare/3',_,p(X),Call,Succ):- 
        atom(X),!,
	Succ = Call.
sharefree_clique_success_builtin('compare/3',_,p(X),Call,Succ):- 
        var(X),!,
	Call = (Call_SH,Call_fr),
	update_lambda_cf([X],Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_success_builtin('compare/3',_,_,_,'$bottom').
sharefree_clique_success_builtin('indep/2',_,p(X,Y),Call,Succ):- 
	( ground(X) ; ground(Y) ), !,
	Succ = Call.
sharefree_clique_success_builtin('indep/2',_,p(X,Y),Call,Succ):- 
	varset(X,Xv),
	varset(Y,Yv),
	Call = ((Call_Cl,Call_Sh),Call_fr),
	varset(Call_fr,Vars),        
	eliminate_couples_clique(Call_Cl,Xv,Yv,Succ_Cl),
	eliminate_couples(Call_Sh,Xv,Yv,Succ_Sh),
	ord_union(Succ_Cl,Succ_Sh,Succ_SH),
	projected_gvars(Succ_SH,Vars,Ground),
	change_values_if_differ(Ground,Call_fr,Succ_fr,g,f),!,
	Succ = ((Succ_Cl,Succ_Sh),Succ_fr).
sharefree_clique_success_builtin('indep/2',_,_,_,'$bottom').
sharefree_clique_success_builtin('indep/1',_,p(X),Call,Succ):- 
	nonvar(X),
	handle_each_indep(X,sharefree_clique,Call,Succ), !.  
sharefree_clique_success_builtin('indep/1',_,_,_,'$bottom').

sharefree_clique_success_builtin('var/1',[X],p(X),Call,Succ):- 
	Call = (Call_SH,Call_fr),
	var_value(Call_fr,X,Valuex),
	Valuex \== g,
	change_values([X],Call_fr,Succ_fr,f),
	Succ = (Call_SH,Succ_fr), !.
sharefree_clique_success_builtin('var/1',_,_,_,'$bottom').
sharefree_clique_success_builtin('free/1',[V],p(V),Call,Succ) :- !,
        sharefree_clique_success_builtin('var/1',[V],p(V),Call,Succ).

%------------------------------------------------------------------------%
% sharefree_clique_call_to_success_builtin(+,+,+,+,+,-)                  |
% sharefree_clique_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)   |
% Handles those builtins for which computing Prime is easier than Succ   |
%------------------------------------------------------------------------%
sharefree_clique_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr),Succ):-
	varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
	Call = (Call_SH,Call_fr),
	ord_subtract(Sv,VarsX,VarsY),
	update_lambda_cf(VarsY,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr),Succ):-
	varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
	Call = (Call_SH,Call_fr),
	ord_subtract(Sv,VarsY,VarsX),
	update_lambda_cf(VarsX,Call_fr,Call_SH,Succ_fr,Succ_SH),
	Succ = (Succ_SH,Succ_fr).
sharefree_clique_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	var(X),var(Y), !,
	Proj = (_,Proj0_fr),	
	project_freeness(Sv,Proj0_fr,Proj_fr),  %% necessary for def
	obtain_prime_clique_var_var(Proj_fr,Call,Succ).
sharefree_clique_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
	var(X), !,
	Proj = (Proj_SH,Proj_fr),	
	ord_subtract(Sv,[X],VarsY),
	var_value(Proj_fr,X,ValueX),
	product_clique(ValueX,X,VarsY,Sv,Proj_SH,Proj_fr,Prime_SH,Prime_fr),
	Prime= (Prime_SH,Prime_fr),
	sharefree_clique_extend(Prime,Sv,Call,Succ).
sharefree_clique_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,!,
	varset(Xterm,Vars),
	sharefree_clique_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),Sv,
	        Call,Proj,_Prime,Succ).
sharefree_clique_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom'):-!.
sharefree_clique_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
	sharefree_clique_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),Sv,
	        Call,Proj,_Prime,Succ).
sharefree_clique_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	var(X), !,
	Proj = (_SH,Fr),
	var_value(Fr,X,Val),
	( Val = f ->
	  Succ = '$bottom'
	; varset([X,Y],Sv),
	  copy_term(Y,Yterm),
	  varset(Yterm,Vars),
	  sharefree_clique_call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),Sv,
	               Call,Proj,_Prime,Succ)
	).
sharefree_clique_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	functor(X,'.',_), !,
	varset0(X,[Z|_]),
	Call = (Call_SH,Call_fr),
	change_values_if_f([Z],Call_fr,Temp_fr,nf),
	varset([X,Y],Sv),
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,
	varset(Xterm,Vars),
	Proj = (SH,Fr),
	change_values_if_f([Z],Fr,TFr,nf),
	sharefree_clique_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),Sv,
	        (Call_SH,Temp_fr),(SH,TFr),_Prime,Succ). 
sharefree_clique_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
	sharefree_clique_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      Intermediate operations                           |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Most of the following operations are defined in sharefree.pl           | 
% They should be exported by share.pl (they are defined in sharefree.pl) |
%------------------------------------------------------------------------%

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

%-------------------------------------------------------------------------
% update_lambda_clique_non_free(+,+,+,-,-)                               |
% update_lambda_clique_non_free(Gv,Fr,Sh,NewFr,NewSh)                    |
% Identical to update_lambda_sf but:                                     |
% *  it tests that the variables that become ground are not free.        |
%    The reason is that Ground should be ground already, and therefore   |
%    they cannot make a definitely free variable to become ground        |
% *  it does not change the freeness value of any variable from f to nf  |
%    The same reason                                                     |
%-------------------------------------------------------------------------
update_lambda_clique_non_free([],Fr,Sh,Fr,Sh).
update_lambda_clique_non_free([X|Xs],Fr,SH,Fr1,SH1):-
	rel_w([X|Xs],SH,(Int_Cl,Int_Sh)),
	irrel_w([X|Xs],SH,(Disj_Cl,Disj_Sh)),
        ord_union(Int_Cl,Int_Sh,Int),
        ord_union(Disj_Cl,Disj_Sh,Disj),
	merge_list_of_lists(Int,Coupled),
	merge_list_of_lists(Disj,NotCoupled),
	ord_subtract(Coupled,NotCoupled,NewGv),
	change_values_if_differ(NewGv,Fr,Fr1,g,f),
	SH1= (Cl1,Disj_Sh),
	delete_vars_from_list_of_lists([X|Xs],Int_Cl,Cl2),
	sort_list_of_lists(Cl2,Cl2_sorted),
	ord_union(Cl2_sorted,Disj_Cl,Cl1).
	
%------------------------------------------------------------------------%
% update_lambda_cf(+,+,+,-,-)                                            |
% update_lambda_cf(Gv,Fr,Sh,NewFr,NewSh)                                 |
% This predicates handles the case in which a set of variables (Gv) have |
% been determined as ground, and it has to:                              |
%   - Update the sharing&clique component                                |
%   - Update the freeness component in order to:                         |
%         - all ground variables appear as ground                        |
%         - those free variables which are coupled (but not are become   |
%           ground) should become non free.                              |
%------------------------------------------------------------------------%
update_lambda_cf([],Fr,Sh,Fr,Sh):- !.
update_lambda_cf(Gv,Fr,SH,Fr1,SH1):-
	rel_w(Gv,SH,(Int_Cl,Int_Sh)),
	irrel_w(Gv,SH,(Disj_Cl,Disj_Sh)),
        ord_union(Int_Cl,Int_Sh,Int),
        ord_union(Disj_Cl,Disj_Sh,Disj),
	merge_list_of_lists(Int,Coupled),
	merge_list_of_lists(Disj,NotCoupled),
	ord_intersection_diff(Coupled,NotCoupled,NonFv,NewGv),
	change_values(NewGv,Fr,Temp_Fr,g),
	change_values_if_f(NonFv,Temp_Fr,Fr1,nf),
	SH1= (Cl1,Disj_Sh),
	delete_vars_from_list_of_lists(Gv,Int_Cl,Cl2),
	sort_list_of_lists(Cl2,Cl2_sorted),
	ord_union(Cl2_sorted,Disj_Cl,Cl1).

% TODO:!!
obtain_freeness(f,f):- !, fail.
obtain_freeness(_,_).

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

%% %-------------------------------------------------------------------------
%% % mynonvar(+,+,+)                                                        |
%% % mynonvar(Vars,Fr,Fv)                                                   |
%% % Satisfied if the variables in Vars are definitely nonvariables         |
%% %-------------------------------------------------------------------------
%% 
%% mynonvar([],_Sh,_Free).
%% mynonvar([F|Rest],Sh,Free):-
%% 	insert(Free,F,Vars),
%% 	share_project(Vars,Sh,NewSh),
%% 	impossible(NewSh,NewSh,Vars),!,
%% 	mynonvar(Rest,Sh,Free).

%-------------------------------------------------------------------------
% propagate_non_freeness(+,+,+,+,-)                                      |
% propagate_non_freeness(Vars,NonFv,Sh,Fr,NewFr)                         |
% NewFr is the result of inserting each variable in Vars with value nf,  |
% if it appears in Sh with a nonfree variable. Otherwise it inserts X/f. |
%-------------------------------------------------------------------------
propagate_non_freeness([],_,_,Fr,Fr).
propagate_non_freeness([X|Xs],NonFv,Sh,[Y/Value|Fr],NewFr):-
        X @> Y, !,
	NewFr = [Y/Value|RestNewFr],
        propagate_non_freeness([X|Xs],NonFv,Sh,Fr,RestNewFr).
propagate_non_freeness([X|Xs],NonFv,Sh,Fr,NewFr):-
	ord_split_lists(Sh,X,Sh_Subs,_),
	ord_intersect_lists(NonFv,Sh_Subs), !,
	NewFr = [X/nf|RestNewFr],
	propagate_non_freeness(Xs,NonFv,Sh,Fr,RestNewFr).
propagate_non_freeness([X|Xs],NonFv,Sh,Fr,[X/f|NewFr]):- 
	propagate_non_freeness(Xs,NonFv,Sh,Fr,NewFr).

%-------------------------------------------------------------------------
% add_environment_vars(+,+,-)                                            |
% add_environment_vars(Fr1,Fr2, NewFr).                                  |
% Fr2 contains all variables in Fr1 and possibly new ones (Fr1           |
% corresponds to a prime while Fr2 corresponds to a call)                |
% Then, NewFr = Fr1 + {X/V in Fr2| X/_ \notin Fr1}                       |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

add_environment_vars([],Fr2,Fr2).
add_environment_vars([Y/Vy|Fr1],[X/V|Fr2],NewFr):- 
	compare(D,X,Y),
	add_environment_vars(D,Y/Vy,Fr1,X/V,Fr2,NewFr).

add_environment_vars(=,Elem,Fr1,_,Fr2,[Elem|NewFr]):-
	add_environment_vars(Fr1,Fr2,NewFr).
add_environment_vars(<,Y/Vy,Fr1,El,[X/V|Fr2],[El|NewFr]):-
	compare(D,X,Y),
	add_environment_vars(D,Y/Vy,Fr1,X/V,Fr2,NewFr).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% member_value_freeness_differ(+,-,+)                                    |
% member_value_freeness_differ(Fr,Vars,Value)                            |
% It returns in Vars the list of variables with freeness value different |
% from Value                                                             |
%-------------------------------------------------------------------------
member_value_freeness_differ([],[],_).
member_value_freeness_differ([X/Valuex|Rest],ListValue,Value):- 
	Valuex \== Value,!,
	ListValue = [X|More],
	member_value_freeness_differ(Rest,More,Value).
member_value_freeness_differ([_|Rest],ListValue,Value):- 
	member_value_freeness_differ(Rest,ListValue,Value).

%-------------------------------------------------------------------------
% non_free_vars(+,+,+,-,-)                                               %
% non_free_vars(Vars,Fr1,Fr2,Fv,NewFr).                                  %
% NewFr is the result of adding to Fr2 all X/nf s.t. X in Vars and X/nf  %
% in Fr1 (Note that if X in Vars, then X/_ not in Fr2).                  %
% Fv contains the rest of variables in Vars. All Ordered                 %
% The reason is the following: Vars is the set of variables in success   %
% and not in prime. Thus, those variables in Vars with value in Call     %
% different from nf are free, and should be added to BVarsf.             %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).
% TODO: change names for different arities?
non_free_vars([],_,Fr2,[],Fr2).
non_free_vars([X|Xs],Fr1,Fr2,BVarsf,NewFr):-
	non_free_vars(Fr2,X,Xs,Fr1,BVarsf,NewFr).

non_free_vars([],X,Xs,[Y/V|Fr1],BVarsf,NewFr):-
	compare(D,X,Y),
	non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
non_free_vars([Y/V|Fr2],X,Xs,Fr1,BVarsf,NewFr):-
	compare(D,X,Y),
	non_free_vars(D,X,Xs,Fr1,Y/V,Fr2,BVarsf,NewFr).

non_free_vars(>,X,Xs,Fr1,Elem,Fr2,BVarsf,[Elem|NewFr]):-
	non_free_vars(Fr2,X,Xs,Fr1,BVarsf,NewFr).
non_free_vars(<,X,Xs,Fr1,Elem,Fr2,BVarsf,NewFr):-
	var_value_rest(Fr1,X,nf,New_Fr1,Flag),
	non_free_vars(Flag,X,Xs,New_Fr1,[Elem|Fr2],BVarsf,NewFr).

non_free_vars1(>,X,Xs,_,[Y/V|Fr1],BVarsf,NewFr):-
	compare(D,X,Y),
	non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
non_free_vars1(=,X,Xs,V,Fr1,BVarsf,NewFr):-
	V = nf,!,
	NewFr = [X/nf|Rest_temp2],
	non_free_vars2(Xs,Fr1,BVarsf,Rest_temp2).
non_free_vars1(=,X,Xs,_V,Fr1,[X|BVarsf],NewFr):-
	non_free_vars2(Xs,Fr1,BVarsf,NewFr).

non_free_vars2([],_Fr1,[],[]).
non_free_vars2([X|Xs],[Y/V|Fr1],BVarsf,NewFr):-
	compare(D,X,Y),
	non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).

non_free_vars(yes,X,Xs,Fr1,Fr2,BVarsf,[X/nf|NewFr]):-
	non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).
non_free_vars(no,X,Xs,Fr1,Fr2,[X|BVarsf],NewFr):-
	non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% var_value_rest(+,+,+,-,-)                                              |
% var_value_rest(Fr,X,Value,NewFr,Flag)                                  |
% If the freeness value of X in Fr is Value, then Flag = yes.            |
% Otherwise it is set to no.                                             |
% NewFr is the result of eliminating all Y/V s.t. Y less equal X.        |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

var_value_rest([],_X,_Value,no,[]).
var_value_rest([Y/V|More],X,Value,Rest,Flag):-
	compare(D,X,Y),
	var_value_rest(D,V,More,X,Value,Rest,Flag).

var_value_rest(=,V,More,_X,Value,Rest,Flag):-
	V = Value,!,
	Flag = yes,
	Rest = More.
var_value_rest(=,_V,More,_X,_Value,Rest,Flag):-
	Flag = no,
	Rest = More.
var_value_rest(>,_Elem,More,X,Value,Rest,Flag):-
	var_value_rest(More,X,Value,Rest,Flag).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% make_dependence(+,+,+,-,-)                                             |
% make_dependence(Sh,Vars,Fr,NewFr,NewSh),                               |
% It gives the new sharing and freeness component for the variables in Y |
% (Vars) when recorded(X,Y,Z) was called, once the variables in Z have   |
%  been made ground                                                      |
%-------------------------------------------------------------------------
make_clique_dependence(([],[]),Y,TempPrime_fr,Prime_fr,([],[])):- !,
	change_values(Y,TempPrime_fr,Prime_fr,g).
make_clique_dependence(SH,Y,TempPrime_fr,Prime_fr,Prime_SH):- 
	star_w(SH,Prime_SH),
	change_values_if_f(Y,TempPrime_fr,Prime_fr,nf).

%-------------------------------------------------------------------------%
% propagate_clique_non_freeness(+,+,+,+,-)                                |
% propagate_clique_non_freeness(Vars,NonFv,Sh,Fr,NewFr)                   |
%-------------------------------------------------------------------------%
propagate_clique_non_freeness([],_,_,Fr,Fr) :- !.
propagate_clique_non_freeness(Vars,NonFv,(Cl,Sh),Fr,NewFr):-
	  propagate_non_freeness(Vars,NonFv,Cl,Fr,NewFr1),
	  propagate_non_freeness(Vars,NonFv,Sh,Fr,NewFr2),
	  compute_lub_fr(NewFr1,NewFr2,NewFr).

product_clique(f,X,VarsY,_,SH,Lda_fr,Prime_SH,Prime_fr):-
	share_clique_project(VarsY,SH,Temp),
	bin_union_w(Temp,([],[[X]]),Temp1),
	share_clique_sort(Temp1,Prime_SH),
	take_clique_coupled(SH,[X],Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
product_clique(nf,X,VarsY,Sv,SH,Lda_fr,Prime_SH,Prime_fr):-
	share_clique_project(VarsY,SH,Temp),
	star_w(Temp,Temp1),
	bin_union_w(Temp1,([],[[X]]),Temp2),
	share_clique_sort(Temp2,Prime_SH),
	take_clique_coupled(SH,Sv,Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).

%------------------------------------------------------------------------%
% take_clique_coupled(+,+,-)                                             |
% take_clique_coupled(Sh,Vars,Coupled)                                   |
% SH is pair of list of lists of variables, Vars is a list of variables  |
% Returns in Coupled the list of variables X s.t. exists at least        |
% one list in SH containing X and at least one element in Vars.          |
%------------------------------------------------------------------------%
take_clique_coupled((Cl,Sh),Vars_u,Coupled):-
	sort(Vars_u,Vars),
%% sharing
	ord_split_lists_from_list(Vars,Sh,Intersect_Sh,_),
	merge_list_of_lists(Intersect_Sh,IntVars_Sh),
	merge(Vars,IntVars_Sh,Coupled_Sh),
%% clique
	ord_split_lists_from_list(Vars,Cl,Intersect_Cl,_),
	merge_list_of_lists(Intersect_Cl,IntVars_Cl),
	merge(Coupled_Sh,IntVars_Cl,Coupled).

%------------------------------------------------------------------------%
% obtain_prime_clique_var_var(+,+,+,-)                                   |
% obtain_prime_clique_var_var(Sv,[X/V,Y/V],Call,Success)                 |
% handles the case X = Y where both X,Y are variables which freeness     |
% value \== g                                                            |
%------------------------------------------------------------------------%
obtain_prime_clique_var_var([X/f,Y/f],(Call_SH,Call_fr),Succ):- !,
	amgu_clique_ff(X,[Y],Call_SH,Succ_SH),
	Succ = (Succ_SH,Call_fr).
obtain_prime_clique_var_var([X/_,Y/_],Call,Succ):-
	Prime = (([],[[X,Y]]),[X/nf,Y/nf]),
	sharefree_clique_extend(Prime,[X,Y],Call,Succ).

