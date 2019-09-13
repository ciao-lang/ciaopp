:- module(sharefree_non_var, [], [assertions, isomodes]).

:- doc(title, "sharing+freeness+nonvar (abstract domain)").
% started: 23/7/96
:- doc(author, "Maria Garcia de la Banda").

%------------------------------------------------------------------------%
%                    Meanning of the Program Variables                   %
%                                                                        %
% _sh      : suffix indicating the sharing component                     %
% _fr      : suffix indicating the freeness component                    %
% Sh and Fr: for simplicity, they will represent ASub_sh and ASub_fr     %
%            respectively                                                %
% BPrime   : similar to the abstract prime constraint: abstract          %
%            subtitution obtained after the analysis of the clause being %
%            considered still projected onto Hv (i.e. just before going  %
%            Sv and thus, to Prime)                                      %
% Binds    : List of primitive bindings corresponding to the unification %
%            of Term1 = Term2.                                           %
% Gv       : set of ground variables (can be added as a prefix of a set  %
%            of variables, e.g. GvHv means the set of ground variables of%
%            the head variables)                                         %
% Tv       : set of variables in a term                                  %
% _args    : Added as a prefix of a term, means the set of variables     %
%            s.t. the i-th set contains the set of variables (ordered) in%
%            the i-th argument of the Term                               %
% Star     : a closure under union of a set of sets (can be added as a   %
%            suffix of a set of sets)                                    %
% ShareArgs: Set of sets of numbers in which each set represents the     %
%            possible set sharing among the argument positions indicated %
%            by the numbers                                              %
% Rest are as in domain_dependent.pl                                     %
%------------------------------------------------------------------------%

:- use_module(library(sets), 
	[ insert/3, 
	  merge/3,
	  ord_intersect/2,
	  ord_intersection_diff/4,
	  ord_subset/2, 
	  ord_subtract/3,
 	  ord_test_member/3
	]).
:- use_module(library(terms_vars), [varset/2, varset0/2, varset_in_args/2]).
:- use_module(domain(sharing),
	[ project_share/3,
	  share_less_or_equal/2,
	  share_project/3,
	  % TODO: move to other shared module?
	  script_p_star/3,
	  script_p/3
	]).
:- use_module(domain(sharefree),
	[ shfr_asub_to_native/5,
	  shfr_input_interface/4,
	  shfr_input_user_interface/5,
	  shfr_project/3,
	  shfr_sort/2,
	  % TODO: move to other shared module?
	  project_freeness/3,
	  project_freeness_n/3,
	  propagate_non_freeness/5,
	  make_dependence/5,
	  add_environment_vars/3,
	  all_terms_identical/2,
	  change_values/4,
	  change_values_if_f/4,
	  change_values_if_not_g/4,
	  values_differ/3,
	  take_coupled/3,
	  prune/4,
	  prune/5,
	  partition_sf/4,
	  update_lambda_non_free/5,
	  update_lambda_sf/5,
	  split_coupled/4,
	  values_equal/3,
	  compute_lub_sh/3,
	  covering/3,
	  eliminate_non_element/4,
	  insert_each/3,
	  member_value_freeness_differ/3,
	  obtain_freeness/2
	]).
:- use_module(domain(s_grshfr), 
	[ change_values_if_differ/5,
	  change_values_insert/4,
	  collect_vars_freeness/2,
	  member_value_freeness/3, 
	  projected_gvars/3,
	  var_value/3
	]).
:- use_module(library(lists), [list_to_list_of_lists/2]).
:- use_module(library(lsets), 
	[ closure_under_union/2,
	  merge_each/3,
	  merge_list_of_lists/2, 
	  merge_lists/3,
	  ord_split_lists/4,
	  ord_split_lists_from_list/4,
	  powerset_of_set_of_sets/2,
	  sort_list_of_lists/2
	]).
:- use_module(domain(s_eqs), [simplify_equations/3]).
	
:- use_module(domain(share_aux)).

:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Identical to shfr_project/3, called straight from domain_dependent.pl  %
%------------------------------------------------------------------------%


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrnv_call_to_entry(+,+,+,+,+,+,+,-,-)                                %
% shfrnv_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)          %
%------------------------------------------------------------------------%
% The sharing component is computed as for the shfr domain. The freeness %
% component is also computed as in the shfr except for abs_unify_entry/6 %
% (to take nv into account) and collapse_non_freeness (nf(_,_) is        %
% transformed into nv rather than into nf).                              %
%------------------------------------------------------------------------%

:- export(shfrnv_call_to_entry/9).
shfrnv_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
	variant(Sg,Head),!,
	Flag = yes,
	copy_term((Sg,Proj),(NewTerm,NewProj)),
	Head = NewTerm,
	shfr_sort(NewProj,(Temp_sh,Temp_fr)),
	change_values_insert(Fv,Temp_fr,Entry_fr,f),	
	list_to_list_of_lists(Fv,Temp1),
	merge(Temp1,Temp_sh,Entry_sh),
	Entry = (Entry_sh,Entry_fr).
shfrnv_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
	list_to_list_of_lists(Fv,Entry_sh),
	change_values_insert(Fv,[],Entry_fr,f),
	Entry = (Entry_sh,Entry_fr).
shfrnv_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,(Proj_sh,Proj_fr),Entry,ExtraInfo):-
%%%% freeness and initial sharing
	simplify_equations(Sg,Head,Binds),
	change_values_insert(Hv,Proj_fr,Temp1_fr,f),
	shfrnv_abs_unify_entry(Temp1_fr,Proj_sh,Binds,Hv,Temp2_fr,NewProj_sh,NewBind),
	change_values_insert(Fv,Temp2_fr,Temp3_fr,f),
	shfrnv_collapse_non_freeness(Temp3_fr,Beta_fr),
        merge(Hv,Fv,Cvars),
	project_freeness(Cvars,Beta_fr,Entry_fr),
%%%%%% sharing
	partition_sf(NewBind,Temp3_fr,NewProj_sh,Share),
	project_share(Hv,Share,Project_sh),
	powerset_of_set_of_sets(Project_sh,Beta_sh),
	script_p_star(Sg,NewProj_sh,ShareArgsStar),
	varset_in_args(Head,Head_args),
	list_to_list_of_lists(Fv,Temp1),
	prune(Beta_sh,Head_args,ShareArgsStar,Temp1,Entry_sh),
	Entry = (Entry_sh,Entry_fr),
%%%%% ExtrInfo
	project_freeness_n(Proj_fr,Beta_fr,N_Lda_fr),
	ExtraInfo = ((NewProj_sh,N_Lda_fr),Binds),
	!.

%-------------------------------------------------------------------------
% shfrnv_collapse_non_freeness(+,-)                                      |
% shfrnv_collapse_non_freeness(Fr,NewFr)                                 |
%-------------------------------------------------------------------------
% Transform any X/nf(_,_) in Freeness into X/nv.                         |
%-------------------------------------------------------------------------
 
shfrnv_collapse_non_freeness([],[]).
shfrnv_collapse_non_freeness([X/V1|Xs],[X/V|Changed]):- 
	( V1 = nf(Y,_) ->
	    ( Y == X ->
	       V = nv
	    ;  V = nf)
	;   V = V1
        ),        
	shfrnv_collapse_non_freeness(Xs,Changed).

%-------------------------------------------------------------------------
% shfrnv_abs_unify_entry(+,+,+,+,-,-,-)                                  %
% shfrnv_abs_unify_entry(Fr,Sh,Binds,Hv,NewFr,NewSh,NewBinds)            %
%-------------------------------------------------------------------------
% Identical, the only difference is in shfrnv_aunify_entry/7             %
%-------------------------------------------------------------------------

shfrnv_abs_unify_entry(Fr,Sh,Binds,Hv,NewFr,NewSh,NewBinds):-
	shfrnv_aunify_entry(Binds,Fr,Sh,Hv,Fr1,Sh1,Binds1),
	shfrnv_fixpoint_aunify_entry(Fr,Binds,Fr1,Sh1,Binds1,Hv,NewFr,NewSh,NewBinds).

shfrnv_fixpoint_aunify_entry(Fr,Binds,Fr1,Sh1,Binds1,_,NewFr,NewSh,NewBinds):-
	Fr == Fr1, Binds == Binds1, !,
	NewFr = Fr1,
	NewSh = Sh1,
	NewBinds = Binds.
shfrnv_fixpoint_aunify_entry(_,_,Fr1,Sh1,Binds1,Hv,NewFr,NewSh,NewBinds):- 
	shfrnv_abs_unify_entry(Fr1,Sh1,Binds1,Hv,NewFr,NewSh,NewBinds).

%-------------------------------------------------------------------------
% shfrnv_aunify_entry(+,+,+,+,-,-,-)                                     %
% shfrnv_aunify_entry(Binds,Fr,Sh,Hv,NewFr,NewSh,NewBinds)               %
%-------------------------------------------------------------------------
% Identical except for the cases in which the binding does not ground    %
% one of the terms (last two clauses, table_from_y_entry and             %
% table_from_term_entry, in which nv has to be taken into account).      %
%-------------------------------------------------------------------------

shfrnv_aunify_entry([],Fr,Sh,_,Fr,Sh,[]).
shfrnv_aunify_entry([(X,_,Tv)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):-
	var_value(Fr,X,Val),
	Val = g,!,
	shfrnv_decide_update_lambda(Tv,Fr,Sh,Hv,Fr1,L1),
	shfrnv_aunify_entry(Binds,Fr1,L1,Hv,NewFr,NewSh,NewBinds).
shfrnv_aunify_entry([(X,_,Tv)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):-
	values_equal(Tv,Fr,g), !, 
	shfrnv_decide_update_lambda([X],Fr,Sh,Hv,Fr1,L1),
	shfrnv_aunify_entry(Binds,Fr1,L1,Hv,NewFr,NewSh,NewBinds).
shfrnv_aunify_entry([(X,Term,Vars)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):- 
	var(Term),!,
	var_value(Fr,X,ValueX),
	var_value(Fr,Term,ValueTerm),
	shfrnv_table_from_y_entry(ValueX,ValueTerm,X,Term,Sh,Fr,Fr1),
	NewBinds = [(X,Term,Vars)|RestE],
	shfrnv_aunify_entry(Binds,Fr1,Sh,Hv,NewFr,NewSh,RestE).
shfrnv_aunify_entry([(X,Term,Tv)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):- 
	var_value(Fr,X,ValueX),
	shfrnv_table_from_term_entry(ValueX,X,Term,Sh,Tv,Fr,Fr1),
	NewBinds = [(X,Term,Tv)|RestE],
	shfrnv_aunify_entry(Binds,Fr1,Sh,Hv,NewFr,NewSh,RestE).

%-------------------------------------------------------------------------
% table_from_y_entry(+,+,+,+,+,+,-)                                      %
% table_from_y_entry(ValueX,ValueY,X,Y,Sh,Fr,NewFr)                      %
%-------------------------------------------------------------------------
% Identical except for:                                                  %
%  * In the last clause, if both values are not nf, at least one must be % 
%    nv or nf(_,_). Thus, X and Y must be nv rather than nf (although    %
%    the coupled are still nf).                                          %
% *  In table_from_y_entry_f, the case of nv has to be considered, and   %
%    if the value is nf(_,_) and all terms are not identical, X and Y    %
%    must be nv rather than nf.                                          %
%-------------------------------------------------------------------------


shfrnv_table_from_y_entry(f,ValueY,X,Y,Sh,Fr,NewFr):- !,
	shfrnv_table_from_y_entry_f(ValueY,X,Y,Sh,Fr,NewFr).
shfrnv_table_from_y_entry(ValueX,f,X,Y,Sh,Fr,NewFr):- !,
	shfrnv_table_from_y_entry_f(ValueX,Y,X,Sh,Fr,NewFr).
shfrnv_table_from_y_entry(nf(_,Term1),nf(_,Term2),_,_,_,Fr,Fr):-
	Term1 == Term2, !.
shfrnv_table_from_y_entry(ValueX,ValueY,X,Y,Lda_sh,Fr,NewFr):-  
	take_coupled(Lda_sh,[X,Y],Coupled),
	change_values_if_f(Coupled,Fr,TmpFr,nf),
	( ValueX = nf, ValueY = nf ->
	    NewFr = TmpFr 
	;   sort([X,Y],Vars),
	    ( ( ValueX = nv ; ValueY = nv; ValueX = nf(A,_), X == A; ValueY = nf(A,_), Y == A) ->
	          change_values(Vars,TmpFr,NewFr,nv)
	    ;    change_values_if_f(Vars,TmpFr,NewFr,nf))
	).

shfrnv_table_from_y_entry_f(f,_X,_Y,_Sh,Fr,Fr).
shfrnv_table_from_y_entry_f(nv,X,_Y,Sh,Fr,NewFr):-
 	take_coupled(Sh,[X],Coupled),
 	change_values_if_f(Coupled,Fr,TmpFr,nf),
 	change_values([X],TmpFr,NewFr,nv).
shfrnv_table_from_y_entry_f(nf,X,_Y,Sh,Fr,NewFr):-
 	take_coupled(Sh,[X],Coupled),
 	change_values_if_f(Coupled,Fr,NewFr,nf).
shfrnv_table_from_y_entry_f(nf(A,Term),X,Y,Sh,Fr,NewFr):-
	take_coupled(Sh,[X],Coupled),
	split_coupled(Coupled,Fr,FreeCoupled,Terms),
	( all_terms_identical(Terms,Term) ->
	    change_values_if_not_g(FreeCoupled,Fr,TmpFr,nf(A,Term)),
	    ( A == Y ->
	       change_values([X],TmpFr,NewFr,nf(X,Term))
	    ;  NewFr = TmpFr)
	;   change_values_if_f(Coupled,Fr,TmpFr,nf),
	    sort([X,Y],Vars),
	    ( A == Y ->
	        change_values(Vars,TmpFr,NewFr,nv)
	     ;  change_values_if_f(Vars,TmpFr,NewFr,nf))
        ).

%-------------------------------------------------------------------------
% shfrnv_table_from_term_entry(+,+,+,+,+,+,-)                            %
% shfrnv_table_from_term_entry(ValueX,X,Term,Sh,Tv,Fr,NewFr)             %
%-------------------------------------------------------------------------
% Identical, but X must be nv rather than nf                             %
%-------------------------------------------------------------------------

shfrnv_table_from_term_entry(f,X,Term,Sh,_,Fr,NewFr):- 
	take_coupled(Sh,[X],Coupled),
	split_coupled(Coupled,Fr,FreeCoupled,Terms),
	( all_terms_identical(Terms,Term) ->
	    	change_values_if_not_g(FreeCoupled,Fr,NewFr,nf(X,Term))
	; change_values_if_f(Coupled,Fr,TmpFr,nf),
	  change_values([X],TmpFr,NewFr,nv)
        ).
shfrnv_table_from_term_entry(nv,X,_,Sh,Tv,Fr,NewFr) :- 
	take_coupled(Sh,[X|Tv],Coupled),
	change_values_if_f(Coupled,Fr,NewFr,nf).
shfrnv_table_from_term_entry(nf,X,_,Sh,Tv,Fr,NewFr) :- 
	take_coupled(Sh,[X|Tv],Coupled),
	change_values_if_f(Coupled,Fr,TmpFr,nf),
	change_values([X],TmpFr,NewFr,nv).
shfrnv_table_from_term_entry(nf(_,Term1),_,Term,_,_,Fr,Fr) :-
	 Term1 == Term, !.
shfrnv_table_from_term_entry(nf(_,_),X,_,Sh,Tv,Fr,NewFr) :-
	take_coupled(Sh,[X|Tv],Coupled),
	change_values_if_f(Coupled,Fr,TmpFr,nf),
	change_values([X],TmpFr,NewFr,nv).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrnv_exit_to_prime(+,+,+,+,+,-,-)                                    %
% shfrnv_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)               %
%------------------------------------------------------------------------%
% The sharing component is computed as for the shfr domain. The freeness %
% component is also computed as in the shfr except for abs_unify_exit/4  %
% (to take nv into account) and collapse_non_freeness (nf(_,_) is        %
% transformed into nv rather than into nf).                              %
%------------------------------------------------------------------------%

:- export(shfrnv_exit_to_prime/7).
shfrnv_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
	Prime = '$bottom'.
shfrnv_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
	shfr_project(Exit,Hv,(BPrime_sh,BPrime_fr)),
	copy_term((Head,(BPrime_sh,BPrime_fr)),(NewTerm,NewPrime)),
	Sg = NewTerm,
	shfr_sort(NewPrime,Prime).	
shfrnv_exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
	list_ground(Sv,Prime_fr),
	Prime = ([],Prime_fr).
shfrnv_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
	ExtraInfo = ((Lda_sh,Lda_fr),Binds),
 	shfr_project(Exit,Hv,(BPrime_sh,BPrime_fr)),
 	merge(Lda_fr,BPrime_fr,TempFr),
 	shfrnv_abs_unify_exit(TempFr,Binds,NewTempFr,NewBinds),
	member_value_freeness(NewTempFr,Gv,g),
	ord_split_lists_from_list(Gv,Lda_sh,_Intersect,Sg_sh),
 	merge(Sg_sh,BPrime_sh,Shtemp),
 	partition_sf(NewBinds,NewTempFr,Shtemp,Share),
 	project_share(Sv,Share,Project_sh),
 	powerset_of_set_of_sets(Project_sh,Sup_Prime_sh),
 	shfrnv_collapse_non_freeness(NewTempFr,Sup_lda_fr),
 	project_freeness(Sv,Sup_lda_fr,Prime_fr),
%%%%% sharing
 	script_p(Head,BPrime_sh,ShareArgs),
 	varset_in_args(Sg,Sg_args),
 	ord_intersection_diff(Sup_Prime_sh,Lda_sh,Intersect,Disjoint),
	covering(Disjoint,Lda_sh,AlsoPossible),
	merge(Intersect,AlsoPossible,Lda_sh_temp),
 	prune(Lda_sh_temp,Sg_args,ShareArgs,Prime_sh), 
 	Prime = (Prime_sh,Prime_fr),
 	!.

%-------------------------------------------------------------------------
% shfrnv_abs_unify_exit(+,+,-,-)                                         %
% shfrnv_abs_unify_exit(Fr,Binds,NewFr,NewBinds)                         %
%-------------------------------------------------------------------------
% Again, the only diffrences are in table_from_y_exit and in             %
% table_from_term_exit.                                                  %
%-------------------------------------------------------------------------

shfrnv_abs_unify_exit(Fr,Binds,NewFr,NewBinds):-
	shfrnv_aunify_exit(Fr,Binds,Fr1,Binds1),
	shfrnv_fixpoint_aunify_exit(Fr,Binds,Fr1,Binds1,NewFr,NewBinds).

shfrnv_fixpoint_aunify_exit(Fr,Binds,Fr1,Binds1,NewFr,NewBinds):- 
	Fr == Fr1, Binds == Binds1, !,
	NewFr = Fr1,
	NewBinds = Binds.
shfrnv_fixpoint_aunify_exit(_Fr,_Binds,Fr1,Binds1,NewFr,NewBinds):- 
	shfrnv_abs_unify_exit(Fr1,Binds1,NewFr,NewBinds).

shfrnv_aunify_exit(Fr,[],Fr,[]):- !.
shfrnv_aunify_exit(Fr,[(X,_,Tv)|More],NewFr,NewBinds):-
	var_value(Fr,X,Val),
	Val = g,!,
	change_values(Tv,Fr,Fr1,g),
	shfrnv_aunify_exit(Fr1,More,NewFr,NewBinds).
shfrnv_aunify_exit(Fr,[(X,_,Tv)|More],NewFr,NewBinds):-
	values_equal(Tv,Fr,g), !, 
	change_values([X],Fr,Fr1,g),    
	shfrnv_aunify_exit(Fr1,More,NewFr,NewBinds).
shfrnv_aunify_exit(Fr,[(X,Y,Vars)|More],NewFr,NewBinds):- 
	var(Y), !,
	var_value(Fr,X,ValueX),
	var_value(Fr,Y,ValueY),
	shfrnv_table_from_y_exit(ValueX,ValueY,X,Y,Fr,Fr1),
	NewBinds = [(X,Y,Vars)|RestBinds],
	shfrnv_aunify_exit(Fr1,More,NewFr,RestBinds).
shfrnv_aunify_exit(Fr,[(X,Term,Tv)|More],NewFr,NewBinds):- !,
	NewBinds = [(X,Term,Tv)|RestBinds],
	var_value(Fr,X,ValueX),
	shfrnv_table_from_term_exit(ValueX,X,Term,Tv,Fr,Fr1),
	shfrnv_aunify_exit(Fr1,More,NewFr,RestBinds).

shfrnv_table_from_y_exit(Valuex,Valuey,_,_,Fr,Fr):- 
	Valuex == Valuey, !.
shfrnv_table_from_y_exit(f,ValueY,X,_,Fr,Fr1):-  !,
	change_values([X],Fr,Fr1,ValueY).
shfrnv_table_from_y_exit(Valuex,f,_,Y,Fr,Fr1):- !,
	change_values([Y],Fr,Fr1,Valuex).
shfrnv_table_from_y_exit(Valuex,Valuey,X,Y,Fr,Fr1):- 
	sort([X,Y],Sorted),
	( Valuex = nf, Valuey = nf ->
	    change_values(Sorted,Fr,Fr1,nf)
	;   change_values(Sorted,Fr,Fr1,nv)
        ).


shfrnv_table_from_term_exit(f,X,Term,_,Fr,Fr1):- !,
	change_values([X],Fr,Fr1,nf(X,Term)).
shfrnv_table_from_term_exit(nv,_,_,Tv,Fr,Fr1) :- !,
	change_values_if_f(Tv,Fr,Fr1,nf).
shfrnv_table_from_term_exit(nf,_,_,Tv,Fr,Fr1) :- !,
	change_values_if_f(Tv,Fr,Fr1,nf).
shfrnv_table_from_term_exit(nf(_,Term1),_,Term,_,Fr,NewFr) :-
	Term1 == Term, !,
	NewFr = Fr.
shfrnv_table_from_term_exit(_,X,_,Tv,Fr,Fr1) :- !,
	change_values_if_f(Tv,Fr,TmpFr,nf),
	change_values([X],TmpFr,Fr1,nv).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT SORT
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% Identical to shfr_sort/2, called straight from domain_dependent.pl     %
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT LUB
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% shfrnv_compute_lub(+,-)                                                %
% shfrnv_compute_lub(ListASub,Lub)                                       %
%------------------------------------------------------------------------%
% It computes the lub of a set of Asub. For each two abstract            %
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   %
% (1) merging the Sh1 and Sh2  (identical to compute_lub_sh in shfr)     %
% (2) foreach X/Value1 in Fr1 and X/Value2 in Fr2, X/Value in Fr where   %
%     Value is computed from the lattice   f < nf, g < nv < nf           %
%------------------------------------------------------------------------%

:- export(shfrnv_compute_lub/2).
shfrnv_compute_lub([X],X):- !.
shfrnv_compute_lub([ASub1,ASub2|Xs],Lub):-
	shfrnv_compute_lub_el(ASub1,ASub2,ASubLub),
	shfrnv_compute_lub([ASubLub|Xs],Lub).

%:- export(shfrnv_compute_lub_el/3).  
shfrnv_compute_lub_el('$bottom',ASub,ASub):- !.
shfrnv_compute_lub_el((Sh1,Fr1),(Sh2,Fr2),(Lub_sh,Lub_fr)):- !,
	compute_lub_sh(Sh1,Sh2,Lub_sh),
	shfrnv_compute_lub_fr(Fr1,Fr2,Lub_fr).
shfrnv_compute_lub_el(ASub,_,ASub).

shfrnv_compute_lub_fr([],[],[]).
shfrnv_compute_lub_fr([X/Value1|Fr1],[X/Value2|Fr2],[X/Value|Lub]):- 
	shfrnv_lub_val(Value1,Value2,Value),
	shfrnv_compute_lub_fr(Fr1,Fr2,Lub).

shfrnv_lub_val(Value,Value,Value):- !.
shfrnv_lub_val(g,Value2,Value):- !,
	( Value2 = nv ->
	    Value = nv
	;   Value = nf).
shfrnv_lub_val(nv,Value2,Value):- !,
	( Value2 = g ->
	    Value = nv
	;   Value = nf).
shfrnv_lub_val(_,_,nf).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Extend
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% shfrnv_extend(+,+,+,-)                                                 %
% shfrnv_extend(Prime,Sv,Call,Succ)                                      %
%------------------------------------------------------------------------%
% Identical except for non_free_vars and member_value_freeness_differ.   %
%------------------------------------------------------------------------%

:- export(shfrnv_extend/4).    
shfrnv_extend('$bottom',_Sv,_Call,Succ):- !,
	Succ = '$bottom'.
shfrnv_extend(_Prime,[],Call,Succ):- !,
	Call = Succ.
shfrnv_extend((Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),Succ):-
%-extend_sh
	ord_split_lists_from_list(Sv,Call_sh,Intersect,Disjunct),
	closure_under_union(Intersect,Star),
	eliminate_non_element(Sv,Star,Prime_sh,Extended),
	merge(Extended,Disjunct,Succ_sh),
%-extend_fr
	member_value_freeness_differ(Call_fr,NonGvCall,g),
	merge_list_of_lists(Succ_sh,NonGvSucc),
	ord_subtract(NonGvCall,NonGvSucc,NewGv),
	change_values_insert(NewGv,Prime_fr,Temp1_fr,g),
	ord_subtract(NonGvSucc,Sv,BVars),
	shfrnv_non_free_vars(BVars,Call_fr,Temp1_fr,BVarsf,Temp2_fr),
	( BVarsf = [] ->
	  Temp3_fr = Temp2_fr
	; member_value_freeness_differ(Prime_fr,NonFree,f),
	  propagate_non_freeness(BVarsf,NonFree,Succ_sh,Temp2_fr,Temp3_fr)
	),
	add_environment_vars(Temp3_fr,Call_fr,Succ_fr),
	Succ = (Succ_sh,Succ_fr), !.

%-------------------------------------------------------------------------
% shfrnv_non_free_vars(+,+,+,-,-)                                        %
% shfrnv_non_free_vars(Vars,Fr1,Fr2,Fv,NewFr).                           %
%-------------------------------------------------------------------------
% Identical but variables in Vars which appear in Fr1 with value nv are  %
% also added to NewFr                                                    %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

shfrnv_non_free_vars([],_,Fr2,[],Fr2).
shfrnv_non_free_vars([X|Xs],Fr1,Fr2,BVarsf,NewFr):-
	shfrnv_non_free_vars(Fr2,X,Xs,Fr1,BVarsf,NewFr).

shfrnv_non_free_vars([],X,Xs,[Y/V|Fr1],BVarsf,NewFr):-
	compare(D,X,Y),
	shfrnv_non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
shfrnv_non_free_vars([Y/V|Fr2],X,Xs,Fr1,BVarsf,NewFr):-
	compare(D,X,Y),
	shfrnv_non_free_vars(D,X,Xs,Fr1,Y/V,Fr2,BVarsf,NewFr).

shfrnv_non_free_vars(>,X,Xs,Fr1,Elem,Fr2,BVarsf,[Elem|NewFr]):-
	shfrnv_non_free_vars(Fr2,X,Xs,Fr1,BVarsf,NewFr).
shfrnv_non_free_vars(<,X,Xs,Fr1,Elem,Fr2,BVarsf,NewFr):-
	shfrnv_var_value_rest(Fr1,X,New_Fr1,Value),
	shfrnv_non_free_vars(Value,X,Xs,New_Fr1,[Elem|Fr2],BVarsf,NewFr).

shfrnv_non_free_vars1(>,X,Xs,_,[Y/V|Fr1],BVarsf,NewFr):-
	compare(D,X,Y),
	shfrnv_non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
shfrnv_non_free_vars1(=,X,Xs,V,Fr1,BVarsf,NewFr):-
	(V = nf ; V=nv), !,
	NewFr = [X/V|Rest_temp2],
	shfrnv_non_free_vars2(Xs,Fr1,BVarsf,Rest_temp2).
shfrnv_non_free_vars1(=,X,Xs,_V,Fr1,[X|BVarsf],NewFr):-
	shfrnv_non_free_vars2(Xs,Fr1,BVarsf,NewFr).

shfrnv_non_free_vars2([],_Fr1,[],[]).
shfrnv_non_free_vars2([X|Xs],[Y/V|Fr1],BVarsf,NewFr):-
	compare(D,X,Y),
	shfrnv_non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).

shfrnv_non_free_vars(f,X,Xs,Fr1,Fr2,[X|BVarsf],NewFr):-
	shfrnv_non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).
shfrnv_non_free_vars(nf,X,Xs,Fr1,Fr2,BVarsf,[X/nf|NewFr]):-
	shfrnv_non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).
shfrnv_non_free_vars(nv,X,Xs,Fr1,Fr2,BVarsf,[X/nv|NewFr]):-
	shfrnv_non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% shfrnv_var_value_rest(+,+,-,-)                                         |
% shfrnv_var_value_rest(Fr,X,NewFr,Value)                                |
%-------------------------------------------------------------------------
% The freeness value of X in Fr is Value                                 |
% NewFr is the result of eliminating all Y/V s.t. Y less equal X.        |
%-------------------------------------------------------------------------

shfrnv_var_value_rest([Y/V|More],X,Rest,Value):-
	compare(D,X,Y),
	shfrnv_var_value_rest_(D,V,More,X,Rest,Value).

shfrnv_var_value_rest_(=,Value,More,_,More,Value).
shfrnv_var_value_rest_(>,_,More,X,Rest,Value):-
	shfrnv_var_value_rest(More,X,Rest,Value).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Identical except for abs_unify_entry, collapse_non_freeness and        %
% extend.
%-------------------------------------------------------------------------

:- export(shfrnv_call_to_success_fact/9). 
shfrnv_call_to_success_fact(_Sg,[],_Head,_K,Sv,Call,_Proj,Prime,Succ) :- 
	Call = (Call_sh,Call_fr),!,
	update_lambda_sf(Sv,Call_fr,Call_sh,Succ_fr,Succ_sh),
	list_ground(Sv,Prime_fr),
	Prime = ([],Prime_fr),
	Succ = (Succ_sh,Succ_fr).
shfrnv_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,(Sg_sh,Lda_fr),Prime,Succ) :-
% call_to_entry      -------------------------------------------------
	simplify_equations(Sg,Head,Binds), !,
	change_values_insert(Hv,Lda_fr,Lda_fr_all,f),
	shfrnv_abs_unify_entry(Lda_fr_all,Sg_sh,Binds,Hv,New_Lda_fr,New_Sg_sh,E),
	partition_sf(E,New_Lda_fr,New_Sg_sh,Share),
	project_share(Hv,Share,Project_sh),
	powerset_of_set_of_sets(Project_sh,Beta_sh),
	shfrnv_collapse_non_freeness(New_Lda_fr,Entry_fr),
	script_p_star(Sg,New_Sg_sh,ShareArgsStar),
	varset_in_args(Head,Head_args),
	prune(Beta_sh,Head_args,ShareArgsStar,Entry_sh),
% exit_to_prime      -------------------------------------------------

	project_share(Sv,Share,New_Project_sh),
	powerset_of_set_of_sets(New_Project_sh,Sup_Prime_sh),
	project_freeness(Sv,Entry_fr,Prime_fr),
	script_p(Head,Entry_sh,ShareArgs),
	varset_in_args(Sg,Sg_args),
 	ord_intersection_diff(Sup_Prime_sh,New_Sg_sh,Intersect,Disjoint),
	covering(Disjoint,New_Sg_sh,AlsoPossible),
	merge(Intersect,AlsoPossible,Lda_sh_temp),
	prune(Lda_sh_temp,Sg_args,ShareArgs,Prime_sh),
	Prime = (Prime_sh,Prime_fr),
	shfrnv_extend(Prime,Sv,Call,Succ).
%
shfrnv_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%-------------------------------------------------------------------------
% shfrnv_unknown_entry(+,+,-)                                            |
% shfrnv_unknown_entry(Sg,Qv,Call)                                       |
%-------------------------------------------------------------------------
% Identical to shfr_unknown_entry/3, called from domain_dependent.pl     %
%-------------------------------------------------------------------------

%------------------------------------------------------------------------%
% shfrnv_input_user_interface(+,+,-,+,+)                                 %
% shfrnv_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)        %
%------------------------------------------------------------------------%
% identical but taking non_free into account.                            %
%------------------------------------------------------------------------%

:- export(shfrnv_input_user_interface/5). 
shfrnv_input_user_interface((Sh,Fr,Nv),Qv,(Call_sh,Call_fr),Sg,MaybeCallASub):-
	shfr_input_user_interface((Sh,Fr),Qv,(Call_sh,Call_fr0),Sg,MaybeCallASub),
	sort(Nv,NonVar),
	change_values_insert(NonVar,Call_fr0,Call_fr,nv).

:- export(shfrnv_input_interface/4). 
shfrnv_input_interface(Info,Kind,(Sh0,Fr,Nv),(Sh,Fr,Nv)):-
	shfr_input_interface(Info,Kind,Sh0,Sh), !.
shfrnv_input_interface(not_free(X),perfect,(Sh,Fr,Nv0),(Sh,Fr,Nv)):-
	var(X),
	myinsert(Nv0,X,Nv).

myinsert(Fr0,X,Fr):-
	var(Fr0), !,
	Fr = [X].
myinsert(Fr0,X,Fr):-
	insert(Fr0,X,Fr).

%% %------------------------------------------------------------------------%
%% % shfrnv_output_interface(+,-)                                             %
%% % shfrnv_output_interface(ASub,Output)                                     %
%% %------------------------------------------------------------------------%
%% % The readible format still close to the internal formal is identical    %
%% % for the Sharing part. The output for Fr is the set of free variables   %
%% %-------------------------------------------------------------------------
%% 
%:- export(shfrnv_output_interface/2).  
%% shfrnv_output_interface(ac('$bottom',Flag),('$bottom',Flag)) :- !.
%% shfrnv_output_interface(ac(d(ACons,Del),Flag),Output) :- 
%% 	del_output(ac(Del,Flag),ACons,Output).
%% shfrnv_output_interface(d(ACons,Del),Output) :- 
%% 	del_output(Del,ACons,Output).
%% shfrnv_output_interface((Sh,Fr),(Sh,Fr)).
%% shfrnv_output_interface('$bottom','$bottom').
%% shfrnv_output_interface([],[]).
%% shfrnv_output_interface([Succ],OutSucc):- !,
%% 	shfrnv_output_interface(Succ,OutSucc).
%% shfrnv_output_interface([Succ|LSucc],[OutSucc|LOutSucc]):-
%% 	shfrnv_output_interface(Succ,OutSucc),
%% 	shfrnv_output_interface0(LSucc,LOutSucc).
%% 
%% shfrnv_output_interface0([],[]).
%% shfrnv_output_interface0([Succ|LSucc],[OutSucc|LOutSucc]):-
%% 	shfrnv_output_interface(Succ,OutSucc),
%% 	shfrnv_output_interface0(LSucc,LOutSucc).

%------------------------------------------------------------------------%
% shfrnv_asub_to_native(+,+,+,-,-)                                       %
% shfrnv_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                 %
% The user friendly format consists in extracting the nonfree variables  %
% plus ground and free                                                   %
%------------------------------------------------------------------------%

:- export(shfrnv_asub_to_native/5). 
shfrnv_asub_to_native((Sh,Fr),Qv,OutFlag,ASub_user,Comps):-
	shfr_asub_to_native((Sh,Fr),Qv,OutFlag,ASub_user0,Comps),
	member_value_freeness(Fr,Nv,nv),
	if_not_nil(Nv,not_free(Nv),ASub_user,ASub_user0).

%------------------------------------------------------------------------%
% shfrnv_less_or_equal(+,+)                                              %
% shfrnv_less_or_equal(ASub0,ASub1)                                      %
%------------------------------------------------------------------------%
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

:- export(shfrnv_less_or_equal/2). 
shfrnv_less_or_equal((Sh0,Fr0),(Sh1,Fr1)):-
	share_less_or_equal(Sh0,Sh1),
	member_value_freeness(Fr0,ListFr0,f),
	member_value_freeness(Fr1,ListFr1,f),
	ord_subset(ListFr1,ListFr0),
	member_value_freeness(Fr0,ListNv0,nv),
	member_value_freeness(Fr1,ListNv1,nv),
	ord_subset(ListNv1,ListNv0).

%% %------------------------------------------------------------------------%
%% % shfrnv_more_instantiate(+,+)                                           %
%% % shfrnv_more_instantiate(ASub0,ASub1)                                   %
%% %------------------------------------------------------------------------%
%% % Succeeds if ASub1 is possibly more instantiated or equal to ASub0.     %
%% % WARNING, incomplete since definite dependencies in ASub0 afecting      %
%% % variables which are also free in ASub1, must appear in ASub1           %
%% %------------------------------------------------------------------------%
%% 
%:- export(shfrnv_more_instantiate/2). 
%% shfrnv_more_instantiate((Sh0,Fr0),(Sh1,Fr1)):-
%%         member_value_freeness(Fr0,ListGr0,g),
%%         member_value_freeness(Fr1,ListGr1,g),
%%         ord_subset(ListGr0,ListGr1),
%%         member_value_freeness(Fr0,ListNv0,nv),
%%         member_value_freeness(Fr1,ListNv1,nv),
%% 	merge(ListNv1,ListGr1,Inst1),
%%         ord_subset(ListNv0,Inst1),
%%         member_value_freeness(Fr1,ListFr1,f),
%% 	merge(ListNv0,ListGr0,Inst0),
%%         ord_intersection(ListFr1,Inst0,[]),
%%         member_value_freeness(Fr0,ListFr0,f),
%% 	( ListFr1 = [] ->
%% 	    true
%% 	;  \+ (shfrnv_mynonvar(ListFr1,Sh0,ListFr0))
%%         ),
%% 	ord_subtract(Sh1,Sh0,Disj),
%% 	merge_list_of_lists(Disj,Vars),
%% 	ord_split_lists_from_list(Vars,Sh0,Int,_),
%% 	closure_under_union(Int,Star),
%% 	ord_subset(Disj,Star),!.

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% shfrnv_special_builtin(+,+,+,-,-)                                      |
% shfrnv_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                 |
%-------------------------------------------------------------------------
% Identical to shfr, called straight from domain_dependent.pl            %
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% shfrnv_success_builtin(+,+,+,+,-)                                      |
% shfrnv_success_builtin(Type,Sv_u,Condv,Call,Succ)                      |
%-------------------------------------------------------------------------
% Identical except for when it says %% CHANGED                           %
%-------------------------------------------------------------------------

:- export(shfrnv_success_builtin/5).
shfrnv_success_builtin(new_ground,Sv_u,_,Call,Succ):-
	sort(Sv_u,Sv),
	Call = (Lda_sh,Lda_fr),
	update_lambda_sf(Sv,Lda_fr,Lda_sh,Succ_fr,Succ_sh), 
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin(bottom,_,_,_,'$bottom').
shfrnv_success_builtin(unchanged,_,_,Lda,Lda).
shfrnv_success_builtin(some,_Sv,NewGr,Call,Succ):-
	Call = (Call_sh,Call_fr),
	update_lambda_sf(NewGr,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin(old_ground,Sv_u,_,Call,Succ):-
	sort(Sv_u,Sv),
	Call = (Call_sh,Call_fr),
	update_lambda_non_free(Sv,Call_fr,Call_sh,Succ_fr,Succ_sh),!,
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin(old_ground,_,_,_,'$bottom').
shfrnv_success_builtin(old_new_ground,_,(OldG,NewG),Call,Succ):-
	Call = (Call_sh,Call_fr),
	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
	update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin(old_new_ground,_,_,_,'$bottom').
shfrnv_success_builtin(all_nonfree,Sv_u,_,Call,Succ):- !,
	sort(Sv_u,Sv),
	shfr_project(Call,Sv,(Proj_sh,Proj_fr)),
	closure_under_union(Proj_sh,Prime_sh),
	change_values_if_f(Sv,Proj_fr,Prime_fr,nf), 
	shfrnv_extend((Prime_sh,Prime_fr),Sv,Call,Succ).
shfrnv_success_builtin(arg,_,p(X,Y,Z),Call,Succ):-
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
	shfrnv_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
shfrnv_success_builtin(arg,_,_,_,'$bottom').
shfrnv_success_builtin(exp,_,Sg,Call,Succ):-
	Head = p(A,f(A,_B)),
	varset(Sg,Sv),
	varset(Head,Hv),
	shfr_project(Call,Sv,Proj),
	shfrnv_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
shfrnv_success_builtin(exp,_,_,_,'$bottom').
shfrnv_success_builtin('=../2',_,p(X,Y),(Call_sh,Call_fr),Succ):-
	varset(X,Varsx),
	values_equal(Varsx,Call_fr,g),!,
	varset(Y,VarsY),
	update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('=../2',_,p(X,Y),(Call_sh,Call_fr),Succ):-
	varset(Y,VarsY),
	values_equal(VarsY,Call_fr,g),!,
	varset(X,VarsX),
	update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('=../2',Sv_uns,p(X,Y),Call,Succ):-
	var(X), var(Y),!,
	sort(Sv_uns,Sv),
	Call = (_,Call_fr),
	project_freeness(Sv,Call_fr,[A/Val1,B/Val2]),
	( obtain_freeness(Val1,Val2) ->
	    shfrnv_extend(([Sv],[A/nv,B/nv]),Sv,Call,Succ) %% CHANGED
	; Succ = '$bottom'
        ).
shfrnv_success_builtin('=../2',Sv_uns,p(X,Y),Call,Succ):-
	var(X), !,
	sort(Sv_uns,Sv),
	Call = (Call_sh,Call_fr),	
	project_freeness(Sv,Call_fr,Proj_fr),
	Y = [Z|_],
	var_value(Proj_fr,X,ValueX),
	( var(Z) ->
	    var_value(Proj_fr,Z,ValueZ),
	    ( ValueZ = f , ValueX = f ->
		Succ = '$bottom'
	    ; ord_subtract(Sv,[Z],NewVars),
	      project_share(NewVars,Call_sh,Proj_sh),
	      ord_subtract(NewVars,[X],VarsY),
	      shfrnv_product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr), %% CHANGED
	      shfrnv_extend((Prime_sh,Prime_fr),Sv,Call,Succ)
	    )
	; project_share(Sv,Call_sh,Proj_sh),
	  ord_subtract(Sv,[X],VarsY),
	  shfrnv_product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr), %% CHANGED
	  shfrnv_extend((Prime_sh,Prime_fr),Sv,Call,Succ)
        ).
shfrnv_success_builtin(read2,Sv_u,p(X,Y),(Call_sh,Call_fr),Succ):- 
	varset(X,Varsx),
	update_lambda_non_free(Varsx,Call_fr,Call_sh,Temp_fr,Temp_sh),
	( var(Y) ->
	  change_values_if_f([Y],Temp_fr,Succ_fr,nf), 
	  Succ = (Temp_sh,Succ_fr)
	; varset(Y,Varsy),
	  shfr_project((Temp_fr,Temp_sh),Varsy,(Proj_sh,Prime_fr)),
	  closure_under_union(Proj_sh,Prime_sh),
	  sort(Sv_u,Sv),
	  shfrnv_extend((Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),Succ)
	).
shfrnv_success_builtin(recorded,_,p(Y,Z),Call,Succ):-
        varset(Z,NewG),
	varset(Y,VarsY),
	merge(NewG,VarsY,Vars),
	shfr_project(Call,Vars,(Sh,Fr)),
	update_lambda_sf(NewG,Fr,Sh,TempPrime_fr,TempPrime_sh),
	make_dependence(TempPrime_sh,VarsY,TempPrime_fr,Prime_fr,Prime_sh),
	Prime = (Prime_sh,Prime_fr),
	shfrnv_extend(Prime,Vars,Call,Succ).
shfrnv_success_builtin(copy_term,_,p(X,Y),Call,Succ):-
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
	shfrnv_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                    (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
	collect_vars_freeness(FrCall,VarsCall),
	shfr_project(Temp_success,VarsCall,Succ).
shfrnv_success_builtin('current_key/2',_,p(X),Call,Succ):-
	varset(X,NewG),
	Call = (Call_sh,Call_fr),
	update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('current_predicate/2',_,p(X,Y),Call,Succ):-
	var(Y),!,
	Call = (Call_sh,Call_fr),
	change_values_if_f([Y],Call_fr,Temp_fr,nf), 
	varset(X,NewG),
	update_lambda_sf(NewG,Temp_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('current_predicate/2',_,p(X,_Y),Call,Succ):- 
	Call = (Call_sh,Call_fr),
	varset(X,NewG),
	update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin(findall,_,p(X,Z),(Call_sh,Call_fr),(Succ_sh,Succ_fr)):-
	varset(X,Xs),
	member_value_freeness(Call_fr,GVars,g),
	ord_subset(Xs,GVars), !,
	varset(Z,Zs),
	update_lambda_sf(Zs,Call_fr,Call_sh,Succ_fr,Succ_sh).
shfrnv_success_builtin(findall,_,_,Call,Call).
shfrnv_success_builtin('functor/3',_,p(X,Y,Z),Call,Succ):-
	var(X),
	Call = (Call_sh,Call_fr),
	var_value(Call_fr,X,f),!,
	change_values([X],Call_fr,Temp_fr,nv),  %% CHANGED
	varset([Y,Z],OldG),
	( update_lambda_non_free(OldG,Temp_fr,Call_sh,Succ_fr,Succ_sh) ->
	  Succ = (Succ_sh,Succ_fr)
	; Succ = '$bottom'
	).
shfrnv_success_builtin('functor/3',_,p(_X,Y,Z),Call,Succ):- 
	Call = (Call_sh,Call_fr),
	varset([Y,Z],NewG),
	update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('name/2',_,p(X,Y),Call,Succ):-
        varset(X,OldG),
	Call = (Call_sh,Call_fr),
	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
        varset(Y,NewG),
	update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('name/2',_,p(X,Y),Call,Succ):-
        varset(Y,OldG),
	Call = (Call_sh,Call_fr),
	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
        varset(X,NewG),
	update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('name/2',_,_,_,'$bottom').
shfrnv_success_builtin('nonvar/1',_,p(X),Call,Succ):-
        var(X), !,
	Call = (Call_sh,Call_fr),
	var_value(Call_fr,X,Val),
	( Val = f ->
	  Succ = '$bottom'
	; change_values_if_not_g([X],Call_fr,Succ_fr,nv),
	  Succ = (Call_sh,Succ_fr)
	).
shfrnv_success_builtin('nonvar/1',_,_,Call,Call):- !.
shfrnv_success_builtin('numbervars/3',_,p(X,Y,Z),Call,Succ):-
	Call = (Call_sh,Call_fr),
	varset(Y,OldG),
	update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
	varset(p(X,Z),NewG),
	update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('numbervars/3',_,_,_,'$bottom').
shfrnv_success_builtin('compare/3',_,p(X),Call,Succ):- 
        atom(X),!,
	Succ = Call.
shfrnv_success_builtin('compare/3',_,p(X),Call,Succ):- 
        var(X),!,
	Call = (Call_sh,Call_fr),
	update_lambda_sf([X],Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('compare/3',_,_,_,'$bottom').
shfrnv_success_builtin('indep/2',_,p(X,Y),Call,Succ):- 
	( ground(X) ; ground(Y) ), !,
	Succ = Call.
shfrnv_success_builtin('indep/2',_,p(X,Y),Call,Succ):- 
	varset(X,Xv),
	varset(Y,Yv),
	Call = (Call_sh,Call_fr),
	varset(Call_fr,Vars),
	eliminate_couples(Call_sh,Xv,Yv,Succ_sh),
	projected_gvars(Succ_sh,Vars,Ground),
	change_values_if_differ(Ground,Call_fr,Succ_fr,g,f),!,
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('indep/2',_,_,_,'$bottom').
shfrnv_success_builtin('indep/1',_,p(X),Call,Succ):- 
	nonvar(X),
	handle_each_indep(X,shfrnv,Call,Succ), !.
shfrnv_success_builtin('indep/1',_,_,_,'$bottom').
shfrnv_success_builtin('length/2',_,p(X,Y),Call,Succ):-
        var(X),var(Y),!,
	Call = (_,Call_fr),
	var_value(Call_fr,X,Valuex),
	var_value(Call_fr,Y,Valuey),
	shfrnv_update_from_values(Valuex,Valuey,X,Y,Call,Succ). %% CHANGED
shfrnv_success_builtin('length/2',_,p(X,_Y),Call,Succ):-
        var(X),!,
	Call = (Call_sh,Call_fr),
	take_coupled(Call_sh,[X],Coupled),
	change_values_if_f(Coupled,Call_fr,Tmp_fr,nf),
	change_values_if_not_g([X],Tmp_fr,Succ_fr,nv), %% CHANGED
	Succ = (Call_sh,Succ_fr).
shfrnv_success_builtin('length/2',_,p(X,Y),Call,Succ):-
	functor(X,'.',_),
	varset0(X,[Z|_]),
	Call = (Call_sh,Call_fr),
	take_coupled(Call_sh,[Z],Coupled),
	change_values_if_f(Coupled,Call_fr,Temp_fr,nf),
	change_values_if_not_g([X],Temp_fr,Temp1_fr,nv),  %% CHANGED
	update_lambda_sf([Y],Temp1_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_success_builtin('var/1',[X],p(X),Call,Succ):- 
	Call = (Call_sh,Call_fr),
	var_value(Call_fr,X,Valuex),
	Valuex \== g, Valuex \== nv, %% CHANGED
	member_value_freeness(Call_fr,FreeVars,f),
	\+ (shfrnv_mynonvar([X],Call_sh,FreeVars)),
	change_values([X],Call_fr,Succ_fr,f),
	Succ = (Call_sh,Succ_fr).
shfrnv_success_builtin('var/1',_,_,_,'$bottom').

%-------------------------------------------------------------------------
% shfrnv_call_to_success_builtin(+,+,+,+,+,-)                              %
% shfrnv_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)               %
%-------------------------------------------------------------------------

:- export(shfrnv_call_to_success_builtin/6). 
shfrnv_call_to_success_builtin('==/2','=='(X,Y),_Sv,Call,Proj,Succ):-
        var(X),!,
	shfrnv_identical_one_var(X,Y,Call,Proj,Succ).
shfrnv_call_to_success_builtin('==/2','=='(X,Y),_Sv,Call,Proj,Succ):-
        var(Y),!,
	shfrnv_identical_one_var(Y,X,Call,Proj,Succ).
%% shfrnv_call_to_success_builtin('==/2','=='(X,Y),Sv,Call,_Proj,Succ):-
%% 	Call = (Call_sh,Call_fr),
%% 	free_peel(X,Y,Binds,[]),
%% 	extract_ground(Sv,Call_fr,Gv),
%% 	shfrnv_make_reduction(Binds,(Call_sh,Call_fr),Gv,Call_fr,Tfr,NewGv,Elim_u-[]),
%% 	sort(Elim_u,Elim),
%% 	ord_split_lists_from_list(NewGv,Call_sh,_Intersect,Temp_sh),
%% 	ord_subtract(Temp_sh,Elim,Succ_sh),
%% 	update_freeness(Tfr,Succ_sh,Succ_fr),
%% 	non_free_to_ground(Call,(Succ_sh,Succ_fr),Succ).
shfrnv_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr),Succ):-
	varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
	Call = (Call_sh,Call_fr),
	ord_subtract(Sv,VarsX,VarsY),
	update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr),Succ):-
	varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
	Call = (Call_sh,Call_fr),
	ord_subtract(Sv,VarsY,VarsX),
	update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
	Succ = (Succ_sh,Succ_fr).
shfrnv_call_to_success_builtin('=/2','='(X,Y),_Sv,Call,Proj,Succ):-
	var(X),var(Y), !,
	Proj = (_,Proj_fr),	
	shfrnv_obtain_prime_var_var(Proj_fr,Call,Succ).
shfrnv_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
	var(X), !,
	Proj = (Proj_sh,Proj_fr),	
	ord_subtract(Sv,[X],VarsY),
	var_value(Proj_fr,X,ValueX),
	shfrnv_product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
	Prime= (Prime_sh,Prime_fr),
	shfrnv_extend(Prime,Sv,Call,Succ).
shfrnv_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,!,
	varset(Xterm,Vars),
	shfrnv_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
shfrnv_call_to_success_builtin('=/2',_,_,_call,_,'$bottom').
shfrnv_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):- !,
	shfrnv_call_to_success_builtin('=/2','='(X,[Y|Z]),Sv,Call,Proj,Succ).
shfrnv_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):-
        shfrnv_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ).
shfrnv_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	var(X), !,
	Proj = (_Sh,Fr),
	var_value(Fr,X,Val),
	( Val = f ->
	  Succ = '$bottom'
	; varset([X,Y],Sv),
	  copy_term(Y,Yterm),
	  varset(Yterm,Vars),
	  shfrnv_call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),not_provided,Sv,Call,Proj,_Prime,Succ) % TODO: add some ClauseKey?
	).
shfrnv_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
	functor(X,'.',_), !,
	varset0(X,[Z|_]),
	Call = (Call_sh,Call_fr),
	change_values_if_not_g([Z],Call_fr,Temp_fr,nv),
	varset([X,Y],Sv),
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,
	varset(Xterm,Vars),
	Proj = (Sh,Fr),
	change_values_if_not_g([Z],Fr,TFr,nv),
	shfrnv_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_sh,Temp_fr),(Sh,TFr),_Prime,Succ). % TODO: add some ClauseKey?
shfrnv_call_to_success_builtin('sort/2',_,_,_,_,'$bottom').

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%            Intermediate Functions                                      %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% shfrnv_decide_update_lambda(+,+,+,+,-,-)                               %
% shfrnv_decide_update_lambda(Gv,Fr,Sh,Hv,NewFr,NewSh)                   %
%-------------------------------------------------------------------------
% identical except for change_values_if_f                                %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

shfrnv_decide_update_lambda([],Fr,Sh,_,Fr,Sh).
shfrnv_decide_update_lambda([X|Xs],Fr,Sh,Hv,NewFr,NewSh):-
	ord_test_member(Hv,X,Flag),
	shfrnv_decide_update_lambda(Flag,X,Xs,Fr,Sh,NewFr,NewSh).

shfrnv_decide_update_lambda(yes,X,Xs,Fr,Sh,NewFr,Sh):-
	change_values([X|Xs],Fr,NewFr,g).
shfrnv_decide_update_lambda(no,X,Xs,Fr,Sh,NewFr,NewSh):- 
	ord_split_lists_from_list([X|Xs],Sh,Intersect,NewSh),
	merge_list_of_lists(Intersect,Coupled),
	merge_list_of_lists(NewSh,NotCoupled),
	ord_intersection_diff(Coupled, NotCoupled,NonFv,NewGv),
	change_values(NewGv,Fr,Temp_Fr,g),
	change_values_if_f(NonFv,Temp_Fr,NewFr,nf).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------

shfrnv_product(f,X,VarsY,_,Sh,Lda_fr,Prime_sh,Prime_fr):-
	project_share(VarsY,Sh,Temp),
	insert_each(Temp,X,Temp1),
	sort_list_of_lists(Temp1,Prime_sh),
	take_coupled(Sh,[X],Coupled),
	change_values_if_f(Coupled,Lda_fr,Tmp_fr,nf),
	change_values([X],Tmp_fr,Prime_fr,nv).
shfrnv_product(nv,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
	project_share(VarsY,Sh,Temp),
	closure_under_union(Temp,Temp1),
	merge_each([X],Temp1,Temp2),
	sort(Temp2,Prime_sh),
	take_coupled(Sh,Sv,Coupled),
	change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
shfrnv_product(nf,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
	project_share(VarsY,Sh,Temp),
	closure_under_union(Temp,Temp1),
	merge_each([X],Temp1,Temp2),
	sort(Temp2,Prime_sh),
	take_coupled(Sh,Sv,Coupled),
	change_values_if_f(Coupled,Lda_fr,Tmp_fr,nf),
	change_values([X],Tmp_fr,Prime_fr,nv).
	
%-------------------------------------------------------------------------
% shfrnv_identical_one_var(+,+,+,+,-)                                    |
% shfrnv_identical_one_var(X,Y,Call,Proj,Succ)                           |
%-------------------------------------------------------------------------

shfrnv_identical_one_var(X,Y,Call,_Proj,Succ):-
	ground(Y),!,
	Call = (Call_sh,Call_fr),
	( update_lambda_non_free([X],Call_fr,Call_sh,Succ_fr,Succ_sh) ->
	  Succ = (Succ_sh,Succ_fr)
	; Succ = '$bottom'
	).
shfrnv_identical_one_var(X,Y,Call,Proj,Succ):-
	var(Y),!,
	Proj = (_Sh,Fr),
	var_value(Fr,X,ValueX),
	var_value(Fr,Y,ValueY),
	shfrnv_identical(ValueX,ValueY,X,Y,Call,Succ).
%%%%% COMMENT the cases in which Y is a complex term missing
shfrnv_identical_one_var(_X,_Y,_Call,_Proj,'$bottom').

%-------------------------------------------------------------------------
% shfrnv_identical(+,+,+,+,+,-)                                          |
% shfrnv_identical(ValueX,ValueY,X,Y,Call,Succ)                          |
%-------------------------------------------------------------------------

shfrnv_identical(g,f,_X,_Y,_Call,'$bottom'):- !.
shfrnv_identical(f,g,_X,_Y,_Call,'$bottom'):- !.
shfrnv_identical(nv,f,_X,_Y,_Call,'$bottom'):- !.
shfrnv_identical(f,nv,_X,_Y,_Call,'$bottom'):- !.
shfrnv_identical(g,g,_X,_Y,Proj,Proj):- !.
shfrnv_identical(ValueX,ValueY,X,Y,Call,Succ):-
	(ValueX=g;ValueY=g),!,
	Call = (Call_sh,Call_fr),
	( update_lambda_non_free([X,Y],Call_fr,Call_sh,Succ_fr,Succ_sh) ->
	  Succ = (Succ_sh,Succ_fr)
	; Succ = '$bottom'
	).
shfrnv_identical(ValueX,ValueY,X,Y,(Call_sh,Call_fr),Succ):- 
	ord_split_lists(Call_sh,X,Intersect,Disjoint),
	ord_split_lists(Disjoint,Y,NonPossibleY,PossibleNonXY),
	ord_split_lists(Intersect,Y,PossibleXY,NonPossibleX),
	varset(p(NonPossibleX,NonPossibleY),Coupled),
	varset(p(PossibleXY,PossibleNonXY),NonCoupled),
	ord_subtract(Coupled,NonCoupled,NewGround),
	( values_differ(NewGround,Call_fr,f) ->
	  merge(PossibleXY,PossibleNonXY,Succ_sh),
	  shfrnv_less(ValueX,ValueY,Val),
	  sort([X,Y],Vars),
	  change_values(Vars,Call_fr,Succ_fr,Val), 
%%%% COMMENT This can introduce inconsistent sharing abstractions
	  Succ = (Succ_sh,Succ_fr)
	; Succ = '$bottom'
	). 

shfrnv_less(nv,_,nv):- !.
shfrnv_less(_,nv,nv):- !.
shfrnv_less(f,_,f):- !.
shfrnv_less(_,f,f):- !.
shfrnv_less(nf,nf,nf).

%-------------------------------------------------------------------------
% obtain_prime_var_var(+,+,-)                                            |
% obtain_prime_var_var([X/V,Y/V],Call,Success)                           |
%-------------------------------------------------------------------------

shfrnv_obtain_prime_var_var([X/f,Y/f],(Call_sh,Call_fr),Succ):- !,
	ord_split_lists(Call_sh,X,Intersect,Disjoint),
	ord_split_lists(Disjoint,Y,OnlyY,NonXY),
	ord_split_lists(Intersect,Y,XY,OnlyX),
	merge_lists(OnlyY,OnlyX,BothXY),
	merge(XY,NonXY,Succ1),
	merge(BothXY,Succ1,Succ_sh),
	Succ = (Succ_sh,Call_fr).
shfrnv_obtain_prime_var_var([X/VX,Y/VY],Call,Succ):-
	( (VX=nv; VY=nv) ->
	    Prime = ([[X,Y]],[X/nv,Y/nv])
	;   Prime = ([[X,Y]],[X/nf,Y/nf])),
	shfrnv_extend(Prime,[X,Y],Call,Succ).

%-------------------------------------------------------------------------
% shfrnv_mynonvar(+,+,+)                                                 |
% shfrnv_mynonvar(Vars,Fr,Fv)                                            |
%-------------------------------------------------------------------------

shfrnv_mynonvar([],_Sh,_Free).
shfrnv_mynonvar([F|Rest],Sh,Free):-
	insert(Free,F,Vars),
	share_project(Vars,Sh,NewSh),
	shfrnv_impossible(NewSh,NewSh,Vars),!,
	shfrnv_mynonvar(Rest,Sh,Free).
	
shfrnv_impossible([Element|Sh],Sh1,Vars):-
	shfrnv_possible(Element,Sh1,Vars,Temp), !,
	sort([Element|Temp],Elements),
	ord_subtract(Sh,Elements,NewSh),
	shfrnv_impossible(NewSh,Sh1,Vars).
shfrnv_impossible(X,_,_):-
	X = [_|_].
	
shfrnv_possible(Vars,_Sh1,OldVars,Elements):- 
	Vars == OldVars,!,
	Elements = [].
shfrnv_possible(Vars,Sh1,OldVars,[S|NewElements]):-
	shfrnv_take_element_free(Sh1,Vars,NewSh1,S),
	merge(S,Vars,NewVars),
	shfrnv_possible(NewVars,NewSh1,OldVars,NewElements).
		
shfrnv_take_element_free([S|Sh],OldVars,NewSh,NewS):-
	\+ (ord_intersect(S,OldVars)),!,
	NewSh = Sh,
	NewS = S.
shfrnv_take_element_free([S|Sh],OldVars,[S|NewSh],NewS):-
	shfrnv_take_element_free(Sh,OldVars,NewSh,NewS).

%% shfrnv_non_free_to_ground((_,Lcall_fr),(Lsucc_sh,Lsucc_fr),(Lsucc_sh,Lsucc_fr)):-
%% 	shfrnv_compare_free_to_ground(Lcall_fr,Lsucc_fr), !.
%% shfrnv_non_free_to_ground(_,_,'$bottom').
%% 
%% shfrnv_compare_free_to_ground([],[]).
%% shfrnv_compare_free_to_ground([X/Xf|Xs],[X/Yf|Ys]):-
%% 	Xf = f, !,
%% 	Yf \== g, Yf \== nv, %% CHNAGED
%% 	shfrnv_compare_free_to_ground(Xs,Ys).
%% shfrnv_compare_free_to_ground([_|Xs],[_|Ys]):- !,
%% 	shfrnv_compare_free_to_ground(Xs,Ys).

%------------------------------------------------------------------------
% shfrnv_update_from_values(+,+,+,+,+,-)                                |
% shfrnv_update_from_values(ValueX,ValueY,X,Y,Call,Succ)                |
%------------------------------------------------------------------------
% It returns the adecuate values of Success for length(X,Y) when both X |
% and Y are variables. It is based on the freeness values of X and Y.   |
%------------------------------------------------------------------------

shfrnv_update_from_values(g,g,_,_,Proj,Proj):- !.
shfrnv_update_from_values(g,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):-
	update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).
shfrnv_update_from_values(f,g,X,_Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- !,
	take_coupled(Call_sh,[X],Coupled),
	change_values_if_f(Coupled,Call_fr,Tmp_fr,nf),
	change_values([X],Tmp_fr,Succ_fr,nv),
	Succ_sh = Call_sh.
shfrnv_update_from_values(f,f,_X,_Y,_Proj,'$bottom'):- !.
shfrnv_update_from_values(f,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
	update_lambda_non_free([Y],Call_fr,Call_sh,Tmp_fr,Succ_sh),!,
	take_coupled(Succ_sh,[X],Coupled),
	change_values_if_f(Coupled,Tmp_fr,Tmp1_fr,nf),
	change_values([X],Tmp1_fr,Succ_fr,nv).
shfrnv_update_from_values(f,_,_X,_Y,_Proj,'$bottom').
shfrnv_update_from_values(nv,g,_X,_Y,Proj,Proj):- !.
shfrnv_update_from_values(nv,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
	update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).
shfrnv_update_from_values(nf,g,_X,_Y,Proj,Proj):- !.
shfrnv_update_from_values(nf,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
	update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).


%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%           ABSTRACT meta_call
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% identical to shfr_unknown_call, called from domain_dependent.pl        %
%-------------------------------------------------------------------------

%% %%%%%%%%%% ANNOTATION PROCESS
%% %-------------------------------------------------------------------------
%% % update_lambda_non_free_iterative(+,+,+,-,-,-)
%% % update_lambda_non_free_iterative(Ground,Freeness,Sh,NewFreeness,NewSh)
%% % Identical to update_lambda_non_free but:
%% %-------------------------------------------------------------------------
%% 
%% update_lambda_non_free_iterative([],V,L,V,L,[]).
%% update_lambda_non_free_iterative([X|Xs],V,L,V1,L1,NewGi):-
%% 	member_value_freeness(V,AlreadyGround,g),
%% 	ord_subtract([X|Xs],AlreadyGround,MakeGround),
%% 	take_ground_dep(MakeGround,MakeGround,V,L,TestVars,[],NewGround),
%% 	ord_split_lists_from_list(TestVars,L,_Intersect,Disjoint),
%% 	ord_subtract(MakeGround,NewGround,RestGround),
%% 	loop_ground(RestGround,Disjoint,L1,Vars),
%% 	merge(TestVars,Vars,NewGi),
%% 	change_values(MakeGround,V,V1,g).
%% 
%% loop_ground([],L1,L1,[]).
%% loop_ground([X|RestGround],L,L1,[X|Vars]):-
%% 	ord_split_lists(L,X,_Intersect,Disjoint),
%% 	merge_list_of_lists(Disjoint,NonGround),
%% 	ord_intersection(RestGround,NonGround,RestVars),
%% 	loop_ground(RestVars,Disjoint,L1,Vars).
%% 
%% take_ground_dep([],_,_V,_L,[],G,G).
%% take_ground_dep([X|Xs],Vars,V,L,TestVars,TempG,NewG):-
%% 	check_nonvar(X,L,V,Intersect,StronglyCoupled),!,
%% 	check_nobody_makes_ground(Vars,X,Intersect,Projected),
%%  	(Projected = [[]|_] ->     % nobody in Vars makes X ground
%% 	 TestVars = [X|RestVars],
%% 	 ord_intersection(Vars,StronglyCoupled,AlreadyGround),
%% 	 merge(AlreadyGround,TempG,NewTempG)
%% 	; TestVars = RestVars,
%% 	  NewTempG = TempG
%% 	),
%% 	take_ground_dep(Xs,Vars,V,L,RestVars,NewTempG,NewG).
%% 
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
%                        DELAY PREDICATES
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% Assumptions: programs are normalized.
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% shfrnv_check_cond(+,+,-)
% shfrnv_check_cond(Conds,ACns,Flag)
%-------------------------------------------------------------------------
% Identical, but nonvar variables help in definitely woken (5th clause)  %
%-------------------------------------------------------------------------

%% :- push_prolog_flag(multi_arity_warnings,off).
%% 
%:- export(shfrnv_check_cond/5).
%% shfrnv_check_cond(Conds,(Sh,Fr),Sv,Flag,WConds):-
%% 	shfrnv_check_cond(Conds,(Sh,Fr),Sv,[],Flag,[],WConds).
%% 
%% shfrnv_check_cond([],_,_,Acc,Flag,WAcc,WConds):-
%% 	( Acc = [] ->
%% 	    Flag = d
%% 	; Flag = Acc,
%% 	  WConds = WAcc).
%% shfrnv_check_cond([(Gr,Nv,Eq)|Rest],ASub,Sv,Acc,Flag,WAcc,WConds):-
%% 	( shfrnv_make_awoken(ASub,Gr,Nv,Eq,Sv,Flag2) -> 
%% 	    ( Flag2 = w ->
%% 		Flag = w,
%% 	        WConds = [(Gr,Nv,Eq)]
%% 	    ;   shfrnv_check_cond(Rest,ASub,Sv,[Flag2|Acc],Flag,[(Gr,Nv,Eq)|WAcc],WConds))
%% 	; shfrnv_check_cond(Rest,ASub,Sv,Acc,Flag,WAcc,WConds)).
%% 
%% :- pop_prolog_flag(multi_arity_warnings).
%% 
%% shfrnv_make_awoken((Sh,Fr),Gr,Nv,Eq,Sv,Flag):-
%% 	member_value_freeness(Fr,OldGr,g),
%% 	ord_subtract(Gr,OldGr,NewGr),
%% 	( NewGr = [] ->
%% 	    TmpFr = Fr,
%% 	    NewSh = Sh,
%% 	    AllGr = OldGr
%% 	; Flag0 = diff,
%% 	  update_lambda_non_free(NewGr,Fr,Sh,TmpFr,NewSh),
%% 	  member_value_freeness(TmpFr,AllGr,g)),
%% 	member_value_freeness(TmpFr,OldNv,nv),
%% 	ord_subtract(Nv,AllGr,TmpNv),
%% 	ord_subtract(TmpNv,OldNv,NewNv),
%% 	member_value_freeness(TmpFr,Free,f),
%% 	ord_intersection(Free,NewNv,[]),
%% 	( shfrnv_mynonvar(NewNv,NewSh,Free) ->
%% 	    NewFr = TmpFr
%% 	; Flag0 = diff,
%% 	  change_values(NewNv,TmpFr,NewFr,nv)),
%% 	( var(Flag0) ->
%% 	    shfr_check_eq(Eq,AllGr,Free,NewFr,NewSh,Sv,Flag)
%% 	; shfr_project((NewSh,NewFr),Sv,Flag)).
%% 	  
%% 	
%% %% shfrnv_check_cond([(Gr,_)|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %% 	ord_intersect(Gr,NonGround),!, % definitely delays 
%% %% 	shfrnv_check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag).
%% %% shfrnv_check_cond([(_,Nv)|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %% 	ord_intersect(Nv,Free),!,      % definitely delays 
%% %% 	shfrnv_check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag).
%% %% shfrnv_check_cond([(Gr,Nv)|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %% 	ord_subtract(Gr,Ground,PossibleNonG),
%% %% 	PossibleNonG \== [],!,         % possibly woken
%% %% 	update_lambda_non_free(PossibleNonG,Fr,Sh,TmpFr,SuccSh),
%% %% 	change_values_if_not_g(Nv,TmpFr,SuccFr,nv),
%% %% 	shfr_project((SuccSh,SuccFr),Sv,Proj),
%% %% 	Acc0 = [Proj|Acc],
%% %% 	shfrnv_check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc0,Flag).
%% %% shfrnv_check_cond([(_,Nv)|_],Free,_,NonVar,_,Sh,_,_,_,Flag):-
%% %% 	ord_subtract(Nv,NonVar,PossibleFree),
%% %% 	mynonvar(PossibleFree,Sh,Free),!, % definitely woken
%% %% 	Flag = w.
%% %% shfrnv_check_cond([_|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %% 	shfr_project((Sh,Fr),Sv,Proj),
%% %% 	shfrnv_check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,[Proj|Acc],Flag).
%% 
%% %-------------------------------------------------------------------------
%% % shfr_downwards_closed(+,+,-)
%% % shfr_downwards_closed(ACns1,ACns2,ACns)
%% %-------------------------------------------------------------------------
%% % ACns2 must be more instantiated than ACns1 but some downwards closed
%% % properties might have been lost due to a later lub. Thus, those
%% % properties must be returned to ACns2. Iff something non ground becomes 
%% % ground or something free becomes non-free in ACns2, ACns1 is more 
%% % instantiated than ACns2 and we fail. Otherwise we propagate these
%% %  properties from ACns1 to ACns2.
%% %-------------------------------------------------------------------------
%% 
%:- export(shfrnv_downwards_closed/3). 
%% shfrnv_downwards_closed((_,Fr1),(Sh2,Fr2),(Sh,Fr)):- 
%% 	member_value_freeness(Fr1,Gv,g),
%% 	collect_vars_freeness(Fr2,Sv),
%% 	ord_intersection(Gv,Sv,NewGr),
%% 	update_lambda_non_free(NewGr,Fr2,Sh2,TmpFr,Sh),
%% 	member_value_freeness(Fr1,Nv,nv),
%% 	member_value_freeness(TmpFr,Free,f),
%% 	ord_intersection(Free,Nv,[]),
%%         change_values_if_not_g(Nv,TmpFr,Fr,nv).
%% 	
%% 
%% %-------------------------------------------------------------------------
%% % shfrnv_extend_free(+,+,-)
%% % shfrnv_extend_free(ASub,Vars,NewASub)
%% %-------------------------------------------------------------------------
%% % Identical to shfr, called from domain_dependent.pl                     %
%% %-------------------------------------------------------------------------
%% 
%% %------------------------------------------------------------------------%
%% % shfrnv_hash(+,-)
%% % shfrnv_hash(ASub,N)
%% %------------------------------------------------------------------------%
%% % Returns an atom which identifies ASub
%% %------------------------------------------------------------------------%
%% 
%:- export(shfrnv_hash/3).    
%% shfrnv_hash('$bottom',_,-2).
%% shfrnv_hash(true,_,0).
%% shfrnv_hash((Sh,Fr),Fnv,N):-
%% 	\+ \+
%% 	(  primes(Primes),
%% %%	   collect_vars_freeness(Fr,Vars),
%% %%	   append(Vars,_,Primes),
%% 	   append(Fnv,_,Primes),
%% 	   shfrnv_hash_fr(Fr,0,N1),
%% 	   sum_list_of_lists(Sh,N1,N2),
%% 	   recorda_internal('$hash',N2,_)
%%         ),
%% 	recorded_internal('$hash',N,Ref),
%% 	erase(Ref).
%% 
%% shfrnv_hash_fr([],N,N).
%% shfrnv_hash_fr([X/V|Rest],N0,N):-
%% 	( V = f ->
%% 	    N1 is N0+X
%% 	; ( V = g ->
%% 	    N1 is N0-X 
%% 	  ; ( V = nv ->
%% 	      N1 is N0+ (2*X)
%% 	    ; N1 = N0
%% 	    )
%%           )
%%         ),
%% 	shfrnv_hash_fr(Rest,N1,N).
%% 
%% %------------------------------------------------------------------------%
%% % shfrnv_convex_hull(+,+,-)
%% % shfrnv_convex_hull(Old,New,Hull)
%% %------------------------------------------------------------------------%
%% % Computes the convex hull between the initial abstraction Old and the
%% % more instantiated one New           
%% %------------------------------------------------------------------------%
%% 
%:- export(shfrnv_convex_hull/3).
%% shfrnv_convex_hull((OldSh,OldFr),(_,NewFr),(HullSh,HullFr)):- !,
%% 	closure_under_union(OldSh,HullSh),
%% 	shfrnv_hull(OldFr,NewFr,HullFr).
%% shfrnv_convex_hull(_,_,'$bottom').
%% 
%% shfrnv_hull([],[],[]).
%% shfrnv_hull([X/V1|OldFr],[Y/V2|NewFr],[X/V|HullFr]):-
%% 	X == Y,
%% 	shfrnv_hull0(V1,V2,V),
%% 	shfrnv_hull(OldFr,NewFr,HullFr).
%% 	
%% shfrnv_hull0(nf,_,nf).
%% shfrnv_hull0(g,_,g).
%% shfrnv_hull0(f,f,f):- !.
%% shfrnv_hull0(f,_,nf).
%% shfrnv_hull0(nv,_,nv).
%% 
%% %-------------------------------------------------------------------------
%% % shfrnv_impose_cond(+,+,+,-)
%% % shfrnv_impose_cond(Conds,ACns,Sv,LASub)
%% %-------------------------------------------------------------------------
%% 
%:- export(shfrnv_impose_cond/4).
%% shfrnv_impose_cond([],_,_,[]).
%% shfrnv_impose_cond([(Gr,Nv,_)|Rest],Sv,(Sh,Fr),[ASub1|LASub]):-
%% 	update_lambda_sf(Gr,Fr,Sh,Fr1,Sh1),
%%         change_values_if_not_g(Nv,Fr1,Fr2,nv),
%% 	shfr_project((Sh1,Fr2),Sv,ASub1),
%% 	shfrnv_impose_cond(Rest,Sv,(Sh,Fr),LASub).
%% 
%% 
%% %-------------------------------------------------------------------------
%% % shfrnv_real_conjoin(+,+,-)
%% % shfrnv_real_conjoin(ACns1,ACns2,Conj)
%% %-------------------------------------------------------------------------
%% 
%:- export(shfrnv_real_conjoin/3).
%% shfrnv_real_conjoin(_,'$bottom','$bottom'):- !.
%% shfrnv_real_conjoin('$bottom',_,'$bottom').
%% shfrnv_real_conjoin((ShOld,FrOld),(ShNew,FrNew),(Sh,Fr)):-
%% 	member_value_freeness(FrNew,Gv,g),
%% 	update_lambda_sf(Gv,FrOld,ShOld,TmpFr,Sh0),
%% 	member_value_freeness(FrNew,Nv,nv),
%%         change_values_if_not_g(Nv,TmpFr,Fr,nv),
%%         ( (Sh0 == ShNew;all_singletons(ShNew)) ->
%% 	    Sh = Sh0
%% 	; %write(user,'WARNING: a complete conjunction needed'),
%% 	  merge(ShNew,Sh0,Sh)).
%% 
%% all_singletons([]).
%% all_singletons([[_]|Rest]):-
%% 	all_singletons(Rest).
