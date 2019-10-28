:- module(sharing_clique, [], [assertions, isomodes]).

:- doc(title, "CLIQUE-Sharing domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

:- include(ciaopp(plai/plai_domain)).
:- dom_def(share_clique).
:- dom_impl(share_clique, amgu/4).
:- dom_impl(share_clique, augment_asub/3).
:- dom_impl(share_clique, call_to_entry/9).
:- dom_impl(share_clique, exit_to_prime/7).
:- dom_impl(share_clique, project/5).
:- dom_impl(share_clique, compute_lub/2).
:- dom_impl(share_clique, identical_abstract/2).
:- dom_impl(share_clique, abs_sort/2).
:- dom_impl(share_clique, extend/5).
:- dom_impl(share_clique, less_or_equal/2).
:- dom_impl(share_clique, glb/3).
:- dom_impl(share_clique, eliminate_equivalent/2).
:- dom_impl(share_clique, call_to_success_fact/9).
:- dom_impl(share_clique, special_builtin/5).
:- dom_impl(share_clique, success_builtin/6).
:- dom_impl(share_clique, call_to_success_builtin/6).
:- dom_impl(share_clique, input_interface/4).
:- dom_impl(share_clique, input_user_interface/5).
:- dom_impl(share_clique, asub_to_native/5).
:- dom_impl(share_clique, unknown_call/4).
:- dom_impl(share_clique, unknown_entry/3).
:- dom_impl(share_clique, empty_entry/3).
% :- dom_impl(share_clique, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub)).

%------------------------------------------------------------------------%
% This file contains the domain dependent abstract functions for the     |
% clique-sharing domain defined by Hill, Bagnara and Zaffanella (for     |
% bottom-up analysis and inferring pair-sharing).                        |
%------------------------------------------------------------------------%
% The representation of this domain is different from Set-Sharing. It is |
% made up of two components: one is the original set-sharing domain      |
% while the other represents all possible subsets of each of its         |
% elements.                                                              |
% SH = (Cl,Sh) where Sh is the known Set-Sharing and Cl is the           |
% clique-set.                                                            |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharing.pl                 
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% REMARK: In order to number how many widening process have been
% performed, we assert a fact for each one. To take time measurings, we
% recommend you to comment it.
%------------------------------------------------------------------------%

:- doc(bug,"1. In case of success multivariance the predicate
           eliminate_equivalent/2 must be redefined.").
:- doc(bug,"2. The builtin ==/2 is defined but it is not used. For 
	   its use, comment it out in special_builtin.").
:- doc(bug,"3. The builtins read/2 and length/2 are used in a simple
	   way. In order to use more complex definitions, comment it in 
	   special_builtin.").
:- doc(bug,"4. The non-redundant version is not working because the 
	   semantics of the builtins has not been defined yet.").

:- use_module(library(lsets), 
	       [sort_list_of_lists/2,
		ord_split_lists_from_list/4,
		merge_list_of_lists/2,
		ord_member_list_of_lists/2
		]).	  
:- use_module(library(sets), 
              [
	       ord_subset/2,
	       ord_subtract/3,
	       ord_union/3,
	       ord_intersection/3,
	       ord_member/2,
	       merge/3,
	       insert/3,
	       ord_intersection_diff/4
	       ]).
:- use_module(library(lists), 
              [delete/3,               
	       append/3,
	       powerset/2,
	       list_to_list_of_lists/2
	       ]).
:- use_module(library(sort), 
	      [sort/2]).	
:- use_module(library(terms_vars), [varset/2]).

:- use_module(domain(share_amgu_sets)).
:- use_module(domain(s_grshfr), 
        [projected_gvars/3]).
:- use_module(domain(share_clique_aux), [
	widen/1,
	type_widening/1,
	type_widening_condition/1,
	widen_upper_bound/1,
	widen_lower_bound/1]).
:- use_module(domain(share_aux), [
	eliminate_couples/4,
	handle_each_indep/4,
	eliminate_if_not_possible/3,
	test_temp/2,
	eliminate_if_not_possible/4]).
:- use_module(domain(share_aux), [append_dl/3]).
:- use_module(domain(share_clique_1_aux),
	[split_list_of_lists_singleton/3,
 	 share_clique_1_normalize/4]).

:- use_module(domain(sharing)).
:- use_module(domain(share_clique_aux)).
:- use_module(domain(share_amgu_aux)).
:- use_module(domain(share_aux), [if_not_nil/4,handle_each_indep/4]).

:- use_module(library(lists), [length/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(aggregates), [findall/3]). % (for number_of_widening/1)
:- use_module(library(messages), [error_message/1]).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_call_to_entry(+,+,+,+,+,+,+,-,?)                          |
%------------------------------------------------------------------------%
:- export(share_clique_call_to_entry/9).
share_clique_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
     variant(Sg,Head),!,
     ExtraInfo = yes,
     copy_term((Sg,Proj),(NewSg,NewProj)),
     Head = NewSg,
     share_clique_abs_sort(NewProj,(Cl,Temp)),
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp,Sh),
     %Entry = (Cl,Sh).
     share_clique_normalize((Cl,Sh),Entry).
share_clique_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,ExtraInfo):- !,
     ExtraInfo = no,
     list_to_list_of_lists(Fv,Sh_Entry),
     %Entry = ([],Sh_Entry).
     share_clique_normalize(([],Sh_Entry),Entry).
share_clique_call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
     % groundness propagation to exit_to_prime
     projected_gvars_clique(Proj,Sv,Gv_Call),
     peel_equations( Sg,Head, Equations),
     share_clique_augment_asub(Proj,Hv,ASub),     
     share_clique_iterate(Equations,star,ASub,ASub1),
     share_clique_widen(plai_op,ASub1,_,Result),
     share_clique_project(Sg,Hv,not_provided_HvFv_u,Result,Entry0),
     share_clique_augment_asub(Entry0,Fv,Entry1),   
     %Entry1 = Entry,
     share_clique_normalize(Entry1,Entry),
     ExtraInfo = (Equations,Gv_Call),!.
share_clique_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).

%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_exit_to_prime(+,+,+,+,+,-,-)                              |
%------------------------------------------------------------------------%

:- export(share_clique_exit_to_prime/7).            
share_clique_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
share_clique_exit_to_prime(Sg,Hv,Head,_Sv,Exit,Flag,Prime):-  
     Flag == yes, !,
     share_clique_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
     copy_term((Head,BPrime),(NewHead,NewPrime)),
     Sg = NewHead,
     share_clique_abs_sort(NewPrime,Prime).
share_clique_exit_to_prime(_,[],_,_,_,_,([],[])):- !.
share_clique_exit_to_prime(Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Gv_Call),     	
     share_clique_augment_asub(Exit,Sv,ASub),     
     share_clique_iterate(Equations,star,ASub, Prime0),
     share_clique_widen(plai_op,Prime0,_,Prime1),
     share_clique_project(Sg,Sv,not_provided_HvFv_u,Prime1,(Cl,Sh)),
     % groundness propagation from call_to_entry
     irrel_w(Gv_Call,(Cl,Sh),(Cl1,Sh1)),
     Prime = (Cl1,Sh1).

%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_amgu(+,+,+,-)                                             %
% share_clique_amgu(Sg,Head,ASub,AMGU)                                   %
% @var{AMGU} is the abstract unification between @var{Sg} and @var{Head}.%
%------------------------------------------------------------------------%
:- export(share_clique_amgu/4).
share_clique_amgu(Sg,Head,ASub,AMGU):-
	peel_equations(Sg, Head,Eqs),
	share_clique_iterate(Eqs,star,ASub,AMGU),!.

%------------------------------------------------------------------------%
%                            ABSTRACT Iterate                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_iterate(+,+,+,-)                                          %
% share_clique_iterate(Eqs,Flag,ASub0,ASub)                              %
% For each equation in Eqs, it performs the amgu.                        %
%------------------------------------------------------------------------%

share_clique_iterate([],_,ASub, ASub).
share_clique_iterate([(X,Ts)|Eqs],Flag,ASub, ASub2):-
     amgu_clique(X,Ts,Flag,ASub,ASub1),
     share_clique_iterate(Eqs,Flag,ASub1, ASub2).

%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_extend(+,+,+,+,-)                                         |
% share_clique_extend(Sg,Prime,Sv,Call,Succ)                             |
%------------------------------------------------------------------------%
:- export(share_clique_extend/5).
share_clique_extend(_Sg,'$bottom',_Hv,_Call,Succ):- !,
     Succ = '$bottom'.
share_clique_extend(_Sg,_Prime,[],Call,Succ):- !,
     Call = Succ.
share_clique_extend(_Sg,Prime,Sv,Call,Succ):-!,
%open('clsh.pl',append,Fd),
     Call = (Call_Cl,Call_Sh),
     split_list_of_lists(Sv,Call_Cl,Call_Cl_g,_),	
     split_list_of_lists(Sv,Call_Sh,Call_Sh_g,Irrel_Sh),	
     delete_vars_from_list_of_lists(Sv,Call_Cl,Irrel_Cl),	
     star_w((Call_Cl_g,Call_Sh_g),(Cl1,Sh1)), 
%------------------------------------------------------------------------%
% REMARK:In order to be able to go on with the analysis, if |sh2| > 0    |
% then |cl'| must not be greater than 10.                                |
%------------------------------------------------------------------------%
     normalize_if_clsh_needs(Prime,Cl1,NewPrime),
     NewPrime = (Cl2,Sh2),
%------------------------------------------------------------------------%
     % clique of Call clique "allowed" by the Primer clique
     extendcl(Cl2,Cl1,Sv,Irrel_Cl,Extcl0),
     % sharing of Call sharing "allowed" by the Prime clique
     shcl(Sh1,Cl2,Sv,[],ShCl),
     % Remove extcl from Cl* (cliques in the success). In this way,
     % clsh is more efficient and the result less redundant
     delete_list_of_lists(Cl1,Extcl0,Cl12),
     % sharing of Call clique "allowed" by the Prime sharing     
%statistics(walltime,[Time1|_]),
     clsh(Cl12,Sh2,Sv,[],ClSh),
%statistics(walltime,[Time2|_]),
%Time is Time2 - Time1,
%writeq(Fd,time(Time)),writeq(Fd,'.'),
%close(Fd),
     % Since after clsh/5 the sharing can grow too much
     % it's necessary to use 'inter_1'
     share_clique_widen(aamgu,inter_1,([],ClSh),_,(Extcl1,ClSh1)),
     % if here we normalize qplan doesn't run
     %share_clique_normalize((Extcl2,ClSh2),(Extcl1,ClSh1)),
     % sharing of Call sharing "allowed" by the Prime sharing 
     prune_success(Sh1,Sh2,Sv,Irrel_Sh,Extsh0), 
     ord_union(Extsh0,ShCl,Extsh1),
     ord_union(Extsh1,ClSh1,Extsh),
     ord_union(Extcl0,Extcl1,Extcl),
     eliminate_redundancies((Extcl,Extsh),Succ).

normalize_if_clsh_needs((Cl2,[]),_,(Cl2,[])):-!.
normalize_if_clsh_needs((Cl2,Sh2),Cl1,(NewCl2,NewSh2)):-
	T = 7,
	( asub_gt(Cl1,T) ->
	  share_clique_normalize((Cl2,Sh2),100,1,(NewCl2,NewSh2))
        ;
	  (NewCl2,NewSh2) = (Cl2,Sh2)
        ).

:- export(asub_gt/2).
asub_gt([S|Ss],T):-
	length(S,LS),!,
	( LS > T ->
	  true
	;
	  asub_gt(Ss,T)
        ).

:- export(prune_success/5).	
prune_success([],_Prime,_Sv,Succ,Succ).
prune_success([Xs|Xss],Prime,Sv,Call,Succ) :-
     ord_intersection(Xs,Sv,Xs_proj),
     ( ord_member(Xs_proj,Prime) ->
       insert(Call,Xs,Temp)
     ; Temp = Call
     ),
     prune_success(Xss,Prime,Sv,Temp,Succ).

%------------------------------------------------------------------------%
% extendcl(Prime,Call_g*,Sv) =                                           |
% {s'/\s \ U (s' \ g) | s' \in Call_g*, s \in Prime}                     |
% clique groups of the call clique part allowed by the prime clique part |
%------------------------------------------------------------------------%

extendcl([],_,_,Irrel,Irrel).
extendcl([S_cl2|S_cl2s],Cl1,Vars,Irrel,Extendcl):-
	extendcl_(Cl1,S_cl2,Vars,Res),
	extendcl(S_cl2s,Cl1,Vars,Irrel,Result),
	ord_union(Result,Res,Extendcl).
extendcl_([],_,_,[]).
extendcl_([S|Ss],S_cl2,Vars,[Res|Result]):-
	ord_intersection(S_cl2,S,Int),
	ord_subtract(S,Vars,Disj),
	ord_union(Int,Disj,Res),
	extendcl_(Ss,S_cl2,Vars,Result).
extendcl_([_|Ss],S_cl2,Vars,Result):-
	extendcl_(Ss,S_cl2,Vars,Result).

%------------------------------------------------------------------------%
% clsh(cl',sh2,g) = {s | s \subseteq c \in cl', (s/\g) \in sh2}          |
% sharing groups of call clique part allowed by the prime sharing part   |
%------------------------------------------------------------------------%

clsh(Cl,Sh2,Sv,Call,Succ):-
	widen(off),!,
	clsh_more_precise(Cl,Sh2,Sv,Call,Succ).
clsh(Cl,Sh2,Sv,Call,Succ):-
	type_widening(WT),!,
	( (WT == panic_1 ; WT == panic_2) ->
	  clsh_more_efficient(Cl,Sh2,Sv,Call,Succ)
        ; 
          clsh_more_precise(Cl,Sh2,Sv,Call,Succ)
        ).

clsh_more_precise(_,[],_,Succ,Succ):-!.
clsh_more_precise([Cl|Cls],Sh2,Sv,Call,Succ) :-
	sharing_possible(Sh2,Cl,Sv,Sharing_Allowed),
        ord_subtract(Cl,Sv,Sv_No_Projected),
	powerset_with_empty_set(Sv_No_Projected,Pow_Sv_No_Projected),
	clsh_extend_sharing(Sharing_Allowed,Pow_Sv_No_Projected,Res),
	ord_union(Call,Res,Temp),
        clsh_more_precise(Cls,Sh2,Sv,Temp,Succ).
clsh_more_precise([],_,_,Succ,Succ).

:- export(sharing_possible/4).
sharing_possible([],_,_,[]).
sharing_possible([Sh|Shs],Cl,Sv,[Sh|Shs0]):-
	( ord_subset(Sh,Sv),  % all variables of sh are in Sv
	  ord_subset(Sh,Cl)   % and in Cl
        ),!,
	sharing_possible(Shs,Cl,Sv,Shs0).
sharing_possible([_|Shs],Cl,Sv,Shs0):-
	sharing_possible(Shs,Cl,Sv,Shs0).

clsh_extend_sharing([],_,[]).
clsh_extend_sharing(Sh,[],Sh).
clsh_extend_sharing([S|Ss],Pow,ExtSh):-
        bin_union([S],Pow,Res),
	clsh_extend_sharing(Ss,Pow,Result),
        ord_union(Res,Result,ExtSh).	

:- export(powerset_with_empty_set/2).
powerset_with_empty_set(S,PS):-
	powerset(S,PS0),!,
	( PS0 = [] ->
          PS= PS0
        ; 
	  insert(PS0,[],PS1),
	  sort_list_of_lists(PS1,PS)
        ).

%------------------------------------------------------------------------%
% clsh(cl',sh2,g) = {c| c \in cl', (c /\ g) \supseteq s \in sh2}         |
% More EFFICIENT VERSION but less precise !.                             |
%------------------------------------------------------------------------%

clsh_more_efficient(Cl,Sh2,Sv,Call,Succ):-
       clsh_(Cl,Sh2,Sv,Call,Succ_s),
       sort_list_of_lists(Succ_s,Succ).
	
clsh_([],_Sh2,_Sv,Succ,Succ).
clsh_([C|Cs],Sh2,Sv,Call,Succ):-
	ord_intersection(C,Sv,C_proj),!,
	( ord_superset_lists_with_list(Sh2,C_proj) ->
	  Temp = [C|Call]
        ;
	  Temp = Call
        ),  
	clsh_(Cs,Sh2,Sv,Temp,Succ).

%------------------------------------------------------------------------%
% shcl(sh',cl2,g) = {s| s \in sh', (s /\ g) \subseteq c \in cl2}         |
% sharing groups of call sharing part "allowed" by the prime clique part |
%------------------------------------------------------------------------%

shcl(Xss,Cl,Sv,Call,Succ_s):-
	shcl_(Xss,Cl,Sv,Call,Succ),
	sort_list_of_lists(Succ,Succ_s).

shcl_([],_Cl,_Sv,Succ,Succ).
shcl_([Xs|Xss],Cl,Sv,Call,Succ):-
	ord_intersection(Xs,Sv,Xs_proj),!,
	( ord_subset_lists_with_list(Cl,Xs_proj) ->
	  Temp = [Xs|Call]
        ;
	  Temp = Call
        ),  
	shcl_(Xss,Cl,Sv,Temp,Succ).

%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_augment_asub(+,+,-)                                        |
% Augments the abstract subtitution with fresh variables                 |
%------------------------------------------------------------------------%
:- export(share_clique_augment_asub/3).
share_clique_augment_asub(ASub,[],ASub) :- !.
share_clique_augment_asub(ASub,Vars,ASub_s):-
	share_clique_abs_sort(ASub,SASub),
	sort(Vars,SVars),!,
	share_clique_augment_asub_(SASub,SVars,ASub1),
	share_clique_abs_sort(ASub1,ASub_s).

share_clique_augment_asub_(ASub,[],ASub) :- !.
share_clique_augment_asub_(ASub,[H|T],(Cl,[[H]|Sh])):-
	share_clique_augment_asub_(ASub,T,(Cl,Sh)).

%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% share_clique_project(+,+,+,+,-)                                        |
% share_clique_project(Sg,Vars,HvFv_u,ASub,Proj)                         |
%------------------------------------------------------------------------%
:- export(share_clique_project/5).                  
share_clique_project(_,_,_,'$bottom','$bottom'):- !.
share_clique_project(Sg,Vars,HvFv_u,(Cl,Sh),(Cl0,Sh0)) :-
	share_project(Sg,Vars,HvFv_u,Sh,Sh0),
	intersection_lists_with_list(Cl,Vars,Cl0).

%------------------------------------------------------------------------%
%                      ABSTRACT SORT                                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_abs_sort(+,-)                                                 |
% share_clique_abs_sort(Asub,Asub_s)                                         |
% sorts the set of set of variables ASub to obtaint the Asub_s           |
%-------------------------------------------------------------------------
:- export(share_clique_abs_sort/2).                     
share_clique_abs_sort('$bottom','$bottom'):- !.
share_clique_abs_sort((Cl_ASub,Sh_ASub),(Cl_ASub_s,Sh_ASub_s) ):-
	sort_list_of_lists(Cl_ASub,Cl_ASub_s),
	sort_list_of_lists(Sh_ASub,Sh_ASub_s).

%------------------------------------------------------------------------%
% share_clique_identical_abstract(+,+)                                   |
% share_clique_identical_abstract(ASub0,ASub1)                           |
% Succeeds if the two abstract substitutions are defined on the same     |
% variables and are equivalent                                           |
%------------------------------------------------------------------------%
:- export(share_clique_identical_abstract/2).
share_clique_identical_abstract('$bottom','$bottom'):- !.
share_clique_identical_abstract('$bottom',_):- !,fail.
share_clique_identical_abstract(_,'$bottom'):- !,fail.
share_clique_identical_abstract(ASub0,ASub1):-
	ASub0 == ASub1,!.
share_clique_identical_abstract(ASub0,ASub1):- !,
	share_clique_normalize(ASub0,100,1,NASub0),
	( NASub0 == ASub1 ->
	  true
        ;
	  share_clique_normalize(ASub1,100,1,NASub1),
	  NASub0 == NASub1
        ).

%------------------------------------------------------------------------%
% eliminate_equivalent(+,-)                                              |
% eliminate_equivalent(TmpLSucc,LSucc)                                   |
% The list LSucc is reduced wrt the list TmpLSucc  in that it            | 
% does not contain abstract substitutions which are equivalent.          |
% Note that new clique groups can be introduced because of the use of    |
% normalization process.                                                 |
%------------------------------------------------------------------------%
:- export(share_clique_eliminate_equivalent/2).
share_clique_eliminate_equivalent(TmpLSucc,Succ):-
	sort(TmpLSucc,Succ).

% share_clique_eliminate_equivalent(TmpLSucc,Succ):-
% 	normalize_lists(TmpLSucc,New_TmpLSucc),
% 	sort(New_TmpLSucc,Succ).

% normalize_lists([],[]).
% normalize_lists([X|Xs],[New_X|Res]):-
% 	share_clique_normalize(X,100,1,New_X),
% 	normalize_lists(Xs,Res).
	
%------------------------------------------------------------------------%
% share_clique_less_or_equal(+,+)                                        |
% share_clique_less_or_equal(ASub0,ASub1)                                |
% Succeeds if ASub1 is more general or equal to ASub0                    |
%------------------------------------------------------------------------%

:- export(share_clique_less_or_equal/2).
share_clique_less_or_equal('$bottom',_ASub):- !.
share_clique_less_or_equal(ASub,ASub1):-
	share_clique_normalize(ASub,100,1,(Cl0,Sh0)),
	share_clique_normalize(ASub1,100,1,(Cl1,Sh1)),
	clique_part_less_or_equal(Cl0,Cl1),
	sharing_part_less_or_equal(Sh0,Sh1,Cl1).

:- export(clique_part_less_or_equal/2).
clique_part_less_or_equal(Cl0,Cl1):-
	Cl0 == Cl1,!.
clique_part_less_or_equal(Cl0,Cl1):-
	ord_subset_list_of_lists(Cl0,Cl1),!.

:- export(sharing_part_less_or_equal/3).
sharing_part_less_or_equal(Sh0,Sh1,_Cl1):-
	Sh0 == Sh1,!.
sharing_part_less_or_equal(Sh0,Sh1,Cl1):-
	sharing_part_less_or_equal_(Sh0,Sh1,Cl1).

sharing_part_less_or_equal_([],_Sh1,_Cl1).
sharing_part_less_or_equal_([Sh|Shs],Sh1,Cl1):-
	ord_subset([Sh],Sh1),!,	
        sharing_part_less_or_equal_(Shs,Sh1,Cl1).
sharing_part_less_or_equal_([Sh|Shs],Sh1,Cl1):-
	ord_subset_list_of_lists([Sh],Cl1),!,
        sharing_part_less_or_equal_(Shs,Sh1,Cl1).
	
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts|
%------------------------------------------------------------------------%
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
% Note that if we use Proj we need to call explicitly the function       |
% extend, so we can loose information.                                   |
%------------------------------------------------------------------------%

:- export(share_clique_call_to_success_fact/9).
share_clique_call_to_success_fact(_,[],_Head,_K,Sv,(Cl,Sh),_,([],[]),Succ):-!,
	ord_split_lists_from_list(Sv,Sh,_,Succ_Sh),
	delete_vars_from_list_of_lists(Sv,Cl,Succ_Cl),
	Succ = (Succ_Cl,Succ_Sh).
share_clique_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ):-
% exit_to_prime
	share_clique_augment_asub(Call,Hv,ASub),	
	peel_equations(Sg, Head,Equations),
	share_clique_iterate(Equations,star,ASub,(Cl1,Sh1)),
	share_clique_widen(plai_op,(Cl1,Sh1),_,(Cl,Sh)),
	share_clique_project(Sg,Sv,not_provided_HvFv_u,(Cl,Sh),Prime),
% extend
	delete_vars_from_list_of_lists(Hv,Cl,Succ_Cl),
	delete_vars_from_list_of_lists(Hv,Sh,Succ_Sh),
	share_clique_abs_sort((Succ_Cl,Succ_Sh),Succ),!.
share_clique_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%------------------------------------------------------------------------%
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
%------------------------------------------------------------------------%
:- export(share_clique_call_to_prime_fact/6).
share_clique_call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime
	share_clique_augment_asub(Call,Hv,ASub),	
	peel_equations(Sg, Head,Equations),
	share_clique_iterate(Equations,star,ASub,(Cl1,Sh1)),
	share_clique_widen(plai_op,(Cl1,Sh1),_,(Cl,Sh)),
	share_clique_project(Sg,Sv,not_provided_HvFv_u,(Cl,Sh),Prime),!.
share_clique_call_to_prime_fact(_Sg,_Hv,_Head,_Sv,_Call,'$bottom').
%------------------------------------------------------------------------%
%                      ABSTRACT LUB                                      |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_compute_lub(+,-)                                          |
% share_clique_compute_lub(ListASub,Lub)                                 |
% It computes the lub of a set of Asub. For each two abstract            |
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   |
% merging the ASub1 and ASub2.                                           |
%------------------------------------------------------------------------%
:- export(share_clique_compute_lub/2).
share_clique_compute_lub([ASub1,ASub2|Rest],Lub) :- !,
	share_clique_lub_cl(ASub1,ASub2,ASub3),
	share_clique_widen(extend,ASub3,_,ASub_widen),
	share_clique_compute_lub([ASub_widen|Rest],Lub).
share_clique_compute_lub([ASub],ASub).

:- export(share_clique_lub_cl/3).
share_clique_lub_cl(ASub1,ASub2,ASub3):-
	ASub1 == ASub2,!,
	ASub3 = ASub2.
share_clique_lub_cl(ASub1,ASub2,ASub3):-
	merge_subst(ASub1,ASub2,ASub3).

merge_subst('$bottom',Yss,Yss):- !.
merge_subst(Xss,'$bottom',Xss):- !.
merge_subst((Cl1,Sh1),(Cl2,Sh2),Lub) :-
	merge(Cl1,Cl2,Cl0),
	merge(Sh1,Sh2,Sh0),
%	Lub = (Cl0,Sh0).
	share_clique_normalize((Cl0,Sh0),Lub).

%------------------------------------------------------------------------%
% share_clique_glb(+,+,-)                                                       |
% share_clique_glb(ASub0,ASub1,Lub)                                             |
% Glb is just intersection.                                              |
%------------------------------------------------------------------------%

:- export(share_clique_glb/3).      
share_clique_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
share_clique_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
share_clique_glb(ASub0,ASub1,Glb):- 
	ord_intersection_w(ASub0,ASub1,Glb).

%------------------------------------------------------------------------%
% share_clique_input_user_interface(+,+,-,+,+)                           |
% share_clique_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)  |
% Obtaining the abstract substitution for Sharing from the user supplied |
% information just consists in taking the mshare(Sharing) and            | 
% clique(Clique)element of InputUser and sorting it. If there is no such |
% element, get the "top" sharing for the variables involved.             |
%------------------------------------------------------------------------%

:- export(share_clique_input_user_interface/5).
share_clique_input_user_interface((Gv,Sh,Cl,I),Qv,Call,Sg,MaybeCallASub):-
	share_input_user_interface((Gv,Sh,I),Qv,New_Sh,Sg,MaybeCallASub),
	may_be_var(Cl,Cl0),
	take_ground_out_clique(Gv,Cl0,New_Cl),   
	Call = (New_Cl,New_Sh).
%	share_clique_normalize((New_Cl,New_Sh),Call).

take_ground_out_clique(Gv,Cl,Cl1):-
	ord_split_lists_from_list(Gv,Cl,Intersect,Disjoint),
	delete_vars_from_list_of_lists(Gv,Intersect,Intersect1),
	ord_union(Intersect1,Disjoint,Cl1).
        	
:- export(share_clique_input_interface/4).
share_clique_input_interface(clique(X),perfect,(Gv,Sh,Cl0,I),(Gv,Sh,Cl,I)):-
	nonvar(X),
	sort_list_of_lists(X,ASub),
	myappend(ASub,Cl0,Cl),!.         
share_clique_input_interface(Prop,Any,(Gv0,Sh0,Cl,I0),(Gv,Sh,Cl,I)):-
	share_input_interface(Prop,Any,(Gv0,Sh0,I0),(Gv,Sh,I)).

:- export(may_be_var/2). % TODO: duplicated
may_be_var(X,X):- ( X=[] ; true ), !.

:- export(myappend/3). % TODO: duplicated
myappend(Vs,V0,V):-
	var(Vs), !,
	V=V0.
myappend(Vs,V0,V):-
	merge(Vs,V0,V).

%------------------------------------------------------------------------%
% share_clique_asub_to_native(+,+,+,-,-)                                 |
% share_clique_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)           |
% The user friendly format consists in extracting the ground variables   |
%------------------------------------------------------------------------%

:- export(share_clique_asub_to_native/5). 
share_clique_asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
share_clique_asub_to_native((Cl,Sh),Qv,_OutFlag,Info,[]):-
	ord_union(Sh,Cl,All),
	projected_gvars(All,Qv,Gv),
	if_not_nil(Cl,clique(Cl),Info,Info0),
	if_not_nil(Sh,sharing(Sh),Info0,Info1),
	if_not_nil(Gv,ground(Gv),Info1,[]).

%------------------------------------------------------------------------%
% share_clique_unknown_call(+,+,+,-)                                     |
% share_clique_unknown_call(Sg,Vars,Call,Succ)                           |
% Gives the ``top'' value for the variables involved in a                |
% literal whose definition is not present, and adds this top value to    |
% Call.                                                                  |
%------------------------------------------------------------------------%

:- export(share_clique_unknown_call/4).
share_clique_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
share_clique_unknown_call(_Sg,_Vars,([],[]),([],[])) :- !.
share_clique_unknown_call(_Sg,Vars,(Cl,Sh),Succ):-
	split_list_of_lists(Vars,Cl,Cl_vars,_),
	split_list_of_lists(Vars,Sh,Sh_vars,Irrel_Sh_vars),
	delete_vars_from_list_of_lists(Vars,Cl,Irrel_Cl_vars),
	star_w((Cl_vars,Sh_vars),Star),
	ord_union_w(Star,(Irrel_Cl_vars,Irrel_Sh_vars),Succ).

%------------------------------------------------------------------------%
% share_clique_empty_entry(+,+,-)                                        |
% share_clique_empty_entry(Sg,Vars,Entry)                                |
% Gives the ""empty"" value in this domain for a given set of variables  |
% Vars, resulting in the abstract substitution Entry. I.e.,              |
% obtains the abstraction of a substitution in which all variables       |
% Vars are unbound: free and unaliased. In this domain is the list       |
% of singleton lists of variables in the sharing part. The clique part   |
% is initialized to empty list.                                          |
%------------------------------------------------------------------------%

:- export(share_clique_empty_entry/3).
share_clique_empty_entry(Sg,Vars,Entry):-
	share_empty_entry(Sg,Vars,EntryVars),!,
	Entry = ([],EntryVars).

%------------------------------------------------------------------------%
% share_clique_unknown_entry(+,+,-)                                      |
% share_clique_unknown_entry(Sg,Qv,Call)                                 |
% The top value in Clique for a set of variables is the powerset. It     |
% consits of putting Qv directly in the clique part.                     |
%------------------------------------------------------------------------%
         
:- export(share_clique_unknown_entry/3).
share_clique_unknown_entry(_Sg,Qv,Call):-
	sort(Qv,QvS),	
	Call = (QvS,[]).

%------------------------------------------------------------------------%
% share_clique_widen(+,+,+,-)                                            |
% share_clique_widen(Who,ASub1,ExtraInfo,ASub)                           |
%------------------------------------------------------------------------%
% ASub is the result of widening the abstract substitution ASub1.        |
% This interface is only defined for sake of clarity. Who defines what   |
% operation has called to widen. The actions depend on this argument.    |
% if Who = amgu then the value of widen is amgu.                         |
% if Who = extend then the value of widen is not off                     |
% if Who = plai_op then the value of widen is plai_op                    |
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).
:- export(share_clique_widen/4).
share_clique_widen(_,ASub,_,ASub):-
	widen(off),!.
share_clique_widen(amgu,ASub1,ExtraInfo,ASub):-
	widen(amgu),!,
	type_widening(TWid),
	type_widening_condition(TCond),
	share_clique_widen(TCond,TWid,ASub1,ExtraInfo,ASub).
share_clique_widen(plai_op,ASub1,ExtraInfo,ASub):-
	widen(plai_op),!,
	type_widening(TWid),
	share_clique_widen(aamgu,TWid,ASub1,ExtraInfo,ASub).
share_clique_widen(extend,ASub1,ExtraInfo,ASub):-!,
	type_widening(TWid),
	share_clique_widen(aamgu,TWid,ASub1,ExtraInfo,ASub).
%% 1-clique-sharing
share_clique_widen(amgu_clique_1,ASub1,ExtraInfo,ASub):-
	widen(amgu),!,
	type_widening(NTWid),
	widening_clique_1(NTWid,TWid),
	type_widening_condition(TCond),
	share_clique_widen(TCond,TWid,ASub1,ExtraInfo,ASub).
share_clique_widen(plai_op_clique_1,ASub1,ExtraInfo,ASub):-
	widen(plai_op),!,
	type_widening(NTWid),
	widening_clique_1(NTWid,TWid),
	share_clique_widen(aamgu,TWid,ASub1,ExtraInfo,ASub).
share_clique_widen(extend_clique_1,ASub1,ExtraInfo,ASub):-!,
	type_widening(NTWid),
	widening_clique_1(NTWid,TWid),
	share_clique_widen(aamgu,TWid,ASub1,ExtraInfo,ASub).
% it shouldn't but...
share_clique_widen(_,ASub,_,ASub):-!.

widening_clique_1('cautious','cautious_clique_1'):-!.
widening_clique_1('inter_1','inter_1_clique_1'):-!.
widening_clique_1(_,_):-!,
	error_message("Widening not allowed for 1-clique-sharing").
%------------------------------------------------------------------------%
% share_clique_widen(?,?,+,+,-)                                          |
% share_clique_widen(TCond,TWid,ASub1,ExtraInfo,ASub)                    |
% ASub is the result of widening the abstract substitution ASub1.        |
% TCond is the type of condition used and TWid is the type of widening.  |
%------------------------------------------------------------------------%
% Compute the number of widening done.
% Note that it should be removed if time measuring is required.

:- export(share_clique_widen/5).
share_clique_widen(_,_,ASub,_,ASub):-
	widen(off),!.
share_clique_widen(TCond,TWid,ASub1,ExtraInfo,ASub):-!,
	( share_clique_widening_condition(TCond,ASub1,ExtraInfo)->
	  % inc_widen_done,
	  share_clique_widening(TWid,ASub1,ASub)
          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	  % debug
	  %, ASub1 = (_,Sh1),
	  %size_set_of_sets(Sh1,NSh1),
	  %ASub = (_,Sh),
	  %size_set_of_sets(Sh,NSh),
	  %format("WIDENING: ~d-~d ~n",[NSh1,NSh])
          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	;
	  ASub = ASub1
	).

:- pop_prolog_flag(multi_arity_warnings).
%-------------------------------------------------------------------------%
% share_clique_widening_condition(+,+,+)                                  |
% share_clique_widening_condition(Type,ASub,ExtraInfo)                    |
% Succeeds if ASub satisfies a condition.                                 |
% Type can be:                                                            |
% - aamgu (after amgu). The condition is verified after performing the    |
%   amgu.                                                                 |
% - bamgu (before amgu). An upper bound is computed before performing the |
%   amgu in order to avoid to compute it.                                 |
%-------------------------------------------------------------------------%
share_clique_widening_condition(aamgu,SH,_ExtraInfo):-
	widen_upper_bound(UB),
	size_clsh(SH,N),
	!,	
	N > UB.
share_clique_widening_condition(bamgu,(Cl,Sh),_):-
	compute_upper_amgu(Sh,UB_Sh),
	size_set_of_sets(Cl,Size_Cl),
	UB_ClSh is Size_Cl + UB_Sh,
	widen_upper_bound(UB),
        !,
	UB_ClSh > UB.
%	format("~d > ~d ", [UB_ClSh,UB]).

%------------------------------------------------------------------------%
% share_clique_widening(+,+,-)                                           |
% share_clique_widening(Type,ASub,ASub0)                                 |
% ASub0 is a safe approximation of ASub obtained after widening ASub.    |
%------------------------------------------------------------------------%
% So far, some different widenings are defined:                          |
% W(cl,sh) = (cl U {Ush},\emptyset)     panic_1                          |
% W(cl,sh) = ({Ucl U Ush},\emptyset)    panic_2                          |
% W(cl,sh) = normalize((cl,sh))         cautious                         |
% W(cl,sh) = (cl U sh,\emptyset)        inter_1                          |
% W((cl,sh),LB) =                       inter_2                          |
%           1) choose the candidate with the greatest number of subsets  |
%           2) update clique                                             |
%           3) if not more candidates, stop.                             |
%           4) Otherwise, compute (cl'+sh')                              |
%           5) if (cl'+sh') =< lower_bound, stop.                        |
%              otherwise goto 1.                                         |
%------------------------------------------------------------------------%

% Panic widening
share_clique_widening(panic_1,(Cl,Sh),(Cl1,[])):-
     merge_list_of_lists(Sh,USh),	
     ord_union(Cl,[USh],Cl1).
share_clique_widening(panic_2,(Cl,Sh),([Cl1],[])):-
     merge_list_of_lists(Sh,USh),	
     merge_list_of_lists(Cl,UCl),	
     ord_union(UCl,USh,Cl1).
% Cautious widening
share_clique_widening(cautious,SH,SH1):-     
%% with qplan and freeness we have to decrease the threshold (30)
     share_clique_normalize(SH,40,2,SH1).
% Intermediate widening
share_clique_widening(inter_1,(Cl,Sh),(Cl1,[])):-
     ord_union(Cl,Sh,Cl1).
% If LB = 0 this widening is as inter_1 in terms of precision 
% although less efficient because of the widening (NP-complete)
share_clique_widening(inter_2,(Cl,Sh),SH):-
     compute_subsets_for_sh_groups(Sh,Sh,1,Cand_sh),
     regularize_list_of_tuple(Cand_sh,Cand_sh_r),
     widen_lower_bound(LB),
     size_clsh((Cl,Sh),N),
     reduce_sharing(Cand_sh_r,(Cl,Sh),LB,N,SH).

%% 1-clique-sharing widenings
share_clique_widening(inter_1_clique_1,(Cl,Sh),(Cl1,Sing)):-
     split_list_of_lists_singleton(Sh,Non,Sing),	
     ord_union(Cl,Non,Cl1).     
%     ord_union(Cl,Sh,Cl1).
share_clique_widening(cautious_clique_1,SH,SH1):-     
     share_clique_1_normalize(SH,40,2,SH1).

%------------------------------------------------------------------------%
% compute_subsets_for_sh_groups(+,+,+,-)                                 |
% compute_subsets_for_sh_groups(Cands,Sh,UB,Pows)                        |
%------------------------------------------------------------------------%
% Compute the subsets of every sharing group belonging to Cands in Sh    | 
% such that the number of subsets is at least as great as UB.            |
% Pows is a list of a tuple that consists of (number of subsets,         |
% candidate,subsets).                                                    |
%------------------------------------------------------------------------%
compute_subsets_for_sh_groups([],_,_,[]).
compute_subsets_for_sh_groups([X|Xs],Sh,M,Xs1):-
	sublist_list_of_lists(Sh,X,CardCandSh,CandSh),!,	
	( CardCandSh >= M ->   
	  %L is CardCandSh, 
	  L is 0 - CardCandSh,
	  compute_subsets_for_sh_groups(Xs,Sh,M,R),
	  Xs1= [L-X-CandSh|R]
	;
	  compute_subsets_for_sh_groups(Xs,Sh,M,R),
	  Xs1= R
  ).

regularize_list_of_tuple(Cl,Cl1):-
	sort(Cl,Cl_s), % eliminate duplicates
	regularize_list_of_tuple_(Cl_s,Cl_s,Cl1).

regularize_list_of_tuple_([],_,[]).
regularize_list_of_tuple_([Cl1|Cls1],Cls,Cl2):-
	delete(Cls,Cl1,Cls0),!,
	( ord_subset_list_of_tuple(Cls0,Cl1) ->   
          regularize_list_of_tuple_(Cls1,Cls,Cl2)
        ;
	  regularize_list_of_tuple_(Cls1,Cls,Cl0),
	  Cl2 = [Cl1|Cl0]
        ).

ord_subset_list_of_tuple([],_):- !,fail.
ord_subset_list_of_tuple([_-H1-_|_],_-H2-_) :-
	ord_subset(H2,H1),!.
ord_subset_list_of_tuple([_|T1],H2) :-
	ord_subset_list_of_tuple(T1,H2).

reduce_sharing([],SH,_,_,SH).
reduce_sharing([(L-Cand-Sh_cand)|T],SH,LB,Size,Res):-
     New_Size is Size + L,!, % L is negative (for sorting)
     %New_Size is Size - L,!, % L is positive (for sorting)
     update_clique(Cand,SH,Sh_cand,NewSH),!,	
     ( New_Size > LB ->
       reduce_sharing(T,NewSH,LB,New_Size,Res)
     ;
       Res = NewSH
     ). 
%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              |
%------------------------------------------------------------------------%
% share_clique_special_builtin(+,+,+,-,-)                                |
% share_clique_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)           |
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
%------------------------------------------------------------------------%
:- export(share_clique_special_builtin/5).
share_clique_special_builtin('read/2',read(X,Y),_,'recorded/3',p(Y,X)) :- !.
share_clique_special_builtin('length/2',length(_X,Y),_,some,[Y]) :- !.
share_clique_special_builtin('==/2',_,_,_,_):- !, fail.
share_clique_special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
	share_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
	
%------------------------------------------------------------------------%
% share_clique_success_builtin(+,+,+,+,+,-)                              |
% share_clique_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                |
% Obtains the success for some particular builtins:                      |
%  * If Type = ground, it updates Call making all vars in Sv_u ground    |
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%------------------------------------------------------------------------%

:- export(share_clique_success_builtin/6).
share_clique_success_builtin(ground,Sv_u,_,_,Call,Succ):-
	sort(Sv_u,Sv),	
	irrel_w(Sv,Call,Succ).
share_clique_success_builtin(bottom,_,_,_,_,'$bottom').
share_clique_success_builtin(unchanged,_,_,_,Call,Call).
share_clique_success_builtin(some,_,NewGround,_,Call,Succ):-
	irrel_w(NewGround,Call,Succ).
% SPECIAL BUILTINS
share_clique_success_builtin('=../2',_,p(X,Y),_,(Cl,Sh),Succ):-
% All variables of X are ground. All variables of Y will be ground
	varset(X,Varsx),
	ord_union(Sh,Cl,All),
	projected_gvars(All,Varsx,Vars),
	Vars == Varsx,!, 
	varset(Y,Varsy),
	ord_split_lists_from_list(Varsy,Sh,_Intersect,Sh1),
        take_ground_out_clique(Varsy,Cl,Cl1),
	Succ = (Cl1,Sh1).
share_clique_success_builtin('=../2',_,p(X,Y),_,(Cl,Sh),Succ):-
% All variables of Y are ground. All variables of X will be ground
	nonvar(Y),
	Y = [Z|W],
	varset(W,Varsy),
	ord_union(Sh,Cl,All),
	projected_gvars(All,Varsy,Vars),
	Vars == Varsy,!,
	varset((X,Z),Varsx),
	ord_split_lists_from_list(Varsx,Sh,_Intersect,Sh1),
	take_ground_out_clique(Varsx,Cl,Cl1),
	Succ = (Cl1,Sh1).
share_clique_success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
% X and Y are variables. Therefore, all variables of X can 
% share with all variables of Y
	var(X), var(Y),!,
	sort(Sv_u,Sv),
	Prime = ([],[Sv]),
	share_clique_extend(not_provided_Sg,Prime,Sv,Call,Succ).
share_clique_success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
% General case: Either X is f(t1,...,tn) or Y is [G|Something]. 
% We must unify [f,t1,...,tn] = [G|Something]
	( var(Y) -> G=g ; Y = [G|_] ), !,
	( var(X) -> Term=[G|X] ; X=..Term ),
	sort(Sv_u,Sv),
	share_clique_project(not_provided_Sg,Sv,not_provided_HvFv_u,Call,Proj),
	share_clique_call_to_success_builtin('=/2','='(Term,Y),Sv,Call,Proj,Succ).
share_clique_success_builtin('=../2',_Sv_u,_,_,_Call,'$bottom').
share_clique_success_builtin('==/2',Sv_u,p(X,Y),_,Call,Succ):-
% If X and Y are identical, we only need to propagate groundness
	sh_peel(X,Y,Binds-[]),
	sort(Sv_u,Sv),
	Call = (Cl,Sh),
	ord_union(Cl,Sh,All),
	projected_gvars(All,Sv,Ground),  
%% clique-part
	clique_make_decomposition(Binds,Cl,Ground,NewGround,NewSH),
	sort(NewGround,NewGround1),
	NewSH = (Succ_Cl,Sh1),
%	share_clique_normalize(NewSH,(Succ_Cl,Sh1)),
%% sharing-part
	ord_union(Sh,Sh1,Sh0),
	share_make_reduction(Binds,Sh0,NewGround1,NewGround2,Sets-[]),
	sort(NewGround2,NewGround3),
	sort_list_of_lists(Sets,Sets1),
	ord_split_lists_from_list(NewGround3,Sh0,_Intersect,Temp),
	ord_subtract(Temp,Sets1,Succ_Sh),
	Succ = (Succ_Cl,Succ_Sh).
share_clique_success_builtin(copy_term,_Sv_u,p(X,Y),_,Call,Succ):-
	varset(X,VarsX),
	share_clique_project(not_provided_Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
	copy_term((X,ProjectedX),(NewX,NewProjectedX)),
	share_clique_abs_sort(NewProjectedX,ProjectedNewX),
	varset(NewX,VarsNewX),
	varset(Y,VarsY),
	merge(VarsNewX,VarsY,TempSv),
	share_clique_project(not_provided_Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
	ord_union_w(ProjectedY,ProjectedNewX,TempProjected),
	ord_union_w(ProjectedNewX,Call,TempCall),
	share_clique_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
	                      TempCall,TempProjected,Temp_success),
        Call = (Cl,Sh),			   
	merge_list_of_lists(Cl,VarsCl),   
	merge_list_of_lists(Sh,VarsSh),   
	ord_union(VarsCl,VarsSh,VarsCall),
	share_clique_project(not_provided_Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
share_clique_success_builtin(findall,_Sv_u,p(X,Z),HvFv_u,Call,Succ):-
	Call=(Cl,Sh),
	ord_union(Sh,Cl,All),
	varset(X,Varsx),
	projected_gvars(All,Varsx,Vars),
	Vars == Varsx,!,
	varset(Z,Varsz),
	share_clique_success_builtin(ground,Varsz,_any,HvFv_u,Call,Succ).
share_clique_success_builtin(findall,_Sv_u,_,_,Call,Call).
share_clique_success_builtin('indep/2',_Sv,p(X,Y),_,(Cl,Sh),(Succ_Cl,Succ_Sh)):-
	varset(X,Xv),
	varset(Y,Yv),
	eliminate_couples_clique(Cl,Xv,Yv,Succ_Cl),
	eliminate_couples(Sh,Xv,Yv,Succ_Sh).
share_clique_success_builtin('indep/2',_Sv,_Condvars,_,_Call,'$bottom').
share_clique_success_builtin('indep/1',_Sv,p(X),_,Call,Succ):- 
	nonvar(X),
	handle_each_indep(X,share_clique,Call,Succ), !.  
share_clique_success_builtin('indep/1',_,_,_,_,'$bottom').

share_clique_success_builtin('recorded/3',Sv_u,p(Y,Z),_,Call,Succ):-
	varset(Z,Varsz),
	irrel_w(Varsz,Call,ASub),
	varset(Y,Varsy),
	share_clique_project(not_provided_Sg,Varsy,not_provided_HvFv_u,ASub,ASub1),!,
	star_w(ASub1,Prime),
	sort(Sv_u,Sv),
	share_clique_extend(not_provided_Sg,Prime,Sv,Call,Succ).

share_clique_success_builtin(var,_Sv,p(X),_,(Cl,Sh),Succ):-
	var(X),
	( ord_member_list_of_lists(X,Cl) ;
          ord_member_list_of_lists(X,Sh)), !,
	Succ = (Cl,Sh).
share_clique_success_builtin(var,_Sv,_Condvars,_HvFv_u,_Call,'$bottom').

%------------------------------------------------------------------------%
% share_clique_call_to_success_builtin(+,+,+,+,+,-)                      |
% share_clique_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)       |
% Handles those builtins for which computing Prime is easier than Succ   |
%------------------------------------------------------------------------%

:- export(share_clique_call_to_success_builtin/6).
share_clique_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
	copy_term(X,Xterm),
	copy_term(Y,Yterm),
	Xterm = Yterm,!,
	varset(Xterm,Vars),
	share_clique_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
share_clique_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom') :- !.
share_clique_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):- !,
	share_clique_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
share_clique_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- !,
	share_clique_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
share_clique_call_to_success_builtin('expand_term/2',expand_term(X,Y),Sv,Call,
	                          Proj,Succ):- !,
	share_clique_call_to_success_builtin('arg/3',arg(1,Y,X),Sv,Call,Proj,Succ).
share_clique_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- !,
	share_clique_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
share_clique_call_to_success_builtin('arg/3',arg(X,Y,Z),_,Call,Proj,Succ):- !,
	varset(X,OldG),
	irrel_w(OldG,Call,TempCall),
	Sg = p(Y,Z),
	Head = p(f(A,_B),A),
	varset(Sg,Sv),
	varset(Head,Hv),
	share_clique_project(not_provided_Sg,Sv,not_provided_HvFv_u,TempCall,Proj),
        share_clique_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempCall,Proj,_Prime,Succ). % TODO: add some ClauseKey?

%------------------------------------------------------------------------%
%                      Intermediate operations                           |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% clique_make_decomposition(+,+,+,-,-):-                                |
% clique_make_decomposition(Eqs,Cl,Ground,NewGround,NewSH):-            | 
% It gives the adecuate abstract substitution                            |
% resulting of the unification of A and B when ==(A,B) was called.       |
% If neither X nor Term in one binding is ground, since they have to     |
% be identicals (==), each set C of the clique domain have to            |
% satisfied that X is an element of C if and only if at least one        |
% variable in Term appears also in C. Therefore, we have to decompose    |
% the initial clique in subcliques and sharing sets such that either only| 
% X or only variables of Term cannot appear. The difference wrt          |
% share_make_reduction/5 is that clique_make_decomposition/5 returns    |
% the final elements and share_make_reduction/5 returns the sharing sets |
% that have to be eliminated.                                            |
%------------------------------------------------------------------------%

:- export(clique_make_decomposition/5).
clique_make_decomposition([],_,_,[],([],[])).
clique_make_decomposition([(X,VarsTerm)|More],Cl,Ground,NewGround,NewSH):-
	ord_member(X,Ground), !,
	clique_make_decomposition(More,Cl,Ground,NewGround1,NewSH1),
	append(VarsTerm,NewGround1,NewGround),
        ord_difference_list_of_lists(Cl,VarsTerm,NewCl),
	sort_list_of_lists(NewCl,NewCl1),
	ord_union_w((NewCl1,[]),NewSH1,NewSH).
clique_make_decomposition([(X,VarsTerm)|More],Cl,Ground,[X|NewGround],NewSH):-
	ord_subset(VarsTerm,Ground), !,
	clique_make_decomposition(More,Cl,Ground,NewGround,NewSH1),
        ord_difference_list_of_lists(Cl,[X],NewCl),
	sort_list_of_lists(NewCl,NewCl1),
	ord_union_w((NewCl1,[]),NewSH1,NewSH).
clique_make_decomposition([(X,[Y])|More],Cl,Ground,NewGround,NewSH):-
	var(Y), !,
	sort([X,Y],Vars),
	decompose_if_not_possible(Cl,Vars,NewSH0),  
	clique_make_decomposition(More,Cl,Ground,NewGround,NewSH1),
	ord_union_w(NewSH0,NewSH1,NewSH).
clique_make_decomposition([(X,VarsTerm)|More],Cl,Ground,NewGround,NewSH):-
	ord_subtract(VarsTerm,Ground,List),
	decompose_if_not_possible(Cl,X,List,NewSH0), 
	clique_make_decomposition(More,Cl,Ground,NewGround,NewSH1),
	ord_union_w(NewSH0,NewSH1,NewSH).

%-----------------------------------------------------------------------%
% decompose_if_not_possible(+,+,-)                                      |  
% decompose_if_not_possible(Cls,Vars,(Cl0,Sh0))                         |
% {(c \ Vars,sh)  |c \in Cls}                                           |
% where:                                                                |
% sh= { Vars U p | p \in P(c \ Vars)}                                   |
% Note: decompose_if_not_possible/3 is the complement operation of      |
% eliminate_if_possible/3 for cliques                                   |
%-----------------------------------------------------------------------%

decompose_if_not_possible([],_,([],[])).
decompose_if_not_possible([Z|Rest],Vars,(NewCl,Sh)):-
	ord_intersection_diff(Z,Vars,Term,Disj),	
	test_temp(Term,Vars), !,
	powerset(Disj,PDisj),
	obtain_sharing(PDisj,Vars,NewSh),	
	decompose_if_not_possible(Rest,Vars,(NewCl0,NewSh0)),
	ord_union(NewCl0,[Disj],NewCl),
	ord_union(NewSh0,NewSh,Sh).
decompose_if_not_possible([_|Rest],Vars,ASub):-
	decompose_if_not_possible(Rest,Vars,ASub).

%-----------------------------------------------------------------------%
% decompose_if_not_possible(+,+,+,-)                                    |
% decompose_if_not_possible(Cl,X,Vars,(Cl,Sh)) =                        |
% {(c \ (X U Vars'),sh1 U sh2)  |c \in Cls}                             |
% where:                                                                |
% Vars' = Vars /\ c                                                     |
% sh1= {{x} U p1 | p1 \in (Powerset(Vars')\empty)}                      |
% sh2= {s U p2 | s \in sh1, p2 \in Powerset(c \ (X U Vars'))}           |
% Note: decompose_if_not_possible/4 is the complement operation of      |
% eliminate_if_possible/4 for cliques                                   |
%-----------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
decompose_if_not_possible([],_,_,([],[])).
decompose_if_not_possible([Z|Rest],X,Vars,More):-
	test_eliminate(Z,X,Vars,NewVars),
	ord_union([X],NewVars,All),
	ord_intersection_diff(Z,All,_,Disj),
	test_clique(X,NewVars,Z,Disj,Rest,More). % TODO: Missing cut?
decompose_if_not_possible([_|Rest],X,Vars,More):-
	decompose_if_not_possible(Rest,X,Vars,More).
	
test_eliminate(Z,X,Vars,NewVars):-
	ord_member(X,Z),
	ord_intersection(Z,Vars,NewVars),
	NewVars \== [].
	
:- pop_prolog_flag(multi_arity_warnings).

test_clique(X,Vars,Z,Disj,Rest,(NewCl,Sh)):-
	ord_member(X,Z),!,
	powerset(Vars,PVars),
	ord_union_lists_with_list(PVars,[X],Sh1),
	powerset(Disj,PDisj),
        ord_union_list_of_lists(PDisj,Sh1,Sh2),	
	ord_union(Sh1,Sh2,NewSh),
	decompose_if_not_possible(Rest,X,Vars,(NewCl0,NewSh0)),
	add_disj(Disj,NewCl0,NewCl),
	ord_union(NewSh0,NewSh,Sh).
test_clique(X,Vars,_,_,Rest,More):- !,
	decompose_if_not_possible(Rest,X,Vars,More).

add_disj([],X,X). % TODO: missing cut?
add_disj(Xs,Ys,Zs):- ord_union([Xs],Ys,Zs).

% obtain_sharing/3 is equals to ord_union_lists_with_list but it
% adds the second argument into the third one.
obtain_sharing(_,[],[]) :- !.
obtain_sharing([],Term,[Term]).
obtain_sharing([D|Disj],Term,NewSh):-
	merge(Term,D,NewTerm),
	obtain_sharing(Disj,Term,NewSh0),
	merge(NewSh0,[NewTerm],NewSh).

%------------------------------------------------------------------------
% eliminate_couples_clique(+,+,+,-)                                      |
% eliminate_couples_clique(Cl,Xv,Yv,NewCl)                               |
% All arguments ordered                                                  |
%------------------------------------------------------------------------
:- export(eliminate_couples_clique/4).
eliminate_couples_clique(Cl,Xv,Yv,NewCl1):-
	split_list_of_lists(Xv,Cl,Int1,Disj1),
	split_list_of_lists(Yv,Int1,Int2,Disj2),
	merge(Disj1,Disj2,T),
	partition_cliques(Int2,Xv,Yv,T,NewCl),
	sort_list_of_lists(NewCl,NewCl1).

partition_cliques([],_,_,X,X).
partition_cliques([Cl|Cls],Xv,Yv,Tail,[NewXv0,NewYv0|NewCls]):-
	partition_set(Cl,Xv,Yv,NewXv,NewYv,Disj),
	merge(NewXv,Disj,NewXv0),
	merge(NewYv,Disj,NewYv0),
	partition_cliques(Cls,Xv,Yv,Tail,NewCls).

%------------------------------------------------------------------------
% partition_set(+,+,+,-,-,-)                                             |
% partition_set(Set,Xv,Yv,IntXv,IntYv,Disj)                              |
%------------------------------------------------------------------------
partition_set([],_,_,[],[],[]).
partition_set([H|T],Xv,Yv,[H|NXv],NYv,NDisj):-
	ord_member(H,Xv),!,
	partition_set(T,Xv,Yv,NXv,NYv,NDisj).
partition_set([H|T],Xv,Yv,NXv,[H|NYv],NDisj):-
	ord_member(H,Yv),!,
	partition_set(T,Xv,Yv,NXv,NYv,NDisj).
partition_set([H|T],Xv,Yv,NXv,NYv,[H|Disj]):-
	partition_set(T,Xv,Yv,NXv,NYv,Disj).

%------------------------------------------------------------------------%
% This predicates is defined in sharing.pl. It should be exported        |
%------------------------------------------------------------------------%
% share_make_reduction(+,+,+,-,-)                                        |
% share_make_reduction(Eqs,Lambda,Ground,NewGround,Eliminate)            |
% It gives the adecuate abstract substitution                            |
% resulting of the unification of A and B when ==(A,B) was called.       |
% If neither X nor Term in one binding is ground, since they have to     |
% be identicals (==), each set S of the sharing domain have to           |
% satisfied that X is an element of S if and only if at least one        |
% variable in Term appears also in S. Therefore, each set in which       |
% either only X or only variables of Term appear, has to be eliminated.  |
%------------------------------------------------------------------------%
%%% TODO: [IG] This code is duplicated from sharing.pl!!!
:- export(share_make_reduction/5).
share_make_reduction([],_,_,[],Y-Y).
share_make_reduction([(X,VarsTerm)|More],Lambda,Ground,NewGround,Eliminate):-
	ord_member(X,Ground), !,
	share_make_reduction(More,Lambda,Ground,NewGround1,Eliminate),
	append(VarsTerm,NewGround1,NewGround).
share_make_reduction([(X,VarsTerm)|More],Lambda,Ground,[X|NewGround],Eliminate):-
	ord_subset(VarsTerm,Ground), !,
	share_make_reduction(More,Lambda,Ground,NewGround,Eliminate).
share_make_reduction([(X,[Y])|More],Lambda,Ground,NewGround,Eliminate):-
	var(Y), !,
	sort([X,Y],Vars),
	eliminate_if_not_possible(Lambda,Vars,Elim1),
	share_make_reduction(More,Lambda,Ground,NewGround,Elim2),
	append_dl(Elim1,Elim2,Eliminate).
share_make_reduction([(X,VarsTerm)|More],Lambda,Ground,NewGround,Eliminate):-
	ord_subtract(VarsTerm,Ground,List),
	eliminate_if_not_possible(Lambda,X,List,Elim1),
	share_make_reduction(More,Lambda,Ground,NewGround,Elim2),
	append_dl(Elim1,Elim2,Eliminate).

:- export(projected_gvars_clique/3).
projected_gvars_clique(Proj,Sv,Gv):-
     Proj = (Cl,Sh),
     merge_list_of_lists(Cl,Vars_Cl),
     merge_list_of_lists(Sh,Vars_Sh),
     ord_union(Vars_Cl,Vars_Sh,Vars_Proj),
     ord_subtract(Sv,Vars_Proj,Gv).

%------------------------------------------------------------------------%
% size_clsh(+,-)                                                         |
%------------------------------------------------------------------------%
% size_clsh((Cl,SH)) = size'(Cl) + size'(Sh)                             |
% where   size'(X) = Sum{for all x \in X} |x|                            |
%------------------------------------------------------------------------%
% size_clsh((Cl,Sh),N):-
% 	size_set_of_sets(Cl,Size_cl),
% 	size_set_of_sets(Sh,Size_sh),
% 	N is Size_cl + Size_sh.	
size_clsh((_Cl,Sh),Size_sh):-
	size_set_of_sets(Sh,Size_sh).

%------------------------------------------------------------------------%
% size_set_of_sets(+,-)                                                  |
% size_set_of_sets(X) = Sum{for all x \in X} |x|                         |
%------------------------------------------------------------------------%
size_set_of_sets([],0).
size_set_of_sets([S|Ss],Res):-
	length(S,L_S),
	size_set_of_sets(Ss,L_Ss),
	Res is L_S + L_Ss.

:- export(compute_upper_amgu/2). % JN needed by sharedef.pl
compute_upper_amgu(Sh,UB):-
	merge_list_of_lists(Sh,Vars),
	length(Vars,Num_Vars),
	minimum(Sh,Min),
	UB is (2**Num_Vars) - (2**Min).

minimum([],0):-!.
minimum([H|T],M):-
	length(H,L),
	minimum_list_of_lists(T,H,L,M).

minimum_list_of_lists([],_,M,M).
minimum_list_of_lists([S|Ss],X,M,R):-
	length(S,LS),!,
	( LS < M ->   
	  minimum_list_of_lists(Ss,S,LS,R)
	;
	  minimum_list_of_lists(Ss,X,M,R)
        ).

%------------------------------------------------------------------------%
% compute_upper_amgu(+,+,+,-)                                            |
%------------------------------------------------------------------------%
% NG_x:   Number (Upper bound) of sharing groups for x
% CC_x:   Cardinality of the sharing sets x
% M_x:    The longest sharing group of x
% Size_x: size of x, 
%         where: 
%           size((Cl,Sh)) = ( size'(Cl) + size'(Sh))
%           size'(X) = Sum{for all x \in X} |x| 
% UB_x:   size of x (Upper bound)
%------------------------------------------------------------------------%     
% NOTE: CC_Sh_x * M_x is the the cardinality (upper bound) of every      |
% sharing group after the star union. CC_Sh_x may be replaced by a better|
% approximation.                                                         |
%------------------------------------------------------------------------%       
% compute_upper_amgu(Irrel_Sh_xt,Sh_x,Sh_t,UB):-
% 	size_set_of_sets(Irrel_Sh_xt,Size_Irrel_Sh_xt),
% 	length(Sh_x,CC_Sh_x),
% 	NG_Sh_x_star is (2**CC_Sh_x) - 1,
% 	maximum(Sh_x,M_x),
% 	UB_Sh_x is NG_Sh_x_star * CC_Sh_x * M_x,
% 	length(Sh_t,CC_Sh_t),		
% 	NG_Sh_t_star is (2**CC_Sh_t) - 1,
% 	maximum(Sh_t,M_t),
% 	UB_Sh_t is NG_Sh_t_star * CC_Sh_t * M_t,
% 	UB is Size_Irrel_Sh_xt + (UB_Sh_x * UB_Sh_t).
       
% maximum([],0):-!.
% maximum([H|T],M):-
% 	length(H,L),
% 	maximum_list_of_lists(T,H,L,M).

% maximum_list_of_lists([],_,M,M).
% maximum_list_of_lists([S|Ss],X,M,R):-
% 	length(S,LS),!,
% 	( LS >= M ->   
% 	  maximum_list_of_lists(Ss,S,LS,R)
% 	;
% 	  maximum_list_of_lists(Ss,X,M,R)
%         ).

% ===========================================================================
% Debug - count number of widenings

% :- use_package(datafacts).
% :- data widen_done/0.
% 
% inc_widen_done :- asserta(widen_done).
%
% :- export(number_of_widening/1).
% number_of_widening(N):-
% 	findall(widen_done,widen_done,L),
% 	length(L,N),
% 	retractall_fact(widen_done).
% 
% :- export(clean_number_of_widening/0).
% clean_number_of_widening:-
% 	retractall_fact(widen_done).
