/*             Copyright (C)1990-2002 UPM-CLIP				*/
% TODO: Split this module in share and shfr
:- module(share,
	[ share_call_to_entry/8,
	  share_call_to_success_builtin/6,
	  share_call_to_success_fact/8,
	  share_call_to_prime_fact/6,
	  share_compute_lub/2,
	  share_exit_to_prime/7,
	  share_extend/4,     
	  share_glb/3,      
	  share_input_user_interface/3,  
	  share_input_interface/4,  
	  share_less_or_equal/2,
	  share_lub/3,      
	  %share_output_interface/2, 
	  share_asub_to_native/5, 
	  share_project/3,    
	  share_sort/2,       
	  share_special_builtin/4,
	  share_success_builtin/5,
	  share_unknown_call/3,
	  share_empty_entry/2,
	  share_unknown_entry/2,
	% sharing+freeness
	  shfr_call_to_entry/8,
	  shfr_call_to_success_builtin/6, 
	  shfr_call_to_success_fact/8,
	  shfr_call_to_prime_fact/6,
	  %shfr_check_cond/5,
	  shfr_compute_lub/2, 
	  shfr_compute_lub_el/3,  %% commented out by JNL
	  %shfr_convex_hull/3,
	  %shfr_downwards_closed/3,  
	  shfr_exit_to_prime/7,
	  shfr_extend/4,      
	  %shfr_extend_free/3,
	  shfr_glb/3,       
	  %shfr_hash/3,      
	  %shfr_impos_cond/4,
	  shfr_input_user_interface/3,
	  shfr_input_interface/4,
	  shfr_less_or_equal/2,
	  %shfr_more_instantiate/2,  
	  %shfr_output_interface/2,
	  shfr_asub_to_native/5,
	  shfr_obtain/4,
          shfr_obtain/3,
	  shfr_project/3,     
	  %shfr_real_conjoin/3,
	  shfr_sort/2,        
	  shfr_special_builtin/4,
	  shfr_success_builtin/5,
	  shfr_empty_entry/2,
	  shfr_unknown_call/3,
	  shfr_unknown_entry/2,
	% sharing+freeness+nonvar
	  shfrnv_asub_to_native/5, 
	  shfrnv_call_to_entry/8,
	  shfrnv_call_to_success_builtin/6, 
	  shfrnv_call_to_success_fact/8, 
	  %shfrnv_check_cond/5,
	  shfrnv_compute_lub/2,
	  %shfrnv_compute_lub_el/3,  
	  %shfrnv_convex_hull/3,
	  %shfrnv_downwards_closed/3, 
	  shfrnv_exit_to_prime/7,
	  shfrnv_extend/4,    
	  %shfrnv_hash/3,    
	  %shfrnv_impose_cond/4,
	  shfrnv_input_interface/4, 
	  shfrnv_input_user_interface/3, 
	  shfrnv_less_or_equal/2, 
	  %shfrnv_more_instantiate/2, 
	  %shfrnv_output_interface/2,  
	  %shfrnv_real_conjoin/3,
	  shfrnv_success_builtin/5
	],
	[ assertions, isomodes ]).

:- use_module(domain(s_grshfr), 
	[ change_values_if_differ/5,
	  change_values_insert/4,
	  collect_vars_freeness/2,
	  create_values/3,
	  impossible/3,
	  member_value_freeness/3, 
	  new1_gvars/4,
	  projected_gvars/3,
	  var_value/3
	]).

:- include(domain(sharing)).
:- include(domain(sharefree)).
:- include(domain(sharefree_non_var)).

%% :- doc(bug,"1. ?- glb(shfr,([[A,B],[A,C]],[A/nf,Z/g,B/nf,C/nf]),
%%    ([[A]],[A/nf,Z/g,B/g,C/g]),X). X = ([],[A/nf,Z/g,B/g,C/g]) ? 
%%    Should be A/g.").
:- doc(bug,"2. With var(F),length([F|L],X) freenes of F is
	unnecessarily lost.").
%% Solved
%% :- doc(bug,"3. shfr_success_builtin for arg(X,Y,Z) is not prepared
%% 	for a non-variable Y.").

%------------------------------------------------------------------------
% eliminate_couples(+,+,+,-)                                             |
% eliminate_couples(Sh,Xs,Ys,NewSh)                                      |
% Eliminates from Sh all SS s.t. both X,Y\in SS for some X\in Xs,Y\in Ys |
% All arguments ordered                                                  |
%------------------------------------------------------------------------

eliminate_couples([],_,_,[]):- !.
eliminate_couples(Sh,Xs,Ys,NewSh) :-
	ord_split_lists_from_list(Xs,Sh,Intersect,Disjunct1),
	ord_split_lists_from_list(Ys,Intersect,_,Disjunct2),
	merge(Disjunct2,Disjunct1,NewSh).

%------------------------------------------------------------------------
% eliminate_if_not_possible(+,+,-)
% eliminate_if_not_possible(ASub,Vars,More)
% It gives in the third argument each set S in the first argument which 
% has variables in common with Vars but Vars is not a subset of S
%------------------------------------------------------------------------

eliminate_if_not_possible([],_,X-X).
eliminate_if_not_possible([Z|Rest],Vars,More):-
	ord_intersection(Vars,Z,Term),
	test_temp(Term,Vars), !,
	eliminate_if_not_possible(Rest,Vars,More).
eliminate_if_not_possible([Z|Rest],Vars,[Z|More]-More2):-
	eliminate_if_not_possible(Rest,Vars,More-More2).

test_temp([],_).
test_temp([X|Xs],List):-
	[X|Xs] == List.

%------------------------------------------------------------------------
% eliminate_if_not_possible(+,+,+,-)
% eliminate_if_not_possible(ASub,X,Vars,More)
% It gives as a diff list each set S in ASub s.t. either X appears in S
% and no element of Vars appears in S or 
% X does not appear but at least one element in Vars appears
%------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).
	
eliminate_if_not_possible([],_,_,X-X).
eliminate_if_not_possible([Z|Rest],X,Vars,More):-
	ord_intersection(Vars,Z,V), !,
	test_set(V,X,Z,Rest,Vars,More).
eliminate_if_not_possible([Z|Rest],X,Vars,More):-
	ord_member(X,Z), !,
	eliminate_if_not_possible(Rest,X,Vars,More).
eliminate_if_not_possible([Z|Rest],X,Vars,[Z|More]-More1):-
	eliminate_if_not_possible(Rest,X,Vars,More-More1).

:- pop_prolog_flag(multi_arity_warnings).

test_set([],X,Z,Rest,Vars,More):-
	ord_member(X,Z),!,
	More = [Z|Rest1]-Rest2,
	eliminate_if_not_possible(Rest,X,Vars,Rest1-Rest2).
test_set([],X,_,Rest,Vars,More):- !,
	eliminate_if_not_possible(Rest,X,Vars,More).
test_set([_|_],X,Z,Rest,Vars,More):-
	ord_member(X,Z),!,
	eliminate_if_not_possible(Rest,X,Vars,More).
test_set([_|_],X,Z,Rest,Vars,More):- !,
	More = [Z|Rest1]-Rest2,
	eliminate_if_not_possible(Rest,X,Vars,Rest1-Rest2).

%------------------------------------------------------------------------

handle_each_indep([],_AbsInt,Call,Call).
handle_each_indep([[X,Y]|Rest],AbsInt,Call,Succ):-
	success_builtin(AbsInt,'indep/2',_,p(X,Y),Call,Succ1), !,
	handle_each_indep(Rest,AbsInt,Succ1,Succ).

success_builtin(share,Key,Sv,Vs,Call,Succ):-
	share_success_builtin(Key,Sv,Vs,Call,Succ).
success_builtin(shfr,Key,Sv,Vs,Call,Succ):-
	shfr_success_builtin(Key,Sv,Vs,Call,Succ).
success_builtin(shfrnv,Key,Sv,Vs,Call,Succ):-
	shfrnv_success_builtin(Key,Sv,Vs,Call,Succ).

%------------------------------------------------------------------------

has_give_intersection(=,X,Xs,_Y,Ys,yes,[X|Inter],[X|Xs]):-
	ord_intersection(Xs,Ys,Inter).
has_give_intersection(<,_X,[],_Y,_Ys,Flag,_Inter,_NewVars):- !,
	Flag = end.
has_give_intersection(<,_,[X|Xs],Y,Ys,Flag,Inter,NewVars):-
	compare(D,X,Y),
	has_give_intersection(D,X,Xs,Y,Ys,Flag,Inter,NewVars).
has_give_intersection(>,X,Xs,_Y,[],Flag,_Inter,NewVars):- !,
	NewVars = [X|Xs],
	Flag = no.
has_give_intersection(>,X,Xs,_,[Y|Ys],Flag,Inter,NewVars):- 
	NewVars = [X|Xs],
	compare(D,X,Y),
	has_give_intersection_next(D,X,Xs,Y,Ys,Flag,Inter).

has_give_intersection_next(=,X,Xs,_Y,Ys,yes,[X|Inter]):-
	ord_intersection(Xs,Ys,Inter).
has_give_intersection_next(<,_X,[],_Y,_Ys,Flag,_Inter):- !,
	Flag = no.
has_give_intersection_next(<,_,[X|Xs],Y,Ys,Flag,Inter):-
	compare(D,X,Y),
	has_give_intersection_next(D,X,Xs,Y,Ys,Flag,Inter).
has_give_intersection_next(>,_X,_Xs,_Y,[],Flag,_Inter):- !,
	Flag = no.
has_give_intersection_next(>,X,Xs,_,[Y|Ys],Flag,Inter):-
	compare(D,X,Y),
	has_give_intersection_next(D,X,Xs,Y,Ys,Flag,Inter).

%------------------------------------------------------------------------%

append_dl(X-Y,Y-Z,X-Z).

% dl_to_l(X-[],X).

list_ground([],[]).
list_ground([X|Xs],[X/g|Rest]):-
	list_ground(Xs,Rest).

if_not_nil([],_,Xs,Xs):- !.
if_not_nil(_,X,[X|Xs],Xs).
