/*             Copyright (C)1990-2002 UPM-CLIP				*/
% TODO: Split this module in share and shfr
:- module(share, [], [assertions, isomodes]).

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
