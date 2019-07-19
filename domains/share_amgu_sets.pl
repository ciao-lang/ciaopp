/*             Copyright (C)2004-2005 UNM-CLIP				*/

:- module(share_amgu_sets,
	[ 
	 delete_list_of_lists/3,
	 sublist_list_of_lists/4,
	 sublist_list_of_lists2/3,
	 nosublist_list_of_lists/3,
	 intersect_lists_with_list/3,
	 intersection_list_of_lists/3,
	 intersection_lists_with_list/3,
	 intersection2_lists_with_list/3,
	 ord_difference_list_of_lists/3,
	 delete_vars_from_list_of_lists/3,
%	 ord_intersection2/3,
%	 ord_intersect2/2,
	 split_list_of_lists/4,
	 ord_subset_list_of_lists/2,
	 ord_subset_lists_with_list/2,
	 ord_superset_lists_with_list/2,
	 ord_union_lists_with_list/3,
	 ord_union_list_of_lists/3	 
	],
	[ assertions, isomodes ]).

:- use_module(library(lsets),
        [delete_var_from_list_of_lists/4, sort_list_of_lists/2]).
:- use_module(library(sets), 
	[ord_subset/2,
	 ord_union/3,
	 ord_intersection/3,
	 ord_intersect/2,
	 ord_intersection_diff/4
	]).
:- use_module(library(lists), [delete/3]).

%------------------------------------------------------------------------%
% This file implements new predicates for the libraries sets.pl and      |
% lsets.pl                                                               |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                                                                        |
%        programmer: J. Navas                                            |
%                                                                        |
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% delete_list_of_lists(LL1,LL2,LL3)                                      |
% Delete each list L of the list of lists LL2 in LL1                     |
%------------------------------------------------------------------------%
delete_list_of_lists(Sh,[],Sh0):- !,
	delete(Sh,[],Sh0).
delete_list_of_lists(Sh,[S|Ss],Sh1):-
	delete(Sh,S,Sh0),!,
	delete_list_of_lists(Sh0,Ss,Sh1).
delete_list_of_lists(Sh,_,Sh).

%------------------------------------------------------------------------%
% sublist_list_of_lists(Ls,L,Card,Ss)                                    |
% Ss is a list of lists composed by lists of Ls that ARE a SUBLIST of L. | 
% Card is the lenght of Ss (avoid recomputations)                        |
%------------------------------------------------------------------------%
sublist_list_of_lists([],_,0,[]).
sublist_list_of_lists([Sh|Shs],Sh1,Card,[Sh|Shs0]):-
	ord_subset(Sh,Sh1),!,
	sublist_list_of_lists(Shs,Sh1,Card0,Shs0),
	Card is Card0 + 1.
sublist_list_of_lists([_|Shs],Sh1,Card,Shs0):-
	sublist_list_of_lists(Shs,Sh1,Card,Shs0).

%------------------------------------------------------------------------%
% sublist_list_of_lists2(Ls,L,Ss)                                        |
% Ss is a list of lists composed by lists of Ls such that L is SUBLIST   |
% of them.                                                               | 
%------------------------------------------------------------------------%
sublist_list_of_lists2([],_,[]).
sublist_list_of_lists2([Sh|Shs],Sh1,[Sh|Shs0]):-
	ord_subset(Sh1,Sh),!,
	sublist_list_of_lists2(Shs,Sh1,Shs0).
sublist_list_of_lists2([_|Shs],Sh1,Shs0):-
	sublist_list_of_lists2(Shs,Sh1,Shs0).

%------------------------------------------------------------------------%
% nosublist_list_of_lists(LLs,L,LLs1)                                    |
% LLs1 is a list of lists composed by those lists of LLs that ARE NOT    |
% a SUBLIST of L.                                                        |
%------------------------------------------------------------------------%
nosublist_list_of_lists([],_,[]).
nosublist_list_of_lists([L|Ls],L1,Ls0):-
	ord_subset(L,L1),!,
	nosublist_list_of_lists(Ls,L1,Ls0).
nosublist_list_of_lists([L|Ls],L1,[L|Ls0]):-
	nosublist_list_of_lists(Ls,L1,Ls0).

%------------------------------------------------------------------------%
% intersect_lists_with_list(Ls,L,Ss)                                     |
% Ss is a list of lists composed by lists of Ls that have at least one   |
% element in common with L.                                              |
%------------------------------------------------------------------------%
intersect_lists_with_list([],_,[]).
intersect_lists_with_list([X|Xs],E,[X|R]):-
%	ord_intersect2(X,E),!,
	ord_intersect(X,E),!,
	intersect_lists_with_list(Xs,E,R).
intersect_lists_with_list([_|Xs],E,Int):-
	intersect_lists_with_list(Xs,E,Int).

%------------------------------------------------------------------------%
% intersection_list_of_lists(Ls1,Ls2,Ss)                                 |
% Ss is a list of lists composed by the intersection of Ls1 and  Ls2     |    
%------------------------------------------------------------------------%
intersection_list_of_lists([],_,[]).
intersection_list_of_lists([L1|Ls1],Ls2,Int0):-
	intersection_lists_with_list(Ls2,L1,Int),
	intersection_list_of_lists(Ls1,Ls2,Ints),
	ord_union(Int,Ints,Int0).

%------------------------------------------------------------------------%
% intersection_lists_with_list(Ls,L,Ss)                                  |
% Ss is a list of lists composed by the intersection of lists of Ls and  |    
% the list L. Note that the property of sorted list is not closed under  |
% this operation. Therefore, it is necessary to sort the final list.     |
%------------------------------------------------------------------------%
intersection_lists_with_list(Ls,L,Ss):-
	intersection_lists_with_list_(Ls,L,S),
	sort_list_of_lists(S,Ss).

intersection_lists_with_list_([],_,[]).
intersection_lists_with_list_([X|Xs],E,Int0):-
%	ord_intersection2(X,E,Int),
	ord_intersection(X,E,Int),
	insert_not_nil(Int,R,Int0),
	intersection_lists_with_list_(Xs,E,R).

%------------------------------------------------------------------------%
% intersection2_lists_with_list(Ls,L,Ss)                                 |
% Ss is a list of lists composed by the intersection of the list L       |
% and lists of Ls . Note that the property of sorted list is not closed  | 
% under this operation. Therefore, it is necessary to sort the final     |
% list.                                                                  |
%------------------------------------------------------------------------%
intersection2_lists_with_list(Ls,L,Ss):-
	intersection2_lists_with_list_(Ls,L,S),
	sort_list_of_lists(S,Ss).

intersection2_lists_with_list_([],_,[]).
intersection2_lists_with_list_([X|Xs],E,Int0):-
	ord_intersection(E,X,Int),
	insert_not_nil(Int,R,Int0),
	intersection2_lists_with_list_(Xs,E,R).
	
%------------------------------------------------------------------------%
% ord_difference_list_of_lists(Ls1,Vars,Ss)                              |
% Ss is a list of lists composed by the difference of each list of Ls1   |
% and Vars.                                                              |
% Note that the property of sorted list is not closed under this         |
% operation. Therefore, it is necessary to sort the final list.          |
%------------------------------------------------------------------------%
ord_difference_list_of_lists(Ls1,Vars,Diff):-
	difference_list_of_lists(Ls1,Vars,Diff0),
	sort_list_of_lists(Diff0,Diff).

difference_list_of_lists([],_,[]).
difference_list_of_lists([L1|Ls1],Vars,Diff1):-
	ord_intersection_diff(L1,Vars,_,Diff),
	difference_list_of_lists(Ls1,Vars,Diff0),
	insert_not_nil(Diff,Diff0,Diff1).
	
%------------------------------------------------------------------------%
% delete_vars_from_list_of_lists(Vs,LLs,LLs0)                            |
% Delete the list of variables Vs from the list of lists LLs             |
% Note that the property of sorted list is not closed under this         |
% operation. Therefore, it is necessary to sort the final list.          |
%------------------------------------------------------------------------%
delete_vars_from_list_of_lists(Vs,LLs,LLs1):-
	delete_vars_from_list_of_lists_(Vs,LLs,LLs0),
	sort_list_of_lists(LLs0,LLs1).

delete_vars_from_list_of_lists_([],LLs,LLs).
delete_vars_from_list_of_lists_([Vs|Vss],List_of_Lists,LLs) :-
	delete_var_from_list_of_lists(Vs,List_of_Lists,New_LLs,_),
	delete_vars_from_list_of_lists_(Vss,New_LLs,LLs).

%------------------------------------------------------------------------%
% ord_intersection2(S1,S2,Int)                                           |
% Int is a list composed by the intersection of S1 and S2                |    
% S1 and S2 MUST BE SORTED.                                              |
% ord_intersection/3 cannot be used becuase it has a different behaviour |
% ?- ord_intersection([Y,Z],[X,Y,Z],Int).                                |
% Int = []                                                               |
%------------------------------------------------------------------------%
% ord_intersection2([],_,[]):-!.
% ord_intersection2(_,[],[]):-!.
% ord_intersection2([H1|T1],[H2|T2],[H1|Int]):-
% 	compare(=,H1,H2),
% 	ord_intersection2(T1,T2,Int).
% ord_intersection2([H1|T1],[H2|T2],Int):-
% 	compare(<,H1,H2),
% 	ord_intersection2(T1,[H2|T2],Int).
% ord_intersection2([H1|T1],[H2|T2],Int):-
% 	compare(>,H1,H2),
% 	ord_intersection2([H1|T1],T2,Int).

%------------------------------------------------------------------------%
% split_list_of_lists(+,+,-,-)                                           |
% split_list_of_lists(Xs,OrdXss,Intersect,Disjunct)                      |
% Split the ordered list of lists Xss into two sorted lists: Intersect   |
% contains the elements in Xss containing some element of Xs, Disjunct   |
% those containing no element of Xs                                      |
% ord_split_lists_from_list/4 cannot be used!                            |
%------------------------------------------------------------------------%
split_list_of_lists(_,[],[],[]) :- !.
split_list_of_lists(Vars,[S|Sh],Int,Disj):-
%	( ord_intersect2(Vars,S) ->
	( ord_intersect(Vars,S) ->
	  Int = [S|Int0],
	  Disj = Disj0
        ;
	  Int = Int0,  
	  Disj = [S|Disj0]
        ),
        split_list_of_lists(Vars,Sh,Int0,Disj0).

%------------------------------------------------------------------------%
% ord_intersect2(S1,S2)                                                  |
% Succeeds when the two ordered lists have at least one element in       |
% common.                                                                |    
% S1 and S2 MUST BE SORTED.                                              |
% ord_intersect/2 cannot be used becuase it has a different behaviour    |
% ?- ord_intersect([Y,Z],[X,Y,Z]).                                       |
% no                                                                     |
%------------------------------------------------------------------------%

% ord_intersect2([H1|_],[H2|_]):-
% 	compare(=,H1,H2),!.
% ord_intersect2([H1|T1],[H2|T2]):-
% 	compare(<,H1,H2),
% 	ord_intersect2(T1,[H2|T2]).
% ord_intersect2([H1|T1],[H2|T2]):-
% 	compare(>,H1,H2),
% 	ord_intersect2([H1|T1],T2).

%------------------------------------------------------------------------%
% ord_subset_list_of_lists(LS1,LS2)                                      |
% Succeeds when every element of LS1 appears in LS2 as a                 |
% subset.                                                                |
%------------------------------------------------------------------------%
ord_subset_list_of_lists([], _).
ord_subset_list_of_lists([H1|T1], L2) :-
	ord_subset_list_of_lists_(L2, H1),
	ord_subset_list_of_lists(T1,L2).

ord_subset_list_of_lists_([H|_],L):-
	ord_subset(L,H),!.
ord_subset_list_of_lists_([_|T],L):-
	ord_subset_list_of_lists_(T,L).

%------------------------------------------------------------------------%
% ord_subset_lists_with_lists(Lss,L)                                     |
% Succeeds when L is subset of any list of Lss                           |
%------------------------------------------------------------------------%
ord_subset_lists_with_list([],_):- !,fail.
ord_subset_lists_with_list([H1|_],L) :-
	ord_subset(L,H1),!.
ord_subset_lists_with_list([_|T1],L) :-
	ord_subset_lists_with_list(T1,L).

%------------------------------------------------------------------------%
% ord_superset_lists_with_lists(Lss,L)                                   |
% Succeeds when L is superset of some list of Lss                        |
%------------------------------------------------------------------------%
ord_superset_lists_with_list([],_):- !,fail.
ord_superset_lists_with_list([H1|_],L) :-
	ord_subset(H1,L),!.
ord_superset_lists_with_list([_|T1],L) :-
	ord_superset_lists_with_list(T1,L).

%-------------------------------------------------------------------------
% ord_union_lists_with_list(+,+,-)                                       |
%-------------------------------------------------------------------------
ord_union_lists_with_list([],_Ys,[]).
ord_union_lists_with_list([Xs|Rest],Ys,Result):-
	ord_union(Xs,Ys,Rs),
	ord_union_lists_with_list(Rest,Ys,Zs),
	ord_union(Zs,[Rs],Result).

%-------------------------------------------------------------------------
% ord_union_list_of_lists(+,+,-)                                         |
%-------------------------------------------------------------------------	
ord_union_list_of_lists([],_LLs,[]).
ord_union_list_of_lists([Xs|Rest],LLs,Result):-
	ord_union_lists_with_list(LLs,Xs,Rs),
	ord_union_list_of_lists(Rest,LLs,Zs),
	ord_union(Zs,Rs,Result).

insert_not_nil(H,T,Res):-
	( H = [] ->
	  Res = T
        ;
	  Res = [H|T]
        ).
