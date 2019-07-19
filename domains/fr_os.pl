%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : Freeness Domain
% Copyright (C) 1993 Gerda Janssens and Katholieke Universiteit Leuven.
% Extended by Veroniek Dumortier - September 1993
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%--------------------------------------------------------------------------
% set operations on ordered sets of uninstantiated variables
%
% G. Janssens
% based on the ordered set implementation in the library of BIMprolog
% and the ordsets.pl in the library of sicstus prolog
% (renamed to kulordsets.pl to avoid name conflicts)
% Extended by V. Dumortier (September '93)
%--------------------------------------------------------------------------

%--------------------------------------------------------------------------
				% S : succeeds
				% F : fails
				% B : backtracks

% :- global set_eq/2.		% (S,F)	set_eq(+Set,+Set)
% :- global set_compare/3	% (S,F) set_compare(?Order,?Set,?Set)
% :- global set_union/3 .	% (S)	set_union(+SetA,+SetB,-Set_A_U_B)
% :- global set_union_list/2	% (?)	set_union_list(+SetList,-Set)
% :- global set_intersect/3 .	% (S)	set_intersect(+SetA,+SetB,-Set_A_/\_B)
% :- global set_disjoint/2 .	% (SF)	set_disjoint(+SetA,+SetB)
% :- global set_nondisjoint/2	% (SF)	set_nondisjoint(+SetA,+SetB)
% :- global set_empty/1 .	% (SF)	set_empty(?Set)
% :- global set_create/2 .	% (S)	set_create(+ElementList,-Set)
% :- global set_is_in/2 .	% (SF)	set_is_in(+Element,+Set)
% :- global set_member/2 .	% (SFB)	set_member(-Element,+Set)
% :- global set_all_members/2 .	% (S)	set_all_members(+Set,-ElementList)
% :- global set_add_el/3 .	% (SFB)	set_add_el(+Element,+Set,-ResultSet)
% :- global set_is_subset/2 .	% (SF)	set_is_subset(+SubSet,+Set)
% added by Gerda Janssens 23/10
% :- global set_diff/3 .	% (S)	set_diff(+Set,+Set,-Set)
% :- global set_print/1		% (S)  	set_print(+set)
% :- global set_compare/3	% (S,F)	set_compare(?Order,?Set,?Set)
% :- global set_rename/4	% (?)	set_rename(+Set,+VarList,+VarList,-Set)
% added by Veroniek Dumortier 9/93
% :- global set_singleton/1	% (S,F)	set_singleton(?Set)
% :- global set_boxplus/3	% (?)	set_boxplus(+Set,+Set,-Set)
% :- global set_product/3	% (?)	set_product(+Set, +Set, ?SSet)

% version with ordered sets 
% to be used with sets of uninstantiated variables


% set_eq(S1, S2)
% is true when S1 and S2 represent the same set. Since they
% are assumed to be ordered representations, they must be identical.
%
set_eq(S1, S2):-
	kulord_seteq(S1, S2).


% set_compare(Order, S1, S2)
% is true when "S1 Order S2" holds, where Order is the standard order.
%
set_compare(Order, S1, S2):-
	compare(Order, S1, S2).


% set_union(S1, S2, Su)
% is true when Su is the union of S1 and S2 (when something occurs in both sets,
% only one copy will be retained !).
% 
set_union(S1, S2, Su) :-
	kulord_union(S1, S2, Su).


% set_union_list(SetList, S)
% is true when S is the union of all the sets in SetList.
%
set_union_list(SetList, S) :-
	kulord_union(SetList, S).


% set_intersect(S1, S2, Si)
% is true when Si is the ordered representation of the intersection of S1 and
% S2
%
set_intersect(S1, S2, Si) :-
	kulord_intersection(S1, S2, Si).

%% % set_disjoint(S1, S2)
%% % is true when the two ordered sets S1 and S2 have no element in common
%% %
%% set_disjoint(S1,S2) :-
%% 	kulord_disjoint(S1,S2).

% set_nondisjoint(S1, S2)
% is true when the two ordered sets S1 and S2 have at least one element
% in common.
% 
set_nondisjoint(S1, S2) :-
	kulord_intersect(S1, S2).


% set_empty(S)
% is true when S is the empty set
%
set_empty(S):-
	kulord_empty(S).


% set_create(List, Set)
% is true when Set is the ordered representation of the set represented
% by the unordered representation List.
%
set_create(List, Set) :-
	list_to_kulord_set(List, Set).


% set_is_in(E, S)
% is true when E occurs in the set S
% MAY ONLY BE USED TO TEST WHETHER A KNOWN ELEMENT OCCURS IN A KNOWN SET
% In return for this limited use, it is more efficient when it is applicable.
%
set_is_in(E, S) :-
	kulord_setutl_memberchk(E, S).

%% % set_member(E, S).
%% % s true when E occurs in the set S
%% % 
%% set_member(E,S) :-
%% 	kulord_setutl_member(E,S).

% set_all_members(S, L)
% L is the ordered list of all elements in the set S
%
set_all_members(S,S).


% set_add_el(E, Sold, Snew)
% is true when Snew is Sold with E inserted in it, preserving the order
%
set_add_el(E, Sold, Snew) :-
	kulord_add_element(Sold, E, Snew).


% set_is_subset(Subs, S)
% is true when every element of the ordered set Subs appears in the ordered
% set S
%
set_is_subset(Subs, S) :-
	kulord_subset(Subs, S).

% set_diff(S1, S2, S1min2)
% is true when S1min2 contains all and only the elements of S1 which are not
% also in S2.
%
set_diff(S1, S2, S1min2) :-
	kulord_subtract(S1, S2, S1min2).

% set_print(S)
% prints out the set S
%
%% set_print(S) :-
%% 	write(S).


% set_rename(S, VIlist1, VIlist2, Sr)
% Sr contains the elements of S in which the variables out of VIlist1 have
% been renamed to the corresponding variables in VIlist2.
% Sr is again an ordered set.
%
set_rename(S,VIlist1,VIlist2, Sr) :-
	set_all_members(S, LS), set_empty(S2i),
	videntl_rename(LS, VIlist1,VIlist2, S2i, Sr).
	
% :- mode videntl_rename(i,i,i,i,o).
videntl_rename([], _Ilist1,_Ilist2, Sr, Sr).
videntl_rename([I|IL], Ilist1,Ilist2, Sp, Sr) :-
	vident_rename(I,Ilist1,Ilist2,Ir),
	set_add_el(Ir,Sp, Sp1),
	videntl_rename(IL, Ilist1,Ilist2, Sp1,Sr).

% :- mode vident_rename(i,i,i,o).
vident_rename(I,[VI|_], [VIr|_], VIr):- I == VI, !.
vident_rename(I,[_|Ilist1], [_|Ilist2], VIr) :-
	vident_rename(I,Ilist1, Ilist2, VIr).

%% % set_is_singleton(S)
%% % is true when S is a singleton
%% %
%% set_is_singleton(S):-
%% 	kulord_is_singleton(S).

% set_boxplus(S1, S2, S12)
% S12 = S1 \boxplus_1 S2
%
% :- mode set_boxplus(i,i,o).
set_boxplus(S1, S2, S12):-
	set_intersect(S1, S2, S1DS2),
	( set_empty(S1DS2) ->
		(set_union(S1,S2,S12set), S12 = [S12set])
	;
		constructplus(S1, S2, S1DS2, [], S12)
	).

% constructplus(S1, S2, S1DS2, S12Acc, S12)
% S1DS2 = intersection of S1 and S2; note: S1DS2 =/= empty_set !
%
% :- mode constructplus(i,i,i,i,o).
constructplus(S1, S2, S1DS2, S12Acc, S12):-
	set_union(S1, S2, S1US2),
	set_diff(S1US2, S1DS2, S12minus),
	(set_empty(S12minus) ->		% test can be removed if possible
					% unsatisfiability is represented
		NewS12Acc = S12Acc
	;
		ss_add_el(S12minus, S12Acc, NewS12Acc)
	),
	add_extensions(S12minus, S1DS2, NewS12Acc, S12).

% add_extensions(S, D, SEAcc, SE)
% SE = { S U {Xi} | Xi in D }
%
% :- mode add_extensions(i,i,i,o).
add_extensions(_, [], S12, S12):- !.
add_extensions(S, [X | D], S12Acc, S12):-
	set_add_el(X, S, NewS),
	ss_add_el(NewS, S12Acc, NewS12Acc),
	add_extensions(S, D, NewS12Acc, S12).


% set_product(Set1, Set2, SSet)
% is true when SSet is the cartesian product of Set1 and Set2.
% SSet is an ordered set of sets (where sets on itself are also ordered);
% the order is the standard order @<
% requirement : use only if the intersection of Set1 and Set2 is empty !!
%
% :- mode set_product(i,i,?).

set_product([], _S2, []):- !.
set_product(_S1, [], []):- !.
set_product(S1, S2, SProd):-
	set_prod(S1, S2, [], SProd).

set_prod([], _S2, SProd, SProd):- !.
set_prod([Head | Tail], S2, SProdAcc, SProd):-
	set_prod1(S2, Head, SProd1),
	ss_union(SProdAcc, SProd1, NewSProdAcc),
	set_prod(Tail, S2, NewSProdAcc, SProd).

set_prod1([], _, []):- !.
set_prod1([Head | Tail], X, [HeadX | SProd1]):-
	pair(Head, X, HeadX),
	set_prod1(Tail, X, SProd1).

pair(Head, X, [Head,X]):-
	Head @< X, !.
pair(Head, X, [X,Head]).	% Head @>= X
