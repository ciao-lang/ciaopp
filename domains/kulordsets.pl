% :- compatibility.
/* Copyright(C) 1988, Swedish Institute of Computer Science */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%   File   : ORDSETS.PL							      %
%   Author : Lena Flood							      %
%   Updated: 9 September 1988						      %
%   Purpose: Ordered set manipulation utilities				      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%   :- module(ordsets, [
%   	is_kulordset/1,
%   	list_to_kulord_set/2,
%   	kulord_add_element/3,
%   	kulord_del_element/3,
%   	kulord_disjoint/2,
%   	kulord_intersect/2,
%   	kulord_intersection/3,
%   	kulord_intersection/2,
%   	kulord_seteq/2,
%   	kulord_setproduct/3,
%   	kulord_subset/2,
%   	kulord_subtract/3,
%   	kulord_symdiff/3,
%   	kulord_union/3,
%   	kulord_union/2,
%   	kulord_union/4
%   		   ]).

%   Adapted from shared code written by Richard A O'Keefe. 

%   In this package, sets are represented by ordered lists with no
%   duplicates.	 Thus {c,r,a,f,t} would be [a,c,f,r,t].	 The ordering
%   is defined by the @< family of term comparison predicates, which
%   is the ordering used by sort/2 and setof/3.

%   The benefit of the ordered representation is that the elementary
%   set operations can be done in time proportional to the Sum of the
%   argument sizes rather than their Product. 

%   Renamed by V. Dumortier in order to avoid name conflict a.o. with
%   predicates used in PLAI

%% :- mode
%% 	is_kulordset(+),
%% 	    is_kulordset(+, ?),
%% 	list_to_kulord_set(+, ?),
%% 	kulord_add_element(+, +, ?),
%% 	    kulord_add_element(+, +, +, +, ?),
%% 	kulord_del_element(+, +, ?),
%% 	    kulord_del_element(+, +, +, +, ?),
%% 	kulord_disjoint(+, +),
%% 	    kulord_disjoint(+, +, +, +, +),
%% 	kulord_intersect(+, +),
%% 	    kulord_intersect(+, +, +, +, +),
%% 	kulord_intersection(+, +, ?),
%% 	    kulord_intersection(+, +, +, +, +, ?),
%% 	kulord_intersection(+, ?),
%% 	    kulord_intersection(+, +, +, +, ?),
%% 	kulord_seteq(+, +),
%% 	kulord_setproduct(+, +, ?),
%% 	    kulord_setproduct(+, +, ?, -),
%% 	kulord_subset(+, +),
%% 	    kulord_subset(+, +, +, +),
%% 	kulord_subtract(+, +, ?),
%% 	    kulord_subtract(+, +, +, +, +, ?),
%% 	kulord_symdiff(+, +, ?),
%% 	    kulord_symdiff(+, +, +, +, +, ?),
%% 	kulord_union(+, +, ?),
%% 	    kulord_union(+, +, +, +, +, ?),
%% 	kulord_union(+, ?),
%% 	    kulord_union_all(+, +, ?, ?),
%% 	kulord_union(+, +, ?, ?),
%% 	    kulord_union(+, +, +, +, +, ?, ?).

%% %   is_kulordset(+Set)
%% %   is true when Set is an ordered set.
%% 
%% is_kulordset(X) :- var(X), !, fail.
%% is_kulordset([]).
%% is_kulordset([Head|Tail]) :-
%% 	is_kulordset(Tail, Head).
%% 
%% is_kulordset(X, _) :- var(X), !, fail.
%% is_kulordset([], _).
%% is_kulordset([Head|Tail], Left) :-
%% 	Left @< Head,
%% 	is_kulordset(Tail, Head).

%   list_to_kulord_set(+List, ?Set)
%   is true when Set is the ordered representation of the set represented
%   by the unordered representation List.  

list_to_kulord_set(List, Set) :-
	sort(List, Set).


%   kulord_add_element(+Set1, +Element -Set2)
%   is true when Set2 is Set1 with Element inserted in it, preserving
%   the order.

kulord_add_element([], Element, [Element]).
kulord_add_element([Head|Tail], Element, Set) :-
	compare(Order, Head, Element),
	kulord_add_element(Order, Head, Tail, Element, Set).

kulord_add_element(<, Head, Tail, Element, [Head|Set]) :-
	kulord_add_element(Tail, Element, Set).
kulord_add_element(=, Head, Tail, _, [Head|Tail]).
kulord_add_element(>, Head, Tail, Element, [Element,Head|Tail]).

%% %   kulord_del_element(+Set1, +Element, ?Set2)
%% %   is true when Set2 is Set1 but with Element removed.
%% 
%% kulord_del_element([], _, []).
%% kulord_del_element([Head|Tail], Element, Set) :-
%% 	compare(Order, Head, Element),
%% 	kulord_del_element(Order, Head, Tail, Element, Set).
%% 
%% kulord_del_element(<, Head, Tail, Element, [Head|Set]) :-
%% 	kulord_del_element(Tail, Element, Set).
%% kulord_del_element(=, _, Tail, _, Tail).
%% kulord_del_element(>, Head, Tail, _, [Head|Tail]).
%% 
%% %   kulord_disjoint(+Set1, +Set2)
%% %   is true when the two ordered sets have no element in common.  
%% 
%% 
%% kulord_disjoint([], _) :- !.
%% kulord_disjoint(_, []) :- !.
%% kulord_disjoint([Head1|Tail1], [Head2|Tail2]) :-
%% 	compare(Order, Head1, Head2),
%% 	kulord_disjoint(Order, Head1, Tail1, Head2, Tail2).
%% 
%% kulord_disjoint(<, _, [], _, _) :- !.
%% kulord_disjoint(<, _, [Head1|Tail1], Head2, Tail2) :-
%% 	compare(Order, Head1, Head2),
%% 	kulord_disjoint(Order, Head1, Tail1, Head2, Tail2).
%% kulord_disjoint(>, _, _, _, []) :- !.
%% kulord_disjoint(>, Head1, Tail1, _, [Head2|Tail2]) :-
%% 	compare(Order, Head1, Head2),
%% 	kulord_disjoint(Order, Head1, Tail1, Head2, Tail2).


%   kulord_intersect(+Set1, +Set2)
%   is true when the two ordered sets have at least one element in common.

kulord_intersect([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	kulord_intersect(Order, Head1, Tail1, Head2, Tail2).

kulord_intersect(<, _, [Head1|Tail1], Head2, Tail2) :-
	compare(Order, Head1, Head2),
	kulord_intersect(Order, Head1, Tail1, Head2, Tail2).
kulord_intersect(=, _, _, _, _).
kulord_intersect(>, Head1, Tail1, _, [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	kulord_intersect(Order, Head1, Tail1, Head2, Tail2).



%   kulord_intersection(+Set1, +Set2, ?Intersection)
%   is true when Intersection is the ordered representation of Set1
%   and Set2, provided that Set1 and Set2 are ordered sets.

kulord_intersection([], _, []) :- !.
kulord_intersection(_, [], []) :- !.
kulord_intersection([Head1|Tail1], [Head2|Tail2], Intersection) :-
	compare(Order, Head1, Head2),
	kulord_intersection(Order, Head1, Tail1, Head2, Tail2, Intersection).

kulord_intersection(<, _, [], _, _, []) :- !.
kulord_intersection(<, _, [Head1|Tail1], Head2, Tail2, Intersection) :-
	compare(Order, Head1, Head2),
	kulord_intersection(Order, Head1, Tail1, Head2, Tail2, Intersection).
kulord_intersection(=, Head, Tail1, _, Tail2, [Head|Intersection]) :-
	kulord_intersection(Tail1, Tail2, Intersection).
kulord_intersection(>, _, _, _, [], []) :- !.
kulord_intersection(>, Head1, Tail1, _, [Head2|Tail2], Intersection) :-
	compare(Order, Head1, Head2),
	kulord_intersection(Order, Head1, Tail1, Head2, Tail2, Intersection).

%% %   kulord_intersection(+Sets, ?Intersection)
%% %   is true when Intersection is the ordered set representation of the
%% %   intersection of all the sets in Sets.
%% 
%% kulord_intersection([], Intersection) :- !, Intersection = [].
%% kulord_intersection(Sets, Intersection) :- 
%% 	length(Sets, NumberOfSets),
%% 	kulord_intersection(NumberOfSets, Sets, Intersection, []).
%% 
%% kulord_intersection(1, [Set|Sets], Set, Sets) :- !.
%% kulord_intersection(2, [Set,Set2|Sets], Intersection, Sets) :- !,
%% 	kulord_intersection(Set, Set2, Intersection).
%% kulord_intersection(N, Sets0, Intersection, Sets) :-
%% 	A is N>>1,
%% 	Z is N-A,
%% 	kulord_intersection(A, Sets0, X, Sets1),
%% 	kulord_intersection(Z, Sets1, Y, Sets),
%% 	kulord_intersection(X, Y, Intersection).

%   kulord_seteq(+Set1, +Set2)
%   is true when the two arguments represent the same set.  Since they
%   are assumed to be ordered representations, they must be identical.

kulord_seteq(Set1, Set2) :-
	Set1 == Set2.

%% %   kulord_setproduct(+Set1, +Set2, ?SetProduct)
%% %   is true when SetProduct is the cartesian product of Set1 and Set2. The
%% %   product is represented as pairs Elem1-Elem2, where Elem1 is an element
%% %   from Set1 and Elem2 is an element from Set2.
%% 
%% kulord_setproduct([], _, []).
%% kulord_setproduct([Head|Tail], Set, SetProduct)  :-
%% 	kulord_setproduct(Set, Head, SetProduct, Rest),
%% 	kulord_setproduct(Tail, Set, Rest).
%% 
%% kulord_setproduct([], _, Set, Set).
%% kulord_setproduct([Head|Tail], X, [X-Head|TailX], Tl) :-
%% 	kulord_setproduct(Tail, X, TailX, Tl).

%   kulord_subset(+Set1, +Set2)
%   is true when every element of the ordered set Set1 appears in the
%   ordered set Set2.

kulord_subset([], _).
kulord_subset([Head1|Tail1], [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	kulord_subset(Order, Head1, Tail1, Tail2).

kulord_subset(=, _, Tail1, Tail2) :-
	kulord_subset(Tail1, Tail2).
kulord_subset(>, Head1, Tail1, [Head2|Tail2]) :-
	compare(Order, Head1, Head2),
	kulord_subset(Order, Head1, Tail1, Tail2).



%   kulord_subtract(+Set1, +Set2, ?Difference)
%   is true when Difference contains all and only the elements of Set1
%   which are not also in Set2.


kulord_subtract([], _, []) :- !.
kulord_subtract(Set1, [], Set1) :- !.
kulord_subtract([Head1|Tail1], [Head2|Tail2], Difference) :-
	compare(Order, Head1, Head2),
	kulord_subtract(Order, Head1, Tail1, Head2, Tail2, Difference).

kulord_subtract(<, Head1, [], _, _, [Head1]) :- !.
kulord_subtract(<, Head0, [Head1|Tail1], Head2, Tail2, [Head0|Difference]) :-
	compare(Order, Head1, Head2),
	kulord_subtract(Order, Head1, Tail1, Head2, Tail2, Difference).
kulord_subtract(=, _, Tail1, _, Tail2, Difference) :-
	kulord_subtract(Tail1, Tail2, Difference).
kulord_subtract(>, Head1, Tail1, _, [], [Head1|Tail1]) :- !.
kulord_subtract(>, Head1, Tail1, _, [Head2|Tail2], Difference) :-
	compare(Order, Head1, Head2),
	kulord_subtract(Order, Head1, Tail1, Head2, Tail2, Difference).

%% %   kulord_symdiff(+Set1, +Set2, ?Difference)
%% %   is true when Difference is the symmetric difference of Set1 and Set2.
%% 
%% kulord_symdiff([], Set2, Set2) :- !.
%% kulord_symdiff(Set1, [], Set1) :- !.
%% kulord_symdiff([Head1|Tail1], [Head2|Tail2], Difference) :-
%% 	compare(Order, Head1, Head2),
%% 	kulord_symdiff(Order, Head1, Tail1, Head2, Tail2, Difference).
%% 
%% kulord_symdiff(<, Head0, [], Head2, Tail2, [Head0,Head2|Tail2]) :- !.
%% kulord_symdiff(<, Head0, [Head1|Tail1], Head2, Tail2, [Head0|Difference]) :-
%% 	compare(Order, Head1, Head2),
%% 	kulord_symdiff(Order, Head1, Tail1, Head2, Tail2, Difference).
%% kulord_symdiff(=, _,     Tail1, _,	    Tail2, Difference) :-
%% 	kulord_symdiff(Tail1, Tail2, Difference).
%% kulord_symdiff(>, Head1, Tail1, Head0, [], [Head0,Head1|Tail1]) :- !.
%% kulord_symdiff(>, Head1, Tail1, Head0, [Head2|Tail2], [Head0|Difference]) :-
%% 	compare(Order, Head1, Head2),
%% 	kulord_symdiff(Order, Head1, Tail1, Head2, Tail2, Difference).


%   kulord_union(+Set1, +Set2, ?Union)
%   is true when Union is the union of Set1 and Set2.  Note that when
%   something occurs in both sets, we want to retain only one copy.

kulord_union([], Set2, Set2) :- !.
kulord_union(Set1, [], Set1) :- !.
kulord_union([Head1|Tail1], [Head2|Tail2], Union) :-
	compare(Order, Head1, Head2),
	kulord_union(Order, Head1, Tail1, Head2, Tail2, Union).

kulord_union(<, Head0, [], Head2, Tail2, [Head0,Head2|Tail2]) :- !.
kulord_union(<, Head0, [Head1|Tail1], Head2, Tail2, [Head0|Union]) :-
	compare(Order, Head1, Head2),
	kulord_union(Order, Head1, Tail1, Head2, Tail2, Union).
kulord_union(=, Head,  Tail1, _,	  Tail2, [Head|Union]) :-
	kulord_union(Tail1, Tail2, Union).
kulord_union(>, Head1, Tail1, Head0, [], [Head0,Head1|Tail1]) :- !.
kulord_union(>, Head1, Tail1, Head0, [Head2|Tail2], [Head0|Union]) :-
	compare(Order, Head1, Head2),
	kulord_union(Order, Head1, Tail1, Head2, Tail2, Union).


%   kulord_union(+Sets, ?Union) 
%   is true when Union is the union of all the sets in Sets. 

kulord_union([], Union) :- !, Union = [].
kulord_union(Sets, Union) :-
	length(Sets, NumberOfSets),
	kulord_union_all(NumberOfSets, Sets, Union, []).

kulord_union_all(1, [Set|Sets], Set, Sets) :- !.
kulord_union_all(2, [Set,Set2|Sets], Union, Sets) :- !,
	kulord_union(Set, Set2, Union).
kulord_union_all(N, Sets0, Union, Sets) :-
	A is N>>1,
	Z is N-A,
	kulord_union_all(A, Sets0, X, Sets1),
	kulord_union_all(Z, Sets1, Y, Sets),
	kulord_union(X, Y, Union).


%% %   kulord_union(+Set1, +Set2, ?Union, ?New)
%% %   is true when Union is the union of Set1 and Set2, and New is
%% %   the difference between Set2 and Set1.  This is useful if you
%% %   are accumulating members of a set and you want to process new
%% %   elements as they are added to the set.
%% 
%% kulord_union([], Set, Set, Set) :- !.
%% kulord_union(Set, [], Set, []) :- !.
%% kulord_union([O|Os], [N|Ns], Set, New) :-
%% 	compare(C, O, N), 
%% 	kulord_union(C, O, Os, N, Ns, Set, New).
%% 	
%% kulord_union(<, O, [], N, Ns, [O,N|Ns], [N|Ns]) :- !.
%% kulord_union(<, O1, [O|Os], N, Ns, [O1|Set], New) :-
%% 	compare(C, O, N), 
%% 	kulord_union(C, O, Os, N, Ns, Set, New).
%% kulord_union(=, _, Os, N, Ns, [N|Set], New) :-
%% 	kulord_union(Os, Ns, Set, New).
%% kulord_union(>, O, Os, N, [], [N,O|Os], [N]) :- !.
%% kulord_union(>, O, Os, N1, [N|Ns], [N1|Set], [N1|New]) :-
%% 	compare(C, O, N), 
%% 	kulord_union(C, O, Os, N, Ns, Set, New).

