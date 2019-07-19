:- module(psets,[ord_remove/3,update_if_member_idlist/3],[]).

:- push_prolog_flag(multi_arity_warnings,off).

ord_remove([], _, []) :- !.
ord_remove([Head1|Tail1], Element, Difference) :-
	compare(Order, Head1, Element),
	ord_remove(Order, Head1, Tail1, Element, Difference).
ord_remove(<, Head1, [], _, [Head1]) :- !.
ord_remove(<, Head0, [Head1|Tail1], Element, [Head0|Difference]) :-
	compare(Order, Head1, Element),
	ord_remove(Order, Head1, Tail1, Element, Difference).
ord_remove(=, _, Tail1, _, Tail1).
ord_remove(>, Head1, Tail1, _, [Head1|Tail1]).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% update_if_member_idlist(+,+,-)                                         %
% update_if_member_idlist(List,Id,AddList)                               %
% This predicate is some kind of "select". If Id/_ is in List, then      %
% AddList is the result of eliminating Id/_ from List. Otherwise they    %
% are identical.                                                         %
%  This predicate has been modified and now only keeps in Addlist those  %
% nodes older than Id (GPS)                                              %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

update_if_member_idlist([],_Id,[]).
update_if_member_idlist([Head1/V|Tail1],Id,List):-
	compare(Order,Id,Head1),
	update_if_member_idlist(Order,Head1/V,Tail1,Id,List).

update_if_member_idlist(<,_Head1,_Tail1,_Id,[]).
%update_if_member_idlist(<,Head1,Tail1,_Id,[Head1|Tail1]).
update_if_member_idlist(=,_,Tail1,Id,List):-
	update_if_member_idlist(Tail1,Id,List).
update_if_member_idlist(>,Head1,Tail1,Id,[Head1|List]):-
	update_if_member_idlist(Tail1,Id,List).

:- pop_prolog_flag(multi_arity_warnings).
