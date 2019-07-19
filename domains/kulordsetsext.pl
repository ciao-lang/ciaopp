% :- compatibility.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extensions to ordered set operations (based on the ordsets.pl in the library
% of sicstus prolog)
% Copyright (C) 1993 Veroniek Dumortier and Katholieke Universiteit Leuven.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% A set is represented as an ordered list of elements, where the order
% is defined by the @< family of term comparison predicates


        %*************************************************}
        %* kulord_setutl_member(?_Element, ?_Set)        *}
        %* is true when Set is a list, and _Element      *}
        %* occurs in it.                                 *}
        %*************************************************}

%% kulord_setutl_member(_Element, [_Head|_Tail]) :-
%% 	kulord_setutl_member(_Element, _Head, _Tail).
%% 
%% kulord_setutl_member(_Element, _Element, _).
%% kulord_setutl_member(_Element, _, [_Head|_Rest]) :-
%% 	kulord_setutl_member(_Element, _Head, _Rest).

        %**************************************************}
        %* kulord_setutl_memberchk(i_Element, i_Set)      *}
        %* means the same thing, but may only be used to  *}
        %* test whether a known _Element occurs in a      *}
        %* known Set.  In return for this limited use, it *}
        %* is more efficient when it is applicable.       *}
        %**************************************************}

% :- mode kulord_setutl_memberchk(i, i) .
kulord_setutl_memberchk(_Element, [_Head|_Tail]) :-
	kulord_setutl_memberchk(_Element, _Head, _Tail).

% :- mode kulord_setutl_memberchk(i,i, i) .
kulord_setutl_memberchk(_Element1, _Element2, _) :- _Element1 == _Element2,
	!.
kulord_setutl_memberchk(_Element, _, [_Head|_Rest]) :-
	kulord_setutl_memberchk(_Element, _Head, _Rest).


	%*************************************************
	% kulord_is_singleton(i_Set)
	% is true when Set is a singleton
	%*************************************************

% kulord_is_singleton([_]).


	%*************************************************
	% kulord_empty(?_Set)
	% is true when Set is empty
	%*************************************************

kulord_empty([]).
