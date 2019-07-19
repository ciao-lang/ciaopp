
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : Freeness Domain
% Copyright (C) 1993 Veroniek Dumortier and Katholieke Universiteit Leuven.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%--------------------------------------------------------------------------
% set of sets 
%
% V. Dumortier
% started September 1993
%
% 13/08/94 Wim Simoens  Corrected bug in ss_reduce_min/3
% set represented as ordered list of variable sets
% (ordering on variable-sets is the set_compare order defined in fros.pl,
% which is in fact the standard order;
% warning : if this order is changed, almost all operations have to be
% redefined !).
%
% Is based on the ordered set implementation in the library of sicstus
% (renamed to kulordsets.pl to avoid naming conflicts)
% 
% warning : abstract data type approach is not followed completely :
%	ss_compare/3,
%	ss_minimise/2, ss_close/2, ss_oplusm/3, ss_aconjm/3,
%	ss_singunion/2
% are implemented in the knowledge that sets are represented as lists !
%
%--------------------------------------------------------------------------
%
% :- global ss_is_singleton/1		% (SF)	ss_is_singleton(+Sset)
% :- global ss_eq/2.			% (SF) 	ss_eq(+Sset,+Sset)
% :- global ss_compare/3.		% (S) 	ss_compare(-Order,+Sset,+Sset)
% :- global ss_add_el/3 .		% (S) 	ss_add_el(+Set,+Sset,-Sset)
% :- global ss_union/3 .		% (S) 	ss_union(+Sset,+Sset,-Sset)
% :- global ss_union_list/2		% (S)	ss_union_list(+ListOfSset,-Sset)
% :- global ss_is_in/2 .		% (SFB)	ss_is_in(+Set,+Sset)
% :- global ss_print/1 .		% (S)	ss_print(+Sset)
% :- global ss_empty/1 . 		% (S) 	ss_empty(-Sset)
% :- global ss_is_subset/2 .		% (SF) 	ss_is_subset(+Sset,+Sset)
% :- global ss_diff/3 .			% (S) 	ss_diff(+Sset,+Sset,-Sset)
%
% :- global ss_inters_sd/4		% (S)	ss_inters_sd(+Sset,+Sset,-Sset,-Sset)
% :- global ss_minimise/2 .		% (S) 	ss_minimise(+Sset,-Sset)
% :- global ss_close/2 .		% (S) 	ss_close(+Sset,-Sset)
% :- global ss_lubm/3			% (S)	ss_lubm(+Sset, +Sset, -Sset)
% :- global ss_oplusm/3 .		% (S) 	ss_oplusm(+Sset,+Sset,-Sset)
% :- global ss_aconjm/3 .		% (S) 	ss_aconjm(+Sset,+Sset,-Sset)
% :- global ss_rename/4.		% (S)	ss_rename(+Sset,+Varlist,+Varlist,-Sset)
% :- global ss_restriction		% (S)	ss_restriction(+Sset,+Varlist,-Sset)
% :- global ss_identical/2		% (SF)	ss_identical(+Sset,+Sset)
% :- global ss_sort/2			% (S)	ss_sort(+Sset,-Sset)
% :- global ss_make_AlfaFunctor/3	% (S)	ss_make_AlfaFunctor(+Varlist,+Var,-Sset)
% :- global ss_make_AlfaFunctor_groups/3	% (S)	ss_make_AlfaFunctor_groups(+Grouplist,+Var,-Sset)
% :- global ss_split/4			% (S)	ss_split(+Sset,+Varlist,-Sset,-Sset)
% :- global ss_make_singl/2		% (S)	ss_make_singl(+Varlist,-Sset)
% :- global ss_reducemin/3		% (S)	ss_reducemin(+Sset,+Varlist,-Sset)
% :- global ss_make_pairs/2		% (S)	ss_make_pairs(+Varlist,-Sset)
% :- global ss_make_pairs/3		% (S)	ss_make_pairs(+Varlist,+Varlist,-Sset)
%
%--------------------------------------------------------------------------

%% % ss_is_singleton(SS)
%% % tests whether SS is a singleton
%% %
%% ss_is_singleton([_]).
%% 
%% %--------------------------------------------------------------------------
%% 
%% % ss_eq(SS1, SS2)
%% % is true when SS1 and SS2 represent the same set of sets
%% %
%% % :- mode ss_eq(i,i).
%% ss_eq(SS1, SS2):-
%% 	kulord_seteq(SS1, SS2).
%% 
%% %--------------------------------------------------------------------------
%% 
%% % ss_compare(Order, SS1, SS2)
%% % is true when "SS1 Order SS2" holds, where Order is the standard order.
%% %
%% % :- mode ss_compare(?,?,?).
%% ss_compare(Order, SS1, SS2):-
%% 	compare(Order, SS1, SS2).

%--------------------------------------------------------------------------

% ss_add_el(E, SSold, SSnew)
% is true when SSnew is SSold with E inserted in it, preserving the order
%
% :- mode ss_add_el(i,i,o).
ss_add_el(E, SSold, SSnew):-
	kulord_add_element(SSold, E, SSnew).

%--------------------------------------------------------------------------

% ss_union(SS1, SS2, SSunion)
% is true when SSunion is the union of SS1 and SS2 (when something occurs
% in both sets of sets, only one copy will be retained !).
%
% :- mode ss_union(i,i,o).
ss_union(SS1, SS2, SSunion):-
	kulord_union(SS1, SS2, SSunion).

%--------------------------------------------------------------------------

% ss_union_list(ListSS, SSunion)
% is true when SSunion is the union of all the sets in ListSS.
%
% :- mode ss_union_list(i,o).
ss_union_list(ListSS, SSunion):-
	kulord_union(ListSS, SSunion).

%--------------------------------------------------------------------------

% ss_is_in(E,SS)
% is true when E occurs in the set SS
% MAY ONLY BE USED TO TEST WHETHER A KNOWN ELEMENT OCCURS IN A KNOWN SET
% In return for this limited use, it is more efficient when it is applicable.
%
% :- mode ss_is_in(o,i).
ss_is_in(E, SS):-
	kulord_setutl_memberchk(E, SS).

%--------------------------------------------------------------------------

% ss_print(SS)
% prints out the set of sets SS
%
% :- mode ss_print(i).
%% ss_print(SS):-
%% 	write(SS).

%--------------------------------------------------------------------------

% ss_empty(SS)
% is true when SS is the empty set
%
ss_empty(SS):-
	kulord_empty(SS).

%--------------------------------------------------------------------------

% ss_is_subset(SubSS, SS)
% is true when every element of SubSS appears in SS
%
% :- mode ss_is_subset(i,i).
ss_is_subset(SubSS, SS):-
	kulord_subset(SubSS, SS).

%--------------------------------------------------------------------------

% ss_diff(SS1, SS2, SS1min2)
% is true when SS1min2 contains all and only the elements of SS1 which
% are not also in SS2
%
% :- mode ss_diff(SS1, SS2, SS1min2).
ss_diff(SS1, SS2, SS1min2):-
	kulord_subtract(SS1, SS2, SS1min2).

%--------------------------------------------------------------------------

%% % ss_inters_sd(SS1,SS2,Inters,LSd)       (S)
%% % SS1,SS2, Inters, Lsd : ordered set of (ordered) sets; 
%% % Inters = { S | S in SS1 \cap SS2}
%% % LSd = { S | S in (SS1 \ SS2)  or  S in (SS2 \ SS1)}
%% %
%% % :- mode ss_inters_sd(i,i,o,o).
%% ss_inters_sd(SS1, SS2, Inters, LSd) :-
%%         ss_empty(Empty),
%%         ssl_inters_sd(SS1, SS2, Empty, Inters, LSd).
%% 
%% % ssl_inters_sd(L1,L2,Interspart,Inters,LSd)     (S)
%% % L1,L2, Interspart, Inters, LSd : ordered set of (ordered) sets;
%% % Inters = { S | S in L1 \cap L2} U Interspart
%% % LSd = { S | S in (L1 \ L2)  or  S in (L2 \ L1) }
%% %
%% % :- mode ssl_inters_sd(i,i,i,o,o).
%% ssl_inters_sd(L1, [], Inters, Inters, L1) :-!.
%% ssl_inters_sd([], L2, Inters, Inters, L2) :-!.
%% ssl_inters_sd([Head1|Tail1], [Head2|Tail2], Inters, IntersR, Sd) :-
%%         set_compare(Rel, Head1, Head2),
%%         ssl_inters_sd(Rel, Head1, Tail1, Head2, Tail2, Inters, IntersR, Sd).
%% 
%% % ssl_inters_sd(Rel,Head1,Tail1, Head2, Tail2, Inters, IntersR,Sd)       (S)
%% % Head1,Head2 : (ordered) set; Tail1, Tail2, ,Sd: ordered set of (ordered) sets
%% % Rel is '=' or '<' or '>'; Inters, IntersR : Ordered Lists of ordered sets
%% %
%% % :- mode ssl_inters_sd(i,i,i,i,i,i,o,o).
%% ssl_inters_sd('=', Head1, Tail1, _Head2, Tail2, Inters, IntersR , Sd):-!,
%%         ss_add_el(Head1, Inters, Inters1),
%%         ssl_inters_sd(Tail1, Tail2, Inters1, IntersR, Sd).
%% ssl_inters_sd('<', Head1, Tail1, Head2, Tail2, Inters, IntersR, [Head1|Sd]):-
%%         ssl_inters_sd(Tail1, [Head2|Tail2], Inters, IntersR, Sd).
%% ssl_inters_sd('>', Head1, Tail1, Head2, Tail2, Inters, IntersR, [Head2|Sd]):-
%%         ssl_inters_sd([Head1|Tail1], Tail2, Inters, IntersR, Sd).

%--------------------------------------------------------------------------
%%% ss_minimise/2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Version 2 with difference lists : a new minimal set is added at the end of
% SSetMin so far.
% No special check for pairs
% Test if "union of subsets of A = A" is done immediately !
% 	(stop as soon as "union of >part of< the subsets of A = A")
% Difference with version 1 with difference lists is in ss_min/5 (4th clause),
% ss_is_subsetunion/5 and ss_is_subsetunion3/3

% ss_minimise(SS, SSmin)
% SSmin = minimise(SS)
%
% :- mode ss_minimise(i,o).
ss_minimise([], []):- !.
ss_minimise(SS, SSmin):-
	ss_singunion(SS, Sing),
	ss_min(SS, Sing, SSm, SSm, SSmin).

% ss_min(SS, Sing, SSmH, SSmT, SSmin)
%	the third and fourth argument (SSmH and SSmT) form a difference list
% SS is the not yet considered part of the set of sets to be minimised
% Sing is the union of all singletons in the set of sets to be minimised
% SSmH - SSmT is the minimised SS constructed so far
% SSmin = (SSmH - SSmT) U { S | S minimal in SS }
%
% note : add a case if the empty set may occur in SS (if unsatisfiability is
%	represented)
%
% :- mode ss_min(i,i,?,?,o).
ss_min([], _, SSmin, [], SSmin):- !.
ss_min([[Elem] | Tail], Sing, SSmH, [[Elem] | SSmT], SSmin):-
	!,
	ss_min(Tail, Sing, SSmH, SSmT, SSmin).
ss_min([A | SS], Sing, SSmH, SSmT, SSmin):-
	set_is_subset(A, Sing), !,
	ss_min(SS, Sing, SSmH, SSmT, SSmin).
ss_min([A | SS], Sing, SSmH, SSmT, SSmin):-
	( ss_is_subsetunion(A, SSmH, SSmT, SS, []) ->
		% A is not minimal since it is the union of subsets
		NewSSmT = SSmT
	;
		SSmT = [A | NewSSmT]
	),
	ss_min(SS, Sing, SSmH, NewSSmT, SSmin).

% ss_is_subsetunion(A, SSmH, SSmT, SS, U).
% A, U : set; SSmH-SSmT, SS : set of sets 
% A =  U  U  U{ D | D in SSmH - SSmT  or D in SS, D \subseteq A }
%
% :- mode ss_is_subsetunion(i,?,?,i,i).
ss_is_subsetunion(_A, SSmH, SSmT, [], _U):-
	SSmH == SSmT, !, fail.
ss_is_subsetunion(A, SSmH, SSmT, SS, U):-
	SSmH == SSmT, !,
	ss_is_subsetunion3(A, SS, U).
ss_is_subsetunion(A, [D | SSmH], SSmT, SS, U):-
	( set_is_subset(D, A) ->
		( set_union(D, U, NewU),
		  (set_eq(NewU,A) ->
				true
			;
				ss_is_subsetunion(A, SSmH, SSmT, SS, NewU)
		  )
		)
	;
		ss_is_subsetunion(A, SSmH, SSmT, SS, U)
	).

% ss_is_subsetunion3(A, SS, U).
% A, U : set; SS : set of sets 
% A =  U  U  U{ D | D in SS, D \subseteq A }
%
% :- mode ss_is_subsetunion3(i,i,i).
ss_is_subsetunion3(_A, [], _U):-
	!, fail.
ss_is_subsetunion3(A, [D | SS], U):-
	( set_is_subset(D, A) ->
		( set_union(D, U, NewU),
		  ( set_eq(NewU,A) ->
				true
			;
				ss_is_subsetunion3(A, SS, NewU)
		  )
		)
	;
		ss_is_subsetunion3(A, SS, U)
	).


% ss_singunion(Sset, Set)
% Set is the union of all singletons in Sset
%
% :- mode ss_singunion(i,o).
ss_singunion([], []):- !.
ss_singunion([[Elem] | Tail], [Elem | Sing]):-
	!,
	ss_singunion(Tail, Sing).
ss_singunion([_ | Tail], Sing):-
	ss_singunion(Tail, Sing).

%--------------------------------------------------------------------------
%%% ss_close/2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss_close(SS, SSc)
% SSc = close(SS)
%
% :- mode ss_close(i,o).
ss_close(SS, SSc):-
	ss_close3(SS, [], SSc).

% ss_close(SS, SScAcc, SSc).
% SSc = SScAcc U { A U B | A in SS, B in SScAcc } U { A | A in SS}
%
% :- mode ss_close3(i,i,o).
ss_close3([], SSc, SSc):- !.
ss_close3([A | SS], SScAcc, SSc):-
	unions_A_SScAcc(A, SScAcc, [], Us),
	ss_union(SScAcc, Us, SScAcc2),
	ss_add_el(A, SScAcc2, NewSScAcc),
	ss_close3(SS, NewSScAcc, SSc).

% unions_A_SScAcc(A, SScAcc, UsAcc, Us)
% A : ordered set; SScAcc, UsAcc, Us : ordered set of sets
% Us = UsAcc U { A U B | B in SScAcc }
%
% :- mode unions_A_SScAcc(i,i,i,o).
unions_A_SScAcc(_A, [], Us, Us):- !.
unions_A_SScAcc(A, [B | SSc], UsAcc, Us):-
	set_union(A, B, AUB),
	ss_add_el(AUB, UsAcc, NewUsAcc),
 	unions_A_SScAcc(A, SSc, NewUsAcc, Us).


%--------------------------------------------------------------------------
%%% ss_lubm/3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss_lubm(SS1, SS2, SSlub)
% SSlub = lubm(SS1, SS2) = minimise(lub(SS1,SS2))
%
% :- mode ss_lubm(i,o).
ss_lubm(SS1, SS2, SSlub):-
	ss_union(SS1, SS2, SS12),
	ss_minimise(SS12, SSlub).

%--------------------------------------------------------------------------
%%% ss_oplusm/3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss_oplusm(SS1, SS2, SSres)
% requirement : SS1 and SS2 should be minimal !
% SSres = SS1 \oplus_m SS2
%
% :- mode ss_oplusm(i,i,o).
ss_oplusm([], _SS2, []):- !.
ss_oplusm(_SS1, [], []):- !.
ss_oplusm(SS1, SS2, SSres):-
	extract_sings(SS1, Sing1, ComSS1),
	extract_sings(SS2, Sing2, ComSS2),
	ss_empty(H1Acc),
	( set_empty(Sing2) ->
		( ComSS1prime = ComSS1, H1 = H1Acc )
	;
		( ss_close(ComSS1, ComSS1Cl),
		  subtract_sings(ComSS1Cl, Sing2, H1Acc, H1),
		  ss_union(ComSS1, H1, ComSS1prime) )
	),
	ss_empty(H2Acc),
	( set_empty(Sing1) ->
		( ComSS2prime = ComSS2, H2 = H2Acc )
	;
		( ss_close(ComSS2, ComSS2Cl),
		  subtract_sings(ComSS2Cl, Sing1, H2Acc, H2),
		  ss_union(ComSS2, H2, ComSS2prime) )
	),
	ss_close(ComSS1prime, ComSS1primeCl),
	ss_close(ComSS2prime, ComSS2primeCl),
	ss_boxplus(ComSS1primeCl, ComSS2primeCl, [], CombSS),
	( set_nondisjoint(Sing1,Sing2) ->
		ss_union(SS1,SS2, H3)	% adjust if unsatisfiability is
					% represented !
	;
		add_singcombs(Sing1, Sing2, ComSS1prime, ComSS2prime, CombSS,
				H1, H2, H3)
	),
	ss_union_list([H1,H2,H3,CombSS], SSresFull),
	ss_minimise(SSresFull, SSres).


% :- mode extract_sings(i,o,o).
% extract_sings(SS, Sing, ComSS)
% SS is an ordered set of sets
% Sing is the union of the singletons in SS (ordered set)
% ComSS is the set of the non-singletons in SS (ordered set of sets)
%
extract_sings([], [], []):- !.
extract_sings([[X] | SS], [X | TailSing], ComSS):-
	!,
	extract_sings(SS, TailSing, ComSS).
extract_sings([A | SS], Sing, [A | TailComSS]):-
	% A is a non-singleton
	extract_sings(SS, Sing, TailComSS).


% :- mode subtract_sings(i,i,i,o).
% subtract_sings(ComSSi, Sing(3-i), HAcc, H)
% H = { A \ Sing(3-i) | A in ComSSi, A \D Sing(3-i) =/= empty,
%			A \ Sing(3-i) =/= empty }  U  HAcc
% H is the set of all sets obtained from ComSSi original by propagating
% Sing(3-i) info (only propagate on ComSSi sets which are non-disjoint with
% Sing(3-i), and do not add empty sets if no unsatisfiability is represented)
% note : Sing(3-i) =/= empty_set
%
subtract_sings([], _Sing, H, H):- !.
subtract_sings([A | SS], Sing, HAcc, H):-
	( set_nondisjoint(A, Sing) ->
		( set_diff(A, Sing, NewA),
		  ( set_empty(NewA) ->		% adjust when unsatisfiability
						% info is represented !
			NewHAcc = HAcc
		    ;
			ss_add_el(NewA, HAcc, NewHAcc)
		  )
		)
	;
		NewHAcc = HAcc
	),
	subtract_sings(SS, Sing, NewHAcc, H).


% ss_boxplus(SS1, SS2, SSplusAcc, SSplus)
% SSplus = SSplusAcc U { A \boxplus_1 B | A in SS1, B in SS2 }
%
% :- mode ss_boxplus(i,i,i,o).
ss_boxplus([], _SS2, SSplus, SSplus):- !.
ss_boxplus(_SS1, [], SSplus, SSplus):- !.
ss_boxplus([A1 | SS1], SS2, SSplusAcc, SSplus):-
	ss_boxplus1(A1, SS2, SSplusAcc, NewSSplusAcc),
	ss_boxplus(SS1, SS2, NewSSplusAcc, SSplus).

% ss_boxplus1(A1, SS, SSplusAcc, SSplus)
% SSplus = SSplusAcc U { A1 \boxplus_1 A2 | A2 in SS }
%
% :- mode ss_boxplus1(i,i,i,o).
ss_boxplus1(_A1, [], SSplus, SSplus):- !.
ss_boxplus1(A1, [A2 | SS], SSplusAcc, SSplus):-
	set_boxplus(A1, A2, A12),
	ss_union(A12, SSplusAcc, NewSSplusAcc),
	ss_boxplus1(A1, SS, NewSSplusAcc, SSplus).


% add_singcombs(Sing1, Sing2, ComSS1', ComSS2', CombSS, H1, H2, H3)
% H3 =	{ {X1,X2} | X1 in Sing1, X2 in Sing2 } (1)
%	U { {X} U A | X in Sing1, A in ComSS2' U CombSS U H1 } (2)
%	U { {X} U A | X in Sing2, A in ComSS1' U CombSS U H2 } (3)
% (special cases for efficiency : Sing1 and/or Sing2 = empty)
% (1) = SSpairs
% (2) = SSsingsets1
% (3) = SSsingsets2
%
% :- mode add_singcombs(i,i,i,i,i,i,i,o).
add_singcombs([], [], _, _, _, _, _, []):- !.
add_singcombs([], Sing2, ComSS1prime, _, CombSS, _, H2, SSRes):-
	!,
	ss_union_list([ComSS1prime, CombSS, H2], ASS2),
	add_XAsets(Sing2, ASS2, [], SSRes).
% REPLACING THE LAST LINE WITH
%	ss_minimise(ASS2, MinASS2),
%	add_XAsets(Sing2, MinASS2, [], SSRes).
% MAY GIVE A SPEED-UP ???
add_singcombs(Sing1, [], _, ComSS2prime, CombSS, H1, _, SSRes):-
	!,
	ss_union_list([ComSS2prime, CombSS, H1], ASS1),
	add_XAsets(Sing1, ASS1, [], SSRes).
% REPLACING THE LAST LINE WITH
%	ss_minimise(ASS1, MinASS1),
%	add_XAsets(Sing1, MinASS1, [], SSRes).	
% MAY GIVE A SPEED-UP ???
add_singcombs(Sing1, Sing2, ComSS1prime, ComSS2prime, CombSS, H1, H2, SSRes):-
	set_product(Sing1, Sing2, SSpairs),
	ss_union_list([ComSS2prime, CombSS, H1], ASS1),
	add_XAsets(Sing1, ASS1, [], SSsingsets1),
% REPLACING THE LAST LINE WITH
%	ss_minimise(ASS1, MinASS1),
%	add_XAsets(Sing1, MinASS1, [], SSsingsets1),
% MAY GIVE A SPEED-UP ???
	ss_union_list([ComSS1prime, CombSS, H2], ASS2),
	add_XAsets(Sing2, ASS2, [], SSsingsets2),
% REPLACING THE LAST LINE WITH
%	ss_minimise(ASS2, MinASS2),
%	add_XAsets(Sing2, MinASS2, [], SSsingsets2),
% MAY GIVE A SPEED-UP ???
	ss_union_list([SSpairs, SSsingsets1, SSsingsets2], SSRes).

% add_XAsets(Sing, ASS, SSextAcc, SSext)
% Sing : ordered set of variables
% ASS, SSextAcc, SSext : ordered set of sets
% SSext = SSextAcc U { {X} U A | X in Sing, A in ASS }
%
% :- mode add_XAsets(i,i,i,o).
add_XAsets([], _, SSext, SSext):- !.
add_XAsets([X | S], SS, SSextAcc, SSext):-
	add_one_XAset(X, SS, [], SSextOne),
	ss_union(SSextAcc, SSextOne, NewSSextAcc),
	add_XAsets(S, SS, NewSSextAcc, SSext).

% add_one_XAset(Var, SS, SSextAcc, SSext)
% SSext = SSextAcc U { {Var} U S | S in SS }
% (note: to prevent doubles : used ss_add_el instead of adding at the end !
%
% :- mode add_one_XAset(i,i,i,o).
add_one_XAset(_X, [], SSext, SSext):- !.
add_one_XAset(X, [S | SS], SSextAcc, SSext):-
	set_add_el(X, S, Sext),
	ss_add_el(Sext, SSextAcc, NewSSextAcc),
	add_one_XAset(X, SS, NewSSextAcc, SSext).


%--------------------------------------------------------------------------
%%% ss_aconjm/3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss_aconjm(SS1, SS2, SScj)
% requirement : SS1 and SS2 should be minimal !
% SScj = SS1 \AconjM SS2
%
% note : adjust if empty set may occur in the abstraction (if unsatisfiability
%	is represented)
%
% :- mode ss_aconjm(i,i,o).
ss_aconjm([], SS2, SS2):- !.
ss_aconjm(SS1, [], SS1):- !.
ss_aconjm(SS1, SS2, SScj):-
	extract_sings(SS1, Sing1, ComSS1),
	extract_sings(SS2, Sing2, ComSS2),
	ss_empty(H1Acc),
	( set_empty(Sing2) ->
		( ComSS1prime = ComSS1, H1 = H1Acc )
	;
		( subtract_sings(ComSS1, Sing2, H1Acc, H1),
		  ss_union(ComSS1, H1, ComSS1prime) )
	),
	ss_empty(H2Acc),
	( set_empty(Sing1) ->
		( ComSS2prime = ComSS2, H2 = H2Acc )
	;
		( subtract_sings(ComSS2, Sing1, H2Acc, H2),
		  ss_union(ComSS2, H2, ComSS2prime) )
	),
	ssl23_close(ComSS1prime, ComSS1primeCl),
	ssl23_close(ComSS2prime, ComSS2primeCl),
	ss23_empty(CombSSAcc),
	ss23_boxplus(ComSS1primeCl, ComSS2primeCl, CombSSAcc, CombSS),
	ss23_to_list(CombSS, LCombSS),
	ss_minimise(LCombSS, LCombSSmin),
	ss_union_list([SS1,SS2,H1,H2,LCombSSmin], SScjFull),
	ss_minimise(SScjFull, SScj).


%%% ssl23_close/2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ssl23_close(SS, SSc)
% SS : ordered set of sets (list)
% SSc: orderedset of sets (23tree)
%
ssl23_close(SS, SSc):-
	ss23_empty(SScAcc),
	ssl23_close3(SS, SScAcc, SSc).

% ssl23_close3(SS, SScAcc, SSc)
% SS : ordered set of sets (list)
% SScAcc, SSc : ordered set of sets (23 trees)
%
ssl23_close3([], SSc, SSc):- !.
ssl23_close3([A | SS], SScAcc, SSc):-
	unions23_A_SScAcc(A, SScAcc, SScAcc, SScAcc2),
	% note: union of 23-trees is not faster than inserting each elem
	% of the 1st tree in the 2nd  <-> with lists : ss_union is faster
	ss23_add_el(A, SScAcc2, NewSScAcc),
	ssl23_close3(SS, NewSScAcc, SSc).

% unions23_A_SScAcc(A, SS, SSunAcc, SSun)
% A : ordered set (list)
% SS, SSunAcc, SSun : ordered set of sets (23-trees)
% SSun = SSunAcc U { A U B | B in SS }
%
unions23_A_SScAcc(_A, two_three, SSun, SSun).
unions23_A_SScAcc(A, two(Key), SSunAcc, SSun):-
	set_union(A, Key, AUKey),
	ss23_add_el(AUKey, SSunAcc, SSun).
unions23_A_SScAcc(A, two(T0,Key,T1), SSunAcc, SSun):-
	set_union(A, Key, AUKey),
	ss23_add_el(AUKey, SSunAcc, SSunAcc2),
	unions23_A_SScAcc(A, T0, SSunAcc2, SSunAcc3),
	unions23_A_SScAcc(A, T1, SSunAcc3, SSun).
unions23_A_SScAcc(A, three(Key1,Key2), SSunAcc, SSun):-
	set_union(A, Key1, AUKey1),
	ss23_add_el(AUKey1, SSunAcc, SSunAcc2),
	set_union(A, Key2, AUKey2),
	ss23_add_el(AUKey2, SSunAcc2, SSun).
unions23_A_SScAcc(A, three(T0,Key1,T1,Key2,T2), SSunAcc, SSun):-
	set_union(A, Key1, AUKey1),
	ss23_add_el(AUKey1, SSunAcc, SSunAcc2),
	set_union(A, Key2, AUKey2),
	ss23_add_el(AUKey2, SSunAcc2, SSunAcc3),
	unions23_A_SScAcc(A, T0, SSunAcc3, SSunAcc4),
	unions23_A_SScAcc(A, T1, SSunAcc4, SSunAcc5),
	unions23_A_SScAcc(A, T2, SSunAcc5, SSun).



%%% ss23_boxplus/4 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss23_boxplus(SS1, SS2, SSplusAcc, SSplus)
% SS1, SS2, SSplusAcc, SSplus : ordered set of sets (23tree)
% SSplus = SSplusAcc U { A \boxplus_1 B | A in SS1, B in SS2 }
% treats special cases before calling the general ss23_boxplus_it1/4
%
% :- mode ss23_boxplus(i,i,i,o).
ss23_boxplus(two_three, _SS2, SSplus, SSplus):- !.
ss23_boxplus(_SS1, two_three, SSplus, SSplus):- !.
ss23_boxplus(SS1, SS2, SSplusAcc, SSplus):-
	ss23_boxplus_it1(SS1, SS2, SSplusAcc, SSplus).


% ss23_boxplus_it1(SS1, SS2, SSplusAcc, SSplus)
% SS1, SS2, SSplusAcc, SSplus : ordered set of sets (23tree)
% SSplus = SSplusAcc U { A \boxplus_1 B | A in SS1, B in SS2 }
%
ss23_boxplus_it1(two_three, _SS2, SSplus, SSplus).
ss23_boxplus_it1(two(Key), SS2, SSplusAcc, SSplus):-
	ss23_boxplus1(Key, SS2, SSplusAcc, SSplus).
ss23_boxplus_it1(two(T0,Key,T1), SS2, SSplusAcc, SSplus):-
	ss23_boxplus1(Key, SS2, SSplusAcc, SSplusAcc2),
	ss23_boxplus_it1(T0, SS2, SSplusAcc2, SSplusAcc3),
	ss23_boxplus_it1(T1, SS2, SSplusAcc3, SSplus).
ss23_boxplus_it1(three(Key1,Key2), SS2, SSplusAcc, SSplus):-
	ss23_boxplus1(Key1, SS2, SSplusAcc, SSplusAcc2),
	ss23_boxplus1(Key2, SS2, SSplusAcc2, SSplus).
ss23_boxplus_it1(three(T0,Key1,T1,Key2,T2), SS2, SSplusAcc, SSplus):-
	ss23_boxplus1(Key1, SS2, SSplusAcc, SSplusAcc2),
	ss23_boxplus1(Key2, SS2, SSplusAcc2, SSplusAcc3),
	ss23_boxplus_it1(T0, SS2, SSplusAcc3, SSplusAcc4),
	ss23_boxplus_it1(T1, SS2, SSplusAcc4, SSplusAcc5),
	ss23_boxplus_it1(T2, SS2, SSplusAcc5, SSplus).


% ss23_boxplus1(A1, SS, SSplusAcc, SSplus)
% A1 : ordered set (list)
% SS, SSplusAcc, SSplus : ordered set of sets (23tree)
% SSplus = SSplusAcc U { A1 \boxplus_1 A2 | A2 in SS }
%
% :- mode ss_boxplus1(i,i,i,o).
ss23_boxplus1(_A1, two_three, SSplus, SSplus):- !.
ss23_boxplus1(A1, two(A2), SSplusAcc, SSplus):-
	set_boxplus(A1, A2, A12),
	ss23_add_list(A12, SSplusAcc, SSplus).
ss23_boxplus1(A1, two(T0,A2,T1), SSplusAcc, SSplus):-
	set_boxplus(A1, A2, A12),
	ss23_add_list(A12, SSplusAcc, SSplusAcc2),
	ss23_boxplus1(A1, T0, SSplusAcc2, SSplusAcc3),
	ss23_boxplus1(A1, T1, SSplusAcc3, SSplus).
ss23_boxplus1(A1, three(Key1,Key2), SSplusAcc, SSplus):-
	set_boxplus(A1, Key1, A1Key1),
	ss23_add_list(A1Key1, SSplusAcc, SSplusAcc2),
	set_boxplus(A1, Key2, A1Key2),
	ss23_add_list(A1Key2, SSplusAcc2, SSplus).
ss23_boxplus1(A1, three(T0,Key1,T1,Key2,T2), SSplusAcc, SSplus):-
	set_boxplus(A1, Key1, A1Key1),
	ss23_add_list(A1Key1, SSplusAcc, SSplusAcc2),
	set_boxplus(A1, Key2, A1Key2),
	ss23_add_list(A1Key2, SSplusAcc2, SSplusAcc3),
	ss23_boxplus1(A1, T0, SSplusAcc3, SSplusAcc4),
	ss23_boxplus1(A1, T1, SSplusAcc4, SSplusAcc5),
	ss23_boxplus1(A1, T2, SSplusAcc5, SSplus).	


%%% ss23_ procedures (copied from vero23.pl) %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% ss23_empty/1 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ss23_empty(two_three).


%%% ss23_add_el/3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- mode ss23_add_el(i,i,o).
ss23_add_el(S,SSold,SSnew) :-
	put_23(SSold,S,SSnew).

% put_23(Old23Tree, Key, New23Tree) iff New23Tree is the tree
% obtained by replacing a key K in Old23Tree with Key,
% such that compare_keys(=, K, Key), or inserting Key if
% there is no such K in Old23Tree

put_23(two_three, Key, TwoThree) :- 
	!,
	TwoThree = two(Key).
put_23(Old, Key, New) :-
	put_23(Old, Key, New1, EKey, ETree),
	put_23_top(ETree, New1, EKey, New).

put_23_top(none, New1, _, New) :-
	!,
	New=New1.
put_23_top(ETree, Tree0, EKey, two(Tree0,EKey,ETree)).

put_23(two(Key1), Key, New, _, none) :-
	compare_keys(Rel, Key, Key1),
	put_2(Rel, Key, Key1, New).
put_23(two(Tree0,Key1,Tree1), Key, New, _, none) :-
	compare_keys(Rel, Key, Key1),
	put_2(Rel, Key, Tree0, Key1, Tree1, New).
put_23(three(Key1,Key2), Key, NewTree, ExtraKey, ExtraTree) :-
	compare_keys(Rel, Key, Key1, Key2),
	put_3(Rel, Key, Key1, Key2, NewTree, ExtraKey, ExtraTree).
put_23(three(Tree0,Key1,Tree1,Key2,Tree2), Key, New, EKey, ETree) :-
	compare_keys(Rel, Key, Key1, Key2),
	put_3(Rel, Key, Tree0, Key1, Tree1, Key2, Tree2, New, EKey, ETree).

put_2(=, Key, _, two(Key)).
put_2(<, Key, Key1, three(Key,Key1)).
put_2(>, Key, Key1, three(Key1,Key)).

put_2(=, Key, Tree0, _, Tree1, two(Tree0,Key,Tree1)).
put_2(<, Key, OldTree0, Key1, Tree1, New) :-
	put_23(OldTree0, Key, NewTree0, ExtraKey, ExtraTree),
	put_2_l(ExtraTree, NewTree0, ExtraKey, Key1, Tree1, New).
put_2(>, Key, Tree0, Key1, OldTree1, New) :-
	put_23(OldTree1, Key, NewTree1, ExtraKey, ExtraTree),
	put_2_r(ExtraTree, Tree0, Key1, NewTree1, ExtraKey, New).

put_2_l(none, Tree0, _, Key1, Tree1, two(Tree0,Key1,Tree1)) :- 
	!.
put_2_l(ETree, Tree0, EKey, Key1, Tree1, 
			three(Tree0,EKey,ETree,Key1,Tree1)).

put_2_r(none, Tree0, Key1, Tree1, _, two(Tree0,Key1,Tree1)) :- 
	!.
put_2_r(ETree, Tree0, Key1, Tree1, EKey,
			three(Tree0,Key1,Tree1,EKey,ETree)).

put_3(1, Key, _, Key2, three(Key,Key2), _, none).
put_3(2, Key, Key1, _, three(Key1,Key), _, none).
put_3(<, Key, Key1, Key2, two(Key), Key1, two(Key2)).
put_3(><, Key, Key1, Key2, two(Key1), Key, two(Key2)).
put_3(>, Key, Key1, Key2, two(Key1), Key2, two(Key)).

put_3(1, Key, Tree0, _, Tree1, Key2, Tree2,
		three(Tree0, Key, Tree1, Key2, Tree2),
		_, none).
put_3(2, Key, Tree0, Key1, Tree1, _, Tree2,
		three(Tree0, Key1, Tree1, Key, Tree2),
		_, none).
put_3(<, Key, OldTree0, Key1, Tree1, Key2, Tree2, New, NEKey, NETree) :-
	put_23(OldTree0, Key, NewTree0, EKey, ETree),
	put_3_l(ETree, NewTree0, EKey, Key1, Tree1, Key2, Tree2, 
		New, NEKey, NETree).
put_3(><, Key, Tree0, Key1, OldTree1, Key2, Tree2, New, NEKey, NETree) :-
	put_23(OldTree1, Key, NewTree1, EKey, ETree),
	put_3_m(ETree, Tree0, Key1, NewTree1, EKey, Key2, Tree2, 
		New, NEKey, NETree).
put_3(>, Key, Tree0, Key1, Tree1, Key2, OldTree2, New, NEKey, NETree) :-
	put_23(OldTree2, Key, NewTree2, EKey, ETree),
	put_3_r(ETree, Tree0, Key1, Tree1, Key2, NewTree2, EKey,
		New, NEKey, NETree).

put_3_l(none, Tree0, _, Key1, Tree1, Key2, Tree2,
		three(Tree0,Key1,Tree1,Key2,Tree2),
		_, none) :-
	!.
put_3_l(ETree, Tree0, EKey, Key1, Tree1, Key2, Tree2,
		two(Tree0,EKey,ETree),
		Key1, two(Tree1,Key2,Tree2)).

put_3_m(none, Tree0, Key1, Tree1, _, Key2, Tree2,
		three(Tree0,Key1,Tree1,Key2,Tree2),
		_, none) :-
	!.
put_3_m(ETree, Tree0, Key1, Tree1, EKey, Key2, Tree2,
		two(Tree0,Key1,Tree1),
		EKey,
		two(ETree,Key2,Tree2)).

put_3_r(none, Tree0, Key1, Tree1, Key2, Tree2, _,
		three(Tree0,Key1,Tree1,Key2,Tree2),
		_, none) :-
	!.
put_3_r(ETree, Tree0, Key1, Tree1, Key2, Tree2, EKey,
		two(Tree0,Key1,Tree1),
		Key2,
		two(Tree2,EKey,ETree)).


% compare_keys(Rel, Key, Key1, Key2) assumes that Key1 < Key2,
% then Rel = < iff Key < Key1
%            1     Key = Key1
%            ><    Key1 < Key < Key2
%            2     Key = Key2
%            >     Key2 < Key
% with respect to the pairwise order of the relation compare_keys/3.

compare_keys(Rel, Key, Key1, Key2) :-
	compare_keys(Rel1, Key, Key1),
	compare_keys1(Rel1, Key, Key2, Rel).

compare_keys1(=, _, _, 1).
compare_keys1(<, _, _, <).
compare_keys1(>, Key, Key2, Rel) :-
	compare_keys(Rel2, Key, Key2),
	compare_keys1(Rel2, Rel).

compare_keys1(=, 2).
compare_keys1(<, ><).
compare_keys1(>, >).

% compare_keys(Rel, Key0, Key1) is a total order on Keys that is used
% to structure the 23-trees.

compare_keys(Rel, Key0, Key1) :-
	set_compare(Rel, Key0, Key1).


%%% ss23_add_list/3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss23_add_list(LS,SSpart, SS)	(S) SS is the 23-tree that results from adding
% the (ordered) sets in the list LS to the 23-tree SSpart.
% :- mode ss_add_list(?,?,o).
ss23_add_list([],SS,SS) .
ss23_add_list([S |L],SS1,SS2) :-
	ss23_add_el(S,SS1, SS1h),
	ss23_add_list(L,SS1h, SS2).

%%% ss23_to_list/2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ss23_to_list(SS,LS) 	(S) converts the 23-tree of (ordered) sets SS into
% an ordinary list of (ordered) sets LS
% :- mode ss23_to_list(i,o).
ss23_to_list(SS,LS) :-
	ss23_to_list(SS,[],LS).

% ss23_to_list(SS, Lpart, LS) 	(S) Lpart: accumulating parameter (list of sets)
% :- mode ss23_to_list(i,i,o).
ss23_to_list(two_three,LS,LS).
ss23_to_list(two(Key),Lpart, LS) :- LS = [Key|Lpart].
ss23_to_list(two(T0,Key,T1),Lpart, LS) :- 
	ss23_to_list(T1,Lpart,Lpart1),
	Lpart2 =[Key|Lpart1],
	ss23_to_list(T0, Lpart2,LS).
ss23_to_list(three(Key1,Key2),Lpart, LS) :- LS = [Key1,Key2|Lpart].
ss23_to_list(three(T0,Key1,T1,Key2,T2),Lpart, LS) :-
	ss23_to_list(T2,Lpart,Lpart1),
	Lpart2 =[Key2|Lpart1],
	ss23_to_list(T1, Lpart2,Lpart3),
	Lpart4 =[Key1|Lpart3],
	ss23_to_list(T0, Lpart4,LS).

%--------------------------------------------------------------------------

%% % ss_rename(SS, Varlist1, Varlist2, SSren).	(S)
%% % Varlist1, Varlist2 : congruent lists of var. identifiers (unordered !)
%% % SS in terms of vars of Varlist1 is renamed to SSren in terms of vars of
%% % Varlist2
%% %
%% % :- mode ss_rename(?,?,?,o).
%% ss_rename(SS, Varlist1, Varlist2, SSren):-
%% 	ss_ren(SS, Varlist1, Varlist2, [], SSren).	% [] is empty <SS>
%% 
%% % :- mode ss_ren(?,?,?,?,o).
%% ss_ren([], _, _, SSren, SSren).
%% ss_ren([S | SS], Varlist1, Varlist2, SSrenAcc, SSren):-
%% 	set_rename(S, Varlist1, Varlist2, Sren),
%% 	ss_add_el(Sren, SSrenAcc, NewSSrenAcc),
%% 	ss_ren(SS, Varlist1, Varlist2, NewSSrenAcc, SSren).

%--------------------------------------------------------------------------

% ss_restriction(SS, Vars, SSr).	(S)
% Vars : ordered set of variables
% SSr = { S in SS | S subseteq Vars }
%
% :- mode ss_restriction(?,?,o).
ss_restriction([], _Vars, []).
ss_restriction([S | SS], Vars, SSr):-
	( set_is_subset(S, Vars) ->
		( SSr = [S | SSrRest],	% uses the fact that [S | SS] is ordered
		ss_restriction(SS, Vars, SSrRest) )
	;
		ss_restriction(SS, Vars, SSr)
	).

%--------------------------------------------------------------------------

% ss_identical(SS1, SS2)	(SF)
% succeeds if SS1 and SS2 are identical
%
% :- mode ss_identical(?,?).
ss_identical(SS1, SS2):-
	SS1 == SS2.

%--------------------------------------------------------------------------

% ss_sort(SS, SSsort)		(S)
% SS is sorted into SSsort (i.e. each variable set in SS is sorted and the
% variable sets themselves are also sorted)
%
% :- mode ss_sort(?,o).
ss_sort(SS, SSsort):-
        ss_sort3(SS, [], SSsort).	% [] is empty <SS>

ss_sort3([], SSsort, SSsort).
ss_sort3([A | SS], SSsortAcc, SSsort):-
        sort(A, Asort),
        ss_add_el(Asort, SSsortAcc, NewSSsortAcc),
        ss_sort3(SS, NewSSsortAcc, SSsort).

%--------------------------------------------------------------------------

% ss_make_AlfaFunctor_groups(VarGroups, X, AlfaC)
% computes the abstraction of X (=|#) Term with VarGroups being
% an ordered set of (ordered) sets of variables in Term
% (variables in a numerical expression form one group, other
%  variables form singleton groups)
% AlfaC = {{X}} U { {X} U G | G in VarGroups }
%
% :- mode ss_make_AlfaFunctor(?,?,o).
ss_make_AlfaFunctor_groups(VarGroups, X, AlfaC):-
	ss_addpairs_groups(VarGroups, X, [[X]], AlfaC).  % [X] is ordered set

% ss_addpairs_groups(VarGroups, X, Acc, AlfaC)
% Acc, AlfaC: ordered set of sets
% AlfaC = Acc U { {X} U G | G in VarGroups }
%
ss_addpairs_groups([],_X,AlfaC,AlfaC).
ss_addpairs_groups([G| Rest],X,Acc,AlfaC) :-
	set_add_el(X,G,S),
	ss_add_el(S,Acc,AccNew),
	ss_addpairs_groups(Rest,X,AccNew,AlfaC).

%--------------------------------------------------------------------------

% ss_split(SS, Vars, SS1, SS2)
% SS = SS1 U SS2 where SS1 contains no variables of Vars
%		and SS2 contains variables of Vars
%
% :- mode ss_split(i,i,o,o).
ss_split([], _Vars, [], []).
ss_split([A | SS], Vars, SS1, [A | SS2]):-
        set_nondisjoint(A,Vars), !,
        ss_split(SS, Vars, SS1, SS2).
ss_split([A | SS], Vars, [A | SS1], SS2):-
        ss_split(SS, Vars, SS1, SS2).

%--------------------------------------------------------------------------

% ss_make_singl(L, SS).
% L is a list of variables (ordered)
% SS is an ordered set of sets
% SS = { {X} | X in L }
%
% :- mode ss_make_singl(i,o).
ss_make_singl([], []).
ss_make_singl([X | Tail], [[X] | SS]):-
        ss_make_singl(Tail, SS).

%--------------------------------------------------------------------------

% ss_reduce_min(SS, Vars, SSrm)
% NOTE: only needed for DFm abstraction
% SS, SSrm : ordered set of sets
% Vars : ordered set of variables
% SSrm = minimise(reduce(SS,Vars))
% with reduce(SS,Vars) = { S \ Vars | S in SS } \ { emptyset }

% :- mode ss_reduce_min(i,i,o).
ss_reduce_min(SS, [], SSrm):- 
	!,  % WS 13/08/94 Corrected bug , was not minimised!
	ss_minimise(SS, SSrm).
ss_reduce_min(SS, Vars, SSrm) :-
	reduce(SS, Vars, [], SSrm_nonmin),
	ss_minimise(SSrm_nonmin, SSrm).

% :- mode reduce(i,i,i,o). 
reduce([], _Vars, SSr, SSr).
reduce([Set | Tail], Vars, Tmp, SSr) :-
	set_diff(Set, Vars, Setmin),
	(Setmin = [],!,
	 Tmp2 = Tmp
	;
	 ss_add_el(Setmin, Tmp, Tmp2)
	),
	reduce(Tail, Vars, Tmp2, SSr).

%--------------------------------------------------------------------------

%% % ss_make_pairs(Vars, Pairs)
%% % Vars : ordered set of variables
%% % Pairs = {{X,Y} | X in Vars, Y in Vars (X # Y) }, ordered set of sets
%% % note: Pairs can directly be constructed as an ordered set !
%% %
%% ss_make_pairs(Vars, Pairs):-
%% 	ss_make_pairs_acc(Vars, [], Pairs).
%% 
%% ss_make_pairs_acc([], Pairs, Pairs).
%% ss_make_pairs_acc([V1 | Rest1], Acc, Pairs):-
%% 	ss_make_pairs_1(Rest1, V1, Acc, NewAcc),
%% 	ss_make_pairs_acc(Rest1, NewAcc, Pairs).

ss_make_pairs_1([], _X, Pairs, Pairs).
ss_make_pairs_1([Y|Ys], X, Acc, Pairs):-
	ss_add_el([X,Y], Acc, NewAcc),	% X <= Y
	ss_make_pairs_1(Ys, X, NewAcc, Pairs).

%--------------------------------------------------------------------------

% ss_make_pairs(Vars1, Vars2, Pairs)
% Vars1, Vars2 : ordered set of variables
% Pairs = {{X,Y} | X in Vars1, Y in Vars2 (X # Y) }, ordered set of sets
%
ss_make_pairs(Vars1, Vars2, Pairs):-
	ss_make_pairs2(Vars1, Vars2, [], Pairs).

ss_make_pairs2([], _Vars2, Pairs, Pairs).
ss_make_pairs2([V1|Vars1], Vars2, Acc, Pairs):-
	ss_one_pairs(Vars2, V1, Acc, NAcc),
	ss_make_pairs2(Vars1, Vars2, NAcc, Pairs).


ss_one_pairs([], _, SS, SS).
ss_one_pairs([X|Vars], Y, Acc, SS):-
	( X \== Y ->
		set_create([X,Y], S),
		ss_add_el(S, Acc, NAcc)
	;
		NAcc = Acc
	),
	ss_make_pairs_1(Vars, Y, NAcc, SS).
