:- module(ch_trees,
	[ch_tree/2,
	 add_ch_tree/2, 
	 clean_up_ch_trees/0,
	 collect_all_ch_trees/1
	], [assertions, isomodes, datafacts]).

:- doc(title,"Basic Operations on Characteristic Trees").

:- doc(author, "Germ@'{a}n Puebla").
:- doc(author, "Claudio Ochoa").

:- doc(module,"This module provides a series of basic operations 
	for using characteristic trees.").

:- use_module(library(aggregates), [findall/3]).

:- data ch_tree/2.

:- pred add_ch_tree(+Id,+Ch_Tree) #"Adds a new ch_tree to the DB".

add_ch_tree(Id,Ch_Tree):-
	assertz_fact(ch_tree(Id,Ch_Tree)).

:- pred clean_up_ch_trees #"Clean ups all ch_trees".

clean_up_ch_trees:-
	retractall_fact(ch_tree(_Id,_Ch_Tree)).

:- pred collect_all_ch_trees(-All_trees) #"Returns all asserted ch_trees".

collect_all_ch_trees(All_trees):-
	findall(Ch_Tree,
	        ch_tree(_,Ch_Tree),
	       All_trees).

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- pred estimate_unfolding_steps(+Ch_tree,-Steps) # "Returns the
% 	number of unfolding @var{Steps} as determined by the
% 	corresponding @var{Ch_tree}".

% estimate_unfolding_steps([],0).
% estimate_unfolding_steps([Path|Paths],N):-
% 	length(Path,N1),
% 	estimate_unfolding_steps(Paths,N2),
% 	N is N1 + N2.

% :- pred amount_externals(+Cht,-Ext) #"Returns the number @var{Ext}
% 	of external predicate calls contained in @var{Cht}".

% amount_externals([],0).
% amount_externals([Path|T],N):-
% 	amount_externals_path(Path,N1),
% 	amount_externals(T,N2),
% 	N is N1 + N2.

% amount_externals_path([],0).
% amount_externals_path([(_:H)|T],N):-
% 	number(H),!,
% 	amount_externals_path(T,N).
% amount_externals_path([_|T],N):-
% 	amount_externals_path(T,N1),
% 	N is N1 + 1.

% :- pred count_atoms(+Cht,-Atoms) # "Returns an estimation of the
% 	numbers of @var{Atoms} to be created in the SLD tree
% 	represented by @var{Cht}.".

% count_atoms(Cht,N):-
% 	prettyvars(Cht),
% 	meta_count_atoms([Cht],N).


% meta_count_atoms([],0).
% meta_count_atoms([Cht|T],N):-
% 	count_atoms_chtree(Cht,N1),
% 	meta_count_atoms(T,N2),
% 	N is N1 + N2.

% count_atoms_chtree([],0):-!.
% count_atoms_chtree([Path],N):-!, % deterministic: count body atoms
% 	body_sizes(Path,N).
% count_atoms_chtree(Cht,Atoms):-
% 	next_branches(Cht,Br),
% 	add_body_atoms(Br,N1),
% 	init_partition(Br,InitP),
% 	partition(Cht,InitP,P),
% 	end_partition(P,EndP),
% 	length(Br,Heads),
% 	meta_count_atoms(EndP,N2),
% 	Atoms is N1 + N2 + Heads - 1.

% add_body_atoms([],0).
% add_body_atoms([A|T],N):-
% 	body_sizes([A],N1),
% 	add_body_atoms(T,N2),
% 	N is N1 + N2.

% next_branches(Cht,Br):-
% 	next(Cht,NB),
% 	sort(NB,Br).

% next([[A|_]],[A]).
% next([[A|_]|T],[A|R]):-
% 	next(T,R).

% init_partition([],[]).
% init_partition([A|T],[(A,[])|R]):-
% 	init_partition(T,R).

% end_partition([],[]).
% end_partition([(_,P)|T],[P|R]):-
% 	end_partition(T,R).

% partition([],P,P).
% partition([Path|T],CP,P):-
% 	Path=[Descriptor|Tail],
% 	insert_into_partition(CP,Descriptor,Tail,NP),
% 	partition(T,NP,P).

% insert_into_partition([(D,L)|T],D,Tail,[(D,[Tail|L])|T]):-!.
% insert_into_partition([C|T],D,Tail,[C|R]):-
% 	insert_into_partition(T,D,Tail,R).

% :- pred body_sizes(+Col,-N) # "Returns the amount of literals @var{N}
% 	in the body of clauses in @var{Col}".

% body_sizes([],0).
% body_sizes([(_:Cl)|T],N):-
% 	number(Cl),!,
% 	orig_clause(_,Body,Cl),
% 	length(Body,N1),
% 	body_sizes(T,N2),
% 	N is N2 + N1 -1 .
% body_sizes([_|T],N):-
% 	body_sizes(T,N).

% :- pred rename_vars(+Cht) # "In order to be able to compare variables,
% 	these are renamed in @var{Cht}. This is done on a per-path basis, so equivalent".

% rename_vars([]).
% rename_vars([Path|T]):-
% 	rename_vars_path(Path).
% 	rename_vars(T).

% rename_vars([]).
% rename_vars([Term|T]):-
% 	numbervars(Term,0,_),
% 	rename_vars(T).

% count_atoms_t([],0).
% count_atoms_t([Col|T],N):-
% 	atoms_col(Col,N1),
% 	count_atoms_t(T,N2),
% 	N is N1 + N2.

% atoms_col(Col,N):-
% 	copy_term(Col,Col_c),
% 	rename_vars(Col_c,RC),
% 	sort(RC,S),
% 	heads(S,N1),
% 	body_sizes(S,N2),
% 	N is N1 + N2 - 2.

% :- pred heads(+Col,-N) #"Returns the number @var{N} of new heads to be
% 	created, i.e., 1 if the pred is determinate, or greater than 1
% 	otherwise".

% heads(Col,N):-
% 	length(Col,N).
