:- module(unfold_core,[unfold/3],[assertions]).

:- doc(title, "Unfold Transformation").
:- doc(author, "John Gallagher").
% Modified by: Alejandro Serrano, 2013


:- doc(module, "This module tries to remove indirect recursion.  It
   will unfold calls to 

   (1) any non-recursive user-defined predicates and 
   (2) any recursive predicates in a multi-predicate SCC, which is
   not also directly recursive, except for the \"top\" predicate in that
   SCC.  

   The \"top\" predicate in an SCC is not unique; it always takes the first
   predicate of an SCC discovered by the SCC algorithm (which is the
   last predicate in the SCC as listed by the SCC algorithm.

   Note that some indirect recursion can remain. It is not possible
   in general to eliminate indirect recursion by unfolding.:- op(1150,
   fx, entry).").

:- doc(bug, "Does not terminate for predicates of the form:

:- entry p/1 : num.
p(0).
p(N):- N>0, q(N,N).

q(0,N):- N1 is N - 1,p(N1).	
q(M,N):- M>0, M1 is M - 1, q(M1,N).

Note: Such structure of is common in transformed code that has nested loops.
").

:- use_module(library(aggregates)).
:- use_module(library(lists)).

:- use_module(canonical).
:- use_module(readprog).
:- use_module(scc).

:- op(1150, fx, entry).

% TODO: document

unfold(Cls,Entries,UCls) :-
	sortClauses(Cls,Ps,Prog),
	scc(Ps,Prog,SCCs1),
	postprocess_sccs(SCCs1,Entries,SCCs),
	unfoldAll(Cls,Prog,Entries,SCCs,UCls),
	!.

postprocess_sccs([],_,[]).
postprocess_sccs([(recursive,L)|R],Entries,[(recursive,FinalL)|PostR]) :-
	member(E,Entries),
	member(E,L), !,
	delete(L,E,L1),
	append(L1,[E],FinalL), !,
	postprocess_sccs(R,Entries,PostR).
postprocess_sccs([A|R],Entries,[A|PostR]) :-
	!, postprocess_sccs(R,Entries,PostR).

unfoldAll([predicates(_)|Cls],Prog,Entries,SCCs,Cls1) :-
	unfoldAll(Cls,Prog,Entries,SCCs,Cls1).
unfoldAll([clause((A :- B),_Ws)|Cls],Prog,Entries,SCCs,[Cls0|Cls1]) :-
	unfoldClause(A,B,Prog,Entries,SCCs,Cls0),
	unfoldAll(Cls,Prog,Entries,SCCs,Cls1).
unfoldAll([],_,_,_,[]).
	
unfoldClause(A,B,Prog,Entries,SCCs,Cls0) :-
	functor(A,P,N),
	\+ unfoldable(P/N,SCCs,Prog,Entries),
	!,
	melt((A,B),(H,B1)),
	findall((H :- R), resultant(B1,R,Prog,Entries,SCCs), Cls0).
unfoldClause(_,_,_,_,_,[]).

resultant((B,Bs),R,Prog,Entries,SCCs) :-
	functor(B,P,N),
	unfoldable(P/N,SCCs,Prog,Entries),
	user_clauses(Prog,P/N,Cls),
	!,
	member((X:-Y),Cls),
	melt((X,Y),(B,Z)),
	conjoin(Z,Bs,Bs1),
	resultant(Bs1,R,Prog,Entries,SCCs).
resultant((B,Bs),(B,R),Prog,Entries,SCCs) :-
	!,
	resultant(Bs,R,Prog,Entries,SCCs).
resultant(B,R,Prog,Entries,SCCs) :-
	functor(B,P,N),
	unfoldable(P/N,SCCs,Prog,Entries),
	user_clauses(Prog,P/N,Cls),
	!,
	member((X:-Y),Cls),
	melt((X,Y),(B,Z)),
	resultant(Z,R,Prog,Entries,SCCs).
resultant(B,B,_,_,_).
	
unfoldable(P/N,SCCs,Prog,Entries) :-
	member((non_recursive,[P/N]),SCCs),
	\+ member(P/N, Entries), % P/N \== E, 	
	user_clauses(Prog,P/N,Cls),
	Cls \== [],
	!.
unfoldable(P/N,SCCs,Prog,Entries) :-
	member((recursive,G),SCCs),
	length(G,K),
	K > 1,
	member(P/N,G),
	\+ nth(K,G,P/N),
	\+ member(P/N,Entries), % P/N \== E,
	user_clauses(Prog,P/N,Cls),
	Cls \== [],
	\+ directRecursive(Cls,P/N).
	
directRecursive(Cs,P/N) :-
	member((_:-Y),Cs),
	bodyMemb(B,Y),
	functor(B,P,N).

bodyMemb(B,(B,_)) :-
	!.
bodyMemb(B,(_,Bs)) :-
	!,
	bodyMemb(B,Bs).
bodyMemb(B,B).
	
conjoin(true,C,C) :-
	!.
conjoin((C,Cs),D,(C,E)) :-
	!,
	conjoin(Cs,D,E).
conjoin(C,D,(C,D)).