:- module(acc_ops,
       [relevant/1,
	init_relevant_entries/0,
	add_relevant/1,
	remove_irrelevant_entries/0,
	remove_identical_entries/1],
	[assertions, datafacts]).

:- doc(title,"Reduced Certificates for Abstraction-Carrying Code").

:- doc(author, "Elvira Albert").
:- doc(author, "P. Arenas").

:- doc(module,"This module contains operations which are common to 
	the algorithms used for Abstraction-Carrying Code.").

:- data relevant/1.

:- doc(relevant(Id),"relevant facts are used for asserting in
database the @var{Id} of relevant entries").

:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(library(conc_aggregates), [findall/3]).
:- use_module(ciaopp(plai/fixpo_ops), [complete_prev/7]).
:- use_module(ciaopp(plai/domains), [abs_sort/3, identical_proj/5]).

init_relevant_entries:-
        retractall_fact(relevant(_)).


add_relevant(relevant(A)):-
	relevant(A),!.
add_relevant(relevant(A)):-
	asserta_fact(relevant(A)).

%------------------------------------------------------------------------%

:- doc(remove_irrelevant_entries,"Retracts from database those
completes which are irrelevant in the sense that checking can still be
done in one pass without having them in the certificate. It is useful
for Reduced Certificates for Abstraction-Carrying Code").

remove_irrelevant_entries:- 
	findall(complete(_SgKey,_AbsInt,_Subg,_Proj1,_Prime1,Id,_Fs),
	   current_fact(complete(_SgKey,_AbsInt,_Subg,_Proj1,_Prime1,Id,_Fs)),
	   L),
	remove_irrelevant(L),!.

remove_irrelevant([]):-!.
remove_irrelevant([complete(_SgKey,_AbsInt,_Subg,_Proj1,_Prime1,Id,_Fs)|Ls]):-
	relevant(Id),!,
	remove_irrelevant(Ls).

remove_irrelevant([complete(_SgKey,_AbsInt,_Subg,_Proj1,_Prime1,Id,_Fs)|Ls]):-
	retract_fact(complete(_SgKey,_AbsInt,_Subg,_Proj1,_Prime1,Id,_Fs)),
	remove_irrelevant(Ls).



%------------------------------------------------------------------------%

:- doc(remove_identical_entries,"Retracts from database those
completes in the current analysis which are identical to those
computed in the previous analysis. It is useful for the generation of
Incremental Certificates for ACC").

remove_identical_entries(AbsInt):-
	current_fact(complete(SgKey,AbsInt,Sg,Proj_u,_Prime_u,Id,_Fs),Ref),
	Id \== no,
	abs_sort(AbsInt,Proj_u,Proj),
	((current_fact(complete_prev(SgKey,AbsInt,Subg,Proj1,_Prime1_u,Id,_Fs1),Ref2),
	  identical_proj(AbsInt,Sg,Proj,Subg,Proj1)
	 ) ->
	  erase(Ref),
	  erase(Ref2)
	),
	fail.

remove_identical_entries(_AbsInt).



