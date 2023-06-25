:- module(slicing,[slicing/3],[]).

:- use_package(assertions).

:- use_module(spec(ch_trees),  [collect_all_ch_trees/1]).
:- use_module(library(compiler/p_unit), [program/2]).
:- use_module(library(llists), [flatten/2]).
:- use_module(library(sort)).

:- doc(title,"A Forward Slicing Algoritm based on Partial Deduction").

:- doc(author, "Germ@'{a}n Puebla").
:- doc(author, "Claudio Ochoa").

:- doc(module," This module contains the implementation of a
    forward slicing algorithm as presented in a paper by Michael
    Leuschel and German Vidal in ESOP2005.").

slicing(_Abs,Sliced_Prog,Sliced_Dicts):-
    program(Prog,Dicts),
    filter_unused(Prog,Dicts,Sliced_Prog,Sliced_Dicts).

filter_unused(Prog,Dicts,Sliced_Prog,Sliced_Dicts):-
    collect_all_ch_trees(All_Trees),
    flatten(All_Trees,List_atoms),
    atoms2ids(List_atoms,List_IDs),
    sort(List_IDs,List_Id_Sorted),
    filter_list(Prog,Dicts,1,List_Id_Sorted,Sliced_Prog,Sliced_Dicts).


:- pred filter_list(Prog,Dicts,Clause_no,Ids,Sl_prog,Sl_dict) 
    : (list(Prog), list(Dicts), int(Clause_no), list(Ids))
    => (list(Sl_prog), list(Sl_dict))

# "Filter elements from @var{Prog} and @var{Dict} according to the
   elements belonging to @var{Ids}, and returns the sliced
   @var{Sl_prog} and @var{Sl_dict}. @var{Clause_no} is just a regular
   counter. @var{Ids} must be sorted.".

filter_list([],[],_,_,[],[]).
filter_list([X|Xs],[Y|Ys],N,[N|Ns],[X|SXs],[Y|SYs]) :- 
    !, N1 is N + 1,
    filter_list(Xs,Ys,N1,Ns,SXs,SYs).
filter_list([_|Xs],[_|Ys],N,Zs,SXs,SYs) :- 
    N1 is N + 1,
    filter_list(Xs,Ys,N1,Zs,SXs,SYs).

    
atoms2ids([],[]).
atoms2ids([(_:N)|R],[N|R2]):-
    number(N),!,
    atoms2ids(R,R2).
atoms2ids([(_:_)|R],R2):-
    atoms2ids(R,R2).
