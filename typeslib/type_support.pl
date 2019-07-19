:- module(type_support,
	[ closed_var_list/2,
          var_list/2,
	  ins_without_dup/2,
	  replace_var_by_term/4,
	  vset_diff/3,
          find_list_entry/3
	], []).

:- use_module(library(idlists), [member_0/2]).

%
% Creates a (closed) list with the set of variables of a term.
%

closed_var_list(X, OVarSet):-
    var_list_0(X, [], OVarSet).

var_list_0(X, IVarSet, OVarSet):-
     var(X),
     !,
     add_variable_not_duplicates(X, IVarSet, OVarSet).
var_list_0([], IVarSet, IVarSet):- 
     !.
var_list_0([X|Xs], IVarSet, OVarSet):- 
     !,
     var_list_0(X, IVarSet, TeVarSet),          
     var_list_0(Xs, TeVarSet, OVarSet).
var_list_0(X, IVarSet, OVarSet):-
     X=..[_|Args],
     var_list_0(Args, IVarSet, OVarSet).

add_variable_not_duplicates(Var, List, OuList):-
      % member_term(Var, List) % PLG May-17-2003 
      member_0(Var, List) 
       -> OuList = List 
        ; OuList = [Var|List].

%
% Creates an open list with the set of variables of a term.
%

var_list(X,VarSet):-
     var(X),!,
     ins_without_dup(VarSet,X).
var_list([],_):- !.

var_list([X|Xs],VarSet):- !,
     var_list(X,VarSet),          
     var_list(Xs,VarSet).
var_list(X,VarSet):-
     X=..[_|Args],
     var_list(Args,VarSet).


%
% Insert an item in a list if it isn't in yet.
%

ins_without_dup(L,I) :- 
	var(L), !,
	L = [I|_].
ins_without_dup(L,I) :- 
	nonvar(L),
	L = [Item|_],
	Item==I, !.
ins_without_dup(L,I) :- 
	nonvar(L),
	L = [Item|List],
	I \== Item,
	ins_without_dup(List,I).

% vset_diff(+L1, +L2, -L3) binds L3 to the set difference of L1 and L2,
% i.e., to the set of objects in L1 that are not in L2.

vset_diff(L1, L2, L3) :- vset_diff_4(L1, L2, [], L3).

vset_diff_4([X|L1], L2, L3in, L3out) :-
   (member_0(X, L2) ->
      L3mid = L3in ;
      L3mid = [X|L3in]
   ),
   vset_diff_4(L1, L2, L3mid, L3out).
vset_diff_4([], _, L, L).

%------------------------------------------------------------------------%
% Get a type term from a term and a typing of its variables

replace_var_by_term(InTerm, ReplaceVar, ByTerm, ByTerm):-
    InTerm == ReplaceVar, !.
replace_var_by_term(InTerm, ReplaceVar, _ByTerm, InTerm):-
    var(InTerm), InTerm \== ReplaceVar, !.
replace_var_by_term(InTerm, ReplaceVar, ByTerm, OuTerm):-
    nonvar(InTerm),  InTerm \== ReplaceVar, !,
    functor(InTerm, F, A),
    functor(OuTerm, F, A),
    arg_replace_var_by_term(A, InTerm, ReplaceVar, ByTerm, OuTerm).

arg_replace_var_by_term(0, _InTerm, _ReplaceVar, _ByTerm, _OuTerm):-!.
arg_replace_var_by_term(Arg_Num, InTerm, ReplaceVar, ByTerm, OuTerm):-
      Arg_Num > 0,
      NArg_Num is Arg_Num - 1,
      arg(Arg_Num, InTerm, InArg),
      arg(Arg_Num, OuTerm, OuArg),
      replace_var_by_term(InArg, ReplaceVar, ByTerm, OuArg),
      arg_replace_var_by_term(NArg_Num, InTerm, ReplaceVar, ByTerm, OuTerm).

% 

find_list_entry(VT, _, _) :- 
	var(VT), !.
find_list_entry(VT, Var, Entry) :- 
	nonvar(VT),
	VT = [E|_],
	E = vt(EVar, _),
        EVar == Var, !,
        Entry = E.
find_list_entry(VT, Var, Entry) :- 
	nonvar(VT),
	VT = [E|S],
        E = vt(EVar, _),
	EVar \== Var,
	find_list_entry(S, Var, Entry).
