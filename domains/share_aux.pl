:- module(share_aux, [], [assertions, modes_extra]).

% (auxiliary definitions for sharing and other domains)

:- use_module(library(sets), 
    [ merge/3,
      ord_intersection/3,
      ord_member/2
    ]).
:- use_module(library(lsets), [ord_split_lists_from_list/4]).

:- pred eliminate_couples(+Sh,+Xs,+Ys,-NewSh) 
   #
"Eliminates from `Sh` all `SS` s.t. both `X`,`Y`\in `SS` for some `X`\in `Xs`,`Y`\in `Ys`. 
All arguments ordered.                                                  
".

:- export(eliminate_couples/4).
eliminate_couples([],_,_,[]):- !.
eliminate_couples(Sh,Xs,Ys,NewSh) :-
    ord_split_lists_from_list(Xs,Sh,Intersect,Disjunct1),
    ord_split_lists_from_list(Ys,Intersect,_,Disjunct2),
    merge(Disjunct2,Disjunct1,NewSh).

:- pred eliminate_if_not_possible(+ASub,+Vars,-More)
   #
"It gives in the third argument each set `S` in the first argument which 
has variables in common with Vars but `Vars` is not a subset of `S`.
".

:- export(eliminate_if_not_possible/3).
eliminate_if_not_possible([],_,X-X).
eliminate_if_not_possible([Z|Rest],Vars,More):-
    ord_intersection(Vars,Z,Term),
    test_temp(Term,Vars), !,
    eliminate_if_not_possible(Rest,Vars,More).
eliminate_if_not_possible([Z|Rest],Vars,[Z|More]-More2):-
    eliminate_if_not_possible(Rest,Vars,More-More2).

:- export(test_temp/2).
test_temp([],_).
test_temp([X|Xs],List):-
    [X|Xs] == List.

:- pred eliminate_if_not_possible(+ASub,+X,+Vars,-More)
   #
"It gives as a diff list each set `S` in ASub s.t. either `X` appears in `S`
and no element of Vars appears in `S` or 
`X` does not appear but at least one element in `Vars` appears.
".

:- export(eliminate_if_not_possible/4). 
eliminate_if_not_possible([],_,_,X-X).
eliminate_if_not_possible([Z|Rest],X,Vars,More):-
    ord_intersection(Vars,Z,V), !,
    test_set(V,X,Z,Rest,Vars,More).
eliminate_if_not_possible([Z|Rest],X,Vars,More):-
    ord_member(X,Z), !,
    eliminate_if_not_possible(Rest,X,Vars,More).
eliminate_if_not_possible([Z|Rest],X,Vars,[Z|More]-More1):-
    eliminate_if_not_possible(Rest,X,Vars,More-More1).

test_set([],X,Z,Rest,Vars,More):-
    ord_member(X,Z),!,
    More = [Z|Rest1]-Rest2,
    eliminate_if_not_possible(Rest,X,Vars,Rest1-Rest2).
test_set([],X,_,Rest,Vars,More):- !,
    eliminate_if_not_possible(Rest,X,Vars,More).
test_set([_|_],X,Z,Rest,Vars,More):-
    ord_member(X,Z),!,
    eliminate_if_not_possible(Rest,X,Vars,More).
test_set([_|_],X,Z,Rest,Vars,More):- !,
    More = [Z|Rest1]-Rest2,
    eliminate_if_not_possible(Rest,X,Vars,Rest1-Rest2).

%------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [success_builtin/7]).

:- export(handle_each_indep/4).
handle_each_indep([],_AbsInt,Call,Call).
handle_each_indep([[X,Y]|Rest],AbsInt,Call,Succ):-
    success_builtin(AbsInt,'indep/2',[X,Y],p(X,Y),_HvFv_u,Call,Succ1), !, % TODO: _HvFv_u unbound! (JF)
    handle_each_indep(Rest,AbsInt,Succ1,Succ).

%------------------------------------------------------------------------

:- export(has_give_intersection/8).
has_give_intersection(=,X,Xs,_Y,Ys,yes,[X|Inter],[X|Xs]):-
    ord_intersection(Xs,Ys,Inter).
has_give_intersection(<,_X,[],_Y,_Ys,Flag,_Inter,_NewVars):- !,
    Flag = end.
has_give_intersection(<,_,[X|Xs],Y,Ys,Flag,Inter,NewVars):-
    compare(D,X,Y),
    has_give_intersection(D,X,Xs,Y,Ys,Flag,Inter,NewVars).
has_give_intersection(>,X,Xs,_Y,[],Flag,_Inter,NewVars):- !,
    NewVars = [X|Xs],
    Flag = no.
has_give_intersection(>,X,Xs,_,[Y|Ys],Flag,Inter,NewVars):- 
    NewVars = [X|Xs],
    compare(D,X,Y),
    has_give_intersection_next(D,X,Xs,Y,Ys,Flag,Inter).

has_give_intersection_next(=,X,Xs,_Y,Ys,yes,[X|Inter]):-
    ord_intersection(Xs,Ys,Inter).
has_give_intersection_next(<,_X,[],_Y,_Ys,Flag,_Inter):- !,
    Flag = no.
has_give_intersection_next(<,_,[X|Xs],Y,Ys,Flag,Inter):-
    compare(D,X,Y),
    has_give_intersection_next(D,X,Xs,Y,Ys,Flag,Inter).
has_give_intersection_next(>,_X,_Xs,_Y,[],Flag,_Inter):- !,
    Flag = no.
has_give_intersection_next(>,X,Xs,_,[Y|Ys],Flag,Inter):-
    compare(D,X,Y),
    has_give_intersection_next(D,X,Xs,Y,Ys,Flag,Inter).

%------------------------------------------------------------------------%

:- export(list_ground/2).
list_ground([],[]).
list_ground([X|Xs],[X/g|Rest]):-
    list_ground(Xs,Rest).

%------------------------------------------------------------------------%

:- export(append_dl/3).
append_dl(X-Y,Y-Z,X-Z).

% dl_to_l(X-[],X).

:- export(if_not_nil/4).
if_not_nil([],_,Xs,Xs):- !.
if_not_nil(_,X,[X|Xs],Xs).
