
:- data(pgm_type_name/3). %% User programs type names.
:- data(lib_type_name/3). %% Library type names.
:- data(typ_name_counter/1).
:- data(lib_typ_name_counter/1).
:- data(pgm_equiv_name/2).
:- data(lib_equiv_name/2).

type_name(Name, List, Count):-
	pgm_type_name(Name, List, Count).
type_name(Name, List, Count):-
	lib_type_name(Name, List, Count).

equiv_name(A,B):-
	pgm_equiv_name(A,B).
equiv_name(A,B):-
	lib_equiv_name(A,B).


init_typ_name_counter:-
%%	asserta_fact(typ_name_counter(0)).
	lib_typ_name_counter(Count),!,
	set_fact(typ_name_counter(Count)).
init_typ_name_counter:-
	asserta_fact(typ_name_counter(0)).

current_type_name_counter_value(Count):-
   typ_name_counter(Count), !.
current_type_name_counter_value(Count):-
   init_typ_name_counter,
   typ_name_counter(Count).

new_type_name(NewTyp):-
    current_type_name_counter_value(N),
    !,
    retractall_fact(typ_name_counter(_)),
    N1 is N + 1, 
    asserta_fact(typ_name_counter(N1)),
    name(N, NName),
    append("name", NName, TypName),
    name(NewTyp, TypName).


undoall_type_names:-
	retractall_fact(pgm_type_name(_,_,_)),
	retractall_fact(typ_name_counter(_)),
	retractall_fact(pgm_equiv_name(_,_)).

insert_type_name(Name,List,Count):-
	asserta_fact(pgm_type_name(Name,List,Count)).

retract_type_name(Name,List,Count):-
	retract_fact(pgm_type_name(Name,List,Count)).
% retract_type_name(Name,_,_):-
% 	nonvar(Name),
% 	display(user,'FFFFFFFFFFFFFFFFFFailllllllllllllllll'),display(user,Name),nl(user),fail.

get_type_name(Name,List):- 
	type_name(Name,List,_).
% get_type_name(Name,_):- 
% 	nonvar(Name),
% 	display(user,'FFFFFFFFFFFFFFFFFFailllllllllllllllll'),display(user,Name),nl(user),fail.



insert_equiv_name(Name,Canonical):-
	asserta_fact(pgm_equiv_name(Name,Canonical)).

retract_equiv_name(Name,Canonical):-
	retract_fact(pgm_equiv_name(Name,Canonical)).

get_equiv_name(Name,Canonical):- 
	equiv_name(Name,Canonical).



get_equiv_names(Names):-
	findall(equiv_name(X,Y), equiv_name(X,Y), Names).

get_type_names(Names):-
	findall(type_name(X,Y,Z), type_name(X,Y,Z), Names).
