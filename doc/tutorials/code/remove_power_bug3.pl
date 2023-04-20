:- module(_,[remove_power/3],[assertions]).

remove_power([],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\= power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).