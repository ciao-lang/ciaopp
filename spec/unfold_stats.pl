:- module(unfold_stats,
    [ reset_unfold_stats/0,
      inc_derivation_steps/1,
      inc_unfold_evals/1,
      ask_unfold_stats/1
    ],
    [assertions, isomodes, datafacts]).

:- doc(author, "Claudio Ochoa").
:- doc(module,"This module contains some predicates for updating
     statistics related to unfolding, such as unfolding steps
     performed, evaluations, etc. A simple unfolding statistics scheme
     consists in one call to @pred{reset_unfold_stats/0} followed by a
     series of calls to @pred{inc_derivation_steps/1} or
     @pred{inc_unfold_evals/1} finalyzed by one call to
     @pred{ask_unfold_stats/1}.").

:- trust success derivation_steps(A) => ground(A).

:- data derivation_steps/1.

:- trust success evaluations(A) => ground(A).

:- data evaluations/1.

:- pred reset_unfold_stats # "This predicate is used to reset the
    statistics collected by this module".

reset_unfold_stats:-
    retractall_fact(derivation_steps(_)),
    retractall_fact(evaluations(_)).

:- pred inc_derivation_steps(+Steps) # "This predicate should be
    called every time a derivation step is performed, indicating
    the number @var{Steps} of derivation steps to be incremented".

inc_derivation_steps(D):-       
    derivation_steps(S),
    D >= 0,!,
    S1 is S + D,
    retractall_fact(derivation_steps(_)),
    asserta_fact(derivation_steps(S1)).
inc_derivation_steps(D):-
    D >= 0,!,
    asserta_fact(derivation_steps(D)).      

:- pred inc_unfold_evals(+Evals) # "This predicate should be called
    every time an evaluation is performed during unfolding,
    indicating the number @var{Evals} of evaluations to be
    incremented".

inc_unfold_evals(N):-
    evaluations(E),
    N >= 0,!,
    E1 is E + N,
    retractall_fact(evaluations(_)),
    asserta_fact(evaluations(E1)).
inc_unfold_evals(N):-
    N >= 0,!,
    asserta_fact(evaluations(N)).   

:- pred ask_unfold_stats(-Stats) # "Returns in list @var{Stats} the
    statistics collected in this module".

ask_unfold_stats([derivation_steps(U),evaluations(E)]):-
    (derivation_steps(U) -> true; U=0),
    (evaluations(E) -> true; E=0),!.  
