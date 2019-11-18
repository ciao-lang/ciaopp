:- module(unfold_times,
    [init_unfold_times/0,
     ask_unfold_times/1,
     increment_unfold_time/1,
     increment_local_control_time/1,
     increment_global_control_time/1,
     global_time_ellapsed/3
     ],
     [assertions, datafacts]).

:- doc(title,"Accurate Timing of Partial Evaluation").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains a series of predicates for 
    measuring the time actually taken by both local control (unfolding) 
    and global control.").

:- use_module(ciaopp(preprocess_flags)).

:- data unfold_time/1.

:- data local_control_time/1.

:- data global_control_time/1.

init_unfold_times:-
    retractall_fact(unfold_time(_)),
    retractall_fact(local_control_time(_)),
    retractall_fact(global_control_time(_)).

:- pred ask_unfold_times(Info) : var(Info) => ground(Info) # "When
     partially evaluating a program, a series of specialized
     definitions are computed. This predicate returns the time spent
     in global control, in unfolding during the generation of the
     specialized definitions (unfold) and the total time used in local
     control which also includes, in addition to unfolding, putting in
     the right format and asserting the specialized definitions. Note
     that unfolding time is already included in local_control
     time. Thus, partial evaluation time is the addition of local and
     global control (plus some extra time at the analysis level).".

    
ask_unfold_times(Info):-
    current_pp_flag(local_control,LC),
    LC == off,!,
    Info = [].
ask_unfold_times([(global_control,G),(local_control,T),(unfold,U)]):-
    current_fact(global_control_time(G)),
    current_fact(local_control_time(T)),
    current_fact(unfold_time(U)),!.
ask_unfold_times([]).


increment_unfold_time(T_u):-
    unfold_time(Time),!,
    NTime is Time + T_u,
    retractall_fact(unfold_time(_)),
    asserta_fact(unfold_time(NTime)).
increment_unfold_time(T_u):-
    asserta_fact(unfold_time(T_u)).

increment_local_control_time(T_T):-
    local_control_time(Time),!,
    NTime is Time + T_T,
    retractall_fact(local_control_time(_)),
    asserta_fact(local_control_time(NTime)).
increment_local_control_time(T_T):-
    asserta_fact(local_control_time(T_T)).

increment_global_control_time(T_T):-
    global_control_time(Time),!,
    NTime is Time + T_T,
    retractall_fact(global_control_time(_)),
    asserta_fact(global_control_time(NTime)).
increment_global_control_time(T_T):-
    asserta_fact(global_control_time(T_T)).


global_time_ellapsed(GT_After,GT_Before,TE):-
    TE is round(1000*(GT_After - GT_Before))/1000.
