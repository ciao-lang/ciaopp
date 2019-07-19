:- module(mem_usage,
	[ reset_mem_usage/0,
	  reset_mem_usage_no_gc/0,
	  update_mem_usage/0,
	  readjust_max_mem_usage/0,
	  report_mem_usage/0,
	  ask_mem_usage/2,
	  ask_mem_usage_no_gc/2
	],
	[assertions, datafacts]).

:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains some predicates for polling
     memory usage and show the maximum amount of memory used, together with
     a breakdown into different categories.").

:- use_module(library(lists), [member/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(library(messages)).
:- use_module(engine(runtime_control), [push_prolog_flag/2, pop_prolog_flag/1]).

:- trust success mem_usage(A,B,C) => (ground(A), ground(B), ground(C)).

:- data mem_usage/3.

:- pred reset_mem_usage # "This predicate is used to fix the base-line for 
     memory consumption.  Memory usage is considered to be the current 
     memory usage minus this base-line. A simple memory measurement scheme 
     consists in one call to @pred{reset_mem_usage/0} followed by a series 
     of calls to @pred{update_mem_usage/0} finalyzed by one call to either 
     @pred{ask_memory_usage/2} or @pred{report_mem_usage/0}.".  

reset_mem_usage:-
	retractall_fact(mem_usage(_,_,_)),
	read_memory_usage(Total,P,G,L,T,C),
	Details = [(program,P,P),(global_stack,G,G),
	           (local_stack,L,L),(trail,T,T),(choice,C,C)],
	asserta_fact(mem_usage(Total,0,Details)).

:- pred reset_mem_usage_no_gc # "Same as @tt{reset_mem_usage}, but
      additionally, temporarily sets garbage collection to off.".

reset_mem_usage_no_gc:-
	push_prolog_flag(gc,off),
	reset_mem_usage.

:- pred update_mem_usage # "This predicate should be called at intervals to 
     check whether the current memory being used exceeds the temporary ceiling 
     for memory consumption. In such case we replace the temporary ceiling.".

update_mem_usage:-
	read_memory_usage(Total,P,G,L,T,C),
	mem_usage(Old_mem,Inc,Old_Details),
	(Old_mem >= Total ->
	    true
	;
	    retract_fact(mem_usage(_,_,_)),
	    Delta is Total-Old_mem+Inc,
	    Old_Details = [(program,_P,P0),(global_stack,_G,G0),
	             (local_stack,_L,L0),(trail,_T,T0),(choice,_C,C0)],
	    Details = [(program,P,P0),(global_stack,G,G0),
	             (local_stack,L,L0),(trail,T,T0),(choice,C,C0)],
	    asserta_fact(mem_usage(Total,Delta,Details))
	).


:- pred report_mem_usage # "Prints out a series of messages informing
     about the ceiling reached up to the present moment for memory
     consumption.".

report_mem_usage:-
	mem_usage(_Total,Delta,Details),
        simple_message("Total memory ~0f",[Delta]),
	member((program,P,P0),Details),
	P_used is P - P0,
        simple_message("Program memory ~0f",[P_used]),
	member((global_stack,G,G0),Details),
	G_used is G - G0,
        simple_message("Term Heap ~0f",[G_used]),
	member((local_stack,L,L0),Details),
	L_used is L - L0,
        simple_message("Stack ~0f",[L_used]),
	member((trail,T,T0),Details),
	T_used is T - T0,
        simple_message("Trail ~0f",[T_used]),
	member((choice,C,C0),Details),
	C_used is C - C0,
        simple_message("Choice-points ~0f",[C_used]).


:- pred ask_mem_usage(-Delta,-Details) # "Returns in @var{Delta} 
      the total memory used in bytes and in @var{Details} such 
      memory usage is split into the standard categories.".

ask_mem_usage(Delta,Details):-
	mem_usage(_Total,Delta,Details).

:- pred ask_mem_usage_no_gc(-Delta,-Details) # "Same as
      @tt{ask_mem_usage(Delta,Details)}, but additionally, resets the
      behaviour of garbage collection to that prior to measuring
      memory consumption.".

ask_mem_usage_no_gc(Delta,Details):-
	mem_usage(_Total,Delta,Details),
	pop_prolog_flag(gc).

read_memory_usage(Total,P,G,L,T,C):-
        pp_statistics(program,[P,_]),
        pp_statistics(global_stack,[G,_]),
        pp_statistics(local_stack,[L,_]),
        pp_statistics(trail,[T,_]),
        pp_statistics(choice,[C,_]),
        Total is P+G+L+T+C.

:- pred readjust_max_mem_usage # "Allows measuring memory consumption of 
        a subprogram by readjusting the maximal memory used by now to that 
	being used when entering the subprogram. This allows modifying the 
	base-line to the memory used at the entry to the subprogram.".

readjust_max_mem_usage:-
	read_memory_usage(Total,_P,_G,_L,_T,_C),
	mem_usage(_OldMax,Delta,Details),
	retractall_fact(mem_usage(_OldMax,Delta,Details)),
	NewMax is Total + Delta,
	asserta_fact(mem_usage(NewMax,Delta,Details)).	
