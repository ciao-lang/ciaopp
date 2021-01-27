:- module(_,[
    modules_analyzed/1,
    % priority queue
    reset_queue/0,
    push/2,
    pop/2
],[assertions, isomodes, nativeprops, datafacts]).

:- include(intermod_options). % intermod compilation options

% ------------------------------------------------------------
:- doc(title, "Intermodular analysis scheduler").
% ------------------------------------------------------------

:- doc(module, "This module implements different intermodular scheduling
policies. This affects the order in which modular iteration is performed.").

:- use_module(ciaopp(plai/intermod_db)).
:- use_module(ciaopp(plai/intermod_punit)).

:- use_module(library(lists), [reverse/2, select/3]).
:- use_module(library(sets), [insert/3]).

%%------------------------------------------------------------------
:- export(naive_pending_modules/1).
:- data naive_pending_modules/1.
% Modules for which the analysis must be forced, even if they
% have their registry entries up-to-date.
:- export(force_analysis/1).
:- data force_analysis/1.

:- export(cleanup_intermod_scheduling/0).
cleanup_intermod_scheduling :-
    set_fact(queue([])),
    retractall_fact(module_processed(_,_)).

:- data modules_analyzed/1.
modules_analyzed([]).

:- export(naive_module_order/1).
% TODO: rename. Stores the modules to be analyzed and the order. Note that this
% order is static, it is precomputed before modular analysis and never modified
%% IG: exported check if a module will be analyzed before loading its registry
:- data naive_module_order/1.

% number of (groups of) modules analyzed during the intermodular analysis.
% Number of calls to the analyzer.
:- export(iterations/1).
:- data iterations/1.

:- pred queue(QueueList) => list
   # "Data predicate to store (in a single fact) the priority queue.
   @list{QueueList} must be the list of @tt{priority-module} pairs in reverse
   order.".
:- data queue/1.
queue([]).

:- export(module_processed/2).
:- pred module_processed(Module,AlreadyProcessed)
   # "Lists the modules in the program unit and whether they are already
   processed or not.".
:- data module_processed/2.

%%------------------------------------------------------------------
:- export(setup_scheduling/4).
:- pred setup_scheduling(SchedPolicy,Domains,TopLevel,ModList)
# "This predicate sets up some stuff in specific global scheduling
 policies. Implemented policies are as follows:

@begin{itemize}

@item @tt{abs_depth_first} Starting from the modules which require
    analysis (those in @var{ModList}, it uses the depth in the
    intermodule dependency graph as priority, and analyzes the
    modules with higher priority first.

@item @tt{naive_top_down} Traverses the list of modules in the
    intermodule graph in top-down order, and analyzes the modules
    which have pending patterns.  Initially, the modules with
    pending patterns are the ones in @var{ModList}.  It stops when
    in a module traversal there is no module with pending
    patterns.

@item @tt{naive_bottom_up} The same as @tt{naive_top_down}, but the
    list of modules is in reverse top-down order.

@item @tt{top_down_preanalysis} The same as @tt{naive_top_down}, but
    initially all modules are scheduled for analysis. This
    scheduling policy is intended for using an entry policy
    different of @tt{main_module} (for example, @tt{all}).

@item @tt{bottom_up_preanalysis} The same as
    @tt{top_down_preanalysis}, but a bottom-up traversal of the
    intermodule graph is made.
@end{itemize}
".
setup_scheduling(abs_depth_first,_Analyses,TopLevel,ModList):-
    clean_scheduling_common,
    push_modules_priorities(ModList),
    retractall_fact(module_depth(_,_)),
    get_all_module_cycles(TopLevel,CycleList),
    gen_module_depths(CycleList,_).
setup_scheduling(naive_top_down,_Analyses,TopLevel,ModList):-
    clean_scheduling_order,
    get_all_module_cycles(TopLevel,CycleList),
    reverse(CycleList,RevCycleList),
    assert_in_order(RevCycleList),
    add_naive_pending_modules_(ModList).
setup_scheduling(naive_bottom_up,_Analyses,TopLevel,ModList):-
    clean_scheduling_order,
    get_all_module_cycles(TopLevel,CycleList),
    assert_in_order(CycleList),
    add_naive_pending_modules_(ModList).
setup_scheduling(top_down_preanalysis,_Analyses,TopLevel,_ModList):-
    clean_scheduling_order,
    get_all_module_cycles(TopLevel,CycleList),
    reverse(CycleList,RevCycleList),
    assert_in_order(RevCycleList),
    add_pending_modules_preanalysis(RevCycleList).
setup_scheduling(bottom_up_preanalysis,_Analyses,TopLevel,_ModList):-
    clean_scheduling_order,
    get_all_module_cycles(TopLevel,CycleList),
    assert_in_order(CycleList),
    add_pending_modules_preanalysis(CycleList).
setup_scheduling(_Sched,_Analyses,_TopLevel,ModList):-
    clean_scheduling_common,
    push_modules_priorities(ModList).

clean_scheduling_order :-
    retractall_fact(naive_module_order(_)),
    retractall_fact(naive_pending_modules(_)),
    clean_scheduling_common.

clean_scheduling_common :-
    retractall_fact(force_analysis(_)),
    retractall_fact(iterations(_)).

gen_module_depths([MList],1):-
    gen_module_depths_(MList,1).
gen_module_depths([MList|MLists],N):-
    gen_module_depths(MLists,N1),
    N is N1+1,
    gen_module_depths_(MList,N).

gen_module_depths_([],_).
gen_module_depths_([M|Ms],N):-
    asserta_fact(module_depth(M,N)),
    gen_module_depths_(Ms,N).

assert_in_order([]):- !.
assert_in_order([Elem|List]):-
    assert_in_order(Elem),
    assert_in_order(List).
assert_in_order(Base):-
    atom(Base),
    assertz_fact(naive_module_order(Base)).

:- export(is_naive_scheduling/1).
is_naive_scheduling(naive_top_down).
is_naive_scheduling(naive_bottom_up).
is_naive_scheduling(top_down_preanalysis).
is_naive_scheduling(bottom_up_preanalysis).

push_modules_priorities([]).
push_modules_priorities([(M,D,F)|ModList]):-
    push(M,D),
    ( F = force -> asserta_fact(force_analysis(M)) ; true ),
    push_modules_priorities(ModList).

%% Adds the modules in the list to naive_pending_modules/1, and
%% sets force analysis of the ones which need it.
:- export(add_naive_pending_modules/1).
:- pred add_naive_pending_modules/1 : list + not_fails.
add_naive_pending_modules_([]).
add_naive_pending_modules_([(M,_,F)|ModList]):-
    add_naive_pending_modules([M]),
    ( F = force -> asserta_fact(force_analysis(M)) ; true ),
    add_naive_pending_modules_(ModList).

add_naive_pending_modules([]).
add_naive_pending_modules([M|Ms]):-
    ( current_fact(naive_pending_modules(M)) -> true
    ;   asserta_fact(naive_pending_modules(M))
    ),
    add_naive_pending_modules(Ms).

add_pending_modules_preanalysis([]):- !.
add_pending_modules_preanalysis([X|Xs]):-
    add_pending_modules_preanalysis(X),
    add_pending_modules_preanalysis(Xs).
add_pending_modules_preanalysis(M):-
    atom(M),
    add_naive_pending_modules([M]).

%% ******************************************************************
:- doc(section, "Priority Queue handling predicates").
%% ******************************************************************
:- pred reset_queue # "Empties the queue.".
reset_queue:-
    set_fact(queue([])).

:- pred pop(-Element,-Priority) => (atm(Element), int(Priority))
   # "Pops the element @var{Element} with highest priority from the priority
   queue.".
pop(Element,Priority):-
    retract_fact(queue([Pty-Element|Rest])),
    Priority is Pty * (-1),
    set_fact(queue(Rest)).

:- pred push(+Element,+Priority) : (atm(Element), int(Priority))
   # "Pushes a new element @var{Element} with priority @var{Priority} into the
   priority queue. If @var{Element} is already in the queue, it is not
   duplicated, but its priority is changed to the maximum prioriy of the already
   existing element and the priority of the new element.".
:- pred push(+ElementList,+Priority) : list(atm) * integer
   # "Pushes a set of new elements @var{ElementList} with priority
   @var{Priority} into the priority queue. If any element of @var{ElementList}
   is already in the queue, it is not duplicated, but its priority is changed to
   the maximum prioriy of the already existing element and the priority of the
   new element.".
push([],_):- !.
push([Element|Rest],[Pty|Ptys]):-
    push(Element,Pty),
    push(Rest,Ptys),!.
push([Element|Rest],Priority):-
    integer(Priority),
    push(Element,Priority),
    push(Rest,Priority),
    !.
% no integer priority means nothing.
push(_,Priority):-
    \+ integer(Priority).
push(Element,Priority):-
    integer(Priority),!,
    Pty is Priority * (-1),
    current_fact(queue(Queue)),
    ( select(Pty0-Element,Queue,Queue0) ->
      ( Pty0 =< Pty ->
        true
      ; insert(Queue0,Pty-Element,NewQueue),
        set_fact(queue(NewQueue))
      )
    ; insert(Queue,Pty-Element,NewQueue),
      set_fact(queue(NewQueue))
    ).
% no integer priority means nothing.
push(_,_Priority).
