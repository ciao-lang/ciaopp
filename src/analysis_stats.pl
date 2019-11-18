:- module(analysis_stats, [], [assertions, isomodes, regtypes, hiord, datafacts]).

% "High-level" performance counters

:- doc(title, "Analysis statistics library").

:- doc(author, "Isabel Garcia-Contreras").

:- use_module(library(lists), [member/2]).
:- use_module(library(format), [format/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(engine(runtime_control), [statistics/2]).
:- use_module(engine(stream_basic)).
:- use_module(library(write), [portray_clause/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- doc(module, "This module is a database for statistics gathered
during modular and incremental analysis.").

:- export(clean_stats/1).
:- pred clean_stats(What) #"Removes all stored stats with identifier @var{What}.".
clean_stats(What) :-
    retractall_fact(stat_runtime(What, _)).

% TODO: copied from find.pl
:- export(stat/2).
:- meta_predicate stat(+, goal).
:- pred stat(What, Goal) #"Runs @var{Goal} and stores the time that it took.".
stat(What, Goal) :-
    stat_no_store(Goal, Time),
    retractall_fact(stat_runtime(What, _)),
    assertz_fact(stat_runtime(What, Time)).

:- export(stat_no_store/2).
:- meta_predicate stat_no_store(goal, -).
stat_no_store(Goal, Time) :-
    pp_statistics(runtime, [T0, _]),
    Goal,
    pp_statistics(runtime,[T, _]),
    Time is T - T0.

:- export(add_stat/2).
:- data stat_runtime/2.
:- pred add_stat(What, Stat) #"Adds a statistic (@var{Stat}) with
identifier @var{What} to the database.".
add_stat(What, Stat) :-
    assertz_fact(stat_runtime(What, Stat)).

%% TODO: set point times (so that it is not needed to create a
%% specific predicate in order to calculate the time)

:- export(gather_stats/2).
:- pred gather_stats(+Operation, -Stats) #"Gathers the stats associated
with a phase of analysis of ciaopp.".
gather_stats(Operation, Stats) :-
    findall(S, operation_stat(Operation, S), Stats).

:- export(pretty_print_stats/1).
:- pred pretty_print_stats(Stats) : list.
pretty_print_stats(Stats) :-
    ( % failure-driven loop
      member(S,Stats),
        S =.. [SName,Time],
        format('~w ~t ~3f msec.~n', [SName,Time]),
        fail
    ; format('~n', [])
    ).

:- pred operation_stat(+Operation, -Stat).
operation_stat(Operation, Stat) :-
    ciaopp_operation_stat(Operation, StatName),
    get_stored_stat_nofail(StatName, Value),
    Stat =.. [StatName, Value]. % TODO: slow

get_stored_stat_nofail(Stat, Value) :-
    retract_fact(stat_runtime(Stat, Value)), !.
get_stored_stat_nofail(_, 0).

:- export(get_stat/2).
:- pred get_stat(Stats, X) : list(Stats) #"Given a statistics
    structure (currently implemented a as list), gets the value of
    a specific statistic contained in the set).".
get_stat(Stats, X) :-
    member(X, Stats), !.

:- regtype ciaopp_operation_stat/2.
% TODO: multifile predicate??
% MODULE STATISTICS
ciaopp_operation_stat(module, comp_diff).
ciaopp_operation_stat(module, restore).

% ANALYSIS STATISTICS
ciaopp_operation_stat(analysis, proc_diff).
ciaopp_operation_stat(analysis, proc_assrts).
ciaopp_operation_stat(analysis, td_add).
ciaopp_operation_stat(analysis, update_ana).
ciaopp_operation_stat(analysis, upd_lat).
ciaopp_operation_stat(analysis, fixp).
ciaopp_operation_stat(analysis, preproc).
ciaopp_operation_stat(analysis, upd_clauses).
ciaopp_operation_stat(analysis, itmem).
ciaopp_operation_stat(analysis, td_delete) :-
    current_pp_flag(del_strategy, top_down), !.
ciaopp_operation_stat(analysis, bu_delete).

%% test stats here

% summarize type of stats that are being used
:- regtype ciaopp_stat/2.
ciaopp_stat(time, prep). % analysis stats
ciaopp_stat(time, ana).
% intermod specific stats
ciaopp_stat(time, genreg).
% incanal specific stats
ciaopp_stat(time, comp_diff). % diff computation time
ciaopp_stat(time, proc_diff). % differences to analysis database addition time
ciaopp_stat(time, proc_assrts). % incremental assrtion processing time
ciaopp_stat(time, add).       % addition of clauses time
ciaopp_stat(time, delete).    % deletion of clauses time

%% T = [time(5.945,[(prep,0.854),(ana,5.091)]),memory(0,[(program,30473864,30473864),(global_stack,32656,32656),(local_stack,1184,1184),(trail,2296,2296),(choice,1400,1400)])] ?

% step(N, Mod, Load, Ana, GenReg, Memory).
:- data step/7.
:- data step_cont/1.

next_step(C) :-
    retract_fact(step_cont(X)), !,
    C is X + 1,
    assertz_fact(step_cont(C)).
next_step(0) :-
    assertz_fact(step_cont(0)).

:- export(add_stat_step/1).
:- pred add_stat_step(Mod) #"Collects all the stats generated during a
modular analysis, i.e., the stats generated in each of the iterations
that it requires.".
add_stat_step(Mod) :-
    retract_fact(stat_runtime(load, Load)),
    retract_fact(stat_runtime(genreg, GenReg)),
    retract_fact(stat_runtime(savereg, SaveReg)),
    retract_fact(stat_runtime(ana, Ana)),
    ( retract_fact(stat_runtime(itmem, Mem)) ->
        true
    ;
        Mem = memory(0, [(_,0,0)])
    ),
    next_step(C),
    assertz_fact(step(C, Mod, Load, Ana, GenReg, SaveReg, Mem)).

:- export(dump_steps/1).
:- pred dump_steps(File) #"Writes in a file (with terms) the steps
generated by add_stat_step.".
dump_steps(File) :-
    open(File, write, S),
    ( % failure-driven loop
      step(A, B, C, D, E, F, G),
        portray_clause(S, step(A, B, C, D, E, F, G)),
        fail
    ;   true
    ),
    close(S).

:- export(clean_stat_steps/0).
:- doc(clean_stat_steps/0, "Cleans the steps of the database.").
clean_stat_steps :-
    retractall_fact(step(_,_,_,_,_,_,_)),
    retractall_fact(step_cont(_)).

modular_stat_ana_format(Stats, ModStats) :-
    get_stat(Stats, proc_diff(DiffT)),
  get_stat(Stats, proc_assrts(DiffA)),
  Diff is DiffT + DiffA,
    ModStats = [time(TotalT,[(prep(Diff), ana(AnaT))])],
    ( get_stat(Stats, add(AddT)) -> true
    ; AddT = 0
    ),
    ( get_stat(Stats, delete(DelT)) -> true
    ; DelT = 0
    ),
    AnaT is AddT + DelT,
    TotalT is Diff + AnaT.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(section, "Statistics handling from intermod").
% moved from intermod.pl
%% Cumulative information for modular analyses. In this predicate
%% are grouped all the results returned by the successive calls to
%% analyze/2.

:- use_module(library(sort), [sort/2]).

:- data total_info/1.

:- export(reset_total_info/0).
reset_total_info :-
    set_fact(total_info([])).

:- export(set_total_info/1).
set_total_info(Info) :-
    set_fact(total_info(Info)).

%% Adds information to total_info/1.
%% - Time information is added;
%% - The maximum of the memory information is stored;
%% - assertion information is appended.
:- export(add_to_total_info/1).
add_to_total_info(Info):-
    current_fact(total_info(TotalInfo)),
    add_to_info(Info,TotalInfo,TotalInfo1),
    set_total_info(TotalInfo1),
    !.

:- export(add_to_info/3).
:- pred add_to_info(+Info,+PrevInfo,-TotalInfo) #"Adds @var{Info} to previously
    accumulated statistics (@var{PrevInfo}) to prouce @var{TotalInfo}.".
add_to_info([],TotalInfo,TotalInfo).
add_to_info([Elem|Info],TotalInfo,TotalInfo2):-
    add_to_info_2(Elem,TotalInfo,TotalInfo1),
    add_to_info(Info,TotalInfo1,TotalInfo2).

% TODO: do not ignore
add_to_info_2(Elem,[],New):- !,
    ( total_info_new_element(Elem,NewElem) ->
        New = [NewElem]
    ;
        New = []
    ).
add_to_info_2(Elem,[TElem|TotalInfo],[TElem1|TotalInfo]):-
    same_element(Elem,TElem),
    !,
    add_to_info_3(Elem,TElem,TElem1).
add_to_info_2(Elem,[TElem|TotalInfo],[TElem|TotalInfo1]):-
    add_to_info_2(Elem,TotalInfo,TotalInfo1).

same_element(time(_,_),time(_,_)).
same_element(memory(_,_),memory(_,_)).
same_element(assert_count(Module,_),assert_count(Module,_)).

total_info_new_element(time(A,B),time(A,B)).
total_info_new_element(memory(A,B),memory(A,B)).
total_info_new_element(assert_count(M,L),assert_count(M,NL)) :-
    app_count_diff_2(L,NL).

add_to_info_3(time(T,TL),time(TT,TTL),time(TT1,TTL1)) :-
    TT1 is TT+T,
    add_times(TL,TTL,TTL1).
add_to_info_3(memory(T,TL),memory(TT,TTL),memory(TT1,TTL1)) :-
    TT1 is TT+T,
    max_memory(TL,TTL,TTL1).
add_to_info_3(assert_count(_,TL),assert_count(_,TTL),assert_count(_,TTL1)) :-
    app_count_diff(TL,TTL,TTL1).

add_times([],L,L).
add_times([(N,T)|TLs],TTLs,TTL2s):-
    add_times_2((N,T),TTLs,TTL1s),
    add_times(TLs,TTL1s,TTL2s).

add_times_2((N,T),[],[(N,T)]) :- !.
add_times_2((N,T),[(N,TT)|TTLs],[(N,TT1)|TTLs]):- !,
    TT1 is TT+T.
add_times_2((N,T),[(N0,TT)|TTLs],[(N0,TT)|TTL1s]):-
    add_times_2((N,T),TTLs,TTL1s).

max_memory([],L,L).
max_memory([(N,T,S)|TLs],[(N,TT,SS)|TTLs],[(N,TT1,SS1)|TTL1s]):-
    max(TT,T,TT1),
    max(SS,S,SS1),
    max_memory(TLs,TTLs,TTL1s).

max(A,B,A):-
    A >= B, !.
max(_A,B,B).

app_count_diff([],L,L2):-
    app_count_diff_2(L,L2). %% The stored list is empty.
app_count_diff([(N,T)|TLs],[(N,V)|TTLs],[(N,TV)|TTL2s]):-
    app_count_diff_3(T,V,TV),
    app_count_diff(TLs,TTLs,TTL2s).

% if there is no previous list, just converts the numbers in lists with 1 element.
app_count_diff_2([],[]).
app_count_diff_2([(N,V)|Ts],[(N,[V])|TTs]):-
    app_count_diff_2(Ts,TTs).

% appends the number to the list, substracting the previous numbers in the list.
% (because assertions checked in previous steps are checked again).
app_count_diff_3([],V,[V]).
app_count_diff_3([N0|Ts],V,[N0|TVs]):-
    V1 is V-N0,
    app_count_diff_3(Ts,V1,TVs).

:- export(get_total_info/1).
get_total_info(Info):-
    current_fact(total_info(Info0)),
    sort_total_info(Info0,Info),
    !.  % TODO: IG why this cut?, all total_info data are generated with set_fact

%% All lists of results in the same order for every item.
sort_total_info([],[]).
sort_total_info([I0|I0s],[I1|I1s]):-
    functor(I0,F,A),
    arg(1,I0,Arg1),
    arg(2,I0,I0list),
    sort(I0list,I1list),
    functor(I1,F,A),
    arg(1,I1,Arg1),
    arg(2,I1,I1list),
    sort_total_info(I0s,I1s).

:- export(pp_statistics/2).
% The precision of runtime vs walltime is much worse in linux than in mac
% pp_statistics(runtime,B) :- !,
%         statistics(walltime,B).
pp_statistics(A,B) :-
    statistics(A,B).
