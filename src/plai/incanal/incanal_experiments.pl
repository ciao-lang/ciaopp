:- module(incanal_experiments,
    [
        td_add_file_clause_by_clause/2,
        td_delete_file_clause_by_clause/2,
        bu_delete_file_clause_by_clause/2
    ],
    [assertions, modes]).

:- use_module(ciaopp(plai/incanal/incanal_driver)).
:- use_module(ciaopp(raw_printer), [show_analysis/0]).

:- use_module(spec(mem_usage),
    [reset_mem_usage/0, ask_mem_usage/2, update_mem_usage/0, report_mem_usage/0]).

:- use_module(engine(io_basic)).
:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(lists), [length/2, reverse/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- use_module(library(hiordlib), [maplist/3]).

:- doc(module, "This module contains experiments using the incremental
    analysis driver").

:- doc(author, "Isabel Garcia-Contreras (ported from ciaopp-0.8)").

:- doc(bug, "Statistics are not displayed correctly").

:- doc(section, "Top down additition experiment").

:- pred td_add_file_clause_by_clause(+File, +AbsInt) #"This is the
    entry point to analyze a file clause by clause".
td_add_file_clause_by_clause(File,AbsInt):-
    init_file_inc_analysis(File, Cls, _Ds),
    reset_mem_usage,
    pp_statistics(runtime,[_,T0]),
    td_analyze_clause_by_clause(Cls, AbsInt),
    pp_statistics(runtime,[_,T1]),
    T is T1 - T0,
    report_time('td_analyzed_clause_by_clause',0,T),
    report_mem_usage,
    message(inform, ['}']).

td_analyze_clause_by_clause([], _AbsInt).
td_analyze_clause_by_clause([Cl:Id|_], AbsInt) :-
    td_add_clauses([Id], AbsInt),
    display(added(Cl)), nl,
    show_analysis, % IG
    fail.
td_analyze_clause_by_clause([_|Cls], AbsInt) :-
    td_analyze_clause_by_clause(Cls, AbsInt).

:- doc(section, "Top down deletion experiment").

:- pred td_delete_file_clause_by_clause(File, AbsInt) : atm * atm
    #"This predicate performs the experiment of removing clauses
     from a @var{File} one by one (in an ordered way, starting from the
     last clause), using a top down deletion strategy.

     Note that clauses are added one by one without checking if
     are original clauses or were generated after transformation
     (i.e., for example cuts are transformed in more than one
     clause)".
td_delete_file_clause_by_clause(File,AbsInt):-
    set_up_del_cl_cl(File, AbsInt, Cls),
    reverse(Cls, Inv_Cls),
    length(Inv_Cls,CC),
    top_down_delete_loop(Inv_Cls,AbsInt,CC),
    report_time('top_down_deleted_clause_by_clause',0,_T1).

top_down_delete_loop([], _, _).
top_down_delete_loop([Clid|_], AbsInt, _CC) :-
    td_delete_clauses([Clid], AbsInt),
    display(deleting(Clid)), nl,
    show_analysis,
    fail.
top_down_delete_loop([_|MoreCls], AbsInt, CC) :-
    CC1 is CC - 1,
    top_down_delete_loop(MoreCls, AbsInt, CC1).

:- pred set_up_del_cl_cl(+File, +AbsInt, -Clids) #"
    Prepares analysis of the file for incremental deletion. 
    Steps:

    1. Initializes ciaopp (fixpoint dd).
    2. Reads @var{File} and asserts internal structures.
    3. Initializes tarjan and internal data.
    4. Analyzes for all the clauses from scratch for @var{AbsInt}.

    This predicate returns the program clauses id in @var{Cls}.".
set_up_del_cl_cl(File, AbsInt, Clids) :-
    init_file_inc_analysis(File, Cls, _Ds),
    maplist(clid_from_cl_struct, Cls, Clids),
    td_add_clauses(AbsInt, Clids), % IG adds all clauses and analyzes
    display('---------- Initial analysis ----------'), nl,
    show_analysis.

clid_from_cl_struct(_:Clid, Clid).      

:- doc(section, "Bottom up deletion experiment").

:- pred bu_delete_file_clause_by_clause(File, AbsInt) : atm * atm
    #"This predicate performs the experiment of removing clauses
     from a @var{File} one by one (in an ordered way, starting from the
     last clause), using a bottom up deletion strategy.

     Clauses are added in the same way as in
     @pred{top_down_delete_clause_by_clause/2}".

bu_delete_file_clause_by_clause(File,AbsInt):-
    set_up_del_cl_cl(File, AbsInt, Clids),
    reverse(Clids, Inv_Cls),
    length(Inv_Cls,CC),
    bottom_up_delete_loop(Inv_Cls,AbsInt,CC).

bottom_up_delete_loop([],_AbsInt,_).
bottom_up_delete_loop([Clid|_],AbsInt,_CC):-
    bu_delete_clauses([Clid],AbsInt),
    display(deleting(Clid)), nl,
    show_analysis,
    fail.
bottom_up_delete_loop([_|MoreCls],AbsInt,CC):-
    CC1 is CC -1,
    bottom_up_delete_loop(MoreCls,AbsInt,CC1).

:- doc(section, "Auxiliary predicates").
report_time(_Action, _T0, _T1) :-
    %display_list([Action, ' ', T0, ' ', T1]), nl.
    true.
