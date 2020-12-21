:- module(trace_fixp, [
    fixpoint_trace/7,
    trace_fixp/1,
    memotable_trace/3,
    show_spypoint_op_count/0,
    show_updated_memotable/3,
    trace_init/0,
    trace_end/0,
    trace_reset/0
], [assertions, regtypes, datafacts]).

:- use_module(library(aggregates), [findall/3]).
:- use_module(engine(messages_basic)).
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(format), [format/2]).
:- use_module(library(write), [numbervars/3]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).

:- use_module(ciaopp(plai/view_fixp)).  % windowing
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- doc(title, "Fixpoint tracer").

:- doc(module, "This module traces the operations of fixpoints by
explicitely calling @pred{fixpoint_trace/7} during computation.

To deactivate tracing (it can slowdown the analysis), package
@tt{ciaopp(plai/notrace)} has to be imported in the used fixpoint.").

:- doc(stability, devel).

:- data fixpoint_trace/1,
    fixpoint_op_count/3.

:- data init_time/1.

trace_init :-
    current_pp_flag(trace_fixp, X),
    \+ X = no, !,
    trace_fixp(X),
    pp_statistics(runtime, [T0, _]),
    set_fact(init_time(T0)).
trace_init :-
    trace_fixp(no).

trace_end :-
    % TODO: here dump results if not done already? -- for op_count
    end_view,
    trace_reset.

trace_reset :-
    retractall_fact(fixpoint_op_count(_,_,_)),
    clean_fixpoint_graph.

%% --------------------------------------------------------------------
%% tracing the fixpoint:
fixpoint_trace(Mess,Id,F,SgKey,Sg,Proj,Childs):-
    ( fixpoint_trace(op_count) -> update_fixpoint_op_count(Mess,Id) ; true ),
    ( fixpoint_trace(trace) -> trace_fixpoint(Mess,Id,F,Sg,Proj) ; true ),
    ( fixpoint_trace(view) -> view_fixpoint(Mess,Id,F,SgKey,Sg,Proj,Childs) ; true).

%% --------------------------------------------------------------------
%% toggle tracing:

:- export(trace_option/1).
:- regtype trace_option/1.
trace_option(no).
trace_option(op_count).
trace_option(trace).
trace_option(view).

:- doc(trace_fixp(X), "Toggle a trace of the fixpoint computation during
    analysis. The (X=op_count) option counts steps of fixpoint operations, show
    certain relevant spy points during analysis (X=trace), and/or display the
    analysis graph which is being constructed (X=view). The information added up
    can be seen at end of analysis with @tt{show_fixpoint_op_count.}").

:- pred trace_fixp(X) : trace_option(X) + not_further_inst(X)
   # "Mode for setting the current flag to a single value.".
:- pred trace_fixp(X) : list(trace_option, X)   + not_further_inst(X)
   # "Mode for setting the current flag to several values.".
%% TODO: Tracing in several ways at the same time is not currently integrated
%% with preprocess_flags
trace_fixp(F):-
    var(F), !,
    findall(S,fixpoint_trace(S),F).
trace_fixp(F):-
    trace_fixp0(F).

trace_fixp0(X):-
    fixpoint_trace(X), !.
trace_fixp0(no):-
    trace_reset. % TODO: why stopping the tracing should clean the result?
trace_fixp0(view):-
    start_view,
    asserta_fact(fixpoint_trace(view)).
trace_fixp0(trace):-
    asserta_fact(fixpoint_trace(trace)).
trace_fixp0(info):-
    asserta_fact(fixpoint_trace(info)).
trace_fixp0([]).
trace_fixp0([F|Fs]):-
    trace_fixp0(F),
    trace_fixp0(Fs).

%% --------------------------------------------------------------------
%% trace:

:- push_prolog_flag(multi_arity_warnings,off).
trace_fixpoint(Mess,Id,_L,Sg,Proj) :-
    trace_fixpoint(Mess), !,
    ( current_pp_flag(timestamp_trace,on) ->
        pp_statistics(runtime, [Tn, _]),
        init_time(T0),
        T is Tn - T0,
        message(inform, ['{[', ~~(T), '] ', ~~(Mess), ' for node ', ''(Id), '}'])
    ;
        message(inform, ['{', ~~(Mess), ' for node ', ''(Id), '}'])
    ),
    ( \+ (var(Sg), var(Proj)) ->
        \+ \+ ( numbervars(p(Sg,Proj),0,_),
                message(inform, ['{', ''(Sg), '   ', ''(Proj), '}'])
              )
    ; true ).
trace_fixpoint(_Mess,_Id,_L,_Sg,_Proj).

trace_fixpoint('start query').
trace_fixpoint('end query').
trace_fixpoint('init fixpoint').
trace_fixpoint('visit goal').
trace_fixpoint('visit clause').
trace_fixpoint('visit fact').
trace_fixpoint('exit fact').
trace_fixpoint('exit goal').
trace_fixpoint('exit clause').
trace_fixpoint('non-recursive initiated').
trace_fixpoint('non-recursive completed').
trace_fixpoint('complete used').
trace_fixpoint('fixpoint used').
trace_fixpoint('approx used').
trace_fixpoint('approx unchanged').
trace_fixpoint('fixpoint initiated').
trace_fixpoint('fixpoint completed').
trace_fixpoint('fixpoint approximated').
trace_fixpoint('fixpoint iteration').
trace_fixpoint('result of widening').
trace_fixpoint('builtin completed').
trace_fixpoint('external call completed').
trace_fixpoint('trust').
trace_fixpoint('applied trust').
% For incremental analysis inside fixpoint dd
trace_fixpoint('visit change').
trace_fixpoint('visit change clause').
trace_fixpoint('exit change clause').
% For incremental analysis driver
trace_fixpoint('[incanal] change').
trace_fixpoint('[incanal] bu fixpoint started').
trace_fixpoint('[incanal] bu fixpoint completed').
trace_fixpoint('[incanal] bu non-recursive initiated').
trace_fixpoint('[incanal] bu non-recursive completed').
% For intermodular analysis driver
trace_fixpoint('[mod] reg read').
trace_fixpoint('[mod] reg header created').
trace_fixpoint('[mod] new child').
trace_fixpoint('[mod] new parent').
trace_fixpoint('[mod] new registry').
trace_fixpoint('[mod] succ changed').
trace_fixpoint('[mod] check reg').

:- pop_prolog_flag(multi_arity_warnings).

%% --------------------------------------------------------------------
%% info:

:- push_prolog_flag(multi_arity_warnings,off).

update_fixpoint_op_count(Mess,Id) :-
    update_fixpoint_op_count(Mess), !,
    update_fixpoint_op_count0(Mess,Id).
update_fixpoint_op_count(_Mess,_Id).

update_fixpoint_op_count0(Mess,Id) :-
    retract_fact(fixpoint_op_count(Id,Mess,N)), !,
    N1 is N+1,
    asserta_fact(fixpoint_op_count(Id,Mess,N1)).
update_fixpoint_op_count0(Mess,Id) :-
    asserta_fact(fixpoint_op_count(Id,Mess,1)).

update_fixpoint_op_count('visit_clause').
update_fixpoint_op_count('non-recursive completed').
update_fixpoint_op_count('approx used').
update_fixpoint_op_count('approx unchanged').
update_fixpoint_op_count('fixpoint initiated').
update_fixpoint_op_count('fixpoint iteration').

:- pop_prolog_flag(multi_arity_warnings).
%------------------- MORE FIXPOINT TRACE PREDICATES -----------------------%
% Shows certain spy points of the analysis. It only shows this information
% if and only if trace_fixp/1 includes the option trace.
show_spypoint_op_count :-
    fixpoint_trace(op_count),!,
    message(inform, ['{The following information contains certain spy points of the analysis}']),
    show_spypoint_op_count_.
show_spypoint_op_count.

show_spypoint_op_count_ :-
    current_fact(fixpoint_op_count(Id,Mess,N)),
    message(inform, ['{', ~~(Id), ' ', ~~(Mess), ' ', ~~(N), '}']),
    fail.
show_spypoint_op_count_.

%------------------- MEMOTABLE TRACE PREDICATES -------------------%
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(library(pathnames), [path_splitext/3]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(ciaopp(plai/fixpo_plai), [approx/6, fixpoint/6, '$depend_list'/3]).
:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(library(write), [write/2]).

memotable_trace(IdMess,Id,SgKey) :-
    (fixpoint_trace(trace), trace_memotable(IdMess,Mess)),!,        
    message(inform, ['{', ~~(Mess), ' for node ', ~~(Id), ' and ', ~~(SgKey), '}']),
    show_updated_memotable(IdMess,Id,SgKey).
memotable_trace(_IdMess,_Id,_SgKey).
    
trace_memotable(1,'MT: Updated from approx to complete').
trace_memotable(2,'MT: Added non-recursive method as complete').
trace_memotable(3,'MT: Added as fixpoint').
trace_memotable(4,'MT: Updated from fixpoint to complete').
trace_memotable(5,'MT: Updated from fixpoint to approx').
trace_memotable(6,'MT: Added builtin as complete').
trace_memotable(7,'MT: Updated from fixpoint to fixpoint').
trace_memotable(8,'MT: Added external call as complete').

show_updated_memotable(Mess,Id,SgKey) :-
    curr_file(Path,_),
    path_splitext(Path,Basefile,_),
    Ext = '.MEMOTABLE',
    atom_concat([Basefile,Ext],Output),
    open(Output,append,Stream),!,   
    nl(Stream),
    trace_memotable(Mess,Mess0),
    write(Stream,Mess0),write(Stream,' for node '),
    write(Stream,Id),write(Stream,' and '),write(Stream,SgKey),nl(Stream),
    show_dependencies(Stream),nl(Stream),
    write(Stream,'-------------------- MEMO TABLE --------------------'), 
    nl(Stream),
    show_complete(Stream),
    show_fixpoint(Stream),
    show_approx(Stream).

show_complete(Stream) :-
    current_fact(complete(_SgKey,_,Subg,Proj,Prime,_Id,_Fs),_Ref),
    display_subgoal(Stream,Subg),write(Stream,':'),
    write(Stream,' COMPLETE '),
    write(Stream,Proj),write(Stream,' -> '),
    write(Stream,Prime),nl(Stream),
    write(Stream,'----------------------------------------------------'), 
    nl(Stream),
    fail.
show_complete(_).

show_fixpoint(Stream) :-
    current_fact(fixpoint(_SgKey,Subg,Proj,Prime,_Id,_Fs),_Ref),
    display_subgoal(Stream,Subg),write(Stream,':'),
    write(Stream,' FIXPOINT '),
    write(Stream,Proj),write(Stream,' -> '),
    write(Stream,Prime),nl(Stream),
    write(Stream,'----------------------------------------------------'), 
    nl(Stream),
    fail.
show_fixpoint(_).

show_approx(Stream) :-
    current_fact(approx(_SgKey,Subg,Proj,Prime,_Id,_Fs),_Ref),
    display_subgoal(Stream,Subg),write(Stream,':'),
    write(Stream,' APPROX '),
    write(Stream,Proj),write(Stream,' -> '),
    write(Stream,Prime),nl(Stream),
    write(Stream,'----------------------------------------------------'), 
    nl(Stream),
    fail.
show_approx(_).

:- use_module(library(terms_vars), [varset/2]).
display_subgoal(Stream,Subgoal) :-
    varset(Subgoal,Vars),
    functor(Subgoal,F,_),
    Goal =.. [F|Vars],
    write(Stream,Goal).

show_dependencies(Stream) :-
    current_fact('$depend_list'(Id,SgKey,List)),
    write(Stream,'depend('),write(Stream,Id),write(Stream,'-'),
    write(Stream,SgKey),write(Stream,','),write(Stream,List),
    write(Stream,')'),nl(Stream),
    fail.
show_dependencies(_).
