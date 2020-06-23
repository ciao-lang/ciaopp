:- module(ciaopp_batch, [analysis_start/2], [assertions, isomodes, regtypes, datafacts]).

:- doc(title, "Batch analysis client").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(stability, devel).

:- doc(module, "
This module contains predicates for managing the batch analysis of sets of modules.

@bf{Note}: this code is not performing multi-modular analysis. Some of
its components can be generalized for other processes (compilation,
program transformation) and be integrated into the build system,
compiler, analyzer, etc.

@section{Analysis options}
@begin{itemize}
@item @bf{no_incremental} : By default, analysis is made only for modules in
  Paths which were not analyzed before. With this option, analysis
  will be runned from scratch.
@item @bf{timeout(@var{T})} : @var{T} is the time limit for the analysis of
    each module independently.
@item @bf{analysis(@var{ListAbsInt})} : @var{ListAbsInt} is a list of abstract
    domains available in ciaopp.
@item @bf{workers(@var{N})} : @var{N} is the number of threads use to perform
    the analysis of independent modules. Currently only 1 worker is supported.
@end{itemize}
Example:
@begin{verbatim}
? - use_module(ciaopp_batch(ciaopp_batch)).
? - analysis_start(['~/ciao-devel/core/lib/'], [timeout(40), analysis([eterms, gr])]).
@end{verbatim}

@begin{alert}

Fast load through caching of assertions from libraries is
available in @tt{ciaopp_worker}.

To @bf{create} and @bf{manually update} this cache run command:
@tt{update_lib_cache}
@end{alert}

@begin{note}
Configuring ciaopp flags is not available yet.
@end{note}

@section{Description of the implementation}

@subsection{Prolog files:}
@begin{itemize}
@item `ciaopp_batch.pl`: driver for the per-module CiaoPP analysis
@item `ciaopp_master.pl`: performs control of ciaopp_workers, i.e.,
  launchs them and kills them.
@item `ciaopp_worker.pl`: does the actual analysis.
@item `ciaopp_batch_aux.pl`: file for auxiliary predicates.
@item `statistics_collecter.pl`: collects statistics of the analyzed files
  (time and memory).
@end{itemize}

@subsection{Other directories:}
@begin{itemize}
@item `Attic/`: placeholder for not used files that may be useful at some point
@end{itemize}

@section{Data files}

The status of the analysis is stored in the `data/` directory:
@begin{itemize}
@item `data/task_status.pl`: status of the modules (analyzed, errors, etc)
@item `last_analyzed_file.pl`: last analyzed predicate
@item `analysis.log`: date and time when each module started being analyzed
@end{itemize}
").

% NOTE: Make sure that this module does not have explicit dependencies
%   with the whole CiaoPP (just with the batch database)

:- use_module(engine(io_basic)).
:- use_module(engine(stream_basic), [fixed_absolute_file_name/3]).
:- use_module(library(process), [process_call/3]).
:- use_module(library(lists), [member/2]).
:- use_module(library(system), [working_directory/2]).

:- use_module(ciaobld(config_common), [cmd_path/4]).

:- use_module(ciaopp_batch(db_analysis)).
:- reexport(ciaopp_batch(db_analysis), [update_tasks_analysis_status/0]).

:- data no_inc_flag/0.

:- pred analysis_start(Paths, Opts) : list * list
    #"Analyzes modules in some @var{Paths} and dumps their analysis information
      to disk, given some @var{Opts}.".
analysis_start(Paths, Opts) :-
    ( member(no_incremental, Opts) -> clean_db, set_fact(no_inc_flag) ; true ),
    ( member(timeout(T), Opts) -> true ; T = 30 ), % 30s by default
    ( member(workers(N), Opts) -> true ; N = 1 ), % 1 worker by default
    ( member(analysis(AbsInts), Opts) -> true ; AbsInts = [pdb] ), % reachability by default
    atom_number(Ta, T),
    atom_number(Na, N),
    init_analysis_db,
    prepare_work(Paths, AbsInts, [], Work), %% Flags not supported at the moment!
    cmd_path(ciaopp, plexe, 'ciaopp_master', Exe), % TODO: extra process needed?
    process_call(Exe, [Ta, Na], [stdin(terms(Work))]),
    clean_tmp_db.

:- pred prepare_work(+Paths, +AbsInts, +Flags, -Work)
   : list * list * term * var => list(Work).
prepare_work([], _, _, []).
prepare_work([P|Ps], AbsInts, Flags, W1) :-
    working_directory(D,D),
    fixed_absolute_file_name(P, D, AP),
    clean_err_if_needed(AP),
    prepare_work_(AbsInts, AP, Flags, W1, Wt),
    Wt = W,
    prepare_work(Ps, AbsInts, Flags, W).

prepare_work_([], _, _, T, T).
prepare_work_([A|As], P, Flags, [w(P,A,Flags)|W], Wt) :-
    prepare_work_(As, P, Flags, W, Wt).

clean_err_if_needed(P) :-
    no_inc_flag, !,
    process_call(path(find), [P, '-type', 'f', '-name', '*.err', '-delete'], []).
clean_err_if_needed(_).
% TODO: write in prolog when .err files can be stored in a dedicated directory (ala CIAO_CACHE_DIR)

:- doc(doinclude, analysis_opt/1).
:- prop analysis_opt(Opt) #"Option of ciaopp batch (not ciaopp flags)".
analysis_opt(no_incremental).
analysis_opt(timeout(N)) :- int(N), N > 0.
analysis_opt(workers(N)) :- int(N), N > 0.
analysis_opt(analysis(L)) :- list(atm, L).

