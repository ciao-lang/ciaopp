:- module(statistics_collecter, [collect_all_stats/1, set_flag_restore_time/1], [assertions, datafacts]).

:- doc(title, "Collecting statistics").

:- doc(author,"Isabel Garcia-Contreras").
% TODO: this module is outdated

:- doc(module, "Collects statistics from @tt{.err} files created while
   analyzing and summarizes them to produce an output in html or tex
   format.").

:- use_module(library(lists), [append/3, length/2]).
:- use_module(library(pathnames), [path_concat/3, path_basename/2]).
:- use_module(library(format), [format/3, format/2]).
:- use_module(library(system), [directory_files/2, file_property/2, file_exists/1]).
:- use_module(engine(stream_basic)).
:- use_module(library(read), [read/2]).
:- use_module(ciaopp(p_unit/p_dump), [restore/2]).

:- use_module(ciaopp_batch(ciaopp_batch_aux), [string_contained/2]).
:- use_module(ciaopp_batch(db_analysis), [db_data_dir/1]).

:- data timeout_counter/1.
:- data counter/2.
:- data total_files/1.
:- data test_flag/2.

:- data flag_restore_time/1.

test_flag(output, latex).
test_flag(show_errors, off).
test_flag(show_timeouts, off). 

:- export(stat_collecter_set_flag/2).
:- pred stat_collecter_set_flag(Flag, Status) : atm * atm
    #"Predicate for changing flags of the output. The available flags are:
@begin{itemize}
@item output. Modify output format; html or tex.
@item show_errors. on: display also modules that have errors while analyzing
@item show_timeouts. on: display also modules that did not finish before a timeout.
@end{itemize}
".
stat_collecter_set_flag(Flag, Status) :-
    set_fact(test_flag(Flag, Status)).

timeout_counter(0).
counter(load, 0).
counter(eterms, 0).
counter(shfr, 0).
counter(t_load, 0).
counter(e_ana_time, 0).
counter(e_memory, 0).
counter(s_ana_time, 0).
counter(s_memory, 0).

flag_restore_time(on).

clean_counters :-
    set_fact(timeout_counter(0)),
    retractall_fact(counter(_,_)),
    assertz_fact(counter(load, 0)),
    assertz_fact(counter(eterms, 0)),
    assertz_fact(counter(shfr, 0)),
    assertz_fact(counter(t_load, 0)),
    assertz_fact(counter(e_ana_time, 0)),
    assertz_fact(counter(e_memory, 0)),
    assertz_fact(counter(s_ana_time, 0)),
    assertz_fact(counter(s_memory, 0)).

inc_timeout_counter :-
    timeout_counter(X),
    Y is X + 1,
    set_fact(timeout_counter(Y)).

inc_counter(Name) :-
    counter(Name, X),
    Y is X + 1,
    retract_fact(counter(Name, X)),
    asserta_fact(counter(Name, Y)).
sum_counter(Name, Amount) :-
    counter(Name, X),
    Y is X + Amount,
    retract_fact(counter(Name, X)),
    asserta_fact(counter(Name, Y)).

inc_info(LT, EAT, EM, SAT, SM) :-
    sum_counter(t_load, LT),
    sum_counter(e_ana_time, EAT),
    sum_counter(e_memory, EM),
    sum_counter(s_ana_time, SAT),
    sum_counter(s_memory, SM).

:- pred set_flag_restore_time(Status) : atm
    #"Predicate for setting the flag to collect statistics of restoring time".
set_flag_restore_time(X) :-
    set_fact(flag_restore_time(X)).

add_extension_to_report(Base, File) :-
    ( test_flag(output, html) ->
        atom_concat(Base, '.html', File)
    ;
        atom_concat(Base, '.tex', File)
    ).

report_file(F) :-
    db_data_dir(D),
    path_concat(D, 'statistics_report.html', F).

:- pred collect_all_stats(Paths) : list(Paths) #"Collects the time and
memory statistics from .err files in a list of @var{Paths}".
collect_all_stats(Paths) :-
    clean_counters,
    files_from_paths(Paths, Files),
    length(Files, L),
    set_fact(total_files(L)),
    report_file(Base),
    add_extension_to_report(Base, F),
    open(F, write, S),
    print_header(S),
    gather_info_from_files(Files, S),
    print_summary(S),
    print_foot(S),
    close(S).

gather_info_from_files([], _).
gather_info_from_files([F|Files], S) :-
    gather_info_from_file(F, S),
    gather_info_from_files(Files, S).

gather_info_from_file(err(FilePath, ModName), S) :-
    open(FilePath, read, FileS),
    read(FileS, Info),
    close(FileS),
    Info = diagnosis(Load, _, LErrors, Eterms, _, EErrors, Shfr, _, SErrors),
    info_from_load(Load, LTime),
    ( LTime = timeout ->
        inc_timeout_counter,
        print_info_timeout(S, ModName)
    ;
        ( errors_in_message(LErrors) ->
            print_load_error(S, ModName, LTime)
        ;
            inc_counter(load),
            info_from_analysis(eterms, Eterms,EErrors,EPreT, EAnaT, EProgramM,
            EGlobalStackM, ELocalStackM, ETrailM, EChoiceM),
            info_from_analysis(shfr, Shfr,SErrors, SPreT, SAnaT, SProgramM,
            SGlobalStackM, SLocalStackM, STrailM, SChoiceM),                
            RestoreTime = '-',
            inc_info(LTime, EAnaT, EGlobalStackM, SAnaT, SGlobalStackM),
            print_info(S, ModName, LTime, EPreT, EAnaT,
            EProgramM, EGlobalStackM, ELocalStackM, ETrailM,
            EChoiceM,SPreT, SAnaT, SProgramM, SGlobalStackM,
            SLocalStackM, STrailM, SChoiceM, RestoreTime)
        )
    ).

errors_in_message(Msg) :-
    string_contained("ERROR", Msg).

info_from_load(timeout, timeout) :- !.
info_from_load(LInfo, LTime) :-
    LInfo = [time(LTime, _)].

dump_file(FilePath, DumpFile) :-
    atom_concat(ModName, '.err', FilePath),
    atom_concat(ModName, '.dump', DumpFile).

info_from_analysis(_, AInfo,EErrors, PreT, AnaT, error, '-', '-', '-', '-') :-
    errors_in_message(EErrors), !,
    AInfo = [time(_,[(prep,PreT),(ana,AnaT)]),memory(_,_)].
info_from_analysis(Domain, AInfo, _, PreT, AnaT, ProgramM, GlobalStackM, LocalStackM, TrailM, ChoiceM) :-
    inc_counter(Domain),
    AInfo =
    [time(_,[(prep,PreT),(ana,AnaT)]),
    memory(_,[(program,ProgramM,_),(global_stack,GlobalStackM,_),(local_stack,LocalStackM,_),(trail,TrailM,_),(choice,ChoiceM,_)])].

print_info(S, ModName, LTime, EPreT, EAnaT, EProgramM, EGlobalStackM,
    ELocalStackM, ETrailM, EChoiceM,SPreT, SAnaT, SProgramM,
    SGlobalStackM, SLocalStackM, STrailM, SChoiceM, RestoreTime) :-
      (test_flag(output, html) ->
          print_html_info(S, ModName, LTime, EPreT, EAnaT, EProgramM, EGlobalStackM,
          ELocalStackM, ETrailM, EChoiceM,SPreT, SAnaT, SProgramM,
          SGlobalStackM, SLocalStackM, STrailM, SChoiceM, RestoreTime)
      ;
          print_latex_info(S, ModName, LTime, EPreT, EAnaT, EProgramM, EGlobalStackM,
          ELocalStackM, ETrailM, EChoiceM,SPreT, SAnaT, SProgramM,
          SGlobalStackM, SLocalStackM, STrailM, SChoiceM, RestoreTime)
      ).

print_html_info(S, ModName, LTime, EPreT, EAnaT, EProgramM, EGlobalStackM,
    ELocalStackM, ETrailM, EChoiceM,SPreT, SAnaT, SProgramM,
    SGlobalStackM, SLocalStackM, STrailM, SChoiceM, RestoreTime) :-
     format(S,
    '<tr><td>~w</td><td>~w</td>', [ModName, LTime]),
    format(S, '<td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td>', [EPreT, EAnaT, EProgramM, EGlobalStackM,
    ELocalStackM, ETrailM, EChoiceM]),
    format(S, '<td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td><td>~w</td></tr>~n',
    [SPreT, SAnaT, SProgramM, SGlobalStackM, SLocalStackM,
    STrailM, SChoiceM, RestoreTime]).

print_latex_info(S, ModName, LTime, _EPreT, EAnaT, _EProgramM, EGlobalStackM,
    _ELocalStackM, _ETrailM, _EChoiceM, _SPreT, SAnaT, _SProgramM,
    SGlobalStackM, _SLocalStackM, _STrailM, _SChoiceM, _RestoreTime) :-
    format(S,
    '~w & ~w &', [ModName, LTime]),
    format(S, '~w & ~w &', [EAnaT, EGlobalStackM]),
    format(S, '~w & ~w  \\\\ \\hline~n',
    [SAnaT, SGlobalStackM]).

print_info_timeout(S, ModName) :-
    (test_flag(show_timeouts, on) ->
        print_info(S, ModName, timeout, '-', '-','-','-','-','-','-','-','-','-','-','-','-','-','-')
    ;
        true).

print_load_error(S, ModName, _LTime) :-
    (test_flag(show_errors, on) ->
        print_info(S, ModName, error, '-', '-','-','-','-','-','-','-','-','-','-','-','-','-', '-')
    ;
        true).

print_header(S) :-
    (test_flag(output, html) ->
        print_html_header(S)
    ;
        print_latex_header(S)
    ).
print_html_header(S) :-
    format(S, '<html>', []),
    format(S, '<head><style type="text/css"> body { font-family: monospace; } </style></head>', []),
    format(S, '<body>', []),
    format(S, 'Times are in msec, memory in Bytes~n<table>~n', []),
    print_info(S, path, load_time, e_pre_time, 'regtype ana time', e_program_mem, 'regtype global stack mem', e_local_stack_mem, e_trail_mem, e_choice_mem, s_pre_time, 'shfr ana time', s_program_mem, 'shfr global stack mem', s_local_stack_mem, s_trail_mem, s_choice_mem, restore_time).

print_latex_header(S) :-
    format(S, '\\begin{small}~n', []),
    format(S, '\\begin{longtable}{||p{40mm}|p{10mm}|p{13mm}|p{18mm}|p{10mm}|p{17mm}||}~n', []),
    format(S, '\\caption{Analysis statistics from core/lib modules.\\label{tab:statsreduced}}\\\\~n \\hline\\hline~n', []),
    print_info(S, '\\textbf{path}', '\\textbf{load_time}', '\\textbf{e_pre_time}', '\\textbf{regtype ana time}', '\\textbf{e_program_mem}', '\\textbf{regtype global stack mem}', '\\textbf{e_local_stack_mem}', '\\textbf{e_trail_mem}', '\\textbf{e_choice_mem}', '\\textbf{s_pre_time}', '\\textbf{shfr ana time}', '\\textbf{s_program_mem}', '\\textbf{shfr global stack mem}', '\\textbf{s_local_stack_mem}', '\\textbf{s_trail_mem}', '\\textbf{s_choice_mem}', '\\textbf{restore_time}'),
    format(S, '\\hline\\hline~n\\endfirsthead~n\\caption{Analysis statistics from core/lib modules \\emph{(continued)}.}\\ \\hline\\hline~n', []),
    print_info(S, '\\textbf{path}', '\\textbf{load_time}', '\\textbf{e_pre_time}', '\\textbf{regtype ana time}', '\\textbf{e_program_mem}', '\\textbf{regtype global stack mem}', '\\textbf{e_local_stack_mem}', '\\textbf{e_trail_mem}', '\\textbf{e_choice_mem}', '\\textbf{s_pre_time}', '\\textbf{shfr ana time}', '\\textbf{s_program_mem}', '\\textbf{shfr global stack mem}', '\\textbf{s_local_stack_mem}', '\\textbf{s_trail_mem}', '\\textbf{s_choice_mem}', '\\textbf{restore_time}'),
    format(S, '\\hline\\hline~n\\endhead~n \\multicolumn{6}{c}{\\emph{(continued in next page)}}\\\\~n \\endfoot~n \\endlastfoot~n', []).

print_avg(S) :-
    counter(t_load, TL),
    counter(e_ana_time, EAT),
    counter(e_memory, EM),
    counter(s_ana_time, SAT),
    counter(s_memory, SM),
    total_files(TF),
    ATL is TL/TF,
    AEAT is EAT/TF,
    AEM is EM/TF,
    ASAT is SAT/TF,
    ASM is SM/TF,
    print_info(S, 'Total', TL, _, EAT, _, EM, _, _, _, _, SAT, _, SM, _, _, _, _),
    print_info(S, 'AVG', ATL, _, AEAT, _, AEM, _, _, _, _, ASAT, _, ASM, _, _, _, _).       

print_summary(S) :-
    ( test_flag(output, html) ->
       format(S, '</table>', []),
       counter(load, LC),
       counter(eterms, EEC),
       counter(shfr, SEC),
       timeout_counter(TC),
       total_files(TF),
       format(S, '# Loaded: ~w/~w ~nEterms Analyzed: ~w/~w ~n Shfr Analyzed: ~w/~w ~nTimeouts: ~w', [LC, TF, EEC, TF, SEC, TF, TC])
    ;  true
    ).

print_foot(S) :-
    ( test_flag(output, htm) ->
      print_html_foot(S)
    ;
        print_latex_foot(S)
    ).

print_html_foot(S) :-
    format(S, '</body>~n', []),
    format(S, '</html>~n', []).

print_latex_foot(S) :-
    print_avg(S),
    format(S, '\\end{longtable}~n', []),
    format(S, '\\end{small}~n', []).

files_from_paths(Paths, Files) :-
    files_from_paths_(Paths, Files, []).

files_from_paths_([], Fs, Fs).
files_from_paths_([Path|Paths], Fs, Fs0) :-
    files_from_path(Path, Fs, Fs1),
    files_from_paths_(Paths, Fs1, Fs0).

files_from_path(Path, Fs, Fs0) :-
    ( atom_concat(Base, '.pl', Path) ->
        path_basename(Base, Module),
        Fs = [pl(Path,Module)|Fs0]
    ; related_err_at(Path, Files),
      append(Files, Fs0, Fs)
    ).

% TODO: copied from librowser
:- meta_predicate related_files_at(?, pred(1), ?).
related_err_at(Dir, Files) :-
    directory_files(Dir,AllFiles),
    related_err_at_aux(AllFiles,Dir, Files).

related_err_at_aux([],_,[]).
related_err_at_aux(['.'|Nf],Dir,  NNf) :-
    !,
    related_err_at_aux(Nf,Dir,NNf).
related_err_at_aux(['..'|Nf],Dir,NNf) :-
    !,
    related_err_at_aux(Nf,Dir,NNf).
related_err_at_aux([File|Nf],Dir,NNf) :-
    atom_concat('.#',_,File),
    !,
    related_err_at_aux(Nf,Dir,NNf).
related_err_at_aux([File|Nf],Dir,ModList) :-
    atom_concat(Module,'.err',File),
    !,
    atom_concat(Module,'.err',PlFile),
    path_concat(Dir,PlFile,AbsFile),
    ModList = [err(AbsFile,Module)|NNf],
    related_err_at_aux(Nf,Dir,NNf).
related_err_at_aux([File|Nf],Dir,RelatedFiles) :-
    path_concat(Dir,File,AbsFile),
    is_dir_nolink(AbsFile),
%       file_property(AbsFile,type(directory)),
    !,
    related_err_at_aux(Nf,Dir,NNf),
    related_err_at(AbsFile, NewFiles),
    append(NNf,NewFiles,RelatedFiles).
related_err_at_aux([_|Nf],Dir,NNf) :-
    !,
    related_err_at_aux(Nf,Dir,NNf).

% TODO: copied from source_tree.pl, fix
% FileName is a directory that is not a symbolic link
is_dir_nolink(FileName) :-
    \+ file_property(FileName, linkto(_)),
    file_exists(FileName),
    file_property(FileName, type(directory)).

