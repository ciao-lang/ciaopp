:- module(ciaopp_batch_report, [main/1], [assertions, datafacts]).

:- doc(title, "XML report for ciaopp-batch output").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "This command generates a report in xml format compatible with
   junit xml
   (@url{https://www.ibm.com/support/knowledgecenter/en/SSQ2R2_14.1.0/com.ibm.rsar.analysis.codereview.cobol.doc/topics/cac_useresults_junit.html}).
   It can then be used to visualize the results of launching ciaopp_batch with
   the allure tool (see @url{https://github.com/allure-framework}), as well as
   in gitlab (@url{https://docs.gitlab.com/ee/ci/unit_test_reports.html}.").

:- use_module(engine(stream_basic), [open/3, close/1,fixed_absolute_file_name/3]).
:- use_module(library(process), [process_call/3]).
:- use_module(library(pathnames), [path_concat/3, path_splitext/3]).
:- use_module(library(format), [format/2, format/3]).
:- use_module(library(read), [read/2]).
:- use_module(library(system), [directory_files/2, working_directory/2, make_directory/1]).
:- use_module(library(pillow/html), [html2terms/2]).
% to escape terms of the messages
:- use_module(library(terms), [atom_concat/2]).
:- use_module(library(bundle/bundle_paths), [bundle_path/4]).

:- use_module(ciaopp_batch(ciaopp_batch), [analysis_start/2]).

main([Path0]) :-
    working_directory(D,D),
    fixed_absolute_file_name(Path0, D, Path),
    % copy all .err to generate report
    working_directory(WD, WD),
    path_concat(WD, 'error1234', EP), % TODO: mkdir in tmp
    format(user, 'Copying .err files to ~w~n', [EP]),
    bundle_path(core, builddir, 'xmlreport', AP),
    format(user, 'Generating report at ~w~n', [AP]),
    process_call(path(rm), ['-rf', EP], []),
    % TODO: use system_extra and source_tree predicates
    process_call(path(rm), ['-rf', AP], []),
    process_call(path(mkdir), [EP], []),
    process_call(path(mkdir), [AP], []),
    process_call(path(find), [Path, '-name', '\*.err', '-exec', 'cp', '{}', EP, '\;'], []),
    % generate report
    directory_files(EP, Fs),
    ( member(F, Fs), \+ (F = '..', F = '.'),
      generate_report_of_file(F, EP, AP),
      fail
    ; true
    ),
    close_xml_reports(AP).

generate_report_of_file(F, ErrorPath, APath) :-
    path_splitext(F, Mod, '.err'),
    path_concat(ErrorPath,F,Report),
    open(Report, read, S1),
    repeat,
    read(S1, X),
    ( X = end_of_file, !
    ;
        X = diagnosis(Test, Status, Info, OutStr, ErrStr),
        init_xml_report(APath, Test, S),
        atom_concat([Test,'.',Mod], Id),
        format_test(Status, S, Mod, Test, Id, Info, OutStr, ErrStr),
        close(S),
        fail
    ),
    close(S1).

xml_report_filepath(Path, RId, RP) :-
    atom_concat(RId, '.xml', Rep),
    path_concat(Path, Rep, RP).

open_xml_report(Path, RId, S) :-
    xml_report_filepath(Path, RId, RP),
    open(RP, append, S).

:- data initialized_report/1.

init_xml_report(Path, RId, S) :-
    open_xml_report(Path, RId, S),
    ( initialized_report(RId) ->
        true
    ;
        format(S, '<?xml version="1.0" encoding="UTF-8"?>~n', []),
        format(S, '<testsuites id="CiaoPP" name="CiaoPP" tests="1" failures="1" time="1">~n', []),
        format(S, '<testsuite id="~w" name="~w" tests="" failures="1" time="1">~n', [RId,RId]),
        asserta_fact(initialized_report(RId))
    ).

close_xml_reports(Path) :-
    ( % failure-driven loop
      retract_fact(initialized_report(RId)),
        open_xml_report(Path, RId, S),
        format(S, '</testsuite>~n', []),
        format(S, '</testsuites>~n', []),
        close(S),
        fail
    ; true).

format_test(ok, S, Mod, Test, Id, Info, _, Err) :-
    ( Info = [time(T,_)|_] -> true
    ; T = 0 ),
    format_successful_test(S, Test, Mod, Id, T, Err).
format_test(err, S, Mod, Test, Id, _, _, Err) :-
    format_failed_test(S, Test, Mod, Id, Err).
format_test(skip, S, Mod, Test, Id, _, _, _) :-
    format_skipped_test(S, Test, Mod, Id).

format_failed_test(S, Action, Mod, Id, Mess) :-
    X = testcase([id=Id, classname=Action, name=Mod], [failure([message=Mess], [])]),
    html2terms(Str, X),
    format(S, '~s', [Str]).

format_successful_test(S, Action, Mod, Id, Time, _Mess) :-
    T is Time/1000,
    X = testcase([id=Id, classname=Action, name=Mod, time=T], []),
    html2terms(Str, X),
    format(S, '~s~n', [Str]).

format_skipped_test(S, Action, Mod, Id) :-
    X = testcase([classname=Action, id=Id, name=Mod], [skipped([],[])]),
    html2terms(Str, X),
    format(S, '~s~n', [Str]).
