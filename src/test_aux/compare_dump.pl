:- module(compare_dump, [compare_dumps_auto_detect_db/6],
          [assertions, hiord, datafacts, isomodes, fsyntax]).

:- doc(title, "Semantic dump comparator").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(stability, devel).

:- doc(module, "This module provides funcionality for comparing two
instances of the ciaopp analysis database.

").

:- use_module(engine(io_basic)).
:- use_module(library(fastrw), [fast_read/2]).
:- use_module(library(pathnames), [path_splitext/3, path_concat/3]).
:- use_module(library(system), [file_exists/1, directory_files/2, file_property/2]).
:- use_module(library(write), [numbervars/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(lists), [member/2]).

:- use_module(ciaopp(plai/plai_db), [complete/7, memo_table/6]).
:- use_module(ciaopp(plai/domains), [less_or_equal/3, abs_sort/3, needs/2]).
:- use_module(ciaopp(plai/fixpo_ops), [each_abs_sort/3, each_less_or_equal/3]).
:- use_module(ciaopp(p_unit/p_abs)).
:- use_module(ciaopp(p_unit/p_dump), [restore/1]).
:- use_module(ciaopp(p_unit/auxinfo_dump), [acc_auxiliary_info/2, dump_auxiliary_info/1]).

:- use_module(typeslib(typeslib), [is_new_type/1]).

:- use_module(ciaopp(plai/incanal/plai_db_comparator), [compare/4]).
:- use_module(ciaopp(plai/incanal/plai_db_instances), [copy_db/2, plai_db_tuple/8]).

:- export(checking_domain/1).
:- data checking_domain/1.

:- meta_predicate process_diff_item(?, pred(1)).
process_diff_item(D, Skip) :-
    Skip(D), !, fail.
process_diff_item(abs_diff(_,_,_, Sg:Call, Succ, new), _) :- !,
    human_display_list(['NEW CALL ', Sg:Call, Succ]),
    show_auxiliary_info_list([Call|Succ],~checking_domain).
process_diff_item(abs_diff(_,_,_,_,_,X), _) :-
    X = modif(Sg:Call, Succ, Succ2), !,
    checking_domain(AbsInt),
    each_abs_sort(Succ, AbsInt, Succ_s),
    each_abs_sort(Succ2, AbsInt, Succ2_s),
    ( each_less_or_equal(Succ_s, AbsInt, Succ2_s) ->
        % this means that the second analysis is equal or less precise
        human_display_list(['LOSS ', Sg:Call, Succ_s, Succ2_s])
    ;
        % this means that the second analysis is more precise
        human_display_list(['ERROR ', Sg:Call, Succ_s, Succ2_s])
    ),
    show_auxiliary_info_list([Call|Succ_s],AbsInt),
    show_auxiliary_info_list(Succ2_s,AbsInt).
process_diff_item(abs_diff(_,_,_,_,_,X),_) :-
    X = not_in(Sg:Call), !,
    human_display_list(['MISSING ', Sg:Call]),
    show_auxiliary_info_list([Call],~checking_domain).
process_diff_item(abs_diff(_,_,_,_,_,X),_) :-
    X = contained(_Sg:_Call), !,
    fail.
process_diff_item(X,_) :-
    display(X), nl.

:- export(print_diff/3).
:- meta_predicate print_diff(+, pred(1), ?).
print_diff([], _, []).
print_diff([D_item|Ds], Skip, [D_item|ND]) :-
    process_diff_item(D_item, Skip), !,
    print_diff(Ds, Skip, ND).
print_diff([_|Ds], Skip, ND) :-
    print_diff(Ds, Skip, ND).

:- pred compare_dumps_auto_detect_db(+DF1, +DF2, ?To1, ?To2, +AbsInt, -Diff)
    #"This predicate performs the same comparison as
      @pred{compare_dumps/8} but detects the type of plai db by
looking at the dump file extension.".
compare_dumps_auto_detect_db(DF1, DF2, To1, To2, AbsInt, Diff) :-
    detect_restore(DF1,To1),
    detect_restore(DF2,To2),
    compare(To1, To2, AbsInt, Diff).

detect_restore(File, To) :-
    ( file_property(File, type(regular)) ->
        restore_and_copy_db(complete, File, To)
    ;   restore_and_copy_db(registry, File, To)
    ).

db_from_ext('.reg', registry).
db_from_ext('.inc_reg', registry).
db_from_ext('.dump', complete).

:- export(compare_dumps/8).
:- pred compare_dumps(+D1, +D2, +From1, +From2, +To1, +To2, +AbsInt, -Diff)
    #"This predicate compares the content of dump of abstract
     DBs. Variables mean:
* @var{DX}: Dump File X.
* @var{FromX}: Id of the src plai_db.
* @var{ToX}: Id of the copy.
* @var{AbsInt}: Abstract domain that is going to be compared.
* @var{Diff}: Differences between the files.
".
compare_dumps(D1, D2, From1, From2, To1, To2,  AbsInt, Diff) :-
    file_exists(D1),
    file_exists(D2),
    restore_and_copy_db(From1, D1, To1),
    restore_and_copy_db(From2, D2, To2),
    compare(To1, To2, AbsInt, Diff).
% IG: the typeslib database should not be cleaned each comparison
% because it is needed later for determining what kind of error has
% ocurred (loss of precission, incompatible results, etc), with process_diff.

:- export(restore_and_copy_db/3).
restore_and_copy_db(From, File, To) :-
    clean_facts(From),
    restore(From, File),
    copy_db(From, To).

restore(complete, DumpF) :-
    p_dump:restore(DumpF).
restore(registry, DumpD) :-
    not_hidden_directory_files(DumpD, Fs),
    ( % failure-driven loop
      member(F, Fs),
        path_splitext(F, Module, '.reg'),
        path_concat(DumpD, Module, Reg),
        ensure_registry_file(Module, Reg, quiet),
        fail
    ; true).

:- export(not_hidden_directory_files/2).
not_hidden_directory_files(Dir, Files_s) :-
    directory_files(Dir, Fs),
    filter_state_dirs(Fs, Files),
    sort(Files, Files_s).

filter_state_dirs([], []).
filter_state_dirs([F|Fs], FFs) :-  % I do not want files beginning with dot
    filter_file(F), !,
    filter_state_dirs(Fs, FFs).
filter_state_dirs([F|Fs], [F|FFs]) :-
    filter_state_dirs(Fs, FFs).

filter_file(F) :-
    atom_codes(F,X),
    X = [0'.|_].

% TODO: unify with p_dump
clean_facts(complete) :-
    retractall_fact(complete(_, _, _, _, _, _, _)),
    retractall_fact(memo_table(_, _, _, _, _, _)).
clean_facts(registry) :-
    cleanup_p_abs_all.

human_display(X) :-
    %numbervars(X, 0, _),
    display(X).

human_display_list([]).
human_display_list([X|Xs]) :-
    human_display(X), nl,
    human_display_list(Xs).

show_auxiliary_info_list(Sub, AbsInt) :-
    needs(AbsInt,aux_info), !,
    acc_auxiliary_info(AbsInt, Sub),
    dump_auxiliary_info(display_nl).
show_auxiliary_info_list(_Sub,_).

display_nl(typedef(T,TD)) :-
    ( is_new_type(T)  ->
        display(typedef(T,TD)), nl
    ; true ). % don't show the definition if predefined type
