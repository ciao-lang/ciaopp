:- module(plai_db_comparator, [compare/4], [assertions, regtypes, datafacts]).

:- doc(title, "plai_db (answer table) comparator").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "
This module compares instances of plai databases that are present in
plai_db_instances, independently of their representation.

After computing two plai dbs (@var{DB1} and @var{DB2}) with
@tt{compare(DB1, DB2, AbsInt, Diff)}, several types of differences may
appear in a list of elements abs_diff(Id2, AbsInt, DBId2, Sg:Call,
Succ, new)

* modif(Sg:Call, Succ, Succ2) : means that there is a tuple in both
  dbs but the success pattern is not the same in both. It is
  @var{Succ} in DB1 and @var{Succ2} in DB2.

* contained(Sg:Call) : means that the call pattern in DB1 Sg:Call is not in DB1 but it is contained in one more general in DB2

* not_in(Sg:Call) : means there is a tuple for Sg:Call in DB1 but
  there is not in DB2.

* new : means that the tuple of DB2 does not exist in DB1.

Module @ref{Incremental modular analysis sequence checker} is an
example of use of this module.

").

:- use_module(ciaopp(plai/incanal/plai_db_instances), [plai_db_tuple/8]).
:- use_module(library(format), [format/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [append/3]).

:- use_module(ciaopp(plai/domains), [identical_proj/5, abs_sort/3, less_or_equal_proj/5]).
:- use_module(ciaopp(plai/fixpo_ops), [each_identical_abstract/3, each_abs_sort/3]).

:- doc(bug, "First attempt, it does not check memo_table for consistency").

:- data equivalent/4.
:- data abs_diff/6.

:- pred compare(DBId1, DBId2, AbsInt, Diff) : atm * atm * atm * var => atm * atm * atm * list(abs_diff_type)
    #"Compares two previously loaded abstract databases of domain
     @var{AbsInt}, @var{DBId1} and @var{DBId2} to produce a list
     with the differences in @var{Diff}, expressed relative to
     database @var{DBId1}.".
compare(DBId1, _, _, _) :-
    \+ plai_db_tuple(DBId1, _, _, _, _, _, _, _), !,
    format(user_error, 'WARNING: empty db ~w~n', [DBId1]).
compare(_, DBId2, _, _) :-
    \+ plai_db_tuple(DBId2, _, _, _, _, _, _, _), !,
    format(user_error, 'WARNING: empty db ~w~n', [DBId2]).
compare(DBId1, DBId2, AbsInt, Diff) :-
    retractall_fact(abs_diff(_, _, _, _, _, _)),
    retractall_fact(equivalent(_, _, _, _)),
    look_for_differences(DBId1, DBId2, AbsInt),
    gather_differences(DBId1, DBId2, AbsInt, Diff).

look_for_differences(DBId1, DBId2, AbsInt) :-
    ( %failure-driven loop
        plai_db_tuple(DBId1, SgKey, AbsInt, Sg, Call, Succ, Id, _),
        look_for_equivalent(DBId1, SgKey, AbsInt, Sg, Call, Succ, Id, DBId2),
        fail
    ; true).

% First look for a tuple that has the same abstract call substitutions
look_for_equivalent(DBId1, SgKey, AbsInt, Sg, Call, Succ, Id, DBId2) :-
    plai_db_tuple(DBId2, SgKey, AbsInt, Sg2, Call2, Succ2, Id2, _),
    check_same_calls(AbsInt, Sg, Call, Sg2, Call2), !,
    ( check_same_success(AbsInt, Succ, Succ2) ->
        add_equivalent(DBId1, Id, DBId2, Id2)
    ;
        add_difference(Id, AbsInt, DBId1, DBId2, Id2, modif(Sg:Call, Succ, Succ2))
    ).
% There is not an equivalent call
look_for_equivalent(DBId1, _, AbsInt, Sg, Call, _Succ, Id, _DBId2) :-
    add_difference(Id, DBId1, AbsInt, _, _, not_in(Sg:Call)).

add_equivalent(DBId1, Id, DBId2, Id2) :-
    retractall_fact(equivalent(DBId1, Id, _, _)),
    assertz_fact(equivalent(DBId1, Id, DBId2, Id2)).

add_difference(Id1, AbsInt, DBId1, DBId2, Id2, DiffType) :-
    assertz_fact(abs_diff(Id1, AbsInt, DBId1, DBId2, Id2, DiffType)).

gather_differences(DBId1, DBId2, AbsInt, Diff) :-
    findall(D1, difference(D1), Diff1),
    findall(D2, new_in_db(DBId2, DBId1, AbsInt, D2), Diff2),
    append(Diff1, Diff2, Diff).
    
new_in_db(DBId2, DBId1, AbsInt, D) :-
    plai_db_tuple(DBId2, _, AbsInt, Sg, Call, Succ, Id2, _),
    \+ equivalent(DBId1, _, DBId2, Id2),
    \+ abs_diff(_, AbsInt, DBId1, DBId2, Id2, modif(_, _, _)),
    ( contained(Sg, Call, DBId2, Sg2, Call2) ->
        D = abs_diff(Id2, AbsInt, DBId2, Sg:Call, Succ, contained(Sg2:Call2))
    ;
        D = abs_diff(Id2, AbsInt, DBId2, Sg:Call, Succ, new)
    ).

:- pred contained(+Sg, +Call, +DBId, -Sg2, -Call2) #"The call pattern
    @var{Sg}:@var{Call} is strictly more precise than an existing
    call patern in plai_db instance @var{DBId} which is
    @var{Sg2}:@var{Call2}".
contained(Sg, Call, DBId, Sg2, Call2) :-
    % failure-driven loop
    plai_db_tuple(DBId, _, AbsInt, Sg2, Call2, _Succ, _, _),
    less_or_equal_proj(AbsInt, Sg, Call, Sg2, Call2),
    \+ identical_proj(AbsInt, Sg, Call, Sg2, Call2).

difference(D) :-
    abs_diff(Id1, AbsInt, DBId1, DBId2, Id2, DiffType),
    D = abs_diff(Id1, AbsInt, DBId1, DBId2, Id2, DiffType).

:- export(check_same_success/3).
:- pred check_same_success(AbsInt, Succ1, Succ2) : atm(AbsInt)
#"Succeeds if @var{Succ1} and @var{Succ2} are quivalent abstract substitution
patterns.".
check_same_success(_, '$bottom', '$bottom') :- !.
check_same_success(_, ['$bottom'], ['$bottom']) :- !.
check_same_success(AbsInt, Succ, Succ2) :-
    each_abs_sort(Succ,AbsInt,Succ_s),
    each_abs_sort(Succ2,AbsInt,Succ2_s),
    each_identical_abstract(Succ_s, AbsInt, Succ2_s).

:- export(check_same_success_sorted/3).
check_same_success_sorted('$bottom', _, '$bottom') :- !.
check_same_success_sorted(['$bottom'], _, ['$bottom']) :- !.
check_same_success_sorted(Succ1,AbsInt,Succ2) :-
    each_identical_abstract(Succ1, AbsInt, Succ2).

:- export(check_same_calls/5).
:- pred check_same_calls(AbsInt, Sg1, Call1, Sg2, Call2) : atm(AbsInt)
    #"Succeeds if @var{Call1} and @var{Call2} are quivalent call
     patterns for goals @var{Sg1} and @var{Sg2}.".
check_same_calls(AbsInt, Sg, Call, Sg2, Call2) :-
    abs_sort(AbsInt,Call,Call_s),
    abs_sort(AbsInt,Call2,Call2_s),
    identical_proj(AbsInt,Sg,Call_s,Sg2,Call2_s).

:- regtype abs_diff_expl/1.
abs_diff_expl(new).
abs_diff_expl(not_in(_)).
abs_diff_expl(contained(_:_)).
abs_diff_expl(modif(_:_, _, _)).

:- regtype abs_diff_type/1.
abs_diff_type(abs_diff(_Id, _AbsInt, _DBId, _Sg:_Call, _Succ, Expl)) :-
    abs_diff_expl(Expl).
