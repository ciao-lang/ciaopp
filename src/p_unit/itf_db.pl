:- module(itf_db,
    [ assert_itf/5, assert_itf_kludge/2,
      cleanup_itf_db/0,
      current_itf/3,
      retract_itf/5,
      dump_lib_itf/1,
      load_lib_itf/1,
      cleanup_lib_itf/0,
      preloaded_module/2
    ],
    [assertions, isomodes, datafacts]).

:- use_module(engine(io_basic)).
:- use_module(engine(stream_basic), [absolute_file_name/7]).
:- use_module(library(pathnames), [path_split/3, path_splitext/3]).
:- use_module(library(compiler/c_itf), [module_expansion/9]).
:- use_module(ciaopp(p_unit/p_abs), [get_module_from_sg/2]).
:- use_module(ciaopp(p_unit/unexpand), [unexpand_meta_calls/2]).

:- reexport(ciaopp(p_unit/itf_base_db)).

:- doc(bug, "assert_itf_kludge/2 ?").
:- doc(bug, "Missing doc").

cleanup_itf_db:-
    retractall_fact(defines(_,_,_)),
    retractall_fact(imports(_,_)),
    retractall_fact(exports(_,_)),
    retractall_fact(multifile(_,_)),
    retractall_fact(meta(_,_)),
    retractall_fact(dynamic(_)),
    retractall_fact(curr_module(_)),
    retractall_fact(curr_file(_,_)),
    retractall_fact(impl_defines(_,_)),
    % defines_module not cleaned here?, added by IG
    retractall_fact(defines_module(_,_)),
    retractall_fact(defines_module_rev_idx(_,_)).

assert_itf(defined,M,F,A,_Type):- % already expanded
    assertz_fact(defines(F,A,M)).
assert_itf(defines,M,F,A,_Type):-
    functor(Goal0,F,A),
    goal_module_expansion(Goal0, M, Goal),
    functor(Goal,FG,A),
    assertz_fact(defines(FG,A,M)).
assert_itf(imports,_M,F,A,r(IM,EM)) :- !, % reexported predicates reexported
    functor(Goal0,F,A),
    goal_module_expansion(Goal0, EM, Goal),
    % unexpand_meta_calls(Goal1,Goal), % TODO: remove? related with addmodule?
    % TODO: this depends on type_of_goal which, at some point calls current_itf(meta, Goal, Meta)
    assertz_if_needed(imports(Goal,EM)), % TODO: IG missing which imports which
    assertz_if_needed(imports(Goal0,r(IM,EM))). % (unexpanded goal for unexpand.pl)
assert_itf(imports,_IM,F,A,EM):-
    functor(Goal0,F,A),
    goal_module_expansion(Goal0, EM, Goal),
    % unexpand_meta_calls(Goal1,Goal), % TODO: remove? related with addmodule?
    assertz_if_needed(imports(Goal,EM)).  % TODO: IG missing which imports which
assert_itf(exports,M,F,A,_M):-
    functor(Goal0,F,A),
    goal_module_expansion(Goal0, M, Goal),
    assertz_if_needed(exports(Goal,M)).
assert_itf(new_exports,M,F,A,_M):-
    functor(Goal,F,A),
    assertz_if_needed(exports(Goal,M)).
assert_itf(multifile,M,F,A,_DynType):-
    functor(Goal0,F,A),
    goal_module_expansion(Goal0, M, Goal),
    assertz_fact(multifile(Goal,M)).
assert_itf(meta,M,F,A,Meta0):-
    functor(Goal0,F,A),
    goal_module_expansion(Goal0, M, Goal),
    functor(Goal,MF,_),
    Meta0 =.. [_|As],
    Meta =.. [MF|As],
    assertz_fact(meta(Goal,Meta)).
assert_itf(dynamic,M,F,A,_Deftype):-
    functor(Goal0,F,A),
    goal_module_expansion( Goal0 , M , Goal ),
    assertz_if_needed(dynamic(Goal)).
assert_itf(defines_module,M,_,_,Base):-
    ( current_fact(defines_module(Base,M)) ->
        true
    ;
        assertz_fact(defines_module(Base,M)),
        assertz_fact(defines_module_rev_idx(M, Base))
    ).
assert_itf(impl_defines,M,F,A,_DynType):-
    functor(Goal0,F,A),
    goal_module_expansion( Goal0 , M , Goal ),
    assertz_fact(impl_defines(Goal,M)).

assertz_if_needed(imports(Goal,M)) :-
    ( current_fact(imports(Goal, M)) -> true
    ; assertz_fact(imports(Goal,M))
    ).
assertz_if_needed(exports(Goal,M)) :-
    ( current_fact(exports(Goal, M)) -> true
    ; assertz_fact(exports(Goal,M))).
assertz_if_needed(dynamic(Goal)) :-
    ( current_fact(dynamic(Goal)) -> true
    ; assertz_fact(dynamic(Goal))).

assert_itf_kludge(remote,imports(Goal,IM)):-
    ( current_fact(imports(Goal,IM)) -> true
    ; assertz_fact(imports(Goal,IM)) ).

% {ERROR (p_asr): ERROR PROCESSING FACT exports(basiccontrol,\+,1,static,\+goal)
%   from ast file}

goal_module_expansion(if(A,B,C), _basiccontrol, if(A,B,C)) :- !.
goal_module_expansion(','(A,B), _basiccontrol, ','(A,B)) :- !.
goal_module_expansion(';'(A,B), _basiccontrol, ';'(A,B)) :- !.
goal_module_expansion(^(A,B), _basiccontrol, ^(A,B)) :- !.
goal_module_expansion('->'(A,B), _basiccontrol, '->'(A,B)) :- !.
goal_module_expansion(\+A, _basiccontrol, \+A) :- !.
goal_module_expansion(!, _basiccontrol, !) :- !.
goal_module_expansion(Goal, M, GoalExpanded) :-
    % TODO: location/3?
    c_itf:module_expansion(Goal, true, M, _, asr, _, _, GoalExpanded, _Body).

:- pred retract_itf(+Class,_M0,+F,+A,_M)
   # "This predicate allows removing itf information when it is no longer true.
      This can happen for example during program transformation.".
retract_itf(exports,M0,F,A,_M):-
    functor(Goal,F,A),
    retract_fact(exports(Goal,M0)).

current_itf(visible,Goal,X):-
    var(X),
    visible_goal(Goal).
current_itf(visible,F,A):-
    nonvar(A),
    visible_spec(F,A).
current_itf(defines,F,A):-
    current_fact(defines(F,A,_)).
current_itf(defines,F,A):-
    lib_defines(F,A,_).
current_itf(defines_pred,G,M):-
    current_fact(defines(F,A,M)),
    functor(G,F,A).
current_itf(defines_pred,G,M):-
    lib_defines(F,A,M),
    functor(G,F,A).
current_itf(imports,Goal,IM):- % IG change name to imported? do not confuse with compiler
    current_fact(imports(Goal,IM)).
% TODO: use a different predicate for imports relation. Uses of this case of
% current_itf look strange... I.e., if an expanded literal appears in an
% expanded body, then it is obvious that the pred is imported.
current_itf(imports,Goal,IM):-
    lib_imports(Goal,IM).
current_itf(exports,Goal,M):- % IG change name to exported? do not confuse with compiler
    current_fact(exports(Goal,M)). 
current_itf(exports,Goal,M):-
    lib_exports(Goal,M).
current_itf(exports,Goal,user(File)):-
    curr_file(_,user(File)),
    current_fact(defines(F,A,user(File))),
    functor(Goal,F,A).
current_itf(multifile,Goal,M):-
    current_fact(multifile(Goal,M)).
current_itf(multifile,Goal,M):-
    lib_multifile(Goal,M).
current_itf(meta,Goal,Meta):-
    current_fact(meta(Goal,Meta)).
current_itf(meta,Goal,Meta):-
    lib_meta(Goal,Meta).
current_itf(dynamic,Goal,_Deftype):-
    current_fact(dynamic(Goal)).
current_itf(dynamic,Goal,_Deftype):-
    lib_dynamic(Goal).
current_itf(defines_module,M,Base):-
    defines_module_(M, Base).
current_itf(impl_defines,Goal,M):-
    current_fact(impl_defines(Goal,M)).
current_itf(impl_defines,Goal,M):-
    lib_impl_defines(Goal,M).

defines_module_(M, Base) :-
    var(M),
    (current_fact(defines_module(Base, M))
    ; lib_defines_module(Base,M)).
defines_module_(M, Base) :-
    nonvar(M), var(Base),
    (current_fact(defines_module_rev_idx(M, Base))
    ; lib_defines_module_rev_idx(M, Base)).

visible_goal(Goal):-
    current_itf(imports,Goal,_).
visible_goal(Goal):-
    current_itf(defines,F,A),
    functor(Goal,F,A).
visible_goal(Goal):-
    current_fact(multifile(Goal,_)).

visible_spec(F,A):-
    current_itf(defines,F,A).
visible_spec(F,A):-
    current_itf(imports,Goal,_),
    functor(Goal,F,A).
visible_spec(F,A):-
    current_fact(multifile(Goal,_)),
    functor(Goal,F,A).

:- use_module(library(write), [writeq/2]).
:- data lib_defines/3, lib_imports/2, lib_exports/2, lib_multifile/2, lib_meta/2.
:- data lib_dynamic/1, lib_impl_defines/2, lib_defines_module/2.
% reverse indexes
:- data lib_defines_module_rev_idx/2.

:- export(fake_module_name/1).
:- data fake_module_name/1.
%fake_module_name(lib_fake).

dump_lib_itf(Stream):-
    defines(A,B,C),
    \+ fake_module_name(C),
    writeq(Stream,lib_defines(A,B,C)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    imports(A,B),
    writeq(Stream,lib_imports(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    exports(A,B),
    \+ fake_module_name(B),
    writeq(Stream,lib_exports(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    multifile(A,B),
    writeq(Stream,lib_multifile(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    meta(A,B),
    get_module_from_sg(A,M),
    \+ fake_module_name(M),
    writeq(Stream,lib_meta(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    dynamic(A),
    get_module_from_sg(A,M),
    \+ fake_module_name(M),
    writeq(Stream,lib_dynamic(A)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    defines_module(A,B),
    \+ fake_module_name(B),
    writeq(Stream,lib_defines_module(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(Stream):-
    impl_defines(A,B),
    writeq(Stream,lib_impl_defines(A,B)),
    display(Stream,'.'),nl(Stream),
    fail.
dump_lib_itf(_).

%--------------------------------------------------------------------------
:- pred cleanup_lib_itf
   # "Cleans up all facts of lib_* predicates.".
cleanup_lib_itf:-
    retractall_fact(lib_defines(_,_,_)),
    retractall_fact(lib_imports(_,_)),
    retractall_fact(lib_exports(_,_)),
    retractall_fact(lib_multifile(_,_)),
    retractall_fact(lib_meta(_,_)),
    retractall_fact(lib_dynamic(_)),
    retractall_fact(lib_defines_module(_,_)),
    retractall_fact(lib_defines_module_rev_idx(_,_)),
    retractall_fact(lib_impl_defines(_,_)).

%--------------------------------------------------------------------------

:- use_module(library(read), [read/2]).

:- pred load_lib_itf(Stream)
   # "Loads the facts for lib_*/* from the stream @var{Stream}.".
load_lib_itf(Stream):-
    repeat,
    read(Stream,Fact),
    ( Fact = end_of_file ->
        true
    ;
        add_fact(Fact),
        fail
    ).

add_fact(lib_defines_module(A,B)) :- !,
    assertz_fact(lib_defines_module(A,B)),
    assertz_fact(lib_defines_module_rev_idx(B,A)).
add_fact(Fact) :-
    assertz_fact(Fact). % TODO: meta!

%--------------------------------------------------------------------------
:- pred preloaded_module(M,Base) # "Module @var{M} with basename
   @var{Base} is a module already preloaded into CiaoPP.".

preloaded_module(M,Base):-
    lib_defines_module(Base,M).
