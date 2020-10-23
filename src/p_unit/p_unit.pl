:- module(p_unit, [
    preprocessing_unit/3,
    program/2,
    replace_program/2,
    %
    entry_assertion/3,
    exit_assertion/3, % TODO: Not imported anywhere
    native_to_prop/2,
    prop_to_native/2,
    native_to_props_visible/2,
    dynamic_or_unknown_predicate/1,
    % Assertions
    get_assertion/2,
    add_assertions/1, add_assertion/1,
    % Directives
    add_directive/1, erase_directive/1,
    type_of_directive/2, % TODO: check (see code)
    % Predicate index
    pr_key_clean/0,
    pr_key_add/1, % TODO: only from p_unit (and tgd)
    pr_key_get/1, % TODO: only from p_printer (and tgd)
    add_defined_pred/2,
    new_internal_predicate/3,
    new_predicate/3,
    internal_predicate_names/1,
    predicate_names/1,
    %
    language/1,
    %
    push_history/1,
    pop_history/1,
    get_output_path/2,
    %
    inject_output_package/1,
    %
    % TODO: move to clause_db or similar?
    add_output_package/1,
    get_output_package/1,
    add_output_operator/3,
    get_output_operator/3,
    % Comments
    add_comment/1,
    get_comment/1,
    cleanup_comment_db/0,
    % Commented (%) assertions
    cleanup_commented_assrt/0,
    get_commented_assertion/2,
    add_commented_assertions/1,
    add_commented_assertion/1,
    %
    cleanup_punit/0, % TODO: update with other cleanup_* preds here
    %
    get_call_from_call_assrt/7
], [assertions, basicmodes, regtypes, datafacts, hiord]).

:- use_package(ciaopp(p_unit/p_unit_argnames)).

% Documentation
:- use_module(library(assertions/c_itf_props)).

:- use_module(library(messages)).

:- use_module(library(pathnames), [path_splitext/3]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(compiler/c_itf), [opt_suffix/2, set_ciaopp_expansion/1]).

:- use_module(library(hiordlib), [maplist/2]).
:- use_module(library(lists), [member/2]).
:- use_module(library(vndict),
    [ create_dict/2, complete_dict/3,
      varnamedict/1, varnamesl2dict/2
    ]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(engine(internals), [module_concat/3]).

% CiaoPP library
:- reexport(ciaopp(p_unit/p_canonical)).
:- use_module(ciaopp(p_unit/itf_db)).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9]).
:- use_module(ciaopp(p_unit/clause_db)).
:- use_module(ciaopp(p_unit/program_keys),
    [clause_key/2,cleanup_program_keys/0,rewrite_source_clause/3, clause/1]).
:- use_module(ciaopp(p_unit/unexpand),
    [
      generate_unexpanded_data/1
    , clean_unexpanded_data/0
    , unexpand_meta_calls/2
    ]).
:- use_module(ciaopp(p_unit/native),
    [ builtin/2, native_prop_map/3, native_prop_term/1, native_property/2]).

:- reexport(ciaopp(p_unit/p_unit_basic), [type_of_goal/2]).

:- use_module(ciaopp(p_unit/p_asr), [cleanup_pasr/0, preprocessing_unit_opts/4]).
:- use_module(ciaopp(tr_syntax), [cleanup_tr_syntax/0, traverse_clauses/5]).
:- use_module(typeslib(typeslib), [
    legal_user_type_pred/1, 
    insert_user_type_pred_def/2,
    post_init_types/0]).

:- use_module(ciaopp(preprocess_flags)).

% ---------------------------------------------------------------------------

:- on_abort(set_ciaopp_expansion(false)). % TODO: (JF) be careful!

:- initialization(opt_suffix(_,'')). % TODO: (JF) be careful!

%% ---------------------------------------------------------------------------
:- doc(title,"Preprocessing Unit Information Server").

:- doc(author, "The Ciao Development Team").

:- doc(module,"This module loads the preprocessing unit of a file
    to be preprocessed and serves all the information related to it
    to the rest of CiaoPP, including (but not limited to) the source 
    code.").

:- doc(bug,"2. May clauses not of the current module be erased?.").
:- doc(bug,"3. Allow for native(regtype).").
:- doc(bug,"4. Properties native and regtype must now be used in assertions
    with a Pred which is a most general goal.").
:- doc(bug,"5. Every component creating new predicates should use 
    new_predicate here. Check.").
% Done when collecting them:
% :- doc(bug,"6. The calls assertion should be unique.").
:- doc(bug,"7. Builtin tables should be generated off-line!.").
% Seems ok now:
% :- doc(bug,"8. There might be info missing for imported predicates; e.g.,
%       the meta-predicate declarations.").
:- doc(bug,"9. Avoid the need for several native declarations. E.g.,
    for prop var(A) + ( native(free(A)), native(var(A)) ).").
:- doc(bug,"10. Meta terms should not be here.").
%:- doc(bug,"11. visible is not working").
:- doc(bug,"12. Type symbols is not what we want in native_prop").
:- doc(bug,"13. language/1 is a bit naive.").
:- doc(bug,"14. Put make_prop_visible/1 to work.").
:- doc(bug,"15. At least \+ (maybe others?) is not expanded properly.
    See the current kludge in type_of_goal(imported,_) and
    type_of_goal(metapred,_). This shows up in, e.g., peephole.pl").
:- doc(bug,"16. Have a look to expansion of basic types. Things are rather
    strange now:
                 typedef('basic_props:num',[num]).
                 typedef('arit:arithexpression',[num,['basic_props:num']]).
           ").

%% ---------------------------------------------------------------------------

:- pred preprocessing_unit(Fs,Ms,E)
    :  list(Fs,filename) => (list(moddesc,Ms), switch(E))
    # "Loads the preprocessing unit of @var{Fs} defining @var{Ms}.".
:- pred preprocessing_unit(F,M,E) : filename(F) => ( moddesc(M), switch(E) )
    # "Loads the preprocessing unit of @var{F} defining @var{M}.".

preprocessing_unit(Fs,Ms,E):- Fs=[_|_], !,
    preprocessing_unit_list(Fs,Ms,E).
preprocessing_unit(F,M,E):-
    preprocessing_unit_list([F],[M],E).

preprocessing_unit_list(Fs,Ms,E):-
    cleanup_pasr,
    % TODO: fixme (see comment below)
    % init related files db for the closure
    %jcf%-Following comment is temporary (it is called from module/1 already)
    %jcf%       cleanup_code_and_related_assertions,
%       cleanup_punit,
    set_ciaopp_expansion(true),
    % TODO: use '-v' option for debugging
    % note: this includes splitting pred assertions into calls and success
    preprocessing_unit_opts(Fs, [load_mod], Ms, E),
%       assert_curr_modules(Ms),
%       assert_curr_files(Fs,Ms),
    % identify and assert native props
    init_native_props,
    % setup type definitions
    init_types,
    post_init_types,
    % TODO: code seems to work without this; perhaps because some other ensure_registry_file; however it seems necessary at least to upload types from the registry (see patch_registry_file_/3)
    % TODO: this was done just before build_defined_types_lattice/0 (when current_pp_flag(types,deftypes)), is it fine here?
    ( \+ current_pp_flag(intermod,off) ->
        ensure_registry_current_files(quiet) % [IG] mixed modular
    ; true
    ),
    % remove disjunctions and all that stuff
    % TODO: clean pr_key here! otherwise we remove a lot of stuff
    pr_key_clean,
    maplist(normalize_clauses, Ms),
    !,
    set_ciaopp_expansion(false). % TODO: move earlier?
preprocessing_unit_list(_Fs,_Ms,_E):-
    set_ciaopp_expansion(false),
    fail.

% ---------------------------------------------------------------------------

:- pred cleanup_punit # "Clean up all facts that p_unit asserts.".
cleanup_punit :-
    cleanup_program_keys,
    cleanup_tr_syntax,
    %
    cleanup_history,
    %
    retractall_fact(pl_output_op(_, _, _)),
    retractall_fact(pl_output_package(_)),
    %
    retractall_fact(internal_pred_name(_,_,_)),
    retractall_fact(p_unit:native(_,_)),
    retractall_fact(regtype(_,_)).

% assert_curr_files([],[]).
% assert_curr_files([A|As],[M|Ms]):-
%       just_module_name(A,M),
%       asserta_fact(curr_file(A,M)),
%       assert_curr_files(As,Ms).

%% ---------------------------------------------------------------------------

:- use_module(ciaopp(p_unit/p_abs)).

% Fill type definition for all regtypes
init_types:-
    enum_regtype(Head,Prop),
    get_module_from_sg(Head,Module),%% JCF
    \+ preloaded_module(Module,_),  %% JCF: preloaded modules are processed already.
%       displayq( init_types( Head , Prop ) ),nl,
    % definable (i.e., not basic --top, num, etc.-- not [] nor [_|_])
    legal_user_type_pred(Head),
    ( Head==Prop ->
        findall((Head:-Body),
                ( one_type_clause(Head,Body0),
                  unexpand_meta_calls(Body0,Body)
                ), Cls)
    ; Cls=[(Head:-Prop)]
    ),
    ( Cls=[] -> true
    ; insert_user_type_pred_def(Head,Cls)
    ),
    fail.
init_types.

one_type_clause(Head,Body):-
    clause_read(_,Head,Body,_VarNames,_Source,_LB,_LE).
one_type_clause(Head,Body):-
    % in other (imported) modules
    prop_clause_read(_,Head,Body,_VarNames,_Source,_LB,_LE).

%% ---------------------------------------------------------------------------

% TODO: change name?
:- pred program(P,D) :: list(clause) * list(varnamedict) : var * var
    # "@var{P} are the clauses (no directives) of the current module
       and @var{D} their dictionaries.".
program(P,D):-
    findall((clause(H,B),Key,Dict),
             current_fact(source_clause(Key,clause(H,B),Dict)),
            P0),
    split1(P0,P,D).

split1([],[],[]).
split1([(Cl,K,D)|P0s],[Cl:K|Ps],[D|Ds]):-
    split1(P0s,Ps,Ds).

normalize_clauses(M):-
    findall((Cl,Key,Dict),program_clause(M,Cl,Key,Dict),P0),
    split(P0,Cls0,Ds0),
    % --- DTM: This should be separated into 2 tranforms: one to
    %          remove cuts and another to remove disjuntions.
    % TODO: why twice? reuse compiler code instead?
    traverse_clauses(Cls0,Ds0,all,Cls1,Ds1), % TODO: delay clause_key/2 if traverse_clauses/4 do not need them
    traverse_clauses(Cls1,Ds1,all,Cls,Ds),
    assert_program(Cls,Ds).

program_clause(M,Cl,Key,Dict):-
    retract_fact(clause_read(M,Head,Body,VarNames,Source,LB,LE)),
    ( number(Head) ->
        Cl=directive(Body)
    ;
        Cl=clause(Head,Body)
    ),
    % create a clause id and a reference to program source
    % TODO: include somewhere else?
    clause_key(Head,Key), % TODO: this has a counter!
    add_clause_locator(Key,loc(Source,LB,LE)),
    % TODO: "El diccionario de variables de c_itf no esta completo!!" is it ok?
    ( VarNames=[] ->
        create_dict((Head,Body),Dict)
    ; varnamesl2dict(VarNames,Dict0),
      complete_dict(Dict0,(Head,Body),Dict)
    ).

split([],[],[]).
split([(Cl,K,D)|P0s],[Cl:K|Ps],[D|Ds]):-
    split(P0s,Ps,Ds).

assert_program([],[]).
assert_program([Cl:Key|Cls],[D|Ds]):-
    rewrite_source_clause(Cl,Key,Clause), % TODO: use rewrite_source_all_clauses/2?
    add_clause(Key,Clause,D),
    assert_program(Cls,Ds).

% ---------------------------------------------------------------------------

:- pred replace_program(P,D) : list(clause) * varnamedict # "The
   database holding the program is updated by first deleting its
   contents and then adding the clauses in @var{P} and dictionaries in
   @var{D}.".
replace_program(Cls,Ds):-
    % TODO: only clauses, not directives; is it OK? (change done by 'jfc')
%jcf%   retractall_fact(source_clause(_,_,_)),
    pr_key_clean,
    retractall_fact(source_clause(_,clause(_,_),_)),
    add_all_clauses(Cls,Ds).

add_all_clauses([],[]).
add_all_clauses([Cl:Key|Cls],[D|Ds]):-
    add_clause(Key,Cl,D),
    add_all_clauses(Cls,Ds).

add_clause(Key,Cl,D) :-
    assertz_fact(source_clause(Key,Cl,D)),
    generate_pr_key(Cl).

%% ---------------------------------------------------------------------------

% TODO: (JF) review this code
:- doc(hide,language/1).
language(clp):- 
    current_fact(source_clause(_Key,directive(impl_defined('.=.'/2)),_D)),
    !.
language(lp).

% ---------------------------------------------------------------------------
:- doc(section, "History of analysis/transformations (for output name)").

:- use_module(library(lists), [reverse/2]).

:- pred history_item(X) # "History item (in reverse order)".

:- doc(history_item(X), "The history of analysis/transformation steps,
   which is used to assign a name (e.g. @tt{filename_shfr_pred_op.pl})
   to the output file in @pred{output/0}").

:- data history_item/1.

:- pred cleanup_history # "Cleanup history items.".
cleanup_history :-
    retractall_fact(history_item(_)).

:- pred push_history(X) : atom(X) # "Push history item @var{X}.".
push_history(X) :-
    asserta_fact(history_item(X)).

:- pred pop_history(X) : atom(X) # "Pop history item @var{X}.".
pop_history(X) :-
    retract_fact(history_item(X)).

% TODO: if we export history_item (or similar) this predicate could be moved to another module
:- pred get_output_path(UseHistory, Path) => (atm(UseHistory),atm(Path))
   # "Default output file name based. Encode analysis/transformation
      history if @var{UseHistory} is @tt{yes}.".

get_output_path(UseHistory, OptFile) :-
    % Base and extension of the main file
    % TODO: allow a different main file?
    ( curr_file(SrcFile, _) -> true ; fail ), % (first)
    path_splitext(SrcFile, Base, Ext),
    % Get list of history (analysis/transformation) items, for name
    ( UseHistory = yes ->
        findall(X, history_item(X), Ls0),
        ( Ls0 = [] -> Ls = [none]
        ; reverse(Ls0, Ls)
        )
    ; Ls = []
    ),
    % Compose name
    atom_concat_with_underscore([Base|Ls], File),
    atom_concat(File, '_co', FileCo),
    ( current_pp_flag(output_lang, intermediate) ->
        Ext2 = '.pl'
    ; Ext2 = Ext
    ),
    atom_concat(FileCo, Ext2, OptFile).

atom_concat_with_underscore([L], L) :- !.
atom_concat_with_underscore([A|As], L) :- !,
    atom_concat_with_underscore(As, AsC),
    atom_concat(A, '_', A2),
    atom_concat(A2, AsC, L).
atom_concat_with_underscore(L, L).

%% ---------------------------------------------------------------------------

:- pred entry_assertion(Goal,Call,Name) :: callable(Goal)
    # "There is an entry assertion for @var{Goal} with call
       pattern @var{Call}, uniquely identifiable by @var{Name}.".
entry_assertion(Goal,Call,Name):-
    \+ current_pp_flag(entry_point, calls),
    curr_module(M),
    assertion_read(Goal,M,_Status,entry,Body,_Dict,_S,_LB,_LE),
    assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
    ( builtin(entry_point_name(Goal,Name),Entry),
      member(Entry,Comp)
    -> true
    ; functor(Goal,Name,_)
    ).
entry_assertion(Goal,Call,Name):-
    \+ current_pp_flag(entry_point, entry),
    curr_module(M),
    assertion_read(Goal,M,_Status,Type,Body,_Dict,_S,_LB,_LE),
    (Type == success; Type == comp),
    assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
    ( builtin(entry_point_name(Goal,Name),Entry),
      member(Entry,Comp)
    -> true
    ; functor(Goal,Name,_)
    ).
entry_assertion(Goal,Call,Name):-
    \+ current_pp_flag(entry_point, entry),
    curr_module(M),
    get_call_from_call_assrt(Goal,M,_Status,Call,_,_,_),
    functor(Goal,Name,_).

:- pred get_call_from_call_assrt(Sg,M,Status,Call,Source,LB,LE)
   # "Returns in @var{Call}, upon backtracking call patterns from calls
   assertions related to @var{Sg}, in module @var{M}. Also takes care of 
 disjunctions.".
% Removes call patterns for which there exists a success
get_call_from_call_assrt(Sg,M,Status,OneCall,Source,LB,LE) :-
    assertion_read(Sg,M,Status,calls,Body,_Dict,Source,LB,LE),
    assertion_body(Sg,_Compat,FullCall,_Succ,_Comp,_Comm,Body),
    get_single_call(FullCall,OneCall),
    filter_call(OneCall,Sg).

get_single_call([(A;As)],AOut):-!,
    get_one_disjunct((A;As),AOut).
get_single_call(A,A).

get_one_disjunct((A;_),A).
get_one_disjunct((_;As),A):-!,
    get_one_disjunct(As,A).
get_one_disjunct(A,A).

% Do not take call patterns for which there exists success P:C => S
filter_call(Call,Sg) :- 
    copy_term((Sg,Call),(CpSg,CpCall)),
    assertion_read(CpSg,_M,_Status,success,Body,_Dict,_Source,_LB,_LE),
    assertion_body(CpSg,_Compat,Call_x,_InfoSucc,_Comp,_Comm,Body),
    variant(CpCall,Call_x),
    !,fail.
filter_call(_,_).

%% ---------------------------------------------------------------------------
 % TODO: Not imported anywhere and not used here, remove??
:- pred exit_assertion(Goal,Call,Succ) :: callable(Goal)
    # "There is an exit assertion for @var{Goal} with call
       pattern @var{Call} and success pattern @var{Succ}.".
exit_assertion(Goal,Call,Succ):-
    ( Type=pred ; Type=success ),
    ( Status=true ; Status=trust ),
    assertion_read(Goal,_M,Status,Type,Body,_Dict,_S,_LB,_LE),
    assertion_body(Goal,_Compat,Call,Succ,_Comp,_Comm,Body).

%% ---------------------------------------------------------------------------
%% :- reexport(ciaopp(p_unit/p_unit_basic), [type_of_goal/2]).

:- pred dynamic_or_unknown_predicate(Goal)
    # "@var{Goal} is an atom for a predicate such that all its clauses might
 not be available or may change in the program unit.".
dynamic_or_unknown_predicate(Goal):- type_of_goal(imported,Goal), !.
% TODO: for imported extract module name from goal and check if is loaded.
dynamic_or_unknown_predicate(Goal):- type_of_goal(dynamic,Goal), !.
dynamic_or_unknown_predicate(Goal):- type_of_goal(multifile,Goal), !.
dynamic_or_unknown_predicate(Goal):- type_of_goal(impl_defined,Goal), !.

% ---------------------------------------------------------------------------
:- doc(section, "Assertions").

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db), [
    add_assertion_read/9,
    ref_assertion_read/10]).

get_assertion(Goal, Ass) :-
    Ass = as${module => M,
        status => Status,
        type => Type,
        head => Key,
        compat => Compat,
        call => Call,
        succ => Succ,
        comp => Comp,
        dic => Dic,
        comment => Comment,
        locator => Loc},
    Loc = loc(S, LB, LE),
    ref_assertion_read(Goal, M, Status, Type, Body, Dic, S, LB, LE, _ARef),
    assertion_body(Key, Compat, Call, Succ, Comp, Comment, Body).

:- export(assertion_set_status/3).
assertion_set_status(X0, Status, X) :-
    X0 = as(M,_,Type,Head,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere),
    X = as(M,Status,Type,Head,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere).

:- export(assertion_set_head/3).
assertion_set_head(A0, Head, A) :-
    A0 = as(M,Status,Type,_,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere),
    A = as(M,Status,Type,Head,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere).

:- export(assertion_set_calls/3).
assertion_set_calls(X0, Calls, X) :-
    X0 = as(M,Status,Type,Head,Co,_,Success,Comp,Dic,Loc,Comm,Fromwhere),
    X = as(M,Status,Type,Head,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere).

:- export(assertion_set_success/3).
assertion_set_success(X0, Success, X) :-
    X0 = as(M,Status,Type,Head,Co,Calls,_,Comp,Dic,Loc,Comm,Fromwhere),
    X = as(M,Status,Type,Head,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere).

:- export(assertion_set_comp/3).
assertion_set_comp(X0, Comp, X) :-
    X0 = as(M,Status,Type,Head,Co,Calls,Success,_,Dic,Loc,Comm,Fromwhere),
    X = as(M,Status,Type,Head,Co,Calls,Success,Comp,Dic,Loc,Comm,Fromwhere).

:- pred add_assertions(AssrtList) : list(AssrtList)
   # "Add assertions list @var{AssrtList} to internal DB.".

add_assertions([]).
add_assertions([A|As]) :-
    add_assertion(A),
    add_assertions(As).

:- pred add_assertion(Assrt) # "Add assertion @var{Assrt} to internal DB.".
add_assertion(As) :-
    As = as${module => M,
        status => Status,
        type => Type,
        head => Head,
        compat => Compat,
        call => Calls,
        succ => Succ,
        comp => Comp,
        dic => Dic,
        locator => AsLoc,
        comment => Com},
    AsLoc = loc(S, LB, LE),
    assertion_body(Head, Compat, Calls, Succ, Comp, Com, Body),
    add_assertion_read(Head, M, Status, Type, Body, Dic, S, LB, LE),
    !.
add_assertion(As) :-
    error_message("Internal Error: add_assertion: Could not add ~p", [As]).

% ---------------------------------------------------------------------------
:- doc(section, "Directives").

:- use_module(library(vndict), [null_dict/1]).

:- pred add_directive(C) : term(C)
# "The directive @var{C} is added to the program data base. This
   directive will be considered as read from the program, i.e.,
   analizers, transformations and output will use/show it.".
% E.g., add_directive(use_module(...)), add_directive(redefining(append/3)).
add_directive(Body) :-
    ( current_fact(source_clause(_Key, directive(Body), _Dict)) -> % TODO: sure?
        true
    ; null_dict(Dict),
      Key = '\6\newdirective', % TODO: key is not unique?!
      assertz_fact(source_clause(Key, directive(Body), Dict))
    ).

:- pred erase_directive(D) : term(D)
    # "Erase directive @var{D} (previously added with @pred{add_directive/1}".
erase_directive(Body) :-
    Key = '\6\newdirective',
    retractall_fact(source_clause(Key, directive(Body), _)).

% TODO: this is using clause_read, which is removed when code is normalized!
:- pred type_of_directive(Type,Body) 
    # "There is a directive of the form @var{:- Type Body}
       (of arity one).".
type_of_directive(Type,Body):-
    functor(D,Type,1),
    arg(1,D,Body),
    clause_read(_M,0,D,_VarNames,_Source,_LB,_LE).

% ---------------------------------------------------------------------------
:- doc(section, "Predicate index").

% TODO: merge with itf_db?

:- use_module(ciaopp(p_unit/program_keys), [predkey/1]).
:- use_module(ciaopp(p_unit/unexpand), [add_head_unexpanded_data/1]).
:- use_module(ciaopp(p_unit/itf_db), [assert_itf/5]).

:- data pr_key/1.

:- pred pr_key_clean # "Removes all information about predicate order.".
pr_key_clean :-
    retractall_fact(pr_key(_)).

:- pred pr_key_get(K) => predkey(K) # "Current predicate keys".
pr_key_get(K) :- pr_key(K).

:- pred pr_key_add(K) => predkey(K) # "Add a predicate key (once)".
pr_key_add(K) :-
    ( pr_key(K) -> true
    ; assertz_fact(pr_key(K))
    ).

generate_pr_key(Cl) :-
    Cl = clause(H,_),
    !,
    functor(H, F, A),
    functor(Key, F, A),
    pr_key_add(Key), % (only added once)
    ( add_head_unexpanded_data(H) -> true ; true ). % TODO: it was marked as a kludge, why? % TODO: may it fail?
generate_pr_key(_). % TODO: not for directives

% TODO: used only in some transformations, check again
:- pred add_defined_pred(ClKey, M) : (term(ClKey), atm(M))
# "Add the necessary data in itf_db (and @pred{pr_key/1}) to define
  the predicate @var{ClKey} in the module @var{M}.".
add_defined_pred(Key, M) :-
    \+ pr_key(Key),
    functor(Key, F, A),
    assert_itf(defined, M, F, A, _),
    !,
    assertz_fact(pr_key(Key)).
add_defined_pred(_, _).
 
:- pred new_predicate(+F,+A,-NewF)
    # "Checks wether there is a predicate @var{F}/@var{A} in the
       program and returns @var{NewF} so that there is no predicate
       @var{NewF}/@var{A} in the program.".
new_predicate(F,A,NewF):-
    curr_module(M),
    new_predicate_name(F,F,A,0,NewF),
    assert_itf(defined,M,NewF,A,_).
    
new_predicate_name(TmpF,F,A,N,NewF):-
    current_itf(visible,TmpF,A), !,
    N1 is N+1,
    name(N1,S1),
    "_"=[S],
    atom_codes(Suffix,[S|S1]),
    atom_concat(F,Suffix,TmpF1),
    new_predicate_name(TmpF1,F,A,N1,NewF).
new_predicate_name(NewF,_F,_A,_N,NewF).

:- pred predicate_names(-list)
    # "Returns the specs of predicates defined in the current module.".
predicate_names(Names):-
    findall(F/A, current_itf(defines,F,A), Names).

:- data internal_pred_name/3.

:- doc(hide,internal_predicate_names/1).
internal_predicate_names(Names):-
    findall((F,A,NF), current_fact(internal_pred_name(F,A,NF)), Names).

:- doc(hide,new_internal_predicate/3).

% this checks clashes with current module predicates, but not between
% internal names (which are names created by CiaoPP, not module-expanded)
new_internal_predicate(F,A,NewF):-
    current_fact(internal_pred_name(F,A,NewF)), !.
new_internal_predicate(F,A,NewF):-
    ( curr_module(user(_)) -> % TODO: "(user(_), user)" is duplicated elsewhere
        M = user
    ; curr_module(M)
    ),
    module_concat(M,F,MF),
    new_predicate_name(MF,MF,A,0,NewF0),
    ( MF==NewF0 -> 
      NewF=F
    ; NewF=NewF0,
      asserta_fact(internal_pred_name(F,A,NewF)) % TODO: why not assertz_fact? (JF)
    ).

% ---------------------------------------------------------------------------
:- doc(section, "Native props").

:- use_module(library(streams)).

:- redefining(native/2). % also in basic_props % TODO: rename?
:- data native/2.
:- data regtype/2.

% Fill p_unit:native/2 and regtype/2 from assertions
init_native_props:-
    % (failure-driven loop)
%Nop!   current_itf(visible,Goal,_),
    % only prop assertions
    % TODO: (IC) is ":- prop p(X). :- comp p(X) + native." recognized as a native prop?
    %   possible fix: check that it is prop in one assertion_read/9 query ask for native in another
    assertion_read(Goal,_M,_,prop,Body,_,_,_,_),
    assertion_body(Goal,_Compat,_Call,_Succ,Comp,_Comm,Body),
    % should assert most general goals?
    % can be native several times
    ( builtin(native(Goal,Prop),Native),
      member(Native,Comp),
%         displayq( native_props( Goal , Prop ) ), nl,
      asserta_fact(p_unit:native(Goal,Prop))
    ; true
    ),
    % can be regtype only once
    ( builtin(regtype(Prop0),Regtype),
      member(Regtype,Comp) ->
        unexpand_meta_calls(Prop0,Type), % TODO: why? (JF)
        % displayq(regtype(Goal,Type)), nl,
        asserta_fact(regtype(Goal,Type))
    ; true
    ),
    fail.
%% init_native_props:-
%%         current_fact(regtype(Head,Prop)),
%%         display(regtype(Head,Prop)), nl,
%%      fail.
init_native_props.

% enum_regtype(-Goal, -NProp)
enum_regtype(Goal, NProp) :-
    current_fact(regtype(Goal,NProp0)),
    % TODO: equivalent to prop_to_native/2 in this case
    ( prop_to_native_(Goal,NProp) -> true
    ; NProp=NProp0
    ).

:- pred prop_to_native(+Prop,-NProp) => callable * native_prop_term
   # "Obtain the native property (lit) @var{NProp} that corresponds to
   the (lit) @var{Prop} user predicate.".

prop_to_native(Prop,_NProp):-
    var(Prop), !, throw(error(instantiation_error(Prop), prop_to_native/2)).
prop_to_native(Prop,NProp2):-
    current_fact(regtype(Prop,NProp0)), !,
    NProp2=regtype(NProp),
    ( prop_to_native_(Prop,NProp) -> true % TODO: why?
    ; NProp=NProp0
    ).
prop_to_native(Prop,NProp):-
    prop_to_native_(Prop,NProp).

prop_to_native_(Prop,NProp):-
    current_fact(p_unit:native(Prop,NProp)).
prop_to_native_(Prop,NProp):-
    native_property(Prop,NProp). % builtin tables

:- pred native_to_prop(+NProp,-Prop) => native_prop_term * callable
   # "Obtain the user predicate (lit) @var{Prop} that corresponds to
   the native property (lit) @var{NProp}.".

% TODO: why? simplify
native_to_prop(NProp2,Prop) :-
    ( NProp2 = regtype(NProp) -> RegType=yes ; NProp=NProp2, RegType=no ),
    %
    ( current_fact(p_unit:native(Prop0,NProp)) -> Prop=Prop0 % TODO: bad indexing
    ; native_property(Prop0,NProp) -> Prop=Prop0 % builtin tables % TODO: bad indexing
    ; RegType=yes, current_fact(regtype(Prop0,NProp)) -> Prop=Prop0 % TODO: bad indexing
    ; fail
    ).

%% ---------------------------------------------------------------------------

:- pred native_to_props_visible(Props,Goals) :: list(callable) * list(callable)
    # "Maps native @var{Props} into their corresponding @var{Goals}
      visible in the current module.".
native_to_props_visible([],[]).
native_to_props_visible([I|Info],OutputUser):-
    native_to_props_visible_(I,OutputUser,OutputUser1),
    native_to_props_visible(Info,OutputUser1).

native_to_props_visible_(Prop,OutputUser,OutputUser1):-
    native_prop_map(Prop,P,Vars), !,
    each_to_prop(Vars,P,OutputUser,OutputUser1).
native_to_props_visible_(Prop,[O|OutputUser],OutputUser):-
    native_to_prop_visible(Prop,O).

each_to_prop([V|Vars],P,[O|OutputUser],OutputUser1):-
    functor(Prop,P,1),
    arg(1,Prop,V),
    native_to_prop_visible(Prop,O),
    each_to_prop(Vars,P,OutputUser,OutputUser1).
each_to_prop([],_P,OutputUser,OutputUser).

% TODO: document why?
native_to_prop_visible(NProp,Prop):-
    native_to_prop(NProp,Prop),
    current_itf(visible,Prop,_), !.
native_to_prop_visible(NProp,Prop):-
    native_property(Prop,NProp), !. % builtin tables % TODO: bad indexing
% should be:
%% native_to_prop_visible(NProp,Prop):-
%%      native_to_prop(NProp,Prop), !,
%%      make_prop_visible(Prop).
native_to_prop_visible(NProp,NProp).

% % TYPE_SYMBOLS_NOT_WHAT_WE_WANT
% native_to_prop_visible(NProp,Prop):-
%       functor(NProp,T,1),
% % not really: should check that it is indeed a type!!!
%       rule_type_symbol(T), !,
%       Prop=NProp.
% native_to_prop_visible(NProp,NProp):-
%       curr_module(M),
%       builtin_package(B),
%       ( clause_read(M,0,use_package(B),_,_Source,_LB,_LE)
%       -> true
%        ; assertz_fact( clause_read(M,0,use_package(B),no,0,0,0) )
%       ).

% make_prop_visible(Prop):-
%       functor(Prop,F,A),
%       extract_module(F,M),
%       module_spec(Spec,M), % if it was reversible!
%       functor(G,F,A),
%       assert_itf_kludge(p_unit,imports(F,Spec)).

% ---------------------------------------------------------------------------
:- doc(section, "Inject packages for output (post-preprocessing unit)"). % TODO: per module?

:- use_module(engine(stream_basic), [absolute_file_name/7]).

:- pred inject_output_package(A) : atm(A)
   # "Inject the package @var{A} in the current program database
      (including the output package list). The necesary information
      from these packages is loaded for correct treatment and
      unexpansion.".

inject_output_package(A) :-
    ( curr_file(_, M) -> true
    ; error_message("inject_output_package/1 with no loaded module"),
      fail
    ),
    ( get_output_package(A) -> % already loaded
        true
    ; absolute_file_name(library(A),'_opt','.pl','.',_,File,_),
      load_package_info(M, File),
      add_output_package(A)
    ).

load_package_info(M, File) :-
    load_package_info_(File, [load_pkg_from(M)]),
    % TODO: update unexpanded data?
    clean_unexpanded_data,
    generate_unexpanded_data(M).

load_package_info_(File, Opts) :-
    set_ciaopp_expansion(true), % TODO: try to avoid this
    ( preprocessing_unit_opts([File], Opts, _, _E) -> true ; true ), % TODO: can it fail?
    fail.
load_package_info_(_File, _Opts) :-
    set_ciaopp_expansion(false).

% ---------------------------------------------------------------------------
:- doc(section, "Packages that must be included in the output"). % TODO: per module?
% TODO: be careful! this cannot work for all packages (JF)

% TODO: delay "load_package_info/1"?

:- data pl_output_package/1.

:- pred get_output_package(X) # "@var{X} is a package that will be
   included in the output (@tt{module} directive).".
get_output_package(X) :-
    pl_output_package(X).

:- pred add_output_package(A) : atm(A)
   # "Add the package @var{A} to the output packages list".

add_output_package(A) :-
    ( pl_output_package(A) ->
        true
    ; assertz_fact(pl_output_package(A))
    ).

% ---------------------------------------------------------------------------
:- doc(section, "Operators that must be included in the output"). % TODO: per module?

:- data pl_output_op/3.

:- pred add_output_operator(Prec, Type, OP) : (int(Prec),atm(Type),atm_or_atm_list(OP))
   # "Define an operator for output (same arguments as in @pred{op/3}).".

add_output_operator(A, B, C) :-
    asserta_fact(pl_output_op(A, B, C)). % TODO: why not assertz_fact? (JF)

:- pred get_output_operator(Pred, Type, OP) : (int(Prec),atm(Type),atm_or_atm_list(OP))
   # "Enumerate output operators (same arguments as in @pred{op/3}).".

get_output_operator(A,B,C) :-
    current_fact(pl_output_op(A,B,C)).

% ---------------------------------------------------------------------------
:- doc(section, "Comment DB"). % TODO: per module?
% Note: this is a simplified version for the current uses (see older
%   version in Attic/ for more potential features)

:- pred comment_db(Comment) : string(Comment)
   # "Text comments, added at the beginning of the module output".

:- data comment_db/1.

:- pred cleanup_comment_db # "Cleans up the comment db".
cleanup_comment_db :-
    retractall_fact(comment_db(_)).

:- pred add_comment(Comment) : string(Comment)
   # "Add comment to the comment db".
add_comment(Comment) :-
    assertz_fact(comment_db(Comment)).

:- pred get_comment(Comment) => string(Comment)
   # "Retrieves comments from the comment db".
get_comment(Comment) :-
    current_fact(comment_db(Comment)).

% ---------------------------------------------------------------------------
:- doc(section, "Commented (%) assertions").

:- data commented_assrt/1.

cleanup_commented_assrt :-
    retractall_fact(commented_assrt(_)).

:- pred add_commented_assertions(A) : list(A)
   # "Add the assertions list @var{A} to the commented assertions DB.".
add_commented_assertions([]).
add_commented_assertions([A|As]) :-
    add_commented_assertion(A),
    add_commented_assertions(As).

% TODO: changing 'fromwhere' may be avoided
:- pred add_commented_assertion(A) : term(A)
    # "Add assertion @var{A} to the commented assertions DB.".
add_commented_assertion(A) :-
    A = as${module => M, status => S, type => T, head => H, compat => C,
        call => Ca, succ => Su, comp => Co, dic => D,
        locator => L, comment => Com},
    !,
    A1 = as${module => M, status => S, type => T, head => H, compat => C,
        call => Ca, succ => Su, comp => Co, dic => D,
        locator => L, comment => Com, fromwhere => commented},
    assertz_fact(commented_assrt(A1)).
add_commented_assertion(A) :-
    error_message("INTERNAL ERROR: add_commented_assertion: "||
        "~q is not a valid assertion", [A]).

get_commented_assertion(ClKey, As) :-
    As = as${head => ClKey},
    current_fact(commented_assrt(As)).

