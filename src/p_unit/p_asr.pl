:- module(p_asr, [
    preprocessing_unit_opts/4,
    do_cache/0,
    show_asr/1,
    cleanup_code_and_related_assertions/0,
    cleanup_pasr/0,
    load_related_files/2,
    load_lib_sources/1,
    gen_lib_sources/1, % TODO: do_cache/0?
    loaded_lib_sources/0,
    cleanup_lib_sources/0,
    % regtypes
    preprocessing_opts/1
], [
    assertions,
    basicmodes,
    regtypes,
    datafacts,
    hiord,
    ciaopp(ciaopp_options)
]).

%% :- doc(doinclude,assertion_read/9).
%% :- doc(doinclude,clause_read/7).

:- doc(title, "Assertion processing library").

:- doc(author, "Manuel Hermenegildo").
:- doc(author, "Francisco Bueno").

:- doc(module, "

This library processes the @tt{.asr} files @cindex{.asr files},
which are a cache of the assertions relevant to the exported predicates of a
file. To be able to correctly interpret such assertions, the definitions of
the exported and local properties transitively used by the
exported properties are also cached. This information forms the @em{assertion
interface} @cindex{assertion interface} of the file.

Currently, @tt{.asr} files have the assertions for exported predicates and
all property definitions plus all assertions related to properties. This is
a superset of the assertion interface, but it is easier to treat.

For the purpose of preprocessing the current module, more than its assertion
interface is required. In this case, the @em{preprocessing unit} of
the file should be gathered together. @cindex{preprocessing unit} 
Currently, a superset of the preprocessing unit is put together by this
module. It is made up of the current module source, the assertions for
predicates exported by the related files, the properties defined in the
related files and their assertions, and the assertions for exported predicates,
the properties and their assertions in files transitively imported by the
related files, up to a file that does not export any property.
Note that this is a superset of the
preprocessing unit, since not all such properties may be needed to
interpret the assertions imported by the current module (and the assertions
for predicates exported by non-related files are useless).

The data collected by the predicates exported by this library is asserted in
different modules. If you want to have access to it, you may want to consider
importing libraries @lib{ciaopp/p_unit}, @lib{ciaopp/p_unit/itf_db}, 
@lib{ciaopp/p_unit/assrt_db}, or @lib{ciaopp/p_unit/clause_db}.

").

%% The preprocessing unit is made up of the file code, the assertion
%% interfaces of modules imported (which are called the @em{related
%% files}), and the definitions of the exported properties and of all
%% local properties transitively used by the exported properties for
%% files which export a property transitively used by one of the exported
%% properties of the related files.

:- doc(bug, "1. Should expand module qualifications in the
   relevant directives: initialization, on_abort, ... (multifile, dynamic,
    data, and meta_predicate are handled via itf_db.").

:- doc(bug, "2. Should go into higher order properties and check the
   arguments for import/export also (and should probably look at the
   meta-predicate declarations for these)?").

:- doc(bug, "3. Opaque properties are not handled yet.").

:- doc(bug, "4. Save assertion heads WITH modes (non-normalized) and 
   normalize them only when asserting in the database.").

:- doc(bug, "5. No way of expanding when reading the .asr. Currently
   not reading them!").

:- doc(bug, "6. Add support for something like the ciaoc -u option.").

%% :- doc(bug,"7. Several copies of the same assertions remain in DB.").

:- doc(bug, "8. Have to cleanup code: reduce asserts.").

%% Solved:
%% :- doc(bug,"9. Currently, if a related file does not export a property
%%    the transitive closure from this file does NOT occur: this is not
%%    correct. Now solved.").
%% :- doc(bug,"10. Implicit importation of builtin modules from another 
%%      builtin module does not work: properties are not read in. This is 
%%      relevant when using package pure for properties callable/1 and iso/1 in
%%      basiccontrol. This was part of the previous bug: now solved.").

%% Solved with set_ciaopp_expansion(true)
%% :- doc(bug,"11. Things like this won't work:
%%    current_itf(imports,,(rt_module_exp(_483,fact,mmatrixpaco,-,fail,_488),
%%                          set_fact(_488)),_197)
%%    .").

:- doc(bug, "12. Should properties be defined only in terms of other
    properties? Currently, if this is not the case, predicates used
    in the definition of properties are not cached.").

:- doc(bug, "13. The modedef of parametric modules that may appear in the
    output will be wrong since call/2 is module expanded for the current
    module instead of for the proper hiord_rt:call/2.").

:- doc(bug, "14. When saving the assertions of dynamic.pl:
    WARNING: (lns 343-345) Predicate current_predicate/1 undefined 
    in source").

% :- doc( bug, "15. When loading an user file (no module
%    declaration), the error:
%    call basename(prelude.pl,user(/usr/cvs/Benchmarks/ciaopp/types/headunify))
%    ?  {ERROR: atomic_basic:atom_codes/2, arg 1 - expected atom, found
%    user(...)} appears" ).

% ===========================================================================

:- use_package(ciaopp(p_unit/p_unit_argnames)).

% Documentation
:- use_module(library(assertions/c_itf_props)).

:- use_module(ciaopp(p_unit/p_canonical)).
:- use_module(ciaopp(frontend_driver), [
    detect_language/2,
    translate_input_file/5]).

:- use_module(library(pathnames), [path_split/3, path_splitext/3]).
:- use_module(library(compiler/c_itf), [defines/3]).
:- use_module(library(formulae), [asbody_to_conj/2]).
:- use_module(engine(runtime_control), [module_split/3]).

:- use_module(ciaopp(p_unit), [add_output_operator/3, add_output_package/1]).
:- use_module(ciaopp(p_unit), [add_assertions/1, add_commented_assertion/1, get_assertion/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2, set_pp_flag/2]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

:- use_module(library(aggregates), [findall/3]).

% TODO: merge c_itf here, merge second pass with compiler
:- use_module(library(compiler/c_itf), [
    activate_translation/3, cleanup_c_itf_data/0,
    module_expansion/9, location/3,
    clause_of/7,
    comp_defines/1, defines/5, defines_module/2, def_multifile/4,
    c_itf_internal_pred/2, c_itf_internal_pred_decl/1,
    exports/5, false/1, imports_pred/7,
    module_error/0, module_error/1, end_goal_trans/1,
    process_file/7,
    restore_defines/5,
    restore_imports/5,
    restore_multifile/4,
    imports/5,
    meta_args/2,
    dyn_decl/4
   ]).
:- use_module(library(compiler/translation),
        [expand_clause/6, del_goal_trans/1, del_clause_trans/1]).
:- use_module(library(ctrlcclean), [ctrlc_clean/1]).
:- use_module(library(errhandle),  [error_protect/2]).
:- use_module(library(fastrw),     [fast_read/2, fast_write/2]).
:- use_module(library(messages)).
:- use_module(library(read), [read/2]).
%% :- use_module(library(system),
%%      [fmode/2,chmod/2,file_exists/1,file_exists/2,delete_file/1]).
:- use_module(library(system), [working_directory/2]).
:- use_module(library(pathnames), [path_split/3]).
:- use_module(library(lists),  [member/2]).
:- use_module(library(pathnames), [path_basename/2, path_splitext/3]).
:- use_module(engine(stream_basic)).
:- use_module(engine(stream_basic), [absolute_file_name/7]).
:- use_module(engine(io_basic)).
:- use_module(library(stream_utils), [write_string/1]).
:- use_module(engine(messages_basic), [message/2]).

% Own libraries
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/assrt_db)).
:- use_module(ciaopp(p_unit/assrt_norm)).
:- use_module(ciaopp(p_unit/clause_db)).
:- use_module(ciaopp(p_unit/itf_db), [
    current_itf/3,
    assert_itf/5,
    curr_file/2,
    preloaded_module/2,
    dump_lib_itf/1,
    load_lib_itf/1]).

% asr files
:- use_module(ciaopp(p_unit/aux_filenames), [get_module_filename/3]).

%% ---------------------------------------------------------------------------
:- pred asr_version/1 :: atm
# "Contains a version number which identifies
   the @tt{.asr} files associated with this version of the assertion
   library. Should be changed every time changes are made which render
   the @tt{.asr} files incompatible, since this forces recomputation
   of all such files.".

asr_version('5.0').

%% ---------------------------------------------------------------------------
:- pred cleanup_code_and_related_assertions/0
# "Cleans up data asserted by assertion/code reader/normalizer.".

cleanup_code_and_related_assertions :-
    cleanup_c_itf_data,
    cleanup_clause_db,
    cleanup_assrt_db.

%% ---------------------------------------------------------------------------

:- regtype filenames/1.
filenames(X) :- filename(X).
filenames(X) :- list(filenames, X).

:- regtype preprocessing_opts/1
   # "Defines the possible options when loading a module:
@begin{itemize}
@item load_pkg_from(M): Load package (ignore assertions), 
       all facts are added as if they were imported from M.
@item '-v': Produce verbose output for tracing.
@item '-d': Produce verbose output for debugging.
@end{itemize}".

preprocessing_opts('-v').
preprocessing_opts('-d').
preprocessing_opts(load_pkg_from(_)).

:- pred preprocessing_unit_opts(in(Fs), in(Opts), out(Ms), out(E))
    :: filenames * list(preprocessing_opts)
    * moddesc * switch
# "This is the main entry point to the @concept{assertion reader/normalizer}. 
   It accepts some options in @var{Opts}. In particular, @tt{'-v'}
   produces verbose output for debugging. Also passes on the options
   in @var{Opts} to pass two of the assertion normalizer.

   With the default options it does the following:
   @begin{itemize}
   @item Reads all declarations and code in @var{Fs} and leaves everything asserted 
     in the database. Clauses are stored in @pred{clause_db:clause_read/7}.
     Assertions are normalized and stored in @pred{assrt_db:assertion_read/9}.
     @var{Ms} are the modules names defined by @var{Fs}.

   @item Also, it reads and normalizes assertions @em{of the exported
     predicates} in all files related to each file in @var{Fs} (i.e.,
     imported by it, directly or by reexportation), leaving them also
     asserted by means of @pred{assrt_db:add_assertion_read/9}. All
     local property definitions which are transitively used by the
     exported properties of the related files are also stored in
     @pred{clause_db:prop_clause_read/7}. If up to date @tt{.asr}
     files exist for any of the related files, the information is read
     directly from such @tt{.asr} files. @cindex{.asr files}
     Otherwise, the @tt{.pl} file is read and an up to date @tt{.asr}
     file is generated.

   @item The same processing of the previous paragraph is done also
     for files which export a property transitively used by one of the
     exported properties of the related files.
   @end{itemize}

   Since this predicate is intended for gathering file information for
   purposes which can be other than compilation to executable code
   (e.g., generating documentation or in the preprocessor) this
   predicate catches errors and proceeds in cases where file
   processing (e.g., during actual compilation) might normally abort.
   ".

preprocessing_unit_opts(Fs, Opts, Ms, E) :-
    % get verbosity
    ( ( current_pp_flag(verbosity, very_high)
      ; member('-v', Opts)
      ) ->
        Verb = verbose
    ; member('-d', Opts) -> Verb = debug
    ; Verb = quiet 
    ),
    % read_cache, % TODO: why not? (JF)
    % process main file
    process_main_files(Fs, Opts, Ms, Verb),
    ( ( member(load_pkg_from(Mod), Opts)
      ; member(Mod, Ms) % TODO: wrong! only first one?!
      ; Ms = [user(_)], Mod = [user] % TODO: why not a list?
      ) ->
        asserta_fact(adding_to_module(Mod)) % TODO: wrong! we may add to several modules! it should be in related_file/1
    ; retractall_fact(adding_to_module(_)) % TODO: review this
    ),
    % traverse the related files closure
    related_files_closure(direct, Verb, Opts),
    retractall_fact(adding_to_module(_)),
    %% check for props in the related files
    % ver_esp_asr,
    delayed_checks,
    % any error upon loading?
    there_was_error(E).

% ---------------------------------------------------------------------------

% ver_esp_asr :-
%       display( 'imprimiendo la prueba\n\n' ),
%                       assertion_read(PD,_AM,_Status,prop,_Body,_Dict,_S,_LB,_LE),
%       display( PD ), nl,
%       fail.
%
% ver_esp_asr :-
%       display( '\n\nimprimiendo los irrelevantes\n\n' ),
%       current_fact( irrelevant_file(PD) ),
%       display( PD ), nl,
%       fail.
% ver_esp_asr.

% DTM: When loading ast file, if we are adding the module to the
% output, i.e., we add one module information to the current one (see
% load_package_info/1), we have to add import fact in
% itf_db. adding_to_module specifies the original (first) loaded module 
:- data adding_to_module/1.

process_main_files([],     _Opts, [],     _Verb) :- !.
process_main_files([F|Fs], Opts,  [M|Ms], Verb) :- !,
    process_main_file1(F,  Opts, M,  Verb),
    process_main_files(Fs, Opts, Ms, Verb).

:- if(defined(mini_pp)).
maybe_translate(F, _Opts, _M, Lang, NF) :-
    Lang = ciao,
    NF = F.
:- else.
maybe_translate(F, Opts, M, Lang, NF) :-
    atom(F),
    detect_language(F, Lang),
    call_to_sockets_init, % TODO:[new-resources] make it optional!
    translate_input_file(Lang, F, Opts, M, NF).
:- endif.

process_main_file1(F, Opts, M, Verb) :-
    maybe_translate(F, Opts, M, Lang, NF),
    set_pp_flag(prog_lang, Lang), % TODO: one per module
    filetype_from_opts(Opts, Type),
    error_protect(ctrlc_clean(
            process_file(NF, asr, Type,
                process_main_info_file(M, Verb, Opts),
                false, false, do_nothing)
        ),fail). % TODO: fail or abort?

filetype_from_opts(Opts, Type) :-
    ( member(load_pkg_from(_), Opts) ->
        Type = package
    ; Type = any
    ).

:- use_module(library(sockets), [initial_from_ciaopp/0]).
:- data socket_initialized/0.
call_to_sockets_init :-
    current_fact(socket_initialized), !.
call_to_sockets_init :-
    asserta_fact(socket_initialized),
    sockets:initial_from_ciaopp.

:- pred cleanup_pasr
# "Clean up all facts that p_asr asserts.".

cleanup_pasr :-
    retractall_fact(warned(_, _, _)),
    retractall_fact(processed_file(_)),
    retractall_fact(related_file(_)),
    retractall_fact(irrelevant_file(_)),
    retractall_fact(file_included_by_package(_)),
    retractall_fact(socket_initialized).

there_was_error(yes) :- module_error, !.
there_was_error(yes) :- module_error(_), !.
there_was_error(no).

%% ---------------------------------------------------------------------------
%% Main file (current module) processing
%% ---------------------------------------------------------------------------

%% this file have to assert related_file fact to be processed later.

% process_main_file(Base,M,Verb,Opts):- 
%         pplog(load_assrts, ['{Processing main module ']),
%       defines_module(Base,M),
%       assertz_fact( processed_file( Base ) ),
%       assert_itf(defines_module,M,_,_,Base),
%       %% forces generation of defines/5 data (used below)
%       c_itf:comp_defines(Base),
%       %% (can not!) checks that properties are identifiable
%       normalize_assertions(M,Base,Opts),
%         %% save clauses, assertions, and itf (everything expanded)
%         activate_second_translation(Base,M),
%       % treat assertions
%       get_assertions_of( _, M, Assrt ),
%       compound_to_simple_assrt( Assrt, NAssrt ),
%       % Save orignal pred assertions
%       comment_original_pred_assertions( Assrt ),
%       % Add clauses to DB
%       assert_clauses_of(Base,M),
%       % Add assertions to DB
%       add_assertions( NAssrt ),
%       % add ift facts to DB
%       save_itf_of(Base,M),
%         deactivate_second_translation( Base, M ),
%       %% initialize the (directly) related files of Base
%       assert_related_files_( Base, Verb ),
%         pplog(load_assrts, ['}']).

:- pred load_related_files(Files, M) : (list(Files), var(M))
# "Add some related files to the current module(s) loaded. The
  assertions and properties are loaded. Also the necessary information
  for a correct unexpansion.".

load_related_files([F|Fs], M) :-
    add_related_file(F),
    load_related_files(Fs, M).
load_related_files([], M) :-
    ( asserta_fact(adding_to_module(M), Ref)
    ; erase(Ref), fail
    ),
    related_files_closure(direct, quiet, []),
    erase(Ref),
    !.

process_main_info_file(M, _Verb, Opts, Base) :-
    pplog(load_assrts,['{Processing main module ']),
    defines_module(Base, M),
    assertz_fact(processed_file(Base)),
    assert_itf(defines_module, M, _, _, Base),
    %% forces generation of defines/5 data (used below)
    c_itf:comp_defines(Base),
    %% (can not!) checks that properties are identifiable
    %% save clauses, assertions, and itf (everything expanded)
    activate_second_translation(Base, M),
    % treat assertions
    normalize_assertions(M, Base, []), % TODO: Opts=[]! why?
    get_assertions_of(_, M, Assrt),
    compound_to_simple_assrt(Assrt, NAssrt),
    % Add assertions to DB
    add_assertions(NAssrt),
    % Save orignal pred assertions
    comment_original_pred_assertions(Assrt),
    %
    ( member(load_pkg_from(_), Opts) -> % Do not add clauses
        true
    ; assert_clauses_of(Base, M)
    ),
    % Add operators to output operator DB
    assert_operators_of(Base),
    % add ift facts to DB
    ( member(load_pkg_from(_), Opts) ->
        % TODO: (JF) I changed it injection of packages behave like 
        %   'related files' (it fills impl_defines now)
        IsMain = no
    ; IsMain = yes
    ),
    save_itf_info_of(Base, M, IsMain),
    deactivate_second_translation(Base, M),
%% initialize the (directly) related files of Base
    assert_related_files_(Base, quiet),
    pplog(load_assrts,['}']).
save_itf_info_of(Base, M, _IsMain) :-
    defines(Base, F, A, DefType, Meta),
    assert_itf(defines, M, F, A, M),
    save_meta_dynamic(Meta, DefType, M, F, A),
    fail.
save_itf_info_of(Base, M, _IsMain) :-
    defines(Base, F, A, implicit, _Meta),
    assert_itf(impl_defines, M, F, A, M),
    fail.
save_itf_info_of(_Base, M, yes) :- % saving imported preds
    imports(M, IM, F, A, EM),
    ( (EM = '.' ; IM = EM) ->
        assert_itf(imports, IM, F, A, IM) % IG define end module and reexported
    ;
        assert_itf(imports, IM, F, A, r(IM,EM)), % TODO: needed for output
        assert_itf(imports, IM, F, A, EM)
    ),
    %       save_meta_dynamic(Meta, DefType, M, F, A), %%% IG: here use meta_args
    fail.
save_itf_info_of(_Base, M, yes) :- % saving meta preds
    meta_args(M, Pred),
    functor(Pred, F, A),
    assert_itf(meta, M, F, A, Pred),
    fail.
save_itf_info_of(Base, M, yes) :- % saving dynamic/data/concurrent preds
    dyn_decl(Base, F, A, Decl),
    assert_itf(dynamic, M, F, A, Decl),
    fail.
% TODO: dyn_decl/4 is there as long as clause_of/7 is there. The same info is in
% defines/5... I am not sure which predicate is really alive at this phase.
save_itf_info_of(Base, M, yes) :-
    exports(Base, F, A, _DefType, _Meta),
    assert_itf(exports, M, F, A, M),
    fail.
save_itf_info_of(Base, M, yes) :-
    def_multifile(Base,F,A,DefType),
    \+ c_itf_internal_pred(F,A),
    assert_itf(multifile, M, F, A, DefType),
    fail.
save_itf_info_of(_Base, _M, _IsMain).

save_meta_dynamic(Meta, DefType, M, F, A) :-
    ( Meta\==0 -> assert_itf(meta, M, F, A, Meta)
    ; true
    ),
    ( ( DefType=dynamic ; DefType=data ; DefType=concurrent) ->
       assert_itf(dynamic, M, F, A, DefType)
    ; true
    ).

mod_from_base(N, M) :-
    % TODO: review this code
    ( atom(N) -> % atom: relative or absolute path
       N2 = N
    ; absolute_file_name(N,'_opt','.pl','.',_,N2,_)
    ),
    path_splitext(N2, NoExt, _),
    path_split(NoExt, _, M).

% Add pred assertions to the commented assertions DB. This is
% necessary only for the output.
comment_original_pred_assertions([]).
comment_original_pred_assertions([A|As]) :-
    A = as${type => pred},
    !,
    add_commented_assertion(A),
    comment_original_pred_assertions(As).
comment_original_pred_assertions([_|As]) :-
    comment_original_pred_assertions(As).

%% %%% REVISED TILL HERE

:- data processed_file/1.
:- data related_file/1.
:- data irrelevant_file/1.

% module M is (resp.) 
% processed/related/processed but irrelevant (a leave in the closure)

related_files_closure(Rel, Verb, Opts) :-
    current_fact(related_file(_)), !,
    related_files(Rel, Verb, Opts).
related_files_closure(_Rel, _Verb, _Opts).

related_files(Rel, Verb, Opts) :-
    retract_fact(related_file(I)),
    \+ current_fact(processed_file(I)),
% lets ass this at the begining
    \+ user_module(I),
    error_protect(ctrlc_clean(
            process_file(I, asr, any,
                process_related_file(Rel, Verb, Opts),
                false,
                asr_readable(Verb),
                do_nothing)
        ),fail), % TODO: fail or abort?
    fail.
related_files(_Rel, Verb, Opts) :-
%jcf%- To load only the directly related modules (for testing), just 
%jcf%- comment out this line.
%       related_files_closure(trans,Verb,Opts).
    related_files_closure(direct, Verb, Opts).
%jcf%   
%true.

% DTM: Cannot this be asserted at the beginning?
user_module(user). %% 'user' module cannot be treated as a normal module.

do_nothing(_).

% fail ==> force generation of .asr
asr_readable(Verb, Base) :-
% DTM: If you suspect that asr files are being 
%     reading more than once, uncomment these lines
%
    ( current_fact(processed_file(Base)) ->
        message(inform, ['Internal Error: file ', Base,
                ' is beeing processed twice!'])
    ;
        assertz_fact(processed_file(Base)),
        get_module_filename(pl,  Base, PlName),
        get_module_filename(asr, Base, AsrName),
        file_up_to_date(AsrName, PlName),
        % display('Reading asr file '), display(AsrName), nl,
        read_asr_file(AsrName, Verb),
        defines_module(Base, M),
        assert_itf(defines_module, M, _, _, Base)
    ).

add_related_file(IMAbs) :-
    \+ current_fact(processed_file(IMAbs)),
    \+ current_fact(related_file(IMAbs)),
    \+ preloaded_module(_, IMAbs),
    assertz_fact(related_file(IMAbs)),
%       display( added_related_file( IMAbs ) ),nl,
    !.
add_related_file(_IMAbs).

:- use_module(library(system), [modif_time/2]).

:- pred file_up_to_date(+AuxName,+PlName) : ( atm(AuxName), atm(PlName) )
# "Checks that the file named @var{AuxName} is up to date with respect
  to the file named @var{PlName} (@var{AuxName} modification time is
  later than @var{PlName}). It fails if any of the files does not
  exist.".
file_up_to_date(AuxName,PlName):-
    modif_time(AuxName, AuxTime),
    modif_time(PlName, PlTime),
    PlTime < AuxTime.

%% ---------------------------------------------------------------------------
%% Preprocessing Unit closure

assert_related_files0(direct, Base, _M, Verb) :- !,
    assert_related_files_(Base, Verb).
assert_related_files0(trans, Base, M, Verb) :-
    assert_related_files(Base, M, Verb).

% the closure finalizes when there is no property exported:
assert_related_files(Base, M, Verb) :-
    relevant_prop(M, Prop),
    functor(Prop, F, A),
    exports(Base, F, A, _DefType, _Meta),
    !,
    assert_related_files_(Base, Verb).

assert_related_files(_Base, M, _Verb) :-
    Fact = irrelevant_file(M),
    assertz_fact(Fact),
    write_asr_fact(Fact).

:- data related_file_on_asr/1.

assert_related_files_(Base, _Verb) :-
    retractall_fact(related_file_on_asr(IMAbs)),
    imports_pred(Base, IM, _F, _A, _DefType, _Meta, _EndFile),
    \+ user_module(IM),
% NEW
    file_path(Base, CWD),
%%jcf% working_directory/2 is needed to evaluate .() notation.
    working_directory(OldCWD, CWD),
    absolute_file_name(IM, '_opt', '.pl', CWD, _, IMAbs, _),
    working_directory(_, OldCWD),
% OLD:
%       file_path(Base,Path),
%       working_directory(Old,Path),
%       absolute_file_name(IM,'','.pl','.',_,IMAbs,_),
%       working_directory(_Path,Old),
    \+ current_fact(related_file_on_asr(IMAbs)),
    ( current_fact(generate_asr_file(_)) ->
        asserta_fact(related_file_on_asr(IMAbs)),
        write_asr_fact(related_file(IMAbs))
    ;
        true
    ),
    add_related_file(IMAbs),
    fail.
assert_related_files_(_Base, _Verb).

% TODO: check predicate (is '.' needed?)
file_path(Base,Path):-
    path_split(Base,Path0,_),
    ( Path0 = '' -> Path = '.' ; Path = Path0 ).

relevant_prop(M, Prop) :-
    current_fact(assertion_of(PD, M, _, prop, _, _, _, _LB, _LE)),
    functor(PD,   F, A),
    functor(Prop, F, A).

% remove_undesired_directives( Base ) :-
%       db_directive_of( Base,Body,_VNames,_Src,_L0,_L1 ),
%       display( dir( Body ) ),nl,nl,
%       Body = use_package( Package ),
%       add_output_package(Package),
%       fail.
% remove_undesired_directives( _ ).

% we fo have to process include directives. If one include directive
% belongs to a syntax pakage, then all things included from that
% directive will not be added to CiaoPP

:- data file_included_by_package/1.

assert_clauses_of(Base, _M) :-
    Body = include(File),
    db_directive_of(Base, Body, _, Source, _, _),
    % include directives that belong to a syntax package
    ( get_module_from_path(Source, Module),
        is_syntax_package(Module)
    ; % ubckyde directives included by include directives that
      % belongs to a syntax package
      file_included_by_package(Source)
    ),
    absolute_file_name(File,'_opt','.pl','.',_,AbsFile,_),
    atom_concat(AbsFile, '.pl', AbsSourceFile),
    asserta_fact(file_included_by_package(AbsSourceFile)),
%       display( file_included( AbsSourceFile ) ),nl,
    fail.
% --- DTM: make translations tables from source to module...
assert_clauses_of(Base, M) :-
    db_clause_of(_H, Base, M, Head, Body, VarNames, Source, Line0, Line1),
    has_to_be_asserted(M, Head, Body, Source),
    assertz_fact(clause_read(M,Head,Body,VarNames,Source,Line0,Line1)),
    fail.
assert_clauses_of(_Base, _M).

assert_operators_of(Base) :-
    Body = op(OP1, OP2, OP3),
    db_directive_of(Base, Body, _VarNames, _Source, _Line0, _Line1),
    add_output_operator(OP1, OP2, OP3),
    fail.
assert_operators_of(_Base).

get_assertions_of(Pred, M, As) :-
    findall(A, get_one_assertion_of(Pred, M, A), As), % TODO: this never fails!
    !.
get_assertions_of(_Pred, _M, []).

fast_write_assertions([],     _).
fast_write_assertions([A|As], S) :-
    A = as${
        module => M,
        head => ExpPD,
        compat => Co,
        call => Ca,
        succ => Su,
        comp => Cp,
        status => Status,
        type => Type,
        dic => Dict,
        comment => Cm,
        locator => Loc
    },
    Loc = loc(Source, LB, LE),
    assertion_body(ExpPD, Co, Ca, Su, Cp, Cm, Body1),
    ASSRT = assertion_read(ExpPD, M, Status, Type, Body1, Dict, Source, LB,
        LE),
    write_asr_fact(ASSRT),
    fast_write_assertions(As, S).

%%% --------------------------------
%%% --- TEMPORARY
%%% --------------------------------

% TODO: SPLIT INTO TWO DISTINCT USES! names are wrong

%% by default we include everything from our own module
has_to_be_asserted(user(_), _Head, _Body, _Source) :-
    !.
%% by default we include everything from our own module
has_to_be_asserted(Module, Head, Body, Source) :-
    get_module_from_path(Source, Module),
    !,
    \+
    ( number(Head),
        ( % include declarations are "included"/read by Ciao
            functor(Body, include, 1) -> true
        ; % use_package directives are not saved in CiaoPP either
            Body = use_package(Package), atom(Package) ->
              % TODO: atom/1 check added to preserve previous behaviour; review it!
              add_use_package(Package)
        ; fail
        )
    ).
%% a directive has to be keep iff it belongs to a package which
%% is not syntax one
has_to_be_asserted(_, Head, Body, Source) :-
    !,
%       display( has_to_be( Source ) ),nl,
    get_module_from_path(Source, Module),
%       display( has_module(Module,Body) ),nl,nl,
    ( is_syntax_package(Module) ->
        % if it is a directive
        ( number(Head) ->
            % it is no necesary to add directives from syntax packages
            add_output_package(Module),
            fail
        ; % ERROR: A syntax package is adding a clause => then
          % it is no syntax one
          error_message("Package ~w is said to be syntax " ||
                "package but has the clause: ~w :- ~w. " ||
                "The Output will be incorrect.",
                [Module, Head, Body])
        )
    ; % File is not included by default
      \+ is_included_by_default(Module),
      % File not included by a syntax package 
      \+ file_included_by_package(Source)
    ).

% (for directive, which accepts lists)
add_use_package([]).
add_use_package([P|Ps]) :- !,
    add_output_package(P),
    add_use_package(Ps).
add_use_package(P) :-
    add_output_package(P).

get_module_from_path(Path, Module) :-
    path_basename(Path, File),
    path_splitext(File, Module, _).

% ---------------------------------------------------------------------------
% Packages that will included in the output (and not expanded)

% TODO: update! compute dynamically?

is_syntax_package(rtchecks).
is_syntax_package(basicmodes).
is_syntax_package(isomodes).
is_syntax_package(assertions).
is_syntax_package(regtypes).
is_syntax_package(nativeprops).
is_syntax_package(fsyntax).
is_syntax_package(chr).
is_syntax_package(clpr).
is_syntax_package(clpq).
is_syntax_package('chr/ciao/chr2').
is_syntax_package(chr2).
is_syntax_package(chr_atts).
is_syntax_package(swi_mattr_global).
is_syntax_package(mattr_global).
is_syntax_package(dcg).
is_syntax_package(pcpe_rtquery).

% TODO: use compiler
is_included_by_default(prelude).

%% ---------------------------------------------------------------------------
%% Module Name Expansion in the DB

%% --- DTM: The Dict should be vnDict (to complete variables and unify with 
%%          clauses one)

get_one_assertion_of(PD, M, As2) :-
    current_fact(assertion_of(PD,M,Status,Type,Body0,Dict,Source,LB,LE)),
    Type \== test, % Skip tests assertions, not processed here
    assertion_body(PD, Co, Ca, Su, Cp, Cm, Body0),
    LOC = loc(Source, LB, LE),
    head_expand(Type, PD, M, Dict, ExpPD, LOC), % TODO: rename these predicates
    expand_subbody(Co, M, Dict, ECo, LOC),
    expand_subbody(Ca, M, Dict, ECa, LOC),
    expand_subbody(Su, M, Dict, ESu, LOC),
    expand_subbody(Cp, M, Dict, ECp, LOC),
%       build_a_fake_body(Co,Ca,Su,Cp,FakeBody),
%       module_expand(PD,FakeBody,M,Dict,ExpPD,ExpBody,Source,LB,LE),
%       split_a_fake_body(ECo,ECa,ESu,ECp,ExpBody),
    As2 = as${
        module => M,
        head => ExpPD,
        compat => ECo,
        call => ECa,
        succ => ESu,
        comp => ECp,
        status => Status,
        type => Type,
        dic => Dict,
        comment => Cm,
        locator => Loc
    },
    Loc = loc(Source, LB, LE).

% We process modedef and true here to avoid warnings about undefined
% predicates. --EMM
not_allow_external(modedef, _).
not_allow_external(_,       true). % True is not expanded

head_expand(Type, PD, M, Dict, ExpPD, loc(Source, LB, LE)) :-
    not_allow_external(Type, PD),
    !,
  functor(PD, F, A),
  ( functor(Meta, F, A), meta_args(M, Meta) -> true ; Meta = 0 ),
    module_expand(PD, true, M, Dict, ExpPD0, _, Source, LB, LE),
  fix_assrt_head(ExpPD0, Meta, M, ExpPD),
    functor(PD, F, A),
    (defines(M, F, A) -> true ; assertz_fact(defines(M, F, A))).
% Using module_expand in this way allows us to write assertions of
% predicates that are in other modules: --EMM
head_expand(_, PD, M, Dict, ExpPD, loc(Source, LB, LE)) :-
    functor(PD, F, A),
    ( functor(Meta, F, A), meta_args(M, Meta) -> true ; Meta = 0 ),
    module_expand(true, PD, M, Dict, _, ExpPD0, Source, LB, LE),
    % TODO: expanded as goal, not as head
    fix_assrt_head(ExpPD0, Meta, M, ExpPD).

fix_assrt_head(ExpPD0, 0, _M, ExpPD) :- !,
    ExpPD = ExpPD0. % no meta, no fix
fix_assrt_head(ExpPD0, Meta, M, ExpPD) :-
    ExpPD0 =.. [F|Args],
    Meta =.. [_|MetaArgs],
    fix_assrt_args(Args,MetaArgs,M,NArgs),
    ExpPD =.. [F|NArgs].

fix_assrt_args([],[],_M,[]).
fix_assrt_args([A,_|Args],[MetaArg|MetaArgs],M,[A,_|NArgs]) :-
    ( MetaArg = addmodule(_) ; MetaArg = addterm(_) ),
    !,
    % replace next arg with a fresh var so that the head is normalized
    fix_assrt_args(Args,MetaArgs,M,NArgs).
fix_assrt_args([A|Args],[_MetaArg|MetaArgs],M,[NA|NArgs]) :-
    ( var(A) -> NA = A
    ; A = 'hiord_rt:call'(X) -> NA = X
    ; NA = A % should not happen
    ),
    fix_assrt_args(Args,MetaArgs,M,NArgs).

expand_subbody(C, M, Dict, CO, loc(Source, L0, L1)) :-
    asbody_to_conj(C, CC),
    module_expand(in_assertion_body, CC, M, Dict, _, EC, Source, L0, L1),
    asbody_to_conj(CO, EC).

% build_a_fake_body(Co,Ca,Su,Cp,(CCo;CCa;CSu;CCp)):-
%       list_to_conj(Co,CCo),
%       list_to_conj(Ca,CCa),
%       list_to_conj(Su,CSu),
%       list_to_conj(Cp,CCp).

% split_a_fake_body(Co,Ca,Su,Cp,(CCo;CCa;CSu;CCp)):-
%       conj_to_list(CCo,Co),
%       conj_to_list(CCa,Ca),
%       conj_to_list(CSu,Su),
%       conj_to_list(CCp,Cp).

db_directive_of(Base, Body, VarNames, Source, Line0, Line1) :-
    clause_of(Base, Head, Body, VarNames, Source, Line0, Line1),
    number(Head),
    \+ c_itf_internal_pred_decl(Body).

db_clause_of(Head, Base, M, H, B, VarNames, Source, Line0, Line1) :-
    clause_of(Base, Head, Body, VarNames, Source, Line0, Line1),
    ( number(Head) ->
        \+ c_itf_internal_pred_decl(Body),
        H = Head,
        B = Body
    ;
        module_expand(Head,Body,M,VarNames,H,B,Source,Line0,Line1)
    ).

activate_second_translation(Base, M) :-
    activate_translation(Base, M, add_clause_trans),
    activate_translation(Base, M, add_goal_trans),
    expand_clause(0, 0, M, _, _, _). % Translator initialization

deactivate_second_translation(_Base, M) :-
    end_goal_trans(M),
    del_goal_trans(M),
    del_clause_trans(M).

module_expand(Head, Body, M, VarNames, H, B, Source, Line0, Line1) :-
    ( module_expansion(Head,Body,M,VarNames,asr,Source,Line0,Line1,_,_,H,B) ->
        (VarNames = [], ! ; true)
    ;
%%          error_message( loc(Source,Line0,Line1),
%%                         "Unable to expand~n  ~q :- ~q",[Head,Body]),
%% DTM: just trying the pretty printer!
%% --- DTM: this is an assertion, not a clause
        error_message(loc(Source, Line0, Line1),
            "INTERNAL ERROR: Unable to expand~n  ~p",
            ['$clause'(Head, Body, VarNames)]),
% Error recovery
        Body=B,
        Head=H
    ).

module_expansion(H, B, Module, Dict, Mode, Src, Ln0, Ln1, H1, B1, H2, B2):-
    asserta_fact(location(Src,Ln0,Ln1), Ref),
    ( c_itf:module_expansion(H, B, Module, Dict, Mode, H1, B1, H2, B2) ->
      true
     ; display(user_error,internal_error(H,B)), nl(user_error) % TODO: wrong
    ),
    erase(Ref).

%% ---------------------------------------------------------------------------
%% Related file processing

:- data generate_asr_file/1.

process_related_file(Rel, Verb, Opts, Base) :-
    defines_module(Base, M),
    assertz_fact(processed_file(Base)),
%       display( processed_file( Base ) ), nl,

    assert_itf(defines_module, M, _, _, Base),
    pplog(load_assrts,['{Processing related module ', M]),
%% .asr file
    get_module_filename(asr, Base, AsrName),
    (
        open_asr_to_write(AsrName, Stream, CI),
        !,
        write_asr_header(Stream),
        fast_write(Stream, defines(M, Base)),
        set_fact(generate_asr_file(Stream))
    ;
% DTM: in which case is this neccessary???
        retractall_fact(generate_asr_file(_))
    ),
% The first fact saved is defines...
    save_itf_of_to_asr(Base, M),
%% inhibits the expansion of meta-predicates
%% (can not!) checks that properties are identifiable
    normalize_assertions(M, Base, Opts), % TODO: Opts=[] in other calls, why?
%% saves exported assertions, identifies relevant properties,
%% and saves such property definitions
    activate_second_translation(Base, M),
    save_exported_assertions_of(Base, M),
    save_relevant_properties_of(Base, M),
    deactivate_second_translation(Base, M),
%% store (more) files related to Base
    assert_related_files0(Rel, Base, M, Verb),
%% .asr file
    (  current_fact(generate_asr_file(Stream)) ->
        close_asr(Stream, CI),
        retractall_fact(generate_asr_file(Stream))
    ;
        true
    ),
    % TODO: should multifile be saved?
    save_itf_info_of(Base, M, no),
    pplog(load_assrts,'}').

write_and_save_assertions_of(P, M) :-
    get_assertions_of(P, M, Assrt),
    compound_to_simple_assrt_same_pred(Assrt, NAssrt),
    add_assertions(NAssrt),
    ( current_fact(generate_asr_file(S)) ->
        fast_write_assertions(NAssrt, S)
    ;
        true
    ).
% --- notify internal error!
% write_and_save_assertions_of( P, M ) :-

save_exported_assertions_of(Base, M) :-
    exports(Base, F, A, _DefType, _Meta),
    functor(PD, F, A),
    write_and_save_assertions_of(PD, M),
    fail.
save_exported_assertions_of(_Base, _M).

save_relevant_properties_of(Base, M) :-
    relevant_prop(M, Prop),
    save_predicate_clauses_of(Base, M, Prop),
    functor(Prop, F, A),
    \+ exports(Base, F, A, _DefType, _Meta),
    write_and_save_assertions_of(Prop, M),
    fail.
save_relevant_properties_of(_Base, _M).

save_predicate_clauses_of(Base, M, Prop) :-
    db_clause_of(Prop, Base, M, Head, Body, VarNames, Source, Line0,
        Line1),
    write_asr_fact(prop_clause_read(M, Head, Body, VarNames, Source, Line0,
            Line1)),
    add_prop_clause_read(M, Head, Body, VarNames, Source, Line0, Line1),
    fail.
save_predicate_clauses_of(_Base, _M, _Prop).

%
% DTM: This is a kludge. The metapredicate information
% should be read from .itf file, but while ciaopp and ciao
% this is the more sensate solution.
%
% save_itf_of_to_asr( Base, M ) :-
%       defines(Base,F,A,DefType,Meta),
%       write_asr_fact( defines(M,F,A,DefType,Meta) ),
%       fail.
% save_itf_of_to_asr( Base, M ) :-
%       imports_pred(Base,IM,F,A,DefType,Meta,_EndFile),
%       write_asr_fact( imports(M,IM,F,A,DefType,Meta) ),
%       read_asr_data_loop__action( imports(M,IM,F,A,DefType,Meta) ),
%       fail.

% DTM: Restriction: When loading from ast file, imports fact has to be
% read before exports, because exports may need to add a meta_predicate
% information, and its needs module_expansion/9, which need imports to
% be defined.
% save_itf_of_to_asr( _Base, M ) :-
%       c_itf:imports(M,IM,F,A,EndMod),
%       Fact = imports(M,IM,F,A,EndMod),
%       write_asr_fact( Fact ),
%       read_asr_data_loop__action( Fact ),
%       fail.   
save_itf_of_to_asr(Base, M) :-
    c_itf:exports(Base, F, A, DefType, Meta),
    Meta \== 0,
%       c_itf:imports(M,_IM,F,A,EndMod),
    Fact = exports(M, F, A, DefType, Meta),
    write_asr_fact(Fact),
    read_asr_data_loop__action(Fact),
    fail.
% save_itf_of_to_asr( Base, M ) :-
%       def_multifile(Base,F,A,DefType),
%       \+ c_itf_internal_pred(F,A),
%       Fact = multifile(M,F,A,DefType),
%       write_asr_fact( Fact ),
%       read_asr_data_loop__action( Fact ),
%       fail.
% save_itf_of_to_asr( Base, M ) :-
% %     defines(Base,F,A,implicit,Meta), same as:
%       impl_defines( Base, F, A ),
%       (meta_pred( Base, F, A, Meta ) -> true ; Meta = 0),
%       Fact = impl_defines(M,F,A,Meta),
%       write_asr_fact( Fact ),
%       read_asr_data_loop__action( Fact ),
%       fail.
save_itf_of_to_asr(_Base, _M).

%% ---------------------------------------------------------------------------
%% Library preloading info generation.
%% ---------------------------------------------------------------------------

:- use_module(ciaopp(p_unit/itf_db), [cleanup_lib_itf/0]).

:- use_module(typeslib(typeslib), [
    gen_lib_type_info/1,
    load_lib_type_info/1,
    cleanup_lib_type_info/0]).

:- pred cleanup_lib_sources
    # "Cleans up all preloaded assertion information.".
cleanup_lib_sources :-
    assrt_db:cleanup_lib_assrt,
    typeslib:cleanup_lib_type_info,
    clause_db:cleanup_lib_props,
    itf_db:cleanup_lib_itf.

:- pred load_lib_sources(Path) # "Loads source files for preloading
    assertion info.  Files are loaded from directory @var{Path}.".
load_lib_sources(Path) :-
    % current_pp_flag(library_preloading,on),!,
    load_from_file(Path, 'lib_assertion_read.pl', assrt_db:load_lib_assrt),
    load_from_file(Path, 'lib_prop_clause_read.pl', clause_db:load_lib_props),
    load_from_file(Path, 'lib_itf_db.pl', itf_db:load_lib_itf),
    load_from_file(Path, 'lib_typedb.pl', typeslib:load_lib_type_info).
%load_lib_sources(_Path).

:- use_module(library(pathnames)).

:- meta_predicate load_from_file(?, ?, pred(1)).
load_from_file(Path, Name, Pred) :-
    path_concat(Path, Name, F),
    open(F, read, InS),
    Pred(InS),
    close(InS).

:- pred loaded_lib_sources/0 #"Checks if the library sources are already
    preloaded. This predicate assumes that the lib cache contains at least
    one assertion. This is enough in practice".
loaded_lib_sources :-
    loaded_lib_assrt.

:- use_module(engine(runtime_control), [push_prolog_flag/2, pop_prolog_flag/1]). % TODO: do in a better way

:- pred gen_lib_sources(Path) # "Generates source files for preloading
    info from assertions.  Files are generated in directory @var{Path}.".
gen_lib_sources(Path) :-
    push_prolog_flag(write_strings, on),
    write_to_file(Path, 'lib_assertion_read.pl', assrt_db:gen_lib_assrt),
    write_to_file(Path, 'lib_prop_clause_read.pl', gen_lib_props),
    write_to_file(Path, 'lib_itf_db.pl', dump_lib_itf),
    write_to_file(Path, 'lib_typedb.pl', typeslib:gen_lib_type_info),
    pop_prolog_flag(write_strings).

:- meta_predicate write_to_file(?, ?, pred(1)).
write_to_file(Path, Name, Pred) :-
    path_concat(Path, Name, F),
    open(F, write, OutS),
    display(OutS, '%% Do not modify this file: it is generated automatically.'),
    nl(OutS),
    Pred(OutS),
    close(OutS).

%% ---------------------------------------------------------------------------
%% Checking for properties in assertions
%% ---------------------------------------------------------------------------

:- data warned/3.

delayed_checks :- % TODO: checking every assertion in the program!!!!!, this can be done better
    assertion_read(PD, M, _Status, Type, Body, _Dict, S, LB, LE),
    \+ current_fact(irrelevant_file(M)),
    \+ Type = modedef,
    \+ Type = test,
    functor(PD, F, A),
    assertion_body(_NPD, CNDP, CNCP, CNAP, CNGP, _CO, Body),
    Where= loc(S, LB, LE),
    check_properties(CNDP, F, A, M, Where),
    check_properties(CNCP, F, A, M, Where),
    check_properties(CNAP, F, A, M, Where),
    check_properties(CNGP, F, A, M, Where),
    fail.
delayed_checks.

check_properties([], _F, _A, _M, _Where) :- !.
check_properties([(P1;P2)], F, A, M, Where) :- !,
    check_properties(P1, F, A, M, Where),
    check_properties_special_case(P2, F, A, M, Where).
check_properties([Prop|Props], F, A, M, Where) :- !,
    functor(Prop, PF, PA),
    check_property(PF, PA, Prop, F, A, M, Where),
    check_properties(Props, F, A, M, Where).
check_properties(PROP, F, A, M, Where) :-
    error_message(Where,
        "INTERNAL ERROR: check_properties: list of properties " ||
        "expected as argument. "||
        "Found: ~q. It was used in an assertion ~w in module ~w",
        [PROP, F/A, M]).

% Here is the case:
%
%  The body assertion _type_ is a list. Then ';' were introduced and
% things like [A;B], with A, B lists, are now accepted.  A problem
% araise when we have something like [A;B;C].  As ';' works like a
% functor, we got ';'(A,(B;C)), with A,B and C list, _BUT_ in:
%
% check_properties( [(P1;P2)],F,A,M,Where):-
%       !,
%       check_properties(P1,F,A,M,Where),
%       check_properties(P2,F,A,M,Where).
%
% P2 is (B;C) so it is not a list!.
%
% Then, here we have the special case:
check_properties_special_case((P1;P2), F, A, M, Where) :- !,
    check_properties(P1, F, A, M, Where),
    check_properties_special_case(P2, F, A, M, Where).
check_properties_special_case(P1, F, A, M, Where) :-
    check_properties(P1, F, A, M, Where).

check_property(call, _PA, _Prop, _F, _A, _M, _Where) :- !.
check_property(';', 2, ';'(A, B), _F, _A, _M, _Where) :-
    check_properties(A, _F, _A, _M, _Where),
    check_properties(B, _F, _A, _M, _Where),
    !.
check_property(PF, PA, _Prop, _F, _A, _M, _Where) :-
%       relevant_prop(_AM,Prop), !.
    functor(PD, PF, PA),
    assertion_read(PD, _AM, _Status, prop, _Body, _Dict, _S, _LB, _LE),
    !.
check_property(PF, PA, _Prop, _F, _A, M, _Where) :-
    warned(PF, PA, M),
    !.
check_property(PF, PA, _Prop, F, A, M, Where) :-
    warning_message(Where,
        "~w used in an assertion for ~w in ~w is not a property",
        [PF/PA, F/A, M]),
    asserta_fact(warned(PF, PA, M)).

%% ---------------------------------------------------------------------------
%% SHOW ASR FILE
%% ---------------------------------------------------------------------------

:- pred show_asr(+File) #"Read and shows the asr @var{File} file.".
show_asr(File) :-
    open(File, read, Stream),
    read(Stream, X),
    display('ASR VERSION: '),
    display(X),
    nl,
    read_and_show(Stream),
    close(Stream).

read_and_show(S) :-
    fast_read(S, T),
    display(T), nl, nl,
    read_and_show(S).
read_and_show(_).

%% ---------------------------------------------------------------------------
%% READ ASR FILE
%% ---------------------------------------------------------------------------

read_asr_file(AsrName, Verb) :-
    catch(open(AsrName, read, Stream), _, fail),
    (
        asr_version(V),
        read(Stream, v(V)),
        !,
        pplog(load_assrts,['{Reading ', AsrName]),
        read_asr_data_loop(Verb, AsrName, Stream),
        close(Stream),
        pplog(load_assrts,['}'])
    ;
        pplog(load_assrts,['{Old version in ', AsrName, '}']),
        close(Stream),
        fail
    ).

%% fast_read/1 version (just fails at end of file)
read_asr_data_loop(Verb, F, Stream) :-
    ( fast_read(Stream, X) ->
        ( read_asr_data_loop__action(X) ->
            true
        ;
            error_message("ERROR PROCESSING FACT ~w from ast file ~w",
                [X, F])
        ),
        read_asr_data_loop(Verb, F, Stream)
    ;
        true
    ).

% not fails + determinist
read_asr_data_loop__action(defines(M, Base)) :-
    !,
    assert_itf(defines_module, M, _, _, Base).
read_asr_data_loop__action(related_file(M)) :-
    !,
    add_related_file(M).
read_asr_data_loop__action(defines(M, F, A, DefType, Meta)) :-
    !,
    restore_defines(M, F, A, DefType, Meta),
    assert_itf(defines, M, F, A, M),
    save_meta_dynamic(Meta, DefType, M, F, A).
% read_asr_data_loop__action( imports(M,IM,F,A,DefType,Meta) ) :-
%       !,
%       assert_itf(imports,M,F,A,IM),
%       save_meta_dynamic(Meta,DefType,M,F,A).
read_asr_data_loop__action(imports(M, IM, F, A, EndMod)) :-
    c_itf:restore_imports(M, IM, F, A, EndMod),
    assert_itf(imports, M, F, A, IM).
read_asr_data_loop__action(exports(M, F, A, DefType, Meta)) :-
    !,
    ( adding_to_module(CM) ->
        c_itf:restore_imports(CM, M, F, A, M),
        assert_itf(imports, CM, F, A, M)
%           read_asr_data_loop__action( imports(CM, M, F, A, DefType, Meta) )
    ;
        assert_itf(exports, M, F, A, M)
    ),
    restore_defines(M, F, A, DefType, Meta),
    save_meta_dynamic(Meta, DefType, M, F, A).
%       read_asr_data_loop__action( defines(M, F, A, DefType, Meta) ).
read_asr_data_loop__action(multifile(M, F, A, DefType)) :-
    !,
    c_itf:restore_multifile(M, F, A, DefType),
    assert_itf(multifile, M, F, A, DefType).
read_asr_data_loop__action(impl_defines(M, F, A, _Meta)) :-
    !,
    assert_itf(impl_defines, M, F, A, M).
read_asr_data_loop__action(irrelevant_file(F)) :-
    !,
    assertz_fact(irrelevant_file(F)).
read_asr_data_loop__action(X) :-
    X = assertion_read(_, M, _, _, Body, _, _, _, _),
    !,
    ( adding_to_module(CM) ->
        assertion_body(Head, _, _, _, _, _, Body),
        functor(Head,   MF, A),
        functor(Head__, MF, A),
        ( current_itf(imports, Head__, M) ->
            true
        ;
            module_split(MF, _, F),
            read_asr_data_loop__action(imports(CM, M, F, A, M))
        )
    ;
        true
    ),
    X = assertion_read(A1, A2, A3, A4, A5, A6, A7, A8, A9),
    add_assertion_read(A1, A2, A3, A4, A5, A6, A7, A8, A9).
read_asr_data_loop__action(X) :-
    X = prop_clause_read(A1, A2, A3, A4, A5, A6, A7),
    add_prop_clause_read(A1, A2, A3, A4, A5, A6, A7).

%% ---------------------------------------------------------------------------
%% WRITE ASR FILE
%% ---------------------------------------------------------------------------

write_asr_fact(X) :-
    current_fact(generate_asr_file(S)),
    !,
    fast_write(S, X).
write_asr_fact(_).

write_asr_header(S) :-
    asr_version(V),
    displayq(S, v(V)),
    display(S, ' .\n').

open_asr_to_write(AsrName, Stream, CI) :-
    ( catch(open(AsrName, write, Stream), _, fail) ->
        current_output(CI),
        set_output(Stream)
    ).

close_asr(Stream, CI) :-
    set_output(CI),
    close(Stream).

%% ---------------------------------------------------------------------------
% CACHE
%% ---------------------------------------------------------------------------

ast_cache([
            library(aggregates),
            library(debugger),
            library(lists),
% hiord?
%       library(hiord_rt),
            library(sort),
            library(terms_check),
            %
            engine(term_basic),
            engine(arithmetic),
            engine(debugger_support),
            engine(mattr_global),
            engine(term_compare),
            engine(term_typing),
            engine(atomic_basic),
            engine(exceptions),
            engine(runtime_control),
            engine(attributes),
            engine(basic_props),
            engine(internals),
            engine(basiccontrol),
            engine(messages_basic),
            engine(stream_basic),
            library(datafacts/datafacts_rt),
            engine(io_basic),
            engine(system_info)
        ]
).

do_cache :-
    cleanup_pasr,
    removeall_assertion_read(_, _, _, _, _, _, _, _, _),
    ast_cache(Modules),
% this funcion assert 'related_files' in order to make
% related_files_closure work.
    transform_to_related_files(Modules, _Files, Names),
    related_files_closure(direct, quiet, []),
    open_asr_to_write(ciaopp_cache, Stream, CI),
    write_asr_header(Stream),
    set_fact(generate_asr_file(Stream)),
    (
% save assertions_of
        save_cache_assertions(Names, Stream),
% save prop_clauses
        save_prop_clauses(Names),
% save related_files
        save_related_files,
% save processed_files
        save_processed_files
    ->
        true
    ;
        message(error, ['There was an error generating cache.'])
    ),
% save processed_files  
    retractall_fact(generate_asr_file(Stream)),
    close_asr(Stream, CI).

transform_to_related_files([],     [],     []).
transform_to_related_files([M|Ms], [F|Fs], [N|Ns]) :-
    absolute_file_name(M, F),
    !,
    get_module_from_path(F, N),
    add_related_file(F),
    transform_to_related_files(Ms, Fs, Ns).
transform_to_related_files([_|Ms], F, N) :-
    transform_to_related_files(Ms, F, N),
    !.

save_cache_assertions([],     _).
save_cache_assertions([M|Ms], S) :-
    findall(As, get_mod_assertion(M, As), L),
    fast_write_assertions(L, S),
    save_cache_assertions(Ms, S).

get_mod_assertion(M, As) :-
    As = as${ module => M },
    get_assertion(_, As).

save_prop_clauses([]).
save_prop_clauses([M|Ms]) :-
    save_prop_clauses__(M),
    save_prop_clauses(Ms).

save_prop_clauses__(M) :-
% relevant_prop( M, Prop ),
% db_clause_of( Prop, _ , M,Head,Body,VarNames,Source,Line0,Line1),
    prop_clause_read(M, Head, Body, VarNames, Source, Line0, Line1),
    Fact = prop_clause_read(M, Head, Body, VarNames, Source, Line0, Line1),
    write_asr_fact(Fact),
    fail.
save_prop_clauses__(_).

save_related_files :-
    current_fact(related_file(F)),
    write_asr_fact(related_file(F)),
    fail.
save_related_files.

save_processed_files :-
    current_fact(processed_file(F)),
    write_asr_fact(processed_file(F)),
    fail.
save_processed_files.

