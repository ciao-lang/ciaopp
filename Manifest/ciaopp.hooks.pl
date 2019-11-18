:- module(_, [], [ciaobld(bundlehooks)]).

:- doc(title,  "Bundle Hooks for CiaoPP").

% ===========================================================================

:- use_module(library(bundle/bundle_flags), [get_bundle_flag/2]).

% ============================================================================

% top-level and command line
'$builder_hook'(item_nested(cmds)).
'$builder_hook'(cmds:cmd('ciaopp', [main='cmds/ciaoppcl'])).

% ===========================================================================
% TODO: duplicated, move to builder

:- use_module(engine(internals), ['$bundle_id'/1]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaobld(builder_aux), [update_file_from_clauses/3]).

'$builder_hook'(prepare_build_bin) :-
    ConfigFile = ~bundle_path(ciaopp, 'src/ciaopp_config_auto.pl'),
    update_file_from_clauses(~findall(C, emit_config(C)), ConfigFile, _).

emit_config(C) :-
    '$bundle_id'(ciaopp_extra),
    C = (:- compilation_fact(has_ciaopp_extra)).
emit_config(C) :-
    '$bundle_id'(davinci),
    C = (:- compilation_fact(has_davinci)).

% ===========================================================================

:- doc(section, "Hooks for caching library assertions").
% This precompilation of the library assertions allows faster module
% loading in CiaoPP (libraries are not checked, the cached data is
% used).

% Warning: This hook only caches the libraries.
% To enable the lib cache execute:
%   ?- use_module(library(persdb/datadir), [ensure_datadir/2]).
%   ?- use_module(ciaopp(p_unit/p_asr), [load_lib_sources/1]).
%   ?- ensure_datadir('ciaopp_lib_cache', _Dir), load_lib_sources(_Dir).

'$builder_hook'(cmds:cmd('gen_lib_cache', [main='cmds/gen_lib_cache'])).
'$builder_hook'(custom_run(cache_libraries, [])) :- !,
    cache_libraries.

:- use_module(library(bundle/bundle_paths)).
:- use_module(ciaobld(config_common), [cmd_path/4]).
:- use_module(ciaobld(cpx_process), [cpx_process_call/3]).

:- use_module(library(persdb/datadir), [ensure_datadir/2]).

db_data_dir(Dir) :-
    ensure_datadir('ciaopp_lib_cache', Dir).

cache_libraries :-
    db_data_dir(Dir),
    bundle_path(ciaopp, 'src/p_unit', LibFakeDir),
    cmd_path(ciaopp, plexe, 'gen_lib_cache', CmdPath),
    cpx_process_call(CmdPath, [Dir], [cwd(LibFakeDir)]).
