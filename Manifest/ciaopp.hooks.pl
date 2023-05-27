:- module(_, [], [ciaobld(bundlehooks)]).

:- doc(title,  "Bundle Hooks for CiaoPP").

% ===========================================================================

:- bundle_flag(lite, [
    comment("Select lite version"),
    details(
      % .....................................................................
      "Build a version with reduced dependencies"),
    valid_values(['yes', 'no']),
    %
    rule_default('no'),
    %
    interactive([advanced])
]).

% ===========================================================================

:- use_module(library(bundle/bundle_flags), [get_bundle_flag/2]).

% ============================================================================

% top-level and command line
'$builder_hook'(item_nested(cmds)).
'$builder_hook'(cmds:cmd('ciaopp', [main='cmds/ciaoppcl'])).

:- use_module(ciaobld(ciaoc_aux), [cmd_build_copy/4]).
:- use_module(library(bundle/bundle_paths), [bundle_path/3]).

ciaopp_client_sh := ~bundle_path(ciaopp, 'cmds/ciaopp-client.bash').

% TODO: strange target, only for installation, define in another way?
'$builder_hook'(item_nested(ciaopp_client)).
'$builder_hook'(ciaopp_client:cmd('ciao-client', [main='NONE_AUTOGEN', shscript])).
'$builder_hook'(ciaopp_client:build_bin) :- % (override build)
    % (we just copy the script from the builder)
    cmd_build_copy(core, shscript, ~ciaopp_client_sh, 'ciaopp-client').

% ===========================================================================

'$builder_hook'(prepare_build_bin) :-
    create_ciaopp_config.

% ===========================================================================

:- include(.('ciaopp_config.hooks')).

% ===========================================================================

:- doc(section, "Hooks for caching library assertions").

% Precompilation of the library assertions allows faster module
% loading in CiaoPP (libraries are not checked, the cached data is
% used). This hook just calls 'ciaopp --gen-lib-cache'.

'$builder_hook'(custom_run(cache_libraries, [])) :- !,
    cache_libraries.

:- use_module(ciaobld(config_common), [cmd_path/4]).
:- use_module(ciaobld(cpx_process), [cpx_process_call/3]).

cache_libraries :-
    cmd_path(ciaopp, plexe, 'ciaopp', CmdPath),
    cpx_process_call(CmdPath, ['--gen-lib-cache'], []).
