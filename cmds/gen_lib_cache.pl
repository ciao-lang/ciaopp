:- module(_,[main/1],[datafacts]).

:- use_module(engine(io_basic)).
:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaopp(ciaopp), [module/1]).
:- use_module(ciaopp(p_unit/p_asr), [gen_lib_sources/1]).
:- use_module(ciaopp(p_unit/itf_db), [fake_module_name/1]).

:- set_prolog_flag(multi_arity_warnings,off).
main([]):-
    display('Usage: gen_lib_cache <dest-dir>'),nl,
    display('       Where <dest-dir> is the directory where the generated files'),nl,
    display('       will be created.'),nl.
main([Dir]):-
    bundle_path(ciaopp, 'cmds/cachedmods/cached_core.pl', P),
    module(P),
    set_fact(fake_module_name(cached_core)), % do not cache info of cached_core
    p_asr:gen_lib_sources(Dir).

