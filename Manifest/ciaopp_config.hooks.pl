% (included file)

% TODO: duplicated, move to builder (using bundle deps marked as 'optional')
% TODO: due to a (yet to be fixed) cyclic dependency, this code is
%   included several times

:- use_module(library(bundle/bundle_flags), [get_bundle_flag/2]).
:- use_module(engine(internals), ['$bundle_id'/1]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaobld(builder_aux), [update_file_from_clauses/3]).

create_ciaopp_config :-
    ConfigFile = ~bundle_path(ciaopp, 'src/ciaopp_config_auto.pl'),
    update_file_from_clauses(~findall(C, emit_config(C)), ConfigFile, _).

emit_config(C) :-
    '$bundle_id'(ciaopp_cost),
    C = (:- compilation_fact(has_ciaopp_cost)).
emit_config(C) :-
    '$bundle_id'(ciaopp_extra),
    C = (:- compilation_fact(has_ciaopp_extra)).
emit_config(C) :-
    '$bundle_id'(ciaopp_llvm),
    C = (:- compilation_fact(has_ciaopp_llvm)).
emit_config(C) :-
    '$bundle_id'(ciaopp_java),
    C = (:- compilation_fact(has_ciaopp_java)).
emit_config(C) :-
    '$bundle_id'(ciao_ppl),
    yes = ~get_bundle_flag(ciao_ppl:enabled), % (it can be disabled)
    C = (:- compilation_fact(has_ciao_ppl)).
emit_config(C) :-
    '$bundle_id'(mathematica),
    yes = ~get_bundle_flag(mathematica:enabled), % (it can be disabled)
    C = (:- compilation_fact(has_mathematica)).
emit_config(C) :-
    '$bundle_id'(davinci),
    C = (:- compilation_fact(has_davinci)).

