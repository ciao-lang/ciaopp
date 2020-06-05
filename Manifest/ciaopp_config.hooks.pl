% TODO: duplicated, move to builder
% TODO: due to cyclic dep included and done twice (ciaopp and ciaopp_extra bundles)

:- use_module(engine(internals), ['$bundle_id'/1]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaobld(builder_aux), [update_file_from_clauses/3]).

create_ciaopp_config :-
    ConfigFile = ~bundle_path(ciaopp, 'src/ciaopp_config_auto.pl'),
    update_file_from_clauses(~findall(C, emit_config(C)), ConfigFile, _).

emit_config(C) :-
    '$bundle_id'(ciaopp_extra),
    C = (:- compilation_fact(has_ciaopp_extra)).
emit_config(C) :-
    '$bundle_id'(davinci),
    C = (:- compilation_fact(has_davinci)).

