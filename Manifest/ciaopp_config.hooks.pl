% (included file)

% TODO: extract HasBundles from bundle deps marked as optional
% TODO: due to a (yet to be fixed) cyclic dependency, this code is
%   included several times

:- use_module(ciaobld(builder_aux), [generate_config_auto/2]).
:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(library(bundle/bundle_flags), [get_bundle_flag/2]).
:- use_module(library(aggregates), [findall/3]).

lite_version := ~get_bundle_flag(ciaopp:lite).

create_ciaopp_config :-
    ConfigFile = ~bundle_path(ciaopp, 'src/ciaopp_config_auto.pl'),
    HasBundles = ~findall(B, opt_b(B)),
    generate_config_auto(ConfigFile, HasBundles).

opt_b(_) :- ~lite_version = yes, !, fail.
opt_b(ciaopp_cost).
opt_b(ciaopp_extra).
opt_b(ciaopp_fpnum).
opt_b(ciaopp_bshare).
opt_b(ciaopp_llvm).
opt_b(ciaopp_java).
opt_b(ciaotest). % TODO: rename to ciaopp_testgen?
opt_b(ciao_ppl).
opt_b(mathematica).
opt_b(davinci).

