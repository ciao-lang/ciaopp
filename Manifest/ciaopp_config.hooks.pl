% (included file)

% TODO: extract HasBundles from bundle deps marked as optional
% TODO: due to a (yet to be fixed) cyclic dependency, this code is
%   included several times

:- use_module(library(bundle/bundle_paths), [bundle_path/3]).
:- use_module(ciaobld(builder_aux), [generate_config_auto/2]).

create_ciaopp_config :-
    ConfigFile = ~bundle_path(ciaopp, 'src/ciaopp_config_auto.pl'),
    HasBundles = [
        ciaopp_cost,
        ciaopp_extra,
        ciaopp_llvm,
        ciaopp_java,
        ciao_ppl,
        mathematica,
        davinci
    ],
    generate_config_auto(ConfigFile, HasBundles).

