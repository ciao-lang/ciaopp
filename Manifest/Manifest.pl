:- bundle(ciaopp).
depends([
    core,
    typeslib,
    ciao_ppl-[optional], % (optional for polyhedra, numerical constraints, etc.)
    ciao_gsl-[optional], % TODO: remove once ciaopp dep is explicit
    ciaopp_llvm-[optional], % TODO: remove once ciaopp dep is explicit
    davinci-[optional] % (for interactive trace)
]).

alias_paths([
    ciaopp = 'src',
    domain = 'domains',
    %
    library = 'lib', % modules reachable as library(...)
    %
    ciaopp_docsrc = 'doc',
    %
    spec = 'spec',
    %
    ciaopp_batch = 'batch'
]).

lib('src').
lib('domains').
%
lib('lib').
%
lib('spec').
%
lib('batch').

cmd('cmds/ciaopp-dump').
cmd('cmds/ciaopp-batch').
cmd('batch/ciaopp_master'). % TODO: use libexec?
cmd('batch/ciaopp_batch_report'). % TODO: merge with ciaopp-dump?

readme('INSTALLATION', [main='doc/readmes/INSTALLATION_CIAOPP.lpdoc']).
readme('CHANGELOG', [main='doc/readmes/CHANGELOG_CIAOPP.pl']).

manual('ciaopp', [main='doc/reference/SETTINGS.pl']).
% manual('ciaopp_internals', [main='doc/internals/SETTINGS.pl']).
