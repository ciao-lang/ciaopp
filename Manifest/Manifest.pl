:- bundle(ciaopp).
depends([
  core,
  ciaopp_extra-[optional],
  davinci-[optional] % (for interactive trace)
]).

alias_paths([
    ciaopp = 'src',
    auto_interface = 'auto_interface',
    domain = 'domains',
    %
    library = 'lib', % modules reachable as library(...)
    %
    ciaopp_docsrc = 'doc',
    %
    typeslib = 'typeslib',
    spec = 'spec'
]).

lib('src').
lib('auto_interface').
lib('domains').
%
lib('lib').
%
lib('typeslib').
lib('spec').

cmd('cmds/ciaopp-dump-fmt').
cmd('cmds/ciaopp-dump-cmp').

readme('INSTALLATION', [main='doc/readmes/INSTALLATION_CIAOPP.lpdoc']).
readme('CHANGELOG', [main='doc/readmes/CHANGELOG_CIAOPP.pl']).

