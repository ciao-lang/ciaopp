:- bundle(ciaopp).
version('1.7.0').

depends([
    core,
    typeslib,
    ciaodbg-[optional], 
    ciaopp_testgen-[optional],
    ciao_ppl-[optional], % (optional for polyhedra, numerical constraints, etc.)
    ciao_gsl-[optional], % TODO: remove once ciaopp dep is explicit
    ciaopp_fpnum-[optional], % TODO: remove once ciaopp dep is explicit
    ciaopp_bshare-[optional], % TODO: remove once ciaopp dep is explicit
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

% NOTE: These lines enable ciaopp_actmod as a separate binary.
%   A child ciaopp process started with '--actmod' seems more robust.
%     cmd(ciaopp_actmod, [main='cmds/ciaopp_actmod', libexec]). % (dedicated actmod, not used)
%     service(ciaopp_actmod, [actmod, daemon]).
service(ciaopp_actmod, [actmod, child/*daemon*/, binexec(ciaopp)]).

manual('ciaopp', [main='doc/reference/SETTINGS.pl']).
% manual('ciaopp_internals', [main='doc/internals/SETTINGS.pl']).
manual('ciaopp_tutorials', [main='doc/tutorials/SETTINGS.pl']).
