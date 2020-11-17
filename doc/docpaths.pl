% (included file)
% Common paths CiaoPP manuals

% Include paths for Ciao manuals
:- include(core_docsrc(docpaths)).

% Ciao System docs
filepath := ~ciaofilepath_common.
% (core bundle)
filepath := at_bundle(core, 'lib/condcomp').
filepath := at_bundle(core, 'library/regexp').
filepath := at_bundle(core, 'lib/assertions').
filepath := at_bundle(core, 'lib/regtypes').
filepath := at_bundle(core, 'lib/rtchecks').
% (ciaodbg bundle)
filepath := at_bundle(ciaodbg, 'lib/unittest').

% ---------------------------------------------------------------------------
% CiaoPP (main bundle)

% (docs)
filepath := at_bundle(ciaopp, 'doc/readmes').
filepath := at_bundle(ciaopp, 'doc/reference').
filepath := at_bundle(ciaopp, 'doc/tutorials').
filepath := at_bundle(ciaopp, 'doc/figs').
% (commands)
filepath := at_bundle(ciaopp, 'cmds').
% (modules)
filepath := at_bundle(ciaopp, 'src').
filepath := at_bundle(ciaopp, 'src/plai').
filepath := at_bundle(ciaopp, 'src/plai/incanal'). % IG: for incremental analysis
filepath := at_bundle(ciaopp, 'src/p_unit').
filepath := at_bundle(ciaopp, 'src/tr_syntax').
filepath := at_bundle(ciaopp, 'src/infer').
filepath := at_bundle(ciaopp, 'auto_interface').
filepath := at_bundle(ciaopp, 'domains').
%filepath := at_bundle(ciaopp, 'typeslib').
filepath := at_bundle(ciaopp, 'domains/nfdet').

% ---------------------------------------------------------------------------
% CiaoPP-Cost

filepath := at_bundle(ciaopp_cost, 'src').
filepath := at_bundle(ciaopp_cost, 'domains').
filepath := at_bundle(ciaopp_cost, 'domains/resources').
filepath := at_bundle(ciaopp_cost, 'infercost').
filepath := at_bundle(ciaopp_cost, 'resources').

% ---------------------------------------------------------------------------
% CiaoPP-tests

filepath := at_bundle(ciaopp_tests, 'tests/incanal'). % IG: for incremental analysis

% ---------------------------------------------------------------------------
% CiaoPP-Java

filepath := at_bundle(ciaopp_java, 'src').
filepath := at_bundle(ciaopp_java, 'auto_interface').
filepath := at_bundle(ciaopp_java, 'domains').

% ---------------------------------------------------------------------------
% CiaoPP-extra

filepath := at_bundle(ciaopp_extra, 'src').
filepath := at_bundle(ciaopp_extra, 'domains').

% ---------------------------------------------------------------------------
bibfile := ~ciao_bibfile.
