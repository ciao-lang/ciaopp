% -------------------------------------------------------------
% PS figs for the Internals Documentation
% -------------------------------------------------------------
%
% How to make them:
% Run Ciao on this program in the corresponding directory.

% TODO: This module is outdated (fix absolute paths and make it work again)

:- use_module('/home/clip/Systems/ciao/etc/components.pl').
:- use_module('/home/clip/Systems/ciao/etc/xmrefs.pl').

fig(Part):-
    ( Part=ciaopp
    -> components(ciaopp,_,Files)
     ; relevant_files(Part,Files,components)
    ),
    set_files(Files),
    xmlinks.

/* Then save daVinci graph as a .ps : Print - Portrait - Scale 8x13 approx
   Do not resize the daVinci window!!!!
   and then put the .ps in doc/figs
   -------------------------------------------------------------
*/

components(ciaopp,[],
    [ciaopp(ciaopp),ciaopp(frontend_driver),ciaopp(analyze_driver),ciaopp(transform_driver),
     ciaopp(preprocess_flags),
     infer(infer),infercost(infercost),resources(resources),ciaopp(nfgraph/infernf),
     plai(plai),program(p_unit),syntax(tr_syntax)]).
components(p_unit,[ciaopp(p_unit)],
    [ciaopp(p_unit/assrt_db),ciaopp(p_unit/assrt_norm),ciaopp(p_unit/clause_db),
     ciaopp(p_unit/itf_db),ciaopp(p_unit/p_asr),ciaopp(p_unit/p_abs),ciaopp(p_unit/program_keys)]).
components(plai,[plai(plai)],
    [plai(domains),plai(fixpo_plai),plai(normalize),plai(plai_db),
     plai(re_analysis),plai(tarjan),plai(trace_fixp),plai(transform),
     plai(trust),plai(view_fixp)]).
     % ciaopp(p_unit),ciaopp(preprocess_flags)]
components(infernf,[ciaopp(nfgraph/infernf)],
    [domain(nfdet/cover),ciaopp(nfgraph/in_out),ciaopp(nfgraph/nfnf),domain(nfdet/nfbool),
     ciaopp(nfgraph/nfgraph),domain(nfdet/nfsets),domain(nfdet/nfsupport),
     ciaopp(nfgraph/nftable),domain(nfdet/nftypes),domain(nfdet/subproblems),domain(nfdet/tests),
     infer(infer_db)]).
     % typeslib(typeslib),plai(tarjan)]
components(infercost,[infercost(infercost_old)],
    [infercost(dependency),infercost(determinacy),infercost(init),
     infercost(gran/size_rel),infercost(size),infercost(solution),
     infercost(time)]).
     % infer(infer),infer(infer_db),ciaopp(preprocess_flags)]). 
components(resources,[resources(resources)],
    [resources(dependency_res),resources(determinacy_res),resources(init_res),
     resources(gran_res/size_rel_res),resources(size_res),resources(solution_res),
     resources(time_res)]).
     % infer(infer),infer(infer_db),ciaopp(preprocess_flags)]). 
components(infer,[infer(infer)],
    [infer(infer),infer(modes),infer(vartypes),infer(infer_db),
     typeslib(typeslib)]).

/* -------------------------------------------------------------
*/
