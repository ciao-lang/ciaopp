% ===========================================================================
% Hooks for domain implementations

:- include(ciaopp(plai/plai_domain)).
:- dom_itf. % add wrappers to multifiles in this module

% ===========================================================================
:- doc(section, "Reachability domains"). % TODO: for partial evaluation
:- use_module(domain(pd), []).
:- use_module(domain(pdb), []).
% ===========================================================================
:- doc(section, "Constraint domains").
:- use_module(domain(fr_top)).
:- use_module(domain(fd)).
:- use_module(domain(lsign)).
:- use_module(domain(lsigndiff)).
% ===========================================================================
:- doc(section, "Groundness and sharing").
:- use_module(domain(gr), []).
:- use_module(domain(def), []).
:- use_module(domain(sharing), []).
:- use_module(domain(sharefree), []).
:- use_module(domain(sharefree_non_var), []).
:- use_module(domain(shfret)). % TODO: this domain was not registerd in aidomain/1
:- use_module(domain(shareson), []).
:- use_module(domain(shfrson), []).
:- use_module(domain(sondergaard), []).
:- use_module(domain(sharing_amgu), []).
:- use_module(domain(sharefree_amgu), []).
:- use_module(domain(shfrlin_amgu), []).
:- use_module(domain(sharing_clique)).
:- use_module(domain(sharing_clique_1)).
:- use_module(domain(sharefree_clique)).
:- use_module(domain(sharing_clique_def)).
:- use_module(domain(sharefree_clique_def)).
:- if(defined(has_ciaopp_bshare)).
:- use_module(domain(bshare/bshare), []).
:- endif.
% ===========================================================================
:- doc(section, "Structure domains"). % TODO: shape also?
:- use_module(domain(aeq), []).
:- use_module(domain(depthk), []).
:- use_module(domain(top_path_sharing), []).
% ===========================================================================
:- doc(section, "Type domains"). % TODO: shape/structure?
:- use_module(domain(termsd)).
:- use_module(domain(ptypes), []).
:- use_module(domain(eterms)).
:- use_module(domain(etermsvar)).
:- use_module(domain(svterms)).
:- use_module(domain(deftypes), []).
% ===========================================================================
:- doc(section, "Numeric domains").
:- use_module(domain(nonrel_intervals), []). % interval domain [IG]
:- if(defined(has_ciaopp_fpnum)).
:- use_module(domain(nonrel_fintervals), []). % floating-point interval domain [DJ]
:- endif.
:- if(defined(has_ciao_ppl)).
:- use_module(domain(polyhedra)).
:- endif.
% ===========================================================================
:- doc(section, "OO/Java domains").
:- if(defined(has_ciaopp_java)).
:- use_module(domain(java_nullity), []).
:- use_module(domain(oo_son), []).
:- use_module(domain(oo_shnltau), []).
:- use_module(domain(oo_types), []).
:- use_module(domain(java_cha), []).
:- endif.
% ===========================================================================
:- doc(section, "Non-failure and determinism").
:- use_module(domain(nfdet/nfdet)). % nonfailure+determinism
:- use_module(domain(nfdet/nfplai)). % nonfailure
:- use_module(domain(nfdet/detplai)). % determinism
% ===========================================================================
:- doc(section, "Resources domains").
:- if(defined(has_ciaopp_cost)).
:- use_module(domain(resources/res_plai)).
:- use_module(domain(resources/res_plai_stprf)).
:- use_module(domain(resources/sized_types)).
:- endif.
% ===========================================================================

