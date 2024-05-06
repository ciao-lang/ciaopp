:- module(_, [], [doccfg, ciaopp(ciaopp_options)]).

:- use_module(library(aggregates), [findall/3]).
:- include(ciaopp_docsrc(docpaths)).

output_name := 'ciaopp'.

doc_structure :=
    ciaopp_ref_man-[
      ~doc_usage,
      % ~doc_assertions, % Note: assertions moved to alldocs
      ~doc_extensions,
      ~doc_internals
    ].

doc_usage :=
    part_usage-[
      % tut_quick_start,
      auto_interface,
      ciaopp,
      ciaoppcl,
      % release_tutorial,
      % 'tutorial',
      ~doc_domains,
      part_transformations,
      part_fixpoint,
      ~doc_other_commands
    ].

doc_domains := part_domains-(~findall(X,doc_domain(X))).

% All available domains
% TODO: Synchronize automatically; Do "M-x ciao-grep-root" with ":- dom_def(" to find all definitons.
doc_domain(aeq). % :- dom_def(aeq).
doc_domain(def). % :- dom_def(def).
doc_domain(deftypes). % :- dom_def(deftypes).
doc_domain(depthk). % :- dom_def(depthk).
doc_domain(eterms). % :- dom_def(eterms).
doc_domain(etermsvar). % :- dom_def(etermsvar).
doc_domain(frdef). % :- dom_def(frdef).
doc_domain(fr_top). % :- dom_def(fr).
doc_domain(gr). % :- dom_def(gr).
doc_domain(lsign). % :- dom_def(lsign).
doc_domain(lsigndiff). % :- dom_def(difflsign).
doc_domain(detplai). % :- dom_def(det).
doc_domain(nfplai). % :- dom_def(nf).
doc_domain(nonrel_intervals). % :- dom_def(nonrel_intervals).
:- if(defined(has_ciaopp_fpnum)).
doc_domain(nonrel_fintervals). % :- dom_def(nonrel_fintervals).
:- endif.
doc_domain(pd). % :- dom_def(pd).
doc_domain(pdb). % :- dom_def(pdb).
doc_domain(polyhedra). % :- dom_def(polyhedra).
doc_domain(ptypes). % :- dom_def(ptypes).
doc_domain(sharefree). % :- dom_def(shfr).
doc_domain(sharefree_amgu). % :- dom_def(sharefree_amgu).
doc_domain(sharefree_clique). % :- dom_def(sharefree_clique).
doc_domain(sharefree_clique_def). % :- dom_def(sharefree_clique_def).
doc_domain(sharefree_non_var). % :- dom_def(shfrnv).
doc_domain(shareson). % :- dom_def(shareson).
doc_domain(sharing). % :- dom_def(share).
doc_domain(sharing_amgu). % :- dom_def(share_amgu).
doc_domain(sharing_clique). % :- dom_def(share_clique).
doc_domain(sharing_clique_1). % :- dom_def(share_clique_1).
doc_domain(sharing_clique_def). % :- dom_def(share_clique_def).
doc_domain(shfret). % :- dom_def(shfret).
doc_domain(shfrlin_amgu). % :- dom_def(shfrlin_amgu).
doc_domain(shfrson). % :- dom_def(shfrson).
doc_domain(sondergaard). % :- dom_def(son).
doc_domain(svterms). % :- dom_def(svterms).
doc_domain(termsd). % :- dom_def(terms).
doc_domain(top_path_sharing). % :- dom_def(path).
:- if(defined(has_ciaopp_cost)).
doc_domain(sized_types). % :- dom_def(sized_types).
doc_domain(res_plai_stprf). % :- dom_def(res_plai_stprf).
doc_domain(res_plai). % :- dom_def(res_plai).
:- endif.
:- if(defined(has_ciaopp_java)).
doc_domain(oo_types). % :- dom_def(oo_types).
doc_domain(oo_son). % :- dom_def(oo_son).
doc_domain(oo_shnltau). % :- dom_def(oo_shnltau).
doc_domain(java_nullity). % :- dom_def(java_nullity).
doc_domain(java_cha). % :- dom_def(java_cha).
:- endif.
%:- if(defined(has_ciaopp_bshare)).
%doc_domain('bshare/bshare'). % :- dom_def(bshare).
%:- endif.

doc_other_commands :=
    part_other_commands-[
      'ciaopp-dump',
      'ciaopp-batch',
      'ciaopp_batch_report'
    ].

doc_extensions :=
    part_extensions-[
      adding_new_domain,
      domains
      %gr
    ].

doc_internals :=
    'part_internals'-[
      'frontend_driver'-[
        'raw_printer'
      ],
      'analyze_driver',
      'transform_driver',
      'intermod'-[ % modular analysis
        'intermod_db',
        'intermod_schedule',
        'intermod_punit',
        'intermod_entry',
        'intermod_success'
      ],
      'preprocess_flags',
      'Debug_plai',
      'incanal'-[
        'incanal_driver',
        'incanal_deletion',
        'incanal_db',
        'incanal_persistent_db',
        'tarjan_inc',
        'diff',
        'fixpo_dd' % TODO: move next to fixpo_plai?
      ],
      'Punit'-[
        'Punit0',
        'p_unit',
        'native',
        'program_keys',
        'tr_syntax'
      ],
      'Infer1'-[
        'infer'
      ],
      'Plai1'-[
        'Plai0',
        'plai',
        'fixpo_plai',
        % 'domains', % TODO: where?
        % 'gr', % TODO: where?
        'TypeWidening',
        'plai_db',
        'apply_assertions', % TODO: here?
        'Trust'
      ],        
      'DebugFixp'-[
        'trace_fixp',
        'view_fixp'
      ],
      'ciaopp_batch'-[
        'ciaopp_master',
        'ciaopp_worker',
        'ciaopp_batch_aux',
        'db_analysis',
        'tasks_db'
      ],
      ~ciaopp_testing
    ].

:- use_module(engine(internals), ['$bundle_id'/1]).

ciaopp_testing :=
    'TestingBenchmarking'-[
      'ciaopp_bench_manager',
      'incanal_intermod_bench_driver_doc'-[
        'incanal_intermod_bench_driver',
        'incanal_intermod_test',
        'edition_sequence_generator',
        'naive_reader',
        'module_writer',
        'summarize_stat',
        'analysis_stats'
      ],
      'plai_db_instances',
      'plai_db_comparator'
    ] :- '$bundle_id'(ciaopp_tests), !.
ciaopp_testing := [].

% TODO: port this manual
allow_markdown := yes.
% syntax_highlight := no.

%% TODO: these were enabled in internals manual
% syntax_highlight := no.
% doc_mainopts := bugs.
% doc_compopts := bugs.

%% For debugging
% verbosity := full.
