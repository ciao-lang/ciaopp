:- module(_, [], [doccfg]).

:- include(ciaopp_docsrc(docpaths)).

output_name := 'ciaopp'.

doc_structure :=
    ciaopp_ref_man-[
      part_usage-[
        tut_quick_start,
        auto_interface,
        ciaopp,
        ciaoppcl,
        release_tutorial,
        % 'tutorial',
        part_domains-[
          % Available (working) domains (at least the ones in the tutorial)
          % TODO: add all domains from domains_hooks.pl 
          sharing, % TODO: review included files
          sharing_amgu, % TODO: review included files
          eterms,
          detplai,
          nfplai,
          res_plai
        ],
        part_transformations,
        part_fixpoint,
        part_other_commands-[
          'ciaopp-dump',
          'ciaopp-batch',
          'ciaopp_batch_report'
        ]
      ],
      % TODO: remove, use cross-refs?
      part_assertions-[
        debugging_in_ciaopp,
        assertions_doc,
        assertions_props,
        regtypes_doc,
        basic_props,
        native_props,
        % TODO: use cross-refs
%%          'unittest'-[...]
%%                ['unittest/unittest_props',
%%              'unittestdecls_doc',
%%              % 'unittest/unittest_utils',
%%              'unittest/unittest_statistics',
%%              'unittest/unittest_examples'
%%             ],
        rtchecks_doc, % TODO: use cross-refs
        apply_assertions
      ],
      part_extensions-[
        adding_new_domain,
        domains,
        gr
      ],
      ~doc_internals
    ].

doc_internals :=
    'part_internals'-[
      'frontend_driver'-[
        'raw_printer'
      ],
      'analyze_driver',
      'transform_driver',
      'intermod'-[ % modular analysis
        'p_abs',
        'intermod_entry',
        'intermod_success'
      ],
      'preprocess_flags',
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
        % (not in p_unit dir)
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
       ]
     ].

% TODO: port this manual
allow_markdown := no.
% syntax_highlight := no.

%% TODO: these were enabled in internals manual
% syntax_highlight := no.
% doc_mainopts := bugs.
% doc_compopts := bugs.
