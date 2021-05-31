%%% included file
%% ana, atm_title # flag - option : pre_action :: post_action <- guard.

use_cfg, 'Use Saved Menu Configuration' # menu_last_config - none.
save_cfg, 'Menu Configuration Name' # menu_config_name  - none : show_mcfg.

all, 'Menu Level'   # menu_level - naive.
all, 'Action'       # inter_all  - analyze :: all_menu_branch.

check   , 'Analysis Domain' # assert_ctcheck  - auto.
%check(1), 'Modular Analysis'    # ct_mod_ana - curr_mod     <- cct.
%check   , 'Modular Checking'    # ct_modular - curr_mod :: mod_check  <- cct.
check   , 'Modules to Check' # ct_modular - curr_mod  :: mod_check  <- cct.
check   , 'Main module'          # main_module  - '$default'. % TODO: not interactive, added ad-hoc in menu.pl
check   , 'Iterate Over Modules' # ct_mod_iterate - on :: post_iter  <- cct_mod. % TODO: equivalent to intermod? (JF)
check(1) ,'Interleave Analysis and Checking'# interleave_an_check - off <- cct_mod_reg.
check(1), 'Related Modules Info'        # ct_ext_policy - assertions <- cct.
check(1), 'Regenerate Analysis Registry'# ct_regen_reg - off::reg_reg <- cct_mod_reg.
check   , 'Report Non-Verified Assrts'  # ass_not_stat_eval - warning <- cct2.
check(1), 'Predicate-Level CT Checks'   # pred_ctchecks      - on   <- cct.
check(1), 'Multivariant CT Checks'   # multivariant_ctchecks - off  <- cct.
check(1), 'Program-Point CT Checks'     # pp_ctchecks        - on  <- cct.
%check(1), 'Create Error Log File'      # error_log          - off  <- cct.
check   , 'Customize Analysis Flags'    # check_config_ana   - off  <- cct_manual.
check   , 'Generate Certificate'        # gen_certificate    - off.
check   , 'Reduced Certificate'         # reduced_cert       - off  <- gencert.
%check   , 'Optimizing Compilation'# optim_comp - none.
check   , 'Generate CT Checking Intervals'        # ctchecks_intervals    - off.

opt      , 'Type of Optimization'  # inter_optimize - spec :: opt_menu_branch.
~spsl    , 'Abs Specialization'    # spec_poly - off.
~spsl(1) , 'Preserve Finite Failure'      # pres_inf_fail-off  <- spec_pif.
~spsl(1) , 'Execute Unif at Spec Time'    # exec_unif - on     <- spec_pif.
~spsl(1) , 'Postprocessing Phase'  # spec_postproc - on <- spec_pif.
~spsl    , 'Analysis Domain'       # peval_ana         - pd.
~spsl(1) , 'Local Control'         # local_control - df_hom_emb_as.
~spsl(1) , 'Depth'                 # unf_depth         - 1    <- spec_lcd.
~spsl(1) , 'Computation Rule'      # comp_rule - bind_ins_jb  <- spec_lc.
~spsl(1) , 'Partial Concretization'# part_conc         - off  <- spec_lc.
~spsl(1) , 'Argument Filtering'    # inter_opt_arg_filt- on   <- spec_lc.
~spsl(1) , 'Global Control'        # global_control - hom_emb <- spec_lc.
~spsl(1) , 'Use Global Trees'             # global_trees      - off  <- spec_lc.
spec(1)  , 'Post-minimization'            # min_crit          - none <- spec_lc.
~spsl(1) , 'Abstract Spec Definitions'    # abs_spec_defs     - off  <- spec_lc.
~spsl(1) , 'Remove Useless Clauses'       # rem_use_cls       - off  <- spec_lc.
~spsl(1) , 'Simplify Arithmetic Expressions'# sim_ari_exp     - pre  <- spec_lc.
~spsl(1) , 'Branching Factor Nonleftmost' # unf_bra_fac       - 1    <- spec_lc.
~spsl(1) , 'Filter Numbers'               # filter_nums       - off  <- spec_fn.
~spsl(1) , 'Nums Hom Emb in Local Control'# hom_emb_nums      - off  <- spec_hn.

:- if(defined(has_ciaopp_extra)).
sp_poly     , 'Fitness Function'          # poly_fitness       - balance.
sp_poly     , 'Maximum Size of Solution'  # pcpe_bounded_size  - '10K' <- polybounded.
sp_poly     , 'Strategy'                  # poly_strategy      - all_sols.
sp_poly     , 'Aggressivity'              # aggressivity       - normal.
sp_poly(1)  , 'Pruning'                   # poly_pruning       - heuristic <- polystrat.
sp_poly(1)  , 'Heuristic'                 # polyvar_pcpe       - pred <- polyheur.
sp_poly(1)  , 'Modes Domain'              # poly_modes         - sd <- polyvar.
sp_poly(1)  , 'Depth of Pruning'          # poly_depth_lim     - 3 <- polydepth.
sp_poly(1)  , 'Evaluation Time per sol in msecs' # pcpe_evaltime  - 200.
sp_poly(1)  , 'Argument Filtering'        # inter_opt_arg_filt - on.
sp_poly(1)  , 'Post Minimization'         # min_crit           - none.
sp_poly(1)  , 'Verbosity in Output Files' # output_info        - medium. % TODO: move as an moutput(_) option?
:- endif.

:- if(defined(has_ciaopp_extra)).
para     ,  'Annotation Algorithm' # para_ann          - mel.
para     ,  'Type of IAP'          # para_iap          - nsiap.
para     ,  'Local Analysis'       # para_local        - local.
:- endif.

% ------------------------------------------------------------
% analysis domain options
~mtypepar, 'Analyze Non-Failure'  # ana_nf           - none :: p_nf     <- ana_or_check_or_paral_gr.

:- if(defined(has_ciaopp_extra)).
para     , 'Cost Analysis'          # para_cost        - both      <- para_c1.
:- endif.
~mtypepar, 'Analyze Aliasing/Mode' # modes           - shfr   <- ana_or_check_or_paral.
~mtype   , 'Analyze Shape/Types'   # types           - eterms <- ana_or_check.
~lt(1)   , '| Type Precision'      # type_precision  - all    <- ana_or_check_not_nf_types.
~lt(1)   , '| Eval Types'          # type_eval       - off    <- ana_or_check_not_nf_evaltypes.

:- if(defined(has_ciaopp_extra)).
para     , 'Granularity Analysis'   # para_grain       - none.
:- endif.
~mtype   , '| Widening sharing'       # clique_widen     - off       <- clipre.
~mtype   , '| Type of Widening'       # clique_widen_type- cautious  <- clipre.
~mtype   , '| Upper Bound Threshold'  # clique_widen_ub  - 200       <- clipre.
~mtype   , '| Lower Bound Threshold'  # clique_widen_lb  - 250       <- clipre.
~mtypeepar,'Analyze Numeric'       # ana_num          - none      <- ana_or_check_or_paral.
~mtype   , 'Analyze Cost'          # ana_cost         - none      <- ana_or_check.
~mtype   , '| Recurrence Solver'   # req_solver       - builtin <- cost_ana.
~mtype   , '| Algebraic System'    # math_system      - builtin <- cost_ana.
~mtype   , '| Static Profiling'    # perform_static_profiling - no <- cost_ana. % currently disabled
~mtypepar, 'Analyze Determinism'  # ana_det          - none      <- ana_or_check_or_paral_uoudg.
~mtypeepar,'Analysis entry'      # entry_point      - entry     <- ana_or_check_or_paral.

% ------------------------------------------------------------
% modularity options
~mtype   , 'Incremental'                  # incremental - off :: inc_ana <- ana_or_check.
% curated modular analysis flags
~mtype   , 'Intermodular'                 # intermod       - off :: new_mod_ana <- ana_or_check.
~mtype   , '| Entry module'               # entry_policy   - top_level <- new_mod.
~mtype   , '| Module loading'             # module_loading - all  <- new_mod.
~mtype   , '| Success policy'             # success_policy - under_all <- new_mod.
~mtype   , '| Module loading boundary'    # punit_boundary - bundle <- new_mod_expert.
~mtype   , '| Preload libraries'          # preload_lib_sources - on <- new_mod_expert.

% ------------------------------------------------------------
% fixpoint options
~mfixpo,'Customize fixpoint'       # menu_fixpo - on     <- expert.
~mfixpo,'| Fixpoint Algorithm'     # fixpoint       - plai       <- custo_fixpoint. % TODO: was ana_gto (ana_or_check_not_nf + local_control=off)
~mfixpo,'| Widen Call'             # widencall      - com_child  <- custo_fixpoint.
~mfixpo,'| Variants'               # variants       - off        <- custo_fixpoint.
~mfixpo,'| Multivariant Success'   # multi_success  - off        <- custo_fixpoint. % TODO: this option was enabled in opt+para menu, recover if needed
~mfixpo,'| Trace'                  # trace_fixp     - no         <- custo_fixpoint.
% TODO: only for fixpo_di?
~mfixpo,'| Local Control'          # local_control  - off        <- custo_fixpoint_ana_lc. % (ana_or_check + types!=none&modes!=none)
~mfixpo,'| Global Control'         # global_control - hom_emb    <- custo_fixpoint_ana_gc. % (ana_or_check_not_nf_evaltypes + local_control!=off)

% ------------------------------------------------------------
% output options
% 0 = naive, 1 = expert
~moutput(0),'Generate Output'           # menu_output          - on.
~moutput(0),'| Output Language'         # output_lang          - source <- ana_or_check_output.
~moutput(0),'| Include Program Point'   # pp_info              - off    <- ana_or_check_output. % TODO: this option was enabled in opt+para menu, recover if needed
~moutput(0),'| Multi-variant Analysis Results' # vers          - off    <- ana_or_check_output. % TODO: this option was enabled in opt+para menu, recover if needed
~moutput(0),'| Collapse Versions'       # collapse_ai_vers     - on     <- ana_or_check_output. % TODO: this option was enabled in opt+para menu, recover if needed
~moutput(0),'| Output Types'            # type_output          - all    <- ana_or_check_output.
~moutput(1),'| Output Resource'         # output_resources     - functions <- ana_or_check_output.
~moutput(1),'| Output Cost'             # cost_analysis_output - all    <- ana_or_check_output.
~moutput(1),'Dump analysis'             # menu_dump            - off.
