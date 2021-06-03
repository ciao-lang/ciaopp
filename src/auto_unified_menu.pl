%%% included file
%% ana, atm_title # flag - option : pre_action :: post_action <- guard.

use_cfg, 'Use Saved Menu Configuration' # menu_last_config - none.
save_cfg, 'Menu Configuration Name' # menu_config_name  - none : show_mcfg.

all, 'Menu Level'   # menu_level - naive.
all, 'Action'       # inter_all  - analyze_check :: all_menu_branch.

~munified(0), 'CTCheck assertions' # ctcheck  - on :: post_ctcheck.
~munified(0), '| Modules to Check' # ct_modular - curr_mod  :: mod_check  <- cct_manual.
~munified(0), '| Predicate-Level CT Checks'   # pred_ctchecks      - on   <- cct_manual.
~munified(0), '| Program-Point CT Checks'     # pp_ctchecks        - on  <- cct_manual.
~munified(1), '| Multivariant CT Checks'   # multivariant_ctchecks - off  <- cct_manual.
~munified(1), '| Report Non-Verified Assrts'  # ass_not_stat_eval - warning <- cct_manual.
~munified(1), '| Generate CT Checking Intervals' # ctchecks_intervals - off <- cct_manual.
~munified(0), 'Main module'          # main_module  - '$default'.
% TODO: not interactive, added ad-hoc in menu.pl

% ------------------------------------------------------------
% analysis domain options

~munified(0), 'Domain selection' # dom_sel          - auto   .
~munified(0), '| Aliasing/Modes' # modes            - shfr   <- dom_manual.
~munified(0), '| Shape/Types'    # types            - eterms <- dom_manual.
~munified(1), '  | Type precision'       # type_precision   - all <- ana_or_check_not_nf_types.
~munified(1), '  | Eval types'           # type_eval        - off <- ana_or_check_not_nf_evaltypes.
~munified(0), '  | Widening sharing'     # clique_widen     - off       <- clipre.
~munified(1), '  | Type of Widening'     # clique_widen_type- cautious  <- clipre.
~munified(1), '  | Upper Bound Threshold'# clique_widen_ub  - 200       <- clipre.
~munified(1), '  | Lower Bound Threshold'# clique_widen_lb  - 250       <- clipre.
~munified(0), '| Determinism'   # ana_det          - none    <- dom_manual.
~munified(0), '| Non-Failure'   # ana_nf           - none    <- dom_manual.
~munified(0), '| Numeric'       # ana_num          - none    <- dom_manual.
~munified(0), '| Cost'          # ana_cost         - none    <- dom_manual.
~munified(1), '  | Recurrence Solver'    # req_solver       - builtin   <- cost_ana.
~munified(1), '  | Algebraic System'     # math_system      - builtin   <- cost_ana.
~munified(1), '  | Static Profiling'     # perform_static_profiling - no<- cost_ana. % currently disabled

:- if(defined(has_ciaopp_extra)).
~munified(1), '| Cost'          # para_cost        - both      <- para_c1.
:- endif.

~munified(1), 'Analysis entry'         # entry_point      - entry_calls <- expert.

% ------------------------------------------------------------
% modularity options
~munified(0), 'Incremental'                  # incremental - off :: inc_ana.
% curated modular analysis flags
~munified(0), 'Intermodular'                 # intermod       - off :: new_mod_ana.
~munified(0), '| Entry module'               # entry_policy   - top_level <- new_mod.
~munified(0), '| Module loading'             # module_loading - all  <- new_mod.
~munified(1), '| Success policy'             # success_policy - under_all <- new_mod.
~munified(1), '| Module loading boundary'    # punit_boundary - bundle  <- new_mod.
~munified(1), '| Preload libraries'          # preload_lib_sources - on <- new_mod.

% ------------------------------------------------------------
% fixpoint options
~munified(0), 'Customize fixpoint'       # custo_fixpo     - on     <- expert.
~munified(0), '| Fixpoint Algorithm'     # fixpoint       - plai       <- custo_fixpoint. % TODO: was ana_gto (ana_or_check_not_nf + local_control=off)
~munified(1), '| Widen Call'             # widencall      - com_child  <- custo_fixpoint.
~munified(1), '| Variants'               # variants       - off        <- custo_fixpoint.
~munified(1), '| Multivariant Success'   # multi_success  - off        <- custo_fixpoint. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(1), '| Trace'                  # trace_fixp     - no         <- custo_fixpoint.
% TODO: only for fixpo_di?
~munified(1), '| Local Control'          # local_control  - off        <- custo_fixpoint_ana_lc. % (ana_or_check + types!=none&modes!=none)
~munified(1), '| Global Control'         # global_control - hom_emb    <- custo_fixpoint_ana_gc. % (ana_or_check_not_nf_evaltypes + local_control!=off)

% ------------------------------------------------------------
% output options
% 0 = naive, 1 = expert
~munified(0),'Generate Output'           # output          - on.
~munified(0),'| Output Language'         # output_lang          - source <- output_on.
~munified(1),'| Include Program Point'   # pp_info              - off <- output_on. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(1),'| Multi-variant Analysis Results' # vers          - off <- output_on. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(0),'| Collapse Versions'       # collapse_ai_vers     - on <- output_on. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(0),'| Output Types'            # type_output          - all <- output_on.
~munified(1),'| Output Resource'         # output_resources     - functions <- output_on.
~munified(1),'| Output Cost'             # cost_analysis_output - all <- output_on.
~munified(1),'Dump analysis'             # dump            - off.

%%%%% Specialization

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
para     , 'Annotation Algorithm' # para_ann          - mel.
para     , 'Type of IAP'          # para_iap          - nsiap.
para     , 'Local Analysis'       # para_local        - local.
para     , 'Granularity Analysis' # para_grain        - none.
:- endif.
