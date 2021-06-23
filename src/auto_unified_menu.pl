%%% included file
%% ana, atm_title # flag - option : pre_action :: post_action <- guard.

use_cfg, 'Use saved menu configuration' # menu_last_config - none.
save_cfg,'Menu configuration name' # menu_config_name  - none : show_mcfg.

all, 'Menu level'   # menu_level - naive.
all, 'Action'       # inter_all  - analyze_check :: all_menu_branch.

~munified(0), 'CTCheck assertions' # ctcheck  - on :: post_ctcheck.
~munified(0), '| Modules to check' # ct_modular - curr_mod  :: post_mod_check  <- cct_manual.
~munified(0), '| Predicate-level checks'   # pred_ctchecks      - on   <- cct_manual.
~munified(0), '| Program point checks'     # pp_ctchecks        - on  <- cct_manual.
~munified(1), '| Multivariant checks'   # multivariant_ctchecks - off  <- cct_manual.
~munified(1), '| Report non-verified assrts'  # ass_not_stat_eval - warning <- cct_manual.
~munified(1), '| Generate intervals' # ctchecks_intervals - off <- cct_manual.
~munified(0), 'Main module'          # main_module  - '$default'.
% TODO: not interactive, added ad-hoc in menu.pl

% ------------------------------------------------------------
% analysis domain options

~munified(0), 'Domain selection' # dom_sel          - auto   .
~munified(0), '| Aliasing/Modes' # modes            - shfr   <- dom_manual.
~munified(0), '| Shape/Types'    # types            - eterms <- dom_manual.
~munified(1), '  | Type precision'       # type_precision   - all <- types_prec_guard.
~munified(1), '  | Eval types'           # type_eval        - off <- eval_types_guard.
~munified(0), '  | Widening sharing'     # clique_widen     - off       <- clipre.
~munified(1), '  | Type of widening'     # clique_widen_type- cautious  <- clipre.
~munified(1), '  | Upper bound threshold'# clique_widen_ub  - 200       <- clipre.
~munified(1), '  | Lower bound threshold'# clique_widen_lb  - 250       <- clipre.
~munified(0), '| Determinism'   # ana_det          - none    <- dom_manual.
~munified(0), '| Non-failure'   # ana_nf           - none    <- dom_manual.
~munified(0), '| Numeric'       # ana_num          - none    <- dom_manual.
~munified(0), '| Cost'          # ana_cost         - none    <- dom_manual.
~munified(1), '  | Recurrence solver'    # req_solver       - builtin   <- cost_ana.
~munified(1), '  | Algebraic system'     # math_system      - builtin   <- cost_ana.
~munified(1), '  | Static profiling'     # perform_static_profiling - no<- cost_ana. % currently disabled

:- if(defined(has_ciaopp_extra)).
~munified(1), '| Cost'          # para_cost        - both      <- para_c1.
:- endif.

~munified(1), 'Analysis entry'         # entry_point      - entry_calls.

% ------------------------------------------------------------
% modularity options
~munified(0), 'Incremental'                  # incremental - off :: post_inc_ana.
% curated modular analysis flags
~munified(0), 'Intermodular'                 # intermod       - off :: post_mod_ana.
~munified(0), '| Entry module'               # entry_policy   - top_level <- new_mod.
~munified(0), '| Module loading'             # module_loading - all  <- new_mod.
~munified(1), '| Success policy'             # success_policy - under_all <- new_mod.
~munified(1), '| Module loading boundary'    # punit_boundary - bundle  <- new_mod.
~munified(1), '| Preload libraries'          # preload_lib_sources - on <- new_mod.

% ------------------------------------------------------------
% fixpoint options
~munified(1), 'Customize fixpoint'       # custo_fixpo    - on.
~munified(0), '| Fixpoint algorithm'     # fixpoint       - plai       <- custo_fixpoint. % TODO: was ana_gto (ana_or_check_not_nf + local_control=off)
~munified(1), '| Widen call'             # widencall      - com_child  <- custo_fixpoint.
~munified(1), '| Variants'               # variants       - off        <- custo_fixpoint.
~munified(1), '| Multivariant success'   # multi_success  - off        <- custo_fixpoint. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(1), '| PP info of facts'       # fact_info      - off        <- custo_fixpoint.
~munified(1), '| Trace'                  # trace_fixp     - no         <- custo_fixpoint.
% TODO: only for fixpo_di?
~munified(1), '| Local control'          # local_control  - off        <- custo_fixpoint_ana_lc. % (ana_or_check + types!=none&modes!=none)
~munified(1), '| Global control'         # global_control - hom_emb    <- custo_fixpoint_ana_gc. % (ana_or_check_not_nf_evaltypes + local_control!=off)

% ------------------------------------------------------------
% output options
% 0 = naive, 1 = expert
~munified(0),'Generate output'           # output               - on.
~munified(0),'| Output language'         # output_lang          - source <- output_on.
~munified(1),'| Include program point'   # pp_info              - off <- output_on. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(1),'| Multi-variant analysis results'# vers           - off <- output_on. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(0),'| Collapse versions'       # collapse_ai_vers     - on <- output_on. % TODO: this option was enabled in opt+para menu, recover if needed
~munified(0),'| Output types'            # type_output          - all <- output_on.
~munified(1),'| Output resource'         # output_resources     - functions <- output_on.
~munified(1),'| Output cost'             # cost_analysis_output - all <- output_on.
~munified(1),'Dump analysis'             # dump                 - off.

%%%%% Specialization

opt      , 'Type of optimization'  # inter_optimize - spec :: opt_menu_branch.
~spsl    , 'Abs specialization'    # spec_poly - off.
~spsl(1) , 'Preserve finite failure'      # pres_inf_fail-off  <- spec_pif.
~spsl(1) , 'Execute unif at spec time'    # exec_unif - on     <- spec_pif.
~spsl(1) , 'Postprocessing phase'  # spec_postproc - on <- spec_pif.
~spsl    , 'Analysis domain'       # peval_ana         - pd.
~spsl(1) , 'Local dontrol'         # local_control - df_hom_emb_as.
~spsl(1) , 'Depth'                 # unf_depth         - 1    <- spec_lcd.
~spsl(1) , 'Computation rule'      # comp_rule - bind_ins_jb  <- spec_lc.
~spsl(1) , 'Partial concretization'# part_conc         - off  <- spec_lc.
~spsl(1) , 'Argument filtering'    # inter_opt_arg_filt- on   <- spec_lc.
~spsl(1) , 'Global control'        # global_control - hom_emb <- spec_lc.
~spsl(1) , 'Use global trees'             # global_trees      - off  <- spec_lc.
spec(1)  , 'Post-minimization'            # min_crit          - none <- spec_lc.
~spsl(1) , 'Abstract spec definitions'    # abs_spec_defs     - off  <- spec_lc.
~spsl(1) , 'Remove useless clauses'       # rem_use_cls       - off  <- spec_lc.
~spsl(1) , 'Simplify arithmetic expressions'# sim_ari_exp     - pre  <- spec_lc.
~spsl(1) , 'Branching factor nonleftmost' # unf_bra_fac       - 1    <- spec_lc.
~spsl(1) , 'Filter numbers'               # filter_nums       - off  <- spec_fn.
~spsl(1) , 'Nums hom emb in local control'# hom_emb_nums      - off  <- spec_hn.

:- if(defined(has_ciaopp_extra)).
sp_poly     , 'Fitness function'          # poly_fitness       - balance.
sp_poly     , 'Maximum size of solution'  # pcpe_bounded_size  - '10K' <- polybounded.
sp_poly     , 'Strategy'                  # poly_strategy      - all_sols.
sp_poly     , 'Aggressivity'              # aggressivity       - normal.
sp_poly(1)  , 'Pruning'                   # poly_pruning       - heuristic <- polystrat.
sp_poly(1)  , 'Heuristic'                 # polyvar_pcpe       - pred <- polyheur.
sp_poly(1)  , 'Modes domain'              # poly_modes         - sd <- polyvar.
sp_poly(1)  , 'Depth of pruning'          # poly_depth_lim     - 3 <- polydepth.
sp_poly(1)  , 'Evaluation time/sol (msecs)' # pcpe_evaltime    - 200.
sp_poly(1)  , 'Argument filtering'        # inter_opt_arg_filt - on.
sp_poly(1)  , 'Post minimization'         # min_crit           - none.
sp_poly(1)  , 'Verbosity in output files' # output_info        - medium. % TODO: move as an moutput(_) option?
:- endif.

:- if(defined(has_ciaopp_extra)).
para     , 'Annotation algorithm' # para_ann          - mel.
para     , 'Type of IAP'          # para_iap          - nsiap.
para     , 'Local analysis'       # para_local        - local.
para     , 'Granularity analysis' # para_grain        - none.
:- endif.
