# Changelog

## [1.6.0] - 2022-9-28 

### Added

 - Integrate test case generation for assertion-based random test
   generation (currently `ciaotest` bundle) fully into CiaoPP's
   assertion checking pipeline.

### Improved

 - Improvements in tutorials. Tutorials are grouped in a separate
   CiaoPP manual, containing:
   - Interactive tutorials from `exfilter`
   - Other tutorials (quick start and larger) from reference manual
 - Added `--ciaopp:lite=[yes|no]` bundle config flag (which disables
   the inclusion of additional bundles)
 - `output/{1,2}` instantiates unbound `File` arg with default if
   needed.
 - Showing summaries of assertion checking (count check, checked,
   false, etc. assertions).
 - Unify ctcheck assertion checking at predicate level and literal
   level.
 - Improved documentation of normal form expressions (`normal_form`)
   (`ciaopp_cost`).

### Fixed

 - Make sure that typedefs are written to `current_output`.
 - Call sockets initialization only if/when required.
 - Fixed bug in `polyhedra:project_on_dimensions/5`, adding missing copies.
 - Fix variable names in raw output (name counter was reset in the
   wrong places).
 - Recover documentation figure for `infercost`/`resources`.
 - Fix in `res_plai` handling of size types. An error in the
   length/semantics of lists in
   `res_plai_aux:update_non_rec_param_args` made `res_plai` fail when
   working with regtypes whose definition involves rules with some
   recursive calls being placed before a non-recursive call.

## [1.5.0] - 2022-3-2

 - ADDED: CiaoPP is included now by default with the `devenv`
   bundle. 
 - ADDED: Output options in the `output/2` predicate.
 - ADDED: More examples (most of them for verifly).
 - ADDED: Documentation for debugging analyses.
 - ADDED: `ciaoppcl` can start as an active module (flycheck).
 - IMPROVED: Better automatic selection of analysis domains (covering
   better the properties to be checked; using mode domains before type
   domains, etc.); `dom_sel` flag to decide whether to
   automatically select domains for verification.
 - IMPROVED: Refactoring and improving `ctchecks` (compile-time
   assertion checking) code: modular ctchecking working again (i.e.,
   after intermodular fixpoint); report assertions per module; better
   messages; many bug fixes.
 - IMPROVED: Reducing boilerplate code in the implementation of
   analysis domains using the new `aidomain` package.
 - IMPROVED: Simplified menu, unified menu for analysis and ctchecks.
 - IMPROVED: Improved precision of (nf,det) analysis domains. Adding
   (experimental) new `nfdet` combined analysis domain.
 - CHANGED: Change default setting for entry point selection from
   assertions (exported calls by default).
 - CHANGED: Disabled output for `ciaoppcl -V`.
 - CHANGED: Assertion simplification (eliminating statically proven
   properties from run-time checks) now enabled by default during
   assertion checking.
 - CHANGED: `trust pred` assertions expanded to `check calls`,
   `trust success` and `trust comp` assertions.
 - CHANGED: Abort `auto_interface` action early if there is a
   compilation error.
 - CHANGED: `pp_info` flag (printing analysis infor at literal
   level) moved to the naive menu.
 - FIXED: Many bug fixes and performance improvements: eliminated some
   dangling choicepoints; avoid printing some calls assertions twice;
   wrong use of `denorm_goal_prop/3` changed to
   `prop_unapply/3`; missing clause to `abs_exec_cond:type_of/4`
   to handle `deftypes` domain.
 - FIXED: Bug in treatment of dynamic predicates.

## [1.4.0] - 2020-11-18

General changes and new features:

 - LLVM-based frontend improved and moved to its own bundle (see
  `ciaopp_llvm` bundle).
 - Split `typeslib` as a separate bundle.
 - Allow heads of entry assertions to be non-normalized.
 - Adapted to new hiord.
 - ADDED: Command `ciaopp-dump`, which performs several
  actions over a ciaopp analysis dump: it subsumes the old
  `ciaopp-dump-cmp` and `ciaopp-dump-cmp` commands. New
  options for: showing the contents of a dump file, a code
  reachability report, static, offline checks of assertions using
  a dump file, and general statistics for the analysis results.
 - ADDED: Added @tt{-op Suffix} option to ciaopp command-line (useful for flycheck).
 - ADDED: Warning if no entries were found
 - ADDED: Unified messages, now controlled by `ciaopp_log.pl`
 - ADDED: `ciaopp-batch` command to run ciaopp on many files and with timeouts.
 - ADDED: Modular (non-incremental) analysis with types (shortening).
 - ADDED: Bottom-up incremental update of fixpoint (at literal level).
 - ADDED: Modular (non-incremental) analysis with types (shortening).

Domains:

 - Implemented domains using (a special) trait package.
 - Added `needs/2` operation.
 - Renamed `abstypes_abs` to `auxinfo_asub`.
 - eterms: `member/2`, @tt{=/2} as native properties (for assertions).
 - pdb:
  - Optimize `pdb_compute_lub`: top if any @tt{ASub} is top.
  - Use `fail` literals.
 - sharing: fixed `free/1` handlers
 - shfr: fixes in handlers of @tt{==/2}, @tt{=/2},
  @tt{'\\\\=='/2}, @tt{'\\\\='/2}, `free/1` (native version of
  `var/1`)

Fixpoints:

 - Split compilation options (`debug`, `trace`,
  `rtchecks`) in common file `fixpoint_options.pl`
 - Improved tracing of clauses
 - Refactored fixpoints to make them easier to merge

Fixpoint `dd`:

 - FIXED: Reuse a complete with the same head but different vars order
 - [performance] Using get_memo_table because Id+Key is unique
 - FIXED: Case in which a literal is not reachable
 - Improved documentation

Analysis of higher-order code:

 - ADDED: Flag for automatic generation of entries of meta
  calls.
 - FIXED: `call/N` was not being detected as meta predicate
  (and flattened when possible).
 - ADDED: @tt{\\\\+} not treated as meta, flatten calls known at
  compile time.

Flags and options menu:

 - ADDED: Flag to remove useless (unreachable) completes after fixpo.
 - `punit_boundary`: change default value to bundle.
 - Included `incanal` flag, changed `ext_policy` in menu
  (same as `pp_flag`).
 - Improved options menu (added and simplified dependencies,
  simplified text, grouped actions, better documentation).

## [1.3.0] - 2019-11-3

New functionality:

 - Backported (and improved) incremental analysis (incanal)
  from CiaoPP 0.8.
 - Integrated incremental and modular analysis (`pp_flag
  incremental=on`)
 - Integrated modular analysis in the general analysis driver.
 - Added analysis using run-time semantics of assertions to
  the `dd` fixpoint (`pp_flag` `old_trusts=off`).
 - Fixes in meta-calls (work in progress).
 - Modularized domains, now they use the aidomain package
  (work in progress).
 - Added generic, non relational domain with simpler domain operations.
 - New flag value: restrict modular analysis to the modules of
  a bundle (`pp_flag` `punit_boundary=bundle`).

Performance improvements:

 - Added hook to cache library assertions.
 - Added flag to load modules faster by preloading ciao libraries.
 - Fixed many dangling choicepoints across all modules.
 - Fixed performance issues in modular analysis.
 - Fixed bug of metacalls inside a recursion (`dd` fixpoint).

User interface and documentation:

 - Rearranged manual.
 - Created web interface for demos (see `ciaopp_online` bundle).
 - Added a high level interface for intermental analisis (incanal).

Benchmarks, internal testing, and debugging:

 - Tests/benchmarks moved to a separate bundle (ciaopp_tests).
 - Added tests for gitlab CI (continuous integration).
 - Some fixes in the davinci interface.
 - Fixed (documentation) assertions. CiaoPP can be run with
  the package rtchecks.
 - Added analysis_stats.pl to unify statistics collecting.
 - ciaopp-dump-cmp: new command to compare two ciaopp analaysis dumps.
 - ciaopp-dump-fmt: new command that outputs the analysis in dot format.
 - New flag value: Raw analysis printer (`pp_flag`
  `output_lang=raw`).
 - Added `pp_flag` to trace fixpoints.

Other bug fixes, cleanups, refactoring, etc.:

 - Removed `api` (now using `p_unit`).
 - Fixed maintaining `plai_db` for complete operations
 - Fixed classifying mistakenly recursive predicates as non recursive (meta predicates).
 - Fixed issue with reexported predicates in p_unit.
 - Fixed problem with meta_predicates that did not have any meta argument.
 - Added `free/1` to `sharefree_clique` domain.
 - Replaced `runtime_control:statistics/2` by `analysis_stats:pp_statistics/2`.
 - Using `p_unit/program_keys.pl` for the keys of ciaopp.

## [1.2.0] - 2006-01-03

New release.

## [1.0.928] - 2004-12-17

../infer/infer_dom.pl

Predicate `asub_to_props` takes into account the flag
`complexity_output` to output the complexity (steps and term size)
inferred for predicates in terms of just arithmetic functions or
complexity orders of such functions.  (Pedro Lopez Garcia)

## [1.0.927] - 2004-12-17

../preprocess_flags.pl

Added flag `complexity_output` which controls whether to output the
complexity (steps and term size) inferred for predicates in terms of
just arithmetic functions (funct, default value) or complexity orders
of such functions (big_o). (Pedro Lopez Garcia)

## [1.0.926] - 2004-12-16

../preprocess_flags.pl

Added a new value for ana_cost flag: steps_o (analysis option that
gives the complexity order of cost functions). (Pedro Lopez Garcia)

## [1.0.925] - 2004-12-16

../preprocess_flags.pl

Added a new value for ana_size flag: size_o (size analysis option that
gives the complexity order of term size functions). (Pedro Lopez
Garcia)

## [1.0.924] - 2004-12-16

../infercost/infercost.pl

Deleted predicates `approximation_to_size/2` and
`approximation_to_time/2`.  (Pedro Lopez Garcia)

## [1.0.923] - 2004-12-16

../infercost/infercost.pl

Adapted output of complexity analysis (steps and term size) to deal
with steps_o and size_o options (complexity orders, i.e. big O).
(Pedro Lopez Garcia)

## [1.0.922] - 2004-12-16

../infer/infer_dom.pl

Adapted asub_to_props to deal with size_o and steps_o
properties. (Pedro Lopez Garcia)

## [1.0.921] - 2004-12-16

../driver.pl

Added a new time analysis option: steps_o (gives the complexity order
of cost functions, i.e. big O). Added also a new size analysis option:
size_o (gives the complexity order of term size functions). (Pedro
Lopez Garcia)

## [1.0.920] - 2004-12-03

../plai/domains.pl

`asub_to_native` and `asub_to_native_out` return the empty
list in the last argument (instead of a free variable).  (Pedro Lopez
Garcia)

## [1.0.919] - 2004-12-03

../driver.pl

A small change to the startup of all-domains checking (Pawel Pietrzak)

## [1.0.918] - 2004-12-02

../ctchecks/ctchecks_pred.pl

Checking size assertions is now available. Made a call to
`abs_execute_sizes/5` (Pawel Pietrzak)

## [1.0.917] - 2004-12-02

../ctchecks/ctchecks_pred.pl

Fixed some minor bugs with printing ct checking messages (Pawel
Pietrzak)

## [1.0.916] - 2004-12-02

../ctchecks/ctchecks_messages.pl

Fixed some problems with printing pp checking errors (Pawel Pietrzak)

## [1.0.915] - 2004-12-02

../ctchecks/assrt_ctchecks_common.pl

Changes in the definition of pp_check/2 (unexpanding meta terms)
(Pawel Pietrzak)

## [1.0.914] - 2004-11-30

../dist/Makefile.pl

Moved all common options to the distribution generator, that is
located in ciao/contrib/distutils, module distmkf.pl (Edison Mera)

## [1.0.913] - 2004-11-30

../plai/domains/typeslib/typeslib.pl

Added atom test in `internally_defined_type_symbol/2` in
type_rules (was giving runtime error in some cases) (Pawel
Pietrzak)

## [1.0.912] - 2004-11-26

../ctchecks/assrt_ctchecks_pp.pl

Fixed a bug related to success-with-precondition assertions. (Pawel
Pietrzak)

## [1.0.911] - 2004-11-25

../ctchecks/ctchecks_pred.pl

New error/warning messages in CT checking at the predicate
level. Displayed: assertions, analysis info (only relevant info in
case of false assertions,i.e. the info of the domain that has made the
assertion disproved), inferred type rules if needed,
not-yet-simplified parts of assertions in the `check` case. Perhaps
should go a separate module at some point.  (Pawel Pietrzak)

## [1.0.910] - 2004-11-25

../ctchecks/ctchecks_pred.pl

Changes to the scheme of checking `success P:Pre => Post` in the
multivariant case (Pawel Pietrzak)

## [1.0.909] - 2004-11-24

../infer/prepare_ai_output.pl

Added bug comment 7.  (Francisco Bueno Carrillo)

## [1.0.908] - 2004-11-24

../infer/gather_modes.pl

Fixed bug: cost/size analysis is performed even if no entry is
supplied.  (Pedro Lopez Garcia)

## [1.0.907] - 2004-11-22

../printer.pl

Modified `concat_all/2` in order to allow terms with functors and
subterms and not only atoms.  (German Puebla)

## [1.0.906] - 2004-11-20

../spec/spec.pl

The predicate decide_perform_unif is no longer needed as this is
   directly handled now by spec_iterate.pl.  (German Puebla)

## [1.0.905] - 2004-11-20

../spec/spec_iterate.pl

Improved handling of unifications introduced by execution of facts and
bridges. They are now directly executed here rather than in
spec.pl. Also, dictionaries are updated when unifications are
executed.  (German Puebla)


## [1.0.903] - 2004-11-19

../infercost/algebraic/compare.pl

Added and exported `exp_eq_than(Ex1, Ex2)`.  (Pedro Lopez Garcia)

## [1.0.902] - 2004-11-19

../infercost/algebraic/algebraic.pl

Added and exported `exp_eq_than(Ex1, Ex2)`.  (Pedro Lopez Garcia)

## [1.0.901] - 2004-11-19

../infer/infer_dom.pl

Predicate `abs_execute_with_info/4` now works for exact size
property (`size/2`). (Pedro Lopez Garcia)

## [1.0.900] - 2004-11-18

../plai/fixpo_ops.pl

Added predicate `eliminate_bottoms_and_equivalents/3`.  (German
Puebla)

## [1.0.899] - 2004-11-18

../spec/unfold.pl

Added comment(bug,3).  (Elvira Albert)

## [1.0.898] - 2004-11-18

../spec/unfold.pl

The unfolding rule `df_tree_hom_emb` cannot choose now any value
for the flag `comp_rule` different from `leftmost`. This is
currently hardwired in the code. Although, in the long term, the menu
should disable those values which are not applicable. In the case of
`hom_emb_anc`, the computation rule was fixed to leftmost since the
beginning.  (Elvira Albert)

## [1.0.897] - 2004-11-18

../preprocess_flags.pl

Added value `jump_builtin` for flag `comp_rule`. (Elvira Albert)

## [1.0.896] - 2004-11-18

../spec/unfold.pl

Unfolding rules have been adapted to deal with a list of suspended
atoms which is needed for the new computation rule
`jump_builtin`. Only `df_tree_hom_emb` and `hom_emb_anc` do
not work with `jump_builtin` due to the fact that atoms are tuples
in order to track ancestor information. (Elvira Albert)

## [1.0.895] - 2004-11-18

../spec/unfold_local.pl

New computation rule `jump_builtin` which selects always the
leftmost goal but can jump over builtins when they are not
evaluable. A main difference with existing computation rules is that
unfolding is performed 'in situ', i.e., without reordering the atoms
in the goal.  (Elvira Albert)

## [1.0.894] - 2004-11-17

../infer/infer_dom.pl

Added clause to `abs_execute_with_info/4` for handling det domain
   properly.  (Pedro Lopez Garcia)

## [1.0.893] - 2004-11-17

../ctchecks/comp_ctchecks.pl

Deleted predicate de_native_prop/2 (not needed).  (Pedro Lopez Garcia)

## [1.0.892] - 2004-11-17

../p_unit/native.pl

Added size_lb/2, size_ub/2, size_o/2, and size/2 as native properties.
(Pedro Lopez Garcia)

## [1.0.891] - 2004-11-17

../infer/gather_modes.pl

Fixed bug in the inference of modes which caused that predicates not
appearing in the body of any clause were not analyzed by cost/size
analyses.  Added vartypes_to_modes/2 and modified
eliminate_dead_code/10. (Pedro Lopez Garcia)

## [1.0.890] - 2004-11-17

../infer/infer_dom.pl

Finished definition of predicate check_size_info/3 for checking
assertions involving size properties (it works for size_lb, size_ub
and size_o properties). Modified size_info/2.  (Pedro Lopez Garcia)

## [1.0.889] - 2004-11-17

../ctchecks/comp_ctchecks.pl

Finished definition of predicate abs_execute_sizes/5 for checking
assertions involving size properties (it works for size_lb, size_ub
and size_o properties).  (Pedro Lopez Garcia)

## [1.0.888] - 2004-11-16

../spec/abs_exec.pl

The handling of the dynamic abstract executability table is now
separately handled by exported `dyn_abs_exec/4`.  (German Puebla)

## [1.0.887] - 2004-11-16

../spec/spec.pl

The specializer no longer has predicate names hardwired in a builtin
table. Calls to predicates can be abstractly executed if (1) there is
an equiv assertion whose precondition holds, or (2) the predicate is
recognized as native and the static abstract executability table can
handle it, or (3) it is an imported predicate which has been multiply
specialized and thus is in the dynamic abstract executability table.
(German Puebla)

## [1.0.886] - 2004-11-16

../spec/spec_iterate.pl

Data predicate `clause_result/2` now lives in module
spec_iterate.pl.  (German Puebla)

## [1.0.885] - 2004-11-16

../infer/infer.pl

Modified adapt_info/3 for dealing with determinacy info (det domain).
(Pedro Lopez Garcia)

## [1.0.884] - 2004-11-16

../plai/domains.pl

Adapted obtain_info/5 for getting determinacy info (det domain).
(Pedro Lopez Garcia)

## [1.0.883] - 2004-11-16

../plai/domains/detabs.pl

Added det_obtain/4 for getting determinacy info.  (Pedro Lopez Garcia)

## [1.0.882] - 2004-11-16

../plai/domains/detplai.pl

Added det_obtain/4 for getting determinacy info.  Modified split/4 for
dealing with bottom.  (Pedro Lopez Garcia)

## [1.0.881] - 2004-11-16

../ctchecks/comp_ctchecks.pl

Adapted get_det_info/3 for getting determinacy info (det domain).
(Pedro Lopez Garcia)

## [1.0.880] - 2004-11-16

../menu_generator.pl

Fixed potential bug when saving menu flags.  (David Trallero Mena)

## [1.0.879] - 2004-11-15

../spec/mem_usage.pl

Improved documentation.  (German Puebla)

## [1.0.878] - 2004-11-15

../ctchecks/assrt_ctchecks_pp.pl

Minor fixes to pp checking and to printing messages. Added a call to
`adapt_info_to_assrt_head/6`. (Pawel Pietrzak)

## [1.0.877] - 2004-11-15

../plai/intermod.pl

Added exported predicates `monolithic_analyze/3` and
`auto_analyze/3` which return information about the time spent in
several phases of modular analysis.  (Jesus Correas Fernandez)

## [1.0.876] - 2004-11-15

../plai/intermod.pl

Added naive_top_down and naive_bottom_up global scheduling policies.
(Jesus Correas Fernandez)

## [1.0.875] - 2004-11-15

../preprocess_flags.pl

Added naive_top_down, naive_bottom_up values to global_scheduling
preprocess flag.  (Jesus Correas Fernandez)

## [1.0.874] - 2004-11-14

../spec/spec.pl

Reimplemented handling of calls to regular types. The previous version
based on `abs_exec_reg_type_with_post_info/4` was very beatiful
and efficient but may produce wrong results if type analysis is not as
precise as it could be. This happens when analyzing imported types.
(German Puebla)

## [1.0.873] - 2004-11-14

../spec/abs_exec_ops.pl

Added exported `abs_exec_regtype_in_clause/7`.  (German Puebla)

## [1.0.872] - 2004-11-14

../spec/abs_exec_ops.pl

Exported predicate `abs_exec_regtype/4` is now in this module
(German Puebla)

## [1.0.871] - 2004-11-14

../spec/static_abs_exec_table.pl

Exported predicate `abs_exec_regtype/3` is now in abs_exec_ops.pl
(German Puebla)

## [1.0.870] - 2004-11-13

../spec/spec.pl

Exported predicate `get_predicate_names/4` now lives in module
spec_multiple.  (German Puebla)

## [1.0.869] - 2004-11-13

../spec/spec_multiple.pl

Exported predicate `get_predicate_names/4` now lives in module
spec_multiple.  (German Puebla)

## [1.0.868] - 2004-11-13

../auto_interface/auto_interface.pl

Added question for flag exec_unif in expert specialization menu.
(German Puebla)

## [1.0.867] - 2004-11-13

../spec/spec.pl

Execution of `arithmetic:is/2` at specialization time is now
controlled by pp_flag `exec_unif` instead of data predicate
perform_unif.  (German Puebla)

## [1.0.866] - 2004-11-13

../spec/spec_iterate.pl

Removed exported (data) predicate perform_unif, since this is now
controlled by pp_flag `exec_unif`.  (German Puebla)

## [1.0.865] - 2004-11-13

../spec/abs_exec.pl

Reorganized and clarified code for abstract executability and the use
of native props.  (German Puebla)

## [1.0.864] - 2004-11-13

../spec/static_abs_exec_table.pl

Unified abs exec of regular types in new exported predicate
`abs_exec_regtype/3`.  (German Puebla)

## [1.0.863] - 2004-11-12

../p_unit/p_canonical.pl

Commented predicate `decide_pred_status/2` which belongs to old
specification implementation.  (David Trallero Mena)

## [1.0.862] - 2004-11-12

../p_unit/p_canonical.pl

Status of calls assertions derived from `trust pred` is now
`check`.  (Pawel Pietrzak)

## [1.0.861] - 2004-11-11

../p_unit/p_abs.pl

Now `update_current_registry/3` marks callers registries if an
invalidated entry of the current module registry has been reanalyzed.
(Jesus Correas)

## [1.0.860] - 2004-11-11

../p_unit/p_abs.pl

Added an initial version of get_all_modules_depth/2 (to obtain the
list of modules in a program unit with their depths --all modules in a
cycle have the same depth).  (Jesus Correas)

## [1.0.859] - 2004-11-11

../p_unit/p_abs.pl

Added an extra argument to `imported_modules/2` to store the
basename of every module.  (Jesus Correas)

## [1.0.858] - 2004-11-11

../p_unit/p_abs.pl

`compute_external_reachability/0` is now much more efficient.
(Jesus Correas)

## [1.0.857] - 2004-11-11

../plai/plai.pl

Added a call to `reset_previous_analysis(AbsInt)` in
`preprocess/6` for check_di* fixpoint algorithms.  (Jesus
Correas)

## [1.0.856] - 2004-11-11

../plai/fixpo_ops.pl

Added the case `'>='` to `Direction` argument of
`compare_completes_with_prev/3`, to check that success
information in `complete_prev/7` is greater or equal than the
corresponding entries in `complete/7`.  (Jesus Correas)

## [1.0.855] - 2004-11-11

../plai/fixpo_ops.pl

Added `store_previous_analysis_aux_info/1` for adding auxiliary
information of previous analyses (when complete and memo_table
information is already stored).  (Jesus Correas)

## [1.0.854] - 2004-11-11

../plai/fixpo_ops.pl

Changed `store_previous_analysis_completes/1` and
`store_previous_analysis_memo_tables/1` to properly store
auxiliary (type) information.  (Jesus Correas)

## [1.0.853] - 2004-11-11

../plai/domains/share.pl

share_less_or_equal/2 extended to take into account bottom
substitutions.  (Jesus Correas)

## [1.0.852] - 2004-11-11

../plai/domains/sharefree.pl

shfr_less_or_equal/2 extended to take into account bottom
   substitutions.  (Jesus Correas)

## [1.0.851] - 2004-11-11

../p_unit/native.pl

Added steps_o as a native property.  (Pedro Lopez Garcia)

## [1.0.850] - 2004-11-11

../ctchecks/ctchecks_pred.pl

Displaying false assertions regardless of flag `verbose_ctchecks` +
   small fixes related to new flag values (Pawel Pietrzak)

## [1.0.849] - 2004-11-11

../driver.pl

Fixed flag-driven selection of assertion checking algorithms.  (Pawel
   Pietrzak)

## [1.0.848] - 2004-11-11


Added new
   values for the pred_ctchecks flag: new_all - for all domains,
   new_succ - for improved success assertion checking, new_all_succ -
   for both (Pawel Pietrzak)

## [1.0.847] - 2004-11-11

../ctchecks/comp_ctchecks.pl

Fixed a bug in `de_native_prop/2` (Pawel Pietrzak)

## [1.0.846] - 2004-11-10

../spec/static_abs_exec_table.pl

Minor change and added comment bug 1.  (German Puebla)

## [1.0.845] - 2004-11-10

../Makefile.pl

Corrected a bug in the option installbin.  (Edison Mera)

## [1.0.844] - 2004-11-10

../ctchecks/ctchecks_pred.pl

Assertion checking at predicate lavel for all the available analyses
(`simplify_assertions_all/1`) (Pawel Pietrzak)

## [1.0.843] - 2004-11-10

../driver.pl

Added `acheck_all/0` to perform assertion checking at predicate
level for all the available analyses, not just two. (Pawel Pietrzak)

## [1.0.842] - 2004-11-10

../Makefile.pl

Corrected a bug related with the creation of the .ciaorc file.
(Edison Mera)

## [1.0.841] - 2004-11-10

../infer/infer.pl

Adapted inference of type measures (type2measure2/2) for dealing with
module qualified properties (using type_of_goal/2).  (Pedro Lopez
Garcia)

## [1.0.840] - 2004-11-09

../auto_interface/auto_interface.pl

Added missing calls to save_flags and restore_flags in
auto_check_assert.  (German Puebla)

## [1.0.839] - 2004-11-09

../ctchecks/assrt_ctchecks_common.pl

Removed unneeded calls to `native_props`.  (German Puebla)

## [1.0.838] - 2004-11-09

../ctchecks/comp_ctchecks.pl

Fixed bugs 1 and 2.  (Pedro Lopez Garcia)

## [1.0.837] - 2004-11-09

../ctchecks/comp_ctchecks.pl

First shoot to checking of complexity order properties and size
properties.  (Pedro Lopez Garcia)

## [1.0.836] - 2004-11-09

../infercost/algebraic/algebraic.pl

Added predicates for operating with complexity orders. (Pedro Lopez
Garcia)

## [1.0.835] - 2004-11-08

../driver.pl

Added message informing about time taken by ctchecks. Also other
messages are now controled by the flag verbose_ctchecks.  (German
Puebla)

## [1.0.834] - 2004-11-08

../auto_interface/auto_interface.pl

Added question in expert assertion checking menu for pred_ctcheks and
for pp_ctchecks.  (German Puebla)

## [1.0.833] - 2004-11-08

../auto_interface/auto_interface.pl

Fixed the bug in `cct/1` which checks whether compile-time
checking has been selected to the value `on`.  (German Puebla)

## [1.0.832] - 2004-11-08

../driver.pl

Now compile-time checking at predicate level and program point level
is controlled by the corresponding pp_flags.  (German Puebla)

## [1.0.831] - 2004-11-08

../preprocess_flags.pl

Added flags `pred_ctchecks` and `pp_ctchecks` which allow having
several algorithms for compile-time checking available and also turn
off either of them independently.  (German Puebla)

## [1.0.830] - 2004-11-08

../preprocess_flags.pl

For homogeneity, now the values for the flag check_config_ana is
on/off instead of yes/no.  (German Puebla) (German Puebla)

## [1.0.829] - 2004-11-08

../ctchecks/ctchecks_pred.pl

Updates to make comp assertions work again. (Pawel Pietrzak)

## [1.0.828] - 2004-11-08

../ctchecks/comp_ctchecks.pl

Minor changes to integrate with assertions checking (ctchecks_pred.pl)
(Pawel Pietrzak)

## [1.0.827] - 2004-11-08

../auto_interface/auto_interface.pl

Fixed bug added when introducing ana_cost question in checking
menue. Handling of ana_cost is a bit tricky.  (German Puebla)

## [1.0.826] - 2004-11-07

../auto_interface/auto_interface.pl

Added question for error_log flag in expert checking menu.  (German
Puebla)

## [1.0.825] - 2004-11-06

../ctchecks/ctchecks.pl

Reimplemented handling of literals which always fails. For this we
have to check the success substitution for the literal instead of the
call substitution, as was being done.  (German Puebla)

## [1.0.824] - 2004-11-06

../ctchecks/ctchecks.pl

The fact that a literal never succeeds cannot be interpreted as an
error. We now issue warning_message instead of error_message.  (German
Puebla)

## [1.0.822] - 2004-11-06

../ctchecks/comp_ctchecks.pl

Made abs_execute_comp/5 work again (adapted get_cost_info/3 and
select_info/5 to the new cost analysis names steps_lb and
steps_ub). (Pedro Lopez Garcia)

## [1.0.821] - 2004-11-06

../auto_interface/auto_interface.pl

Now when customizing assertion checking, cost analysis can also be
selected.  (German Puebla)

## [1.0.820] - 2004-11-06

../auto_interface/auto_interface.pl

Added a question in the expert menu for checking about
verbose_ctchecks. Also now the value of this flag is pushed just
before executing acheck and popped afterwords.  (German Puebla)

## [1.0.819] - 2004-11-06

../auto_interface/auto_interface.pl

The flag ass_not_stat_eval was never asked.  (German Puebla)

## [1.0.818] - 2004-11-06

../ctchecks/ctchecks_pred.pl

Now only prints assertions whose status has changed if the flag
`verbose_ctchecks` is set to on.  (German Puebla)

## [1.0.817] - 2004-11-06

../preprocess_flags.pl

Added flag `verbose_ctchecks`. When this flag is set to on, all
check assertions which are verified or falsified are printed.  (German
Puebla)

## [1.0.816] - 2004-11-05

../auto_interface/auto_interface.pl

Added question on multivariant success for analysis and compile-time
checking.  (German Puebla)

## [1.0.815] - 2004-11-05

../auto_interface/auto_interface.pl

Now auto_optimize, auto_analyze, and auto_check_assert store the last
   processed file. Thus when calling `again/0` we process
   actually the previous file.  (German Puebla)

## [1.0.814] - 2004-11-05

../ctchecks/ctchecks_pred.pl

Modifications to exploit multivariant analysis in checking call and
success assertions at predicate level. The way of the checking is
controlled by collapse_ai_vers and multi_success flags. (Pawel
Pietrzak)

## [1.0.813] - 2004-11-05

../infer/infer.pl

Added predicate `get_completes/4` to get a set of completes
rather then their lub. Needed for multivariant assertion checking.
(Pawel Pietrzak)

## [1.0.811] - 2004-11-05

../doc/readmes/LPSETTINGS.pl

Renamed INSTALL to INSTALLATION.  (Edison Mera)

## [1.0.810] - 2004-11-04

../auto_interface/auto_interface.pl

Added question in spec menu for comp_rule flag.  (German Puebla)

## [1.0.809] - 2004-11-04

../infercost/infercost.pl

Modified create_worst_case_types/1: abstracted from the type lattice.
(Pedro Lopez Garcia)

## [1.0.808] - 2004-11-04

../infernf/data.pl

Modified create_worst_case_types/3.  (Pedro Lopez Garcia)

## [1.0.807] - 2004-11-04

../plai/domains/typeslib/regtype_basic_lattice.pl

Added comments and documentation.  (Pedro Lopez Garcia)

## [1.0.806] - 2004-11-04

../plai/domains/typeslib/regtype_basic_lattice.pl

Modified dz_type_selects/2: now it uses the predicate
dz_subset_lattice/2, which defines basic inclusion relations in the
type lattice. This allows reducing code a lot: removing the code
duplicating the functionality provided by dz_subset_lattice/2.  Also,
it makes type operations more flexible wrt changes in the type lattice
allowing performing modifications easily. Note however that
dz_subset_lattice/2 does not define inclusion relations involving
compound type terms nor rule type symbols. These relations are defined
by other predicates. The reason for this separate treatment is that it
avoids recursive calls in dz_subset_lattice/2, making type operations
more flexible wrt changes in the type lattice and easing
modifications. However, the separate treatment of compound type terms
and rule type symbols does not involve a lost in generality of type
operations, since it is assumed that compound type terms and rule type
symbols are present in all regular type lattices.  For example, in
order to redefine the type inclusion operation for a new regular type
lattice, it suffices to redefine dz_subset_lattice/2 and additionally
basic_lattice_type_includes_compound_type_term/1 (which defines the
types in the new lattice that include compound type terms). Similarly,
in order to redefine the type intersection operation for a new regular
type lattice, it suffices to redefine
regtype_basic_type_intersection/2 (which defines basic intersection
operations between types in the lattice, except those involving
compound type terms and rule type symbols), and
basic_lattice_type_needs_intersection_with_compound_type_term_args/2.
(Pedro Lopez Garcia)

## [1.0.805] - 2004-11-03

../spec/unfold.pl

Added unfolding rule `df_hom_emb`, which is a depth-first unfolding
rule based on embedding but without ancestors.  (German Puebla)

## [1.0.804] - 2004-11-03

../auto_interface/auto_interface.pl

Changed default values for (spec, local_control) and (ana,
type_output).  (German Puebla)

## [1.0.803] - 2004-11-03

../infer/gather_modes.pl

Modified translate_to_mode/2: make cost/size analysis more flexible
wrt the absence of required info. Now: analyze assuming default (worst
case) info.  (Pedro Lopez Garcia)

## [1.0.802] - 2004-11-03

../infercost/infercost.pl

Fixed bug4: Make cost/size analysis more flexible wrt the absence of
required info. Now: analyze assuming default (worst case)
info. Modified measure_declared/3 in init/dec.pl (Pedro Lopez Garcia)

## [1.0.801] - 2004-11-03

../infercost/infercost.pl

Include mode/type information in output from complexity analyses
(steps_lb, steps_ub, steps_ualb, size_ub, size_ub and size_ualb).
complexity_analysis/2 renamed to time_complexity_analysis/2 and not
exported, term_size_analysis/2 not exported: added
complexity_analysis/3 instead, which perform steps/size analysis
according to its first argument. Also, added and exported:
complexity_to_approximation/2, is_time_analysis/1, is_size_analysis/1,
is_single_complexity_analysis/1, is_ualb_complexity_analysis/3 and
is_complexity_analysis/1. Added (not exported): safe_get_vartype/4 (if
there is no mode/type information then assume term for all variables),
approximation_to_size/2 and approximation_to_steps/2. Imported
predicates: get_vartype/4, make_atom/2 and closed_var_list/2.  (Pedro
Lopez Garcia)

## [1.0.800] - 2004-11-03

../infer/prepare_ai_output.pl

Modified prepare_ai_output_/4 and prepare_infer_output/1: include
mode/type information in output assertions from complexity analyses
(steps_lb, steps_ub, steps_ualb, size_ub, size_ub and
size_ualb). Also, simplified/reduced code by
factorization/generalization (regarding complexity analyses). Imported
predicate from module ciaopp(infercost):
is_ualb_complexity_analysis/3.  (Pedro Lopez Garcia)

## [1.0.799] - 2004-11-03

../infer/infer_dom.pl

Modified asub_to_info/6, asub_to_props/4, complexity_property/5,
asub_to_props/4: include mode/type information in output assertions
from complexity analyses (steps_lb, steps_ub, steps_ualb, size_ub,
size_ub and size_ualb). Also, simplified/reduced code by
factorization/generalization (regarding complexity analyses). Removed:
caslog_property/3. Added: size_name/2,
get_vartypes_from_complexity_info/3 and comp_to_props/5. Imported
predicates from module ciaopp(infercost): is_time_analysis/1,
is_size_analysis/1, is_single_complexity_analysis/1,
is_ualb_complexity_analysis/3 and is_complexity_analysis/1.  (Pedro
Lopez Garcia)

## [1.0.798] - 2004-11-03

../driver.pl

Modified analyze_/3: include mode/type information in output
assertions from complexity analyses (steps_lb, steps_ub, steps_ualb,
size_ub, size_ub and size_ualb). Also, simplified/reduced code by
factorization/generalization (regarding complexity analyses).  Use
complexity_analysis/3 instead of complexity_analysis/2 and
term_size_analysis/2 (from infercost).  (Pedro Lopez Garcia)

## [1.0.797] - 2004-11-02

../spec/unfold.pl

Use the package nomem_usage to avoid the overhead of measuring memory
consumption if we are not running experiments (German Puebla)

## [1.0.796] - 2004-10-30

../plai/plai.pl

Now also memory comsumption is computed. This is returned in the last
argument of `plai/6` together with analysis time.  (German
Puebla)

## [1.0.795] - 2004-10-30

../spec/unfold.pl

Adapted to the new code in mem_usage. This allows computing the memory
required for unfolding even in programs which are not fully unfolded
and where unfolding is calls several times from different memory
prints.  (German Puebla)

## [1.0.794] - 2004-10-30

../spec/mem_usage.pl

Added exported predicate `readjust_max_mem_usage/0`.  (German
Puebla)

## [1.0.793] - 2004-10-30

../spec/mem_usage.pl

Added exported predicate `ask_mem_usage/2`.  (German Puebla)

## [1.0.792] - 2004-10-30

../spec/unfold.pl

Changes needed in order to measure unfolding times.  (German Puebla)

## [1.0.791] - 2004-10-30

../plai/plai.pl

Precise timings are now also provided not only for the whole of
analysis but also for the local_control (unfolding).  (German Puebla)

## [1.0.790] - 2004-10-30

../spec/unfold_times.pl

Added module `unfold_times`. This module contains a series of
dicates for measuring the time actually taken by local control
(unfolding).  (German Puebla)

## [1.0.789] - 2004-10-27

../spec/unfold.pl

Added unfolding rule `df_tree_hom_emb` which implements ancestors
using a proof tree.  (German Puebla)

## [1.0.788] - 2004-10-27

../spec/mem_usage.pl

First version of the module for measuring memory usage.  (German
Puebla)

## [1.0.787] - 2004-10-27

../preprocess_flags.pl

Added value `df_tree_hom_emb` for flag `local_control`.  (German
Puebla)

## [1.0.786] - 2004-10-26

../p_unit/p_abs.pl

Fixed bug that kept incorrect type information with valid registry
entries (added `unmark_typedefs_already_loaded/1` internal
predicate).  (Jesus Correas Fernandez)

## [1.0.785] - 2004-10-26

../p_unit/aux_filenames.pl

Fixed bug in is_library/1.  (Jesus Correas Fernandez)

## [1.0.784] - 2004-10-25

../infer/gather_modes.pl

This module is now called `gather_modes` to avoid name clash.
(German Puebla)

## [1.0.783] - 2004-10-23

../p_unit/p_asr.pl

Fixed bug which did not find correctly the local modules.  (David
Trallero Mena)

## [1.0.782] - 2004-10-22

../plai/domains/eterms.pl

Fixed bug, get_canonical_name is now deterministic (Claudio Vaucheret)

## [1.0.779] - 2004-10-21

../p_unit/assrt_norm.pl

Solved a bug when normalizing calls assertions bodies contaning ';'.
(David Trallero Mena)

## [1.0.778] - 2004-10-21

../p_unit/p_asr.pl

Added necessary funtionality for `check_properties` to check
properties of a list of list of disjuntions ( [A;B;C] ).  (David
Trallero Mena)

## [1.0.777] - 2004-10-21

../p_unit/p_asr.pl

`irrelevant_file/1` was not saved in the ast files, so
check_properties did different things when loading the ast file than
when generating it. (David Trallero Mena)

## [1.0.776] - 2004-10-21

../ctchecks/ctchecks_pred.pl

Adapted code to use the new `abs_execute/2` version.  (David
Trallero Mena)

## [1.0.775] - 2004-10-21

../ctchecks/ctchecks_pred.pl

Using testing_ctchecks to decide whether generate clauses containing
errors or not. Useful for auto-ctchecks testing.  (David Trallero
Mena)

## [1.0.774] - 2004-10-21

../ctchecks/ctchecks_pred.pl

Imported common code from ctchecks_common instead of duplicating it.
(David Trallero Mena)

## [1.0.773] - 2004-10-21

../plai/domains/eterms.pl

Fixed bug in eterms_glb (Claudio Vaucheret)

## [1.0.772] - 2004-10-20

../plai/domains/typeslib/regtype_basic_lattice.pl

Fixed bugs in dz_subset_lattice/2: now it works for all cases,
including those involving flt, struct and gndsrt.  (Pedro Lopez
Garcia)

## [1.0.771] - 2004-10-20

../plai/domains/typeslib/basic_type_operations.pl

Fixed bug in dz_subset/3: now it works for all cases involving
compound pure type terms.  (Pedro Lopez Garcia)

## [1.0.770] - 2004-10-20

../Makefile.pl

Changed realclean by braveclean in the doc generation.  (Edison Mera)

## [1.0.769] - 2004-10-20

../Makefile.pl

Added fullinstallsrcnc that does all except compilation.  Useful to
test installation.  (Edison Mera)

## [1.0.768] - 2004-10-20

../preprocess_flags.pl

Added flag `hom_emb_anc` within local control in order to select an
unfolding rule based on embedding which does not use ancestor stacks
for keeping track of the ancestor information.  (Elvira Albert)

## [1.0.767] - 2004-10-20

../spec/unfold.pl

Added a new strategy `hom_emb_anc` for local unfolding which
implements an unfolding rule based on embedding without using
efficient ancestor stacks but avoiding the restriction to perform only
local unfolding.  (Elvira Albert)

## [1.0.766] - 2004-10-19

../plai/domains/eterms.pl

atom/1, atomic/1 and get_code/2 are deleted from the builtins table of
eterms domain (Claudio Vaucheret)

## [1.0.765] - 2004-10-19

../plai/plai_db.pl

complete_parent/2 now lives in plai_db (Claudio Vaucheret)

## [1.0.764] - 2004-10-19

../plai/fixpo_dx_check_common.pl

Fixed bug related to complete_parent and metacalls (Claudio Vaucheret)

## [1.0.763] - 2004-10-19

../plai/fixpo_di.pl

Fixed bug related to complete_parent and metacalls (Claudio Vaucheret)

## [1.0.762] - 2004-10-19

../plai/fixpo_ops.pl

Fixed bug introduced when replacing `lub` with `multi_success`.
(German Puebla)

## [1.0.761] - 2004-10-19

../plai/domains/typeslib/typeslib.pl

Removed the following warning message from
check_and_remove_empty_types/2: 'The type ~q IS EMPTY. Its type rule
is retracted'.  (Pedro Lopez Garcia)

## [1.0.760] - 2004-10-19

../plai/domains/typeslib/typeslib.pl

Introduced a new item in the type lattice: gndstr (ground struct),
which is the intersection between gnd and struct (and modified type
operations accordingly).  (Pedro Lopez Garcia)

## [1.0.759] - 2004-10-19

../plai/domains/typeslib/typeslib.pl

Fixed bug in typeslib:type_intersection_2/3 (make it call the right
predicates): Predicates typeslib:type_intersection/3 and
regtype_basic_lattice:type_intersection/3 are not mutual recursive
anymore. Renamed regtype_basic_lattice:type_intersection/3 to
regtype_basic_type_intersection/3 (and rewritten its definition in
order to avoid calls to typeslib:type_intersection/3).  Rewritten
typeslib:type_intersection/3 so that calls to
regtype_basic_lattice:regtype_basic_type_intersection/3 are not
(mutually) recursive anymore.  (Pedro Lopez Garcia)

## [1.0.758] - 2004-10-19

../plai/domains/typeslib/typeslib.pl

Regarding comment version 1*0+611,2004/09/08 by David Trallero:
type_intersection/3 needs to be exported, because it is called by
type_intersection_2/3. Otherwise, the wrong type_intersection/3 (the
one in regtype_basic_lattice) is called, and type_intersection_2/3
does not work. (Pedro Lopez Garcia)

## [1.0.757] - 2004-10-19

../plai/domains/typeslib/regtype_basic_lattice.pl

Removed rat and anyfd types from the lattice (and modified type
operations accordingly). Cleaned code.  (Pedro Lopez Garcia)

## [1.0.756] - 2004-10-19

../plai/domains/typeslib/regtype_basic_lattice.pl

Introduced a new item in the type lattice: gndstr (ground struct),
which is the intersection between gnd and struct (and modified type
operations accordingly).  (Pedro Lopez Garcia)

## [1.0.755] - 2004-10-19

../plai/domains/typeslib/regtype_basic_lattice.pl

Renamed regtype_basic_lattice:type_intersection/3 to
regtype_basic_type_intersection/3 (and rewritten its definition in
order to avoid calls to typeslib:type_intersection/3).  (Pedro Lopez
Garcia)

## [1.0.754] - 2004-10-17

../plai/intermod.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.753] - 2004-10-17

../plai/fixpo_plai.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.752] - 2004-10-17

../plai/fixpo_ops.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.751] - 2004-10-17

../plai/fixpo_di.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.750] - 2004-10-17

../plai/fixpo_dd.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.749] - 2004-10-17

../plai/fixpo_check_di4.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.748] - 2004-10-17

../plai/fixpo_check_di3.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.747] - 2004-10-17

../plai/fixpo_check_di2.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.746] - 2004-10-17

../plai/fixpo_check_di.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.745] - 2004-10-17

../plai/domains.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.744] - 2004-10-17

../driver.pl

Replaced flag `lub` by `multi_success`.  (German Puebla)

## [1.0.743] - 2004-10-17

../preprocess_flags.pl

The old flag `lub` and its synonym `multivariance` have been
replaced by flag `multi_success`.  (German Puebla)

## [1.0.742] - 2004-10-14

../infernf/infernf.pl

Non-failure analysis is not performed for predicates which are not
reachable from those exported by the module being analyzed. (Pedro
Lopez Garcia)

## [1.0.741] - 2004-10-14

../infernf/validation.pl

Added a new argument to validate_data/3 so that it creates a list with
predicates which are not reachable from those exported by the module
being analyzed (which are also the predicates for which there is no
mode/type information, since it is assumed that mode and type analysis
has been performed before).  (Pedro Lopez Garcia)

## [1.0.740] - 2004-10-14

../infernf/in_out.pl

Added remove_preds_from_scc_call_graph/3 to remove from the SCC Call
Graph those predicates which are not reachable from those exported by
the module being analyzed, so that they are not analyzed.  (Pedro
Lopez Garcia)

## [1.0.739] - 2004-10-14

../spec/abs_exec_cond.pl

replaced calls to `type_intersection/3` with
`type_intersection_2/3` (the former takes type definitions, the
later type symbols) (Pawel Pietrzak)

## [1.0.738] - 2004-10-13

../spec/static_abs_exec_table.pl

Some improvements making type checking work, when type names are
returned in the condition to be abstractly executed.  (Pawel Pietrzak)

## [1.0.737] - 2004-10-13

../plai/fixpo_di.pl

Fixed bug which made handling of complete_parents fail. Has to be
double checked.  (German Puebla)

## [1.0.736] - 2004-10-13

../preprocess_flags.pl

Modified inter_ana flag to execute nf and cost analysis.  (David
Trallero Mena)

## [1.0.735] - 2004-10-12

../p_unit/p_canonical.pl

Solved a bug that did not convert compound pred assertions with true
as a precondition to success assertions.  (David Trallero Mena)

## [1.0.734] - 2004-10-11

../plai/domains/eterms.pl

Commented out the clause for `atom/1` in
`eterms_special_builtin/5` which seems to be wrong.  (German
Puebla)

## [1.0.732] - 2004-10-11

../p_unit/clidlist.pl

first_key/2 takes into account cuts without keys (just ignore them).
(Pedro Lopez Garcia)

## [1.0.731] - 2004-10-11

../preprocess_flags.pl

Added a new flag (ana_size) to control the type of size analysis:
lower bounds (size_lb), upper bounds (size_ub), or both
(size_ualb). (Pedro Lopez Garcia)

## [1.0.730] - 2004-10-11

../infer/prepare_ai_output.pl

prepare_ai_output_/4 and prepare_infer_output/1 take size_ualb (both,
upper and lower bound size analysis) into account, so that information
is put together in a unique assertion per predicate.  (Pedro Lopez
Garcia)

## [1.0.729] - 2004-10-11

../infer/infer_dom.pl

asub_to_info/6 takes into account a new size analysis option:
size_ualb (both, upper and lower bound size analysis). (Pedro Lopez
Garcia)

## [1.0.728] - 2004-10-11

../driver.pl

Added a new size analysis option: size_ualb (both, upper and lower
bound size analysis). (Pedro Lopez Garcia)

## [1.0.727] - 2004-10-11

../menu_generator.pl

Menu options are plain saved, so we dont distinguish between menu
levels (basic, advance, expert...). Read comment in
`save_flag_list/1`.  (David Trallero Mena)

## [1.0.726] - 2004-10-11

../plai/success.pl

Added an argument to `get_success_info/8` and
`apply_success_policy/9` to indicate whether there is any pattern
applicable to compute the success pattern or not.  (Jesus Correas)

## [1.0.725] - 2004-10-11

../plai/fixpo_di.pl

Added check to control if there are applicable analysis results or
trust information for library imported predicates. If there is no such
information, a warning message is raised.  (Jesus Correas)

## [1.0.724] - 2004-10-11

../plai/domains/typeslib/basic_type_operations.pl

use_module(typeslib(regtype_basic_lattice) , [pure_type_term/1] ) back
to live. Necessary for properties assertions checking.  (David
Trallero Mena)

## [1.0.723] - 2004-10-09

../spec/static_abs_exec_table.pl

Adapted to the fact that the native prop for nonvar/1 is not_free/1.
(German Puebla)

## [1.0.722] - 2004-10-09

../ctchecks/ctchecks_common.pl

Adapted to the new interface of `adapt_info_to_assrt_head/6`.
(German Puebla)

## [1.0.721] - 2004-10-09

../ctchecks/ctchecks.pl

Adapted to the new interface of `adapt_info_to_assrt_head/6`.
(German Puebla)

## [1.0.720] - 2004-10-09

../spec/spec.pl

Adapted to the new interface of `adapt_info_to_assrt_head/6`.
(German Puebla)

## [1.0.719] - 2004-10-09

../spec/abs_exec_ops.pl

Modified `adapt_info_to_assert_head` since the latest changes
introduced were incorrect. In particular, a new argument `Vars` is
required. (German Puebla)

## [1.0.718] - 2004-10-10

../Makefile.pl

Fixed bug: Should generate lpdoc SETTINGS, at least until we move
./doc to lpmake/lpdoc.  (Edison Mera)

## [1.0.717] - 2004-10-09

../spec/static_abs_exec_table.pl

Most of the information for abstract executability of the most
comments tests, i.e., those in `term_typing.pl` now lives in
`equiv` assertions in the library and are commented out from this
file.  (German Puebla)

## [1.0.716] - 2004-10-09

../Makefile.pl

Bug corrections when generating distribution: the distclean option now
depends of the path_setup_src.pl file.  (Edison Mera)

## [1.0.715] - 2004-10-08

../spec/abs_exec.pl

Some improvements to `determinable/2`.  (German Puebla)

## [1.0.714] - 2004-10-08

../spec/spec.pl

Now dictionaries are preserved as much as possible even when
unifications are executed at specialization time.  (German Puebla)

## [1.0.713] - 2004-10-09

../Makefile.pl

Updated files to support lpdoc-2.0 and lpmake.  Now gmake is not
required.  (Edison Mera)

## [1.0.712] - 2004-10-08

../spec/spec.pl

Improved handling of specialization of imported predicates.  (German
Puebla)

## [1.0.711] - 2004-10-07

../spec/static_abs_exec_table.pl

Added entries for native property `free/1`.  (German Puebla)

## [1.0.710] - 2004-10-08

../spec/abs_exec.pl

We now use `native_prop/2` to relate predicate names and the
static abstract executability table.  (German Puebla)

## [1.0.709] - 2004-10-08

../spec/sp_clauses.pl

Added new (exported) predicate `collect_orig_clauses`, necessary
   for implementing depth-first local unfolding.  (Elvira Albert)

## [1.0.708] - 2004-10-08

../preprocess_flags.pl

Added flag `df_hom_emb_as` to select the depth-first implementation
of local unfolding with ancestor stacks. The breadth-first
implementation is now `hom_emb_as`.  (Elvira Albert)

## [1.0.707] - 2004-10-08

../spec/unfold_local.pl

Reorganized the code and integrated the local unfolding rule in the
module `unfolding` with the remaining unfolding strategies. Now,
only the local selection of atoms lives here.  (Elvira Albert)

## [1.0.706] - 2004-10-08

../spec/unfold.pl

Added a new depth-first implementation of the local unfolding rule
with ancestors stacks in order to improve efficiency of partial
evaluation in CiaoPP. It can be selected by setting the Local Control
flag (i.e.,`local_control`) to the value `df_hom_emb_as`.
(Elvira Albert)

## [1.0.705] - 2004-10-08

../plai/fixpo_di.pl

Added `initial_guess/7` to control the initial success
substitution used for a predicate that is to be analyzed. Its
objective is twofold: on the one hand, it allows to start the
computation of the success substitution in what 'initial_guess' flag
is set to. On the other hand, it sets the success substitution for
dynamic/multifile predicates to topmost, and adds the corresponding
trust information, if any. (Jesus Correas)

## [1.0.704] - 2004-10-08

../infercost/infercost.pl

Changed lbsize and ubsize analysis names to size_lb and size_ub
respectively (Pedro Lopez Garcia)

## [1.0.703] - 2004-10-08

../infer/infer_dom.pl

Changed lbsize and ubsize analysis names to size_lb and size_ub
respectively (Pedro Lopez Garcia)

## [1.0.702] - 2004-10-08

../driver.pl

Changed lbsize and ubsize analysis names to size_lb and size_ub
respectively.  (Pedro Lopez Garcia)

## [1.0.701] - 2004-10-08

../preprocess_flags.pl

Added help comment for non-failure, determinacy, and cost (and size)
analysis related flags.  (Pedro Lopez Garcia)

## [1.0.700] - 2004-10-06

../plai/fixpo_plai.pl

Modified handling of meta-calls in order to cope with meta-predicates
which have `clause` as meta argument.  (German Puebla)

## [1.0.699] - 2004-10-06

../plai/fixpo_dx_check_common.pl

Modified handling of meta-calls in order to cope with meta-predicates
which have `clause` as meta argument.  (German Puebla)

## [1.0.698] - 2004-10-07

../infer/infer_dom.pl

Added (a call to) translation from parametric to non-parametric types
   before abstract execution (Pawel Pietrzak)

## [1.0.697] - 2004-10-07

../p_unit/p_unit.pl

Removed cut in one_type_clause/2 - it has to be
non-deterministic. Now, user-defined types can have more than 1 rule.
(Pawel Pietrzak)

## [1.0.696] - 2004-10-07

../plai/success.pl

`apply_success_policy/8` adapted to apply the success policy to a
list of (call,success) patterns instead of being specific to the
intermodular scenario only.  This predicate is now exported.  (Jesus
Correas)

## [1.0.695] - 2004-10-07

../plai/entry_policy.pl

Fixed bug which prevented the addition of entry points related to
multifile predicates when a modular program is being analyzed.  (Jesus
Correas)

## [1.0.694] - 2004-10-07

../p_unit/itf_db.pl

Added module to multifile predicates information.  (Jesus Correas)

## [1.0.693] - 2004-10-07

../preprocess_flags.pl

Changed success_policy flag value 'bot' to 'bottom' (to make it equal
to initial_guess values).  (Jesus Correas)

## [1.0.692] - 2004-10-07

../preprocess_flags.pl

Added initial_guess flag to indicate how to obtain the initial guess
when performing the analysis of a predicate of the current module.
(Jesus Correas)

## [1.0.691] - 2004-10-04

../spec/global_control.pl

The flag `comp_rule` is read by the global control and passed to
the local control (Elvira Albert)

## [1.0.690] - 2004-10-04

../preprocess_flags.pl

Added flag `comp_rule` for choosing the computation rule to select
the atoms to be unfolded in the local control of partial evaluation.
(Elvira Albert)

## [1.0.689] - 2004-10-04

../spec/unfold.pl

Existing unfolding strategies have been parameterized with the
computation rule `comp_rule` in order to allow local unfolding.
(Elvira Albert)

## [1.0.688] - 2004-10-04

../spec/unfold_local.pl

Any unfolding strategy can now be performed with 3 different
computation rules: By default, we have `leftmost` unfolding. Then,
`local_builtin` implements a computation rule which first selects
builtins which can be evaluated. Finally, `local_emb` tries to
select atoms which do not endanger the embedding ordering or evaluable
builtins whenever possible.  (Elvira Albert)

## [1.0.687] - 2004-10-02

../spec/spec.pl

Unified handling of dynamic and static abstract executability table
for locating optimizations in specialized versions.  (German Puebla)

## [1.0.686] - 2004-10-02

../spec/spec_multiple.pl

Added predicate `decide_remove_original_exported_predicate` to
make the module interface consistent with the specialized program.
(German Puebla)

## [1.0.685] - 2004-10-03

../plai/intermod.pl

Modified auto_transform/3 to deal with the specialization of modular
programs with cycles in the module dependency graph.  (Jesus Correas)

## [1.0.684] - 2004-10-03

../p_unit/p_abs.pl

Modified the computation of the reachability relation between the
exported predicates of the current module and the predicates imported
from other modules, in order to deal with meta-calls.  (Jesus Correas)

## [1.0.683] - 2004-10-03

../p_unit/p_abs.pl

Added the exported predicate get_all_module_cycles/2 that computes the
post-order traversal of the module graph, grouping the modules
involved in cycles.  Needed by the specializer of modular programs.
(Jesus Correas)

## [1.0.682] - 2004-10-02

../p_unit/itf_db.pl

Added exported predicate `retract_itf/5`.  (German Puebla)

## [1.0.681] - 2004-10-02

../spec/spec_multiple.pl

Improved handling of names for versions which correspond to entries
for exported predicates. See comment in `assign/8`.  (German
Puebla)

## [1.0.680] - 2004-10-02

../plai/plai_errors.pl

Replaced error message with warning message for `conflict`.
(German Puebla)

## [1.0.679] - 2004-09-30

../spec/unfold.pl

Fixed complicated bug in `unfold_one_step`.  (German Puebla)

## [1.0.678] - 2004-10-01

../preprocess_flags.pl

Valid flag values for ana_cost changed to none, steps_ub, steps_lb,
and STEPS_UALB (instead of lower, upper and both). (Pedro Lopez
Garcia)

## [1.0.677] - 2004-09-29

../spec/spec.pl

We now detect optimizations from specialized versions of predicates in
imported modules after abstract specialization has taken place for
them already.  (German Puebla)

## [1.0.676] - 2004-09-28

../auto_interface/auto_interface.pl

Added question in spec menu for flag pres_inf_fail.  (David Trallero
Mena)

## [1.0.675] - 2004-09-28

../spec/unfold_local.pl

Unfolding is no longer restricted to leftmost selection and can be
used now with _local_ selection rules.  (Elvira Albert)

## [1.0.674] - 2004-09-28

../spec/spec_iterate.pl

Literals to the left of a literal which does not succeed are no longer
removed if the flag `pres_inf_fail` is `on`, even if they have
no side-effects.  (German Puebla)

## [1.0.673] - 2004-09-28

../preprocess_flags.pl

Added flag `pres_inf_fail` which controls whether finite failure
should be preserved during specialization or not.  (German Puebla)

## [1.0.672] - 2004-09-27

../p_unit/p_abs.pl

include_parents/0 now propagates information to the ancestor modules
which are not in module_to_analyze_parents/1, instead of including
just immediate parents.  (Jesus Correas)

## [1.0.671] - 2004-09-27

../p_unit/p_abs.pl

get_intermodule_graph/3 has been reimplemented and changed to
get_intermodule_graph/2. It did not return the complete list of
modules to be analyzed.  (Jesus Correas)

## [1.0.670] - 2004-09-27

../p_unit/p_abs.pl

get_intermodule_graph/3 is not exported now.  (Jesus Correas)

## [1.0.669] - 2004-09-24

../Makefile.pl

Minor change in option fullinstall.  (Edison Mera)

## [1.0.668] - 2004-09-23

../spec/abs_exec_ops.pl

changed adapt_info_to_assrt_head, the abstract substitutions nead to
be projected to the goal's variables before to call to call_to_entry
(Claudio Vaucheret)

## [1.0.666] - 2004-09-21

../driver.pl

Came back to the past, now output is saved where the file is read.
(David Trallero Mena)

## [1.0.665] - 2004-09-21

../auto_interface/auto_interface.pl

Restore options are asked if there is any.  (David Trallero Mena)

## [1.0.664] - 2004-09-21

../auto_interface/auto_interface.pl

When selecting 'none' option in type or mode analysis in the check
assertions menu an error raised up. Fixed.  (David Trallero Mena)

## [1.0.662] - 2004-09-21

../preprocess_flags.pl

Added flags: menu_last_config and menu_config_name. Needed for saving
menu configurations in auto_interface.  (David Trallero Mena)

## [1.0.661] - 2004-09-21

../menu_generator.pl

`menu_opt/5` is now `menu_opt/6`. The new argument is a new
hook that is invoked whenever the selected menu option is going to be
printed.  (David Trallero Mena)

## [1.0.660] - 2004-09-21

../menu_generator.pl

Added `get_menu_configs/1`.  (David Trallero Mena)

## [1.0.659] - 2004-09-21

../preprocess_flags.pl

The `modetypeanalysis/1` returned none twice. Fixed.  (David
Trallero Mena)

## [1.0.658] - 2004-09-20

../p_unit/p_dump.pl

Error (arity mismatch) in assertions declaration for `restore`
and `restore/2` solved.  (David Trallero Mena)

## [1.0.657] - 2004-09-20

../p_unit/p_canonical.pl

pred assertions are expanded now according to their status.  (David
Trallero Mena)

## [1.0.656] - 2004-09-20

../p_unit/p_canonical.pl

There was a bug in `decide_status/2`, the possible status of an
assertion is false, not fail.  (David Trallero Mena)

## [1.0.655] - 2004-09-20

../p_unit/p_asr.pl

The 'pred assertions that are read and processed are now saved as
commented assertions to allow producing nice output.  (David Trallero
Mena)

## [1.0.654] - 2004-09-20

../p_unit/p_asr.pl

Added some ':- pred' declaration that were missing.  (David Trallero
Mena)

## [1.0.653] - 2004-09-20

../auto_interface/auto_help.pl

`again/0` is now printed in the command list.  (David Trallero
Mena)

## [1.0.652] - 2004-09-20

../auto_interface/auto_interface.pl

Added `again/0`.  (David Trallero Mena)

## [1.0.651] - 2004-09-20

../preprocess_flags.pl

Added help to dump_ai flag.  (David Trallero Mena)

## [1.0.650] - 2004-09-20

../ciaopp_template.pl

Export `show_asr/1` was missing.  (David Trallero Mena)

## [1.0.649] - 2004-09-20

../plai/success.pl

Added a call to clause_applies/2 to check that a substitution is
applicable.  (Jesus Correas)

## [1.0.648] - 2004-09-20

../plai/entry_policy.pl

Code adapted to handle entry_policy=force (all both user and
intermodular entries must be scheduled for analysis).  (Jesus Correas)

## [1.0.647] - 2004-09-20

../driver.pl

Added code in analyze/2 to provide one-module (manual) modular
analysis capabilities when intermod flag is set to on.  (Jesus
Correas)

## [1.0.646] - 2004-09-20

../p_unit/p_abs.pl

Added recover_from_invalid_state/2 to mark as invalid the entries
which depend on invalid entries or inexistent registry files.  (Jesus
Correas)

## [1.0.645] - 2004-09-20

../p_unit/p_abs.pl

Fixed a bug in replace_imdg_subs/3 ('$query' dependencies were removed
from the imdg list).  (Jesus Correas)

## [1.0.644] - 2004-09-20

../p_unit/p_abs.pl

Fixed a bug in compute_scc_depth/2 (some modules appeared in the depth
table with several depths, while others did not appear).  (Jesus
Correas)

## [1.0.643] - 2004-09-20

../p_unit/p_abs.pl

Added cut in `upload_typedefs/2` to prevent backtracking (it
succeeded twice!).  (Jesus Correas)

## [1.0.642] - 2004-09-20

../p_unit/p_abs.pl

`get_modules_to_analyze/3` changed to add a flag for each module
for forcing reanalysis of all its entries.  (Jesus Correas)

## [1.0.641] - 2004-09-15

../preprocess_flags.pl

Added entry in `valid_flag_value/2` to analysis_info.  (David
Trallero Mena)

## [1.0.640] - 2004-09-15

../ciaopp_template.pl

Added perform_init_checks.  (David Trallero Mena)

## [1.0.639] - 2004-09-15

../ciaopp_template.pl

Added reexport( auto_interface( auto_help ) ).  (David Trallero Mena)

## [1.0.638] - 2004-09-15

../auto_interface/auto_interface.pl

Predicate `auto_check_assert/1` was not considering all options.
(David Trallero Mena)

## [1.0.637] - 2004-09-15

../preprocess_flags.pl

Added `pp_flag` regtype definition.  (David Trallero Mena)

## [1.0.636] - 2004-09-15

../preprocess_flags.pl

To be coherent , assert_ctchecks is on off instead of none yes.
(David Trallero Mena)

## [1.0.635] - 2004-09-15

../preprocess_flags.pl

Typo in ass_not_stat_eval options: erro -> error.  (David Trallero
Mena)

## [1.0.626] - 2004-09-12

../driver.pl

acheck2 is now acheck.  (David Trallero Mena)

## [1.0.625] - 2004-09-12

../driver.pl

Removed calls to old runtime and compile-time code.  (David Trallero
Mena)

## [1.0.624] - 2004-09-12

../printer.pl

Fixed bugs 3, 4 and 5.  (David Trallero Mena)

## [1.0.618] - 2004-09-10

../p_unit/unexpand.pl

Added 1 clause to predicate `generate_unexpanded_data/1` which
control the user(_) module load.  (David Trallero Mena)

## [1.0.617] - 2004-09-10

../p_unit/p_asr.pl

Solved bug 15.  (David Trallero Mena)

## [1.0.616] - 2004-09-09

../plai/intermod.pl

Call to driver:modules/1 replaced to driver:module/1.  (Jesus Correas
Fernandez)

## [1.0.615] - 2004-09-09

../p_unit/p_unit.pl

Removed redundant code in preprocessing_unit/3 (Jesus Correas
Fernandez)

## [1.0.614] - 2004-09-09

../p_unit/p_asr.pl

Documented use of preprocessing_unit/3 when first and second arguments
are lists instead of file names.  (Jesus Correas Fernandez)

## [1.0.613] - 2004-09-09

../driver.pl

Removed exported predicates modules/1 and modules/2. Now module/1 and
module/2 are polymorphic and can receive either a source file name or
a list of file names.  (Jesus Correas Fernandez)

## [1.0.612] - 2004-09-08

../plai/domains/gr.pl

Added a cut for $bottom in gr_sort/2 (it raised an error on
backtracking).  (Jesus Correas Fernandez)

## [1.0.611] - 2004-09-08

../plai/domains/typeslib/typeslib.pl

The `type_intersection/3` cannot be exported as it is
internal!. Use `type_intersection_2/3` instead.  (David Trallero
Mena)

## [1.0.610] - 2004-08-30

../spec/unfold.pl

Reorganized and further modularized code. Now this module only exports
`unfold/7`. The rest of previously exported predicates are now in
auxilary modules.  (German Puebla)

## [1.0.609] - 2004-08-30

../spec/unfold_operations.pl

Exported predicate `replicate_atoms/4` now lives here.  (German
Puebla)

## [1.0.608] - 2004-08-30

../spec/sp_clauses.pl

Now code for handling clauses during partial evaluation lives here.
(German Puebla)

## [1.0.607] - 2004-08-30

../spec/useless_clauses.pl

Code related to removal of useless clauses now lives here (German
Puebla)

## [1.0.606] - 2004-08-21

../spec/arg_filtering.pl

Predicate `create_pretty_dict/2` and auxiliary predicates have
been improved and moved to ciao library `vndict`.  (German Puebla)

## [1.0.603] - 2004-08-08

../p_unit/p_canonical.pl

Added `compound_to_simple_assrt/2` and
`compound_to_simple_assrt_same_pred/2`. (David Trallero Mena)

## [1.0.602] - 2004-08-08

../p_unit/p_asr.pl

Assertions are simplified when generating the .ast file.  (David
Trallero Mena)

## [1.0.601] - 2004-08-08

../p_unit/p_asr.pl

Added show_asr.  (David Trallero Mena)

## [1.0.600] - 2004-08-08

../p_unit/p_asr.pl

Fixed bug 7. The same asr file was read several times.  (David
Trallero Mena)

## [1.0.599] - 2004-08-06

../infercost/infercost.pl

Modified output_complexity_trust_info/9 so that cost analysis info is
asserted in module infer_db with identifiers steps_ub (upper bounds)
and steps_lb (lower bounds) (Pedro Lopez Garcia)

## [1.0.598] - 2004-08-06

../driver.pl

Modified analyze_/4 so that currently cost analysis options are:
steps_ub (upper bounds), steps_lb (lower bounds) and steps_ualb (both,
upper and lower bounds).  (Pedro Lopez Garcia)

## [1.0.597] - 2004-08-03

../p_unit/p_canonical.pl

Not asked for get_key_predicates, as we have to normalize all pred
assertions.  (David Trallero Mena)

## [1.0.596] - 2004-07-30

../p_unit/unexpand.pl

Added code in `transform_body/2` necessary to treat (A;B) (that
appears in assertions body).  (David Trallero Mena)

## [1.0.595] - 2004-07-30

../p_unit/p_canonical.pl

Recoded a bit, to allow better integration with c_itf and Ciao in the
   future.  (David Trallero Mena)

## [1.0.594] - 2004-07-30

../p_unit/p_asr.pl

Added has_to_be_asserted.  (David Trallero Mena)

## [1.0.593] - 2004-07-30

../p_unit/clause_db.pl

clause_locator still had bugs.  (David Trallero Mena)

## [1.0.592] - 2004-07-30

../p_unit/clause_db.pl

Added add_clause_locator.  (David Trallero Mena)

## [1.0.591] - 2004-07-30

../printer.pl

Removed uncessary code for printing output (print_imported_modules).
(David Trallero Mena)

## [1.0.590] - 2004-07-30

../printer.pl

Fixed bug 13.  (David Trallero Mena)

## [1.0.589] - 2004-07-30

../driver.pl

The pp output is saved into the loaded directory file, not in the
working directory of ciaopp buffer.  (David Trallero Mena)

## [1.0.588] - 2004-07-29

../Makefile.pl

Added the option reconfigure, reconfiguresrc and installsrc to let
ciaopp can be loaded from the source instead of the installed
libraries.  This will be usefull for ciaopp developers.  (Edison Mera)

## [1.0.587] - 2004-07-28

../Makefile.pl

Corrected some incorrect behavior in the createdoc option.  (Edison
Mera)

## [1.0.586] - 2004-07-28

../dist/Makefile.pl

Now the creation of distribution takes the more recent source from the
cvs.  (Edison Mera)

## [1.0.585] - 2004-07-28

../plai/intermod.pl

Got rid of m_unit for performing monolithic analysis. Now multimodule
loading is available from p_unit and p_asr.  (Jesus Correas Fernandez)

## [1.0.584] - 2004-07-26

../p_unit/p_asr.pl

Internal predicates `related_file/1` and `processed_file/1`
now store basenames instead of full module file names.  (Jesus Correas
Fernandez)

## [1.0.583] - 2004-07-26

../p_unit/p_unit.pl

Added in preprocessing_unit/3 code for handling a list of current
modules.  (Jesus Correas Fernandez)

## [1.0.582] - 2004-07-26

../p_unit/p_asr.pl

calls to `absolute_file_name/2` changed to
   `absolute_file_name/7`.  (Jesus Correas Fernandez)

## [1.0.581] - 2004-07-26

../p_unit/aux_filenames.pl

calls to `absolute_file_name/2` changed to
`absolute_file_name/7`.  (Jesus Correas Fernandez)

## [1.0.580] - 2004-07-26

../driver.pl

Added exported predicate modules/1-2 to load a list of current modules
into CiaoPP.  (Jesus Correas Fernandez)

## [1.0.578] - 2004-07-22

../Makefile.pl

Changed option environment.  Now it generate all the configuration
files.  (Edison Mera)

## [1.0.577] - 2004-07-22

../dist/Makefile.pl

Added option environment that configures ciaopp correctly.  (Edison
Mera)

## [1.0.576] - 2004-07-22

../spec/spec.pl

Handling of `equiv` assertions in now done using
`adapt_info_to_assrt_head/5`.  (German Puebla)

## [1.0.575] - 2004-07-22

../spec/abs_exec_ops.pl

Added exported predicate `adapt_info_to_assrt_head/5`.  (German
Puebla)

## [1.0.574] - 2004-07-20

../paths.pl

Moved options to paths_common.  (Edison Mera)

## [1.0.573] - 2004-07-20

../Makefile.pl

Modified the installation process.  Now it copies the library and
binary files to directories given by LIBDIR and BINDIR.  (Edison Mera)

## [1.0.572] - 2004-07-20

../spec/modular_spec.pl

`equiv/2` now has a `meta_predicate` declaration which makes
it not necessary to module qualify by hand.  (German Puebla)

## [1.0.571] - 2004-07-19

../spec/spec.pl

The specializer can now properly handle literals which are calls to
predicates imported from other modules for which an `equiv`
assertion exists. In the preconditions in the assertion are proved to
hold, the literal is replaced by its corresponding optimized
version. Both monovariant and polyvariant specialization now profit
from `equiv` declarations.  (German Puebla)

## [1.0.570] - 2004-07-19

../spec/abs_exec_cond.pl

Now `cond/4` can handle `ground` tests with non-variable
arguments.  (German Puebla)

## [1.0.569] - 2004-07-19

../spec/abs_exec_cond.pl

Added exported predicate `abs_exec_conj_props/3`.  (German
Puebla)

## [1.0.568] - 2004-07-19

../spec/modular_spec.pl

Now `generate_abs_execs_from_equivs/0` qualifies predicate names
by hand.  (German Puebla)

## [1.0.567] - 2004-07-19

../spec/spec_multiple.pl

Optimized generation of multiply specialized program by introducing
`decide_replace_version/2`.  (German Puebla)

## [1.0.566] - 2004-07-19

../spec/static_abs_exec_table.pl

`ground/1` is now also executable to _true_ under condition
`ground(1)`, in addition to being executable to _ground/1_ which
is handled directly by the specializer.  (German Puebla)

## [1.0.565] - 2004-07-19

../spec/abs_exec_ops.pl

Created module `abs_exec_ops`.  (German Puebla)

## [1.0.564] - 2004-07-19

../spec/spec_gen_pred_vers.pl

All the stuff related to the generation of the multiply specialized
program after version minimization lives now in module
`spec_gen_pred_vers`.  (German Puebla)

## [1.0.563] - 2004-07-17

../p_unit/p_unit.pl

Fixed tr_syntax bug with brutal force.  (David Trallero Mena)

## [1.0.562] - 2004-07-16

../spec/spec.pl

Now also multivariant specialization of partially instantiated
literals for regular types is working.  (German Puebla)

## [1.0.561] - 2004-07-16

../spec/abs_exec_cond.pl

Added exported predicate
`abs_exec_reg_type_with_post_info_one_version/5 (German Puebla)

## [1.0.560] - 2004-07-16

../tr_syntax/tr_syntax.pl

Last clause of predicate `remove_disjunctions__/10` left some
free variables.  (David Trallero Mena)

## [1.0.559] - 2004-07-16

../p_unit/p_unit.pl

normalize_assertions predicate moved to p_canonical
module.  (David Trallero Mena)

## [1.0.558] - 2004-07-16

../p_unit/p_canonical.pl

Several `pred` are transformed into `calls` assertion with
disjuntion of call pred assertion body as body.  (David Trallero Mena)

## [1.0.557] - 2004-07-16

../printer.pl

The output contains rtchecks package only if it is necessary.  (David
Trallero Mena)

## [1.0.556] - 2004-07-16

../printer.pl

Filename contains the name of analysis and transformations applied.
(David Trallero Mena)

## [1.0.555] - 2004-07-16

../spec/spec.pl

Implemented mono variant specialization of partially instantiated
calls to regular types via the use of
{abs_exec_reg_type_with_post_info/4`.  (German Puebla)

## [1.0.554] - 2004-07-16

../spec/abs_exec_cond.pl

Added exported predicate `abs_exec_reg_type_with_post_info/4`.
(German Puebla)

## [1.0.553] - 2004-07-16

../plai/domains/typeslib/regtype_basic_lattice.pl

Added exported predicate `translate_lattice_types/4`.  (German
Puebla)

## [1.0.549] - 2004-07-15

../plai/fixpo_ops.pl

Added copy_completes/1 to the exported predicates list. It is needed
by intermod.  (Jesus Correas Fernandez)

## [1.0.548] - 2004-07-15

../p_unit/p_abs.pl

Registry file name generation moved to aux_filenames.pl.  (Jesus
Correas Fernandez)

## [1.0.547] - 2004-07-15

../p_unit/aux_filenames.pl

Source file creation.  (Jesus Correas Fernandez)

## [1.0.546] - 2004-07-15

../p_unit/p_asr.pl

Added support for writing asr files (in ciaopp format, with '.ast'
extension). asr files are stored where `asr_dir` flag indicates:
either the directory where the corresponding source file resides, or a
given directory for all source files. Assertion reading procedure does
not fail if asr files cannot be written on disk (in order to work with
library directories with user write permissions disabled.  (Jesus
Correas Fernandez)

## [1.0.545] - 2004-07-15

../preprocess_flags.pl

Added `asr_dir` flag to set the directory where asr files are to
be stored. This flag can be either `source` to indicate that the
asr files are stored in the same directory where the source file is
located, or an atom with a valid directory specification.  (Jesus
Correas Fernandez)

## [1.0.544] - 2004-07-14

../spec/s_simpspec.pl

Reimplemented `next_or_last_key` so that it behaves correctly in
the presence of cut literals without keys and without making any
assumption on the internal representation of keys.  (German Puebla)

## [1.0.542] - 2004-07-14

../driver.pl

Now `all_versions/5` is imported from module `spec_multiple`
instead of `spec`.  (German Puebla)

## [1.0.541] - 2004-07-14

../spec/static_abs_exec_table.pl

The static abstract executability table now lives in module
   `static_abs_exec_table`.  (German Puebla)

## [1.0.540] - 2004-07-14

../spec/modular_spec.pl

This module contains the dynamic abstract executability table for
predicates defined in imported modules. This table contains both
specialized versions introduced by hand and automatically generated.
(German Puebla)

   
## [1.0.539] - 2004-07-14

../spec/spec_multiple.pl

The machinery for performing (minimal) multiple specialization now
lives in module `spec_multiple`.  (German Puebla)

## [1.0.538] - 2004-07-14

../spec/spec_iterate.pl

Iterative optimization of programs now lives in module
`spec_iterate`.  (German Puebla)

## [1.0.537] - 2004-07-14

../spec/abs_exec_cond.pl

The abstract execution of conditions under which a literal can be
abstractly executed now lives in module `abs_exec_cond`.  (German
Puebla)

## [1.0.531] - 2004-07-07

../plai/plai.pl

Fixpoint module fixpo_di_mod removed. Now intermodular analysis is
integrated into fixpo_di.  (Jesus Correas Fernandez)

## [1.0.530] - 2004-07-07

../plai/intermod.pl

Fixpoint module fixpo_di_mod removed. Now intermodular analysis is
integrated into fixpo_di.  (Jesus Correas Fernandez)

## [1.0.529] - 2004-07-07

../preprocess_flags.pl

'fixpoint' option 'di_mod' removed. Now intermodular analysis is
integrated into 'di' fixpoint.  (Jesus Correas Fernandez)

## [1.0.528] - 2004-07-07

../spec/spec.pl

Implemented fully fledged handling of useless clauses. This includes
removing both facts and rules not only when there is no complete which
unifies with the clause but also when the abstract call pattern is
incompatible with the head of the clause. If these optimizations can
only be done in specialized versions, several versions will be
generated. I.e., useless clauses are now first class citizens for the
abstract specializer, same as abstractly executable literals.  (German
Puebla)

## [1.0.527] - 2004-07-07

../plai/fixpo_plai.pl

In `body_succ/8`, the success substitution is bottom whenever the
call substitution is bottom. Rather than using `bottom/1` to
generate the success substition, it is more efficient to unify it with
the call substitution, which we know is bottom. (German Puebla)

## [1.0.526] - 2004-07-07

../plai/fixpo_di.pl

In `body_succ/8`, the success substitution is bottom whenever the
call substitution is bottom. Rather than using `bottom/1` to
generate the success substition, it is more efficient to unify it with
the call substitution, which we know is bottom.  (German Puebla)

## [1.0.524] - 2004-07-05

../p_unit/p_unit.pl

Added decide_status (David Trallero Mena)

## [1.0.523] - 2004-07-05

../spec/unfold.pl

Important changes in order to take the abstract substitution into
acccount during local control. Not finished yet though.  (German
Puebla)

## [1.0.522] - 2004-07-05

../spec/unfold.pl

Useless clauses can now be removed during local control according to
the value of flag `rem_use_cls`.  (German Puebla)

## [1.0.521] - 2004-07-05

../spec/global_control.pl

Important changes in order to make global control depend not only on
the concrete call pattern but also to take the abstract call pattern
into account.  (German Puebla)

## [1.0.520] - 2004-07-05

../preprocess_flags.pl

Added the flag `abs_exec` which controls whether abstract
executability should be performed directly during local control rather
than as a post processing phase.  (German Puebla)

## [1.0.519] - 2004-07-05

../preprocess_flags.pl

Added the value `id_abs` for flag `global_control`. It differs
from `id` in that not only the concrete part but also the abstract
part has to be equivalent in order to reuse a specialized definition.
(German Puebla)

## [1.0.518] - 2004-07-05

../preprocess_flags.pl

The value `hom_emb_l` for `local_control` has been globally
renamed to `hom_em_as` which stands for homeomorphic embedding with
ancestor stacks.  (German Puebla)

## [1.0.517] - 2004-07-05

../preprocess_flags.pl

Added flag `rem_use_cls` which controls whether removal of useless
clauses, i.e., those incompatible with the abstract call pattern,
should be performed during local control.  (German Puebla)

## [1.0.516] - 2004-07-02

../plai/domains/eterms.pl

eterms:eterms_rename_abs/4 modified to create a new name for every
type in the substitutions coming from an external repository
--registry file, dump file-- (this is what is done when an entry
assertion is analyzed).  (Jesus Correas Fernandez)

## [1.0.514] - 2004-07-02

../plai/success.pl

Added typedef handling to upload type definitions stored in registry
files.  (Jesus Correas Fernandez)

## [1.0.513] - 2004-07-02

../plai/intermod.pl

intermod flag reintroduced.  (Jesus Correas Fernandez)

## [1.0.512] - 2004-07-02

../plai/intermod.pl

Intermodule graph code moved to p_unit/p_abs.pl.  (Jesus Correas
Fernandez)

## [1.0.511] - 2004-07-02

../plai/intermod.pl

top_level_module/1 changed to top_level_module/2 for providing
top-level module basename.  (Jesus Correas Fernandez)

## [1.0.510] - 2004-07-02

../plai/fixpo_di.pl

Bug fixed which prevented intermodular analysis from working properly
(complete_parent/2 must be asserted whenever complete/6 is asserted).
(Jesus Correas Fernandez)

## [1.0.509] - 2004-07-02

../plai/entry_policy.pl

Added typedef handling to upload type definitions stored in registry
files.  (Jesus Correas Fernandez)

## [1.0.508] - 2004-07-02

../p_unit/p_abs.pl

upload_typedefs/2 added to rebuild type information from registry
files.  (Jesus Correas Fernandez)

## [1.0.507] - 2004-07-02

../p_unit/p_abs.pl

Intermodule graph traversal now uses tarjan algorithm to compute
strongly connected components.  (Jesus Correas Fernandez)

## [1.0.506] - 2004-07-02

../p_unit/p_abs.pl

Added code for creating .reg files for every module involved in the
analysis of a program unit, even if the .reg file is empty (for
library modules, this is enabled only if process_libraries flag is set
to 'on'). This behaviour is needed to perform incremental intermodular
analysis.  (Jesus Correas Fernandez)

## [1.0.505] - 2004-07-02

../p_unit/p_abs.pl

Bug fixed in get_modules_to_analyze/3. When intermod:auto_analyze/2
was used for reanalysing a program unit previously analyzed with
changes in some modules, get_modules_to_analyze/3 returned _all_ the
modules in the program unit except the top-level, instead of returning
only those with invalid registry information.  (Jesus Correas
Fernandez)

## [1.0.504] - 2004-07-02

../paths.pl

added path to `api` (David Trallero Mena)

## [1.0.503] - 2004-07-02

../spec/s_simpspec.pl

changed next_or_last_key([A|_],K,K1) (David Trallero Mena)

## [1.0.502] - 2004-07-02

../spec/abs_exec.pl

Chanted bot_type by is_empty_bottom. This is because bot_type means
bot, not that type intersection is bot.  (David Trallero Mena)

## [1.0.501] - 2004-07-02

../p_unit/unexpand.pl

Modifications when printing assertions. Now they are well printed
(without ' in names) (David Trallero Mena)

## [1.0.500] - 2004-07-02

../p_unit/p_unit.pl

Added metrapred in type_of_goal for correct unexpand when printing
output Corrected a bug in bug numbers

    (David Trallero Mena)

## [1.0.499] - 2004-07-02

../p_unit/clause_db.pl

modified locate_clause_locator to throw and error when needed. Also
some cuts added because empty solutions were given.

    (David Trallero Mena)

## [1.0.498] - 2004-07-02

../plai/domains/typeslib/typeslib.pl

is_empty_type exported (David Trallero Mena)

## [1.0.497] - 2004-07-02

../driver.pl

added acheck2... testing now till current implementation will converge
(David Trallero Mena)

## [1.0.496] - 2004-07-02

../driver.pl

changed runtime names to rtc (David Trallero Mena)

## [1.0.495] - 2004-07-02

../dist/Makefile.pl

Corrected a bug when creating a new source distribution.  (Edison
Mera)

## [1.0.494] - 2004-07-02

../Makefile.pl

Corrected a bug when calling the predicate list_files_filter_rec/8.
   (Edison Mera)

## [1.0.493] - 2004-07-01

../Makefile.pl

Corrected method to compile CiaoPP.  Now a simple call to use_module/2
is used. (Edison Mera)

## [1.0.492] - 2004-07-01

../doc/Makefile.pl

Corrected a bug that appears when creating the SETTINGS file. (Edison
Mera)

## [1.0.491] - 2004-07-01

../Makefile.pl

Corrected some bugs when installing documentation in the info file.
(Edison Mera)

## [1.0.490] - 2004-06-30

../dist/Makefile.pl

distsettings.pl renamed to DISTSETTINGS.pl (Edison Mera)

## [1.0.486] - 2004-06-30

../Makefile.pl

Now the install compiles CiaoPP, and places the documentation in the
correct place.  (Edison Mera)

## [1.0.485] - 2004-06-23

../Makefile.pl

The installation process now compiles CiaoPP.  Corrected a bug that
changed the default behavior when there was no `.ciaorc` file
(thanks to Manuel Hermenegildo).  (Edison Mera)

## [1.0.484] - 2004-06-22

../plai/tarjan.pl

Predicate `step2/2` is now exported. The Tarjan algorithm is also
used by intermodular analysis (by means of this predicate).  (Jesus
Correas Fernandez)

## [1.0.483] - 2004-06-18

../plai/domains/eterms.pl

With set_pp_flag(type_eval,on) eterms_call_to_success_builtin
evaluates predicates with comp assertion eval. (Claudio Vaucheret)

 
## [1.0.480] - 2004-06-18

../driver.pl

Added rtchecks_pp_ass. (David Trallero Mena)

## [1.0.479] - 2004-06-17

../plai/fixpo_di.pl

`intermod` flag reintroduced to enable/disable intermodular
analysis.  (Jesus Correas Fernandez)

## [1.0.478] - 2004-06-17

../preprocess_flags.pl

`intermod` flag reintroduced to enable/disable intermodular
analysis.  (Jesus Correas Fernandez)

## [1.0.477] - 2004-06-14

../menu_generator.pl

modifications added for new pp_flag multifile definitions. Also bug
corrected in space.  (David Trallero Mena)

## [1.0.476] - 2004-06-14

../plai/fixpo_ops.pl

Now `inexistent/2` does not fail when called with a goal which is
in a clause whose lines are not known. Added comment(bug) reminding
this should be solved.  (German Puebla)

## [1.0.475] - 2004-06-01

../plai/intermod.pl

dump_flag_list added (David Trallero Mena)

## [1.0.474] - 2004-05-23

../preprocess_flags.pl

In ':- pred' callable and not goal have to be used. Also some typed
corrected (David Trallero Mena)

## [1.0.473] - 2004-05-19

../auto_interface/auto_interface.pl

Collapse AI infor is always asked now (David Trallero Mena)

## [1.0.472] - 2004-05-15

../auto_interface/auto_interface.pl

ana_gto changed (now fixpoint is aked if local_control=off,
independetly of types).  (David Trallero Mena)

## [1.0.471] - 2004-05-15

../auto_interface/auto_interface.pl

changed ana_g2 and added nf_not_selected (David Trallero Mena)

## [1.0.470] - 2004-05-14

../menu_generator.pl

added menu/2 (David Trallero Mena)

## [1.0.469] - 2004-05-14

../auto_interface/auto_interface.pl

help sentece appears only once (David Trallero Mena)

## [1.0.468] - 2004-05-14

../auto_interface/auto_interface.pl

collapse_ai_info flag asked if pp_info is selected (David Trallero
Mena)

## [1.0.467] - 2004-05-14

../menu_generator.pl

mult_display_list now prints 1 space more for better indenting (David
Trallero Mena)

## [1.0.466] - 2004-05-14

../auto_interface/auto_interface.pl

added ana_g2 restriction.  (David Trallero Mena)

## [1.0.465] - 2004-05-10

../preprocess_flags.pl

inter_all has no none option now (MH) (David Trallero Mena)

## [1.0.464] - 2004-05-10

../auto_interface/auto_interface.pl

'Select:' is no printed with Label (David Trallero Mena)

## [1.0.463] - 2004-05-10

../auto_interface/auto_interface.pl

Save flags saves expert and naive menu flags (David Trallero Mena)

## [1.0.462] - 2004-05-03

../auto_interface/auto_interface.pl

menu_level asked in customize( all ) (David Trallero Mena)

## [1.0.461] - 2004-05-03

../preprocess_flags.pl

menu_level flag added (David Trallero Mena)

## [1.0.460] - 2004-05-03

../auto_interface/auto_interface.pl

compile time check set to yes in check_assertions menu (David Trallero
Mena)

## [1.0.459] - 2004-05-02

../preprocess_flags.pl

flag value 'user' for type_output and type_precision flags changed by
'defined' (Claudio Vaucheret)

## [1.0.458] - 2004-05-03

../auto_interface/auto_interface.pl

type_output is asked in all type analysis (David Trallero Mena)

## [1.0.457] - 2004-05-03

../auto_interface/auto_interface.pl

Analysis cost does not appear in check_assertions (David Trallero
Mena)

## [1.0.456] - 2004-04-30

../auto_interface/auto_interface.pl

 Added to documentation.  Added different menu levels Added
set_menu_level and current_menu_level

    (David Trallero Mena)

## [1.0.455] - 2004-04-30

../preprocess_flags.pl

ass_not_eval_flag changed to off, warning, error (David Trallero Mena)

## [1.0.454] - 2004-04-30

../preprocess_flags.pl

The flag `part_conc` now has 3 possible values.  (German Puebla)

## [1.0.453] - 2004-04-28

../ctchecks/assrt_ctchecks_common.pl

Added retract_fact for calls, since will be asserted by _pred
afterwards (Francisco Bueno Carrillo)

## [1.0.452] - 2004-04-28

../plai/transform.pl

Cut not deleted from source anymore.  (Francisco Bueno Carrillo)

## [1.0.451] - 2004-04-28

../spec/unfold.pl

Fail clauses are now added for predicates which are shown to fail
during partial evaluation. This has several pros (side_effect analysis
sees those predicates, run_time execution will not reach undefined
predicates) and the cons that the final program can be a bit
larger. The abstract specializer should be able to remove those fail
clauses in the end.  (German Puebla)

## [1.0.450] - 2004-04-28

../plai/fixpo_di.pl

The new names in `compute_each_change` still gave
problems. Hopefully finally fixed now.  (German Puebla)

## [1.0.449] - 2004-04-28

../plai/domains.pl

Added domain `pdb`.  (German Puebla)

## [1.0.448] - 2004-04-28

../plai/domains.pl

Fixed bug in `call_to_success_fact` for the `pd` domain.
(German Puebla)

## [1.0.447] - 2004-04-28

../plai/domains/pdb.pl

Added pdb domain.  (German Puebla)

## [1.0.446] - 2004-04-28

../preprocess_flags.pl

The default value for the `ass_not_stat_eval` flag is now
`ignore`.  (German Puebla)

## [1.0.445] - 2004-04-27

../auto_interface/auto_interface.pl

bug in check_assertions customize menu. Just added ifthenelse in
ana_g1 (David Trallero Mena)

## [1.0.444] - 2004-04-26

../plai/fixpo_ops.pl

now compare_with_previous_analysis has a third argument. When it is
'=' (or a free variable) it compares for identical abstract
substitutions, when it is '=<' comparations is for less or equal
abstract substitutions

    (Claudio Vaucheret)

## [1.0.443] - 2004-04-26

../plai/domains/termsd.pl

Solved problem when there were several types for the same variable in
   an assertion.  (Francisco Bueno Carrillo)

## [1.0.442] - 2004-04-26

../ctchecks/assrt_ctchecks_pred.pl

notify warning or error when assertion cannot be reduced (David
Trallero Mena)

## [1.0.441] - 2004-04-26

../plai/domains/eterms.pl

Solved problem when there were several types for the same variable in
an assertion.  (Francisco Bueno Carrillo)

## [1.0.440] - 2004-04-26

../plai/domains/typeslib/typeslib.pl

Fixed bug in get_compatible_types/4: it works when the second argument
is gnd (Pedro Lopez Garcia)

## [1.0.439] - 2004-04-26

../plai/domains/eterms.pl

Added eterms_mult_part_conc which extends part_conc and gives
instantiations of goals even in the case types are not deterministic,
it generates a List of pairs of goals and substitution stop unfolding
types as soon as they are recursive. (Claudio Vaucheret)

## [1.0.438] - 2004-04-26

../plai/domains.pl

Added multi_part_conc/4 (Claudio Vaucheret)

## [1.0.437] - 2004-04-22

../preprocess_flags.pl

ass_not_stat_eval flag added to define ctchecks behaviour on none
checked or false assertions (David Trallero Mena)

## [1.0.436] - 2004-04-21

../spec/spec.pl

Adapted handling of exported predicates to the case of new names
generated by unfolding.  (German Puebla)

## [1.0.435] - 2004-04-21

../spec/unfold_operations.pl

Added new exported predicates.  (German Puebla)

## [1.0.434] - 2004-04-21

../spec/unfold.pl

Several predicates moved to module unfold_operations.pl (German
Puebla)

## [1.0.433] - 2004-04-21

../plai/fixpo_di.pl

Fixed a nasty bug when analysis has to iterate via
`compute_each_change` related to different names of predicates
when local_control is not off.  (German Puebla)

## [1.0.432] - 2004-04-21

../spec/unfold_operations.pl

Some auxiliary predicates for unfolding now live here.  (German
Puebla)

## [1.0.431] - 2004-04-19

../spec/unfold.pl

Added the `hom_emb_l` unfolding rule. It provides a much more
efficient and aggresive behaviour than `hom_emb` by using a
pushdown automata for removing unneeded atoms from the set.  (German
Puebla)

## [1.0.430] - 2004-04-19

../spec/unfold.pl

Major rewrital of unfolding rules by replacing internal representation
of specialized definitions.  (German Puebla)

## [1.0.429] - 2004-04-19

../spec/spec.pl

All unifications introduced by unfolding are now marked as
`no_info` using `put_no_keys/2`.  (German Puebla)

## [1.0.428] - 2004-04-19

../spec/homeo_emb.pl

Improved implementation by taking code from MECCE.  (German Puebla)

## [1.0.427] - 2004-04-19

../preprocess_flags.pl

Added `hom_emb_l` as new value for `local_control`. It is also
the default value.  (German Puebla)

## [1.0.426] - 2004-04-13

../spec/unfold.pl

Added the `hom_emb` unfolding rule which guarantees local
termination by not unfolding atoms which are embedded in atoms already
unfolded in the current derivation.  (German Puebla)

## [1.0.425] - 2004-04-13

../spec/unfold.pl

Modified the `first_sol` unfolding rule to stop as soon as a
residual derivation is found instead of all branches solution or
residual.  (German Puebla)

## [1.0.424] - 2004-04-08

../plai/fixpo_ops.pl

Adapted `inexistent` and `variable` to work with clauses
introduced by partial evaluation.  (German Puebla)

## [1.0.423] - 2004-04-08

../auto_interface/auto_interface.pl

Improved handling of `decide_transform/1`.  (German Puebla)

## [1.0.422] - 2004-04-08

../p_unit/clidlist.pl

Added exported predicate `orig_clause_id/2`.  (German Puebla)

## [1.0.421] - 2004-04-08

../spec/global_control.pl

Added support for filtering numbers in order to guarantee global
termination.  (German Puebla)

## [1.0.420] - 2004-04-05

../p_unit/p_abs.pl

.reg files are now stored in the directory set by tmp_dir pp flag. If
tmp_dir is set to 'source', then .reg files are stored in the same
directory where the corresponding source file resides.  (Jesus Correas
Fernandez)

## [1.0.419] - 2004-04-05

../p_unit/p_abs.pl

Bug fixed in compute_external_reachability/0.  (Jesus Correas
Fernandez)

## [1.0.418] - 2004-04-05

../p_unit/p_abs.pl

module_is_processable/1 added to generalize library analysis control.
(Jesus Correas Fernandez)

## [1.0.417] - 2004-04-05

../plai/intermod.pl

First version of automatic intermodular unfolding (it needs further
improvements yet).  (Jesus Correas Fernandez)

## [1.0.416] - 2004-04-05

../plai/intermod.pl

Implementation of the intermodular analysis of a complete program,
including libraries. p_abs:module_is_processable/1 used to generalize
processable modules for library handling.  (Jesus Correas Fernandez)

## [1.0.415] - 2004-04-05

../plai/fixpo_di.pl

Some modifications to introduce latest changes to fixpo_di.pl (Jesus
Correas Fernandez)

## [1.0.414] - 2004-04-04

../spec/unfold_builtins.pl

Checking preconditions of assertions (to ensure they are applicable)
now done using '$meta_call'/1.  (German Puebla)

## [1.0.413] - 2004-04-04

../spec/global_control.pl

The data predicate `spec_wrt/10` is now replaced by data
`spec_wrt/3` since all other arguments are not really required
since they can be recovered from `spec_def_for/8`.  (German
Puebla)

## [1.0.412] - 2004-04-04

../spec/unfold.pl

Implemented the new local_control strategy `det_la` which stands
for 'deterministic with look ahead'. This flag uses the `depth`
argument such that the behaviour of the original deterministic rule is
obtained with depth=1. By making depth=2 we can fully unfold qsort
when called with a known input list.  (German Puebla)

## [1.0.411] - 2004-04-04

../spec/unfold.pl

Calls to predicates which can be evaluated are now much more
efficiently performed using the engine predicate
`'$meta_call'/1`.  (German Puebla)

## [1.0.410] - 2004-04-04

../spec/codegen.pl

Added handling of code generation for `bagof`, `setof` and
`findall`. Handling of existential variables has to be tested.
(German Puebla)

## [1.0.409] - 2004-04-04

../plai/fixpo_dx_common.pl

Commented out the special handling of builtin `true/0` in
`entry_to_exit` since it only applied when this was the last
builtin the clause and also makes the corresponding memo_table not
being recorded, which gives problems in partial evaluation.  (German
Puebla)

## [1.0.408] - 2004-04-04

../p_unit/clidlist.pl

Added handling of `bagof`, `setof` and `findall` to
`inverse_rewrite_source_program/2`.  (German Puebla)

## [1.0.407] - 2004-04-04

../spec/homeo_emb.pl

Predicates related to homeomorphic embedding now live in this module.
(German Puebla)

## [1.0.406] - 2004-04-04

../paths.pl

Added path `rtchecks`.  (German Puebla)

## [1.0.405] - 2004-03-31

../p_unit/clidlist.pl

rewrite_source_body does not rewrite atoms which are already of the
form A:K.  (Francisco Bueno Carrillo)

## [1.0.404] - 2004-03-31

../preprocess_flags.pl

Added process_libraries flag.  (Jesus Correas Fernandez)

## [1.0.403] - 2004-03-31

../preprocess_flags.pl

Added tmp_dir flag.  (Jesus Correas Fernandez)

## [1.0.402] - 2004-03-30

../plai/re_analysis.pl

Added renaming/3.  (Francisco Bueno Carrillo)

## [1.0.401] - 2004-03-30

../plai/domains/detplai.pl

Added operation det_statistics/1 in order to compute statistics about
the number of predicates such that all/some of their variants are
deterministic/mutually exclusive (Pedro Lopez Garcia)

## [1.0.400] - 2004-03-30

../plai/domains/detabs.pl

Added operation det_statistics/1 in order to compute statistics about
the number of predicates such that all/some of their variants are
deterministic/mutually exclusive (Pedro Lopez Garcia)

## [1.0.399] - 2004-03-30

../plai/domains/nfdet_statistics.pl

Created this module in order to compute statistics about the nf and
det abstract interpreters (e.g. number of predicates such that
all/some of their variants are
non-failing/covered/deterministics... (Pedro Lopez Garcia)

## [1.0.398] - 2004-03-30

../plai/domains/nfplai.pl

Added operation nf_statistics/1 in order to compute statistics about
the number of predicates such that all/some of their variants are
non-failing/covered (Pedro Lopez Garcia)

## [1.0.397] - 2004-03-30

../plai/domains/nfabs.pl

Added operation nf_statistics/1 in order to compute statistics about
the number of predicates such that all/some of their variants are
non-failing/covered (Pedro Lopez Garcia)

## [1.0.396] - 2004-03-30

../plai/domains.pl

Added a new (domain dependent) operation dom_statistics/2 in order to
generate information about abstract interpreter results, as for
example, statistics about non-failing, covered or deterministic
predicates or variants. If the operation is not defined by an abstract
domain, then the operation succeeds but no information is the
generated (i.e. the empty list is generated) (Pedro Lopez Garcia)

## [1.0.395] - 2004-03-30

../plai/plai.pl

Modified plai/5 in order to generate information about abstract
interpreter results, as for example, statistics about non-failing,
covered or deterministic predicates or variants (besides analysis
times) (Pedro Lopez Garcia)

## [1.0.394] - 2004-03-26

../spec/codegen.pl

Simplified code not to rename exported predicates since that was
complicating things way too much.  (German Puebla)

## [1.0.393] - 2004-03-26

../spec/spec_support.pl

`prepare_ai_info` no longer computes the list of experted
versions.  (German Puebla)

## [1.0.392] - 2004-03-26

../plai/domains/typeslib/dumper.pl

dump_auxiliary_info/2 changed to dump_auxiliary_info/1. This predicate
does not need the domain name.  (Jesus Correas Fernandez)

## [1.0.391] - 2004-03-26

../plai/fixpo_ops.pl

Calls to dumper:dump_auxiliary_info/2 changed to
dump_auxiliary_info/1. Now this predicate does not need the domain
name.  (Jesus Correas Fernandez)

## [1.0.390] - 2004-03-26

../p_unit/p_dump.pl

Calls to dumper:dump_auxiliary_info/2 changed to
dump_auxiliary_info/1. Now this predicate does not need the domain
name.  (Jesus Correas Fernandez)

## [1.0.389] - 2004-03-26

../p_unit/p_abs.pl

Calls to dumper:dump_auxiliary_info/2 changed to
dump_auxiliary_info/1. Now this predicate does not need the domain
name.  (Jesus Correas Fernandez)

## [1.0.388] - 2004-03-26

../spec/unfold.pl

Negation as failure of calls to builtins can now be fully evaluated at
specialization time.  (German Puebla)

## [1.0.387] - 2004-03-26

../spec/codegen.pl

Partial evaluation now handles source programs which contain negation
as failure.  (German Puebla)

## [1.0.386] - 2004-03-25

../spec/codegen.pl

Much more efficient implementation of `replace_calls/2`. Clause
bodies are no longer transformed into list format.  (German Puebla)

## [1.0.385] - 2004-03-25

../p_unit/clidlist.pl

Extended `inverse_rewrite_source_program/2` to handle
meta-predicates correctly.  (German Puebla)

## [1.0.384] - 2004-03-24

../infer/infer_dom.pl

Modified asub_to_info/6 and asub_to_props/4 for adding (two) term size
analysis (separated from time cost analysis): ubsize (upper bounds)
and lbsize (lower bounds).  (Pedro Lopez Garcia)

## [1.0.383] - 2004-03-24

../driver.pl

Modified analyze_/4 for adding (two) term size analysis (separated
from time cost analysis): ubsize (upper bounds) and lbsize (lower
bounds).  (Pedro Lopez Garcia)

## [1.0.382] - 2004-03-24

../infercost/infercost.pl

Implemented (and exported) term_size_analysis/2, for adding (two) term
size analysis (separated from time cost analysis): ubsize (upper
bounds) and lbsize (lower bounds).  (Pedro Lopez Garcia)

## [1.0.381] - 2004-03-23

../p_unit/p_abs.pl

Added type information handling in .reg files. A reg file will contain
the type information for current module exported predicates, imported
modules predicate calls, and calls from other modules to exported
predicates of the current module.  (Jesus Correas Fernandez)

## [1.0.380] - 2004-03-23

../preprocess_flags.pl

Added qualifications to _fact calls to avoid warnings.  (Manuel
menegildo)

## [1.0.379] - 2004-03-23

../preprocess_flags.pl

Flag entry_policy documented.  (Jesus Correas Fernandez)

## [1.0.378] - 2004-03-23

../spec/unfold.pl

Added the `all_sol` unfolding rule which computes all solutions. It
is the most aggresive rule. However, it can only be used if the search
space is finite.  (German Puebla)

## [1.0.377] - 2004-03-23

../spec/unfold.pl

Improved handling of builtins. Now they can be evaluated even if they
are non-deterministic, as long as they universally terminate since
they are avaluated via findall.  (German Puebla)

## [1.0.376] - 2004-03-16

../plai/intermod.pl

The selection of the entry policy applicable to the top-level module
of the current program unit is now moved completely to entry_policy.pl
(Jesus Correas Fernandez)

## [1.0.375] - 2004-03-16

../plai/intermod.pl

top_level_module/1 is now exported for providing the top-level module
of the current program unit.  (Jesus Correas Fernandez)

## [1.0.374] - 2004-03-16

../plai/success.pl

get_module_from_sg/2 predicate moved to p_unit/p_abs.pl (Jesus Correas
Fernandez)

## [1.0.373] - 2004-03-16

../plai/domains/detabs.pl

Improvement: mutual exclusion check (Pedro Lopez Garcia)

## [1.0.372] - 2004-03-15

../preprocess_flags.pl

Added save_config and restore_config (David Trallero Mena)

## [1.0.371] - 2004-03-15

../spec/unfold_builtins.pl

New version. Seems to be what we want. It requires the addition of
`eval` assertions to builtins.  (German Puebla)

## [1.0.370] - 2004-03-09

../ctchecks/assrt_ctchecks_common.pl

Added recorda_assertion.  (Francisco Bueno Carrillo)

## [1.0.369] - 2004-03-09

../spec/unfold.pl

Added null def of peel_call/2.  (Francisco Bueno Carrillo)

## [1.0.368] - 2004-03-09

../infer/infer_dom.pl

Added marshall_args.  (Francisco Bueno Carrillo)

## [1.0.367] - 2004-03-09

../infer/infer_dom.pl

Changed the default of asub_to_out. Now asub_to_info does not
normalize comp properties.  (Francisco Bueno Carrillo)

## [1.0.366] - 2004-03-09

../ctchecks/comp_ctchecks.pl

Adapted to get_info.  (Francisco Bueno Carrillo)

## [1.0.365] - 2004-03-04

../driver.pl

Second argument of module/2 is not only the time.  (Francisco Bueno
Carrillo)

## [1.0.364] - 2004-03-04

../p_unit/p_asr.pl

Added extra argument to return an error flag.  (Francisco Bueno
Carrillo)

## [1.0.363] - 2004-03-03

../spec/unfold_builtins.pl

First version. Uses assertions for describing builtins. Novel
assertions may be required.  (German Puebla)

## [1.0.362] - 2004-03-02

../preprocess_flags.pl

Argument added to pp_flag for documentation.  (David Trallero Mena)

## [1.0.361] - 2004-02-25

../plai/fixpo_di.pl

init_fixpoint_/11 adapted to the analysis of several modules at the
same time.  (Jesus Correas Fernandez)

## [1.0.360] - 2004-02-25

../plai/intermod.pl

monolithic_analyze/2 added to analyze all the modules of a program
unit at the same time.  (Jesus Correas Fernandez)

## [1.0.359] - 2004-02-25

../plai/entry_policy.pl

call_pattern/3 is now internal (not exported).  (Jesus Correas
Fernandez)

## [1.0.358] - 2004-02-25

../plai/entry_policy.pl

get_entry_info/3 adapted to handle the analysis of several modules at
a time.  (Jesus Correas Fernandez)

## [1.0.357] - 2004-02-25

../p_unit/p_unit.pl

Some internal predicates exported to be used from m_unit.pl.  (Jesus
Correas Fernandez)

## [1.0.356] - 2004-02-25

../p_unit/p_asr.pl

Some internal predicates exported to be used from m_unit.pl.  (Jesus
Correas Fernandez)

## [1.0.355] - 2004-02-25

../p_unit/clause_db.pl

Added cleanup_clause_db_code/0 to cleanup module state except
properties.  (Jesus Correas Fernandez)

## [1.0.354] - 2004-02-25

../p_unit/p_abs.pl

get_module_from_sg/2 added to obtain the module where is defined the
predicate referenced in a call pattern.  (Jesus Correas Fernandez)

## [1.0.353] - 2004-02-25

../p_unit/p_abs.pl

Important changes to enable several modules analyzed at the same time.
(Jesus Correas Fernandez)

## [1.0.351] - 2004-02-25

../plai/fixpo_check_di5.pl

Adapted handling of meta-calls.  (German Puebla)

## [1.0.350] - 2004-02-25

../plai/fixpo_di.pl

Imported treatment of meta-calls from fixpo_plai.  (German Puebla)

## [1.0.349] - 2004-02-25

../plai/domains.pl

Identical non variant projections now verifies that the previous goal
is linear (Claudio Vaucheret)

## [1.0.348] - 2004-02-24

../plai/fixpo_di.pl

Imported treatment of meta-calls from fixpo_plai.  (Francisco Bueno
Carrillo)

## [1.0.347] - 2004-02-24

../test/Check_Fixp/test_check_fixp.pl

Changed to new tester libraries (David Trallero Mena)

## [1.0.346] - 2004-02-24

../test/Spec/test_spec.pl

Changed to new tester libraries (David Trallero Mena)

## [1.0.345] - 2004-02-24

../test/Plai/test_plai.pl

Changed to new tester libraries (David Trallero Mena)

## [1.0.344] - 2004-02-24

../test/Out/test_out.pl

changed to new tester libraries (David Trallero Mena)

## [1.0.343] - 2004-02-24

../plai/domains/mutexcheck.pl

First prototype of mutual exclusion check for determinism analysis
(Pedro Lopez Garcia)

## [1.0.342] - 2004-02-24

../infernf/nftests.pl

Exported predicates for det domain (Pedro Lopez Garcia)

## [1.0.341] - 2004-02-24

../infernf/subproblems.pl

Exported predicates for det domain (Pedro Lopez Garcia)

## [1.0.340] - 2004-02-24

../plai/domains/detabs.pl

First prototype of abstract operations for det domain (Pedro Lopez
cia)

## [1.0.339] - 2004-02-24

../plai/domains/detplai.pl

First prototype of determinism analysis using plai (det abstract ain)
(Pedro Lopez Garcia)

## [1.0.338] - 2004-02-24

../plai/fixpo_ops.pl

Improved remove_useless_memo_tables.  (German Puebla)

## [1.0.337] - 2004-02-24

../plai/fixpo_check_di4.pl

Some optimizations.  (German Puebla)

## [1.0.336] - 2004-02-24

../plai/fixpo_check_di5.pl

Optimized version of check_di4 in which redundant arguments are
eliminated and widen of calls is completely ignored.  (German Puebla)

## [1.0.335] - 2004-02-23

../preprocess_flags.pl

Added 'off' value to widencall flag (Claudio Vaucheret)

## [1.0.334] - 2004-02-23

../plai/domains/svterms.pl

Builtin arg/3 now includes the same value component in svterms (Claudio
cheret)

## [1.0.333] - 2004-02-23

../plai/domains/eterms.pl

Added builtins '>/2','>=/2','=</2','</2', to be abstractly evaluated
with concrete values by type_eval flag on (Claudio Vaucheret)

## [1.0.332] - 2004-02-23

../p_unit/p_dump.pl

Assertions in the source file are no longer written to the dump
file. Only analysis results have to be in the dump file!  (German
Puebla)

## [1.0.331] - 2004-02-23

../driver.pl

Added exported predicate `module/2`.  (German Puebla)

## [1.0.330] - 2004-02-20

../p_unit/p_dump.pl

Fixed bug introduced by having memo_tables with void values.  (German
Puebla)

## [1.0.329] - 2004-02-20

../plai/domains/svterms.pl

Added svterms_call_to_success_builtin for functor/3, arg/3 and is/2
(Claudio Vaucheret)

## [1.0.328] - 2004-02-20

../preprocess_flags.pl

Flags dump_level , dump_level_ext removed.  (German Puebla)

## [1.0.327] - 2004-02-20

../p_unit/p_dump.pl

Added predicate `restore/2` which returns in its second argument
the time needed by the operation. Somewhat improved handling of dump
flags.  (German Puebla)

## [1.0.326] - 2004-02-20

../plai/fixpo_ops.pl

Added exported predicate `each_identical_abstract/3`.  (German
Puebla)

## [1.0.325] - 2004-02-19

../p_unit/native.pl

Added & as a native builtin.  (Francisco Bueno Carrillo)

## [1.0.324] - 2004-02-18

../plai/domains/typeslib/dumper.pl

Taken out arg AbsInt from restore_auxiliary_info: could be free and
force backtracking, which reads and ignores several items.  (Francisco
Bueno Carrillo)

## [1.0.323] - 2004-02-18

../plai/plai.pl

Improved handling of the info generated by `plai/5`.  (German
Puebla)

## [1.0.322] - 2004-02-18

../plai/domains/s_grshfr.pl

Added the logic domain operations for parallelization.  (Francisco
Bueno Carrillo)

## [1.0.321] - 2004-02-18

../test/Check_Fixp/test_check_fixp.pl

Tests for analysis checkers ported to the new tester.  (German Puebla)

## [1.0.320] - 2004-02-18

../plai/fixpo_ops.pl

Added exported predicate `reset_previous_analysis/1`.  (German
Puebla)

## [1.0.319] - 2004-02-18

../p_unit/p_dump.pl

Dumps include type definitions.  (Francisco Bueno Carrillo)

## [1.0.318] - 2004-02-17

../plai/fixpo_ops.pl

The three `compare` predicates exported by this module now have an
additional argument `Flag` which is unified with the atom
`error` if one or more errors are found. `Flag` remains a
variable if no errors are found. This is needed for automatically
checking correctness of a test suite.  (German Puebla)

## [1.0.317] - 2004-02-13

../plai/fixpo_ops.pl

Added restore_previous_analysis/1.  (Francisco Bueno Carrillo)

## [1.0.315] - 2004-02-12

../plai/fixpo_ops.pl

Adapted to use typeslib(dumper).  (Francisco Bueno Carrillo)

## [1.0.314] - 2004-02-11

../preprocess_flags.pl

dump_flags added. It is usefull because you can print the value of the
different flags. You also can create your own list using
dump_flags_list multipredicate (David Trallero Mena)

## [1.0.313] - 2004-02-11

../plai/fixpo_plai.pl

Reusing identical projections for calls that are not variants,
implemented all cases (Claudio Vaucheret)

## [1.0.312] - 2004-02-10

../plai/domains.pl

Added rename_types_in_abs/4.  (Francisco Bueno Carrillo)

## [1.0.311] - 2004-02-10

../plai/domains/typeslib/typeslib.pl

Added insert_renamed_type_defs/2.  (Francisco Bueno Carrillo)

## [1.0.310] - 2004-02-10

../p_unit/p_abs.pl

Registry files adapted to include aditional information (e.g., types).
(Jesus Correas Fernandez)

## [1.0.309] - 2004-02-10

../plai/domains.pl

Added collect_types_in_abs/4.  (Francisco Bueno Carrillo)

## [1.0.308] - 2004-02-10

../plai/domains/typeslib/typeslib.pl

Added get_necessary_rules/2.  (Francisco Bueno Carrillo)

## [1.0.307] - 2004-02-06

../spec/spec.pl

Added a postprocessing phase which executes unifications added by
abstract specialization.  (German Puebla)

## [1.0.306] - 2004-02-06

../preprocess_flags.pl

Added flag `exec_unif` which selects whether the unifications
generated by abstract specialization should be executed at
specialization time or just added to the specialized program.  (German
Puebla)

## [1.0.305] - 2004-02-05

../plai/intermod.pl

Now auto_analyze/2 performs intermodular analysis in an incremental
way: before starting modular analysis, looks for existing .reg files
for modules in the program unit, and checks if they need
reanalysis. It only performs the analysis of modules with outdated
.reg files, and other modules which have been affected by the
reanalysis of the former ones.  (Jesus Correas Fernandez)

## [1.0.304] - 2004-02-05

../p_unit/p_abs.pl

Added get_modules_to_analyze/3 to perform incremental intermodular
analysis.  (Jesus Correas Fernandez)

## [1.0.302] - 2004-02-05

../spec/unfold.pl

Two more unfolding strategies implemented: `first_sol` and
`first_sol_d`. The first one unfolds until a first solution (body =
true) is found. The second stops when a depth bound is reached.
(German Puebla)

## [1.0.301] - 2004-02-05

../spec/arg_filtering.pl

Now it outputs time taken by the transformation.  (German Puebla)

## [1.0.299] - 2004-02-05

../Makefile.pl

Reorganized some predicates, to be compatible with the recent changes
in make/system_extra.  (Edison Mera)

## [1.0.298] - 2004-02-04

../plai/fixpo_di.pl

Reusing identical abstractions for calls that are not variants on di
fixpoint (Claudio Vaucheret)

## [1.0.297] - 2004-02-04

../spec/unfold.pl

Corrected bug in the unfolding strategy `det`.  (Elvira Albert)

## [1.0.296] - 2004-02-04

../spec/unfold.pl

Implemented the unfolding strategy `depthk(K)` which expands the
unfolding tree (always choosing leftmost atoms) until its `K`-th
frontier is reached.  (Elvira Albert)

## [1.0.295] - 2004-02-04

../printer.pl

Solved bug which sometimes included the regtype package twice.
(German Puebla)

## [1.0.294] - 2004-02-04

../plai/intermod.pl

First version of auto_transform/3 to perform intermodular abstract
specialization. It only works with programs without cyclic
intermodular dependencies.  (Jesus Correas Fernandez)

## [1.0.293] - 2004-02-04

../spec/abs_exec.pl

Implemented extended abstract executability table lookup to use the
specialized versions of predicates imported from other modules.
(Jesus Correas Fernandez)

## [1.0.292] - 2004-02-04

../spec/spec.pl

Implemented extended abstract executability table lookup to use the
specialized versions of predicates imported from other modules.
(Jesus Correas Fernandez)

## [1.0.291] - 2004-02-04

../p_unit/p_abs.pl

Added get_spec_info_imported/0 to insert into the extended abstract
executability table the list of specialized version names of the
predicates imported by the current module.  (Jesus Correas Fernandez)

## [1.0.290] - 2004-02-04

../p_unit/p_abs.pl

Added update_spec_info/2 to update the registry with specialized
version names of the predicates.  (Jesus Correas Fernandez)

## [1.0.289] - 2004-02-04

../spec/codegen.pl

This module has now two entry points rather than one depending of
whether argument filtering should be performed or not, instead of one
entry point and a preprocessor flag.  (German Puebla)

## [1.0.288] - 2004-02-03

../spec/spec.pl

Added data `publish_pred_name/2` which indicates which are the
exported predicates for which several implementations are available.
(German Puebla)

## [1.0.287] - 2004-02-03

../infer/infer_dom.pl

Added asub_to_out/6.  (Francisco Bueno Carrillo)

## [1.0.286] - 2004-02-03

../infer/prepare_ai_output.pl

Solved bugs 2 and 6.  (Francisco Bueno Carrillo)

## [1.0.285] - 2004-02-03

../plai/domains.pl

Added asub_to_out/5, modified consequently eterms, termsd, svterms,
shfret, nfplai, detplai.  (Francisco Bueno Carrillo)

## [1.0.284] - 2004-02-03

../spec/spec.pl

Now new versions of exported predicates are also exported. Otherwise
it is not possible to call them from outside the module.  (German
Puebla)

## [1.0.283] - 2004-02-03

../spec/codegen.pl

Assertions for predicates in the original clause (i.e., `prop` and
`regtype`) are now replicated for the newly created predicates.
(German Puebla)

## [1.0.282] - 2004-02-02

../p_unit/p_asr.pl

Now .ast files are read.  (Francisco Bueno Carrillo)

## [1.0.281] - 2004-02-02

../infer/vartypes.pl

Call native_prop to convert properties to internal representation when
comparing with the top type. (Francisco Bueno Carrillo)

## [1.0.280] - 2004-02-02

../p_unit/itf_db.pl

Double module expansion for meta-predicates to solve the problem with
addmodule specs.  (Francisco Bueno Carrillo)

## [1.0.279] - 2004-02-02

../infernf/nftable.pl

Use type_of_goal(builtin(BuiltinGoal),Goal) when creating the program
table.  (Pedro Lopez Garcia)

## [1.0.278] - 2004-02-02

../infer/prepare_ai_output.pl

Added non_collapsable for proper type simplification.  (Francisco
Bueno Carrillo)

## [1.0.277] - 2004-02-01

../spec/codegen.pl

Analysis info allows (again) to perform transform(simp) after codegen.
(German Puebla)

## [1.0.276] - 2004-02-01

../spec/global_control.pl

Fixed bug which appeared when the specialized definition was the empty
set of clauses.  (German Puebla)

## [1.0.275] - 2004-02-01

../plai/domains/pd.pl

Somewhat improved handling of builtins.  (German Puebla)

## [1.0.274] - 2004-01-31

../plai/fixpo_plai.pl

First version on reusing identical projections for calls that are not
variants, implemented only the case of completes.  (Claudio Vaucheret)

## [1.0.273] - 2004-01-31

../plai/domains.pl

Added `identical_proj_1/7` It is different from
`identical_proj/5` because it can be true although the calls are
not variant.  (Claudio Vaucheret)

## [1.0.272] - 2004-01-31

../plai/domains.pl

init_abstract_domain sets which domains take into account the flag
variants (Claudio Vaucheret)

## [1.0.271] - 2004-01-31

../preprocess_flags.pl

added two new flags, `widencall` and `variants`. The first one
chooses which policy is used to get two consecutive aproximations to
be widened at call time. The second decides whether two abstractions
can be identical although the goals are not variants (Claudio
Vaucheret)

## [1.0.270] - 2004-01-30

../p_unit/assrt_norm.pl

Assertion heads now accept terms. Declarative properties must go with
? mode.  (Francisco Bueno Carrillo)

## [1.0.268] - 2004-01-30

../plai/intermod.pl

Added manual_analyze/3 to analyze a module and force the mode of its
registry file. Default values of registry file mode are read_write
(for non-library modules) and read_only (for library modules). This
predicate allows to change the default behaviour.  (Jesus Correas
Fernandez)

## [1.0.267] - 2004-01-30

../p_unit/p_abs.pl

Added change_open_mode/2 to change the mode flag of a registry. This
flag is stored in the registry file. .reg file version has been set to
2.1.  (Jesus Correas Fernandez)

## [1.0.266] - 2004-01-30

../doc/Makefile.pl

Solved a interference between the installed ciao library and the
development ciao library.  Added the line 'CIAOLIB=',
~ciaosrc... before to call lpdoc. (Edison Mera)

## [1.0.265] - 2004-01-30

../dist/Makefile.pl

Solved an interference between the installed ciao library and the
development ciao library.  Added the line 'CIAOLIB=',
~ciaosrc... before to call lpdoc (Edison Mera)

## [1.0.264] - 2004-01-30

../infernf/subproblems.pl

Updated to be compatible with the latest changes in clpq/clpr (Edison
Mera)

## [1.0.263] - 2004-01-30

../spec/arg_filtering.pl

Added predicate `create_filters_exported/2` for maintaining
exported interface even when arg_filtering is not performed.  (German
Puebla)

## [1.0.262] - 2004-01-29

../ctchecks/assrt_ctchecks_common.pl

Calls to native_props within findall in get_calls_assertion were
(wrong) native_prop_.  (Francisco Bueno Carrillo)

## [1.0.261] - 2004-01-29

../preprocess_flags.pl

'intermod' preprocess has been removed as it is no longer needed.
(Jesus Correas Fernandez)

## [1.0.260] - 2004-01-29

../spec/abs_exec.pl

regtypes are abstractly executable to fail when its argument is free
(Claudio Vaucheret)

## [1.0.259] - 2004-01-29

../plai/domains/share.pl

Add some meta-calls as builtins, i.e., findall/3 (also in
sondergaard.pl).  (Francisco Bueno Carrillo)

## [1.0.258] - 2004-01-29

../p_unit/p_abs.pl

Added an extra argument to changed_modules/5 to allow intermodular
analysis with automatic scheduling work without saving .reg files
every time a module is analyzed.  (Jesus Correas Fernandez)

## [1.0.257] - 2004-01-29

../plai/intermod.pl

First version of auto_analyze/2
implemented. auto_analyze(Analysis,TopLevel) analyzes all the modules
that belong to the program unit to which TopLevel is the top-level
module, and calculates the intermodular fixpoint if necessary. The
only scheduling policy implemented so far is depth_first.  (Jesus
Correas Fernandez)

## [1.0.256] - 2004-01-29

../p_unit/p_asr.pl

Assert location/3 so that cioapp gives proper messages on module
expansion.  (Francisco Bueno Carrillo)

## [1.0.255] - 2004-01-29

../plai/fixpo_di.pl

changed di_parents flag by widen flag (Claudio Vaucheret)

## [1.0.254] - 2004-01-29

../preprocess_flags.pl

Elimiated di_parents flag, we are using widen flag instead (Claudio
Vaucheret)

## [1.0.253] - 2004-01-29

../spec/global_control.pl

Improved global control for homeomorphic embedding since sometimes pe
did not terminate when partial concretization is activated.  (German
Puebla)

## [1.0.252] - 2004-01-29

../p_unit/itf_db.pl

All predicates defined in a user file are considered exports.
(Francisco Bueno Carrillo)

## [1.0.251] - 2004-01-28

../plai/fixpo_di.pl

Fixed complicated bug associated to di_parents.  (German Puebla)

## [1.0.250] - 2004-01-28

../plai/domains/typeslib/regtype_basic_lattice.pl

Fixed bug in type_intersection/3: introduced calls to
typeslib:type_intersection/3 in arg_typ_inter/4 and
compound_ground_inter/4. (Pedro Lopez Garcia)

## [1.0.249] - 2004-01-27

../preprocess_flags.pl

di_parents is on by default (Claudio Vaucheret)

## [1.0.248] - 2004-01-27

../plai/fixpo_di.pl

When di_parents flag is on, memo_tables are asserted before to analyze
(Claudio Vaucheret)

## [1.0.247] - 2004-01-27

../spec/arg_filtering.pl

Standalone argument filtering finally working.  (German Puebla)

## [1.0.246] - 2004-01-26

../spec/spec.pl

Added exported predicate `get_version_name/4` which is required
for specialization of modular programs.  (German Puebla)

## [1.0.245] - 2004-01-26

../p_unit/p_abs.pl

Added update_spec_info/2 to store information about exported
predicates' specialized names.  (Jesus Correas Fernandez)

## [1.0.244] - 2004-01-26

../p_unit/p_abs.pl

Added specialized version name generation for current module
predicates.  (Jesus Correas Fernandez)

## [1.0.243] - 2004-01-26

../spec/arg_filtering.pl

Contains predicates for performing argument filtering either during
code generation or as a standalone transformation.  (German Puebla)

## [1.0.242] - 2004-01-26

../spec/codegen.pl

A very optimized implementation of code generation after partial
evaluation is now available.  (German Puebla)

## [1.0.241] - 2004-01-26

../spec/global_control.pl

Global control in a separate module.  (German Puebla)

## [1.0.240] - 2004-01-26

../plai/domains.pl

Improved handling of `PD` domain.  (German Puebla)

## [1.0.238] - 2004-01-26

../preprocess_flags.pl

Added `pd` to the list of domains and improved default values of
several flags.  (German Puebla)

## [1.0.237] - 2004-01-26

../driver.pl

Added `arg_filtering` as a standalone tranformation.  (German
Puebla)

## [1.0.236] - 2004-01-26

../plai/plai.pl

mod_plai/5 predicate added to handle modular analysis.  (Jesus Correas
Fernandez)

## [1.0.235] - 2004-01-26

../plai/intermod.pl

Main module for handling modular analysis. File creation.  (Jesus
Correas Fernandez)

## [1.0.234] - 2004-01-26

../plai/success.pl

Module for handling success policies in modular analysis. File
creation.  (Jesus Correas Fernandez)

## [1.0.233] - 2004-01-26

../plai/entry_policy.pl

Handling of entry policies in modular analysis. File creation.  (Jesus
Correas Fernandez)

## [1.0.232] - 2004-01-26

../p_unit/p_abs.pl

succ_pattern/4 and call_pattern/3 moved to plai/success.pl (reexported
here for compatibility), some internal predicates made public to allow
access to internal structures.  (Jesus Correas Fernandez)

## [1.0.231] - 2004-01-24

../plai/fixpo_di.pl

Added the flag `di_parents` which controls whether the parent
should be included as soon as a complete is created. Off is more
efficient, but on is required for widen_calls to function properly
with the eterms domain.  (German Puebla)

## [1.0.230] - 2004-01-22

../preprocess_flags.pl

The flag `unfold` is now called `local_control`. Additionally,
its value `onestep` is now more correctly called `inst` for
_instantiation_.  (German Puebla)

## [1.0.228] - 2004-01-21

../preprocess_flags.pl

Changed names of flags. Chapuza total!  (Francisco Bueno Carrillo)

## [1.0.227] - 2004-01-19

../preprocess_flags.pl

Added 'force' value to 'entry_policy' preprocessing flag to reanalyze
all the entries in the intermodular registry despite their state.
(Jesus Correas Fernandez)

## [1.0.226] - 2004-01-19

../preprocess_flags.pl

Added global_scheduling preprocessing flag for modular analysis.
(Jesus Correas Fernandez)

## [1.0.225] - 2004-01-19

../preprocess_flags.pl

Changed values of flag normalize to the standard on/ off.  (Claudio
Vaucheret)

## [1.0.224] - 2004-01-19

../plai/domains.pl

The second argument of init_abstract_domain return the value of
normalize flag.  (Claudio Vaucheret)

## [1.0.223] - 2004-01-19

../preprocess_flags.pl

Added flag normalize. Value yes means the program analyzed is the
normalized (Claudio Vaucheret)

## [1.0.222] - 2004-01-18

../spec/spec.pl

Changed since now codegen is a separate module.  (German Puebla)

## [1.0.221] - 2004-01-18

../spec/codegen.pl

Adapted to the changes in module unfold which now uses a two level
table for specialized definitions.  (German Puebla)

## [1.0.220] - 2004-01-18

../spec/abs_exec.pl

Improved handling of types.  (German Puebla)

## [1.0.219] - 2004-01-18

../spec/unfold.pl

The information about specialized definitions is now split into two
tables. This is required for handling partial concretization
correctly.  (German Puebla)

## [1.0.218] - 2004-01-18

../spec/codegen.pl

This is now a separate module, independent of spec.pl.  (German
Puebla)

## [1.0.217] - 2004-01-18

../spec/spec_support.pl

Predicate `prepare_ai_info/3` now lives here instead of in
spec.pl.  (German Puebla)

## [1.0.216] - 2004-01-18

../spec/s_simpspec.pl

Predicates `list_format/2` and `newformat/2` now live here
instead of in module spec.  (German Puebla)

## [1.0.215] - 2004-01-18

../plai/domains.pl

Added the `PD` abstract domain which return Top for all operations.
(Claudio Vaucheret)

## [1.0.214] - 2004-01-13

../Makefile.pl

Made makefile comments generic (so that they are more understandable
when issued during installation).  (Manuel Hermenegildo)

## [1.0.213] - 2004-01-13

../Makefile.pl

Added `Makefile.pl` to lpdoc version control.  (Manuel
Hermenegildo)

## [1.0.210] - 2004-01-13

../spec/spec.pl

Adapted to work properly with ciao-1.11 (German Puebla)

## [1.0.209] - 2004-01-13

../spec/codegen.pl

Analysis information is recovered after transform(codegen). This
allows abstractly executing the partially evaluated program directly!
(German Puebla)

## [1.0.208] - 2004-01-13

../spec/abs_exec.pl

Most of predicates described here are no longer builtins. A temporary
solution has been found.  (German Puebla)

## [1.0.207] - 2004-01-12

../preprocess_flags.pl

Classified analyses in modes/types/etc.  (Francisco Bueno Carrillo)

## [1.0.206] - 2004-01-08

../spec/unfold.pl

Improved behaviour of deterministic unfolding rule.  (German Puebla)

## [1.0.205] - 2004-01-08

../old_interface.pl

Synchronized menu with options in the manual.  (Francisco Bueno
Carrillo)

## [1.0.204] - 2004-01-08

../plai/domains/share.pl

Solved bug 1.  (Francisco Bueno Carrillo)

## [1.0.203] - 2004-01-08

../plai/domains/share.pl

Changed metachoice/metacut builtin keys.  (Francisco Bueno Carrillo)

## [1.0.202] - 2004-01-02

../spec/unfold.pl

Usage of partial concretatization before unfolding already working.
(German Puebla)

## [1.0.201] - 2004-01-02

../spec/codegen.pl

Towards obtaining argument filtering. Added data `rename/3`.
(German Puebla)

## [1.0.200] - 2004-01-02

../preprocess_flags.pl

Added flag `arg_filt` which controls whether argument filtering
should be used when generating code after partial evaluation.  (German
Puebla)

## [1.0.199] - 2003-12-31

../p_unit/native.pl

Added hardwired builtin tables: fail, metacut, metachoice, and the
native properties.  (Francisco Bueno Carrillo)

## [1.0.198] - 2003-12-31

../spec/unfold.pl

Atoms to be unfolded can now be partially concretized before actual
unfolding.  (German Puebla)

## [1.0.197] - 2003-12-31

../spec/codegen.pl

Specialized versions which correspond to external predicates now keep
the original name of the predicate to preserve the module interface.
(German Puebla)

## [1.0.196] - 2003-12-31

../plai/fixpo_ops.pl

Improved handling of backward pointers originated from external calls
in `remove_useless_info/1`.  (German Puebla)

## [1.0.195] - 2003-12-31

../plai/domains.pl

Added exported predicate `part_conc/5`.  (German Puebla)

## [1.0.194] - 2003-12-31

../preprocess_flags.pl

Added flag `part_conc` which determines whether partial
concretization should be applied or not before unfolding. Note that
this is a new possibility simply not available in traditional partial
evaluation.  (German Puebla)

## [1.0.193] - 2003-12-30

../spec/unfold.pl

Implemented homeomorphic embedding and used for improved (always
terminating) global control.  (Elvira Albert)

## [1.0.192] - 2003-12-30

../plai/fixpo_ops.pl

Call identical_proj to compare Prime in completes.  (Francisco Bueno
Carrillo)

## [1.0.191] - 2003-12-30

../infer/prepare_ai_output.pl

Call p_unit for true(Goal).  (Francisco Bueno Carrillo)

## [1.0.189] - 2003-12-30

../printer.pl

Added all packages on output:
[assertions,nativeprops,regtypes,rtchecks] (Francisco Bueno Carrillo)

## [1.0.188] - 2003-12-29

../printer.pl

Solved bug 12. Bug 11 seems solved, too.  (Francisco Bueno Carrillo)

## [1.0.187] - 2003-12-29

../p_unit/unexpand.pl

Added T \== ?  in transform_terms: not correct, though complete
(Francisco Bueno Carrillo)

## [1.0.186] - 2003-12-30

../spec/unfold.pl

Added the possibility to select the global control and implemented
`id` and `inst`. Other strategies soon to come.  (German Puebla)

## [1.0.185] - 2003-12-30

../spec/spec.pl

`prepare_ai_info/2` now computes the identifiers of completes
which correspond to exported versions.  (German Puebla)

## [1.0.184] - 2003-12-30

../spec/codegen.pl

More efficient code generation. Also, repeated specialized definitions
introduced by global control are no longer generated.  (German Puebla)

## [1.0.183] - 2003-12-30

../plai/fixpo_ops.pl

Added exported predicate `remove_useless_info_get_init_calls/2`.
(German Puebla)

## [1.0.182] - 2003-12-30

../plai/fixpo_di.pl

The integration with partial evaluation is now even simpler.  (German
Puebla)

## [1.0.181] - 2003-12-30

../preprocess_flags.pl

Added flag `global_control` which allows selecting among different
strategies for global control during partial evaluation.  (German
Puebla)

## [1.0.180] - 2003-12-29

../p_unit/clidlist.pl

Added clause_number/2.  (Francisco Bueno Carrillo)

## [1.0.179] - 2003-12-29

../spec/spec.pl

Added exported predicate `codegen/5` whose source is in included
file `codegen.pl`.  (German Puebla)

## [1.0.178] - 2003-12-29

../plai/fixpo_dx_check_common.pl

`cleanup_fixpoint` now executes `cleanup_unfolds` as well
(German Puebla)

## [1.0.177] - 2003-12-29

../plai/fixpo_di.pl

This fixpoint algorithm now uses unfolding prior to analyzing the
clauses which correspond to an atom. This allows both performing
partial evaluation and improving analysis results by propagating
concrete substitutions.  (German Puebla)

## [1.0.176] - 2003-12-29

../p_unit/clidlist.pl

Added exported predicate `rewrite_source_all_clauses/2` which is
handy when rewrite_source_clause/4 has to be applied to a list of
clauses.  (German Puebla)

## [1.0.175] - 2003-12-29

../driver.pl

Added `transform(codegen)` which generates the code produced by
partially evaluating the program during analysis.  (German Puebla)

## [1.0.174] - 2003-12-29

../preprocess_flags.pl

Added the flag `unfold` which controls whether unfolding should be
performed during analysis.  (German Puebla)

## [1.0.173] - 2003-12-29

../preprocess_flags.pl

Added entry_policy preprocessing flag.  (Jesus Correas Fernandez)

## [1.0.172] - 2003-12-29

../p_unit/p_unit.pl

Properties native and regtype can only be asserted in prop assertions.
(Francisco Bueno Carrillo)

## [1.0.171] - 2003-12-26

../plai/domains/share.pl

Remove meta-calls as builtins (also in sondergaard.pl).  (Francisco
Bueno Carrillo)

## [1.0.170] - 2003-12-26

../plai/fixpo_ops.pl

Loop for extra complete and memo_table when comparing with prev.
(Francisco Bueno Carrillo)

## [1.0.167] - 2003-12-26

../p_unit/p_unit.pl

Complete clause dicts, which do not have names for the clause free
variables.  (Francisco Bueno Carrillo)

## [1.0.166] - 2003-12-24

../p_unit/assrt_norm.pl

Solved bug 3.  (Francisco Bueno Carrillo)

## [1.0.164] - 2003-12-24

../plai/domains/share.pl

Added int/1 and num/1 as builtins (also in sondergaard.pl).
(Francisco Bueno Carrillo)

## [1.0.163] - 2003-12-23

../p_unit/assrt_norm.pl

Solved bug 4.  (Francisco Bueno Carrillo)

## [1.0.162] - 2003-12-23

../p_unit/p_unit.pl

Do not treat prop assertions as pred assertions.  (Francisco Bueno
Carrillo)

## [1.0.159] - 2003-12-23

../printer.pl

Solved bug 7. comp and prop assertions are now not lost in the
output. Also, props have no status. (Francisco Bueno Carrillo)

## [1.0.158] - 2003-12-18

../plai/fixpo_ops.pl

Changed treatment of call to map_glb.  (Francisco Bueno Carrillo)

## [1.0.157] - 2003-12-18

../plai/fixpo_plai.pl

Changed accumulation of Succ in meta_call from widen to append.
(Francisco Bueno Carrillo)

## [1.0.156] - 2003-12-18

../plai/trust.pl

Any dynamic (i.e., dynamic,multifile,imported) predicate of arity 0 is
trusted as to have Prime=Proj (Francisco Bueno Carrillo)

## [1.0.155] - 2003-12-18

../preprocess_flags.pl

Added 'botfirst', 'botall', 'botbest' and 'bot' values to
success_policy flag.  (Jesus Correas Fernandez)

## [1.0.154] - 2003-12-18

../preprocess_flags.pl

'trust' flag name changed to 'success_policy' (it is not used to
handle trust assertions, only for success info of imported
predicates).  (Jesus Correas Fernandez)

## [1.0.153] - 2003-12-18

../plai/trust.pl

Imported predicates handling (success policy) moved to plai/success.pl
and removed from this module.  (Jesus Correas Fernandez)

## [1.0.152] - 2003-12-18

../plai/trust.pl

Predicate name apply_trusted_/8 changed to apply_glb_inferred/8.
(Jesus Correas Fernandez)

## [1.0.151] - 2003-12-18

../plai/trust.pl

there_are_trust/2 data predicate has been removed because it is
unneeded.  (Jesus Correas Fernandez)

## [1.0.150] - 2003-12-18

../plai/plai.pl

di_mod added as a new fixpoint algorithm.  (Jesus Correas Fernandez)

## [1.0.149] - 2003-12-18

../p_unit/p_abs.pl

.imdg files are no longer generated. Intermodular dependency graph
information is now included in .reg files.  (Jesus Correas Fernandez)

## [1.0.148] - 2003-12-18

../p_unit/p_abs.pl

Low-level registry file handling predicates have been added:
read_registry_file/3, reread_registry_file/3, write_registry_file/3,
and the data predicate registry/2. Although currently they only handle
registry/7 terms in registry files, they have been prepared to easily
extend it to manage other registry information (type descriptions,
specialization and partial evaluation info, etc).  (Jesus Correas
Fernandez)

## [1.0.147] - 2003-12-18

../p_unit/p_abs.pl

cleanup_p_abs/0 has been modified to keep the registry information of
previously loaded modules, instead of cleaning up all the information
every time a module is loaded into ciaopp. cleanup_p_abs_all/0 has
been added to clean all the internal registry information.  (Jesus
Correas Fernandez)

## [1.0.146] - 2003-12-18

../p_unit/p_abs.pl

generate_abs_files/1-3 replaced by gen_registry_info/3 and
save_registry_info/1-2. These predicates allow generating the analysis
information in memory instead of saving them to disk for every module
analyzed.  (Jesus Correas Fernandez)

## [1.0.145] - 2003-12-11

../plai/domains/typeslib/regtype_basic_lattice.pl

Renamed included_in_ground_type/2 to type_included_in_ground/2 (Pedro
Lopez Garcia)

## [1.0.144] - 2003-12-11

../plai/domains/typeslib/typeslib.pl

Simplification of types perform some tabling (more efficient) (Pedro
Lopez Garcia)

## [1.0.143] - 2003-12-11

../plai/domains/typeslib/typeslib.pl

Added a type simplification which collapse inferred types to those
defined in the preprocessing unit only. Controlled by the pp_flag
type_output (which is independent of the pp_flag type_precision).
Activate with set_pp_flag(type_output,user). Default is
set_pp_flag(type_output,all) (Pedro Lopez Garcia)

## [1.0.142] - 2003-12-11

../plai/domains/typeslib/typeslib.pl

Modified get_NO_par_type_definition/2: Now, a type symbol with no
defining type rule is considered empty (bottom).  (Pedro Lopez Garcia)

## [1.0.141] - 2003-12-11

../plai/domains/typeslib/typeslib.pl

Modified retract_rule(TypeSymbol): If there is no type rule for
TypeSymbol, then succeeds as before, but do not raise any error
message.  (Pedro Lopez Garcia)

## [1.0.140] - 2003-12-09

../infer/prepare_ai_output.pl

Added tmp_point_info/4 and tmp_complete_info/5 so that type
simplification is called only once.  (Francisco Bueno Carrillo)

## [1.0.139] - 2003-12-03

../plai/domains/typeslib/regtype_basic_lattice.pl

Created this module. Got rid of anyfd and rat. Changed some operations
(lookup PBC).  (Francisco Bueno Carrillo)

## [1.0.138] - 2003-12-03

../plai/domains/typeslib/typeslib.pl

Grouped code for the different operations. Parameter type basics seem
working (some changes here).  (Francisco Bueno Carrillo)

## [1.0.137] - 2003-11-27

../plai/domains/typeslib/typeslib.pl

Added preliminary support towards handling parameter types.
(Francisco Bueno Carrillo)

## [1.0.135] - 2003-10-20

../preprocess_flags.pl

Added the `trust` flag to select how trust assertions are handled
when there are several substitutions applicable.  (Jesus Correas
Fernandez)

## [1.0.134] - 2003-10-15

../p_unit/unexpand.pl

Changed call to 'hiord_rt:call'.  (Francisco Bueno Carrillo)

## [1.0.133] - 2003-10-15

../p_unit/p_unit.pl

Changed management of regtype/1 in native_prop/2.  (Francisco Bueno
Carrillo)

## [1.0.132] - 2003-10-15

../p_unit/native.pl

Adapted to Ciao 1.11 (module qualifications for native and regtype
builtin properties).  (Francisco Bueno Carrillo)

## [1.0.131] - 2003-10-14

../printer.pl

No engine(builtin_modules) in 1.11!!!  (Francisco Bueno Carrillo)

## [1.0.130] - 2003-10-13

../ctchecks/assrt_ctchecks_pp.pl

Corrected handling of properties in assertions, since first level
conjunction is represented as a list, even if it contains just one
element. Other corrections as well.  (German Puebla)

## [1.0.129] - 2003-10-13

../ctchecks/assrt_ctchecks_common.pl

Added exported predicate `synt_compose_list/3` since now
assertions represent first level conjunctions as lists.  (German
Puebla)

## [1.0.128] - 2003-10-13

../spec/abs_exec.pl

Improved handling of `not_ground/1`.  (German Puebla)

## [1.0.127] - 2003-10-13

../spec/spec.pl

Messages are now issued using inform_user, whose output can be
controlled using the `quiet` prolog flag.  (German Puebla)

## [1.0.126] - 2003-10-13

../plai/plai.pl

In addition to the abstract domain, messages now also inform about the
fixpoint algorithm used.  (German Puebla)

## [1.0.125] - 2003-10-13

../test/Spec/test_spec.pl

Compares the results of program specialization. Though this is
something rather tricky, it is now feasible because: (a) the internal
representation of the specialized program is compared (b) dump files
are stored so that it is possible to reuse fixp ids which in turn
allows that the specialized versions have exactly the same name in
different runs of the analyzer/specializer.  (German Puebla)

## [1.0.122] - 2003-10-09

../plai/fixpo_check_di4.pl

This version tries to optimize checking by using the program point
info as forward pointers. This avoids non-determinism when selecting
completes.  (German Puebla)

## [1.0.121] - 2003-10-09

../plai/domains/share.pl

Created and exported shfr_obtain/3.  (Pedro Lopez Garcia)

## [1.0.120] - 2003-10-09

../plai/domains/nfplai.pl

Fixed bug in compute_modetypes/4: wrong call for obtaining freeness
information which caused that none variable was free. This caused that
the covering check (nf_compute_covering/3) was wrongly called. (Pedro
Lopez Garcia)

## [1.0.119] - 2003-10-07

../p_unit/p_dump.pl

Now the `dump_level` flag controls what the contents of the dump
file should be.  (German Puebla)

## [1.0.118] - 2003-10-07

../preprocess_flags.pl

Added the `dump_level` flag.  (German Puebla)

## [1.0.117] - 2003-10-07

../plai/fixpo_ops.pl

Now, for flexibility, `remove_useless_info/1` always has to be
called from outside this module.  (German Puebla)

## [1.0.116] - 2003-10-07

../plai/fixpo_check_di3.pl

This checker differs from check_di in that neither program point nor
dependency (parents) information is stored.  (German Puebla)

## [1.0.115] - 2003-10-07

../plai/fixpo_check_di2.pl

This checker differs from check_di in that program point information
is not stored.  (German Puebla)

## [1.0.114] - 2003-10-07

../plai/fixpo_dx_common.pl

Most of code originally in this file is now in
fixpo_dx_check_common.pl (German Puebla)

## [1.0.113] - 2003-10-07

../plai/fixpo_dx_check_common.pl

Code which is common to the dx fixpoints and checkers.  (German
Puebla)

## [1.0.112] - 2003-10-07

../plai/fixpo_ops.pl

Two new predicates exported: `compare_completes_with_prev/1` and
`compare_memo_tables_with_prev/1`, which can be used to compare
predicate-level or program-point level information only.  (German
Puebla)

## [1.0.111] - 2003-10-06

../plai/fixpo_ops.pl

Added exported predicate `store_previous_analysis_completes/1`
which does not store program point info.  (German Puebla)

## [1.0.110] - 2003-10-06

../plai/plai.pl

Replaced usage of library(messages) with library(io_aux) and optimized
preprocessing for check_di.  (German Puebla)

## [1.0.109] - 2003-10-06

../driver.pl

In analyze(Analysis,Info), added nfg analysis time to Info:
nfinfo(TimeNf,Num_Pred,Num_NF_Pred,NCov). (Pedro Lopez Garcia)

## [1.0.108] - 2003-10-03

../preprocess_flags.pl

Added exported predicates `push_pp_flag/2` and
`pop_pp_flag/1`.  (German Puebla)

## [1.0.107] - 2003-10-03

../test/Check_Fixp/test_check_fixp.pl

Initial version of tester for fixpoint checker.  (German Puebla)

## [1.0.106] - 2003-10-03

../preprocess_flags.pl

Added the possibility of selecting checkers (in addition to fixpoints)
using the fixpoint flag.  (German Puebla)

## [1.0.105] - 2003-10-03

../plai/fixpo_ops.pl

Added exported predicate `fixpoint_id_reuse_prev_success/6` which
in addition to reusing the identifier for the complete also uses the
answer as initial guess.  (German Puebla)

## [1.0.104] - 2003-10-03

../plai/fixpo_check_di.pl

Initial version of checking whether an answer table is a fixpoint of
analysis. Can be used for proof-carrying-code. Only fixpoint
iterations eliminated. Dependencies and program point info are
computed anyway.  (German Puebla)

## [1.0.102] - 2003-10-03

../test/test_all.pl

Initial version (German Puebla)

## [1.0.101] - 2003-10-03

../test/Plai/test_plai.pl

First version (German Puebla)

## [1.0.100] - 2003-10-03

../test/Plai/generate_all_dumps.pl

Initial version (German Puebla)

## [1.0.99] - 2003-10-02

../plai/notrace_tr.pl

Solved problem in the notrace package which avoided its usage: calls
to cleanup were not eliminated.  (German Puebla)

## [1.0.98] - 2003-09-29

../infer/vartypes.pl

Fixed bug: gather_vartypes/2 infers gnd type instead of ground.
(Pedro Lopez Garcia)

## [1.0.97] - 2003-09-25

../plai/transform.pl

Preds declared native are considered builtins even if defined locally.
(Francisco Bueno Carrillo)

## [1.0.96] - 2003-09-23

../infernf/infernf.pl

Adapted non-failure analysis (nfg) to new meta-call representation.
(Pedro Lopez Garcia)

## [1.0.95] - 2003-09-23

../infercost/infercost.pl

Ported Manuel's error messages modifications from 0.8. Now, CASLOG
messages are in standar ciaopp format.  (Pedro Lopez Garcia)

## [1.0.94] - 2003-09-20

../plai/plai_db.pl

Added memo_call/5.  (Francisco Bueno Carrillo)

## [1.0.93] - 2003-09-20

../p_unit/clidlist.pl

Key of a meta-call is now ahead of the keys of its meta-terms in
rewrite_source_body (Francisco Bueno Carrillo)

## [1.0.92] - 2003-09-19

../plai/fixpo_plai.pl

Ported support for analyzing meta-calls via concrete/4 from 0.8.
(Francisco Bueno Carrillo)

## [1.0.91] - 2003-09-18

../p_unit/p_unit.pl

Added new_internal_predicate/3 and internal_predicate_names/1.
(Francisco Bueno Carrillo)

## [1.0.90] - 2003-09-18

../plai/domains/typeslib/typeslib.pl

selected_rule only selects internally_defined_type_symbol, and added
this one.  (Francisco Bueno Carrillo)

## [1.0.89] - 2003-09-18

../printer.pl

Does not print required types if they are already predicates in the
source.  (Francisco Bueno Carrillo)

## [1.0.88] - 2003-09-17

../infernf/subproblems.pl

Added code for checking covering by calling omega test
(integer_covers/2) (Pedro Lopez Garcia)

## [1.0.87] - 2003-09-16

../plai/domains/typeslib/basic_type_operations.pl

Fixed bug in fdtypes_included_in_ground_type/1. Now, checking
inclusion of types in gnd type works (dz_type_included/2), and also
is_ground_type/1.  (Pedro Lopez Garcia)

## [1.0.86] - 2003-09-16

../plai/domains/share.pl

Changed input_interface for understanding ground types as ground.
(Francisco Bueno Carrillo)

## [1.0.85] - 2003-09-15

../printer.pl

Used unexpand:module_spec/2, local version was wrong.  (Francisco
Bueno Carrillo)

## [1.0.84] - 2003-09-15

../p_unit/itf_db.pl

Added assert_itf_chapuza/2.  (Francisco Bueno Carrillo)

## [1.0.83] - 2003-09-15

../p_unit/unexpand.pl

Added unexpand_terms.  (Francisco Bueno Carrillo)

## [1.0.82] - 2003-09-15

../p_unit/unexpand.pl

Added '$'/3 meta-term type and primitive mea-preds to the unexpansion.
(Francisco Bueno Carrillo)

## [1.0.81] - 2003-09-14

../plai/transform.pl

Consider builtins and metacalls only imported predicates.  (Francisco
Bueno Carrillo)

## [1.0.80] - 2003-09-14

../plai/fixpo_ops.pl

Fixed treatment of meta-calls.  (Francisco Bueno Carrillo)

## [1.0.79] - 2003-09-14

../plai/fixpo_plai.pl

Added call to body_succ0 in unknown meta-calls for the trusts.
   (Francisco Bueno Carrillo)

## [1.0.78] - 2003-09-14

../plai/fixpo_dx_common.pl

Added call to body_succ0 in unknown meta-calls for the trusts.
(Francisco Bueno Carrillo)

## [1.0.77] - 2003-09-13

../plai/fixpo_ops.pl

Added body_succ_meta/8.  (Francisco Bueno Carrillo)

## [1.0.76] - 2003-09-13

../plai/domains/sondergaard.pl

Added glb and son_to_share. (Francisco Bueno Carrillo)

## [1.0.75] - 2003-09-12

../printer.pl

Don't write module header for user files.  (Francisco Bueno Carrillo)

## [1.0.74] - 2003-09-12

../printer.pl

Don't write modedef assertions.  (Francisco Bueno Carrillo)

## [1.0.73] - 2003-09-12

../p_unit/p_unit.pl

Meta-pred decls. for imported now asserted and correctly expanded.
(Francisco Bueno Carrillo)

## [1.0.72] - 2003-09-12

../p_unit/p_unit.pl

Used visible in new_predicate.  (Francisco Bueno Carrillo)

## [1.0.71] - 2003-09-12

../p_unit/p_asr.pl

Added multifile to visible.  (Francisco Bueno Carrillo)

## [1.0.70] - 2003-09-12

../p_unit/p_asr.pl

call/n valid property in assertions.  (Francisco Bueno Carrillo)

## [1.0.69] - 2003-09-11

../infer/inferseff.pl

Assertions for builtins (and imports) now handled. (Francisco Bueno
Carrillo)

## [1.0.68] - 2003-09-11

../p_unit/p_unit.pl

Adapted native_props/2 to check visibility and native_prop/2 to not
check it.  (Francisco Bueno Carrillo)

## [1.0.67] - 2003-09-11

../p_unit/p_unit.pl

Added language/1.  (Francisco Bueno Carrillo)

## [1.0.66] - 2003-09-11

../plai/domains/def.pl

Added glb.  (Francisco Bueno Carrillo)

## [1.0.65] - 2003-09-11

../plai/domains/lsign.pl

Added constraints as builtins: .=., etc.  (Francisco Bueno Carrillo)

## [1.0.64] - 2003-09-09

../printer.pl

Added non_collapsable/1.  (Francisco Bueno Carrillo)

## [1.0.63] - 2003-09-09

../plai/domains/depthk.pl

Added compute_lub, glb, and less_or_equal.  (Francisco Bueno Carrillo)

## [1.0.62] - 2003-09-09

../infer/prepare_ai_output.pl

When no lub, do not add empty (comp) info to the output (accumulate in
prepare_list).  (Francisco Bueno Carrillo)

## [1.0.61] - 2003-09-08

../p_unit/p_unit.pl

Now itf(visible) seems to be working.  (Francisco Bueno Carrillo)

## [1.0.60] - 2003-09-05

../infer/infer_dom.pl

Moved abstract executability for nf/det/cost here.  (Francisco Bueno
Carrillo)

## [1.0.59] - 2003-09-05

../infer/infer_dom.pl

Adapted complexity_property for proper output of cost info.  (Pedro
Lopez Garcia)

## [1.0.58] - 2003-09-04

../infer/infer_dom.pl

Moved abs_execute_with_info/4 here from ctchecks.  (Francisco Bueno
Carrillo)

## [1.0.57] - 2003-09-04

../infercost/algebraic/algebraic.pl

Added file compare.pl from ciaopp 0.8 (Francisco Bueno Carrillo)

## [1.0.56] - 2003-09-04

../infer/infer_dom.pl

Moved nf_flags handling here.  (Francisco Bueno Carrillo)

## [1.0.55] - 2003-09-04

../plai/plai.pl

Now the pp_flag reuse_fixp_id controls whether the identifier for the
call (not seen before) should be simply the next available one or
instead we should try to give the same identifier if an equivalent
call was generated in a previous analysis for which
`store_previous_analysis/1` was executed.  This works with any of
the existing fixpoint algorithms available. (German Puebla)

## [1.0.54] - 2003-09-04

../spec/spec.pl

Added predicate `order_completes_by_ids`. It solves (in
conjunction with other changes in the fixpoint algorithms and in
fixpo_ops) the difficult problem of comparing the results of
specialization or all version generation when using different fixpoint
algorithms. The reason for this need is that even if different
analyses generate the same completes with the same identifiers (by
using `fixpoint_id_reuse_prev`, the order in which they are
asserted may be different. As a result, in the specialized program (or
the program with all versions) the version names are in general
different, which makes automatic comparison almost impossible.
(German Puebla)

## [1.0.53] - 2003-09-04

../plai/fixpo_ops.pl

Added predicate `remove_useless_info/1` which is useful for
several purposes. One is in order not to create spurious versions
during specialization. Another one is in order to be able to compare
analysis results generated by different fixpoint algorithms. This
implementation is considerably simpler than that in ciaopp-0.8. It is
also independent of the format in which the program is stored.
(German Puebla)

## [1.0.52] - 2003-09-02

../preprocess_flags.pl

Added flag error_log.  (Francisco Bueno Carrillo)

## [1.0.51] - 2003-09-02

../infer/infer.pl

Changed do_compute_lub for $bottom.  (Francisco Bueno Carrillo)

## [1.0.50] - 2003-09-01

../p_unit/p_unit.pl

Do not write comp or succ assertion for a pred assertion if there is
no info.  (Francisco Bueno Carrillo)

## [1.0.49] - 2003-09-01

../preprocess_flags.pl

Added a flag for controlling whether fixpoint identifiers from a
previous analysis should be reused.  (German Puebla)

## [1.0.48] - 2003-09-01

../plai/fixpo_ops.pl

Added stuff for comparing results of two analysis phases by means of
the predicates `store_previous_analysis/1`,
`fixpoint_id_reuse_prev/5`, and
`compare_with_previous_analysis/1`.  (German Puebla)

## [1.0.47] - 2003-09-01

../spec/spec.pl

Printing all versions generated by analysis (vers) now works fine.
(German Puebla)

## [1.0.46] - 2003-08-29

../spec/abs_exec.pl

Activated abstract execution for domain def.  (German Puebla)

## [1.0.45] - 2003-08-29

../plai/tarjan.pl

The list of predicates defined in a module are no longer taken care of
in module tarjan but rather in `predicate_names/1`, in module
p_unit.  (German Puebla)

## [1.0.44] - 2003-08-28

../plai/re_analysis.pl

All code in module re_analysis which is not currently used has been
temporarily removed.  (German Puebla)

## [1.0.43] - 2003-08-28

../plai/re_analysis.pl

`update_ai_info_case` working. This allows recovering analysis
information after specialization without an analysis phase.  (German
Puebla)

## [1.0.42] - 2003-08-28

../infer/prepare_ai_output.pl

Call simplify_step2 for all kind of analyses and assertion of list of
lists for comp properties (Pedro Lopez Garcia)

## [1.0.41] - 2003-08-28

../printer.pl

No change (Pedro Lopez Garcia)

## [1.0.40] - 2003-08-28

../plai/domains/eterms.pl

Added eterms_asub_to_native1/2 (Pedro Lopez Garcia)

## [1.0.39] - 2003-08-28

../p_unit/p_unit.pl

Added predicate_names/1.  (Francisco Bueno Carrillo)

## [1.0.38] - 2003-08-28

../spec/spec.pl

The way in which facts (clauses with true as body) are represented has
changed. Modified spec.pl to adapt to this change. (German Puebla)

## [1.0.37] - 2003-08-27

../tr_syntax/remdisj.pl

Added calls to sort_dict/2.  (Francisco Bueno Carrillo)

## [1.0.36] - 2003-08-27

../p_unit/p_unit.pl

Add a comp (besides the success) assertion for each pred
assertion. (Francisco Bueno Carrillo)

## [1.0.35] - 2003-08-27

../spec/s_simpspec.pl

make_atom/2 now lives in spec(s_simpspec).  (Francisco Bueno Carrillo)

## [1.0.34] - 2003-08-26

../plai/domains.pl

`aidomain/1` now distinguishes between modes and term domains.
(German Puebla)

## [1.0.33] - 2003-08-25

../plai/tarjan.pl

added predicate `fake_recursive_classify` which clasifies
everything as recursive. Useful when no distinction is needed, as when
the di fixpoint is used.  (German Puebla)

## [1.0.32] - 2003-08-25

../plai/plai.pl

The predicate analyze/2 can be used to obtain some info on the
analysis. I have modified plai so that it returns an extra argument
with the preprocessing and analysis times for the module.  (German
Puebla)

## [1.0.31] - 2003-08-25

../plai/plai.pl

Since the di fixpoint algorithm does not require to know whether
predicates are recursive or not, preprocessing of the program now
avoids computing tarjan (SCCs) when di is used.  (German Puebla)

## [1.0.30] - 2003-08-25

../plai/fixpo_ops.pl

The predicate make_atom/2 now lives in plai/fixpo_ops.pl instead of in
pool.pl. All modules using such predicate have been modified.  (German
Puebla)

## [1.0.29] - 2003-08-25

../plai/fixpo_ops.pl

Predicates which are common to all the different fixpoint algorithms
have been moved here to avoid duplications and maintaining multiple
versions of the same code. (German Puebla)

## [1.0.28] - 2003-08-25

../plai/fixpo_dx_common.pl

Code common to di and dd has been factored out and now lives here
(German Puebla)

## [1.0.27] - 2003-08-25

../plai/domains.pl

Added missing entry for domain def in `eliminate_equivalent/3`.
(German Puebla)

## [1.0.26] - 2003-08-21

../p_unit/p_asr.pl

Bug Fixed which prevented loading modules residing in a directory
different from the current directory. This bug also raised in some
cases when a module used another module in a different directory.
(Jesus Correas Fernandez)

## [1.0.25] - 2003-08-21

../plai/fixpo_plai.pl

'lub' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.24] - 2003-08-21

../plai/fixpo_di.pl

'lub' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.23] - 2003-08-21

../plai/fixpo_dd.pl

'lub' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.22] - 2003-08-21

../p_unit/p_dump.pl

pr_info preprocess flag changed to pp_info (Jesus Correas Fernandez)

## [1.0.20] - 2003-08-21

../p_unit/p_abs.pl

'intermod' preprocess flag options changed from yes/no to on/off
(Jesus Correas Fernandez)

## [1.0.19] - 2003-08-21

../plai/fixpo_plai.pl

'widen' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.18] - 2003-08-21

../plai/fixpo_di.pl

'widen' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.17] - 2003-08-21

../plai/fixpo_dd.pl

'widen' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.16] - 2003-08-21

../plai/domains.pl

'widen' preprocess flag options changed from yes/no to on/off (Jesus
Correas Fernandez)

## [1.0.14] - 2003-07-21

../p_unit/p_asr.pl

Expansion of meta-predicates inhibited.  (Francisco Bueno Carrillo)

## [1.0.13] - 2003-07-19

../infer/inferseff.pl

Ported from 0.8.  (Francisco Bueno Carrillo)

## [1.0.12] - 2003-07-18

../plai/domains.pl

Added identical_proj/5 and less_or_equal_proj/5.  (Francisco Bueno
Carrillo)

## [1.0.11] - 2003-07-18

../plai/trust.pl

Added assert_trust/7.  (Francisco Bueno Carrillo)

## [1.0.10] - 2002-12-13

../plai/domains/typeslib/typeslib.pl

Added new treatment of user types.  (Pedro Lopez Garcia)

## [1.0.8] - 2002-12-09

../infernf/infernf.pl

Renamed nfnf.pl to nonfail.pl (Pedro Lopez Garcia)

## [1.0.7] - 2002-07-25

../plai/fixpo_dd.pl

Ported fixpo_dd to 1.0.  (Claudio Vaucheret)

## [1.0.6] - 2002-07-09

../plai/domains/gr.pl

Ported gr domain to 1.0.  (Claudio Vaucheret)

## [1.0.5] - 2002-07-09

../plai/domains/share.pl

Unified the sharing analysis in one module.  (Francisco Bueno
Carrillo)

## [1.0.4] - 2002-06-25

../plai/domains/eterms.pl

Ported type domains to 1.0.  (Claudio Vaucheret)

## [1.0.3] - 2002-01-15

../plai/plai.pl

Started porting PLAI to 1.0.  (Francisco Bueno Carrillo)

## [1.0.2] - 2002-01-11

../p_unit/p_unit.pl

Final version (for now) of the preprocessing unit.  (Francisco Bueno
Carrillo)

## [1.0.1] - 2001-11-07

../p_unit/p_unit.pl

First shot at reading a complete preprocessing unit for the current
module.  (Francisco Bueno Carrillo)

## [1.0.0] - 2001-11-07

Major code reorganization from CiaoPP 0.8. Moved to repo system.  See
below for 0.8 changelog prior to 1.0 (covers 1999-2003).

## [0.8.38] - 2003-08-28

Corrected bug in update_ai_goal (German Puebla).

## [0.8.37] - 2003-06-04

Since delay declarations in Ciao currently do not include
`freeze/2`, the optimization which transformed `when/2` into
`freeze/2` whenever possible has been commented out.  (German
Puebla).

## [0.8.36] - 2003-05-24

Added code to avoid non-termination of specialization of recursive
bridges. Then commented out since it is not really needed. In such a
case analysis determines the call does not succeed.  (German Puebla).

## [0.8.35] - 2003-05-14

Bridge predicates are now eliminated by the specializer.  (German
Puebla).

## [0.8.34] - 2003-05-13

Names of specialized versions are now much more readable.  (German
Puebla).

## [0.8.33] - 2003-05-13

Started specialization w.r.t. concrete values in collaboration with
Claudio Vaucheret.  (German Puebla).

## [0.8.32] - 2003-04-25

Added missing `use_module('ciaopp_zero.spec'(spec_delay))` since
predicate `program_points_not_final/4` used in fixpoint_del was
missing.  (German Puebla).

## [0.8.31] - 2003-03-31

Changed the way type definitions are printed in error messages.
(Francisco Bueno Carrillo).

## [0.8.30] - 2003-03-29

Changed text of messages and provided for line numbers in errors at
program points.  (Francisco Bueno Carrillo).

## [0.8.29] - 2003-03-28

Added comp assertion checking.  (Pedro Lopez Garcia).

## [0.8.28] - 2003-03-28

Implemented and exported the predicate exp_greater_than(Ex1, Ex2) in
order to compare (cost/size) functions (Pedro Lopez Garcia).

## [0.8.27] - 2003-03-13

Spec.  (Francisco Bueno Carrillo).

## [0.8.26] - 2002-12-04

Added automatic result checking for non-failure analysis.  (Pedro
Lopez Garcia).

## [0.8.25] - 2002-11-28

Added use_module(library(write)).  (Pedro Lopez Garcia).

## [0.8.24] - 2002-11-15

Reorganized distribution, unified changelogs.  (Francisco Bueno
Carrillo).

## [0.8.23] - 2002-11-15

Added analisis of call/n when possible from the domain info.
(Francisco Bueno Carrillo).

## [0.8.22] - 2002-11-15

Added specialization of meta-calls.  (Francisco Bueno Carrillo).

## [0.8.21] - 2002-10-16

Created file to hold basic operations related to type rules.  (Pedro
Lopez Garcia).

## [0.8.20] - 2002-10-16

Moved some predicates to other files. Commented some predicates.
(Pedro Lopez Garcia).

## [0.8.19] - 2002-11-08

Changed clpr_call/1 to work with ciao-1.8 (Pedro Lopez Garcia).

## [0.8.18] - 2002-11-08

Changed clpr_call/1 to work with ciao-1.8 (Pedro Lopez Garcia).

## [0.8.17] - 2001-11-22
   
`make_atom/2` which was in Ciao metaterms library has been moved
here.  (German Puebla).

## [0.8.16] - 2001-10-26

Changed preshell/0 to avoid the uncontrolled execution aborts
(Francisco Bueno Carrillo).

## [0.8.15] - 2001-09-10

Run-time checking can now be performed at program-point
level. Implemented by Elisa Fromont.  (German Puebla).

## [0.8.13] - 2001-07-27

Added list/1 as builtin in sharefree.  (Francisco Bueno Carrillo).

## [0.8.12] - 2001-07-26

When a literal has bottom as success substitution, a `fail` rather
than a `bottom` is added to the end of the clause. This is useful
for debugging as specialization. Not completely sure this is correct!!
(A. German Puebla Sanchez).

## [0.8.11] - 2001-07-25

Program point assertions are now treated as builtins for mode
analysis. This allows analyzing programs which contain program-point
assertions.  (A. German Puebla Sanchez).

## [0.8.10] - 2001-05-31

Added op declaration for &.  (Francisco Bueno Carrillo).

## [0.8.9] - 2001-03-22

Fixed a bug in handling of `findall/3`.  (A. German Puebla
Sanchez).

## [0.8.8] - 2001-03-22

Since _di_ does not need to know whether clauses are recursive or
not, we add the predicate `no_tarjan/2` which simply marks all
clauses as recursive (no tarjan is computed).  (A. German Puebla
Sanchez).

## [0.8.7] - 2001-03-22

`dd_fixp.pl` and `di_fixp.pl` also use this module now.
(A. German Puebla Sanchez).

## [0.8.6] - 2001-03-22

The depth independent fixpoint algorithm for incremental analysis is
now fully integrated.  (A. German Puebla Sanchez).

## [0.8.5] - 2001-03-06

Included del_meta_call for delay analysis.  (Francisco Bueno
Carrillo).

## [0.8.4] - 2000-10-30

Success assertions without precondition (i.e., precondition is true)
no longer call to prec. Also, solved bug with calls assertions.
(A. German Puebla Sanchez).

## [0.8.3] - 2000-07-11

Fixed bug which made printing files with info at program points fail
if analysis info was bottom.  (A. German Puebla Sanchez).

## [0.8.2] - 2000-07-11

Fixed bug which made specialization of nested meta-calls to fail if
the internal call was a variable.  (A. German Puebla Sanchez).

## [0.8.1] - 2000-07-11

Library modules which were builtins in ISO added to the set of modules
treated as native of mode analysis.  (A. German Puebla Sanchez).

## [0.7.34] - 2000-06-27

Solved bug in specialization of clauses with just a cut in its body.
(A. German Puebla Sanchez).

## [0.7.33] - 2000-03-28

Changed CIAO to Ciao in several places. Added file to version control.
(Manuel Hermenegildo).

## [0.7.32] - 2000-03-06

Changed lists of assertions in calls to rtchecks to disjunctions.
(Francisco Bueno Carrillo).

## [0.7.31] - 2000-02-14

Names of internal predicates are now generated using
reader:new_predicate/3, which should provide more elegant names.
(A. German Puebla Sanchez).

## [0.7.30] - 2000-02-12

Comp assertions are now correctly handled by the run-time checking
scheme. The rtchecks library has also been correspondingly updated.
(A. German Puebla Sanchez).

## [0.7.29] - 1999-12-22

Changed detection of variables in meta-calls.  (Francisco Bueno
Carrillo).

## [0.7.28] - 1999-11-30

Changed name of properties according to `nativeprops` package.
(Francisco Bueno Carrillo).

## [0.7.27] - 1999-11-30

Changed name of properties in trust_determin/5 (Francisco Bueno
Carrillo).

## [0.7.26] - 1999-11-30

Changed name of properties in trust_nonfail/5 (Francisco Bueno
Carrillo).

## [0.7.25] - 1999-11-30

Dummy entries were lost with typesfd. Changed fdtypes_unknown_entry/2
(dr_support.pl) to patch it.  (Francisco Bueno Carrillo).

## [0.7.24] - 1999-11-30

Entries in database had 'ptN'-like types instead of parametric. Solved
by using par_equiv_types/2 (Francisco Bueno Carrillo).

## [0.7.23] - 1999-11-30

With bottom and collapse_ai_vers(no) we got true() instead of
true(fails). Added prepare_point_info/5 to solve this. (Francisco
Bueno Carrillo).

## [0.7.22] - 1999-11-23

The predicate `indep/1` is added to the set of builtins
understood by analysis if annotation is performed and reanalysis is
required.  (A. German Puebla Sanchez).

## [0.7.21] - 1999-11-22

Solved a bug which made calls to side_effect_analyze loop.  (A. German
Puebla Sanchez).

## [0.7.20] - 1999-11-11

Manuals now installed in Ciao group.  (Manuel Hermenegildo).

## [0.7.19] - 1999-11-04

Added modular precompilation.  (Francisco Bueno Carrillo).

## [0.7.18] - 1999-10-20

Dump entries in the database instead of those in the program code
(required for scenario 2).  (Francisco Bueno Carrillo).

## [0.7.17] - 1999-10-18

Dynamic treatment for builtins: (1) no load of builtintables, (2)
on-the-run assert in pplib(builtins).  (Francisco Bueno Carrillo).

## [0.7.16] - 1999-09-29

Created plai_ops and incorporated plai_fixp_or.  (Francisco Bueno
Carrillo).

## [0.7.15] - 1999-09-13

Version of magic1 that keeps clauses for the builtins.  (Francisco
Bueno Carrillo).

## [0.7.14] - 1999-08-04

We now detect clauses whose head is incompatible with its call type
and issue a warning message.  (A. German Puebla Sanchez).

## [0.7.13] - 1999-08-02

Added check/1 and check/2 as meta-calls.  (Francisco Bueno Carrillo).

## [0.7.12] - 1999-08-02

Compile-time checking at program point now also exploits mode
information (in addition to type information).  (A. German Puebla
Sanchez).

## [0.7.11] - 1999-08-02

Predicates for issuing semantic compile-time messages are now in
module `ctchecks_messages`.  (A. German Puebla Sanchez).

## [0.7.9] - 1999-07-21

Added dump_ai_info/2 for raw dump of analysis info.  (Francisco Bueno
Carrillo).

## [0.7.8] - 1999-07-14

Add true as an ""always-builtin"", be it or not in the tables, since
facts have true as body and true is not otherwise understood in sccs
(dg3.pl).  (Francisco Bueno Carrillo).

## [0.7.7] - 1999-07-13

Added treatment for basic types.  (Francisco Bueno Carrillo).

## [0.7.6] - 1999-07-13

Do not try to solve basic types.  (Francisco Bueno Carrillo).

## [0.7.5] - 1999-07-13

Do not include basic types in the sccs.  (Francisco Bueno Carrillo).

## [0.7.4] - 1999-07-13

Tables of builtins off-line.  (Francisco Bueno Carrillo).

## [0.7.3] - 1999-07-13

Do not look for clauses defining builtins.  (Francisco Bueno
Carrillo).

## [0.7.2] - 1999-07-13

Actually only 'term' is in the lattice --all 'any' around changed to
'term'.  (Francisco Bueno Carrillo).

## [0.7.1] - 1999-07-13

First shot at incorporating generic RUL analysis.  (Francisco Bueno
Carrillo).

## [0.7.0] - 1999-07-12

Version freeze for major type inference mods.  (Manuel
Hermenegildo).

## [0.6.25] - 1999-07-05
   
`undoall_but_analysis` now also deletes the fact
`error_file_opened/1` which stores the stream which corresponds to
the error file. (A. German Puebla Sanchez).

## [0.1.24] - 1999-06-30

Changed walltime/1 by statistics/2 (Pedro Lopez Garcia).

## [0.6.23] - 1999-06-29

Adapted to changes in ciao-1.3 c_itf.  (Francisco Bueno Carrillo).

## [0.6.22] - 1999-06-15

Allow call/2 in the definition of regular types instead of regtype/2.
(Pedro Lopez Garcia).

## [0.6.21] - 1999-06-15

Allow call/2 in the body of a regular type definition instead of
regtype/2.  (Pedro Lopez Garcia).

## [0.6.20] - 1999-06-15

Allow call/2 in a regular type definition.  (Pedro Lopez Garcia).

## [0.6.19] - 1999-06-09

Commented out use_module of inferfdtypes (Pedro Lopez Garcia).

## [0.6.16] - 1999-04-12

Precompilation times are now measured using `statistics(runtime,_)`
which should be less dependent on the machine load than
`walltime/1`.  (A. German Puebla Sanchez).

## [0.6.15] - 1999-04-12

Adapted to work with the different fixpoint algorithms now in the
system.  (A. German Puebla Sanchez).

## [0.6.14] - 1999-04-09

As now there are several fixpoint algorithms, the module `fixpoint`
which contains the traditional fixpoint algorithm in PLAI has been
renamed to `plai_fixp`.  (A. German Puebla Sanchez).

## [0.6.13] - 1999-04-09

Integrated the _top-dowm_ or _depth-dependent_ fixpoint
algorithm for (incremental) analysis.  (A. German Puebla Sanchez).

## [0.6.12] - 1999-04-09

Added the flag `fixpoint/1` for selecting the fixpoint algorithm
for abstract interpretation.  (A. German Puebla Sanchez).

## [0.6.11] - 1999-04-09

The flag for controlling fixpoint_trace, previously called fixpoint/1
is now called trace_fixp/1.  (A. German Puebla Sanchez).

## [0.6.10] - 1999-04-08

Program transformation for run-time checking is performed in module
assrt_rtchecks.  (A. German Puebla Sanchez).

## [0.6.9] - 1999-04-08

Compile-time checking of assertions is performed in module
assrt_ctchecks.  (A. German Puebla Sanchez).

## [0.6.8] - 1999-04-08

Now the specializer is a separate module.  (A. German Puebla
Sanchez).

## [0.6.7] - 1999-04-08
   
output_user_interface/4 is now imported from plai(domains).
(A. German Puebla Sanchez).

## [0.6.5] - 1999-04-08

This module has been split into several subcomponents. Just a few of
the predicates originally exported by this module are still here.
(A. German Puebla Sanchez).

## [0.6.4] - 1999-04-08

First attempt at integrating incremental analysis.  (A. German Puebla
Sanchez).

## [0.6.3] - 1999-04-08

Added file type_ops.pl.  (Francisco Bueno Carrillo).

## [0.6.2] - 1999-04-08

Delay register no more set. Change in the future!  (Francisco Bueno
Carrillo).

## [0.6.1] - 1999-04-05

Upgraded to ciao-0.9 (Francisco Bueno Carrillo).

## [0.5.66] - 1999-03-30

Added compilation step for output file (including 'none').  (Francisco
   Bueno Carrillo).

## [0.5.65] - 1999-03-24

Mode and type analysis work together now (like the beatles!).
(Francisco Bueno Carrillo).

## [0.5.63] - 1999-03-13

Changed 'any' all around by top_type_symbol(Any).  (Francisco Bueno
Carrillo).

## [0.5.62] - 1999-03-13

To call spec_intersection instead of asking is_builtin_type now ask
is_base_type.  (Francisco Bueno Carrillo).

## [0.5.61] - 1998-12-24

Added treatment of dynamic/data.  (Francisco Bueno Carrillo).

## [0.5.60] - 1998-12-23

Parameterized query atoms on query_name/2 and query_suffix/1.
(Francisco Bueno Carrillo).

## [0.5.59] - 1998-12-19

Redone treatment of meta-calls.  (Francisco Bueno Carrillo).

## [0.5.58] - 1998-12-19

Error messages much improved.  (A. German Puebla Sanchez).

## [0.5.57] - 1998-12-18

Changed definition of nnegint_constant/2 to include zero.  (Pedro
Lopez Garcia).

## [0.5.56] - 1998-12-17

Patched a problem with type definitions ended by a variable (see
fill_body/2).  (Francisco Bueno Carrillo).

## [0.5.55] - 1998-12-16

Removed (commented out) the predicate builtin_types_list/1, because
currently, ALL builtin types are defined and get from
builtintables.pl.  (Pedro Lopez Garcia).

## [0.5.54] - 1998-12-16

Initialization taken out.  (Francisco Bueno Carrillo).

## [0.5.53] - 1998-11-11

First approach to program point type analysis.  (Pedro Lopez
Garcia).

## [0.5.52] - 1998-11-10

First shoot for operations used in program point type analysis.
(Pedro Lopez Garcia).

## [0.5.51] - 1998-11-04

Added first fact for dynamic predicate param_typ_sym_counter/1.
(Francisco Bueno Carrillo).

## [0.5.50] - 1998-11-04

Import predicate output_user_interface/4 from module infer.  (Pedro
Lopez Garcia).

## [0.5.49] - 1998-11-04

Import predicate output_user_interface/4 from module infer.  (Pedro
Lopez Garcia).

## [0.5.48] - 1998-11-04

Changed ; to # in pred assertions.  (Pedro Lopez Garcia).

## [0.5.47] - 1998-11-04

Added program point non-failure information.  (Pedro Lopez Garcia).

## [0.5.46] - 1998-11-04

Changed asserts to db_put/1 in database.  (Pedro Lopez Garcia).

## [0.5.45] - 1998-11-04

Changed asserts to db_put/1 in database.  (Pedro Lopez Garcia).

## [0.5.44] - 1998-11-04

Changed asserts to db_put/1 in database.  (Pedro Lopez Garcia).

## [0.5.43] - 1998-11-04

Changed asserts to db_put/1 in database.  (Pedro Lopez Garcia).

## [0.5.42] - 1998-10-29

Operations over clauses.  (Pedro Lopez Garcia).

## [0.5.41] - 1998-10-24
   
get_NO_par_type_definition now also looks for equivalences.
(Francisco Bueno Carrillo).

## [0.5.40] - 1998-10-24

Incorporated check_calls into one single module.  (Francisco Bueno
Carrillo).

## [0.5.39] - 1998-10-23

We now load check assertions for builtins.  (A. German Puebla
Sanchez).

## [0.5.38] - 1998-10-23

Compile-time checking of assertions for builtins is now performed.
(A. German Puebla Sanchez).

## [0.5.37] - 1998-10-23

Added clause for ! in types_for_builtins1.  (Francisco Bueno
Carrillo).

## [0.5.36] - 1998-10-22

Adapted documentation to new assertion syntax.  (Pedro Lopez
Garcia).

## [0.5.35] - 1998-10-22

No types are printed on the preprocessor execution.  (A. German Puebla
Sanchez).

## [0.5.34] - 1998-10-21

Made builtintables to be loaded dynamically.  (Francisco Bueno
Carrillo).

## [0.5.33] - 1998-10-21

Adapted the documentation of predicates to the new assertion syntax.
(Pedro Lopez Garcia).

## [0.5.32] - 1998-10-21

Modified the initialization of the counter used for creating type
symbols for parametric type instances. Now, the value of the counter
is taken from the module builtintables. Also, the value of the counter
after creating all parametric type instances is exported (via the
predicate get_last_type_symbol_counter/1).  (Pedro Lopez Garcia).

## [0.5.31] - 1998-10-21

Added builtin_type/1 from builtintables.  (Francisco Bueno
Carrillo).

## [0.5.30] - 1998-10-21

Adapted to new assertion syntax.  (Pedro Lopez Garcia).

## [0.5.29] - 1998-10-21

Adapted to new assertion format (Pedro Lopez Garcia).

## [0.5.28] - 1998-10-21

Adapted to new assertion format.  (Pedro Lopez Garcia).

## [0.5.27] - 1998-10-20

Added bottom_type for dead code.  (Francisco Bueno Carrillo).

## [0.5.26] - 1998-10-20

Incorporated generation of builtin tables from assertions.  (Francisco
Bueno Carrillo).

## [0.5.25] - 1998-10-20

Added missing operators for CHIP (A. German Puebla Sanchez).

## [0.5.24] - 1998-10-16

Added quiet/1 to give errors.  (Francisco Bueno Carrillo).

## [0.5.23] - 1998-10-15

Grouped type related predicates.  (Pedro Lopez Garcia).

## [0.5.22] - 1998-10-12

Put together valiation related predicates.  (Pedro Lopez Garcia).

## [0.5.21] - 1998-10-11

Changed generation of type-annotated terms to take into account
projection according to a mask.  (Pedro Lopez Garcia).

## [0.5.20] - 1998-10-11

Create this file to hold information (types) about predicates.  (Pedro
Lopez Garcia).

## [0.5.19] - 1998-10-10
   
Re-structuring of the code and cleaning.  (Pedro Lopez Garcia).

## [0.5.18,1998-10-10

Re-structuring of the code and cleaning.  (Pedro Lopez Garcia).

## [0.5.17] - 1998-10-08

Added type predicates (Pedro Lopez Garcia).

## [0.5.16] - 1998-10-08

Added type predicates (Pedro Lopez Garcia).

## [0.5.15] - 1998-10-08

Update to new assertions format (Pedro Lopez Garcia).

## [0.5.14] - 1998-10-02

Infertypes gives bottom types for dead code (i.e., bot(X) for all
arguments X -- set_bottom_type(T) should be called instead!)
(Francisco Bueno Carrillo).

## [0.5.13] - 1998-10-02

Prepared for including tables from builtins which are automatically
generated.  (Pawel Pietrzak).

## [0.5.12] - 1998-10-02

Unified inline_clause and builtin_typedef0, and get rid of all other
stuff.  (Francisco Bueno Carrillo).

## [0.5.11] - 1998-09-30

Changed par_equiv_types/2 to handle lists of lists of ...  (Francisco
Bueno Carrillo).

## [0.5.10] - 1998-09-28

Assertions are simplified using Abstract Executability.  (A. German
Puebla Sanchez).

## [0.5.9] - 1998-09-23

Assertions are simplified even if not completely reducible (A. German
Puebla Sanchez).

## [0.5.8] - 1998-09-22

sp_builtin/1 moved to builtin.pl.  (Pawel Pietrzak).

## [0.5.7] - 1998-06-14

Put together procedures proper of determinism analysis (Pedro Lopez
Garcia).

## [0.5.5] - 1998-05-07

Error message incorporates the line number.  (Francisco Bueno
Carrillo).

## [0.5.4] - 1998-05-04

Included Non-failure analysis.  (Pedro Lopez Garcia).

## [0.5.3] - 1998-04-23

Added (some) rewriting of non-standard types (e.g., any) to the basic
types. (Francisco Bueno Carrillo).

## [0.5.2] - 1998-04-23

Added `basic_types_pred_defs` (Francisco Bueno Carrillo).

## [0.4.36] - 1998-03-20

Assertions proved to be false now generate a compiler error.
(A. German Puebla Sanchez).

## [0.4.35] - 1998-3-18

Added back the loop to assert typedefs of builtin types: we should get
rid of this asap.  (Francisco Bueno Carrillo).

## [0.4.34] - 1998-3-18

Added `builtins_are_a_little_special/2` to handle call info for
builtins.  (Francisco Bueno Carrillo).

## [0.4.33] - 1998-3-16

Predicate intlist/1 renamed to intlist_now/1.  (A. German Puebla
Sanchez).

## [0.4.31] - 1998-03-13

Adapted for typesfd (Pawel's analysis).  (A. German Puebla Sanchez).

## [0.4.28] - 1998-3-12

Avoid returning all builtin types in the types `Table`. They are
now taken beforehand by using builtin_typedef/2.  (Francisco Bueno
Carrillo).

## [0.4.27] - 1998-3-12

Pass all types in second argument of fdtypes_td/4, add them as clauses
but with no magic transformation. The change in the magic makes all
calls to them not to be transformed, so types are now understood (in
e.g., entries). (Francisco Bueno Carrillo).

## [0.4.26] - 1998-3-6

Separate definitions of basic types in the lattice of regular types
(Pedro Lopez Garcia).

## [0.4.22] - 1998-3-3

Removed messages to terminal (now only if `debug(inferfdtypes)`
is set).  (Francisco Bueno Carrillo).

## [0.4.21] - 1998-02-28

Adapted to new format of types in memo-table and predicates for type
comparison.  Seems to work. (A. German Puebla Sanchez).

## [0.4.20] - 1998-2-28

Added builtin_typedef/2 to define the builtin types to the simplifier.
(Francisco Bueno Carrillo).

## [0.4.19] - 1998-2-28

Call to setval/2 in init_fdtypes/0 does not seem to work: moved to
undoall_fdtypes/0.  (Francisco Bueno Carrillo).

## [0.4.18] - 1998-2-28

Added support to un_name the variables in type rules, i.e., let them
as true variables.  (Francisco Bueno Carrillo).

## [0.4.17] - 1998-2-28

Added stuff to return typings of predicates and the definitions of the
types inferred in output arguments of fdtypes_td/4.  (Francisco Bueno
Carrillo).

## [0.4.16] - 1998-2-27

Added init_types to assert the builtin types of the analyzer.
(Francisco Bueno Carrillo).

## [0.4.15] - 1998-2-27

Created top.pl. It has the main entry points to assert entries,
polymorphic rules, and start analysis.  (Francisco Bueno
Carrillo).

## [0.4.14] - 1998-2-27

Changed findall's from clause/2 to inline_clause/2, since otherwise it
does not work in ciao because of the module name expansion.
(Francisco Bueno Carrillo).

## [0.4.13] - 1998-2-27

Changed sp_consult/2 so that it takes the program as an input list and
returns the list of predicates as output instead of asserting
them. Also, moved call to abolish_all_existing/0 to exported predicate
undoall_fdtypes/0. Also, replaced abolish by retractall (Francisco
Bueno Carrillo).

## [0.4.12] - 1998-2-27

Changed incorporate_types/2 so that it understands lists of pairs
(`T`,`R`) --`T` is the type, `R` is the rule. (Francisco Bueno
Carrillo).

## [0.4.11] - 1998-2-27

No default polimorphic rules are now asserted: there is an entry point
to assert them from the imported modules. (Francisco Bueno
Carrillo).

## [0.4.10] - 1998-2-27

rep_clauses/3 now just translates clauses from the format used in
precompiler to the format used within the analyzer. (Francisco
Bueno Carrillo).

## [0.4.9] - 1998-2-27

Magic transformation rewritten so that it asserts the clauses instead
of printing them to a file.  (Francisco Bueno Carrillo).

## [0.4.8] - 1998-2-27

Created main file inferfdtypes.pl. It incorporates utility predicates
in t.pl and typer.pl. (Francisco Bueno Carrillo).

## [0.4.7] - 1998-2-27

All definitions of builtin types duplicated so that they are defined
by predicate inline_clause/2 and a findall can be done of this
predicate to return the definitions WITHOUT module name expansion.
(Francisco Bueno Carrillo).

## [0.4.6] - 1998-2-27

Changed one findall from clause/2 to inline_clause/2, since otherwise
it does not work in ciao because of the module name
expansion. (Francisco Bueno Carrillo).

## [0.4.5] - 1998-2-24

Synchronized file versions with global Ciao version.  (Manuel
Hermenegildo).

## [0.4.4] - 1998-02-24

From the prototype version used for AADEBUG'97 (A. German Puebla
Sanchez).

## [0.4.4] - 1998-02-24

From the prototype version used for AADEBUG'97 (A. German Puebla
Sanchez).

## [0.4.2] - 1998-2-15

Put together predicates to be included in files that perform type
translation (Pedro Lopez Garcia).

## [0.4.1] - 1998-2-13

Validation of regular types (Pedro Lopez Garcia).

## [0.4.0] - 1998-2-12

First modularization of the code. (Francisco Bueno Carrillo).

## [0.3.6] - 1997-11-12

Transformed internal documentation to assertion format. (Manuel
Hermenegildo).

## [0.3.5] - 1997-11-24

Grouped support predicates for type operations. Add on-line
documentation (Francisco Bueno and Pedro Lopez Garcia).

## [0.3.4] - 1997-11-20

Included some procedures that were in module rul (Pedro Lopez
Garcia).

## [0.3.3] - 1997-11-20

Improved treatment of numeric types (Pedro Lopez Garcia).

## [0.3.2] - 1997-11-3

Fixed a minor syntax error. (Manuel Hermenegildo).

## [0.3.1] - 1997-10-29

Started adding on-line documentation to typeslib. (Pedro Lopez
Garcia).

## [0.3.0] - 1997-5-1

First version of typeslib. (Pedro Lopez Garcia).

# (Prior changelogs not lpdoc-based, probably lost?)

## [0.1.1] - 1993-10-1

First version of support.pl. (Francisco Bueno).

## [0.1.0] - 1993-10-1

First version of m_ciaopp.pl (Francisco Bueno).

