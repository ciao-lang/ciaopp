# Changelog

## [1.6.0] - 2022-9-28 

### Added

 - Integrate test case generation for assertion-based random test
   generation (currently `ciaotest` bundle) into the CiaoPP's
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

## [1.0.0] - 2001-11-07

Major code reorganization from CiaoPP 0.8. Moved to repo system.  See
0.8 manual for changelog prior to 1.0 (covers 1999-2000).
