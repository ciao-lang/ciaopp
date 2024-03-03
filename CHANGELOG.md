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

