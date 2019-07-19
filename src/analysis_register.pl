:- package(analysis_register).

:- doc(lazy_analysis/1, "Specifies an analysis that can be lazy loaded").

:- multifile lazy_analysis/1.

:- doc(analysis_module/2, "Given an analysis, returns the module that
	contains the implementation (or entry point) of a lazy
	loadable analysis. Such module must implement the analysis/4
	multifile clause.").

:- multifile analysis_module/2.

:- doc(loaded_analysis/1, "Helps to determine if an analysis was
	already loaded.  Must be defined in the same module specified
	by analysis_module/2.").

:- multifile loaded_analysis/1.

