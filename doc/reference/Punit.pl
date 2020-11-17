:- use_package(assertions).

:- doc(filetype, part).

:- doc(title,"The Preprocessing Unit Component").

:- doc(module, "This component is in charge of processing the .asr
files, gathering together the code for the preprocessing unit of the
current module.  The preprocessing unit is the code of the current
module together with the set of assertions/properties which allows a
precise interpretation of the assertions present for the current
module.  It serves the rest of the precompiler current module clauses,
assertions, (definitions of) properties related, and characteristics
of the current module predicates (e.g.: initialization directives,
whether a predicate is a meta-predicate, whether it is a ""builtin"",
etc.).").
