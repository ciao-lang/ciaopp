:- use_package([assertions]).

:- doc(filetype, documentation).

:- doc(title,"The Preprocessing Unit").

:- doc(module,
"This component handles data structures for the code of the current module and
for all information about it that may be necessary to precompile that
module. Since CiaoPP works in a per-module fashion, when preprocessing one
module the modules imported by it may not be accessible. However, 
information on imported predicates may be essential for some manipulations
of the current module: e.g., for analyzing it with greater precision. For
this reason, information about exported predicates of a module is stored
in separate cache files. The cache files of modules imported by the current
module are then loaded together with the file of the current module. All
the information stored together with the current module is called the
preprocessing unit of the current module.

Cache files are used to save assertions that refer to exported predicates,
properties exported or properties that are used in assertions for exported
predicates, and properties used in the definiton of other relevant properties.
(The exact definition of what is cached and how the preprocessing unit is
obtained from this caches is given in the chapter for @lib{p\_asr}).
This facilitates the use within CiaoPP of all information that
may be relevant about exported predicates that may be imported into other
modules. This information from (user) assertions is extracted from the
module code.

Other information that may be relevant is that inferred by CiaoPP on its own.
The information from analysis that refers to exported predicates of a module
is also cached in separate files, so that the preprocessing of other modules
that import such predicates can use the information. Currently, separate
files are used for user supplied assertions (the so called .asr file) and
for information from analysis (the so called .abs file). Module @lib{p\_asr}
is in charge of the .asr file and module @lib{p\_abs} is in charge of the
.abs files.

More information concerning the current module that this component serves
includes: initialization directives, entry assertions that may need
analysis, whether a predicate is a meta-predicate or a dynamic predicate, 
whether it is a ""builtin"", a property, or a native property, etc. In the
sections below we explain what is understood by builtin predicate and native
property. The complete functionality offered by this component is explained
in the following chapters.

@section{The preprocessing unit}

In the following, related files refer to files defining modules from which
the current module imports a predicate, whether via direct importation or 
via re-exportation by an imported module.
The @em{preprocessing unit} @cindex{preprocessing unit} consists of:

@begin{enumerate}
@item the code (and directives) of the current module,
@item the assertions of the current module,
@item the (imported) properties of related files which are used in
      the previous assertions,
@item the assertions of related files for predicates imported by
      the current module,
@item the properties of related files (or imported by them) which are used in
      the previous assertions,
@item the properties transitively used in the definitions of all the
      previous properties, whichever file they are defined.
@end{enumerate}

Note that once the preprocessing unit of the current module is loaded, every
assertion for a predicate of the current module or imported into the current
module can be correctly and completely interpreted, since all the properties
that may appear in such assertions (or transitively used in the definitions
of such properties) are available. This is the main reason for including
the preprocessing unit of the current module instead of simply loading the
current module itself alone (and some assertions for imported predicates, 
probably).

@section{Builtin predicates}

A predicate is builtin @cindex{builtin predicate} if there is information
about it built into one of the components of CiaoPP. This is the case, for
example, for analyzers. Usually, these predicates are ISO predicates, whose
semantics conform with the standard, and thererefore, can be implemented
into CiaoPP once and for all. The names used to refer to these predicates
are thus usually also the ISO names.

However, in a modular system like Ciao, such builtin predicates may be
defined in a module, and can be used (imported) or not by the current module. 
Whether the predicate is visible or not to the current module is solved
by looking at the module interface of the current module. The exact name
of the predicate (at the source language level) can be known; for example,
ISO @tt{var/1} in CiaoPP is @tt{term\_typing:var/1}. This name could also be
built into CiaoPP, but this would tight CiaoPP to the particular module
structure of the library of a system (Ciao, in this case). Instead, there
is a dynamic scheme that makes CiaoPP more flexible: To indicate that a
given predicate in a given module corresponds to a builtin predicate, the
following kind of assertions are used:

@begin{verbatim}
:- pred var(X) + native(var(X)).
@end{verbatim}

This assertion in module @tt{term\_typing} tells CiaoPP that predicate 
@tt{term\_typing:var(X)}
corresponds to the predicate builtin into CiaoPP as @tt{var(X)}. Note that
the name @tt{var/1} should be used all throughtout CiaoPP to identify that
very same predicate (the one in ISO by that name, in this case).
This is mandatory.

Note also that with the above scheme, the only real predicate name that is
built into CiaoPP is that for the property @tt{native(Pred,Name)}, which 
currently is precisely @tt{native(Pred,Name)} (which is currently defined
in library module @lib{engine(basic\_props)}).

@section{Native properties}

A property in Ciao is a predicate. Certain properties are used within CiaoPP
in a native way, which means that some component understands the property
natively (for example, an analysis for groundness understands the property
of being ground). These properties are called  @em{native properties}
@cindex{native properties}.

The same problem above for builtin predicates occurs also for native 
properties, 
and the same solution has been given to the problem also in this case. To
indicate that a given predicate corresponds to a property understood
natively by CiaoPP the following kind of assertions are used:

@begin{verbatim}
:- prop var(X) + native(free(X)).
@end{verbatim}

This is interpreted by CiaoPP so that predicate @tt{term\_typing:var(X)}
corresponds to the native property identified in CiaoPP as @tt{free(X)}. 
Note that the name @tt{free/1} should be used all throughtout CiaoPP to 
identify that property. The names of native properties are defined in
@tt{native:native/1}.

The (default) predicates that are used as source language level counterparts
of the native property names are gathered together in a Ciao library module
that currently is @lib{library(assertions/native\_props)}.

There is an scheme for translating predicate property names to native property
names upon input of the current module, and native property names back to
predicate property names upon output that is described in the chapter about
module @lib{domains}.

@section{Organization of the code}

The organization of the code of this component is as follows:

 @image{punit}

Module @lib{p\_unit} is in charge of supporting all other CiaoPP 
components when they require information about the program. Module
@lib{p\_asr} is in charge of processing the .asr files and gathering
together the preprocessing unit for the current module. Module
@lib{assrt\_norm} is used to normalize assertions. Module @lib{p\_abs} is in
charge of reading .abs files and writing them. Module @lib{assrt\_db} maintains 
the database of assertions, module @lib{clause\_db} the database of
clauses, and module @lib{itf\_db} the database of information related to
the module interface of the current module.

Each of the modules is documented in the following chapters.

").
