:- module(adding_new_domain,[],[assertions]).

:- doc(filetype, documentation).

:- doc(title,"Adding a new analysis domain to CiaoPP").

:- doc(author,"The Ciao Development Team").

:- doc(summary,"This chapter shows how to add an abstract
interpretation-based analysis domain to CiaoPP. It is illustrated with
a simple domain already existing in CiaoPP to infer groundness
information of program variables.").

:- doc(module,"

One of the most relevant features of the CiaoPP system is that it
allows the addition of new analysis domains to the abstract
interpretation-based framework in an easy way. 

The next Chapter (@ref{Plug-in points for abstract domains}) describes
the module @tt{domains.pl}, the general interface used by the analyzer
for accessing the operations of the different domains implemented in
the system.  The developer of a new domain must edit this module,
adding the necessary clauses to link the general interface with the
specific operations of the new domain.


The procedure of adding a new domain is illustrated in 
@ref{Simple groundness abstract domain} by means of a simple abstract
domain for groundness information inference.  It includes a list of
the predicates that need to be implemented by the developer in order
to add the abstract domain to CiaoPP.

").


