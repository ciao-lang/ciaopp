:- module(ciaopp_tutorials,[],[assertions]).

:- doc(filetype, application).

:- doc(title,"CiaoPP Tutorials").
:- doc(author, "The Ciao Development Team").

:- doc(logo, 'ciao-logo').

:- doc(subtitle_extra,"A set of CiaoPP Tutorials").
:- doc(subtitle_extra,"@bf{The Ciao Documentation Series}").
:- doc(subtitle_extra,"@href{https://ciao-lang.org/}").
:- doc(subtitle_extra,"@em{Generated/Printed on:} @today{}").
% :- doc(subtitle_extra,"Technical Report CLIP 1/06 (first version 8/95).").

:- include(core_docsrc(common/'ClipAddress')).

:- doc(credits, "@bf{Edited by:}").
:- doc(credits, "Manuel Hermenegildo").
:- doc(credits, "Pedro L@'{o}pez").
:- doc(credits, "Jos@'{e} Francisco Morales").

:- doc(summary, "This document/site groups a number of @bf{interactive
tutorials} meant to help when starting to use @apl{CiaoPP}. It is a
companion to the @bf{reference} manual for @apl{CiaoPP}, which gives a
fuller description of the system.").

:- doc(module, "This document groups a number of @bf{tutorials} meant
to help when starting to use @apl{CiaoPP}. It is a companion to the
@bf{reference} manual for @apl{CiaoPP}, which gives a fuller description of
the system. Some of these tutorials are @em{interactive},
@cindex{tutorials} @cindex{interactive tutorials} using the
@concept{Active Logic Documents} facility of @apl{LPdoc}.

The following tutorials are available:

@begin{itemize}

@item @ref{CiaoPP at a glance}. This brief tutorial provides a quick
overview suitable for understanding the some basics about how @apl{CiaoPP}
works. It is however is not intended to be a tutorial on how to use
@apl{CiaoPP}. The following tutorial is recommended for this.

@item @ref{A Gentle Introduction to Static Verification and Bug
Finding with CiaoPP}.  This tutorial illustrates step-by-step the
development of a concrete program starting from a given problem
statement and a specification, expressed using the @apl{Ciao}
assertion language, to describe predicates and their properties. Our
aim is to show how to use @apl{CiaoPP} to prove @em{statically}
whether these assertions hold and/or detect bugs, while stepwise
developing the program. The tutorial also provides an introduction to
the dynamic checking aspects of @apl{CiaoPP}. In particular, the
document includes the following topics:

@begin{itemize}
@item Defining modules and exports
@item Type and Mode Analysis 
@item Assertions and properties
@item Non-failure and Determinacy Analysis
@item Dynamic Bug Finding with @apl{CiaoPP}'s Testing Facilities
@end{itemize}

@item @ref{Program Development using the CiaoPP Program Processor} is
a more advanced tutorial. The tutorial includes these sections:

@begin{itemize}

@item Static Analysis and Program Assertions
@begin{itemize}
@item Static Analysis Basics
@item Type Analysis
@item Non-failure and Determinacy Analysis
@item Size, Resources, and Termination Analysis
@item Decidability, Approximations, and Safety
@end{itemize}

@item Program Debugging and Assertion Checking
@begin{itemize}
@item Assertions and Properties
@item Using analysis information for debugging
@item Static Checking of Assertions in System Libraries
@item Static Checking of User Assertions and Program Validation
@item Performance Debugging and Validation
@end{itemize}

@end{itemize}

@end{itemize}

@section{About CiaoPP}

@include{CiaoPPRefSummary.lpdoc}

").

