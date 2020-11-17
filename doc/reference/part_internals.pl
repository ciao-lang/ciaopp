:- module(_,[],[assertions]).

:- doc(filetype, part).

:- doc(title,"PART IV - CiaoPP Internals").

:- doc(module,"CiaoPP is provided as a module that can be either
loaded in the shell or imported into a user program module. There are 
predicates that activate each option, a predicate to load the
file to be processed, and predicates to perform the action of
each task of CiaoPP.

This document describes the structure of the code of CiaoPP, its 
components (each performing a task), and their functionality, from the
point of view of the implementor, not of the user.

@section{How to use CiaoPP in your own preprocessor}

If you implement a program for preprocessing Ciao programs, you can
take advantage of the facilities provided by CiaoPP. The
basic facilities are described in the following three chapters. 
In particular, the chapter on module @lib{driver} explains how to 
integrate your tool and CiaoPP to make them work together.

One particularly useful feature of CiaoPP is that it provides for the correct
reading of an input program to be preprocessed (this is more tricky than
it seems, because of all of the language features that the program might
be using). Once a program is read in by CiaoPP, your tool can process it
as plain Prolog. The chapter on module @lib{p_unit} explains how a
program is (correctly) read in, and provides an interface so that you
can retrieve information about that program.

Depending on the kind of preprocessing you want to do, you may want to use
other parts of CiaoPP. If your program is doing program transformations,
then the chapters on @lib{program_keys} and @lib{tr_syntax} might be helpful.
If you want to use
analysis information to help the transformations, then the chapter on 
@lib{infer} is the one to read. If your program is a program analyzer
based on abstract interpretation, then have a look at the chapters on
@lib{plai} and @lib{domains}. Program analyses not based on abstract 
interpretation (and other possible tools) may be a bit harder to incorporate:
you might need to develop first your skills with the CiaoPP code...
").

:- doc(appendix,"
The work of CiaoPP is focused on one-module-at-a-time.
The file being preprocessed at a given time is called the 
@em{current module} @cindex{current module}.
If the file is of the user module, it is considered as a module which
exports all its predicates.

The preprocessing unit is the code of the current module together with the
set of assertions / properties which allows a correct and complete
interpretation of the assertions present for the current module.
Assertions and properties are usually cached in auxiliary files, which
are called the .asr files.

@section{Basic structure of the code}

The code of CiaoPP is divided into @em{components},
   each of which provides a particular functionality. The top-level 
   organization of the main components is as follows: 

 @image{ciaopp}

Each component is addressed by a particular qualifier, which makes reference
to modules independent of the particular library paths. These qualifiers
are defined in file @lib{paths.pl}. The qualifier for the top-level components
is @lib{ciaopp}.

The component @lib{p_unit} is addressed by qualifier @var{program}
and is in charge of processing the .asr files, gathering together the
code for the preprocessing unit of the current module. 

The component @lib{tr_syntax} is addressed by qualifier @var{syntax}
and implements simple source code syntactic transformations (like removing
disjunctions and the like).

The component @lib{infer} is addressed by qualifier @var{infer}
and is in charge of serving all known semantic information on the
current module, from any analysis and/or assertion.

The component @lib{plai} is addressed by qualifier @var{plai}
and implements abstract interpretation based analysis. 

The component @lib{infernf} is addressed by qualifier @var{infernf}
and implements the non-failure analysis. 

The component @lib{infercost} is addressed by qualifier @var{infercost}
and implements the cost analysis. 

").

