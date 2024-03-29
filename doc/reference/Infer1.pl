:- use_package(assertions).

:- doc(filetype, part).

:- doc(title,"The Global Information Server").

:- doc(module,
"This component is in charge of serving the rest of the precompiler all
known semantic information on the current module, either from any analysis
or from the assertions. 

The (basic) organization of the code is as follows: 

 @image{infer}

Module @lib{infer} is in charge of interfacing with the rest of CiaoPP.
Module @lib{modes} implements a mode analysis based on sharing information.
Module @lib{vartypes} implements a moded type analysis based on freeness
and regular type information. Module @lib{infer\_db} is the centralized
repository for all analysis information.
Module @lib{typeslib} implements a library for manipulation of regular types.
").
