:- module(_, [], [assertions]).

:- doc(filetype, part).

:- doc(title, "Available abstract domains").

:- doc(module, "

@subsection{Groundness and sharing}

  @begin{itemize}
 @item @tt{gr} tracks groundness in a very simple way
        (see @ref{Simple groundness abstract domain}).
 @item @tt{def} tracks groundness dependencies, which improves the accuracy
                in inferring groundness.
 @item @tt{share} tracks sharing among (sets of) variables @cite{ai-jlp},
                  which gives a 
                  very accurate groundness inference, plus information on
                  dependencies caused by unification.
 @item @tt{son} tracks sharing among pairs of variables, plus variables
                which are linear (see @cite{sonder86}).
 @item @tt{shareson} is a combination of the above two @cite{comdom},
                     which may improve on the accuracy of any of them alone.
 @item @tt{shfr} tracks sharing and variables which are free
                 (see @cite{freeness-iclp91}).
 @item @tt{shfrson} is a combination of @tt{shfr} and @tt{son}.
 @item @tt{shfrnv} augments @tt{shfr} with knowledge on variables which
                   are not free nor ground.
@end{itemize}

@subsection{Term structure}
@begin{itemize}
 @item @tt{depth} tracks the structure of the terms bound to the program
                  variables during execution, up to a certain depth; the
                  depth is fixed with the @tt{depth} flag.
 @item @tt{path} tracks sharing among variables which occur within the
                 terms bound to the program variables during execution;
                 the occurrence of run-time variables within terms is tracked
                 up to a certain depth, fixed with the @tt{depth} flag.
 @item @tt{aeq} tracks the structure of the terms bound to the program
                variables during execution plus the sharing among the
                run-time variables occurring in such terms, plus freeness
                and linearity.
                The depth of terms being tracked is set with the @tt{depth}
                flag. Sharing can be selected between set-sharing or
                pair-sharing.
@end{itemize}

@subsection{Types}

Type analysis supports different degrees of precision. For example,
with the flag @tt{type_precision} with value @tt{defined}, the
analysis restricts the types to the finite domain of predefined types,
i.e., the types defined by the user or in libraries, without
generating new types.  Another alternative is to use the normal
analysis, i.e., creating new type definitions, but having only
predefined types in the output. This is handled through the
@tt{type_output} flag.

@begin{itemize}
 @item @tt{eterms} performs structural widening (see @cite{eterms-sas02}).

   Greater precision can be obtained evaluating builtins like @tt{is/2}
   abstractly: @tt{eterms} includes a variant which allows evaluation of the 
   types, which is governed by the @tt{type_eval} flag. 

 @item @tt{ptypes} uses the topological clash widening operator (see
       @cite{VanHentenryckCortesiLeCharlier95}). 
 @item @tt{svterms} implements the rigid types domain of @cite{janss92}.
 @item @tt{terms} uses shortening as the widening operator (see
       @cite{gallagher-types-iclp94}), in several fashions, which are
       selected via the @tt{depth} flag; depth 0 meaning the use of restricted
       shortening @cite{Saglam-Gallagher-94}.
@end{itemize}

@subsection{Partial evaluation}

Partial evaluation is performed during analysis when the @tt{local_control} 
flag is set to other than @tt{off}. Flag @tt{fixpoint} must be set to
@tt{di}. Unfolding will take place while analyzing the program, therefore
creating new patterns to analyze. The unfolding rule is governed by flag
@tt{local_control} (see @tt{transformation(codegen)}).

For partial evaluation to take place, an analysis domain capable of tracking
term structure should be used (e.g., @tt{eterms}, @tt{pd}, etc.). 
In particular:

@begin{itemize}
 @item @tt{pd} allows to perform traditional partial evaluation but using 
       instead abstract 
       interpretation with specialized definitions @cite{ai-spec-defs-tr}.
 @item @tt{pdb} improves the precision of @tt{pd} by detecting calls 
       which cannot succeed, i.e., either loop or fail.
@end{itemize}

Note that these two analyses will not infer useful information on the program.
They are intended only to enable (classical) partial evaluation.

@subsection{Constraint domains}
@begin{itemize}
 @item @tt{fr} @cite{v.phd} determines variables which are not constraint 
       to particular values in the constraint store in which they occur, 
       and also keeps track of possible dependencies between program variables.
 @item @tt{frdef} is a combination of @tt{fr} and @tt{def}, determining
       at the same time variables  which are not constraint to particular 
       values and variables which are constraint to a definite value.
 @item @tt{lsign} @cite{Lsign} infers the signs of variables involved in linear
       constraints (and the possible number and form of such constraints).
 @item @tt{difflsign} is a simplified variant of @tt{lsign}.
@end{itemize}

@subsection{Properties of the computation}

@begin{itemize}

 @item @tt{det} detects procedures and goals that are deterministic
  (i.e. that produce at most one solution), or predicates whose
  clause tests are mutually exclusive (which implies that at most one
  of their clauses will succeed) even if they are not deterministic
  (because they call other predicates that can produce more than one
  solution).

 @item @tt{nfg} detects procedures that can be guaranteed not to fail
  (i.e., to produce at least one solution or not to terminate). It is a
  mono-variant non-failure analysis, in the sense that it infers
  non-failure information for only a call pattern per predicate
  @cite{non-failure-iclp97}.

 @item @tt{nf} detects procedures @em{and goals} that can be guaranteed not
  to fail and is able to infer separate non-failure information for different 
  call patterns @cite{nfplai-flops04}.

 @item @tt{seff} marks predicates as having side-effects or not.

@end{itemize}

@subsection{Size of terms}

Size analysis yields functions which give bounds on the size of output
data of procedures as a function of the size of the input data.  The
size can be expressed in various measures, e.g., term-size, term-depth,
list-length, integer-value, etc.

@begin{itemize}
   @item @tt{size_ub} infers upper bounds on the size of terms.
   @item @tt{size_lb} infers lower bounds on the size of terms.
   @item @tt{size_ualb} infers both upper and lower bounds on the size of 
          terms.
   @item @tt{size_o} gives (worst case) complexity orders for term size 
          functions (i.e. big O).
@end{itemize}

@subsection{Number of resolution steps of the computation}

   Cost (steps) analysis yields functions which give bounds on the cost
 (expressed in the number of resolution steps) of procedures as a
 function of the size of their input data.

@begin{itemize}
  @item @tt{steps_ub} infers upper bounds on the number of resolution
        steps. Incorporates a modified version of the CASLOG
        @cite{caslog} system, so that CiaoPP analyzers are used to
        supply automatically the information about modes, types, and
        size measures needed by the CASLOG system.
  @item @tt{steps_lb} infers lower bounds on the number of resolution
        steps. Implements the analysis described in
        @cite{low-bounds-ilps97}.
  @item @tt{steps_ualb} infers both upper and lower bounds on the number of
        resolution steps.
  @item @tt{steps_o} gives (worst case) complexity orders for cost
        functions (i.e. big O).
@end{itemize}

@subsection{Execution time of the computation}
@begin{itemize}
  @item @tt{time_ap} yields functions which give approximations on the
        execution time (expressed in milliseconds) of procedures as a
        function of the size of their input data.
@end{itemize}
").
