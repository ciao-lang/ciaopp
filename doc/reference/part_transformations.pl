:- module(_, [], [assertions]).

:- doc(filetype, part).

:- doc(title, "Available program transformations").

:- doc(module, "

@subsection{Program specialization}
@begin{itemize}
 @item @tt{simp} This transformation tries to explote analysis
 information in order to @em{simplify} the program as much as
 possible. It includes optimizations such as abstract executability of
 literals, removal of useless clauses, and unfolding of literals for
 predicates which are defined by just a fact or a single clause with
 just one literal in its body (a @em{bridge}). It also propagates
 failure backwards in a clause as long as such propagation is safe.
 @item @tt{spec} This transformation performs the same optimizations
 as @tt{simp} but it also performs multiple specialization when this
 improves the possibilities of optimization. The starting point for
 this transformation is not a program annotated with analysis
 information, as in the case above, but rather an @em{expanded
						     program} which
 corresponds to the analysis graph computed by multi-variant abstract
 interpretation. A minimization algorithm is used in order to
 guarantee that the resulting program is minimal in the sense that
 further collapsing versions would represent losing opportunities for
 optimization. 
 @item @tt{vers} This transformation has in common with @tt{spec} that
 it takes as starting point the @em{expanded program} which
 corresponds to the analysis graph computed by abstract
 interpretation. However, this transformation performs no
 optimizations and does not minimize the program. As a result, it
 generates the expanded program.
@end{itemize}

@subsection{Partial evaluation}

@begin{itemize}
 @item @tt{codegen} This generates the specialized program resulting
 from partial evaluation, obtained by unfolding goals during analysis. The
 kind of unfolding performed is governed by the @tt{comp_rule} flag,
 as follows:

   @begin{itemize}
   @item @tt{leftmost} unfolds the leftmost clause literal;
   @item @tt{eval_builtin} selects for unfolding first builtins which can
         be evaluated;
   @item @tt{local_emb} tries to select first atoms which do not endanger
         the embedding ordering or evaluable builtins whenever possible;
   @item @tt{jump_builtin} selects the leftmost goal but can `jump' over
         (ignore) builtins when they are not evaluable. A main difference
         with the other computation rules is that unfolding is performed 
         `in situ', i.e., without reordering the atoms in the clause.
   
   @item @tt{safe_jb} same as @tt{jump_builtin} with the difference
 that it only jumps over a call to a builtin iff the call is safe @cite{nonleftmost-lopstr05} (i.e., it is error free, binding insensitive and side effect free).

   @item @tt{bind_ins_jb} same as @tt{safe_jb} with the
   difference that it only jumps over a call to a builtin iff  the call is binding insensitive and side effect free.

    @item @tt{no_sideff_jb} same as @tt{bind_ins_jb} with the
  difference that it only jumps over a call to a builtin iff it is
  side effect free.  

@end{itemize}

Unfolding is performed continuously on the already unfolded clauses, until a 
condition for stopping the process is satisfied. This condition is stablished
by the local control policy, governed by the @tt{local_control} flag,
as follows:

   @begin{itemize}
   @item @tt{inst} allows goal instantiation but no actual unfolding is
         performed.
   @item @tt{orig} returns the clauses in the original program for the
         corresponding predicate.
   @item @tt{det} allows unfolding while derivations are deterministic 
         and stops them when a non-deterministic branch is required.
         Note that this may not be terminating.
   @item @tt{det_la} same as @tt{det}, but with look-ahead. It can perform
          a number of non-deterministic steps in the hope that the computation
          will turn deterministic. This number is determined by flag
          @tt{unf_depth}.
   @item @tt{depth} always performs the same number of unfolding steps for 
         every call pattern. The number is determined by flag @tt{unf_depth}.
   @item @tt{first_sol} explores the SLD tree width-first and keeps on 
         unfolding until a first solution is found. It can be non-terminating.
   @item @tt{first_sol_d} same as above, but allows terminating when a
         given depth bound is reached without obtaining any solution.
         The bound is determined by @tt{unf_depth}.
   @item @tt{all_sol} tries to generate all solutions by exploring the 
         whole SLD tree. This strategy only terminates if the SLD is finite.
   @item @tt{hom_emb} keeps on unfolding until the selected atom is
         homeomorphically embedded in an atom previously selected for 
         unfolding.
   @item @tt{hom_emb_anc} same as before, but only takes into account 
         previously
         selected atoms which are ancestors of the currently selected atom.
   @item @tt{hom_emb_as} same as before, but efficiently implemented
         by using a stack to store ancestors.
   @item @tt{df_hom_emb_as} same as before, but traverses the SLD tree
         on a depth-first fashion (all strategies above use wide-first
         search). This allows better performance.
   @item @tt{df_tree_hom_emb} same as above, but does not use the
         efficient stack-based implementation for ancestors.
   @item @tt{df_hom_emb} same as above, but compares with all
         previously selected atoms, and not only ancestors. It is like
         @tt{hom_emb} but with depth-first traversal.
   @end{itemize}

 @item @tt{global_control} In order to guarantee termination of the
 partial evaluation process, it is often required to abstract away
 information before unfolding. This is usually known as global
 control. This flag can have the following values:

   @begin{itemize}
   @item @tt{off} unfolds always;
   @item @tt{id} unfolds patterns which are not equal (modulo renaming) to a 
	 formerly analyzed pattern.
   @item @tt{inst} unfolds patterns which are not an instance of a previous
	 pattern.
   @item @tt{hom_emb} unfolds patterns which are not covered under the
         homeomorphic embedding ordering @cite{Leuschel:SAS98}.
    @item @tt{hom_emb_num} same as @tt{hom_emb},
	but also considers that any number embeds any other number.

 @end{itemize}

   Only @tt{hom_emb} guarantees termination. However, @tt{id} and
   @tt{inst} are more efficient, and terminating in many practical
   cases.

 @item @tt{arg_filtering} This transformation removes from program literals
 static values which are not needed any longer in the resulting program.
 This is typically the case when some information is known at compile-time
 about the run-time values of arguments. 

 @item @tt{codegen_af} This performs @tt{codegen} and @tt{arg_filtering} 
 in a single traversal of the code. Good for efficiency.
@end{itemize}

@subsection{Code size reduction}

@begin{itemize}
 @item @tt{slicing} This transformation is very useful for debugging
 programs since it isolates those predicates that are reachable from a
 given goal. The goals used are those exported by the module.
 The `slice' being obtained is controlled by the following local control 
 policies (described above): @tt{df_hom_emb_as}, @tt{df_hom_emb},
 @tt{df_tree_hom_emb}. It is also necessary to analyze the program
 with any of the currently available analyses for partial evaluation.
 Slicing is also very useful in order to perform other software engineering 
 tasks, such as program understanding, maintenance, specialization, 
 code reuse, etc.
@end{itemize}

@subsection{Program parallelization}

Parallelization is performed by considering goals the execution of which
can be deemed as @em{independent} @cite{sinsi-jlp,consind-toplas}
under certain conditions. Parallel expressions (possibly conditional) are
built from such goals, in the following fashions:

@begin{itemize}
 @item @tt{mel} exploits parallel expressions which preserve the ordering
                of literals in the clauses;
 @item @tt{cdg} tries to exploit every possible parallel expression, without
                preserving the initial ordering;
 @item @tt{udg} is as above, but only exploits unconditional parallel
                expressions @cite{annotators-jlp};
 @item @tt{urlp} exploits unconditional parallel expressions for NSIAP with
                @em{a posteriori} conditions @cite{nsicond-sas94}.
 @item @tt{crlp} exploits conditional parallel expressions for NSIAP with
                @em{a posteriori} conditions.

 @item @tt{granul} This transformation allows to perform run-time
 task granularity control of parallelized code 
 (see @cite{granularity-jsc}), so that the program will decide
 at run-time whether to run parallel expressions or not.
 The decision is based on the value of flag @tt{granularity_threshold}.
@end{itemize}

@subsection{Abstract partial deduction}

@concept{Partial deduction} (or @concept{partial evaluation}) is a program
transformation technique which specializes the program w.r.t. information
known at compile-time. In CiaoPP this is performed during analysis of the
program, so that not only concrete information but also abstract information
(from the analysis) can be used for specialization. With analysis domain
@tt{pd} (and @tt{pdb}) only concrete values will be used; with other analysis 
domains the domain abstract values inferred will also be used.
This feature is governed by the following flags:

@begin{itemize}
 @item @tt{abs_spec_defs} to exploit abstract substitutions in order to:

   @begin{itemize}
   @item @tt{rem} try to eliminate clauses which are incompatible with the
         inferred substitution at each unfolding step;
   @item @tt{exec} perform abstract executability of atoms;
   @item @tt{all} do both.
   @end{itemize}

 @item @tt{part_concrete} to try to convert abstract information into
   concrete information if possible, so that:

   @begin{itemize}
   @item @tt{mono} one concrete atom is obtained;
   @item @tt{multi} multiple atoms are allowed when the information in
         the abstract substitution is disjunctive. 
   @end{itemize}

 @item @tt{rem_use_cls} to identify clauses which are incompatible with
   the abstract call substitution and remove them:

   @begin{itemize}
   @item @tt{pre}  prior to performing any unfolding steps;
   @item @tt{post} after performing unfolding steps;
   @item @tt{both} both before and after performing unfolding steps.
   @end{itemize}

 @item @tt{filter_nums} to filter away during partial evaluation numbers which:

   @begin{itemize}
   @item @tt{safe} are not safe, i.e., do not appear in the original 
         program, or
   @item @tt{on} all numbers.
   @end{itemize}

@end{itemize}
").

% @subsection{Instrumenting the code for run-time assertion checking}
% @begin{itemize}
%  @item @tt{rtchecks} Transforms the program so that it will check the
%        predicate-level assertions at run-time.
% @end{itemize}
       
