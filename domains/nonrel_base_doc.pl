:- module(_, [], [assertions,regtypes,basicmodes]).
:- doc(nodoc,assertions).
:- doc(nodoc,assertions_basic).
:- doc(nodoc,regtypes).

:- doc(filetype, package).

:- doc(title, "Base for Non Relational Domains").
:- doc(author, "Isabel Garcia-Contreras").
:- doc(author, "Jose F. Morales (minor)").

:- doc(stability, devel).

:- doc(module, "
   This source offers a base domain to implement @em{(non-relational)
   abstract domains}. To use this interface, you must implement the
   basic lattice operations marked explicitly as \"implement in
   derived domain\". The more complex operations of CiaoPP's standard
   interface between fixpoints and domains (e.g.,
   @pred{nonrel_call_to_entry/10} and the other exports of this
   module) are then derived automatically from these basic operations
   and exported.

   @begin{alert} 
   @bf{Warning}: when using the output predicates provided with
     CiaoPP, no analysis result will be shown if predicate
     @pred{nonrel_asub_to_native/6} does not translate to properties
     that CiaoPP can express natively. This is the case of the current
     implementation.

     However, analysis results can output in the @em{raw} format,
     which does not process analysis information. This can be done by
     setting the @tt{output_lang} flag.
@begin{verbatim}
?- set_pp_flag(output_lang, raw).
@end{verbatim}
   @end{alert}

   @begin{alert}
     @bf{Warning}: The domains that can take advantage of this module
     are required to be non-relational. This limitation may be lifted in
     the future.
   @end{alert}

   The predicates to be implemented are:
   @begin{itemize}
   @item @pred{nonrel_init_abstract_domain/2},
   @item @pred{nonrel_top/2},
   @item @pred{nonrel_bot/2}, 
   @item @pred{nonrel_var/2}, 
   @item @pred{nonrel_amgu/5},
   @item @pred{nonrel_less_or_equal_elem/3}, 
   @item @pred{nonrel_compute_glb_elem/4},
   @item @pred{nonrel_compute_lub_elem/4},
   @item @pred{nonrel_widen_elem/4}, and
   @item @pred{nonrel_special_builtin0/5},
      @pred{nonrel_call_to_success_builtin0/7} (give a special
      interpretation to some builtin operations, except predefined
      @pred{true/0}, @pred{=/2}, @pred{==/2}).
   @end{itemize}

   Optionally, the user may implement predicates related to the input
   and the output of analysis results. Predicates
   @pred{nonrel_input_interface/5} and
   @pred{nonrel_input_user_interface/4} are used to translate native
   properties, typically present in assertions, to abstract
   substitutions. Predicate @pred{nonrel_asub_to_native/6} translates
   abstract substitutions to properties that CiaoPP can express
   natively.
   @begin{alert}
     @bf{TODO}: Not yet available
   @end{alert}

   @begin{note}
     @bf{Tip}: When developing a new domain the raw output of the
     analyzer may come handy. This is set with
     @tt{set_pp_flag(output_lang, raw)}. With the default output
     options, CiaoPP will try to show the inferred properties in a nicer
     way. This has to be implemented by the user for each domain and may
     summarize the information without explicit notice.
   @end{note}
").

:- include(.(nonrel_base)).

:- impl_defined([nonrel_init_abstract_domain/2]).
:- impl_defined([nonrel_top/2]).
:- impl_defined([nonrel_bot/2]).
:- impl_defined([nonrel_var/2]).
:- impl_defined([nonrel_amgu/5]).
:- impl_defined([nonrel_less_or_equal_elem/3]).
:- impl_defined([nonrel_compute_glb_elem/4]).
:- impl_defined([nonrel_compute_lub_elem/4]).
:- impl_defined([nonrel_widen_elem/4]).
%:-impl_defined([nonrel_input_interface/5]).
:- impl_defined([nonrel_special_builtin0/5]).
:- impl_defined([nonrel_call_to_success_builtin0/7]).
