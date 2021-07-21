:- module(ptypes,[],[assertions,regtypes,basicmodes]).

:- doc(title, "ptypes: types with topological class widening (abstract domain)").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").
:- doc(author, "Ciao Development Team").

:- doc(module,"This module implements a types domain (based on
   @tt{termsd.pl}) using the topological clash widening operator
   (@pred{hentenwid/3}).").

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
:- use_module(domain(termsd)).
:- use_module(typeslib(typeslib), [hentenwid/3]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(ptypes, [default]).

:- dom_impl(_, init_abstract_domain/1, [from(termsd:terms)]).
:- dom_impl(_, call_to_entry/9, [from(termsd:terms)]).
:- dom_impl(_, exit_to_prime/7, [from(termsd:terms)]).
:- dom_impl(_, compute_lub/2, [from(termsd:terms)]).
:- dom_impl(_, identical_abstract/2, [from(termsd:terms)]).
:- dom_impl(_, abs_sort/2, [from(termsd:terms)]).
:- dom_impl(_, extend/5, [from(termsd:terms)]).
:- dom_impl(_, project/5, [from(termsd:terms)]).
:- dom_impl(_, less_or_equal/2, [from(termsd:terms)]).
:- dom_impl(_, glb/3, [from(termsd:terms)]).
:- dom_impl(_, call_to_success_fact/9, [from(termsd:terms)]).
:- dom_impl(_, special_builtin/5, [from(termsd:terms)]).
:- dom_impl(_, success_builtin/6, [from(termsd:terms)]).
:- dom_impl(_, call_to_success_builtin/6, [from(termsd:terms)]).
:- dom_impl(_, input_interface/4, [from(termsd:terms)]).
:- dom_impl(_, input_user_interface/5, [from(termsd:terms)]).
:- dom_impl(_, asub_to_native/5, [from(termsd:terms)]).
:- dom_impl(_, concrete/3, [from(termsd:terms)]).
:- dom_impl(_, unknown_call/4, [from(termsd:terms)]).
:- dom_impl(_, unknown_entry/3, [from(termsd:terms)]).
:- dom_impl(_, empty_entry/3, [from(termsd:terms)]).
:- dom_impl(_, collect_auxinfo_asub/3, [from(termsd:terms)]).
:- dom_impl(_, rename_auxinfo_asub/3, [from(termsd:terms)]).
:- dom_impl(_, needs/1, [from(termsd:terms)]).

:- dom_impl(_, widencall/3, [noq]).
widencall(Prime0,Prime1,Result):-
%    widen(Prime0,Prime1,Result). % TODO: termsd.pl uses this; which is better?
    ( terms_less_or_equal(Prime1,Prime0) ->
        Result = Prime0
    ; terms_compute_lub_el(Prime0,Prime1,Prime),
      henten(Prime0,Prime,Prime2),
      ( terms_identical_abstract(Prime2,Prime) ->
          Result = Prime1
      ; Result = Prime2
      )
    ).

:- dom_impl(_, widen/3, [noq]).
widen(Prime0,Prime1,NewPrime):-
    terms_compute_lub_el(Prime0,Prime1,Prime),
    henten(Prime0,Prime,NewPrime).

henten('$bottom','$bottom','$bottom') :- !.
henten('$bottom',Prime,Prime).
henten([],[],[]).
henten([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
    hentenwid(T1,T2,T),
    henten(Prime0,Prime,NewPrime).
