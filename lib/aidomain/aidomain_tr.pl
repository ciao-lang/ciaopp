:- module(aidomain_tr, [], [assertions, isomodes, datafacts]).

:- doc(title,"AI domain helper (expansion module)").
:- doc(author, "Jose F. Morales").

:- doc(module, "Translation module for syntactic extensions to write
   AI domains.").

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [append/3]).
%:- use_module(library(write), [numbervars/3]).

% ---------------------------------------------------------------------------

:- data dom_def/2.
:- data dom_base/3.

clean_db_pass1(Mod) :-
	retractall_fact(dom_def(_,Mod)),
	retractall_fact(dom_base(_,_,Mod)).

% ---------------------------------------------------------------------------

:- export(treat_sent/3).
treat_sent(0, _, Mod) :- !,
	clean_db_pass1(Mod).
treat_sent(end_of_file, Cs2, Mod) :- !,
	emit_sents(Mod, Cs),
	clean_db_pass1(Mod),
	% TODO: This should be automatic
	append(Cs, [end_of_file], Cs2). % (allow other translations)
treat_sent((:- dom_def(AbsInt)), C2, M) :- !,
	assertz_fact(dom_def(AbsInt,M)),
        C2 = aidomain(AbsInt).
treat_sent((:- dom_base(Spec)), C2, M) :- nonvar(Spec), Spec = F/A, !,
	C2 = [],
	assertz_fact(dom_base(F,A,M)).
treat_sent((:- dom_op(Spec)), C2, _M) :- nonvar(Spec), Spec = F/A, !,
	A1 is A+1,
	C2 = [(:- discontiguous(F/A1))].
treat_sent((:- dom_impl(AbsInt,Spec)), C2, _M) :- nonvar(Spec), Spec = _/_, !,
	emit_dom_impl0(AbsInt,Spec,AbsInt, C2).
treat_sent((:- dom_impl(AbsInt,Spec,from(AbsIntB))), C2, _M) :- nonvar(Spec), Spec = _/_, !,
	emit_dom_impl0(AbsInt,Spec,AbsIntB, C2).

emit_sents(Mod,Cs) :- % TODO: complete
	findall(Impl, dom_def(Impl, Mod), Impls),
	emit_base_hooks_all(Impls, Mod, Cs, []).

emit_base_hooks_all([],_M,Cs,Cs).
emit_base_hooks_all([Impl|Impls],M,Cs,Cs0) :-
	emit_base_hooks(Impl,M,Cs,Cs1),
	emit_base_hooks_all(Impls,M,Cs1,Cs0).

emit_base_hooks(Impl,M,Cs,Cs0) :-
	findall(m(F/A), dom_base(F,A,M), Meths),
	emit_meths(Meths,Impl,Cs,Cs0).

emit_meths([],_Impl,Cs,Cs).
emit_meths([m(Spec)|Meths],Impl,Cs,Cs0) :-
	emit_dom_impl1(Impl,Spec,basedom,C), % TODO: basedom hardwired
	Cs = [C|Cs1],
	emit_meths(Meths,Impl,Cs1,Cs0).

emit_dom_impl0(AbsInt,Spec,AbsIntB, C2) :-
	% AbsInt implements operation Spec
	Spec = OpName/A,
	functor(Op, OpName, A),
	Op =.. [_|As],
	atom_concat('_', OpName, ImplN0),
	atom_concat(AbsIntB, ImplN0, ImplN),
	B =.. [ImplN|As],
	H =.. [OpName,AbsInt|As],
        C2 = (H :- !, B).

emit_dom_impl1(AbsInt,Spec,AbsIntB, C2) :-
	% AbsInt implements operation Spec (AbsInt still an arg) 
	Spec = OpName/A,
	functor(Op, OpName, A),
	Op =.. [_|As],
	atom_concat('_', OpName, ImplN0),
	atom_concat(AbsIntB, ImplN0, ImplN),
	B =.. [ImplN,AbsInt|As],
	H =.. [OpName,AbsInt|As],
        C2 = (H :- !, B).

% err(wrong_impl(C)) :-
% 	message(error, ['Wrong dom_impl: ', ~~(C)]),
% 	fail.
