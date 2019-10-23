:- module(aidomain_tr, [], [assertions, isomodes]).

:- doc(title,"AI domain helper (expansion module)").
:- doc(author, "Jose F. Morales").

:- doc(module, "Translation module for syntactic extensions to write
   AI domains.").

:- use_module(engine(messages_basic), [message/2]).
%:- use_module(library(write), [numbervars/3]).

:- export(dom_sent/3).
dom_sent((:- dom_def(AbsInt)), C2, _M) :- !,
        C2 = aidomain(AbsInt).
dom_sent((:- dom_op(AbsInt,Spec)), C2, _M) :- nonvar(Spec), Spec = _/_, !,
	emit_dom_op0(AbsInt,Spec,AbsInt, C2).
dom_sent((:- dom_op(AbsInt,Spec,from(AbsIntB))), C2, _M) :- nonvar(Spec), Spec = _/_, !,
	emit_dom_op0(AbsInt,Spec,AbsIntB, C2).

emit_dom_op0(AbsInt,Spec,AbsIntB, C2) :-
	% AbsInt implements operation Spec
	Spec = OpName/A,
	functor(Op, OpName, A),
	Op =.. [_|As],
	atom_concat('_', OpName, ImplN0),
	atom_concat(AbsIntB, ImplN0, ImplN),
	B =.. [ImplN|As],
	H =.. [OpName,AbsInt|As],
        C2 = (H :- !, B).

% err(wrong_op(C)) :-
% 	message(error, ['Wrong dom_op: ', ~~(C)]),
% 	fail.
