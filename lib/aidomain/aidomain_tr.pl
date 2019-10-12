:- module(aidomain_tr, [], [assertions, isomodes]).

:- doc(title,"AI domain helper (expansion module)").
:- doc(author, "Jose F. Morales").

:- doc(module, "Translation module for syntactic extensions to write
   AI domains.").

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(write), [numbervars/3]).

:- export(dom_sent/3).
dom_sent((:- dom_def(AbsInt)), C2, _M) :- !,
        C2 = aidomain(AbsInt).
dom_sent((:- dom_op(AbsInt,Spec)), C2, _M) :- nonvar(Spec), Spec = _/_, !,
	emit_dom_op0(AbsInt,Spec,AbsInt, C2).
dom_sent((:- dom_op(AbsInt,Spec,from(AbsIntB))), C2, _M) :- nonvar(Spec), Spec = _/_, !,
	emit_dom_op0(AbsInt,Spec,AbsIntB, C2).
dom_sent((:- dom_op(AbsInt,H,B1,from(AbsIntB))), C2, _M) :- !,
	emit_dom_op(AbsInt,H,B1,AbsIntB, C2).
dom_sent((:- dom_op(AbsInt,H,B1)), C2, _M) :-
	emit_dom_op(AbsInt,H,B1,AbsInt, C2).

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

emit_dom_op(AbsInt,H,B1,AbsIntB, C2) :-
	H =.. [Nh|As],
	B1 =.. [OpName|Bs],
	atom_concat('_', OpName, ImplN0),
	atom_concat(AbsIntB, ImplN0, ImplN),
	B =.. [ImplN|Bs],
	B2 = B,
%	check_dom_op(Nh,AbsInt,As,B1), % (enable to check op)
	H2 =.. [Nh,AbsInt|As],
        C2 = (H2 :- !, B2).

check_dom_op(Nh,AbsInt,As,B1) :-
	B1 =.. [OpName|Bs],
	( OpName == Nh ->
	    ( As == Bs -> true
	    ; ( numbervars(As,0,N0),
		numbervars(Bs,N0,_),
		message(user, [~~(bad_args(AbsInt, OpName, As, Bs))]),
		fail
	      ; true
	      )
	    )
	; message(user, [~~(bad_opname(AbsInt, Nh, OpName))])
	).

err(wrong_op(C)) :-
	message(error, ['Wrong dom_op: ', ~~(C)]),
	fail.
