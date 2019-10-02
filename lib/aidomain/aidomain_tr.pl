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
dom_sent((:- dom_op(C)), C2, _M) :-
	% check_dom_op(C), % (enable to check op)
        C2 = C.

check_dom_op(C) :-
	nonvar(C),
	( C = (H :- !, B) -> true
	; err(wrong_op(C))
	),
	H =.. [Nh,AbsInt|As],
	B =.. [Nb|Bs],
	( atom(AbsInt),
	  atom_concat(AbsInt, Nb0, Nb),
	  atom_concat('_', OpName, Nb0) ->
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
	    )
	; message(user, [~~(bad_domname(AbsInt, Nb))])
	).

err(wrong_op(C)) :-
	message(error, ['Wrong dom_op: ', ~~(C)]),
	fail.
