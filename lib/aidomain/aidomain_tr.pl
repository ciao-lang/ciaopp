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
dom_sent((:- dom_op(AbsInt,Spec)), C2, _M) :- !,
	% AbsInt implements operation Spec
	Spec = N/A,
	functor(Op, N, A),
	Op =.. [_|As],
	atom_concat('_', N, ImplN0),
	atom_concat(AbsInt, ImplN0, ImplN),
	B =.. [ImplN|As],
	H =.. [N,AbsInt|As],
        C2 = (H :- !, B).
dom_sent((:- dom_op(AbsInt,H,B0)), C2, _M) :-
	H =.. [Nh|As],
	( B0 = from(AbsIntB,B1) ->
	    B1 =.. [Nb0|Bs],
	    atom_concat('_', Nb0, Nb1),
	    atom_concat(AbsIntB, Nb1, Nb),
	    B =.. [Nb|Bs]
	; B0 = ok(B1) ->
	    B1 =.. [Nb0|Bs],
	    atom_concat('_', Nb0, Nb1),
	    atom_concat(AbsInt, Nb1, Nb),
	    B =.. [Nb|Bs]
	; B = B0
	),
	B2 = B,
	% check_dom_op(Nh,AbsInt,As,B), % (enable to check op)
	H2 =.. [Nh,AbsInt|As],
        C2 = (H2 :- !, B2).

check_dom_op(Nh,AbsInt,As,B) :-
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
