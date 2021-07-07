:- module(aidomain_tr, [], [assertions, isomodes, datafacts]).

:- doc(title,"AI domain helper (expansion module)").
:- doc(author, "Jose F. Morales").

:- doc(module, "Translation module for syntactic extensions to write
   AI domains.").

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [append/3]).
%:- use_module(library(write), [numbervars/3]).

% (debug)
%:- use_module(library(streams)).
%:- use_module(library(write)).

% ---------------------------------------------------------------------------

:- data dom_def/2.
:- data dom_base/3.
:- data dom_op/3.
:- data dom_itf/1.

clean_db_pass1(Mod) :-
    retractall_fact(dom_def(_,Mod)),
    retractall_fact(dom_base(_,_,Mod)),
    retractall_fact(dom_op(_,_,Mod)),
    retractall_fact(dom_itf(Mod)).

% ---------------------------------------------------------------------------

:- export(treat_sent/3).
treat_sent(0, _, Mod) :- !,
    clean_db_pass1(Mod).
treat_sent(end_of_file, Cs2, Mod) :- !,
    emit_sents(Mod, Cs),
    clean_db_pass1(Mod),
    % TODO: This should be automatic
    append(Cs, [end_of_file], Cs2). % (allow other translations)
%treat_sent(X, _, _) :- X = (:- _),
%    display(x(X)), nl, fail.
treat_sent((:- dom_def(AbsInt)), C2, M) :- !,
    assertz_fact(dom_def(AbsInt,M)),
    C2 = aidomain(AbsInt).
treat_sent((:- dom_itf), C2, M) :- !,
    C2 = [],
    assertz_fact(dom_itf(M)).
treat_sent((:- dom_base(Spec)), C2, M) :- nonvar(Spec), Spec = F/A, !,
    C2 = [],
    assertz_fact(dom_base(F,A,M)).
treat_sent((:- dom_op(Spec)), Cs, M) :- nonvar(Spec), Spec = F/A, !,
    % Declare operation and define wrapper to multifile % TODO: C1 and C2
%       A1 is A+1,
%       mprefix(F, Fm),
%       functor(Hm,Fm,A1),
%       Hm =.. [_|Xs],
%       H =.. [F|Xs],
%       C1 = (H :- Hm),
%       Cs = [C1, (:- discontiguous(Fm/A1)), (:- multifile(Fm/A1))].
    assertz_fact(dom_op(F,A,M)),
    A1 is A+1,
    mprefix(F, Fm),
    Cs = [(:- discontiguous(Fm/A1)), (:- multifile(Fm/A1))].
treat_sent((:- dom_impl(AbsInt,Spec)), C2, M) :- nonvar(Spec), Spec = _/_, !,
    emit_dom_impl0(AbsInt,Spec,AbsInt,M,C2).
treat_sent((:- dom_impl(AbsInt,Spec,from(MAbsIntB))), C2, _M) :- nonvar(Spec), nonvar(MAbsIntB), Spec = _/_, !,
    ( MAbsIntB = MB:AbsIntB -> % different module name
        true
    ; % same module name
      MB = MAbsIntB, AbsIntB = MAbsIntB
    ),
    emit_dom_impl0(AbsInt,Spec,AbsIntB,MB,C2).
% TODO: (experimental)
% I.e., <<Trait>>_Op1(<<AbsInt2>, As1) :- !, <<AbsInt2>>_Op2(As2).
treat_sent((:- dom_deriv_hook(as(AbsInt,Trait),Spec)), C2, _M) :- nonvar(Spec), Spec = _/_, !,
    Spec = OpName/A,
    functor(Op, OpName, A),
    Op =.. [_|As],
    atom_concat(Trait,'_',Traitb), atom_concat(Traitb,OpName,TraitOpName),
    atom_concat(AbsInt,'_',AbsIntb), atom_concat(AbsIntb,OpName,AbsIntOpName),
    H =.. [TraitOpName, AbsInt|As],
    B =.. [AbsIntOpName|As],
    C2 = [(H :- !, B)].
    %writeq(C2), nl.
% TODO: (experimental)
% I.e., :- dom_impl(AbsInt1, Op1F/Op1A).
%       <<AbsInt1>>_Op1(<<AbsInt2>, As1) :- !, <<AbsInt2>>_Op2(As2).
treat_sent((:- dom_impl_deriv(AbsInt1,Head1,AbsInt2,Head2)), C2, M) :- !,
    Head1 =.. [Op1|As1],
    Head2 =.. [Op2|As2],
    atom_concat(AbsInt1,'_',AbsInt1b), atom_concat(AbsInt1b,Op1,AbsIntOp1),
    atom_concat(AbsInt2,'_',AbsInt2b), atom_concat(AbsInt2b,Op2,AbsIntOp2),
    H =.. [AbsIntOp1|As1],
    B =.. [AbsIntOp2|As2],
    C2 = [(H :- !, B)|C3],
    %writeq(C2), nl,
    %
    functor(Head1,Op1F,Op1A),
    Spec = Op1F/Op1A,
    emit_dom_impl0(AbsInt1,Spec,AbsInt1,M,C3).

emit_sents(Mod,Cs) :- % TODO: complete
    % Add default definitions
    findall(Impl, dom_def(Impl, Mod), Impls),
    emit_base_hooks_all(Impls, Mod, Cs, Cs1),
    ( dom_itf(Mod) ->
        % Add itf methods (non-multifile wrappers for multifile)
        findall(m(F/A), dom_op(F, A, Mod), Meths),
        emit_imeths(Meths, Cs1, [])
    ; Cs1 = []
    ).

emit_base_hooks_all([],_M,Cs,Cs).
emit_base_hooks_all([Impl|Impls],M,Cs,Cs0) :-
    emit_base_hooks(Impl,M,Cs,Cs1),
    emit_base_hooks_all(Impls,M,Cs1,Cs0).

emit_base_hooks(Impl,M,Cs,Cs0) :-
    findall(m(F/A), dom_base(F,A,M), Meths),
    emit_meths(Meths,Impl,M,Cs,Cs0).

emit_meths([],_Impl,_M,Cs,Cs).
emit_meths([m(Spec)|Meths],Impl,M,Cs,Cs0) :-
    emit_dom_impl1(Impl,Spec,basedom,M,C), % TODO: basedom hardwired
    Cs = [C|Cs1],
    emit_meths(Meths,Impl,M,Cs1,Cs0).

emit_imeths([],Cs,Cs).
emit_imeths([m(F/A)|Meths],Cs,Cs0) :-
    % Wrappers to multifile preds
    A1 is A+1,
    mprefix(F, Fm),
    functor(Hm,Fm,A1),
    Hm =.. [_|Xs],
    H =.. [F|Xs],
    C1 = (H :- Hm),
    Cs = [C1|Cs1],
    emit_imeths(Meths,Cs1,Cs0).

mprefix(F, Fm) :-
    atom_concat('aidom.', F, Fm).

emit_dom_impl0(AbsInt,Spec,AbsIntB,M,C2) :-
    % AbsInt implements operation Spec
    Spec = OpName/A,
    functor(Op, OpName, A),
    Op =.. [_|As],
    atom_concat('_', OpName, ImplN0),
    atom_concat(AbsIntB, ImplN0, ImplN),
    B =.. [ImplN|As],
    mprefix(OpName, OpNameM),
    H =.. [OpNameM,AbsInt|As],
    C2 = (H :- !, M:B).

emit_dom_impl1(AbsInt,Spec,AbsIntB,M,C2) :-
    % AbsInt implements operation Spec (AbsInt still an arg) 
    Spec = OpName/A,
    functor(Op, OpName, A),
    Op =.. [_|As],
    atom_concat('_', OpName, ImplN0),
    atom_concat(AbsIntB, ImplN0, ImplN),
    B =.. [ImplN,AbsInt|As],
    mprefix(OpName, OpNameM),
    H =.. [OpNameM,AbsInt|As],
    C2 = (H :- !, M:B).

% err(wrong_impl(C)) :-
%       message(error, ['Wrong dom_impl: ', ~~(C)]),
%       fail.
