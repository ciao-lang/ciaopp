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
:- use_module(library(streams)).
:- use_module(library(write)).

% ---------------------------------------------------------------------------

:- data dom_def/3.
:- data dom_base/3.
:- data dom_op/3.
:- data dom_itf/1.
% (experimental)
:- data dom_base_deriv/5.

clean_db_pass1(Mod) :-
    retractall_fact(dom_def(_,_,Mod)),
    retractall_fact(dom_base(_,_,Mod)),
    retractall_fact(dom_op(_,_,Mod)),
    retractall_fact(dom_itf(Mod)),
    retractall_fact(dom_base_deriv(_,_,_,_,Mod)).

% ---------------------------------------------------------------------------

:- export(treat_sent/3).
treat_sent(0, _, Mod) :- !,
    clean_db_pass1(Mod).
treat_sent(end_of_file, Cs2, Mod) :- !,
    emit_sents(Mod, Cs),
    clean_db_pass1(Mod),
    % TODO: This should be automatic
    append(Cs, [end_of_file], Cs2). % (allow other translations)
treat_sent((:- dom_def(AbsInt < BaseDom)), C2, M) :- !,
    assertz_fact(dom_def(AbsInt,BaseDom,M)), % TODO: basedom hardwired
    C2 = aidomain(AbsInt).
treat_sent((:- dom_def(AbsInt)), C2, M) :- !,
    assertz_fact(dom_def(AbsInt,basedom,M)), % TODO: basedom hardwired
    C2 = aidomain(AbsInt).
treat_sent((:- dom_itf), C2, M) :- !,
    C2 = [],
    assertz_fact(dom_itf(M)).
treat_sent((:- dom_base(Spec)), C2, M) :- nonvar(Spec), Spec = F/A, !,
    C2 = [],
    assertz_fact(dom_base(F,A,M)).
treat_sent((:- dom_base_deriv(BaseAbsInt, Spec, Props)), C2, M) :- nonvar(Spec), Spec = F/A, !,
    C2 = [],
    assertz_fact(dom_base_deriv(BaseAbsInt,F,A,Props,M)).
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
% TODO: (experimental, merge)
% I.e., <<Trait>>_Op(<<AbsInt>, As) :- !, <<AbsInt>>_Op(As).
treat_sent((:- dom_impl(QAbsInt,Spec)), C2, _M) :- nonvar(QAbsInt), QAbsInt = as(AbsInt,Trait), nonvar(Spec), Spec = _/_, !,
    Spec = OpName/A,
    functor(Op, OpName, A),
    Op =.. [_|As],
    atom_concat(Trait,'_',Traitb), atom_concat(Traitb,OpName,TraitOpName),
    atom_concat(AbsInt,'_',AbsIntb), atom_concat(AbsIntb,OpName,AbsIntOpName),
    H =.. [TraitOpName, AbsInt|As],
    B =.. [AbsIntOpName|As],
    C2 = [(H :- !, B)].
    %writeq(C2), nl.
treat_sent((:- dom_impl(AbsInt,Spec)), C2, M) :- nonvar(Spec), Spec = _/_, !,
    emit_dom_impl(AbsInt,Spec,[noself],M,C2).
treat_sent((:- dom_impl(AbsInt,Spec,from(MAbsIntB))), C2, M) :- nonvar(Spec), nonvar(MAbsIntB), Spec = _/_, !,
    ( MAbsIntB = MB:AbsIntB -> % different module name
        true
    ; % same module name
      MB = MAbsIntB, AbsIntB = MAbsIntB
    ),
    emit_dom_impl(AbsInt,Spec,[noself,from(MB,AbsIntB)],M,C2).

emit_sents(Mod,Cs) :- % TODO: complete; add only if not defined!!
    % Add default definitions
    findall(b(Impl,BaseDom), dom_def(Impl, BaseDom, Mod), Impls),
    emit_base_hooks_all(Impls, Mod, Cs, Cs1),
    ( dom_itf(Mod) ->
        % Add itf methods (non-multifile wrappers for multifile)
        findall(m(F/A), dom_op(F, A, Mod), Meths),
        emit_imeths(Meths, Cs1, [])
    ; Cs1 = []
    ).

emit_base_hooks_all([],_M,Cs,Cs).
emit_base_hooks_all([b(Impl,BaseDom)|Impls],M,Cs,Cs0) :-
    emit_base_hooks(Impl,BaseDom,M,Cs,Cs1),
    emit_base_hooks_all(Impls,M,Cs1,Cs0).

emit_base_hooks(Impl,BaseDom0,M,Cs,Cs0) :-
    ( BaseDom0 = basedom ->
        Meths0 = []
    ; findall(m(OpName/A,[from(M,BaseDom0)|Props]),
              dom_base_deriv(BaseDom0, OpName, A, Props, M),
              Meths0)
    ),
    emit_meths(Meths0,Impl,M,Cs,Cs1),
    BaseDom = basedom, % TODO: hardwired
    findall(Meth, base_meth(BaseDom, M, Meth), Meths),
    emit_meths(Meths,Impl,M,Cs1,Cs0).

% hooks for the given Impl and BaseDom at module M
% TODO: implement more compositions?
base_meth(BaseDom, M, Meth) :-
    dom_base(F,A,M),
    Meth = m(F/A,[from(M,BaseDom)]).

emit_meths([],_Impl,_M,Cs,Cs).
emit_meths([m(Spec,Props)|Meths],Impl,M,Cs,Cs0) :-
    emit_dom_impl(Impl,Spec,Props,M,C),
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

emit_dom_impl(AbsInt,Spec,Props,M,C2) :-
    ( member(from(MB,AbsIntB), Props) -> true
    ; MB = M, AbsIntB = AbsInt
    ),
    % AbsInt implements operation Spec
    Spec = OpName/A,
    functor(Op, OpName, A),
    Op =.. [_|As],
    atom_concat('_', OpName, ImplN0),
    atom_concat(AbsIntB, ImplN0, ImplN),
    ( member(noself, Props) -> % (do not pass AbsInt)
        B =.. [ImplN|As]
    ; B =.. [ImplN,AbsInt|As] % (pass AbsInt)
    ),
    mprefix(OpName, OpNameM),
    H =.. [OpNameM,AbsInt|As],
    C2 = (H :- !, MB:B).

% err(wrong_impl(C)) :-
%       message(error, ['Wrong dom_impl: ', ~~(C)]),
%       fail.
