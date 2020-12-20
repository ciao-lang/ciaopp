:- module(nfbool, [
    bool_normalize/2,
    push_conj/2,
    push_neg_in_test/2,
    put_negation/3,
    remove_negation/2,
    translate_test/2,
    wff2list/2
], [assertions]).

% Local module required by PLAI-based and NFGRAPH-based analyses
:- doc(title, "Boolean formula manipulation").
:- doc(author, "Pedro L@'{o}pez").

:- doc(bug, "neg_test/2 contains a builtin table, synchronization needed").
:- doc(bug, "translate_test/2 contains a builtin table, synchronization needed").

:- use_module(library(idlists), [member_0/2]).
:- use_module(library(messages)).

% ===========================================================================
%! # p_bool

%% Added by PL.

% bool_normalize(+F0, -F1) takes a Boolean formula F0 and transforms it to
% an equivalent formula F1 that is a disjunction of conjunctions.

bool_normalize(Fin, Fout) :-
    b_push_negation(Fin, F0),
    push_conj(F0, Fout).

% b_push_negation pushes negations inwards using De Morgan's rules.

b_push_negation(not(','(F1, F2)), ';'(G1, G2)) :- !,
    b_push_negation(not(F1), G1),
    b_push_negation(not(F2), G2).
b_push_negation(not(';'(F1, F2)), ','(G1, G2)) :- !,
    b_push_negation(not(F1), G1),
    b_push_negation(not(F2), G2).
b_push_negation(not(not(F)), G) :- !,
    b_push_negation(F, G).
b_push_negation(','(F1, F2), ','(G1, G2)) :- !,
    b_push_negation(F1, G1),
    b_push_negation(F2, G2).
b_push_negation(';'(F1, F2), ';'(G1, G2)) :- !,
    b_push_negation(F1, G1),
    b_push_negation(F2, G2).
b_push_negation(X, X).

push_neg_in_test(X, _Y) :-
    var(X),
    !,
    send_signal(wrong_neg_test(X)),
    fail.
%       message(warning, ['Test is an unexpected free variable']).
push_neg_in_test(\+(\+(X)), Y) :- !, push_neg_in_test(X, Y).
push_neg_in_test(\+(X),     Y) :- !, neg_test(X, Y).
push_neg_in_test(X,         Y) :- translate_test(X, Y).

%% neg_test(true, false). % These are not tests.
%% neg_test(fail, true).
%% neg_test(false, true).
neg_test(=(X,                   Y), '$noteq$'(X, Y)).
neg_test('term_compare:=='(X,   Y), '$noteq$'(X, Y)).
neg_test('term_compare:\\=='(X, Y), =(X,         Y)).
neg_test('term_compare:\\='(X, Y),  =(X,         Y)).
neg_test(is(X,                  Y), =\=(X,       Y)).
neg_test('arithmetic:=\\='(X,   Y), =:=(X,       Y)).
neg_test('arithmetic:=:='(X,    Y), =\=(X,       Y)).
neg_test('arithmetic:<'(X,      Y), >=(X,        Y)).
neg_test('arithmetic:>'(X,      Y), =<(X,        Y)).
neg_test('arithmetic:=<'(X,     Y), >(X,         Y)).
neg_test('arithmetic:>='(X,     Y), <(X,         Y)).
% For Sicstus
neg_test('term_typing:atom'(X),    '$notatom$'(X)).
neg_test('term_typing:integer'(X), '$notinteger$'(X)).
neg_test('term_typing:number'(X),  '$notnumber$'(X)).
% For CIAO
neg_test('basic_props:atm'(X), '$notatom$'(X)).
neg_test('basic_props:int'(X), '$notinteger$'(X)).
neg_test('basic_props:num'(X), '$notnumber$'(X)).
% Negated tests (common for Sicstus and CIAO).
neg_test('$noteq$'(X, Y),   =(X, Y)).
neg_test('$notinteger$'(X), integer(X)).
neg_test('$notnumber$'(X),  number(X)).
neg_test('$notatom$'(X),    atom(X)).

translate_test(=(X, Y),      =(X, Y)) :- !.
translate_test('\\=='(X, Y), '$noteq$'(X, Y)) :- !.
translate_test('\\='(X, Y),  '$noteq$'(X, Y)) :- !.
translate_test('=='(X, Y),   =(X, Y)) :- !.
translate_test(is(X, Y),     =:=(X, Y)) :- !.
translate_test('=\\='(X, Y), =\=(X, Y)) :- !.
translate_test('=:='(X, Y),  =:=(X, Y)) :- !.
translate_test(<(X, Y),      <(X, Y)) :- !.
translate_test(>(X, Y),      >(X, Y)) :- !.
translate_test(=<(X, Y),     =<(X, Y)) :- !.
translate_test(>=(X, Y),     >=(X, Y)) :- !.
translate_test('arithmetic:arithexpression'(X), arithexpression(X)) :- !.
% For Sicstus
translate_test('term_typing:integer'(X), integer(X)) :- !.
translate_test('term_typing:number'(X),  number(X)) :- !.
translate_test('term_typing:atom'(X),    atom(X)) :- !.
% For CIAO
translate_test('basic_props:int'(X),    integer(X)) :- !.
translate_test('basic_props:num'(X),    number(X)) :- !.
translate_test('basic_props:atm'(X),    atom(X)) :- !.
translate_test('term_typing:atomic'(X), atomic(X)) :- !.
translate_test('basic_props:gnd'(X),    ground(X)) :- !.
% Negated tests (common for Sicstus and CIAO).
translate_test('$noteq$'(X, Y),   '$noteq$'(X, Y)) :- !.
translate_test('$notnumber$'(X),  '$notnumber$'(X)) :- !.
translate_test('$notinteger$'(X), '$notinteger$'(X)) :- !.
translate_test('$notatom$'(X),    '$notatom$'(X)) :- !.
translate_test(A,                 A) :-
    warning_message("No translation rule for ~w", [A]).

%% End of added by PL.

% 6 jul 99

remove_negation(\+(\+(X)), Y) :- !,
    remove_negation(X, Y).
remove_negation(\+('$'(Lit, _, _)), Lit) :- !.
remove_negation(\+(X), X) :- !.
remove_negation(X, X).

put_negation(\+(\+(X)), Literal, \+(\+(Test))) :- !,
    put_negation(X, Literal, Test).
put_negation(\+(_X), Literal, \+(Literal)) :- !.
put_negation(_X, Literal, Literal).

% ===========================================================================
%! # s_bool

%% *********************************************************************
%% *                                                                   *
%% *  File:    bool.pl                                                 *
%% *  Purpose: Manipulation of Boolean formulae                        *
%% *  Author:  Saumya Debray                                           *
%% *  Date:    4 Aug 1995                                              *
%% *                                                                   *
%% *  Notes:   I've chosen simplicity of code over efficiency here,    *
%% *    and if performance becomes an issue this would be a good place *
%% *    to look for improvements.                                      *
%% *                                                                   *
%% *********************************************************************

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                 %%
%%  DATA REPRESENTATION: Conjunction is represented by ','/2,      %%
%%    disjunction by ';'/2, negation by not/1.                     %%
%%                                                                 %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% normalize(+F0, -F1) takes a Boolean formula F0 and transforms it to
% an equivalent formula F1 that is a disjunction of conjunctions.

%% normalize(Fin, Fout) :-
%%      push_negation(Fin, F0),
%%      push_conj(F0, Fout).
%% 
%% % push_negation pushes negations inwards using De Morgan's rules.
%% 
%% push_negation(not(','(F1, F2)), ';'(G1, G2)) :-
%%      !,
%%      push_negation(not(F1), G1),
%%      push_negation(not(F2), G2).
%% push_negation(not(';'(F1, F2)), ','(G1, G2)) :-
%%      !,
%%      push_negation(not(F1), G1),
%%      push_negation(not(F2), G2).
%% push_negation(not(not(F)), G) :-
%%      !,
%%      push_negation(F, G).
%% push_negation(','(F1, F2), ','(G1, G2)) :-
%%      !,
%%      push_negation(F1, G1),
%%      push_negation(F2, G2).
%% push_negation(';'(F1, F2), ';'(G1, G2)) :-
%%      !,
%%      push_negation(F1, G1),
%%      push_negation(F2, G2).
%% push_negation(not('='(T1, T2)),       '$noteq$'(T1, T2)) :- !.
%% push_negation(not('$noteq$'(T1, T2)), '='(T1, T2)) :- !.
%% push_negation(X,                      X).

% push_conj repeatedly pushes (i.e., distributes) conjunctions into
% disjunctions. It assumes that negations have already been pushed
% in as far as possible.

push_conj(F, G) :-
    push_conj_3(F, H, Flag),
    ( nonvar(Flag) ->
        push_conj(H, G)
    ; G = H
    ).

push_conj_3((P, (Q;R)), (A1;A2), y) :- !,
    push_conj_3((P, Q), A1, _),
    push_conj_3((P, R), A2, _).
push_conj_3(((Q;R), P), (A1;A2), y) :- !,
    push_conj_3((Q, P), A1, _),
    push_conj_3((R, P), A2, _).
push_conj_3((P, Q), (A1, A2), Flag) :- !,
    push_conj_3(P, A1, Flag),
    push_conj_3(Q, A2, Flag).
push_conj_3((P;Q), (A1;A2), Flag) :- !,
    push_conj_3(P, A1, Flag),
    push_conj_3(Q, A2, Flag).
push_conj_3(G, G, _).

% wff2list(+Fmla, -Lst) takes a formula that is a disjunction of
% conjunctions, and transforms this to a list of lists Lst, where
% each element of the top-level list Lst is a list that represents
% a disjunct whose elements represent conjuncts.

wff2list(F, L) :- disj2list(F, L, []).

disj2list(';'(A1, A2), Hd, Tl) :- !,
    disj2list(A1, Hd,  Mid),
    disj2list(A2, Mid, Tl).
disj2list(A, [CList|Tl], Tl) :-
    conj2list(A, CList0, []),
    rem_dups(CList0, [true], CList).

conj2list(','(A1, A2), Hd, Tl) :- !,
    conj2list(A1, Hd,  Mid),
    conj2list(A2, Mid, Tl).
conj2list(A, [A|Tl], Tl).

% rem_dups(+Lin, +Seen, -Lout) removes duplicate elements from the list
% Lin to produce the list Lout.  Seen is a list of elements that have
% been encountered already.

rem_dups([X|L], Seen, Lout) :-
    ( member_0(X, Seen) ->
        rem_dups(L, Seen, Lout)
    ; Lout = [X|Lout1],
      rem_dups(L, [X|Seen], Lout1)
    ).
rem_dups([], _, []).

