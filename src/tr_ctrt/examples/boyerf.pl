:- module(_, [main/0, tautology/1],  [assertions, regtypes]).

% A toy theorem prover based on Lisp by R. Boyer (nqthm system)
% (originally translated by E. Tick in November 12 1985).
%
% This version includes assertions, relevant regular types, and fixes
% some errors in the translation from Lisp. This code contains several
% versions of a key predicate that is difficult to analyze (see
% below).
%
% Some regtypes are large. This is a problem for eterms. Use the
% `transform(ctrt)` pass to check assertions in this code.
%
% -- Natalia Stulova, Jose Morales (May 2016)
%

% ---------------------------------------------------------------------------
% Selection of rewrite/3 implementation

%:- compilation_fact(ver1).
:- compilation_fact(ver1b).
%:- compilation_fact(ver1c).
%:- compilation_fact(ver2).
%:- compilation_fact(ver3).

% ---------------------------------------------------------------------------

%:- entry benchmark(Data, X) : term * term.

%:- include(common).
%benchmark_data(boyer, 10, 0).
%benchmark(_Data, X) :-
main :-
    wff(X), tautology(X).

:- entry wff(X) : term(X).
%:- pred wff/1 => formula.
:- pred wff/1 : term => formula.

wff(implies(and(implies(X,Y),
    and(implies(Y,Z),
        and(implies(Z,U),
        implies(U,W)))),
    implies(X,W))) :-
    X = f(plus(plus(a,b),plus(c,zero))),
    Y = f(times(times(a,b),plus(c,d))),
    Z = f(reverse(append(append(a,b),[]))),
    U = equal(plus(a,b),difference(x,y)),
    W = lessp(remainder(a,b),member(a,length(b))).

:- entry tautology(X) : formula(X).
:- pred tautology/1: formula => formula.

tautology(Wff) :-
    % display('rewriting...'),nl,
    rewrite(Wff,NewWff),
    % display('proving...'),nl,
    tautology_2(NewWff,[],[]).

:- pred tautology_2/3 : formula * list * list
                 => formula * list * list.

% M.H. Implications changed to ! for right now: incorrect under Quintus!!!

% TODO:{fix} CiaoPP reader problems
%% tautology_2(Wff,Tlist,Flist) :-
%%      ( truep(Wff,Tlist) -> true
%%      ; falsep(Wff,Flist) -> fail
%%      ; Wff = if(If,Then,Else) ->
%%          ( truep(If,Tlist) -> tautology_2(Then,Tlist,Flist)
%%          ; falsep(If,Flist) -> tautology_2(Else,Tlist,Flist)
%%          ; tautology_2(Then,[If|Tlist],Flist), % both must hold
%%            tautology_2(Else,Tlist,[If|Flist])
%%          )
%%      ),
%%      !.

tautology_2(Wff,Tlist,_Flist) :-
    truep(Wff,Tlist), !, true.
tautology_2(Wff,_Tlist,Flist) :-
    falsep(Wff,Flist), !, fail.
tautology_2(Wff,Tlist,Flist) :-
    Wff = if(If,Then,Else),
    tautology_3(If,Then,Else,Tlist,Flist).

tautology_3(If,Then,_Else,Tlist,Flist) :-
    truep(If,Tlist), !, tautology_2(Then,Tlist,Flist).
tautology_3(If,_Then,Else,Tlist,Flist) :-
    falsep(If,Flist), !, tautology_2(Else,Tlist,Flist).
tautology_3(If,Then,Else,Tlist,Flist) :-
    tautology_2(Then,[If|Tlist],Flist), % both must hold
    tautology_2(Else,Tlist,[If|Flist]).

% ---------------------------------------------------------------------------
% Rewrite formula -- version 1
%
% Generic rewrite based functor/3 and arg/3
% 
% NOTE: This version loses precision quickly. It cannot prove
%   that rrr/4+rewrite_args/3 produces a formula in Mid.

:- if(defined(ver1)).
:- pred rewrite/2 : formula * var => formula * formula.

rewrite(Atom,Atom) :-
    atomic(Atom),!.
rewrite(Old,New) :-
    rrr(Old, Mid, _F, N),
    rewrite_args(N,Old,Mid),
    ( equal(Mid,Next), % should be ->, but is compiler smart enough?
      rewrite(Next,New) % to generate cut for ->?
    ; New=Mid
    ),!.

rrr(Old, Mid, F, N) :-
    functor(Old,F,N),
    functor(Mid,F,N).

rewrite_args(0,_,_) :- !.
rewrite_args(N,Old,Mid) :-
    arg(N,Old,OldArg),
    arg(N,Mid,MidArg),
    rewrite(OldArg,MidArg),
    N1 is N-1,
    rewrite_args(N1,Old,Mid).
:- endif.

% ---------------------------------------------------------------------------
% Rewrite formula -- version 1b
%
% rrr+rewrite_args moved in a predicate with its own assertion
% 
% NOTE: It still cannot prove that rrr/4+rewrite_args/3 produces a
%   formula in Mid, but using CTRT transformation helps with the rest
%   of the code.

:- if(defined(ver1b)).
:- pred rewrite/2 : formula * var => formula * formula.

rewrite(Atom,Atom) :-
    atomic(Atom),!.
rewrite(Old,New) :-
    rewrite1(Old, Mid),
    ( equal(Mid,Next), % should be ->, but is compiler smart enough?
      rewrite(Next,New) % to generate cut for ->?
    ; New=Mid
    ),!.

:- pred rewrite1/2 : formula * var => formula * formula.
rewrite1(Old, Mid) :-
    rrr(Old, Mid, _F, N),
    rewrite_args(N,Old,Mid).

rrr(Old, Mid, F, N) :-
    functor(Old,F,N),
    functor(Mid,F,N).

rewrite_args(0,_,_) :- !.
rewrite_args(N,Old,Mid) :-
    arg(N,Old,OldArg),
    arg(N,Mid,MidArg),
    rewrite(OldArg,MidArg),
    N1 is N-1,
    rewrite_args(N1,Old,Mid).
:- endif.

% ---------------------------------------------------------------------------
% Rewrite formula -- version 1c
%
% Variant of 1 that calls the formula type to gain precision (more
% costly at runtime) -- see formula/1 call after atomic/1 and
% rewrite_args/3 in rewrite/2. The worst case execution should not be
% affected (both formula/1 and rewrite_args/3 are O(size(term)))
%
% TODO: Analysis has the same problems than in version 2 and 3!
%   See boyerbug.pl for a reduced example.

:- if(defined(ver1c)).
:- pred rewrite/2 : formula * var => formula * formula.

rewrite(Atom,Atom) :-
    formula(Atom).
rewrite(_Old,New) :-
    formula(Mid),
    rewrite(Next,New).

%rewrite(Atom,Atom) :-
%    atomic(Atom),!,formula(Atom).
%rewrite(Old,New) :-
%%    rrr(Old, Mid, _F, N),
%%    rewrite_args(N,Old,Mid),
%    formula(Mid), % NOTE: force check to help the analysis
%    ( %equal(Mid,Next), % should be ->, but is compiler smart enough?
%      formula(Next), %K
%      rewrite(Next,New) % to generate cut for ->?
%    ; New=Mid
%    ),!.

rrr(Old, Mid, F, N) :-
    functor(Old,F,N),
    functor(Mid,F,N).

rewrite_args(0,_,_) :- !.
rewrite_args(N,Old,Mid) :-
    arg(N,Old,OldArg),
    arg(N,Mid,MidArg),
    rewrite(OldArg,MidArg),
    N1 is N-1,
    rewrite_args(N1,Old,Mid).
:- endif.

% ---------------------------------------------------------------------------
% Rewrite formula -- version 2
%
% This version enumerates all possible formula terms. The analysis
% obtains precise results.
%
% TODO:{fix} Complexity problem with eterms!
%
%   Needs 296 secs for eterms, output much more
%   with implies/2, and/2, or/2, iff/2, not/1, boolean/1
%   Finishes in a couple of seconds for implies/2, and/2, or/2, iff/2, not/1.

:- if(defined(ver2)).
:- pred rewrite/2 : formula * var => formula * formula.

rewrite(Atom,Atom) :-
    atomic_f(Atom),!.
rewrite(Old,New) :-
    rewrite_args(Old,Mid),
    ( equal(Mid,Next), % should be ->, but is compiler smart enough?
      rewrite(Next,New) % to generate cut for ->?
    ; New=Mid
    ),!.

:- pred rewrite_args/2 : formula * var => formula * formula.

rewrite_args(implies(X,Y), implies(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(and(X,Y), and(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(or(X,Y), or(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(if(X,Y,Z), if(X2,Y2,Z2)) :- rewrite(X,X2), rewrite(Y,Y2), rewrite(Z,Z2).
rewrite_args(iff(X,Y), iff(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(not(X), not(X2)) :- rewrite(X,X2).
rewrite_args(assignedp(X,Y), assignedp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(boolean(X), boolean(X2)) :- rewrite(X,X2).
rewrite_args(eqp(X,Y), eqp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(equal(X,Y), equal(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(greatereqp(X,Y), greatereqp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(lessp(X,Y), lessp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(lesseqp(X,Y), lesseqp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(listp(X), listp(X2)) :- rewrite(X,X2).
rewrite_args(numberp(X), numberp(X2)) :- rewrite(X,X2).
rewrite_args(nlistp(X), nlistp(X2)) :- rewrite(X,X2).
rewrite_args(tautologyp(X,Y), tautologyp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(zerop(X), zerop(X2)) :- rewrite(X,X2).
rewrite_args(f(X), f(X2)) :- rewrite(X,X2).
rewrite_args(assignment(X,Y), assignment(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(assume_false(X,Y), assume_false(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(assume_true(X,Y), assume_true(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(add1(X), add1(X2)) :- rewrite(X,X2).
rewrite_args(big_plus1(X,Y,Z), big_plus1(X2,Y2,Z2)) :- rewrite(X,X2), rewrite(Y,Y2), rewrite(Z,Z2).
rewrite_args(big_plus(W,X,Y,Z), big_plus(W2,X2,Y2,Z2)) :- rewrite(W,W2), rewrite(X,X2), rewrite(Y,Y2), rewrite(Z,Z2).
rewrite_args(difference(X,Y), difference(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(decr(X), decr(X2)) :- rewrite(X,X2).
rewrite_args(divides(X,Y), divides(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(gcd(X,Y), gcd(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(greatest_factor(X,Y), greatest_factor(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(exp(X,Y), exp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(even1(X), even1(X2)) :- rewrite(X,X2).
rewrite_args(fix(X), fix(X2)) :- rewrite(X,X2).
rewrite_args(odd(X), odd(X2)) :- rewrite(X,X2).
rewrite_args(plus(X,Y), plus(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(power_eval(X,Y), power_eval(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(power_rep(X,Y), power_rep(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(prime(X), prime(X2)) :- rewrite(X,X2).
rewrite_args(prime1(X,Y), prime1(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(prime_list(X), prime_list(X2)) :- rewrite(X,X2).
rewrite_args(quotient(X,Y), quotient(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(remainder(X,Y), remainder(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(samefringe(X,Y), samefringe(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(sigma(X,Y), sigma(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(times(X,Y), times(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(times_list(X), times_list(X2)) :- rewrite(X,X2).
rewrite_args(append(X,Y), append(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(car(X), car(X2)) :- rewrite(X,X2).
rewrite_args(cdr(X), cdr(X2)) :- rewrite(X,X2).
rewrite_args(cons(X,Y), cons(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(count_list(X,Y), count_list(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(dsort(X), dsort(X2)) :- rewrite(X,X2).
rewrite_args(delete(X,Y), delete(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(intersect(X,Y), intersect(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(flatten(X), flatten(X2)) :- rewrite(X,X2).
rewrite_args(length(X), length(X2)) :- rewrite(X,X2).
rewrite_args(last(X), last(X2)) :- rewrite(X,X2).
rewrite_args(mc_flatten(X), mc_flatten(X2)) :- rewrite(X,X2).
rewrite_args(meaning(X,Y), meaning(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(member(X,Y), member(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(nth(X,Y), nth(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(plus_tree(X), plus_tree(X2)) :- rewrite(X,X2).
rewrite_args(plus_fringe(X), plus_fringe(X2)) :- rewrite(X,X2).
rewrite_args(reverse(X), reverse(X2)) :- rewrite(X,X2).
rewrite_args(reverse_(X), reverse_(X2)) :- rewrite(X,X2).
rewrite_args(reverse_loop(X,Y), reverse_loop(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(sort2(X), sort2(X2)) :- rewrite(X,X2).
rewrite_args(sort_lp(X,Y), sort_lp(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(exec(X,Y,Z), exec(X2,Y2,Z2)) :- rewrite(X,X2), rewrite(Y,Y2), rewrite(Z,Z2).
rewrite_args(fact_(X), fact_(X2)) :- rewrite(X,X2).
rewrite_args(fact_loop(X,Y), fact_loop(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(falsify(X), falsify(X2)) :- rewrite(X,X2).
rewrite_args(falsify1(X,Y), falsify1(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(get(X,Y), get(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(gopher(X), gopher(X2)) :- rewrite(X,X2).
rewrite_args(compile(X), compile(X2)) :- rewrite(X,X2).
rewrite_args(codegen(X,Y), codegen(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(countps_(X,Y), countps_(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(countps_loop(X,Y,Z), countps_loop(X2,Y2,Z2)) :- rewrite(X,X2), rewrite(Y,Y2), rewrite(Z,Z2).
rewrite_args(optimize(X), optimize(X2)) :- rewrite(X,X2).
rewrite_args(tautology_checker(X), tautology_checker(X2)) :- rewrite(X,X2).
rewrite_args(set(X,Y,Z), set(X2,Y2,Z2)) :- rewrite(X,X2), rewrite(Y,Y2), rewrite(Z,Z2).
rewrite_args(value(X,Y), value(X2,Y2)) :- rewrite(X,X2), rewrite(Y,Y2).
rewrite_args(normalize(X), normalize(X2)) :- rewrite(X,X2).

:- pred atomic_f/1 : formula => formula.

atomic_f(1).
atomic_f(2).
atomic_f(6).
atomic_f(t).
atomic_f(f).
atomic_f(zero).
atomic_f([]).
atomic_f(a).
atomic_f(b).
atomic_f(c).
atomic_f(d).
atomic_f(x).
atomic_f(y).
:- endif.

% ---------------------------------------------------------------------------
% Rewrite formula -- version 3
%
% This is a variant of version 2 where the rewrite_args predicate is
% split into getargsN, rewrites, setargsN. No difference
% w.r.t. version 2.
%
% TODO:{fix} Complexity problem with eterms!

:- if(defined(ver3)).
:- pred rewrite/2 : formula * var => formula * formula.

rewrite(Atom,Atom) :-
    atomic_f(Atom),!.
rewrite(Old,New) :-
    rewrite_args(Old,Mid),
    ( equal(Mid,Next), % should be ->, but is compiler smart enough?
      rewrite(Next,New) % to generate cut for ->?
    ; New=Mid
    ),!.

:- pred rewrite_args/2 : formula * var => formula * formula.

rewrite_args(Old, New) :-
    getargs1(Old, X), !,
    rewrite(X, X2),
    setargs1(Old, X2, New).
rewrite_args(Old, New) :-
    getargs2(Old, X, Y), !,
    rewrite(X, X2),
    rewrite(Y, Y2),
    setargs2(Old, X2, Y2, New).
rewrite_args(Old, New) :-
    getargs3(Old, X, Y, Z), !,
    rewrite(X, X2),
    rewrite(Y, Y2),
    rewrite(Z, Z2),
    setargs3(Old, X2, Y2, Z2, New).
rewrite_args(Old, New) :-
    getargs4(Old, W, X, Y, Z), !,
    rewrite(W, W2),
    rewrite(X, X2),
    rewrite(Y, Y2),
    rewrite(Z, Z2),
    setargs4(Old, W2, X2, Y2, Z2, New).

getargs1(not(X), X).
getargs1(boolean(X), X).
getargs1(listp(X), X).
getargs1(numberp(X), X).
getargs1(nlistp(X), X).
getargs1(zerop(X), X).
getargs1(f(X), X).
getargs1(add1(X), X).
getargs1(decr(X), X).
getargs1(even1(X), X).
getargs1(fix(X), X).
getargs1(odd(X), X).
getargs1(prime(X), X).
getargs1(prime_list(X), X).
getargs1(times_list(X), X).
getargs1(car(X), X).
getargs1(cdr(X), X).
getargs1(dsort(X), X).
getargs1(flatten(X), X).
getargs1(length(X), X).
getargs1(last(X), X).
getargs1(mc_flatten(X), X).
getargs1(plus_tree(X), X).
getargs1(plus_fringe(X), X).
getargs1(reverse(X), X).
getargs1(reverse_(X), X).
getargs1(sort(X), X).
getargs1(fact_(X), X).
getargs1(falsify(X), X).
getargs1(gopher(X), X).
getargs1(compile(X), X).
getargs1(optimize(X), X).
getargs1(tautology_checker(X), X).
getargs1(normalize(X), X).

getargs2(implies(X,Y), X,Y).
getargs2(and(X,Y), X,Y).
getargs2(or(X,Y), X,Y).
getargs2(iff(X,Y), X,Y).
getargs2(assignedp(X,Y), X,Y).
getargs2(eqp(X,Y), X,Y).
getargs2(equal(X,Y), X,Y).
getargs2(greatereqp(X,Y), X,Y).
getargs2(lessp(X,Y), X,Y).
getargs2(lesseqp(X,Y), X,Y).
getargs2(tautologyp(X,Y), X,Y).
getargs2(assignment(X,Y), X,Y).
getargs2(assume_false(X,Y), X,Y).
getargs2(assume_true(X,Y), X,Y).
getargs2(difference(X,Y), X,Y).
getargs2(divides(X,Y), X,Y).
getargs2(gcd(X,Y), X,Y).
getargs2(greatest_factor(X,Y), X,Y).
getargs2(exp(X,Y), X,Y).
getargs2(plus(X,Y), X,Y).
getargs2(power_eval(X,Y), X,Y).
getargs2(power_rep(X,Y), X,Y).
getargs2(prime1(X,Y), X,Y).
getargs2(quotient(X,Y), X,Y).
getargs2(remainder(X,Y), X,Y).
getargs2(samefringe(X,Y), X,Y).
getargs2(sigma(X,Y), X,Y).
getargs2(times(X,Y), X,Y).
getargs2(append(X,Y), X,Y).
getargs2(cons(X,Y), X,Y).
getargs2(count_list(X,Y), X,Y).
getargs2(delete(X,Y), X,Y).
getargs2(intersect(X,Y), X,Y).
getargs2(meaning(X,Y), X,Y).
getargs2(member(X,Y), X,Y).
getargs2(nth(X,Y), X,Y).
getargs2(reverse_loop(X,Y), X,Y).
getargs2(sort_lp(X,Y), X,Y).
getargs2(fact_loop(X,Y), X,Y).
getargs2(falsify1(X,Y), X,Y).
getargs2(get(X,Y), X,Y).
getargs2(codegen(X,Y), X,Y).
getargs2(countps_(X,Y), X,Y).
getargs2(value(X,Y), X,Y).

getargs3(if(X,Y,Z), X,Y,Z).
getargs3(big_plus1(X,Y,Z), X,Y,Z).
getargs3(exec(X,Y,Z), X,Y,Z).
getargs3(countps_loop(X,Y,Z), X,Y,Z).
getargs3(set(X,Y,Z), X,Y,Z).

getargs4(big_plus(W,X,Y,Z), W,X,Y,Z).

setargs1(not(_), X, not(X)).
setargs1(boolean(_), X, boolean(X)).
setargs1(listp(_), X, listp(X)).
setargs1(numberp(_), X, numberp(X)).
setargs1(nlistp(_), X, nlistp(X)).
setargs1(zerop(_), X, zerop(X)).
setargs1(f(_), X, f(X)).
setargs1(add1(_), X, add1(X)).
setargs1(decr(_), X, decr(X)).
setargs1(even1(_), X, even1(X)).
setargs1(fix(_), X, fix(X)).
setargs1(odd(_), X, odd(X)).
setargs1(prime(_), X, prime(X)).
setargs1(prime_list(_), X, prime_list(X)).
setargs1(times_list(_), X, times_list(X)).
setargs1(car(_), X, car(X)).
setargs1(cdr(_), X, cdr(X)).
setargs1(dsort(_), X, dsort(X)).
setargs1(flatten(_), X, flatten(X)).
setargs1(length(_), X, length(X)).
setargs1(last(_), X, last(X)).
setargs1(mc_flatten(_), X, mc_flatten(X)).
setargs1(plus_tree(_), X, plus_tree(X)).
setargs1(plus_fringe(_), X, plus_fringe(X)).
setargs1(reverse(_), X, reverse(X)).
setargs1(reverse_(_), X, reverse_(X)).
setargs1(sort2(_), X, sort2(X)).
setargs1(fact_(_), X, fact_(X)).
setargs1(falsify(_), X, falsify(X)).
setargs1(gopher(_), X, gopher(X)).
setargs1(compile(_), X, compile(X)).
setargs1(optimize(_), X, optimize(X)).
setargs1(tautology_checker(_), X, tautology_checker(X)).
setargs1(normalize(_), X, normalize(X)).

setargs2(implies(_,_), X,Y, implies(X,Y)).
setargs2(and(_,_), X,Y, and(X,Y)).
setargs2(or(_,_), X,Y, or(X,Y)).
setargs2(iff(_,_), X,Y, iff(X,Y)).
setargs2(assignedp(_,_), X,Y, assignedp(X,Y)).
setargs2(eqp(_,_), X,Y, eqp(X,Y)).
setargs2(equal(_,_), X,Y, equal(X,Y)).
setargs2(greatereqp(_,_), X,Y, greatereqp(X,Y)).
setargs2(lessp(_,_), X,Y, lessp(X,Y)).
setargs2(lesseqp(_,_), X,Y, lesseqp(X,Y)).
setargs2(tautologyp(_,_), X,Y, tautologyp(X,Y)).
setargs2(assignment(_,_), X,Y, assignment(X,Y)).
setargs2(assume_false(_,_), X,Y, assume_false(X,Y)).
setargs2(assume_true(_,_), X,Y, assume_true(X,Y)).
setargs2(difference(_,_), X,Y, difference(X,Y)).
setargs2(divides(_,_), X,Y, divides(X,Y)).
setargs2(gcd(_,_), X,Y, gcd(X,Y)).
setargs2(greatest_factor(_,_), X,Y, greatest_factor(X,Y)).
setargs2(exp(_,_), X,Y, exp(X,Y)).
setargs2(plus(_,_), X,Y, plus(X,Y)).
setargs2(power_eval(_,_), X,Y, power_eval(X,Y)).
setargs2(power_rep(_,_), X,Y, power_rep(X,Y)).
setargs2(prime1(_,_), X,Y, prime1(X,Y)).
setargs2(quotient(_,_), X,Y, quotient(X,Y)).
setargs2(remainder(_,_), X,Y, remainder(X,Y)).
setargs2(samefringe(_,_), X,Y, samefringe(X,Y)).
setargs2(sigma(_,_), X,Y, sigma(X,Y)).
setargs2(times(_,_), X,Y, times(X,Y)).
setargs2(append(_,_), X,Y, append(X,Y)).
setargs2(cons(_,_), X,Y, cons(X,Y)).
setargs2(count_list(_,_), X,Y, count_list(X,Y)).
setargs2(delete(_,_), X,Y, delete(X,Y)).
setargs2(intersect(_,_), X,Y, intersect(X,Y)).
setargs2(meaning(_,_), X,Y, meaning(X,Y)).
setargs2(member(_,_), X,Y, member(X,Y)).
setargs2(nth(_,_), X,Y, nth(X,Y)).
setargs2(reverse_loop(_,_), X,Y, reverse_loop(X,Y)).
setargs2(sort_lp(_,_), X,Y, sort_lp(X,Y)).
setargs2(fact_loop(_,_), X,Y, fact_loop(X,Y)).
setargs2(falsify1(_,_), X,Y, falsify1(X,Y)).
setargs2(get(_,_), X,Y, get(X,Y)).
setargs2(codegen(_,_), X,Y, codegen(X,Y)).
setargs2(countps_(_,_), X,Y, countps_(X,Y)).
setargs2(value(_,_), X,Y, value(X,Y)).

setargs3(if(_,_,_), X,Y,Z, if(X,Y,Z)).
setargs3(big_plus1(_,_,_), X,Y,Z, big_plus1(X,Y,Z)).
setargs3(exec(_,_,_), X,Y,Z, exec(X,Y,Z)).
setargs3(countps_loop(_,_,_), X,Y,Z, countps_loop(X,Y,Z)).
setargs3(set(_,_,_), X,Y,Z, set(X,Y,Z)).

setargs4(big_plus(_,_,_,_), W,X,Y,Z, big_plus(W,X,Y,Z)).

:- pred atomic_f/1 : formula => formula.

atomic_f(1).
atomic_f(2).
atomic_f(6).
atomic_f(t).
atomic_f(f).
atomic_f(zero).
atomic_f([]).
atomic_f(a).
atomic_f(b).
atomic_f(c).
atomic_f(d).
atomic_f(x).
atomic_f(y).
:- endif.

% ---------------------------------------------------------------------------

truep(t,_) :- !.
truep(Wff,Tlist) :- member_(Wff,Tlist).

falsep(f,_) :- !.
falsep(Wff,Flist) :- member_(Wff,Flist).

:- pred member_/2 : term * list.

member_(X,[X|_]) :- !.
member_(X,[_|T]) :- member_(X,T).

:- pred equal/2 : formula * var => formula * formula.

equal( and(P,Q), % 106 rules
    if(P,if(Q,t,f),f)
    ).
%
equal( append(append(X,Y),Z),
    append(X,append(Y,Z))
    ).
equal( assignment(X,append(A,B)),
    if(assignedp(X,A),
       assignment(X,A),
       assignment(X,B))
    ).
%%
equal( assume_false(Var,Alist),
    cons(cons(Var,f),Alist)
    ).
equal( assume_true(Var,Alist),
    cons(cons(Var,t),Alist)
    ).
equal( boolean(X),
    or(equal(X,t),equal(X,f))
    ).
equal( car(gopher(X)),
    if(listp(X),
       car(flatten(X)),
       zero)
    ).
equal( compile(Form), % ???
    reverse(codegen(optimize(Form),[]))
     ).
%
equal( count_list(Z,sort_lp(X,Y)),
    plus(count_list(Z,X),
     count_list(Z,Y))
    ).
equal( countps_(L,Pred), % ???
      countps_loop(L,Pred,zero)
    ).
equal( difference(A,B),
    C
    ) :- difference(A,B,C).
equal( divides(X,Y),
    zerop(remainder(Y,X))
    ).
equal( dsort(X),
    sort2(X)
    ).
equal( eqp(X,Y),
    equal(fix(X),fix(Y))
    ).
equal( equal(A,B),
    C
    ) :- eq(A,B,C).
equal( even1(X),
    if(zerop(X),t,odd(decr(X)))
    ).
equal( exec(append(X,Y),Pds,Envrn),
    exec(Y,exec(X,Pds,Envrn),Envrn)
    ).
equal( exp(A,B),
    C
    ) :- exp(A,B,C).
%
equal( fact_(I),
    fact_loop(I,1)
    ).
equal( falsify(X),
    falsify1(normalize(X),[])
    ).
equal( fix(X),
    if(numberp(X),X,zero)
    ).
equal( flatten(cdr(gopher(X))),
    if(listp(X),
       cdr(flatten(X)),
       cons(zero,[]))
    ).
equal( gcd(A,B),
    C
    ) :- gcd(A,B,C).
equal( get(J,set(I,Val,Mem)), % ???
    if(eqp(J,I),Val,get(J,Mem))
    ).
equal( greatereqp(X,Y),
    not(lessp(X,Y))
    ).
% TODO: Wrong in the original translation! greatereqpr/2 is not valid
%%equal( greatereqpr(X,Y),
%%    not(lessp(X,Y))
%%    ).
equal( greaterp(X,Y),
    lessp(Y,X)
    ).
equal( if(if(A,B,C),D,E),
    if(A,if(B,D,E),if(C,D,E))
    ).
equal( iff(X,Y),
    and(implies(X,Y),implies(Y,X))
    ).
equal( implies(P,Q),
    if(P,if(Q,t,f),t)
    ).
equal( last(append(A,B)),
    if(listp(B),
       last(B),
       if(listp(A),
%          cons(car(last(A))), % TODO: Wrong in original translation! (see fix below)
      cons(car(last(A)), B), % TODO: Wrong in original translation! (I had to add ", B")
      B))
    ).
equal( length(A),
    B
    ) :- mylength(A,B).
equal( lesseqp(X,Y),
    not(lessp(Y,X))
    ).
%
equal( lessp(A,B),
    C
    ) :- lessp(A,B,C).
equal( listp(gopher(X)),
    listp(X)
    ).
equal( mc_flatten(X,Y),
    append(flatten(X),Y)
    ).
equal( meaning(A,B),
    C
    ) :- meaning(A,B,C).
equal( member(A,B),
    C
    ) :- mymember(A,B,C).
equal( not(P),
    if(P,f,t)
    ).
equal( nth(A,B),
    C
    ) :- nth(A,B,C).
equal( numberp(greatest_factor(X,Y)),
    not(and(or(zerop(Y),equal(Y,1)),
    not(numberp(X))))
    ).
equal( or(P,Q),
%    if(P,t,if(Q,t,f),f) % TODO: Wrong in original translation! (see fix below)
    if(P,if(Q,t,f),f) % TODO: Wrong in original translation!
    ).
equal( plus(A,B),
    C
    ) :- plus(A,B,C).
equal( power_eval(A,B),
    C
    ) :- power_eval(A,B,C).
%
equal( prime(X),
    and(not(zerop(X)),
    and(not(equal(X,add1(zero))),
        prime1(X,decr(X))))
    ).
equal( prime_list(append(X,Y)),
    and(prime_list(X),prime_list(Y))
    ).
equal( quotient(A,B),
    C
    ) :- quotient(A,B,C).
equal( remainder(A,B),
    C
    ) :- remainder(A,B,C).
equal( reverse_(X),
    reverse_loop(X,[])
    ).
equal( reverse(append(A,B)),
    append(reverse(B),reverse(A))
    ).
equal( reverse_loop(A,B),
    C
    ) :- reverse_loop(A,B,C).
equal( samefringe(X,Y),
    equal(flatten(X),flatten(Y))
    ).
equal( sigma(zero,I),
    quotient(times(I,add1(I)),2)
    ).
equal( sort2(delete(X,L)),
    delete(X,sort2(L))
    ).
equal( tautology_checker(X),
    tautologyp(normalize(X),[])
    ).
equal( times(A,B),
    C
    ) :- times(A,B,C).
equal( times_list(append(X,Y)),
    times(times_list(X),times_list(Y))
    ).
equal( value(normalize(X),A),
    value(X,A)
    ).
equal( zerop(X),
    or(equal(X,zero),not(numberp(X)))
    ).

:- pred difference/3 : expr * expr * term => expr * expr * expr.

difference(X, X, zero ) :- !.
difference(plus(X,Y), X, fix(Y) ) :- !.
difference(plus(Y,X), X, fix(Y) ) :- !.
difference(plus(X,Y), plus(X,Z), difference(Y,Z) ) :- !.
difference(plus(B,plus(A,C)), A, plus(B,C) ) :- !.
difference(add1(plus(Y,Z)), Z, add1(Y) ) :- !.
difference(add1(add1(X)), 2, fix(X) ).

:- pred eq/3 : expr * expr * term => expr * expr * formula.

eq(plus(A,B), zero, and(zerop(A),zerop(B)) ) :- !.
eq(plus(A,B), plus(A,C), equal(fix(B),fix(C)) ) :- !.
eq(zero, difference(X,Y),not(lessp(Y,X)) ) :- !.
% TODO: We found a bug here! and/1 was used!
%% eq(X, difference(X,Y),and(numberp(X),
%%                         and(or(equal(X,zero),
%%                             zerop(Y)))) ) :- !.
eq(X, difference(X,Y),and(numberp(X),
                      or(equal(X,zero),
                         zerop(Y))) ) :- !.
eq(times(X,Y), zero, or(zerop(X),zerop(Y)) ) :- !.
eq(append(A,B), append(A,C), equal(B,C) ) :- !.
eq(flatten(X), cons(Y,[]), and(nlistp(X),equal(X,Y)) ) :- !.
eq(greatest_factor(X,Y),zero, and(or(zerop(Y),equal(Y,1)),
                    equal(X,zero)) ) :- !.
eq(greatest_factor(X,_),1, equal(X,1) ) :- !.
eq(Z, times(W,Z), and(numberp(Z),
                    or(equal(Z,zero),
                       equal(W,1))) ) :- !.
eq(X, times(X,Y), or(equal(X,zero),
                   and(numberp(X),equal(Y,1))) ) :- !.
eq(times(A,B), 1, and(not(equal(A,zero)),
                  and(not(equal(B,zero)),
                    and(numberp(A),
                      and(numberp(B),
                        and(equal(decr(A),zero),
                      equal(decr(B),zero))))))
                                ) :- !.
eq(difference(X,Y), difference(Z,Y),if(lessp(X,Y),
                    not(lessp(Y,Z)),
                    if(lessp(Z,Y),
                        not(lessp(Y,X)),
                        equal(fix(X),fix(Z)))) ) :- !.
eq(lessp(X,Y), Z, if(lessp(X,Y),
                   equal(t,Z),
                   equal(f,Z)) ).

:- pred exp/3 : expr * expr * term => expr * expr * expr.

exp(I, plus(J,K), times(exp(I,J),exp(I,K))) :- !.
exp(I, times(J,K), exp(exp(I,J),K) ).

:- pred gcd/3 : expr * expr * term => expr * expr * expr.

gcd(X, Y, gcd(Y,X) ) :- !.
gcd(times(X,Z), times(Y,Z), times(Z,gcd(X,Y)) ).

:- pred mylength/2 : expr * term => expr * expr.

mylength(reverse(X),length(X)).
mylength(cons(_,cons(_,cons(_,cons(_,cons(_,cons(_,X7)))))),
     plus(6,length(X7))).

lessp(remainder(_,Y), Y, not(zerop(Y)) ) :- !.
lessp(quotient(I,J), I, and(not(zerop(I)),
                or(zerop(J),
                   not(equal(J,1)))) ) :- !.
lessp(remainder(X,Y), X, and(not(zerop(Y)),
                and(not(zerop(X)),
                      not(lessp(X,Y)))) ) :- !.
lessp(plus(X,Y), plus(X,Z), lessp(Y,Z) ) :- !.
lessp(times(X,Z), times(Y,Z), and(not(zerop(Z)),
                    lessp(X,Y)) ) :- !.
lessp(Y, plus(X,Y), not(zerop(X)) ) :- !.
lessp(length(delete(X,L)), length(L), member(X,L) ).

meaning(plus_tree(append(X,Y)),A,
    plus(meaning(plus_tree(X),A),
     meaning(plus_tree(Y),A))
    ) :- !.
meaning(plus_tree(plus_fringe(X)),A,
    fix(meaning(X,A))
    ) :- !.
meaning(plus_tree(delete(X,Y)),A,
    if(member(X,Y),
       difference(meaning(plus_tree(Y),A),
          meaning(X,A)),
       meaning(plus_tree(Y),A))).

mymember(X,append(A,B),or(member(X,A),member(X,B))) :- !.
mymember(X,reverse(Y),member(X,Y)) :- !.
mymember(A,intersect(B,C),and(member(A,B),member(A,C))).

nth(zero,_,zero).
nth([],I,if(zerop(I),[],zero)).
nth(append(A,B),I,append(nth(A,I),nth(B,difference(I,length(A))))).

plus(plus(X,Y),Z,
    plus(X,plus(Y,Z))
    ) :- !.
plus(remainder(X,Y),
     times(Y,quotient(X,Y)),
    fix(X)
    ) :- !.
plus(X,add1(Y),
    if(numberp(Y),
       add1(plus(X,Y)),
       add1(X))
    ).

power_eval(big_plus1(L,I,Base),Base,
    plus(power_eval(L,Base),I)
    ) :- !.
power_eval(power_rep(I,Base),Base,
    fix(I)
    ) :- !.
power_eval(big_plus(X,Y,I,Base),Base,
    plus(I,plus(power_eval(X,Base),
        power_eval(Y,Base)))
    ) :- !.
power_eval(big_plus(power_rep(I,Base),
            power_rep(J,Base),
            zero,
            Base),
       Base,
    plus(I,J)
    ).

quotient(plus(X,plus(X,Y)),2,plus(X,quotient(Y,2))).
quotient(times(Y,X),Y,if(zerop(Y),zero,fix(X))).

remainder(_, 1,zero) :- !.
remainder(X, X,zero) :- !.
remainder(times(_,Z), Z,zero) :- !.
remainder(times(Y,_), Y,zero).

reverse_loop(X,Y, append(reverse(X),Y) ) :- !.
reverse_loop(X,[], reverse(X) ).

times(X, plus(Y,Z), plus(times(X,Y),times(X,Z)) ) :- !.
times(times(X,Y),Z, times(X,times(Y,Z)) ) :- !.
times(X, difference(C,W),difference(times(C,X),times(W,X))) :- !.
times(X, add1(Y), if(numberp(Y),
                plus(X,times(X,Y)),
                fix(X)) ).

% -------------------------------------------------------------------
% this is not what might serve for the shfr+eterms analysis
% it's incomplete anyway
% formulae range over other formulae and expressions

:- regtype expr/1.
% arithmetic
expr(add1(X))   :- expr(X).
expr(big_plus1(X,Y,Z)) :- expr(X), expr(Y), expr(Z).
expr(big_plus(W,X,Y,Z)) :- expr(W), expr(X), expr(Y), expr(Z).
expr(difference(X,Y)) :- expr(X), expr(Y).
expr(decr(X)) :- expr(X).
expr(divides(X,Y))  :- expr(X), expr(Y).
expr(gcd(X,Y))  :- expr(X), expr(Y).
expr(greatest_factor(X,Y)) :- expr(X), expr(Y).
expr(exp(X,Y))  :- expr(X), expr(Y).
expr(even1(X)) :- expr(X).
expr(fix(X))    :- expr(X).
expr(odd(X))    :- expr(X).
expr(plus(X,Y)) :- expr(X), expr(Y).
expr(power_eval(X,Y)) :- expr(X), expr(Y).
expr(power_rep(X,Y)) :- expr(X), expr(Y).
expr(prime(X)) :- expr(X).
expr(prime1(X,Y)) :- expr(X), expr(Y).
expr(prime_list(X)) :- expr(X).
expr(quotient(X,Y)) :- expr(X), expr(Y).
expr(remainder(X,Y))  :- expr(X), expr(Y).
expr(samefringe(X,Y)) :- expr(X), expr(Y).
expr(sigma(X,Y)) :- expr(X), expr(Y).
expr(times(X,Y)) :- expr(X), expr(Y).
expr(times_list(X)) :- expr(X).
% list
expr(append(X,Y)) :- expr(X), expr(Y).
expr(car(X)) :- expr(X).
expr(cdr(X)) :- expr(X).
expr(cons(X,Y)) :- expr(X), expr(Y).
expr(count_list(X,Y)) :- expr(X), expr(Y).
expr(dsort(X)) :- expr(X).
expr(delete(X,Y)) :- expr(X), expr(Y).
expr(intersect(X,Y)) :- expr(X), expr(Y).
expr(flatten(X))  :- expr(X).
expr(length(X)) :- expr(X).
expr(last(X)) :- expr(X).
expr(mc_flatten(X))  :- expr(X).
expr(meaning(X,Y)) :- expr(X), expr(Y).
expr(member(X,Y)) :- expr(X), expr(Y).
expr(nth(X,Y)) :- expr(X), expr(Y).
expr(plus_tree(X)) :- expr(X).
expr(plus_fringe(X)) :- expr(X).
expr(reverse(X)):- expr(X).
expr(reverse_(X)):- expr(X).
expr(reverse_loop(X,Y)):- expr(X), expr(Y).
expr(sort2(X))    :- expr(X).
expr(sort_lp(X,Y))    :- expr(X), expr(Y).
% special case / no idea
%expr(equal(X,Y))   :- expr(X), expr(Y).
%
expr(exec(X,Y,Z)) :- expr(X), expr(Y), expr(Z).
expr(fact_(X)) :- expr(X).
expr(fact_loop(X,Y)) :- expr(X), expr(Y).
expr(falsify(X)) :- expr(X).
expr(falsify1(X,Y)) :- expr(X), expr(Y).
expr(get(X,Y)) :- expr(X), expr(Y).
expr(gopher(X)) :- expr(X). % ???
expr(compile(X)) :- expr(X).
expr(codegen(X,Y)) :- expr(X), expr(Y).
expr(countps_(X,Y)) :- expr(X), expr(Y).
expr(countps_loop(X,Y,Z)) :- expr(X), expr(Y), expr(Z).
expr(optimize(X)) :- expr(X).
expr(tautology_checker(X)) :- expr(X).
expr(set(X,Y,Z)) :- expr(X), expr(Y), expr(Z).
expr(value(X,Y)) :- expr(X), expr(Y).
% TODO: missing
expr(normalize(X)) :- expr(X).
% 'terminal'
expr(X)         :- terminal(X).

:- regtype formula/1.
% connectors
formula(implies(X,Y)) :- formula(X), formula(Y).
formula(and(X,Y))     :- formula(X), formula(Y).
formula(or(X,Y))      :- formula(X), formula(Y).
formula(if(X,Y,Z))    :- formula(X), formula(Y), formula(Z).
formula(iff(X,Y))     :- formula(X), formula(Y).
formula(not(X))       :- formula(X).
% predicates
formula(assignedp(X,Y)) :- expr(X), expr(Y).
formula(boolean(X)) :- expr(X).
formula(eqp(X,Y))     :- expr(X), expr(Y).
formula(equal(X,Y)) :- expr(X), expr(Y).
formula(greatereqp(X,Y)) :- expr(X), expr(Y).
formula(lessp(X,Y)) :- expr(X), expr(Y).
formula(lesseqp(X,Y)) :- expr(X), expr(Y).
formula(listp(X))  :- expr(X).
formula(numberp(X)) :- expr(X).
formula(nlistp(X))  :- expr(X).
formula(tautologyp(X,Y)) :- expr(X), expr(Y).
formula(zerop(X))   :- expr(X).
% no idea
formula(f(X))         :- expr(X).
formula(assignment(X,Y)) :- expr(X), expr(Y).
formula(assume_false(X,Y)) :- expr(X), expr(Y).
formula(assume_true(X,Y)) :- expr(X), expr(Y).
% 'terminal'
formula(X) :- expr(X).

:- regtype terminal(X).
terminal(1).
terminal(2).
terminal(6).
terminal(t).
terminal(f).
terminal(zero).
terminal([]).
terminal(a).
terminal(b).
terminal(c).
terminal(d).
terminal(x).
terminal(y).


