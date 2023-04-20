:- module(_,[powers/3],[assertions, regtypes, nativeprops]).

:- use_module(library(lists)).
:- use_module(library(aggregates)).

:- prop sorted(Xs).

sorted([]).
sorted([_]).
sorted([X,Y|Ns]) :-
	X =< Y,
	sorted([Y|Ns]).

:- prop list_nnegint(X) + regtype 
# "Verifies that @var{X} is list of non-negative integers." .  
list_nnegint([]).
list_nnegint([X|T]) :-
    nnegint(X), list_nnegint(T).

:- pred powers(A,B,C) : (list_nnegint(A), nnegint(B), var(C)) => (list_nnegint(C), sorted(C)) + not_fails .

% Unit tests
:- test powers(A,B,C) : (A = [3,4,5], B = 17) => (C = [3,4,5,9,16,25,27,64,81,125,243,256,625,729,1024,2187,3125]) + not_fails.

:- test powers(A,B,C) : (A = [2,9999999,9999998], B = 20) => (C = [2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576]) + not_fails.

:- test powers(A,B,C) : (A = [2,4], B = 6) => (C = [2,4,8,16,32,64]) + not_fails.

powers([],_,[]).
powers(Factors,N,Powers) :-
    quicksort(Factors, SFactors),
    create_pairs(SFactors,Pairs),
    first_powers(N,Pairs,Powers).

% qsort with a slight mistake: it may fail when there are repeated numbers in the list
quicksort(Xs,Ys) :- qsort(Xs,Ys,[]).

qsort([],DL,DL).

qsort([X|Xs],Head,Tail) :-
    partition(Xs,X,L,R),
    qsort(L,Head,[X|QR]),
    qsort(R,QR,Tail).

partition([],_,[],[]).
partition([X|Xs],Pv,[X|L],R) :- X < Pv, !, partition(Xs,Pv,L,R). % (1) should be >= (or =< below)
partition([X|Xs],Pv,L,[X|R]) :- X > Pv, partition(Xs,Pv,L,R).


create_pairs([],[]).
create_pairs([X|R],[(X,X)|S]) :- create_pairs(R,S).


first_powers(N,[(Power,Factor)|PFs],[Power|Powers]) :-
    N > 0, !,
    N1 is N-1,
    remove_power(Power,PFs,PFs1),
    Power1 is Power*Factor,
    sorted_insert(PFs1,(Power1,Factor),PFs2),
    first_powers(N1,PFs2,Powers).
first_powers(0,_,[]).

remove_power(_,[],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\= Power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).

sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]) :- X =< X1, ! .
sorted_insert([P|L1], X, [P|L]) :- sorted_insert(L1, X, L).

