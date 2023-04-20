:- module(power_without_assertions3,[powers/3],[assertions, nativeprops,regtypes]).

:- regtype list_num(X) # "@var{X} is a list of numbers." .
list_num([]).
list_num([X|T]) :-
      num(X), list_num(T).

:- pred powers(A,B,C) : (list_num(A), num(B), var(C)) => list_num(C) .

powers([],_,[]).
powers(Factors,N,Powers) :-
    quicksort(Factors, SFactors),
    create_pairs(SFactors,Pairs),
    first_powers(N,Pairs,Powers).

quicksort(Xs,Ys) :- qsort(Xs,Ys,[]).

qsort([],DL,DL).

qsort([X|Xs],Head,Tail) :-
    partition(Xs,X,L,R),
    qsort(L,Head,[X|QR]),
    qsort(R,QR,Tail).

partition([],_,[],[]).
partition([X|Xs],Pv,[X|L],R) :- X =< Pv, !, partition(Xs,Pv,L,R). 
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
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]):- X =< X1, !.
sorted_insert([X1|L1], X, [X1|L]):- sorted_insert(L1, X, L).
