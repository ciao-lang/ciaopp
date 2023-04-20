:- module(_,[powers/3],[assertions]).

%! powers(X,N,P): `P` is the sorted list that contains the smallest `N` integers that are
%  a power of one of the elements of the list `X`.
%  \includedef{powers/3}
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

%! first_powers(N,L,R): `R` is a sorted list with `N` numbers. The first component of the first
%  element of the pair-list `L` is the next element in the output we are constructing (i.e., `R`).
%  We remove this pair, compute the next power of F (i.e. P*F), and insert the pair (P*F,F)
%  into the pair-list.
%  \includedef{first_powers/3}
first_powers(N,[(Power,Factor)|PFs],[Power|Powers]) :-
    N > 0, !,
    N1 is N-1,
    remove_power(Power,PFs,PFs1),
    Power1 is Power*Factor,
    sorted_insert(PFs1,(Power1,Factor),PFs2),
    first_powers(N1,PFs2,Powers).
first_powers(0,_,[]).


%! remove_powers(P,L,R): `R` is the sorted list of pairs obtained by removing from the list `L`
%  the pair (`P`,_).
%  \includedef{remove_powers/3}
remove_power(_,[],[]).
remove_power(Power,[(Power1,Factor)|RestOut],[(Power1,Factor)|RestOut]) :-
    Power =\= Power1, !.
remove_power(Power,[_|RestPFsIn],PFsOut) :-
    remove_power(Power,RestPFsIn,PFsOut).

%! qsorted_insert(L,P,R): `R` is the sorted list of pairs obtained by adding to the list `L`
%  the pair `P`.
%  \includedef{qsorted_insert/3}
sorted_insert([], X, [X]).
sorted_insert([(X1,F1)|L1], (X,F), [(X,F), (X1,F1)|L1]):- X =< X1, !.
sorted_insert([P|L1], X, [P|L]):- sorted_insert(L1, X, L).