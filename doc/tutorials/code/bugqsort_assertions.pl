:- module(_, [qsort/2], [assertions, regtypes, nativeprops]).

:- pred qsort(A,B) : (list(num, A), var(B)).

qsort([X|L],R) :-
    partition(L,X,L1,L2),        
    qsort(L2,R2), qsort(L1,R1),
    append(R2,[x|R1],R).
qsort([],[]).

partition([],_B,[],[]).
partition([E|R],C,[E|Left1],Right):-  
    E < C, !, partition(R,C,Left1,Right).
partition([E|R],C,Left,[E|Right1]):-
    E >= C, partition(R,C,Left,Right1).

append([],X,X).
append([H|X],Y,[H|Z]):- append(X,Y,Z).

:- calls   qsort(A,B)         : list(num, A).                       % A1
:- success qsort(A,B)         => (list(num,B), sorted_num_list(B)). % A2
:- calls   partition(A,B,C,D) : (ground(A), ground(B)).             % A3
:- success partition(A,B,C,D) => (list(num, C), ground(D)).         % A4
:- calls   append(A,B,C)      : (list(num,A),list(num,B)).          % A5
:- comp    partition/4        + not_fails.                          % A6
:- comp    partition/4        + det.                                % A7
:- comp    partition(A,B,C,D) + terminates.                         % A8

:- prop sorted_num_list/1.
sorted_num_list([]).
sorted_num_list([_]).
sorted_num_list([X,Y|Z]):-
     num(X), num(Y), X=<Y, sorted_num_list([Y|Z]).
