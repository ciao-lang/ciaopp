:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes,doccomments]).

% Describing predicates with modes/assertions in doccomments syntax
% (which also get verified by the system). Try also generating the 
% documentation for this file!

%! qsort(+list(num),-list(num)) + semidet: 
%  The second argument is the first one sorted.
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

%! partition(+list(num),+num,-list(num),-list(num)) + det: 
%  Partitions a list into two lists, greater and
%  smaller than the pivot (second argument). 
partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

%! append(+list(num),+list(num),-list(num)) + semidet: 
append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
