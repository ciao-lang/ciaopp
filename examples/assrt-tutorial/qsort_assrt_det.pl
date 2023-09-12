:- module(_,[qsort/2],[assertions,nativeprops,regtypes,modes]).

% qsort/2 with some assertions.
% The system verifes the assertions and also that 
% =</2 and >/2 are called correctly and will not 
% generate any run-time errors.  
% Try also generating the documentation for this file!

% If qsort/2 is called with a list of numbers, it will
% return a list of numbers and at most one solution.
:- pred qsort(+list(num),-list(num)) + semidet.
 
qsort([], []).
qsort([First|Rest],Result) :-
    partition(Rest,First,Sm,Lg), 
    qsort(Sm,SmS), 
    qsort(Lg,LgS),
    append(SmS,[First|LgS],Result).

% partition/4 is called with a list of numbers and a
% number, and it returns two lists of numbers, one solution,
% and will never fail. 
:- pred partition(+list(num),+num,-list(num),-list(num)) 
        + det.

partition([],_,[],[]).
partition([X|Y],F,[X|Y1],Y2) :- 
    X =< F, 
    partition(Y,F,Y1,Y2).
partition([X|Y],F,Y1,[X|Y2]) :- 
    X > F,
    partition(Y,F,Y1,Y2).

% append/3 is called with two lists of numbers, and will
% return a list of numbers, and at most one solution.
:- pred append(+list(num),+list(num),-list(num)) + semidet.

append([],Xs,Xs).
append([X|Xs],Ys,[X|Zs]) :-
    append(Xs,Ys,Zs).
