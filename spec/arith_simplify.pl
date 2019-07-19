:- module(_,[arith_simp/2],[assertions]).

:- use_package(assertions).

:- doc(title,"Simplification of Arithmetic Operations").

:- doc(author, "Pawel Pietrzak").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains arithmetic simplification 
    rules which allows reducing the size of operations and sometimes even 
    making them evaluable at partial evaluation time.").

% Things like arith_simp(2+(0*T), R) return R=2.

arith_simp(A,R):-
	rewrite(A,A1),!,
	arith_simp(A1,R).	    
arith_simp(A,A).

% rewrite(Expr,Res) 
% Rewrites expression Expr into strictly simpler Res. 
% Fails if nothing can be simplified.

rewrite(A,_R):-
	var(A),
	!,
	fail.
rewrite(A,R) :-
	ground(A),
	\+ number(A), 
        arithexpression(A),
	!,
	R is A.
rewrite(A+B,R):-
	( zero(A), R = B
	; zero(B), R = A
	),
	!.	 
rewrite(A+B,R):-
	( rewrite(A,A1), R = A1 + B 
        ; rewrite(B,B1), R = A + B1 
	),
	!.
rewrite(A+B,R) :-   % orientation / commutativity
	number(B),
	R = B+A,!.
rewrite(A+A2,R) :- % associativity
	nonvar(A2),
	A2 = B+C,
	rewrite(A+B+C,R).
rewrite(A-B,R):-
	( zero(A), R = -B
	; zero(B), R = A
	),
	!.	 
rewrite(A-B,R):-
	( rewrite(A,A1), R = A1 - B 
        ; rewrite(B,B1), R = A - B1 
	),
	!.
rewrite(A*B,R):-
	( zero(A)
	; zero(B)
	),
	R = 0,
	!.	
rewrite(A*B,R):-
	( one(A), R = B
	; one(B), R = A
	),
	!.	  
rewrite(A*B,R):-
	( rewrite(A,A1), R = A1 * B 
        ; rewrite(B,B1), R = A * B1 
	),
	!.
rewrite(A*B,R) :-   % orientation / commutativity
	number(B),
	R = B*A,!.
rewrite(A*A2,R) :-  % associativity
	nonvar(A2),
	A2 = B*C,
	rewrite(A*B*C,R).
rewrite(A/_,R):-
	zero(A), 
	!,
	R = 0.
rewrite(A/B,R):-
	one(B), 
	!,
	R = A.
rewrite(A/B,R):-
	( rewrite(A,A1), R = A1 / B 
        ; rewrite(B,B1), R = A / B1 
	),
	!.
rewrite(A/B,R):-!,
	number(B),
	RB is 1/B,
	R = RB * A.
rewrite(Unary,R) :-
	Unary =.. [F,A],
	\+ \+ arithexpression(Unary), % to avoid binding A
	rewrite(A,SimpA),
	UnaryR =.. [F,SimpA],
	(  number(SimpA) ->
	   R is UnaryR
	;  R = UnaryR
	).

% rewrite(sin(A),R):- !,
%         rewrite(A,A1), 
%         R = sin(A1).
% rewrite(round(A),R):- !,
%         rewrite(A,A1), 
%         R = round(A1).


zero(X):- ground(X), X =:= 0.
one(X):- ground(X), X =:= 1.
