:- regtype list_num(X) # "@var{X} is a list of numbers." .
list_num([]).
list_num([X|T]) :-
      num(X), list_num(T).