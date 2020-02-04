:- module(meta_call,[meta_call/1,peel_meta_call/4,build_meta_call/4],[assertions]).

%-------------------------------------------------------------------------
% Handling metacalls.
% This module implements some predicates needed by tr_syntax for handling
% metacalls properly.
%-------------------------------------------------------------------------

:- use_module(ciaopp(p_unit/itf_db)).

:- pred meta_call(Goal) : callable(Goal) 

# "Succeeds if @var{Goal} is a meta-predicate call.".

meta_call(Goal):-
    current_itf(meta,Goal,_), !. % TODO: missing cut?

%-------------------------------------------------------------------------

:- pred peel_meta_call(Goal,GList,NoGList,Args) 
    : callable(Goal) => (list(callable,GList), list(NoGList), list(Args))
# "Given a meta-predicate call @var{Goal}, returns in @var{GList} the
  list of arguments which are goals, and the arguments which are not goals in
  @var{NoGList}. On return @var{Args} contains the list of all arguments.".

peel_meta_call(Goal,GList,NoGList,Args):-
    current_itf(meta,Goal,Meta), !,
    Goal =.. [_|Args],
    Meta =.. [_|Metaargs],
    peel_meta_call_(Args,Metaargs,GList,NoGList).

peel_meta_call_([],[],[],[]).
peel_meta_call_([A|Args],[goal|Metaargs],[A|GList],NoGList):-
    !,
    peel_meta_call_(Args,Metaargs,GList,NoGList).
peel_meta_call_([A|Args],[_|Metaargs],GList,[A|NoGList]):-
    peel_meta_call_(Args,Metaargs,GList,NoGList).

%-------------------------------------------------------------------------

:- pred build_meta_call(Pred,GList,Args,Goal)
    : (predname(Pred), list(callable,GList), list(Args)) => callable(Goal)
# "Returns in @var{Goal} a goal to a meta-predicate named @var{Pred}
  with arguments @var{Args}, but replacing the arguments in @var{Args}
  which are goals by the elements of @var{GList}.".

build_meta_call(F/A,NGList,Args,Goal):-
    functor(Goal,F,A),
    current_itf(meta,Goal,Meta), !,
    Meta =.. [_|Metaargs],
    build_meta_call_(Args,Metaargs,NGList,NArgs),
    Goal =.. [F|NArgs].

build_meta_call_([],[],[],[]).
build_meta_call_([_|Args],[goal|Metaargs],[G|NGList],[G|NArgs]):-
    !,
    build_meta_call_(Args,Metaargs,NGList,NArgs).
build_meta_call_([A|Args],[_|Metaargs],NGList,[A|NArgs]):-
    build_meta_call_(Args,Metaargs,NGList,NArgs).



