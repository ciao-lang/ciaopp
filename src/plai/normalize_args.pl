/*             Copyright (C)1990-2002 UPM-CLIP                         */
:- module(normalize_args, [normalize_args/4],   [assertions]).

:- use_module(ciaopp(p_unit), [type_of_goal/2]).

:- use_module(library(vndict), [complete_dict/3]).

:- use_module(library(sets), [merge/3, ord_intersection/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% normalize_args(+,-)
%% normalize_args(InProg,OutProg)
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

normalize_args([],[],[],[]).
normalize_args([Cl:Id|Cls],[D|Ds],[NewCl:Id|NewCls],[NewD|NewDs]):-
    normalize_clause(Cl,D,NewCl,NewD),
    normalize_args(Cls,Ds,NewCls,NewDs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% normalize_clause(+,-)
%% normalize_clause(InClause,OutClause)
%% This predicates translates InClause into OutClause
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

normalize_clause(directive(M,I),D,directive(M,I),D).
normalize_clause(clause(Head,true),D,clause(NHead,NBody),NewD):- !,
    normalize_literal(Head,NHead,TmpBody,[]),
    (TmpBody = [] ->
        NBody = true,
        complete_dict(D,NBody,NewD)
    ; flatten_body(TmpBody,NBody),
      complete_dict(D,NBody,NewD)
    ).
normalize_clause(clause(Head,Body),D,clause(NHead,NBody),NewD):- 
    normalize_literal(Head,NHead,TmpBody,TailBody),
    normalize_body(Body,TailBody),
    flatten_body(TmpBody,NBody),
    complete_dict(D,NBody,NewD).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% normalize_body(+,-)
% normalize_body(Body,NBody) 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% normalize_body((Sg:K,Body),NBody):- !,
%       normalize_literal(Sg,NSg,NBody,Tail0),
%       Tail0 = [NSg:K|Tail],
%       normalize_body(Body,Tail).
% normalize_body(Sg:K,NBody):- 
%       normalize_literal(Sg,NSg,NBody,Tail0),
%       Tail0 = [NSg:K].

normalize_body((Lit,Body),NBody):- !,
    normalize_literal0(Lit,NBody,Tail),
    normalize_body(Body,Tail).
normalize_body(Lit,NBody):- 
    normalize_literal0(Lit,NBody,[]).

normalize_literal0(Sg:K,NBody,Tail):- !,
    normalize_literal(Sg,NSg,NBody,Tail0),
    Tail0 = [NSg:K|Tail].
normalize_literal0(_,NBody,NBody).  % for cuts

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% normalize_literal(+,-,?,-)                               
%% normalize_literal(Sg,NSg,Constr,Tail)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

normalize_literal(Sg,NSg,Constr,Tail):- 
    type_of_goal(builtin(_TypeGoal),Sg),!,
    NSg = Sg,
    Constr = Tail.
normalize_literal(Sg,NSg,Constr,Tail):- 
    type_of_goal(metapred(_Type,_Meta),Sg),!,
    NSg = Sg,
    Constr = Tail.
normalize_literal(Sg,NSg,Constr,Tail):-
    functor(Sg,F,A),
    functor(NSg,F,A),
    normalize_literal_(0,A,Sg,NSg,[],Constr,Tail).

normalize_literal_(N,N,_,_,_,Tail,Tail):- !.
normalize_literal_(N1,N,Sg,NSg,Vars,Constr,Tail):-
    N2 is N1 +1,
    arg(N2,Sg,ArgSg),
    arg(N2,NSg,ArgNSg),
    decide_argument(ArgSg,ArgNSg,Constr,Vars,NewConstr,NewVars),
    normalize_literal_(N2,N,Sg,NSg,NewVars,NewConstr,Tail).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% decide_argument(+,?,+,+,-,-)
%% decide_argument(Arg1,Arg2,Constr,Vars,NewConstr,NewVars)
%% Arg1 and Arg2 are the arguments of the Literal and NewLiteral
%% respectively. Cases:
%%    1. If Arg1 is a variable:
%%          * If Arg1 is already in Vars -> is a multiple occurrence
%%            of the variable. Thus Arg2 will be the new variable
%%            and the constraint Arg2 = Arg1 will be added to the set
%%            of constraints Constr.
%%          * Otherwise Arg2 will be unified to Arg1.
%%    3. For the rest, Arg2 is a variable and Arg2 = Arg1 is added
%%      to the set of constraints in Constr
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

decide_argument(Arg1,Arg2,Constr,Vars,NewConstr,NewVars):-
    var(Arg1),!,
    ord_intersection([Arg1],Vars,Intersect),
    decide_var(Intersect,Arg1,Arg2,Constr,Vars,NewConstr,NewVars).
decide_argument(Arg1,Arg2,Constr,Vars,NewConstr,Vars):-
    Constr = [ (Arg2 = Arg1):no | NewConstr ].

decide_var([],Arg1,Arg1,Constr,Vars,NewConstr,NewVars):- !,
    Constr = NewConstr,
    merge([Arg1],Vars,NewVars).
decide_var([_],Arg1,Arg2,Constr,Vars,NewConstr,NewVars):-
    Constr = [ (Arg2 = Arg1):no | NewConstr ],
    NewVars = Vars.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

flatten_body([X],X):- !.
flatten_body([X|Xs],(X,NXs)):- 
    flatten_body(Xs,NXs).
