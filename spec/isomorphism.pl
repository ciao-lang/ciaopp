:- module( isomorphism,
    [
     isomorphic/3,
     qisomorphic_trees/2,
     get_builtins/2,
     gen_residual/1,
     case/3
    ], 
    [assertions, isomodes, datafacts]).

:- doc(title,"A module for determining the isomorphism of two
unfolded atom calls, based on a given minimization criterion").

:- doc(author, "Claudio Ochoa").

:- use_module(spec(spec_iterate), [really_unify/1]).
:- use_module(spec(unfold_operations),  [orig_pred_name/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(library(lists), [append/3, length/2]). 
:- use_module(library(terms), [copy_args/3]). 
:- use_module(library(terms_check), [variant/2, most_specific_generalization/3]).
:- use_module(library(sort), [sort/2]). 
:- use_module(engine(hiord_rt), ['$meta_call'/1]).

:- data gen_residual/1.
:- data case/3.

print_debug_info :- fail.

:- pred isomorphic(+Call1,+Call2,+Key) #"Determines whether two
unfolded atom calls @var{Call1} and var@{Call2} are isomorphic. Each
atom call is a tuple containing the unfolded clauses, the generalized
atom, and the characteristic tree resulting of unfolding the atom call
w.r.t. the program. Isomorphism will depend on the @tt{min_crit}
flag. When this flag is set to @tt{residual}, it will assert residual
code (if needed) using @var{Key} as a key for later retrieval".

isomorphic(call1(Cls1,Sg1,Chtree1),call2(Cls2,Sg2,Chtree2),Key):-
    current_pp_flag(min_crit,Min),
    isomorphic_(Min,Cls1,Sg1,Chtree1,Cls2,Sg2,Chtree2,Key).

isomorphic_(equal,_,_,Chtree1,_,_,Chtree2,_):- 
    Chtree1 == Chtree2.
isomorphic_(codemsg,Clauses1,Sg1,_,Clauses2,Sg2,_,_):- 
    length(Clauses1,Len),
    length(Clauses2,Len),
    isomorphic_clauses(Clauses1,Sg1,Clauses2,Sg2).
isomorphic_(nobindings,Clauses1,Sg1,Chtree1,Clauses2,Sg2,Chtree2,_):- 
    isomorphic_trees(Chtree1,Chtree2,nb),
    isomorphic_clauses(Clauses1,Sg1,Clauses2,Sg2).
isomorphic_(bindings,Clauses1,Sg1,Chtree1,Clauses2,Sg2,Chtree2,_):- 
    isomorphic_trees(Chtree1,Chtree2,bin),
    isomorphic_clauses(Clauses1,Sg1,Clauses2,Sg2).
isomorphic_(residual,Clauses1,Sg1,Chtree1,Clauses2,Sg2,Chtree2,_):- 
    isomorphic_trees(Chtree1,Chtree2,iso),!,
    isomorphic_clauses_with_builtins(Clauses1,Sg1,Chtree1,Clauses2,Sg2,Chtree2).
isomorphic_(residual,_,_,Chtree1,_,_,Chtree2,Key):- 
    qisomorphic_trees(Chtree1,Chtree2),
    asserta_fact(gen_residual(Key)).

:- pred qisomorphic_trees(+T1,+T2) #"Determines whether two
characteristics trees @var{T1} and @var{T2} are quasi-isomorphic. In
this case, bindings belonging to characteristic paths are not taken
into account for comparison".

qisomorphic_trees([],[]).
qisomorphic_trees([H1|T1],[H2|T2]):-
    list(H1),!,
    list(H2),
    qisomorphic_paths(H1,H2),
    qisomorphic_trees(T1,T2).

qisomorphic_paths([],[]).
qisomorphic_paths([(L1:H1)|T1],[(L2:H2)|T2]):-
    number(H1),!,
    number(H2),
    H1==H2,
    L1==L2,
    qisomorphic_paths(T1,T2).
qisomorphic_paths([_|T1],[_|T2]):-
    qisomorphic_paths(T1,T2).

:- pred isomorphic_trees(+T1,+T2,+Crit) #"Determines whether two
characteristics trees @var{T1} and @var{T2} are isomorphic, according
to minimization criterion @var{Crit}".

isomorphic_trees([],[],_).
isomorphic_trees([H1|T1],[H2|T2],Crit):-
    list(H1),!,
    list(H2),
    isomorphic_paths(H1,H2,Crit),
    isomorphic_trees(T1,T2,Crit).

isomorphic_paths([],[],_).
isomorphic_paths([(L1:H1)|T1],[(L2:H2)|T2],Crit):-
    number(H1),!,
    number(H2),
    H1==H2,
    L1==L2,
    isomorphic_paths(T1,T2,Crit).
% isomorphic_paths([(L1:_)|T1],[(L2:_)|T2],res):-
%       !,L1==L2,
%       isomorphic_paths(T1,T2,res).
isomorphic_paths([(L1:(P1,B1))|T1],[(L2:(P2,B2))|T2],Crit):-
    L1==L2,
    matching_builtins(builtin(P1,B1),builtin(P2,B2),Crit),
    isomorphic_paths(T1,T2,Crit).

:- pred isomorphic_clauses(+Cls1,+Call1, +Cls2, +Call2) #"Determines
whether clauses @var{Cls1} and @var{Cls2} are isomorphic by taking its
@tt{msg} and checking if when instantiating back using @var{Call1} and
@var{Call2} respectively, they are variant".

isomorphic_clauses([],_,[],_).
isomorphic_clauses([C1|T1],Sg1,[C2|T2],Sg2):-
    get_orig_clause_name(C1,OC1),
    get_orig_clause_name(C2,OC2),
    copy_term(OC1,C1_copy),
    copy_term(OC2,C2_copy),
    copy_term(Sg1,Sg1_copy),
    copy_term(Sg2,Sg2_copy),
    most_specific_generalization(C1_copy,C2_copy,Gen_Clause),
    copy_term(Gen_Clause,Gen_Clause_copy1),
    copy_term(Gen_Clause,Gen_Clause_copy2),
    match_clause(OC1,Gen_Clause_copy1,Sg1_copy),
    match_clause(OC2,Gen_Clause_copy2,Sg2_copy),
    isomorphic_clauses(T1,Sg1,T2,Sg2).

:- pred get_orig_clause_name(+Cl,-) #"Takes a clause @var{Cl} and
returns the same clause with its original name".

get_orig_clause_name(clause(H,B),clause(NH,B)):-
    rename_clause(H,NH).
get_orig_clause_name(clauseinst(H,I,B),clauseinst(NH,I,B)):-
    rename_clause(H,NH).

:- pred rename_clause(+,-) #"Renames a clause using its original name,
preserving arguments".

rename_clause(H,NH):-
    functor(H,P,A),
    orig_pred_name(P,OP),
    functor(NH,OP,A),
    copy_args(A,H,NH).

:- pred match_clause(+Orig_Clause, +Msg_Clause, +Sg) #"Takes a clause
@var{Orig_Clause}, and another clause @var{Msg_Clause} resulting from
an @tt{msg}. It instantiates @var{Msg_Clause} to @var{Sg}, and
verifies whether this instantiated clause is a variant of the original
@var{Orig_Clause}".

match_clause(Orig_Clause,clause(Gen_Head,_Body),Sg):-
    Sg=Gen_Head,
    variant(Orig_Clause,clause(Gen_Head,_Body)).
match_clause(Orig_Clause,clauseinst(Gen_Head,Inst,_Body),Sg):-
    Sg=Gen_Head,
    exec_all(Inst),
    variant(Orig_Clause,clauseinst(Gen_Head,Inst,_Body)).

:- pred exec_all(+L) #"Exectues all builtins in var@{L}".

exec_all([]).
exec_all([H|Tail]):-
    '$meta_call'(H),
    exec_all(Tail).

:- pred isomorphic_clauses_with_builtins(+Cls1,+Call1, +Chtree1,+Cls2,
+Call2, +Chtree2) #"Determines whether clauses @var{Cls1} and
@var{Cls2} are isomorphic, by taking into account the builtins
contained in @var{Chtree1} and @var{Chtree2}".

isomorphic_clauses_with_builtins(Clauses1,Sg1,Chtree1,Clauses2,Sg2,Chtree2):-
    add_builtins(Clauses1,Chtree1,Clauses1wb),
    add_builtins(Clauses2,Chtree2,Clauses2wb),
    isomorphic_clauses(Clauses1wb,Sg1,Clauses2wb,Sg2).

add_builtins([],_Chtree,[]).
add_builtins([Clause|T],[Ch_Path|Ch_T],[Clausewb|Twb]):-
    add_builtins_clause(Clause,Ch_Path,Clausewb),
    add_builtins(T,Ch_T,Twb).

add_builtins_clause(Clause,Ch_Path,Clausewb):-
    Clause =.. [clause,Head,Body],
    get_builtins(Ch_Path,Builtins),
    Clausewb =.. [clauseinst,Head,Builtins,Body].

:- pred get_builtins(+L,-) #"Collects all builtins from L.  A builtin
is represented by a pair (Predicate,[Bindings]) ".

get_builtins([],[]).
get_builtins([(_:H)|T],L):-
    number(H),!,
    get_builtins(T,L).
get_builtins([(_:(P,B))|T],[P|T2]):-
    really_unify(B),
    get_builtins(T,T2).

:- pred matching_builtins(+B1,+B2,+Crit) #"Determines whether builtins
@var{B1} and @var{B2} match, according to a criterion @var{Crit}".

matching_builtins(builtin(Pred1,Bind1),builtin(Pred2,Bind2),Crit):-
    copy_term(p(Pred1,Bind1),p(P1,B1)),
    copy_term(p(Pred2,Bind2),p(P2,B2)),
    match_(Crit,P1,B1,P2,B2).

match_(nb,_,[],_,[]) :- 
    update_stats(nb).
match_(bin,P1,B1,P2,B2) :- 
    match_variant(P1,B1,P2,B2),!, 
    update_stats(var).
match_(bin,P1,B1,P2,B2) :- 
    match_svsp(P1,B1,P2,B2),
    update_stats(svsp).
match_(iso,_,[],_,[]) :- !,
    update_stats(nb).
match_(iso,P1,B1,P2,B2) :- 
    match_variant(P1,B1,P2,B2),!, 
    update_stats(var).
match_(iso,P1,B1,P2,B2) :- 
    match_svsp(P1,B1,P2,B2),
    update_stats(svsp).

:- pred match_variant(+P1,+B1,+P2,+B2) #"Checks whether @var{P1} and
@var{P2} are variant, after unifying them with their respective
bindings @var{B1} and @var{B2}".

match_variant(P1,B1,P2,B2):-    
    really_unify(B1),
    really_unify(B2),
    variant(P1,P2).

:- pred match_svsp(+P1,+B1,+P2,+B2) #"Checks whether @var{P1} and
@var{P2} have the same values at the same positions, after unifying
them with their respective bindings @var{B1} and @var{B2}".

match_svsp(P1,B1,P2,B2):-    
    get_positions(B1,P1,Pos1),
    get_positions(B2,P2,Pos2),
    append(Pos1,Pos2,Pos),
    sort(Pos,SP),
    really_unify(B1),
    really_unify(B2),
    same_positions(SP,P1,P2).
    
:- pred get_positions(+Bind,+Pred,-Pos) #"Gets a list @var{Pos} of the
position of each binding in @var{Bind} in predicate @var{Pred}".

get_positions([],_P,[]).
get_positions([V=_|T],Pred,[Pos|NT]):-        
    functor(Pred,_,A),
    A>0,
    Pred =.. [_F|Args],
    get_pos(Args,V,1,[],Pos),
    get_positions(T,Pred,NT).

get_pos([Arg|_],V,Cur_pos,Acc_pos,Res):-
    V==Arg,!,
    append(Acc_pos,[Cur_pos],Res).
get_pos([Arg|_],V,Cur_pos,Acc_pos,Res):-
    functor(Arg,_,A),
    A>0,
    Arg =.. [_|Args],
    append(Acc_pos,[Cur_pos],NAP),
    get_pos(Args,V,1,NAP,Res).
get_pos([_|T],V,Cur_pos,Acc_pos,Res):-
    New_pos is Cur_pos + 1,
    get_pos(T,V,New_pos,Acc_pos,Res).       

:- pred same_positions(+L,+P1,+P2) #"Takes a list of positions @var{L}
and checks whether the value in that position is the same in
predicates @var{P1} and @var{P2}".

same_positions([],_,_). 
same_positions([H|T],Pred1,Pred2):-
    same_pos(H,Pred1,Pred2),
    same_positions(T,Pred1,Pred2).

same_pos([],P1,P2):-P1==P2.
same_pos([H|T],P1,P2):-
    arg(H,P1,A1),
    arg(H,P2,A2),
    same_pos(T,A1,A2).

:- pred update_stats(+Case) #"When debugging, it collect statistics to
determine which cases of matching buildings are more common. It
asserts the collected statistics in case/3. ".

update_stats(Case):-
    print_debug_info,!,
    retract_fact(case(A,B,C)),
    update_stats_(Case,A,B,C,NA,NB,NC),
    asserta_fact(case(NA,NB,NC)).
update_stats(_).

update_stats_(nb,A,B,C,NA,B,C):- NA is A + 1. % case 1: no bindings
update_stats_(var,A,B,C,A,NB,C):- NB is B + 1. % case 2: variant
update_stats_(svsp,A,B,C,A,B,NC):- NC is C + 1. % case 3: same values at same positions
