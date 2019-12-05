:- module(_, [sortClauses/3, 
              user_clauses/3,
              jpg_program_format/3], []).

:- use_module(library(lists)).

:- use_module(chclibs_canonical).

:- op(750,fx,type).

sortClauses([predicates(Ps)|Cls], Ps,Procs) :-
    initProcs(Ps,Procs0),
    buildProcs(Cls,Procs0,Procs).

initProcs([],[]).
initProcs([P/N|Ps], [proc(P/N,[])|Procs]) :-
    initProcs(Ps,Procs).
    
buildProcs([],Pr,Pr).
buildProcs([clause((H :- B), Vs)|Cls], Procs0, Procs2) :-
    functor(H,P,N),
    insertClause(Procs0,P/N,H,B,Vs,Procs1),
    buildProcs(Cls, Procs1, Procs2).
    
insertClause([proc(Pred,Cls)|Procs0],Pred,H,B,Vs,[proc(Pred,Cls1)|Procs0]) :-
    !,
    append(Cls,[clause((H :- B), Vs)],Cls1).
insertClause([Proc|Procs0],Pred,H,B,Vs,[Proc|Procs1]) :-
    insertClause(Procs0,Pred,H,B,Vs,Procs1).


user_clauses([],_,[]).
user_clauses([proc(P/N,Cls)|_],P/N,Cls1) :-
    !,
    returnCls(Cls,Cls1).
user_clauses([_|Prcs],P/N,Cls) :-
    user_clauses(Prcs,P/N,Cls).

returnCls([],[]).
returnCls([clause(C,_)|Cls],[C|Cls1]) :-
    returnCls(Cls,Cls1).


% converts from Ciao program reader internal form

jpg_program_format(Cls,Ds,[predicates(Ps)|Cls1]) :-
    convert2jpg(Cls,Ds,Cls1,Ps),
    close_list(Ps).

convert2jpg([],[],[],_).
convert2jpg([clause(H,Body):_|Cls],
            [dic(Vs,Ns)|Ds],[clause((H :- B),Ws)|Cls1],Ps) :-
    !,
    cleanBody(Body,B),
    get_pred_name((H :- B),Pred,Bodypreds),
    each_memb1([Pred|Bodypreds],Ps),
    binding_pairs(Vs,Ns,Ws),
    canonical(clause((H :- B),Ws)),
    convert2jpg(Cls,Ds,Cls1,Ps).
convert2jpg([_|Cls],[_|Ds],Cls1,Ps) :-
    convert2jpg(Cls,Ds,Cls1,Ps).
    
cleanBody((B:_,Bs),(B,Bs1)) :-
    !,
    cleanBody(Bs,Bs1).
cleanBody(B:_,B) :-
    !.
cleanBody((!,Bs),(!,Bs1)) :-
    !,
    cleanBody(Bs,Bs1).
cleanBody(!,!).

get_pred_name((H :- B),P/N,BPs) :-
    !,
    functor(H,P,N),
    body_preds(B,BPs).
get_pred_name(H ,P/N,[]) :-
    functor(H,P,N).

body_preds(B,Ps) :-
    bodyPredNames(B,Ps,[]).

bodyPredNames('$VAR'(_),Ps,Ps) :-
    !.
bodyPredNames(true,Ps,Ps) :-
    !.
bodyPredNames((B,Bs),Ps0,Ps2) :-
    !,
    bodyPredNames(B,Ps0,Ps1),
    bodyPredNames(Bs,Ps1,Ps2).
bodyPredNames(B,[P/N|Ps],Ps) :-
    functor(B,P,N).


each_memb1([],_).
each_memb1([P|Ps],S) :-
    memb1(P,S),
    each_memb1(Ps,S).
    
memb1(X,[X|_]) :-
    !.
memb1(X,[_|Xs]) :-
    memb1(X,Xs).

binding_pairs([],[],[]).
binding_pairs([V|Vs],[A|As],[A=V|Ws]) :-
    binding_pairs(Vs,As,Ws).

close_list([]) :-
    !.
close_list([_|X]) :-
    %write(C),nl,
    close_list(X).
