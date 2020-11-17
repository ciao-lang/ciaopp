:- module(exponential_ac,[exp/3],[assertions]).

:- entry exp(Base,3,_) : int(Base).

exp(Base,Exp,Res):-
    exp_ac(Exp,Base,1,Res).

exp_ac(0,_,Res,Res).
exp_ac(Exp,Base,Tmp,Res):-
    Exp > 0,
    Exp1 is Exp - 1,
    NTmp is Tmp * Base,
    exp_ac(Exp1,Base,NTmp,Res).
