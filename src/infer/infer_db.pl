:- module(infer_db,[domain/1,inferred/3,point_info/5,cleanup_infer_db/1],
    [assertions, datafacts]).

:- doc(bug,"Check that this database is properly cleaned-up.").

:- doc(inferred(Analyzer,Key,Info),
    "The analysis @var{Analyzer} has inferred @var{Info} related
      to the program source part @var{Key}.").
:- data inferred/3.

:- data domain/1.

:- doc(point_info(Key,AbsInt,Vars,FVars,Info),
    "Properties @var{Info} hold at program point @var{Key}.").
:- data point_info/5.

:- pred cleanup_infer_db/1 # "Erases all data in this module.".
cleanup_infer_db(Analysis):-
    retractall_fact(inferred(Analysis,_,_)).

