:- module(spec_gen_pred_vers,
    [
        write_pred_versions/5,
        generate_body/4
    ],
    [assertions, datafacts]).

:- doc(title,"Generation of Multiply Specialized Program after Minimization").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module is in charge of generating the
     multiply specialized program after deciding which are the
     optimizations available in each version and performing the
     minimization algorithm.").

:- use_module(spec(spec_support), 
    [group_predicate/8, replace/3, change_call/3, get_last/2]).

:- use_module(spec(spec),       [versions/2]).
:- use_module(spec(spec_iterate), [body_result/4]).
:- use_module(spec(spec_multiple), 
    [second_components/2, simplif/3, equalities/2]).

:- use_module(library(compiler/p_unit/program_keys), [get_predkey/3]).
:- use_module(ciaopp(plai/plai_db), [complete/7]).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(terms), [copy_args/3]). 
:- use_module(library(aggregates), [findall/3]). 
:- use_module(library(lists), [append/3]). 

%-------------------------------------------------------------------%
% write_pred_versions(+,+,+,-,-)                                    %
% write_pred_versions(Clauses,Dicts,Abs,NClauses,NDicts)            %
%  NClauses,NDicts is the resulting program after generating and    %
% simplifying the specialized versions                              %
%-------------------------------------------------------------------%
write_pred_versions([],[],_Abs,Cs,Ds):-!,
    equal_versions(Cs,Ds).
write_pred_versions([directive(D):Id|Cs],[Dict|Dicts],Abs,
                [directive(D):Id|SCs],[Dict|NewDicts]):-
    write_pred_versions(Cs,Dicts,Abs,SCs,NewDicts).
write_pred_versions(Cs,Ds,Abs,NCs,NDs):-
    group_predicate(Cs,Ds,N,A,Pred,Dict,MoreCs,MoreDs),
    generate_pred_versions(N,A,Pred,Dict,Abs,NCs,NDs,SCs,SDs),
    write_pred_versions(MoreCs,MoreDs,Abs,SCs,SDs).

%-------------------------------------------------------------------%
% We generate all the necessary versions for a list of clauses
% (hopefully a whole predicate)
generate_pred_versions(N,A,Pred,Dict,Abs,NPred,NDict,Tail1,Tail2):-
    get_predkey(N,A,Key),
    current_fact(versions(Key,V)),
    versions(V,Pred,Dict,Abs,NPred,NDict,Tail1,Tail2).
%-------------------------------------------------------------------%
% We generate one version for a list of clauses
versions([],_,_,_Abs,Tail1,Tail2,Tail1,Tail2).
versions([(Completes,Name)|Vs],Pred,Dict,Abs,NPred,NDict,Tail1,Tail2):-
    second_components(Completes,CompNum),
    vers_of_pred(Pred,Dict,Abs,Name,CompNum,NPred,NDict,MPred,MDict),
    versions(Vs,Pred,Dict,Abs,MPred,MDict,Tail1,Tail2).
    
%-------------------------------------------------------------------%
% We only generate a version of a clause if there is a complete     
% with an Id that belongs to this version. This means that different
% versions of a predicate may have different set of clauses
%
vers_of_pred([],[],_,_,_,Tail1,Tail2,Tail1,Tail2).
% useless clauses are now natively undertood by the abstract specializer!
vers_of_pred([_:Clid|Cs],[_D|Ds],Abs,Name,CompN,NCs,NDs,T1,T2):-
    current_fact(simplif(Clid,Name,useless)),!,
    vers_of_pred(Cs,Ds,Abs,Name,CompN,NCs,NDs,T1,T2).
vers_of_pred([clause(H,B):Clid|Cs],[D|Ds],Abs,Name,CompN,[NC|NCs],[D|NDs],T1,T2):-
    functor(H,N,A),
    get_predkey(N,A,Key),
    copy_term(H,Copy),
    current_fact(complete(Key,Abs,Copy,_,_,C,_),_),
    % This check is still required!
    memberchk(C,CompN),
    !,
    functor(NewHead,Name,A),
    copy_args(A,H,NewHead),
    ( B == [] ->
        NewBody2 = []
    ;
        generate_body(B,Name,NewBody,Result),
        body_result(Result,NewHead,NewBody,NewBody2)
    ),
    NC = clause(NewHead,NewBody2):Clid,
    vers_of_pred(Cs,Ds,Abs,Name,CompN,NCs,NDs,T1,T2).
vers_of_pred([_|Cs],[_|Ds],Abs,Name,CompNum,NCs,NDs,T1,T2):-
    vers_of_pred(Cs,Ds,Abs,Name,CompNum,NCs,NDs,T1,T2).

%-------------------------------------------------------------------%
% generate_body(+,+,-,-)                                            %
% generate_body(Body,Version,NewGoals,Result)                       %
%  NewGoals is a copy of Body for a new version whose name is Version
%-------------------------------------------------------------------%
generate_body([],_,[],nonerror).
generate_body([fail:K],_,[fail:K],fail):-!.
generate_body([error:'$bottom'],_,[error:'$bottom'],error):-!.
%-------------------------------------------------------------%
% Goal is simplificable in this particular version            %
%-------------------------------------------------------------%
generate_body([(Goal:K)|Goals],Version,NGoals,Result):-
    current_fact(simplif(K,Version,Sense)),
    !,
    gen_simp_body(Sense,[(Goal:K)|Goals],Version,NGoals,Result).
%-------------------------------------------------------------%
% Goal has to be replaced by a call to a special version      %
%-------------------------------------------------------------%
generate_body([(Goal:K)|Goals],Version,
                           [(NewGoal:K)|NewGoals],Result):-
    current_fact(spec_support:replace(K,Version,NewName)),
    !,
    change_call(Goal,TmpGoal,NewName),
    test_when_replacement(TmpGoal,K,Version,Goals,NewGoal,NewGoals,Result).

%-------------------------------------------------------------%
% Goal is a set of parallel goals                             %
%-------------------------------------------------------------%
generate_body([Parall_exp|Goals],Version,NewGoals,Result):-
    functor(Parall_exp,'.',2), % it is a list
    !,
    generate_body(Parall_exp,Version,NewParall,Result),
    case_parall_body(Result,NewParall,Version,NewGoals,Goals).
%-------------------------------------------------------------%
% We copy the goal as it is                                   %
%-------------------------------------------------------------%
generate_body([G|Goals],Version,[G|NewGoals],Result):-      
    generate_body(Goals,Version,NewGoals,Result).


%-------------------------------------------------------------%
% Particular simplifications we can do in parallel expressions%
%-------------------------------------------------------------%
case_parall_body(fail,[_:K|_],_,[(fail:K)],_):-!.
case_parall_body(error,NewParall,_,Last,_):-!,
    get_last(NewParall,Last).
case_parall_body(Result,NewParall,Version,[NewParall|MoreGoals],Goals):-
    generate_body(Goals,Version,MoreGoals,Result).

test_when_replacement(when(C,G),K,Version,Goals,NewGoal,NewGoals,Result):-
    current_fact(simplif(K,Version,Sense)),!,
    NGoals = [(NewGoal:K)|NewGoals],
    gen_simp_body(Sense,[(when(C,G):K)|Goals],Version,NGoals,Result).

test_when_replacement(Goal,_K,Version,Goals,Goal,NewGoals,Result):-
    generate_body(Goals,Version,NewGoals,Result).
%-------------------------------------------------------------%
% Here we materialize the optimizations                       %
%-------------------------------------------------------------%

gen_simp_body(imported(_,true),[_|Goals],Version,NewGoals,Result):-
    generate_body(Goals,Version,NewGoals,Result).
gen_simp_body(imported(_,'basiccontrol:fail'),[_:K|_],_Version,[(fail:K)],fail).
gen_simp_body(error,[(Goal:K)|_],_,[(Goal:K),(error:'$bottom')],error).

%% gen_simp_body(indep(_,[]),[_|Goals],Version,NewGoals,Result):-!,
%%      generate_body(Goals,Version,NewGoals,Result).
%% gen_simp_body(indep(L,NewL),[indep(L):K|Goals],Version,
%%                                      [indep(NewL):K|NewGoals],Result):-
%%         generate_body(Goals,Version,NewGoals,Result).
%% 
%% gen_simp_body(ground(_,[]),[_|Goals],Version,NewGoals,Result):-!,
%%      generate_body(Goals,Version,NewGoals,Result).
%% gen_simp_body(ground(L,NewL),[ground(L):K|Goals],Version,
%%                              [ground(NewL):K|NewGoals],Result):-
%%         generate_body(Goals,Version,NewGoals,Result).
%% 
%% gen_simp_body(when(Cond,true),OldGoals,Version,NewGoals,Result):-!,
%%      OldGoals = [when(Cond,Goal):K|Goals],
%%      NewGoals = [Goal:K|NGoals],
%%      generate_body(Goals,Version,NGoals,Result).
%% gen_simp_body(when(L,NewL),[when(L,Goal):K|Goals],Version,
%%                              [when(NewL,Goal):K|NewGoals],Result):-
%%         generate_body(Goals,Version,NewGoals,Result).
gen_simp_body(imported(Goal,NewGoal),[Goal:K|Goals],Version,
                            [NewGoal:K|NewGoals],Result):-
    generate_body(Goals,Version,NewGoals,Result).

%-------------------------------------------------------------------%
% equal_versions(-,-)                                               %
% equal_versions(Clauses,Dictionaires)                              %
%  When two or more entries for a predicate are implemented in only %
% one version, we generate here Clauses that transform a call into  %
% a call to the implemented version.                                %
%-------------------------------------------------------------------%
equal_versions(Cs,Ds):-
    findall((C,D),(current_fact(equalities(C,D))),L),
    flatten_lpairs(L,Cs,Ds).

flatten_lpairs([],[],[]).
flatten_lpairs([(C,D)|More],Cs,Ds):-
    append(C,MoreC,Cs),
    append(D,MoreD,Ds),
    flatten_lpairs(More,MoreC,MoreD).
