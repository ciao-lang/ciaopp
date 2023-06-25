:- module(spec_iterate,[
    init_clause_result/0,
    iterate/7,
    simplify/6,
    body_result/4,
    minimal_unif/3,
    really_unify/1,
    clause_result/2], % temporary
    [assertions, isomodes, datafacts]).

:- use_module(engine(hiord_rt), [call/1]). % TODO: review uses here

:- doc(title,"Iterative optimizations of programs in a bottom up
   fashion").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module performs iterative optimizations of 
    programs in a bottom up fashion by replacing calls to predicates 
    which are globally reduced to fail, a fact or a bridge.").

:- doc(bug, "1 unifications introduced by means of abstractly executable 
    meta_calls are not executed but only left indicated regardless of the 
    value of flag exec_unif").

:- use_module(spec(spec), [abs_ex/2]).

:- use_module(spec(unfold_operations),  [decide_orig_goal/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(library(idlists), [memberchk/2]).

:- use_module(library(compiler/p_unit), [type_of_goal/2]).

:- use_module(spec(s_simpspec), [list2body/2, next_pred/2]).
:- use_module(library(compiler/p_unit/program_keys),
    [get_predkeys/2, predkey_from_sg/2, get_predkey/3, make_atom/2]).

:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(ciaopp(infer), [get_info/5]).

:- use_module(spec(spec_support), [get_last/2, non_static/1]).

:- use_module(library(terms_check), [ask/2]).
:- use_module(library(terms_vars), [varset/2]). 
:- use_module(library(vndict), [create_dict/2]).
:- use_module(library(aggregates), [findall/3]). 
:- use_module(library(lists), [append/3]). 

:- use_module(library(vndict), [complete_dict/3, prune_dict/3, sort_dict/2]).

:- data clause_result/2.

init_clause_result:-
    retractall_fact(clause_result(_,_)).
    
:- data iterations/1.

%-------------------------------------------------------------------%   
%                                                                   %
% iterate(+,+,+,+,+,-,-)                                            %
% iterate(Prog,Dicts,N,Preds,Abs,Nprog,Ndicts)                      %
%  Creates a new version of program Prog with dictionaries Dicts in %
% iteration number N and writes the new version in Nprog,Ndicts     %
%-------------------------------------------------------------------%
iterate([],[],N,Preds,Abs,Nprog,Ndicts):-!,
    get_predkeys(Preds,Keys),
    reduce_last_iteration(Preds,Keys,N,Abs,_Flag),
    asserta_fact(iterations(N)),
    add_fail_clauses([],Nprog,[],Ndicts).

iterate(Prog,Dicts,N,Preds,Abs,Nprog,Ndicts):-
    get_predkeys(Preds,Keys),
    reduce_last_iteration(Preds,Keys,N,Abs,Flag),
    (Flag == yes ->
        N1 is N+1,
        it_prog(Prog,Dicts,Iprog,Idicts),
        iterate(Iprog,Idicts,N1,Preds,Abs,Nprog,Ndicts)
    ;
        asserta_fact(iterations(N)),
        add_fail_clauses(Prog,Nprog,Dicts,Ndicts)
    ).

%-------------------------------------------------------------------%
% it_prog(+,+,-,-)                                                  %
% it_prog(Prog,Dicts,NewProg,NewDicts)                              %
%  Transforms Prog,Dicts into NewProg,NewDicts when one or more     %
% predicates have been reduced in the previous iteration            %
%-------------------------------------------------------------------%
it_prog([],[],[],[]).
it_prog([directive(Dir):Id|Cs],[D|Dicts],
                 [directive(Dir):Id|SCs],[D|NewDicts]):-
    it_prog(Cs,Dicts,SCs,NewDicts).
%-------------------------------------------------------------%
% This is the unique clause for a fact previously reduced to  %
% true, so it is removed, as is no longer needed.             %
%-------------------------------------------------------------%
it_prog([clause(H,[]):_|Cs],[_|Dicts],SCs,NewDicts):-
    functor(H,Name,Arity),
    current_fact(abs_ex(Name/Arity,(true,_,_))),
    !,
    it_prog(Cs,Dicts,SCs,NewDicts).
%-------------------------------------------------------------%
% It is a fact but the predicate has not been reduced to true,%
% so we must keep it.                                         %
%-------------------------------------------------------------%
it_prog([clause(H,[]):Clid|Cs],[D|Dicts],
                               [clause(H,[]):Clid|SCs],[D|NDs]):-
    !,
    predkey_from_sg(H,Key),
    asserta_fact(clause_result(Key,fact(H))),
    it_prog(Cs,Dicts,SCs,NDs).
%-------------------------------------------------------------%
% This is the unique clause for a fact previously reduced to  %
% "bridge", so it is removed, as is no longer needed.         %
%-------------------------------------------------------------%
it_prog([clause(H,[_Body]):_|Cs],[_|Dicts],SCs,NewDicts):-
    functor(H,Name,Arity),
    current_fact(abs_ex(Name/Arity,(true,_,_))),
    !,
    it_prog(Cs,Dicts,SCs,NewDicts).
%-------------------------------------------------------------%
% We study the body of clause to see if any goal can be       %
% simplified due to previously reduced predicates.            %        
%-------------------------------------------------------------%
it_prog([clause(Head,Body):Clid|Cs],[D|Dicts],SimpProg,NewDicts):-
    it_body(Head,Body,SimpBody,DictFlag),
    (DictFlag == newdict ->
        sort_dict(D,D0),
        remove_duplicated_vars_in_dict(D0,D1),
        complete_dict(D1,SimpBody,D2),
        prune_dict(SimpBody,D2,ND)
    ;
        ND = D
    ),
    simplify(clause(Head,SimpBody),Cs,CsOut,NewBody,Dicts,DictsOut),
    (NewBody = [(fail:_)] ->
        SimpProg = NewSimp,
        NewDicts = Ndicts
    ;
        SimpProg = [clause(Head,NewBody):Clid|NewSimp],
        NewDicts = [ND|Ndicts],
        (NewBody = [NBody:_] ->
         predkey_from_sg(Head,Key),
         asserta_fact(clause_result(Key,bridge(Head,NBody)))
        ;
            true)),
    it_prog(CsOut,DictsOut,NewSimp,Ndicts).

%-------------------------------------------------------------------%
% it_body(+,+,-,-)                                                  %
% it_body(H,Body,SimpBody,DictFlag)                                 %
%   SimpBody is the simplified version of the clause(H,Body) accor- %
% ding to the predicates reduced in the previous iteration.         %
% DictFlag indicates whether a new dictionary is needed. This is    %
% needed when unifications have been executed                       %
%-------------------------------------------------------------------%
it_body(H,Body,SimpBody,DictFlag):-
    next_pred(Body,Pred),
    it_body_list(Body,SimpBlist,Pred,Result,DictFlag),
    body_result(Result,H,SimpBlist,SimpBody).

%-------------------------------------------------------------------%
% it_body_list(+,-,+,-,-)                                           %
% it_body_list(Goals,NewGoals,Pred,Result,DictFlag)                 %
%  NewGoals is the simplified version of Goals in this iteration    %
% Pred is the functor of first goal in Goals. Result is a Flag indi-%
% cating the status of the clause for later postprocess of the      %
% clause the Goals belong to.                                       %
%-------------------------------------------------------------------%
it_body_list([],[],none,nonerror,_).
%----------------------------------------------------------------%
% This (error:'$bottom') is a fictitious goal introduced previosly   %
% that indicates that the clause ends with a goal reduced to     %
% error. It is useful for not condidering that clause as nonerror%
%----------------------------------------------------------------%
it_body_list([(error:'$bottom')],[(error:'$bottom')],_,error,_):-!.
%----------------------------------------------------------------%
% If we find the goal fail, we know that we have already removed %
% goals according to study_side_effects and there is no need for %
% doing that again. So result is error instead of fail           %     
%----------------------------------------------------------------%
it_body_list([(fail:K)],[(fail:K)],fail/0,error,_):-!. 
%----------------------------------------------------------------%
% This goal calls a predicate reduced in previous iterations     %
%----------------------------------------------------------------%
it_body_list([Goal|Goals],NewGoals,Pred,Result,DictFlag):-
    current_fact(abs_ex(Pred,Inf)),
    !,
    it_abs_ex_goal(Inf,[Goal|Goals],NewGoals,Result,DictFlag).
%----------------------------------------------------------------%
% In this clause we analyze parallel goals                       %
%----------------------------------------------------------------%
it_body_list([P_exp|Goals],NewGoals,Pred,Result,DictFlag):-
    Pred = '.'/2,
    !,
    next_pred(P_exp,NPred),
    it_parall_list(P_exp,P_Goals,NPred,TmpResult,[],Unif_List),
    (TmpResult == fail -> % if one fails they all fail!!
        NewGoals = [fail],
        Result = fail
    ;
        (TmpResult == error ->
            get_last(P_Goals,Last),
            NewGoals = [Last,(error:'$bottom')],
            Result = error
        ;
            (P_Goals == [] ->
                append(Unif_List,MoreGoals,NewGoals)
            ;
                append(Unif_List,[P_Goals|MoreGoals],NewGoals)
            ),
        next_pred(Goals,NewPred),
        it_body_list(Goals,MoreGoals,NewPred,Result,DictFlag)
        )
    ).
%----------------------------------------------------------------%
% The Goal is a meta call (maybe to a reduced predicate)         %
%----------------------------------------------------------------%
it_body_list([Goal:K|Goals],NewGoals,Pred,Result,DictFlag):-
    type_of_goal(metapred(_,_),Goal),!,
    NewGoals = [NewGoal:K|MoreGoals],
    it_body_list_meta_call(Pred,Goal,NewGoal,Goals,MoreGoals,Result,DictFlag).

%----------------------------------------------------------------%
% Rest of Goals                                                  %
%----------------------------------------------------------------%
it_body_list([Goal|Goals],[Goal|NewGoals],_,Result,DictFlag):-
    next_pred(Goals,NewPred),
    it_body_list(Goals,NewGoals,NewPred,Result,DictFlag).
%----------------------------------------------------------------%
% it_body_list_meta_call(+,+,-,+,-,-,-)                          %
% it_body_list_meta_call(Pred,Goal,NewGoal,Goals,NewGoals,Result)%
%  This Goal is a meta_call. We must check if the final call uses%
% a predicate reduced to fail or true and replace the call.      %
% By now we do not simplify the clause as the treatment is diffe-%
% rent for not and findall.                                      %
%----------------------------------------------------------------%
it_body_list_meta_call(_Pred,Goal,NewGoal,Goals,NewGoals,Result,DictFlag):-
    functor(Goal,when,2),!,
    functor(NewGoal,when,2),
    arg(1,Goal,Cond),
    arg(1,NewGoal,Cond),
    arg(2,Goal,Call),
    arg(2,NewGoal,NewCall),
    functor(Call,N,A),
    it_body_list_meta_call(N/A,Call,NewCall,Goals,NewGoals,Result,DictFlag).
it_body_list_meta_call(_Pred,Goal,NewGoal,Goals,NewGoals,Result,DictFlag):-
    type_of_goal(metapredicate(_,_),Goal),
    functor(Goal,Name,Arity),
    functor(NewGoal,Name,Arity),
    (Arity == 1 ->
        Arg = 1
    ;
        Arg = 2,
        arg(1,Goal,Var),
        arg(1,NewGoal,Var),
        arg(3,Goal,List),
        arg(3,NewGoal,List)),
    arg(Arg,Goal,Call),
    arg(Arg,NewGoal,NewCall),
    nonvar(Call),!,
    functor(Call,N,A),
    it_body_list_meta_call(N/A,Call,NewCall,Goals,NewGoals,Result,DictFlag).
it_body_list_meta_call(Pred,Goal,NewGoal,Goals,NewGoals,Result,DictFlag):-
    current_fact(abs_ex(Pred,Info)),!,
    it_body_list_meta_call_abs_ex(Info,Goal,NewGoal,DictFlag),
    next_pred(Goals,NewPred),
    it_body_list(Goals,NewGoals,NewPred,Result,DictFlag).
it_body_list_meta_call(_,Goal,Goal,Goals,NewGoals,Result,DictFlag):-
    next_pred(Goals,Pred),
    it_body_list(Goals,NewGoals,Pred,Result,DictFlag).
%----------------------------------------------------------------%
% it_body_list_meta_call_abs_ex(+,+,-)                           %
%  We replace a call to a predicate reduced to true by a list of %
% unifications that is converted into a conjunction. If is has   %
% been reduced to fail then we replace by fail. We do nothing if %
% the predicate has been reduced to error.                       %
%----------------------------------------------------------------%
it_body_list_meta_call_abs_ex((true,Goal,Unif_list),Goal,NewGoal,_DictFlag):-
    copy_term(Unif_list,Copy_Unif),
    exec_unif(Unif_list,Copy_Unif,New_unif),
    list2body(New_unif,NewGoal).
it_body_list_meta_call_abs_ex(fail,_Goal,fail,_DictFlag).
it_body_list_meta_call_abs_ex((error,_),Goal,Goal,_DictFlag).
%-------------------------------------------------------------------%
% it_abs_ex_goal(+,+,-,-,-)                                         %
% it_abs_ex_goal(Information,Goals,NewGoals,Result,DictFlag)        %
%  NewGoals is the simplified versions of Goals according to Infor- %
% mation. Special case of it_body_list when we know that the first  %
% goal of Goals calls a predicate previously reduced.               %
%-------------------------------------------------------------------%
it_abs_ex_goal((true,Goal,(Unif_list,Bridge)),[(Goal:K)|Goals],NewGoals,Result,DictFlag):-!,
    it_abs_ex_goal_result(Goals,NewGoals,K,Result,(Unif_list,Bridge),DictFlag).
it_abs_ex_goal((true,Goal,Unif_list),[(Goal:K)|Goals],NewGoals,Result,DictFlag):-
    it_abs_ex_goal_result(Goals,NewGoals,K,Result,Unif_list,DictFlag).
it_abs_ex_goal(fail,[_:K|_],[(fail:K)],fail,_DictFlag).
it_abs_ex_goal((error,_),[Goal|_],[Goal,(error:'$bottom')],error,_DictFlag).

it_abs_ex_goal_result([(fail:K)],[(fail:K)],_,fail,_,_DictFlag):-!.
% unif are removed, don't have side-effects
it_abs_ex_goal_result(Goals,NewGoals,K,Result,(Unif_list,Bridge),DictFlag):-!,
    (copy_term(Unif_list,Copy_Unif),
     exec_unif(Unif_list,Copy_Unif,New_unif) ->
     % we have to reduce Brigde!
         functor(Bridge,F,A),
         it_body_list([Bridge:noinfo],NewBridge,F/A,_R,DictFlag),
         current_pp_flag(exec_unif,Unif),
         (Unif = on ->
             DictFlag = newdict,
             really_unify(New_unif),
             OtherGoals = NewBridge
         ;
             put_no_keys(New_unif,New_numbered_unif),
             append(New_numbered_unif,NewBridge,OtherGoals)
         ),
         next_pred(Goals,Pred),
         append(OtherGoals,MoreGoals,NewGoals),
         it_body_list(Goals,MoreGoals,Pred,Result,DictFlag)
    ;
        NewGoals = [(fail:K)],
        Result = fail).
it_abs_ex_goal_result(Goals,NewGoals,K,Result,Unif_list,DictFlag):-
    (copy_term(Unif_list,Copy_Unif),
     exec_unif(Unif_list,Copy_Unif,New_unif) ->
         current_pp_flag(exec_unif,Unif),
         (Unif = on ->
             DictFlag = newdict,
             really_unify(New_unif),
             NewGoals = MoreGoals
         ;
             put_no_keys(New_unif,New_numbered_unif),
             append(New_numbered_unif,MoreGoals,NewGoals)
         ),
         next_pred(Goals,Pred),
         it_body_list(Goals,MoreGoals,Pred,Result,DictFlag)
    ;
        NewGoals = [(fail:K)],
        Result = fail).

really_unify([]).
really_unify([(A=B)|Unif]):-
    call(A=B),
    really_unify(Unif).
%-------------------------------------------------------------------%
% it_parall_list(+,-,+,-,+,-)                                       %
% it_parall_list(Goals,NewGoals,Pred,Result,Lin,Lout)               %
%  NewGoals is the simplified version of a list of parallel goals   %
% Lin is a list unifications and Lout is the previous list possibly %
% increased if the first goal of Goals has been previously reduced  %
% to true (we add to Lin the necessary unifications.                %
%-------------------------------------------------------------------%
it_parall_list([],[],_,_,L,L).
it_parall_list([(G:K)|Gs],NewGoals,Pred,Result,Lin,Lout):-
    current_fact(abs_ex(Pred,(true,G,L))),
    !,      
    copy_term(L,Copy),
    (exec_unif(L,Copy,NewL)->
        put_keys(NewL,unif,DefL),
        append(Lin,DefL,Ltemp),
        next_pred(Gs,NewPred),
        it_parall_list(Gs,NewGoals,NewPred,Result,Ltemp,Lout)
    ;
        % the unifications are known to fail
        NewGoals = [(fail:K)],
        Result = fail).
it_parall_list([_:K|_],NewGoals,Pred,Result,L,L):-
    current_fact(abs_ex(Pred,fail)),
    !,
    NewGoals = [(fail:K)],
    Result = fail.
it_parall_list([(G:K)|_],NewGoals,Pred,error,L,L):-
    current_fact(abs_ex(Pred,(error,_))),
    !,
    NewGoals = [(G:K),(error:'$bottom')].
it_parall_list([G|Gs],[G|NewGs],_,Result,Lin,Lout):-
    next_pred(Gs,NewPred),
    it_parall_list(Gs,NewGs,NewPred,Result,Lin,Lout).


%-------------------------------------------------------------------%
% reduce_last_iteration(+,+,+,+,-)                                  %
% reduce_last_iteration(Preds,Keys,N,Abs,Flag)                      %
%  Process the information generated during the last iteration (N)  %
% to know if any of the predicates in the program (Preds) has been  %
% reduced to true, fail,or error. In that case Flag will have the   %
% value yes.                                                        %
% However, if the flag @tt{spec_postproc} has the value off, then   %
% we do not iterate, no matter whether there are predicates reduced %
% in the previous (first) iteration                                 % 
%-------------------------------------------------------------------%
reduce_last_iteration(_Preds,_Keys,_N,_Abs,_Flag):-
    current_pp_flag(spec_postproc,off),!.
reduce_last_iteration(Preds,Keys,N,Abs,Flag):-
    fail_predicate(Preds,Keys,Flag),
    error_predicate(Preds,Keys,N,Abs,Flag),
    true_predicate(Preds,Keys,Flag),
    retractall_fact(clause_result(_,_)).

remove_duplicated_vars_in_dict(dic([],[]),NDict):-!,
    NDict = dic([],[]).
remove_duplicated_vars_in_dict(dic([V|Vs],[N|Names]),NDict):-
    NDict = dic([V|NVs],[N|NNames]),
    rem_dup_dict(Vs,V,NVs,Names,NNames).

rem_dup_dict([],_V,[],[],[]).
rem_dup_dict([V0|Vs],V,NVs,[_N|Names],NNames):-
    V0 == V,!,
    rem_dup_dict(Vs,V,NVs,Names,NNames).
rem_dup_dict([V0|Vs],_V,NVs,[N|Names],NNames):-
    NVs = [V0|MoreVs],
    NNames = [N|MoreNames],
    rem_dup_dict(Vs,V0,MoreVs,Names,MoreNames).


%-------------------------------------------------------------------%
% exec_unif(+,+,-)                                                  %
% exec_unif(Unif_list,Copy_Unif,New_Unif)                           %
%  New_Unif is the result of eliminating from Unif_list all the     %
%  unnecessary unifications. Copy_Unif is used to check if the set  %
%  of unifications can succeed. We execute the unifications with    %
%  the copy at each step. If that fails, the set of unifications    %
%  will also fail.                                                  %
%-------------------------------------------------------------------%
exec_unif([],[],[]).
%-------------------------------------------------------------%
% If both terms are ground, the unification can be known to   %
% succeed or fail now and is not neccesary at run-time        %
%-------------------------------------------------------------%
exec_unif([_|Unif],[(L=R)|Unif2],NewUnif):-
    ground(L),
    ground(R),
    !,
    L == R,
    exec_unif(Unif,Unif2,NewUnif).
exec_unif([U|Unif],[(L=R)|Unif2],[U|NewUnif]):-
    var(L),
    var(R),
    !,
    L = R,
    exec_unif(Unif,Unif2,NewUnif).
%-------------------------------------------------------------%
% If only one of the terms is a varible we must be sure that  %
% the variable does not occur in the other term, as this would%
% avoid this program from ever finishing                      %
%-------------------------------------------------------------%
exec_unif([U|Unif],[(L=R)|Unif2],[U|NewUnif]):-
    var(R),
    !,
    varset(L,Vars),
    (\+ memberchk(R,Vars) ->
        L = R
    ;
        true),
    exec_unif(Unif,Unif2,NewUnif).
exec_unif([U|Unif],[(L=R)|Unif2],[U|NewUnif]):-
    var(L),
    !,
    varset(R,Vars),
    (\+ memberchk(L,Vars) ->
        L = R       
    ;
        true),
    exec_unif(Unif,Unif2,NewUnif).
exec_unif([U|Unif],[(L=R)|Unif2],[U|NewUnif]):-
    functor(L,Name,Arity),
    functor(R,Name,Arity),
    exec_N_unif(Arity,L,R),
    exec_unif(Unif,Unif2,NewUnif).
%-------------------------------------------------------------%
% We check if all the arguments are unifiable                 %
%-------------------------------------------------------------%
exec_N_unif(0,_,_).
exec_N_unif(N,L,R):-
    arg(N,L,ArgL),
    arg(N,R,ArgR),
    copy_term([(ArgL=ArgR)],Copy),
    exec_unif([(ArgL=ArgR)],Copy,_),
    N1 is N -1,
    exec_N_unif(N1,L,R).

%-------------------------------------------------------------------%
% put_keys(+,+,-)                                                   %
% put_keys(Unif_list,K,New_list)                                   %
%-------------------------------------------------------------------%
put_keys([],_,[]).
put_keys([Goal|Goals],K,[Goal:K|NewGoals]):-
    put_no_keys(Goals,NewGoals).

put_no_keys([],[]).
put_no_keys([Goal|Goals],[Goal:noinfo|NewGoals]):-
    put_no_keys(Goals,NewGoals).

%-------------------------------------------------------------------%
% error_predicate(+,+,+,+,-)                                        %
% error_predicate(Preds,Keys,N,Abs,Flag)                            %
%  Analises if any of the program predicates has been reduced to    %
% error. A predicate must be reduced to error only if there is a    %
% complete for it (it is used in any part of the program). In none  %
% of its clauses has been reduced to error (they have all been      %
% reduced to either failure or notreached) we must add a fail clause%
%-------------------------------------------------------------------%
error_predicate([],[],_,_,_).
error_predicate([Name/A|Ps],[Key|Keys],N,Abs,Flag):-
    \+current_fact(abs_ex(Name/A,_)),
    \+current_fact(clause_result(Key,nonerror)),
    \+current_fact(clause_result(Key,fact(_))),
    \+current_fact(clause_result(Key,bridge(_,_))),
    current_fact(complete(Key,Abs,_,_,_,_,_),_),
    !,
    Flag = yes,
    asserta_fact(abs_ex(Name/A,(error,N))),
%%      (\+current_fact(clause_result(Key,error))->
%%          asserta_fact(abs_ex(add_fail_clause,Name/A),_)
%%      ;
%%          true
%%      ),
    error_predicate(Ps,Keys,N,Abs,Flag).
error_predicate([_|Ps],[_|Keys],N,Abs,Flag):-
    error_predicate(Ps,Keys,N,Abs,Flag).

%-------------------------------------------------------------------%
% fail_predicate(+,+,-)                                             %
% fail_predicate(Preds,Keys,Flag)                                   %
%  Flag will have the value yes if any of the predicates of the     %
% program can be reduced to fail                                    %
%-------------------------------------------------------------------%
fail_predicate([],[],_).
fail_predicate([N/A|Ps],[Key|Keys],Flag):-
    (current_fact(abs_ex(N/A,(error,_))),
     current_fact(clause_result(Key,failure)) ->
        \+current_fact(clause_result(Key,fact(_))),
        \+current_fact(clause_result(Key,bridge(_,_))),
        \+current_fact(clause_result(Key,error)),
        \+current_fact(clause_result(Key,nonerror)),
        !,
        Flag = yes,
        asserta_fact(abs_ex(N/A,fail)),
        functor(Goal,N,A),
        (type_of_goal(exported,Goal) -> 
            asserta_fact(abs_ex(add_fail_clause,N/A),_)
        ;
            true
        ),
        retract_fact(abs_ex(N/A,(error,_))),
        fail_predicate(Ps,Keys,yes)).


fail_predicate([N/A|Ps],[Key|Keys],Flag):-
    \+current_fact(abs_ex(N/A,_)),
    (current_fact(clause_result(Key,failure)) ->
        \+current_fact(clause_result(Key,fact(_))),
        \+current_fact(clause_result(Key,bridge(_,_))),
        \+current_fact(clause_result(Key,error)),
        \+current_fact(clause_result(Key,nonerror)),
        !,
        Flag = yes,
        asserta_fact(abs_ex(N/A,fail)),
        functor(Goal,N,A),
        (type_of_goal(exported,Goal) -> 
            asserta_fact(abs_ex(add_fail_clause,N/A),_)
        ;
            true
        ),
        fail_predicate(Ps,Keys,yes)).
fail_predicate([_|Ps],[_|Keys],Flag):-
    fail_predicate(Ps,Keys,Flag).

%-------------------------------------------------------------------%
% true_predicate(+,+,-)                                             %
% true_predicate(Preds,Keys,Flag)                                   %
%  Flag will have the value yes if any of the predicates of the     %
% program can be reduced to true                                    %
%-------------------------------------------------------------------%
true_predicate([],[],_).
true_predicate([N/A|Ps],[_Key|Keys],Flag):-
    current_fact(abs_ex(N/A,_)),!,
    true_predicate(Ps,Keys,Flag).
true_predicate([_|Ps],[Key|Keys],Flag):-
    current_fact(clause_result(Key,nonerror)),!,
    true_predicate(Ps,Keys,Flag).
true_predicate([_|Ps],[Key|Keys],Flag):-
    current_fact(clause_result(Key,error)),!,
    true_predicate(Ps,Keys,Flag).
true_predicate([N/A|Ps],[Key|Keys],Flag):-
    findall(Key,current_fact(clause_result(Key,fact(Head))),L),
    L = [_],
    \+current_fact(clause_result(Key,bridge(Head,_))),
    functor(Goal,N,A),
    decide_orig_goal(Goal,Orig_Goal),
    \+type_of_goal(exported,Orig_Goal),
    !,
    Flag = yes,
    functor(Generic,N,A),
    current_fact(clause_result(Key,fact(Head))),
    generate_unif(Generic,Head,Unif_List),
    asserta_fact(abs_ex(N/A,(true,Generic,Unif_List))),
    true_predicate(Ps,Keys,yes).
true_predicate([N/A|Ps],[Key|Keys],Flag):-
    findall(Key,current_fact(clause_result(Key,bridge(_Head,_Body))),L),
    L = [_],
    \+current_fact(clause_result(Key,fact(_))),
    functor(Goal,N,A),
    decide_orig_goal(Goal,Orig_Goal),
    \+type_of_goal(exported,Orig_Goal),
    !,
    Flag = yes,
    functor(Generic,N,A),
    current_fact(clause_result(Key,bridge(Head,Body))),
    generate_unif(Generic,Head,Unif_List),
    asserta_fact(abs_ex(N/A,(true,Generic,(Unif_List,Body)))),
    true_predicate(Ps,Keys,yes).
true_predicate([_|Ps],[_|Keys],Flag):-
    true_predicate(Ps,Keys,Flag).

% entries cannot be reduced to true
%% is_entry(Name,A):-
%%      recorded_internal(entry_number,N,_),
%%      is_entry_N(N,Name,A).
%% 
%% is_entry_N(N,Name,A):-
%%      recorded_internal(N,entry(Name,_,H,_,_),_),
%%      functor(H,_,A).
%% is_entry_N(N,Name,A):-
%%      N > 0,
%%      N1 is N -1,
%%      is_entry_N(N1,Name,A).

%-----------------------------------------------------------------------
% this is necessary because if a predicate with clauses, whose heads do
% not unify with any call must keep at least a minimum clause (fail) that
% makes clear that the predicate has been defined (otherwise the system
% can rise a not_defined error
add_fail_clauses(Prog,NProg,Dict,NDict):-
    findall(N/A,
           (current_fact(abs_ex(add_fail_clause,N/A))),
           Preds),
    build_fail_clauses(Preds,Prog,NProg,Dict,NDict).

build_fail_clauses([],Prog,Prog,Dict,Dict):-!.
build_fail_clauses(Preds,Prog,NProg,Dict,NDicts):-
    build_each_fail_clause(Preds,NewClauses,NewDicts),
    append(Prog,NewClauses,NProg),
    append(Dict,NewDicts,NDicts).

build_each_fail_clause([],[],[]).
build_each_fail_clause([N/Arity|NN],[C|Cs],[D|Ds]):-
    functor(Head,N,Arity),
%% %% PBC: create_dict/2
%%      varset(Head,Vars),
%%      copy_term(Vars,Copy),
%%      numbervars(Copy,0,_),
%%      build_dict(Copy,Names),
    create_dict(Head,D),
    make_atom([N,Arity,1],Clid),
    C = clause(Head,[fail:noinfo]):Clid,
    build_each_fail_clause(NN,Cs,Ds).

%-------------------------------------------------------------------%
% simplify(+,+,-,-,+,-)                                             %
% simplify(clause,Rest,Rest2,Newbody,Dict,Dict2)                    %
%  Postprocess the program just after its first clause has been     %
% simplified. Both the first clause and the rest of the program     %
% may be modified.                                                  %
%-------------------------------------------------------------------%
%-------------------------------------------------------------%
% The clause stays the same and we record it is nonerror      %
%-------------------------------------------------------------%
simplify(clause(Head,Body),Rest,Rest,Body,D,D):-
    non_static(Head),!,
    predkey_from_sg(Head,Key),
    asserta_fact(clause_result(Key,nonerror)).

%-------------------------------------------------------------%
% The clause is a  fact                                       %         
%-------------------------------------------------------------%
simplify(clause(Head,[]),Cs,Cs,[],D,D):-
    !,
    predkey_from_sg(Head,Key),
    asserta_fact(clause_result(Key,fact(Head))).

%-------------------------------------------------------------%
% The clause starts with a cut. We check if we can eliminate  %
% other clauses for the same predicate                        %
%-------------------------------------------------------------%
simplify(clause(Head,[!]),RestIn,RestOut,
                          NewGoals,Dicts,DictsOut):-
    !,
    functor(Head,Name,Arity),
    eliminate(RestIn,RestOut,Dicts,DictsOut,Name,Arity,Head,Cut),
    get_predkey(Name,Arity,Key),
    (Cut == yes ->
        NewGoals = [!],
        asserta_fact(clause_result(Key,nonerror))
    ;
        NewGoals = [],
        asserta_fact(clause_result(Key,fact(Head)))).

simplify(clause(Head,[!|Goals]),RestIn,RestOut,
                          NewGoals,Dicts,DictsOut):-
    !,
    functor(Head,Name,Arity),
    eliminate(RestIn,RestOut,Dicts,DictsOut,Name,Arity,Head,Cut),
    get_predkey(Name,Arity,Key),
    (Cut == yes ->
        NewGoals = [!|Goals],
        asserta_fact(clause_result(Key,nonerror))
    ;
        NewGoals = Goals,
%%          (
        (NewGoals = [G:_Id]
%% ,
%%            predkey_from_Sg(Body,SgKey),
%%            \+ (recorded_internal(SgKey,clause(r,Body,_Vars_u,_K,_Body),_)))
        ->
            asserta_fact(clause_result(Key,bridge(Head,G)))
        ;
            asserta_fact(clause_result(Key,nonerror))
        )
    ).
%-------------------------------------------------------------%
% The clause is a failure                                      %         
%-------------------------------------------------------------%
simplify(clause(_Head,[Body:Id]),Cs,Cs,[Body:Id],D,D):-
    (Body == fail;
     Body == 'basiccontrol:fail'), 
    !. % nothing needs doing, already asserted failure!
%-------------------------------------------------------------%
% The clause is a bridge                                      %         
%-------------------------------------------------------------%
simplify(clause(Head,[Body:Id]),Cs,Cs,[Body:Id],D,D):-
%       Body \== fail, % already checked above
    !,
    predkey_from_sg(Head,Key),
    asserta_fact(clause_result(Key,bridge(Head,Body))).

%-------------------------------------------------------------%
% The clause stays the same and we record it is nonerror      %
%-------------------------------------------------------------%
simplify(clause(Head,Body),Rest,Rest,Body,D,D):-
    predkey_from_sg(Head,Key),
    asserta_fact(clause_result(Key,nonerror)).

%-------------------------------------------------------------------%
% body_result(+,+,+,-)                                              %
% body_result(Flag,Head,SimpBody,NewSimpBody)                       %
%  Postprocesses the clause(Head,SimpBody) and Returns NewSimpBody  %
% according to the value of Flag                                    %
%-------------------------------------------------------------------%
body_result(fail,Head,SimpBlist,SimpBody):-
    !,
    decide_study_side_effects(SimpBlist,SimpBody),
    predkey_from_sg(Head,Key),
    ((SimpBody = (['basiccontrol:fail':_]);
         SimpBody = ([fail:_])) ->
        asserta_fact(clause_result(Key,failure))
     ;
        asserta_fact(clause_result(Key,error))).
        
body_result(error,Head,SimpBody,SimpBody):-
    predkey_from_sg(Head,Key),
    asserta_fact(clause_result(Key,error)).

%% body_result(nonerror,_Head,[SimpBody:Id],[SimpBody:Id]):-
%%      !,
%% %%         predkey_from_sg(Head,Key),
%% %%         recorda_internal(Key,bridge(Head,SimpBody),_).
%%      true.
%% 
%% body_result(nonerror,Head,SimpBody,SimpBody):-
%%         predkey_from_sg(Head,Key),
%%         recorda_internal(Key,nonerror,_).

body_result(nonerror,_Head,SimpBody,SimpBody).

%-------------------------------------------------------------------%
% generate_unif(+,+,-)                                              %
% generate_unif(Goal,Head,GoalList)                                 %
%  Builds in GoalList a minimum list of unifications Head introdu-  %
% ces for a generic Goal.                                           %
%-------------------------------------------------------------------%
generate_unif(Goal,Head,GoalList):- 
    functor(Goal,_,A),          
    g_unif(A,Goal,Head,[],Goals),
    post(Goals,Goals,GoalList).
%-------------------------------------------------------------%
% first we generate one unification per argument              %
%-------------------------------------------------------------%
g_unif(0,_,_,GL,GL).
g_unif(N,Goal,Head,Ac,GL):-
    arg(N,Goal,ArgNG),
    arg(N,Head,ArgNH),
    N1 is N-1,
    g_unif(N1,Goal,Head,[(ArgNG = ArgNH)|Ac],GL).
%-------------------------------------------------------------%
% We eliminate the  unifications that generate no bindigs on  %
% the terms in the calling goal                               %
%-------------------------------------------------------------%
post([],L,L).
post([(L=R)|Rest],Ac,Result):-
    var(R),
    !,
    R  = L,
    clean(Rest,NewRest,R),
    left_to(R,Ac,Ac2),
    post(NewRest,Ac2,Result).
post([_|Rest],Ac,Result):-
    post(Rest,Ac,Result).

clean([],[],_).
clean([(_=R)|Rest],NewRest,R2):-
    R2 == R,
    !,
    clean(Rest,NewRest,R2).
clean([Unif|Rest],[Unif|NewRest],R2):-
    clean(Rest,NewRest,R2).

left_to(R,[(L2 = R2)|Rest],[(L2 = R2)|More]):-
    R \== R2,
    !,
    left_to(R,Rest,More).
left_to(_,[_|Rest],Rest).


%-------------------------------------------------------------------%
% eliminate(+,-,+,-,+,+,+,-)                                        %
% eliminate(Cs,NewCs,Ds,NewDs,Name,Arity,H_Cut,Cut)                 %
%   NewCs,NewDs is the transformed program after eliminating those  %
% clauses that belong to Name/Arity and whose head is included in   %
% H_Cut. Cut is yes whenever we have found a clause for Name/Arity  %
% that cannot be eliminated.                                        %
%-------------------------------------------------------------------%
eliminate([],[],[],[],_,_,_,_).
eliminate([clause(Head,Body):K|Cls],NewCls,[D|Ds],NewDs,
                                          Name,Arity,H_Cut,Cut):-
    functor(Head,Name,Arity),
    !,
    (ask(Head,H_Cut) ->
        NewCls = MoreCls,
        NewDs  = MoreDs
    ;
        NewCls = [clause(Head,Body):K|MoreCls],
        NewDs  = [D|MoreDs],
        Cut    = yes),
    eliminate(Cls,MoreCls,Ds,MoreDs,Name,Arity,H_Cut,Cut).
eliminate([C|Cs],[C|NewCs],[D|Ds],[D|NewDs],Name,Arity,H_Cut,Cut):-
    eliminate(Cs,NewCs,Ds,NewDs,Name,Arity,H_Cut,Cut).

decide_study_side_effects(SimpBlist,SimpBody):-
    current_pp_flag(pres_inf_fail,P),
    (P == on ->
        SimpBody = SimpBlist
    ;
        study_side_effects(SimpBlist,SimpBody)
    ).
%-------------------------------------------------------------------%
% study_side_effects(+,-)                                           %
% study_side_effects(Goals,NewGoals)                                %
%  NewGoals is the result of eliminating from Goals the goals that  %
% are not necessary as Goals has fail as last element.              %
%-------------------------------------------------------------------%
study_side_effects([(fail:K)],[(fail:K)]).
study_side_effects([('basiccontrol:fail':K)],[('basiccontrol:fail':K)]).
%-------------------------------------------------------------%
% Cuts are considered side_effects                            %
%-------------------------------------------------------------%
study_side_effects([!|Body],[!|NewBody]):-
    study_side_effects(Body,NewBody).
%-------------------------------------------------------------%
% This clause is for parallel goals                           %
%-------------------------------------------------------------%
study_side_effects([[G:K|Gs]|Body],NewGoals):-
    study_side_effects(Body,NewBody),
    (NewBody = [(fail:_)] ->
        parallel_side_effects([G:K|Gs],NewP),
        (NewP == [] ->
            NewGoals = [(fail:K)]
        ;
            NewGoals = NewP)
    ;
        NewGoals = [[G:K|Gs]|NewBody]).
%-------------------------------------------------------------%
% Rest of goals                                               %
%-------------------------------------------------------------%
study_side_effects([(B:K)|Body],[(NB:K)|NewBody]):-
    study_side_effects(Body,Result),
    ((Result = [(fail:_)];Result = [('basiccontrol:fail':_)]), 
    side_effect_free(B)->
        NB = fail,
        NewBody=[]
    ;
        NB = B,
        NewBody = Result
    ).

%-------------------------------------------------------------------%
% parallel_side_effects(+,-)                                        %
% parallel_side_effects(Parall_Goals,NewParall_Goals)               %
%  NewParall_Goals is the result of eliminating from Parall_Goals   %
% all the goals without side-effects                                %
%-------------------------------------------------------------------%
parallel_side_effects([],[]).
parallel_side_effects([G:_|Gs],PGs):-
    side_effect_free(G),!,
    parallel_side_effects(Gs,PGs).
parallel_side_effects([(G:K)|Gs],[(G:K)|PGs]):-
    parallel_side_effects(Gs,PGs).

%-------------------------------------------------------------------%
% side_effect_free(+)                                               %
% side_effect_free(Goal)                                            %
%  Succeeds if the Goal is guaranteed not to perform any            %
% side_effects. This can only be guaranteed if side_effects         %
% analysis has been performed.                                      %
% Cuts cannot be eliminated directly (even if they do not have      %
% direct side_effects                                               %
%-------------------------------------------------------------------%

side_effect_free(!):-!, fail.
side_effect_free(Goal):-
    get_info(seff,pred,_Key,Goal,Info),
    Info == pure.

:- pred minimal_unif(+Goal,+Result,-Unif_List) # "@var{Unif_List} is
    the minimal set of unifications required in order to make @var{Goal}
    unify with @var{Result}. @var{Result} is assumed to be an instance 
    of @var{Goal}.".

minimal_unif(Goal,Result,Unif_List):-
    generate_unif(Goal,Result,Unif_List0),
    copy_term(Unif_List0,Unif_List0_Copy),
    exec_unif(Unif_List0,Unif_List0_Copy,Unif_List).

