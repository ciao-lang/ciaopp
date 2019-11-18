/*                  Copyright (C)1990-2002 UPM-CLIP                      */

:- module(re_analysis,
    [ 
%%        adapt_info_annotation/13,
%%        analyze_ann_clauses/1,
%%        delete_old_info_annotation/2,
      renaming/3,
      update_ai_info_case/4
    ],
    [assertions, datafacts]).

%------------------------------------------------------------------------%
%                                                                        %
%                          started: April 94                             %
%                       last modified: March 14 96                       %
%                  programmed: German Puebla Sanchez                     %
%                                                                        %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% This file contains predicates which avoid a second run of the analyser %
% both after annotation and specialization.                              %
%------------------------------------------------------------------------%

:- doc(bug,"1. REMEMBER_AMPERSANDS_ARE_JUST_META_CALLS").
:- doc(bug,"2. Remember to revise meta_call treatment and also $var.").
:- doc(bug,"3. The predicates here are not used in every place that
    is needed, yet. Also, some predicates have not been ported, yet.").

:- use_module(ciaopp(p_unit/program_keys),
    [decode_litkey/5, decode_clkey/4, get_predkey/3, predkey_from_sg/2]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(spec(spec), [versions/2]).
:- use_module(ciaopp(plai/plai_db), [memo_lub/5, complete/7, memo_table/6, del_parent/4, get_memo_table/7]).
:- use_module(ciaopp(plai/fixpo_ops), [fixpoint_id/1]).
:- use_module(ciaopp(plai/domains), [call_to_entry/10]).
:- use_module(ciaopp(plai/plai_db), [complete_parent/2]).

:- use_module(library(lists), [member/2]).
:- use_module(library(terms), [copy_args/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(ciaopp(pool), [there_is_delay/0]).

%:- include(re_analysis_extra).

%-------------------------------------------------------------------------
% renaming(G0,Key,G1)
% clauses of predicate G0 have been renamed to G1 and (G0:- G1):Key added
% the and-or graph is changed accordingly
%-------------------------------------------------------------------------

renaming(G0,ClKey,G1:PoKey):-
    functor(G0,F0,A0),
    functor(Sg0,F0,A0), % TODO: Sg0 seems unnecessary (it is unified later)
    get_predkey(F0,A0,SgKey0),
    predkey_from_sg(G1,SgKey1),
    varset((G0,G1), Vars), % suposedly G0 and G1 have the same Vars
    % complete of G0 changes to a new Id
    retract_fact(complete(SgKey0,AbsInt,Sg0,Proj,Prime,Id,Parents)),
    fixpoint_id(New),
    assertz_fact(complete(SgKey0,AbsInt,Sg0,Proj,Prime,New,Parents)),
    % forward links to G0's complete changed to the new Id
    memo_table_new_child(AbsInt,Id,New),
    % obtain Call and Succ of the clause
    varset(Sg0,Sv0),
    ClauseKey = not_provided, % TODO: fix it, add clause key? (JF)
    call_to_entry(AbsInt,Sv0,Sg0,Vars,G0,ClauseKey,[],Proj,Call,_),
    each_call_to_entry(Prime,AbsInt,Sv0,Sg0,Vars,G0,ClauseKey,[],Succs),
    % memo table for the new clause
    assertz_fact( memo_table(PoKey,AbsInt,New,Id,Vars,[Call]) ),
    assertz_fact( memo_table(ClKey,AbsInt,New,no,Vars,Succs) ),
    % complete for G1 has the old Id of G0
    assertz_fact( complete(SgKey1,AbsInt,G1,Call,Succs,Id,[(PoKey,New)])),
    fail.
renaming(_H,_K,_B).

memo_table_new_child(AbsInt,Id,New):-
    retract_fact(memo_table(Key,AbsInt,IdX,Id,VarsX,CallX)),
    assertz_fact(memo_table(Key,AbsInt,IdX,New,VarsX,CallX)),
    fail.
memo_table_new_child(_AbsInt,_Id,_New).

each_call_to_entry([],_AbsInt,_Sv0,_Sg0,_Vars,_G0,_K,_Fv,[]).
each_call_to_entry([Prime|Primes],AbsInt,Sv0,Sg0,Vars,G0,K,Fv,[Succ|Succs]):-
    call_to_entry(AbsInt,Sv0,Sg0,Vars,G0,K,Fv,Prime,Succ,_),
    each_call_to_entry(Primes,AbsInt,Sv0,Sg0,Vars,G0,K,Fv,Succs).

%-------------------------------------------------------------------------
% The way the information is updated after specialization is different when
% the analysis is for delay or not. The first (simpler) case is treated
% by update_ai_info_delay.
%-------------------------------------------------------------------------
update_ai_info_case(Prog,Dicts,NProg,NDicts):-
    there_is_delay,!,
    update_ai_info_delay(Prog,Dicts,NProg,NDicts).
update_ai_info_case(Prog,Dicts,NProg,NDicts):-
    update_ai_info(Prog,Dicts,NProg,NDicts).
update_ai_info_delay([],[],[],[]).
update_ai_info_delay([(directive(D):Id)|Cs],[Dict|Dicts],
                  [(directive(D):Id)|SCs],[Dict|NDicts]):-
    update_ai_info_delay(Cs,Dicts,SCs,NDicts).

update_ai_info_delay([(clause(Head,Body):Id)|Cs],[Dict|Dicts],
               [(clause(NHead,NewBody):NId)|SCs],[NDict|NDicts]):-
    functor(Head,Name,A),
    decode_clkey(Id,N,A,C),
    make_atom([Name,A,C],NId),
    update_ai_delay(N,Name,A,Body,NewBody,Head,NHead,Dict,NDict,Id,NId),
    update_ai_info_delay(Cs,Dicts,SCs,NDicts).

update_ai_delay(Name,Name,_,Body,Body,Head,Head,Dict,Dict,Id,Id):-!.
update_ai_delay(N,Name,A,Body,NewBody,Head,NHead,Dict,NDict,Id,NId):-
    copy_term((Head,Body,Dict),(NHead,NBody,NDict)),
    get_predkey(N,A,Key),
    get_predkey(Name,A,NewKey),
    copy_completes(Key,NewKey,Name,A),
    update_ai_delay_case(NBody,NewBody,Name,Id,NId).

copy_completes(_,NewKey,_Name,_):-
    current_fact(complete(NewKey,_,_,_,_,_,_)),!.
copy_completes(Key,NewKey,Name,A):-
    current_fact(complete(Key,AbsInt,Goal,A2,A3,A4,A5)),
    functor(NewGoal,Name,A),
    copy_args(A,Goal,NewGoal),
    asserta_fact(complete(NewKey,AbsInt,NewGoal,A2,A3,A4,A5)),
    fail.
copy_completes(_,_,_,_).

update_ai_delay_case(true,true,_,_,_):-!.
update_ai_delay_case(NBody,NewBody,Name,Id,NId):-
    update_ai_delay_body(NBody,Name,NewBody),
    copy_memo_table(Id,NId).

update_ai_delay_body((Goal,Goals),Name,(NGoal,NGoals)):-!,
    update_ai_delay_body(Goal,Name,NGoal),
    update_ai_delay_body(Goals,Name,NGoals).
%% update_ai_delay_body((Goal&Goals),Name,(NGoal&NGoals)):-!,
%%      update_ai_delay_body(Goal,Name,NGoal),
%%      update_ai_delay_body(Goals,Name,NGoals).
update_ai_delay_body(Goal,Name,NGoal):-
    update_ai_delay_goal(Goal,Name,NGoal).

update_ai_delay_goal(!,_,true).
update_ai_delay_goal(true,_,true).
update_ai_delay_goal(Goal:noinfo,_,Goal:noinfo):-!.
update_ai_delay_goal(Goal:'$bottom',_,Goal:'$bottom'):-!.
update_ai_delay_goal(Goal:OldKey,Name,Goal:NewKey):-
    decode_litkey(OldKey,_,A,C,L),
    make_atom([Name,A,C,L],NewKey),
    copy_memo_table(OldKey,NewKey).
    
copy_memo_table(OldKey,NewKey):-
    current_fact(memo_table(OldKey,AbsInt,Number,Son,Vars,Info1)),
    asserta_fact(memo_table(NewKey,AbsInt,Number,Son,Vars,Info1)),
    fail.
copy_memo_table(_,_).

%-------------------------------------------------------------------%
% update_ai_info(+,+,-,-)                                           %
% update_ai_info(Program,Dicts,Updated_program,Updated_Dicts)       %
%  This predicate updates both the program and the data-base.       %
% This way the abstract information is valid, and no new analysis   %
% is needed after program specialization and simplification.        %
%-------------------------------------------------------------------%
update_ai_info([],[],[],[]).
update_ai_info([(directive(D),Id)|Cs],[Dict|Dicts],
                  [(directive(D),Id)|SCs],[Dict|NDicts]):-
    update_ai_info(Cs,Dicts,SCs,NDicts).

update_ai_info([(clause(Head,Body):Id)|Cs],[Dict|Dicts],
               [(clause(NHead,NewBody):NId)|SCs],[NDict|NDicts]):-
    functor(Head,Name,A),
    decode_clkey(Id,N,A,C),
    make_atom([Name,A,C],NId),
    update_ai(N,Name,A,Body,NewBody,Head,NHead,Dict,NDict,Id,NId),
    update_ai_info(Cs,Dicts,SCs,NDicts).

update_ai(Name,Name,_,Body,Body,Head,Head,Dict,Dict,Id,Id):-!,
    delete_memo_lub(Body).
update_ai(N,Name,A,Body,NewBody,Head,NHead,Dict,NDict,Id,NId):-
    copy_term((Head,Body,Dict),(NHead,NBody,NDict)),
    get_predkey(N,A,Key),
    get_predkey(Name,A,NewKey),
    update_completes(Key,NewKey,Name,Completes),
    update_ai_case(NBody,NewBody,Key,Name,Completes,Id,NId).

update_ai_case(true,true,_,_,_,_,_):-!.
update_ai_case(NBody,NewBody,Key,Name,Completes,Id,NId):-
    ( var(Completes) ->
        complete_numbers(Key,Name,Completes)
    ;
        true),
    update_ai_body(NBody,Name,Completes,NewBody),
    rename_memo_table(Completes,Id,NId).

delete_memo_lub(!):-!.
delete_memo_lub(true):-!.
delete_memo_lub((Goal,Goals)):-!,
    delete_memo_lub(Goal),
    delete_memo_lub(Goals).
%% delete_memo_lub(_ &Goals):-!,
%%      delete_memo_lub(Goals).
delete_memo_lub(_:noinfo):-!.
delete_memo_lub(_:Key):-
    current_fact(memo_lub(Key,_,_,_,_),Ref),!,
    erase(Ref).
delete_memo_lub(_).

update_ai_body((Goal,Goals),Name,Completes,(NGoal,NGoals)):-!,
    update_ai_body(Goal,Name,Completes,NGoal),
    update_ai_body(Goals,Name,Completes,NGoals).
%% update_ai_body((Goal&Goals),Name,Completes,(NGoal&NGoals)):-!,
%%      update_ai_body(Goal,Name,Completes,NGoal),
%%      update_ai_body(Goals,Name,Completes,NGoals).
update_ai_body(Goal,Name,Completes,NGoal):-
    update_ai_goal(Goal,Name,Completes,NGoal).

update_ai_goal(!,_,_,!).
update_ai_goal(true,_,_,true).
update_ai_goal(Goal:noinfo,_,_,Goal:noinfo):-!.
update_ai_goal(Goal:'$bottom',_,_,Goal:'$bottom'):-!.
update_ai_goal(Goal:OldKey,Name,Completes,Goal:NewKey):-
    decode_litkey(OldKey,_,A,C,L),
    make_atom([Name,A,C,L],NewKey),
    rename_memo_table(Completes,OldKey,NewKey).
    
rename_memo_table(Completes,OldKey,NewKey):-
    member(Number,Completes),
    current_fact(memo_table(OldKey,AbsInt,Number,Son,Vars,Info1),Ref1),
    erase(Ref1),
    asserta_fact(memo_table(NewKey,AbsInt,Number,Son,Vars,Info1),_),
    fail.
rename_memo_table(_,_,_).

complete_numbers(Key,Name,Completes):-
    current_fact(versions(Key,V)),
    member((List,Name),V),
    second_components(List,Completes).

second_components([],[]).
second_components([(_,X2)|More],[X2|Others]):-
    second_components(More,Others).

%-------------------------------------------------------------------------
% As we try to update complete for each clause, the first clause checks 
% if it is already done. The second clause really does the updating.
update_completes(_,NewKey,_,_):-
    current_fact(complete(NewKey,_,_,_,_,_,_),_),!.
update_completes(Key,NewKey,Name,Completes):-
    complete_numbers(Key,Name,Completes),
    update_each_complete(Completes,Key,NewKey,Name).

update_each_complete([],_,_,_).
update_each_complete([C|Cs],Key,NewKey,Name):-
    current_fact(complete(Key,AbsInt,Goal,A1,A2,C,A4),Ref),
    erase(Ref),
    functor(Goal,_,Arity),
    functor(NewGoal,Name,Arity),
    copy_args(Arity,Goal,NewGoal),
    asserta_fact(complete(NewKey,AbsInt,NewGoal,A1,A2,C,A4)),
    update_each_complete(Cs,Key,NewKey,Name).
