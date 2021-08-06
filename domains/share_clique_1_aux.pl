:- module(share_clique_1_aux,
    [amgu_clique_1/4,
     star_clique_1/2,
     nrel_clique_1/3,
     split_list_of_lists_singleton/3,
     share_clique_1_normalize/2,
     share_clique_1_normalize/4,
 % for running benchmarks
     card_cliques_1/2
    ],
       [assertions, isomodes]).

:- doc(author, "Jorge Navas").

%------------------------------------------------------------------------%
% This file contains the amgu and auxiliary functions for the            |
% 1-clique-sharing domain by J.Navas, F.Bueno and M.Hermenegildo.        |
%------------------------------------------------------------------------%

:- use_module(library(sets), [ord_union/3, ord_subset/2, ord_delete/3]).
:- use_module(library(lsets), [merge_list_of_lists/2, sort_list_of_lists/2]).
:- use_module(library(lists), [length/2, delete/3]).
:- use_module(library(aggregates), [bagof/3]).
:- use_module(domain(sharing_clique), [
    abs_sort/2, widen/4
]).
:- use_module(domain(share_clique_aux), 
    [ widen/1,
      amgu_rel_non_rel_info/7,
      amgu_sharing_part/4,
      ord_union_w/3,
      regularize/2,
      minimum_cardinality/1,
      check_threshold/2,
      longest_candidate/5,
      comb/3,
      intersect_all/2,
      number_of_subsets/2
    ]).
:- use_module(domain(share_amgu_sets), 
    [split_list_of_lists/4,
     ord_subset_lists_with_list/2,
     nosublist_list_of_lists/3,
     intersection_lists_with_list/3]).
:- use_module(domain(share_amgu_aux)).
:- use_module(library(messages), [error_message/1]).    

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%          ABSTRACT UNIFICATION for 1-Clique-Sharing domain              |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% amgu_clique_1(+,+,+,-)                                                 |
% amgu_clique_1_(X,T,State,AMGU)                                         |
% amgu_clique_1(x=t,(cl,sh)) =                                           |
%   (cl, \sh_xt U (sh_x* bin sh_t*))             if cl_x = cl_t = empty  |
%    \nrel^{1-c}(xt,(cl,sh)                      if cl_x = sh_x = empty  |
%                                                or cl_t = sh_t = empty  | 
%   \nrel^{1-c}(xt,(cl,sh) U^w                                           |
%    singleton(clsh)                             otherwise               |
% where:                                                                 |
%        clsh = {U (cl_x U cl_t U sh_x U sh_t)}                          |
%                                                                        |
%                          | (\emptyset,{clsh})    if |clsh| = 1         |
%        singleton(clsh) = |                                             |
%                          | ({clsh},\emptyset)    otherwise             |
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
:- push_prolog_flag(discontiguous_warnings,off).

amgu_clique_1(X,T,ASub,AMGU):-           
    widen(amgu),!,
    amgu_clique_1(X,T,ASub,not,AMGU).
amgu_clique_1(X,T,(Cl,Sh),NewCall,AMGU):-           
    amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),
                          Irrel_Sh_xt),!,
    ( (Cl_x = [], Cl_t = []) ->
       ( NewCall == not ->
         ExtraInfo = (Irrel_Sh_xt,Sh_x,Sh_t),
         sharing_clique:widen(amgu_clique_1,(Cl,Sh),ExtraInfo,New_ASub),
         amgu_clique_1(X,T,New_ASub,yes,AMGU)
       ;         
         amgu_sharing_part(Irrel_Sh_xt,Sh_x,Sh_t,AMGU_sh),
         AMGU = (Cl,AMGU_sh)
       )           
    ;
       ( ((Cl_x = [], Sh_x = []) ; (Cl_t = [], Sh_t = [])) -> 
           nrel_clique_1(V_xt,(Cl,Sh),AMGU)
       ;
           nrel_clique_1(V_xt,(Cl,Sh),Irrel_SH_xt),
           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
           ord_union(Cl_x,Cl_t,Cl_xt),
           ord_union(Sh_x,Sh_t,Sh_xt),
           merge_list_of_lists(Cl_xt,Cl_var),
           merge_list_of_lists(Sh_xt,Sh_var),
           ord_union(Cl_var,Sh_var,ClSh),
           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
           singleton(ClSh,ClSh0),
           ord_union_w(Irrel_SH_xt,ClSh0,AMGU)
           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    
%              one(Sh_xt,Sing_Sh_xt),
%              ord_union_w(AMGU1,([],Sing_Sh_xt),AMGU)
       )
       ).

amgu_clique_1(X,T,(Cl,Sh),AMGU):-           
    widen(off),!,
    amgu_rel_non_rel_info(X,T,V_xt,(Cl,Sh),(Cl_x,Sh_x),(Cl_t,Sh_t),
                          Irrel_Sh_xt),
    ( (Cl_x = [], Cl_t = []) ->
       star(Sh_x,S_Sh_x),
       star(Sh_t,S_Sh_t),
       bin_union(S_Sh_x,S_Sh_t,BinUnion_xt),
       split_list_of_lists(V_xt,Sh,_,Irrel_Sh_xt),  
       ord_union(Irrel_Sh_xt,BinUnion_xt,AMGU_Sh),   
       AMGU = (Cl,AMGU_Sh)
    ;
       ( ((Cl_x = [], Sh_x = []) ; (Cl_t = [], Sh_t = [])) -> 
           nrel_clique_1(V_xt,(Cl,Sh),AMGU)
       ;
           nrel_clique_1(V_xt,(Cl,Sh),Irrel_SH_xt),
           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
           ord_union(Cl_x,Cl_t,Cl_xt),
           ord_union(Sh_x,Sh_t,Sh_xt),
           merge_list_of_lists(Cl_xt,Cl_var),
           merge_list_of_lists(Sh_xt,Sh_var),
           ord_union(Cl_var,Sh_var,ClSh),
           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
           singleton(ClSh,ClSh0),
           ord_union_w(Irrel_SH_xt,ClSh0,AMGU)
           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    
%              one(Sh_xt,Sing_Sh_xt),
%              ord_union_w(AMGU1,([],Sing_Sh_xt),AMGU)
       )
       ).

:- pop_prolog_flag(discontiguous_warnings).
:- pop_prolog_flag(multi_arity_warnings).

singleton([],([],[])):-!.
singleton([S],([],[[S]])):-!.
singleton(S,([S],[])).

one([],[]).
one([[S]|Ss],[[S]|Res]):-!,
    one(Ss,Res).
one([_|Ss],Res):-!,
    one(Ss,Res).

%------------------------------------------------------------------------%
%                 STAR UNION FOR 1-Clique-Sharing domain                 | 
%------------------------------------------------------------------------%
% star_clique_1(+,-)                                                     |
% star_clique_1(Xss,Star)                                                |
%                        | Sh*                               if Cl= []   | 
%   star_{1c}((Cl,Sh)) = |                                               |
%                        | singleton(clsh) U^w                           |
%                          (\emptyset, one(Sh))              otherwise(*)|
% (*) REMARK: Cl must be regularized and Sh must be minimal.             |
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
:- push_prolog_flag(discontiguous_warnings,off).

star_clique_1(SH,SH_s):-
    widen(amgu),!,
    star_clique_1(SH,not,SH_s).
star_clique_1(([],Sh),NewCall,SH_s):-!,
    (  NewCall == not ->
       ExtraInfo = ([],Sh,[[_]]),
       sharing_clique:widen(amgu_clique_1,([],Sh),ExtraInfo,New_ASub),           
       star_clique_1(New_ASub,yes,SH_s)
    ;  
       star(Sh,Sh_s),
       SH_s = ([],Sh_s)
    ).
star_clique_1((Cl,Sh),_,SSH):-!,
    regularize(Cl,Cl_reg),
    minimize_clique_1(Sh,Cl_reg,Sh_min),
    merge_list_of_lists(Cl_reg,Cl_Vars),
    merge_list_of_lists(Sh_min,Sh_Vars),
    ord_union(Cl_Vars,Sh_Vars,ClSh),
    singleton(ClSh,SSH1),
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    one(Sh_min,Sing_Sh),
%       one(Cl_reg,Sing_Cl),
%       ord_union(Sing_Sh,Sing_Cl,Sing),
    ord_union_w(SSH1,([],Sing_Sh),SSH).

% widen(off)
star_clique_1(([],[]),([],[])).
star_clique_1(([],Sh),SH):-
    !,star(Sh,SSh),
    normalize_clique_1(([],SSh),100,3,SH).
star_clique_1((Cl,Sh),SSH):-
    regularize(Cl,Cl_reg),
    minimize_clique_1(Sh,Cl_reg,Sh_min),
    merge_list_of_lists(Cl_reg,Cl_Vars),
    merge_list_of_lists(Sh_min,Sh_Vars),
    ord_union(Cl_Vars,Sh_Vars,ClSh),
    singleton(ClSh,SSH1),
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    one(Sh_min,Sing_Sh),
%       one(Cl_reg,Sing_Cl),
%       ord_union(Sing_Sh,Sing_Cl,Sing),
    ord_union_w(SSH1,([],Sing_Sh),SSH).

:- pop_prolog_flag(discontiguous_warnings).
:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
%            NON-RELEVANT INFORMATION FOR 1-Clique-Sharing domain        |
%------------------------------------------------------------------------%
% nrel_clique_1(+,+,-)                                                   |
% nrel_clique_1(Vars,SH,Irrel)                                           |
%  \rel^{1c}(t,(cl,sh)) = (\one(R),\sh_t)                                |
% where:                                                                 |
%    \one(cl) = {c | c\in cl, |cl| > 1}                                  |
%     R = {s | c \in cl, s = c\t}                                        | 
%------------------------------------------------------------------------%
nrel_clique_1(Vars,(Cl,Sh),Irrel):-
    delete_vars_from_list_of_lists_no_sing(Vars,Cl,Irrel_Cl_vars),
    split_list_of_lists(Vars,Sh,_,Irrel_Sh_vars),   
    Irrel = (Irrel_Cl_vars,Irrel_Sh_vars).

%------------------------------------------------------------------------%
%               NORMALIZATION for 1-Clique-Sharing domain                |  
%------------------------------------------------------------------------%
% share_clique_1_normalize(+,-)                                          |
% share_clique_1_normalize(SH,SH1)                                       |
%------------------------------------------------------------------------%
% The specification of the following predicates and the rest of          |
% predicates not defined here are in share_clique_aux.pl                 |
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).        
share_clique_1_normalize(CL,NCL):-
    minimum_cardinality(M),
    share_clique_1_normalize(CL,100,M,NCL).

%------------------------------------------------------------------------%
% REMARK: This interface can only be used directly by predicates which   |
% need the normalization for correctness (i.e. extend, less_or_equal,..) |
%------------------------------------------------------------------------%
share_clique_1_normalize('$bottom',_,_,'$bottom').
share_clique_1_normalize((Cl,Sh),Th,M,(Cl2,Sh2)):-
    regularize(Cl,Cl1), 
    minimize_clique_1(Sh,Cl1,Sh1),
    normalize_clique_1((Cl1,Sh1),Th,M,(Cl2,Sh2)).
:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
% minimize_clique_1(+,+,-)                                               |
% minimize_clique_1(Sh,Cl,NewSh)                                         |
%------------------------------------------------------------------------%
% NewSh = Sh \ {s| s \in Sh, s \subseteq Cl, |s| = 1}                    |
%------------------------------------------------------------------------% 
minimize_clique_1([],_,[]).
minimize_clique_1([[Sh]|Shs],Cl,[[Sh]|Res]):-!,
    minimize_clique_1(Shs,Cl,Res).
minimize_clique_1([Sh|Shs],Cl,Sh1):-
    ord_subset_lists_with_list(Cl,Sh),!,
    minimize_clique_1(Shs,Cl,Sh1).
minimize_clique_1([Sh|Shs],Cl,[Sh|Res]):-!,
    minimize_clique_1(Shs,Cl,Res).    

:- push_prolog_flag(multi_arity_warnings,off).        
% normalize_clique_1/4: Th is between [0,100]
normalize_clique_1(SH,T,M,SH1):-
    check_threshold(T,NT),
    check_minimum(M),
    normalize_clique_1(SH,NT,M,SH1,_).

% normalize_clique_1/5: Th is between [0.0,1.0]
normalize_clique_1((Cl,Sh),Th,M,SH1,Continue):- 
    process_candidate_clique_1((Cl,Sh),Th,M,SH,Continue),!,
    ( var(Continue) ->   
      normalize_clique_1(SH,Th,M,SH1,Continue)
    ; 
      Continue = not,    
      SH1 = (Cl,Sh)
    ).
:- pop_prolog_flag(multi_arity_warnings).

process_candidate_clique_1((Cl,Sh),Th,M,SH,_):- 
    longest_candidate(Sh,M,CardCand,Cand,Info),
    Info = yes,
    sets_in_sharing(Sh,Cand,CardCandSh,CandSh),
    number_sets_in_cliques_1(Cl,Cand,CardCandCl),
    ( is_powerset_clique_1(CardCand,CardCandSh,CardCandCl,Th) ->
      update_clique_1(Cand,(Cl,Sh),CandSh,SH)       
    ;
      fail 
    ).
process_candidate_clique_1(SH,_,_,SH,not).  

is_powerset_clique_1(CardCand,CardCandSh,CardCandCl,Threshold):- 
    number_of_subsets(CardCand,CardPws),
    Limit is Threshold * (CardPws - CardCand),
    TotalSubsets is CardCandSh + CardCandCl,
    TotalSubsets >= Limit.

%------------------------------------------------------------------------%
% update_clique_1(Cand,SH,CandSh,NewSH)                                  |
% update_clique_1(+,+,+,-)                                               |
% Removes sharing groups of Sh that are included in CandSh and           |
% regularizes the clique part removing all redundant cliques with CandSh |
%------------------------------------------------------------------------%
update_clique_1(Cand,(Cl,Sh),CandSh,SH):-
    % Removes set-sharing included in the new clique        
    delete_list_of_lists_no_singleton(Sh,CandSh,Sh1),
    % Removes subcliques of the new clique        
    nosublist_list_of_lists(Cl,Cand,Cl1), 
    sharing_clique:abs_sort(([Cand|Cl1],Sh1),SH).
 
delete_list_of_lists_no_singleton(Sh,[],Sh0):- !,
    delete(Sh,[],Sh0).
delete_list_of_lists_no_singleton(Sh,[[_]|Ss],Sh1):-
    !,
    delete_list_of_lists_no_singleton(Sh,Ss,Sh1).
delete_list_of_lists_no_singleton(Sh,[S|Ss],Sh1):-
    delete(Sh,S,Sh0),!,
    delete_list_of_lists_no_singleton(Sh0,Ss,Sh1).
%delete_list_of_lists_no_singleton(Sh,_,Sh).

%------------------------------------------------------------------------%
% sets_in_sharing(Sh,Cand,Card,Pw).                                      |  
% sets_in_sharing(+,+,-,-)                                               |
%------------------------------------------------------------------------%
% Pw is a list of lists that consists of sharing groups of Sh that are   |
% subset of Cand. Singleton sharing groups are not included (1-clique    |
% semantics).                                                            |
%------------------------------------------------------------------------%  
sets_in_sharing([],_,0,[]).
sets_in_sharing([[_]|Shs],Sh1,Card,Shs0):-
    !,sets_in_sharing(Shs,Sh1,Card,Shs0).
sets_in_sharing([Sh|Shs],Sh1,Card,[Sh|Shs0]):-
    ord_subset(Sh,Sh1),!,
    sets_in_sharing(Shs,Sh1,Card0,Shs0),
    Card is Card0 + 1.
sets_in_sharing([_|Shs],Sh1,Card,Shs0):-
    sets_in_sharing(Shs,Sh1,Card,Shs0).

%------------------------------------------------------------------------%
% sets_in_cliques_1(CL,Cand,J)                                           |
% sets_in_cliques_1(+,+,-)                                               |
%------------------------------------------------------------------------%
% J is the number of sharing groups that are not in the sharing part     |
% because they are included in some cliques (1-clique semantics).        |
%------------------------------------------------------------------------%

number_sets_in_cliques_1(CL,Cand,J):-
    intersection_lists_with_list(CL,Cand,I),
    length(I,End),
    compute_inc_exc_clique_1(I,1,End,plus,0,J).

compute_inc_exc_clique_1(_,Start,End,_,J,J):-
    Start > End.
compute_inc_exc_clique_1(I,Start,End,Sig,Acc,J):-
    bagof(S,
          comb(Start,I,S),
          Combs),
    intersect_all(Combs,Int),
    sum_cliques_1(Int,0,Val),
    ( Sig = plus ->
      NSig = minus,
      NAcc is  Acc + Val
    ;
      NSig = plus,
      NAcc is  Acc - Val
    ),
    Next is Start + 1,
    compute_inc_exc_clique_1(I,Next,End,NSig,NAcc,J).

sum_cliques_1([],Acc,Acc).
sum_cliques_1([C|Cs],Acc,Res):-
    card_clique_1(C,N),
    NAcc is Acc + N,
    sum_cliques_1(Cs,NAcc,Res).

card_clique_1(S,N2):-
    length(S,N),!,
    number_of_subsets(N,N1),
    N2 is N1 - N.

check_minimum(M):-
    M > 1,!.
check_minimum(_):-!,
    error_message("The minimum candidate detected must be at least greater than 2"),
    fail.
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The following predicates are used for tests (don't delete them)
card_cliques_1(Cl,J):-
    length(Cl,End),
    compute_inc_exc_clique_1(Cl,1,End,plus,0,J).

%------------------------------------------------------------------------%
%                      INTERMEDIATE OPERATIONS                           |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% delete_vars_from_list_of_lists_no_sing(Vs,LLs,LLs0)                    |
% Delete the list of variables Vs from the list of lists LLs. None of    |
% list of LLs is a singleton                                             |
%------------------------------------------------------------------------%
delete_vars_from_list_of_lists_no_sing(Vs,LLs,LLs1):-
    delete_vars_from_list_of_lists_no_sing_(Vs,LLs,LLs0),
    sort_list_of_lists(LLs0,LLs1).

delete_vars_from_list_of_lists_no_sing_([],LLs,LLs).
delete_vars_from_list_of_lists_no_sing_([Vs|Vss],List_of_Lists,LLs) :-
    delete_var_from_list_of_lists_no_sing(Vs,List_of_Lists,New_LLs,_),
    delete_vars_from_list_of_lists_no_sing_(Vss,New_LLs,LLs). % TODO: missing cut
delete_var_from_list_of_lists_no_sing(X,[Ys|Yss],List_of_lists,Ans) :-
    ord_delete(Ys,X,New_Ys),
    ( New_Ys = [] ->
        Ans = yes,
        List_of_lists = New_Yss
    ; 
      ( New_Ys = [_] ->
        List_of_lists = New_Yss
      ;
        Ans = Ans1,
        List_of_lists = [New_Ys|New_Yss]
      )
    ),
    delete_var_from_list_of_lists_no_sing(X,Yss,New_Yss,Ans1). % TODO: missing cut
delete_var_from_list_of_lists_no_sing(_,[],[],no).

%------------------------------------------------------------------------%
% split_list_of_lists_singleton(+,-,-)                                   |
% split_list_of_lists_singleton(Xs,Non,Sing)                             |
% Splits a list of lists in a set of non-singleton (Non) and a set of    |
% singletons.
%------------------------------------------------------------------------%
split_list_of_lists_singleton([],[],[]).
split_list_of_lists_singleton([[X]|Xs],R1,[[X]|R2]) :-
    !,split_list_of_lists_singleton(Xs,R1,R2).
split_list_of_lists_singleton([X|Xs],[X|R1],R2) :-
    split_list_of_lists_singleton(Xs,R1,R2).
