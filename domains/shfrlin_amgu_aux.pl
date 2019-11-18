:- module(shfrlin_amgu_aux,
    [shfrlin_amgu_iterate/3, shfrlin_amgu_update_fr_lin/3],
     [assertions, isomodes]).

:- doc(author, "Jorge Navas").
% Copyright (C) 2006-2019 The Ciao Development Team

%------------------------------------------------------------------------%
% This file implements the amgu for sharing+Freeness+linearity           |
%------------------------------------------------------------------------%

:- use_module(library(sort), [sort/2]).
:- use_module(domain(s_grshfr), [member_value_freeness/3]).
:- use_module(library(sets),
    [ord_member/2, ord_subtract/3, ord_union/3, ord_subset/2,
     ord_intersection/3]).
:- use_module(domain(share_amgu_sets), [split_list_of_lists/4]).
:- use_module(domain(share_amgu_aux), [bin_union/3, star/2]).
:- use_module(domain(sharefree_amgu_aux), 
    [amgu_non_star/5, lin/2, update_freeness/4, map_freeness_list/3,
     shfr_update_freeness/4, share_with/3]).

%------------------------------------------------------------------------%
% shfrlin_amgu_iterate(+,+,-)                                            |
%------------------------------------------------------------------------%
shfrlin_amgu_iterate([],ASub,ASub).
shfrlin_amgu_iterate([(X,(Ts,Type,L))|Eqs],ASub,ASub2):-        
     amgu_shfrlin(X,(Ts,Type,L),ASub,ASub1),
     shfrlin_amgu_iterate(Eqs,ASub1, ASub2).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                  UPDATE FREENESS+LINEARITY                             |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfrlin_amgu_update_fr_lin(+,+,-)                                           |
% shfrlin_amgu_update_fr_lin((Sh,F,L),Vars,(Sh',F',L')                        |
%------------------------------------------------------------------------%
shfrlin_amgu_update_fr_lin((Sh,F,L),Vars,(Sh,F1,L1)):-
     shfr_update_freeness(Sh,F,Vars,F1),
     filter_ground(L,F1,L1).
%------------------------------------------------------------------------%
%                      ABSTRACT UNIFICATION                              %
%------------------------------------------------------------------------%
% amgu_shfrlin(+,+,+,-)                                                  |
% amgu_shfrlin(X,(T,Type,L),(Sh,f,l),SHFL')                              | 
% Amgu describes the unification X=T (concrete unification) in a state   |
% described by S.T is of Type t (term) or v (var) and L is l or nl       |
% SHFL' = (Sh',f',l') where:                                             |
% Sh'= \rel(Sh_xt) U (Sh_x \bin Sh_t)             if x in f or t in f    |       
% \rel(Sh_xt) U (Sh_x U (Sh_x \bin Sh_xt*)) \bin  if alin(x),alin(t)     |
%               (Sh_t U (Sh_t \bin Sh_xt*))                              | 
%      \rel(Sh_xt) U (Sh_x* \bin Sh_t)            if alin(x),not alin(t) |
%      \rel(Sh_xt) U (Sh_x \bin Sh_t*)            if not alin(x),alin(t) |
%      amgu(X,T,Sh)                               otherwise              |
%                                                                        |
% f'  =  f                                        if x in f, t in f      |  
%     |  f \ (U sh_x)                             if x in f, t not in f  | 
%     |  f \ (U sh_t)                             if x not in f, t in f  |
%     |  f \ (U sh_x) U (U sh_t)                  if x not in f, t not in f
%                                                                        |
% l'  =  f' U                                                            |
%     |  l \ (U sh_x) /\ (U sh_t)                 if alin(x),alin(t)     | 
%     |  l \ (U sh_x)                             if alin(x), not alin(t)|
%     |  l \ (U sh_t)                             if not alin(x), alin(t)|
%     |  l \ (U sh_x) U (U sh_t)                  otherwise              | 
%------------------------------------------------------------------------%

%amgu_shfrlin(X,(T,Type,TL),(Sh0,F,L0),(NewSh,NewF,NewL)):-
amgu_shfrlin(X,(T,Type,TL),(Sh,F,L),(NewSh,NewF,NewL)):-
     member_value_freeness(F,Free_Vars0,f),
     sort(Free_Vars0,Free_Vars),     
%     sort(L0,L),
%     sort_list_of_lists(Sh0,Sh),
     alin_l(([X],l),Sh,L,Is_Alin_x),  % for efficiency
     alin_l((T,TL),Sh,L,Is_Alin_t),   % for efficiency
     amgu_shfrlin_(X,(T,Type),Is_Alin_x,Is_Alin_t,(Sh,Free_Vars,L),
              (NewSh,NewF,NewL)).
%------------------------------------------------------------------------%
amgu_shfrlin_(X,(T,Type),Is_Alin_x,Is_Alin_t,(Sh,F,L),(NewSh,NewF,NewL)):-
     ord_member(X,F),!,       
%% sharing
     % x or t is free (1)
     amgu_non_star(non_star,X,T,Sh,NewSh),
%% freeness
     ( ((Type == v), T = [T1], ord_member(T1,F)) ->
    % x in f, t in f (1)
    NewF1 = F
     ;  % x in f, t not in f (2)  
    update_freeness([X],Sh,F,NewF1) 
     ),     
%% linearity
     update_linearity([X],T,Is_Alin_x,Is_Alin_t,(Sh,NewF1,L),NewL),
     map_freeness_list(NewF1,f,NewF).
amgu_shfrlin_(X,([T],v),Is_Alin_x,Is_Alin_t,(Sh,F,L),(NewSh,NewF,NewL)):-
     ord_member(T,F),!,
%% sharing
     % x or t is free (1)
     amgu_non_star(non_star,X,[T],Sh,NewSh),
%% freeness
     % x not in f, t in f (3)   
     update_freeness([T],Sh,F,NewF1),
%% linearity
     update_linearity([X],[T],Is_Alin_x,Is_Alin_t,(Sh,NewF1,L),NewL),
     map_freeness_list(NewF1,f,NewF).
amgu_shfrlin_(X,(T,_),Is_Alin_x,Is_Alin_t,(Sh,F,L),(NewSh,NewF,NewL)):-
%% sharing
     update_sh_alin(X,T,Is_Alin_x,Is_Alin_t,Sh,NewSh),
%% freeness
     % x not in f, t not in f (4)       
     ord_union([X],T,X_union_T),
     update_freeness(X_union_T,Sh,F,NewF1),
%% linearity
     update_linearity([X],T,Is_Alin_x,Is_Alin_t,(Sh,NewF1,L),NewL),
     map_freeness_list(NewF1,f,NewF).

%------------------------------------------------------------------------%      
% update_sh_alin(+,+,+,+,+,-)                                            |
% Sh'=                                                                   |       
% \rel(Sh_xt) U (Sh_x U (Sh_x \bin Sh_xt*)) \bin  if alin(x),alin(t)     |
%               (Sh_t U (Sh_t \bin Sh_xt*))                              | 
%      \rel(Sh_xt) U (Sh_x* \bin Sh_t)            if alin(x),not alin(t) |
%      \rel(Sh_xt) U (Sh_x \bin Sh_t*)            if not alin(x),alin(t) |
%      amgu(X,T,Sh)                               otherwise              |
%------------------------------------------------------------------------%
update_sh_alin(X,T,Is_Alin_x,Is_Alin_t,Sh,NewSh):-
    sort(T,V_t),
    ord_union([X],V_t,V_xt),
    split_list_of_lists([X],Sh,Sh_x,_),
    split_list_of_lists(V_t,Sh,Sh_t,_),
    split_list_of_lists(V_xt,Sh,Sh_xt,Irrel_Sh_xt),
    star(Sh_xt,Sh_xt_star),
    ( Is_Alin_x == yes -> 
      ( Is_Alin_t == yes ->
        % if alin(x),alin(t)
        ( Sh_xt_star == [] -> % optimization
          bin_union(Sh_x,Sh_t,Shx_bin_Sht),
          ord_union(Irrel_Sh_xt,Shx_bin_Sht,NewSh)
        ; 
          bin_union(Sh_x,Sh_xt_star,Sh_x_bin_Sh_xt_star),
          bin_union(Sh_t,Sh_xt_star,Sh_t_bin_Sh_xt_star),
          ord_union(Sh_x,Sh_x_bin_Sh_xt_star,NewSh1),
          ord_union(Sh_t,Sh_t_bin_Sh_xt_star,NewSh2),
          bin_union(NewSh1,NewSh2,NewSh0),
          ord_union(Irrel_Sh_xt,NewSh0,NewSh)
        )
      ; % if alin(x),not alin(t)
        star(Sh_x,Sh_x_star),
        bin_union(Sh_x_star,Sh_t,NewSh0),
        ord_union(Irrel_Sh_xt,NewSh0,NewSh)
      )
    ;   % if not alin(x),alin(t)
      ( Is_Alin_t == yes ->
        star(Sh_t,Sh_t_star),
        bin_union(Sh_t_star,Sh_x,NewSh0),
        ord_union(Irrel_Sh_xt,NewSh0,NewSh)
      ; % otherwise (general case)
        star(Sh_t,Sh_t_star),
        star(Sh_x,Sh_x_star),
        bin_union(Sh_t_star,Sh_x_star,NewSh0),
        ord_union(Irrel_Sh_xt,NewSh0,NewSh)
      )
    ).  

% alin_l((t,l),Sh,Lin) iff t \subseteq Lin and lin(t,Sh)
alin_l((T,L),Sh,Lin,yes):-
     alin_l_((T,L),Sh,Lin),!.
alin_l(_,_,_,not):-!.
alin_l_((T,l),Sh,Lin):-
     sort(T,Ts),
     ord_subset(Ts,Lin),!,
     lin(Sh,Ts).

%------------------------------------------------------------------------%
% update_linearity(+,+,+,+,+,-)                                          |
% X is a list                                                            |
%------------------------------------------------------------------------%
% l'  =  f' U                                                            |
%     |  l \ (U sh_x) /\ (U sh_t)   if alin(x),alin(t)                   | 
%     |  l \ (U sh_x)               if alin(x), not alin(t)              |
%     |  l \ (U sh_t)               if not alin(x), alin(t)              | 
%     |  l \ (U sh_x) U (U sh_t)    otherwise                            |
%------------------------------------------------------------------------%
update_linearity(X,T,Is_Alin_x,Is_Alin_t,(Sh,NewF,L),NewL):-
    ( Is_Alin_x == yes ->
      ( Is_Alin_t == yes ->
        % alin(X),alin(T)
        share_with(X,Sh,Sh_x),
        share_with(T,Sh,Sh_t),
        ord_intersection(Sh_x,Sh_t,Sh_xandt),
        ord_subtract(L,Sh_xandt,NewL0)
      ; % alin(X), not alin(T)
        share_with(X,Sh,Sh_x),
        ord_subtract(L,Sh_x,NewL0)
      )
    ; 
      ( Is_Alin_t == yes ->
        % not alin(X), alin(T)
        share_with(T,Sh,Sh_t),
        ord_subtract(L,Sh_t,NewL0)
      ; % otherwise             
        share_with(X,Sh,Sh_x),
        share_with(T,Sh,Sh_t),
        ord_union(Sh_x,Sh_t,Sh_xt),
        ord_subtract(L,Sh_xt,NewL0)
      )
    ),      
    ord_union(NewF,NewL0,NewL).

filter_ground(Lin,Fr,NewLin):-
     member_value_freeness(Fr,Ground,g),
     ord_subtract(Lin,Ground,NewLin).
