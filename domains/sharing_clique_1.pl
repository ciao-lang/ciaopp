:- module(sharing_clique_1, [], [assertions, isomodes]).

:- doc(title, "1-CLIQUE-Sharing domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

:- use_module(domain(sharing_clique), [
    augment_asub/3,
    abs_sort/2,
    success_builtin/6,
    widen/4,
    widen/5,
    special_builtin/5,
    input_user_interface/5,
    empty_entry/3]).
:- include(ciaopp(plai/plai_domain)).
:- dom_def(share_clique_1, [default]).

:- dom_impl(_, abs_sort/2, [from(sharing_clique:share_clique), noq]).
:- dom_impl(_, special_builtin/5, [from(sharing_clique:share_clique), noq]).
:- dom_impl(_, input_user_interface/5, [from(sharing_clique:share_clique), noq]).
:- dom_impl(_, empty_entry/3, [from(sharing_clique:share_clique), noq]).

%------------------------------------------------------------------------%
% This file contains the domain dependent abstract functions for the     |
% clique-sharing domain with an extension that allows to capture         |
% groundness dependencies, without combining it with Def or Pos by       |
% J.Navas, F.Bueno and M.Hermenegildo.                                   |
%------------------------------------------------------------------------%
% The representation of this domain is the same that Clique-Sharing      |
% domain but in this case, a clique C represents all the sharing groups  |
% in the powerset of C but those with cardinality 1.                     |
%------------------------------------------------------------------------%
% The meaning of the variables are defined in sharing.pl                 |
%------------------------------------------------------------------------%

:- doc(bug,"1. THIS DOMAIN HAS A LIMITATION. Since singletons
       are always in the sharing component, the function clsh/5 will
       not run in a shorter time.").
:- doc(bug,"2. In case of success multivariance the predicate
       eliminate_equivalent/2 must de redefined.").
:- doc(bug,"3. Only the following widenings are implemented: inter_1
       and cautious.").

:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(lsets), 
           [sort_list_of_lists/2,
            ord_split_lists_from_list/4,
            merge_list_of_lists/2,
            ord_member_list_of_lists/2
            ]).       
:- use_module(library(sets), 
          [
           ord_subset/2,
           ord_subtract/3,
           ord_union/3,
           ord_intersection/3,
           ord_member/2,
           merge/3,
           insert/3,
           ord_intersection_diff/4
           ]).
:- use_module(library(lists), 
          [delete/3,               
           append/3,
           powerset/2,
           list_to_list_of_lists/2
           ]).
:- use_module(library(sort), 
          [sort/2]).        

:- use_module(domain(share_aux), [
    eliminate_couples/4,
    handle_each_indep/4,
    eliminate_if_not_possible/3,
    test_temp/2,
    eliminate_if_not_possible/4,
    if_not_nil/4,handle_each_indep/4,
    append_dl/3]).

:- use_module(domain(share_amgu_sets)).
:- use_module(domain(share_amgu_aux), [
    peel_equations/3,
    sh_peel/3]).
:- use_module(domain(s_grshfr), [
    projected_gvars/3]).
:- use_module(domain(sharing), [
    input_interface/4,
    project/5]).
:- use_module(domain(sharing_clique), [
    share_make_reduction/5,
    projected_gvars_clique/3,
    clique_part_less_or_equal/2,
    clique_make_decomposition/5,
    asub_gt/2,
    prune_success/5,
    powerset_with_empty_set/2,
    sharing_part_less_or_equal/3,
    sharing_possible/4,
    eliminate_couples_clique/4,
    myappend/3]).

:- use_module(domain(share_clique_aux), [
    widen/1,
    type_widening/1,
    type_widening_condition/1,
    widen_upper_bound/1,
    widen_lower_bound/1,
    ord_union_w/3
   ]).
:- use_module(domain(share_clique_1_aux), 
    [amgu_clique_1/4,
     share_clique_1_normalize/2,
     share_clique_1_normalize/4,
     star_clique_1/2,
     nrel_clique_1/3,
     split_list_of_lists_singleton/3
      ]).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,?)                          |
%------------------------------------------------------------------------%
% TODO: almost like share_clique version
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
     variant(Sg,Head),!,
     ExtraInfo = yes,
     copy_term((Sg,Proj),(NewSg,NewProj)),
     Head = NewSg,
     sharing_clique:abs_sort(NewProj,(Cl,Temp)),
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp,Sh),
     share_clique_1_normalize((Cl,Sh),Entry).
call_to_entry(_,_,[],_Head,_K,Fv,_,Entry,ExtraInfo):- !,
     ExtraInfo = no,
     list_to_list_of_lists(Fv,Sh_Entry),
     share_clique_1_normalize(([],Sh_Entry),Entry).
call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
     % groundness propagation to exit_to_prime
     projected_gvars_clique(Proj,Sv,Gv_Call),
     peel_equations( Sg,Head, Equations),
     sharing_clique:augment_asub(Proj,Hv,ASub),     
     share_clique_1_iterate(Equations,ASub,ASub1),
     sharing_clique:widen(plai_op_clique_1,ASub1,_,Result),
     project(Sg,Hv,not_provided_HvFv_u,Result,Entry0),
     sharing_clique:augment_asub(Entry0,Fv,Entry1),
     share_clique_1_normalize(Entry1,Entry),
     ExtraInfo = (Equations,Gv_Call),!.
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).

%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)                            |
%------------------------------------------------------------------------%

% TODO: almost like share_clique version
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,Flag,Prime):-  
     Flag == yes, !,
     project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
     copy_term((Head,BPrime),(NewHead,NewPrime)),
     Sg = NewHead,
     sharing_clique:abs_sort(NewPrime,Prime).
exit_to_prime(_,[],_,_,_,_,([],[])):- !.
exit_to_prime(Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Gv_Call),           
     sharing_clique:augment_asub(Exit,Sv,ASub),   
     share_clique_1_iterate(Equations,ASub, Prime0),
     sharing_clique:widen(plai_op_clique_1,Prime0,_,Prime1),
     project(Sg,Sv,not_provided_HvFv_u,Prime1,(Cl,Sh)),
     % groundness propagation from call_to_entry
     nrel_clique_1(Gv_Call,(Cl,Sh),(Cl1,Sh1)),
     Prime = (Cl1,Sh1).

%------------------------------------------------------------------------%
%                            ABSTRACT Iterate                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_clique_1_iterate(+,+,+,-)                                        |
% share_clique_1_iterate(Eqs,Flag,ASub0,ASub)                            |
%------------------------------------------------------------------------%

% TODO: almost like share_clique version
share_clique_1_iterate([],ASub, ASub).
share_clique_1_iterate([(X,Ts)|Eqs],ASub, ASub2):-
     amgu_clique_1(X,Ts,ASub,ASub1),
     share_clique_1_iterate(Eqs,ASub1, ASub2).

%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% extend(+,+,+,+,-)                                       |
% extend(Sg,Prime,Sv,Call,Succ)                           |
%------------------------------------------------------------------------%

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Hv,_Call,Succ):- !,
     Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
     Call = Succ.
extend(_Sg,Prime,Sv,Call,Succ):-
%open('clsh.pl',append,Fd),
     % explicit groundness propagation  
     projected_gvars_clique(Prime,Sv,Gv),
     nrel_clique_1(Gv,Call,(Call_Cl,Call_Sh)),
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     split_list_of_lists(Sv,Call_Cl,Call_Cl_g,_),       
     split_list_of_lists(Sv,Call_Sh,Call_Sh_g,_),       
     nrel_clique_1(Sv,(Call_Cl,Call_Sh),(Irrel_Call_Cl,Irrel_Call_Sh)),
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
     star_clique_1((Call_Cl_g,Call_Sh_g),(Cl1,Sh1)), % (Cl1,Sh1) is normalized
     %--------------------------------------------------------------------%
     % REMARK:In order to be able to go on with the analysis, if |sh2| > 0|
     % then |cl'| must not be greater than 10.                            |
     %--------------------------------------------------------------------%
     normalize_1_if_clsh_needs(Prime,Cl1,NewPrime),
     NewPrime = (Cl2,Sh2),
     %--------------------------------------------------------------------%
     % clique of Call clique "allowed" by the Prime clique
     extend_cl_1(Cl2,Cl1,Sv,Irrel_Call_Cl,Extcl0,_),
     % sharing of Call sharing "allowed" by the Prime sharing 
     prune_success(Sh1,Sh2,Sv,Irrel_Call_Sh,Extsh0), 
     % sharing of Call sharing "allowed" by the Prime clique
     shcl_1(Sh1,Cl2,Sv,[],ShCl),
     % Remove extcl from Cl* (cliques in the success). In this way,
     % clsh is more efficient and the result less redundant
     delete_list_of_lists(Cl1,Extcl0,Cl12),
     % sharing of Call clique "allowed" by the Prime sharing
     clsh_1(Cl12,Sh2,Sv,[],ClSh), 
     sharing_clique:widen(aamgu,inter_1_clique_1,([],ClSh),_,(Extcl1,ClSh1)),
     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     ord_union(Extsh0,ShCl,Extsh1),
     ord_union(Extsh1,ClSh1,Extsh),
     ord_union(Extcl0,Extcl1,Extcl),
     Succ = (Extcl,Extsh).

normalize_1_if_clsh_needs((Cl2,[]),_,(Cl2,[])):-!.
normalize_1_if_clsh_needs((Cl2,Sh2),Cl1,(NewCl2,NewSh2)):-
    T = 10,
    ( asub_gt(Cl1,T) ->
      share_clique_1_normalize((Cl2,Sh2),100,2,(NewCl2,NewSh2))
    ;
      (NewCl2,NewSh2) = (Cl2,Sh2)
    ).

%------------------------------------------------------------------------%
% extend_cl_1(+,+,+,-)                                                   |
% extend_cl_1(Prime,Call_g*,Sv,ExtCl)                                    |
% clique groups of the call clique part allowed by the prime clique part |
%------------------------------------------------------------------------%
:- push_prolog_flag(multi_arity_warnings,off).
extend_cl_1([],_,_,Irrel,Irrel,[]).
extend_cl_1([S_cl2|S_cl2s],Cl1,Vars,Irrel,Extendcl_No_Sing,Sh_Sing):-
    extend_cl_1(Cl1,S_cl2,Vars,L1,L2),
    extend_cl_1(S_cl2s,Cl1,Vars,Irrel,L1s,L2s),
    ord_union(L1s,L1,Extendcl_No_Sing),
    ord_union(L2s,L2,Sh_Sing).

extend_cl_1([],_,_,[],[]).
extend_cl_1([S|Ss],S_cl2,Vars,L1,L2):-
    ord_intersection(S_cl2,S,Int),
    ord_subtract(S,Vars,Disj),
    ord_union(Int,Disj,Res),!,
    ( Res = [_] ->
      L1 = L1s,
      L2 = [Res|L2s]
    ;
      L1 = [Res|L1s],
      L2 = L2s      
    ),
    extend_cl_1(Ss,S_cl2,Vars,L1s,L2s).
extend_cl_1([_|Ss],S_cl2,Vars,L1,L2):-
    extend_cl_1(Ss,S_cl2,Vars,L1,L2).
:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
% clsh_1(+,+,+,+,-)                                                      |
% clsh_1(Cl1,Sh2,Sv,Imp,ClSh)                                            |
%------------------------------------------------------------------------%      

% TODO: almost like share_clique version (clsh_more_proceise/5)
clsh_1([],_,_,Succ,Succ).
clsh_1([Cl|Cls],Sh2,Sv,Call,Succ) :-
    sharing_possible(Sh2,Cl,Sv,Sharing_Allowed),
    ord_subtract(Cl,Sv,Sv_No_Proj),
    powerset_with_empty_set(Sv_No_Proj,Pow_Sv_No_Proj),
    clsh_extend_sharing_no_sing(Sharing_Allowed,Pow_Sv_No_Proj,Res),
    ord_union(Call,Res,Temp),
    clsh_1(Cls,Sh2,Sv,Temp,Succ).

clsh_extend_sharing_no_sing([],_,[]).
clsh_extend_sharing_no_sing(Sh,[],Sh).
clsh_extend_sharing_no_sing([S|Ss],Pow,ExtSh):-
    bin_union_no_sing([S],Pow,Res),
    clsh_extend_sharing_no_sing(Ss,Pow,Result),
    ord_union(Res,Result,ExtSh).    

bin_union_no_sing([],_,[]).
bin_union_no_sing([H|T],L2,L):-
    bin_union_(L2,H,SL),
    bin_union_no_sing(T,L2,RL),
    ord_union(RL,SL,L).

bin_union_([],_,[]).
bin_union_([S|Ss],E,BUnion ):-
    ord_union(S,E,Union),
    bin_union_(Ss,E,Res),
    ( Union = [_] ->
      BUnion = Res
    ;
      ord_union(Res,[Union],BUnion)
    ).

%------------------------------------------------------------------------%
% shcl_1(+,+,+,-)                                                        | 
% shcl_1(sh',cl2,g,ShCl)                                                 |
% shcl_1(sh',cl2,g) = {s| s \in sh', |(s /\ g)| > 1,                     |
%                      (s /\ g) \subseteq c \in cl2}                     |
%------------------------------------------------------------------------%
% TODO: almost like share_clique version
shcl_1(Xss,Cl,Sv,Call,Succ_sh_s):-
    shcl_1_(Xss,Cl,Sv,Call,Succ_sh),
    sort_list_of_lists(Succ_sh,Succ_sh_s).

shcl_1_([],_Cl,_Sv,Succ,Succ).
shcl_1_([Xs|Xss],Cl,Sv,Call,Succ):-
    ord_intersection_no_singleton(Xs,Sv,Xs_proj),!,
    ( ord_subset_lists_with_list(Cl,Xs_proj) ->
      Temp = [Xs|Call]
    ;
      Temp = Call
    ),  
    shcl_1_(Xss,Cl,Sv,Temp,Succ).

ord_intersection_no_singleton(Xs,Sv,Int):-
    ord_intersection(Xs,Sv,Xs_proj),!,
    ( Xs_proj = [_] ->
      Int = []
    ;
      Int = Xs_proj
    ).  


%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION                               |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% project(+,+,+,+,-)                                      |
% project(Sg,Vars,HvFv_u,ASub,Proj)                       |
% project(g,(cl,sh)) = (\one(R), S U project(g,sh))                      |
% R = {s | c \in cl, s = c /\ g}                                         |
% S = {{x} | x \in s, c \in cl, s = c /\ g, s \subseteq c}               |
%------------------------------------------------------------------------%

:- redefining(project/5).
:- dom_impl(_, project/5, [noq]).
project(_,_,_,'$bottom','$bottom'):- !.
project(Sg,Vars,HvFv_u,(Cl,Sh),Proj) :-
    sharing:project(Sg,Vars,HvFv_u,Sh,Sh_Proj),
    project_clique_1(Cl,Vars,Cl_Proj,_),
    retrieve_singletons((Cl_Proj,Sh_Proj),Cl,Vars,Proj).
    
%------------------------------------------------------------------------%
% project_clique_1(SS,Vars,Int,Disj)                                     |
% Split the ordered list of lists SS into two sorted lists: Int          |
% contains the intersection of Vars and SS with cardinality > 1,         |
% Disjunct with cardinality equal to 1.                                  |    
%------------------------------------------------------------------------%

project_clique_1(SS,Vars,Int,Disj):-
    project_clique_1_(SS,Vars,Int0,Disj0),
    sort_list_of_lists(Int0,Int),
    sort_list_of_lists(Disj0,Disj).

project_clique_1_([],_,[],[]).
project_clique_1_([X|Xs],Vars,Int1,Disj1):-
    ord_intersection(X,Vars,L),!,
    ( L = [_] -> 
      insert_not_nil(L,Disj,Disj1),
      Int1 = Int
    ;
      insert_not_nil(L,Int,Int1), 
      Disj1 = Disj
    ),
    project_clique_1_(Xs,Vars,Int,Disj).

%------------------------------------------------------------------------%
% retrieve_singletons(+,+,+,-)                                           |
% retrieve_singletons(SH,Ss,g,Sing)                                      | 
%------------------------------------------------------------------------%
% Sing= augment(SS,S) where:                                             |
%  S= {{x} | x \in s , c \in Ss, s = c /\ g, s \subset c}                |
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).
retrieve_singletons(SH_Proj,Ss,Vars,Proj):-
    retrieve_singletons(Ss,Vars,Sing),
    merge_list_of_lists(Sing,Sing_vars),
    sharing_clique:augment_asub(SH_Proj,Sing_vars,Proj).

retrieve_singletons([],_,[]).
retrieve_singletons([S|Ss],Vars,[Int|Ints]):-
    subset_if_not_nil(S,Vars,Int),
    retrieve_singletons(Ss,Vars,Ints).
:- pop_prolog_flag(multi_arity_warnings).
subset_if_not_nil(C,Vars,Res):-
    ord_intersection(C,Vars,Int),!,
    ( compare(=,Int,C) ->
      Res = []
    ;
      Res = Int
    ).  

%------------------------------------------------------------------------%
% compute_lub(+,-)                                        |
% compute_lub(ListASub,Lub)                               |
%------------------------------------------------------------------------%
:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([ASub],ASub).
compute_lub([ASub1,ASub2|Rest],Lub) :-
    lub_cl(ASub1,ASub2,ASub3),
%       sharing_clique:widen(extend_clique_1,ASub3,_,ASub_widen),
    ASub3 = ASub_widen,
    compute_lub([ASub_widen|Rest],Lub).

% :- dom_impl(_, compute_lub_el(ASub1,ASub2,ASub), lub_cl(ASub1,ASub2,ASub), [noq]).
lub_cl(ASub1,ASub2,ASub3):-
    ASub1 == ASub2,!,
    ASub3 = ASub2.
lub_cl(ASub1,ASub2,ASub3):-
    merge_subst_clique_1(ASub1,ASub2,ASub3).

merge_subst_clique_1('$bottom',Yss,Yss):- !.
merge_subst_clique_1(Xss,'$bottom',Xss):- !.
merge_subst_clique_1((Cl1,Sh1),(Cl2,Sh2),Lub) :-
    merge(Cl1,Cl2,Cl0),
    merge(Sh1,Sh2,Sh0),
    share_clique_1_normalize((Cl0,Sh0),100,2,Lub).

%------------------------------------------------------------------------%
% glb(+,+,-)                                              |
% glb(ASub0,ASub1,Lub)                                    |
%------------------------------------------------------------------------%

:- dom_impl(_, glb/3, [noq]).
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb((Cl1,Sh1),(Cl2,Sh2),Lub):-
    intersection_list_of_lists(Cl1,Cl2,Cl0),
    split_list_of_lists_singleton(Cl0,Cl0_Non_sing,_),
    intersection_list_of_lists(Cl1,Sh2,Int0),
    intersection_list_of_lists(Cl2,Sh1,Int1),
    ord_intersection(Sh1,Sh2,Int2),
    ord_union(Int0,Int1,Int3),
    ord_union(Int2,Int3,Sh0),
    Lub = (Cl0_Non_sing,Sh0).

%------------------------------------------------------------------------%
% identical_abstract(+,+)                                 |
% identical_abstract(ASub0,ASub1)                         |
%------------------------------------------------------------------------%
% TODO: almost like share_clique version
:- dom_impl(_, identical_abstract/2, [noq]).
identical_abstract('$bottom','$bottom'):- !.
identical_abstract('$bottom',_):- !,fail.
identical_abstract(_,'$bottom'):- !,fail.
identical_abstract(ASub0,ASub1):-
    ASub0 == ASub1,!.
identical_abstract(ASub0,ASub1):- !,
    share_clique_1_normalize(ASub0,100,2,NASub0),!,
    ( NASub0 == ASub1 ->
      true
    ;
      share_clique_1_normalize(ASub1,100,2,NASub1),
      NASub0 == NASub1
    ).

%------------------------------------------------------------------------%
% eliminate_equivalent(+,-)                                              |
% eliminate_equivalent(TmpLSucc,LSucc)                                   |
%------------------------------------------------------------------------%
:- dom_impl(_, eliminate_equivalent/2, [noq]).
eliminate_equivalent(TmpLSucc,Succ):-
    sort(TmpLSucc,Succ).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                      |
% less_or_equal(ASub0,ASub1)                              |
% Succeeds if ASub1 is more general or equal to ASub0                    |
%------------------------------------------------------------------------%

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal('$bottom',_ASub):- !.
less_or_equal(ASub,ASub1):-
    share_clique_1_normalize(ASub,100,2,(Cl0,Sh0)),
    share_clique_1_normalize(ASub1,100,2,(Cl1,Sh1)),
    clique_part_less_or_equal(Cl0,Cl1),
    sharing_part_less_or_equal(Sh0,Sh1,Cl1).

%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts|
%------------------------------------------------------------------------%
% TODO: almost like share_clique version
:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(_,[],_Head,_K,Sv,(Cl,Sh),_,([],[]),Succ):-!,
    ord_split_lists_from_list(Sv,Sh,_,Succ_Sh),
    delete_vars_from_list_of_lists(Sv,Cl,Succ_Cl),
    Succ = (Succ_Cl,Succ_Sh).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ):-
% exit_to_prime
    sharing_clique:augment_asub(Call,Hv,ASub),        
    peel_equations(Sg, Head,Equations),
    share_clique_1_iterate(Equations,ASub,(Cl1,Sh1)),
    sharing_clique:widen(plai_op_clique_1,(Cl1,Sh1),_,(Cl,Sh)),
    project(Sg,Sv,not_provided_HvFv_u,(Cl,Sh),Prime),
% extend
    delete_vars_from_list_of_lists(Hv,Cl,Succ_Cl0),
    sort_list_of_lists(Succ_Cl0,Succ_Cl1),  
    split_list_of_lists_singleton(Succ_Cl1,Succ_Cl,_),
    delete_vars_from_list_of_lists(Hv,Sh,Succ_Sh),
    sort_list_of_lists(Succ_Sh,Succ_Sh_s),  
    Succ = (Succ_Cl,Succ_Sh_s),!.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%% %------------------------------------------------------------------------%
%% % Specialised version of share_call_to_success_fact in order to allow    |
%% % the computation of the prime, the composition and then the extension   |
%% %------------------------------------------------------------------------%
%% 
%% call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
%% % exit_to_prime
%%      sharing_clique:augment_asub(Call,Hv,ASub),        
%%      peel_equations(Sg, Head,Equations),
%%      share_clique_1_iterate(Equations,ASub,(Cl1,Sh1)),
%%      sharing_clique:widen(plai_op_clique_1,(Cl1,Sh1),_,(Cl,Sh)),
%%      project(Sg,Sv,not_provided_HvFv_u,(Cl,Sh),Prime).
    
% TODO: almost like share_clique version
:- dom_impl(_, input_interface/4, [noq]).
input_interface(clique_1(X),perfect,(Gv,Sh,Cl0,I),(Gv,Sh,Cl,I)):-
    nonvar(X),
    sort_list_of_lists(X,ASub),
    myappend(ASub,Cl0,Cl).         
input_interface(Prop,Any,(Gv0,Sh0,Cl,I0),(Gv,Sh,Cl,I)):-
    sharing:input_interface(Prop,Any,(Gv0,Sh0,I0),(Gv,Sh,I)).

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)                               |
% asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)         |
%------------------------------------------------------------------------%

% TODO: almost like share_clique version
:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
asub_to_native((Cl,Sh),Qv,_OutFlag,Info,[]):-
    ord_union(Sh,Cl,All),
    projected_gvars(All,Qv,Gv),
    if_not_nil(Cl,clique_1(Cl),Info,Info0),
    if_not_nil(Sh,sharing(Sh),Info0,Info1),
    if_not_nil(Gv,ground(Gv),Info1,[]).

%------------------------------------------------------------------------%
% share_clique_unknown_call(+,+,+,-)                                     |
% share_clique_unknown_call(Sg,Vars,Call,Succ)                           |
%------------------------------------------------------------------------%
% Gives the ``top'' value for the variables involved in a                |
% literal whose definition is not present, and adds this top value to    |
% Call.                                                                  |
%------------------------------------------------------------------------% 
:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
unknown_call(_Sg,_Vars,([],[]),([],[])) :- !.
unknown_call(_Sg,Vars,(Cl,Sh),Succ):-
    split_list_of_lists(Vars,Cl,Cl_vars,_),
    split_list_of_lists(Vars,Sh,Sh_vars,_),
    nrel_clique_1(Vars,(Cl,Sh),Rest),
    star_clique_1((Cl_vars,Sh_vars),Star),
    ord_union_w(Star,Rest,Succ).

%------------------------------------------------------------------------%
% unknown_entry(+,+,-)                                    |
% unknown_entry(Sg,Qv,Call)                               |
%------------------------------------------------------------------------%

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Qv,Call):-
    sort(Qv,QvS),   
    sharing_clique:augment_asub((QvS,[]),QvS,Call).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%      
% success_builtin(+,+,+,+,+,-)                            |
% success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)              |
% Obtains the success for some particular builtins:                      |
%  * If Type = ground, it updates Call making all vars in Sv_u ground    |
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%------------------------------------------------------------------------%

:- redefining(success_builtin/6).
:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    nrel_clique_1(Sv,Call,Succ).
success_builtin(bottom,_,_,_,_,'$bottom').
success_builtin(unchanged,_,_,_,Call,Call).
success_builtin(some,_,NewGround,_,Call,Succ):-
    nrel_clique_1(NewGround,Call,Succ).
% TODO: almost like share_clique version
% SPECIAL BUILTINS
success_builtin('=../2',_,p(X,Y),_,(Cl,Sh),Succ):-
% All variables of X are ground. All variables of Y will be ground
    varset(X,Varsx),
    ord_union(Sh,Cl,All),
    projected_gvars(All,Varsx,Vars),
    Vars == Varsx,!, 
    varset(Y,Varsy),
    ord_split_lists_from_list(Varsy,Sh,_Intersect,Sh1),
    take_ground_out_clique_1(Varsy,Cl,Cl1),
    Succ = (Cl1,Sh1).
success_builtin('=../2',_,p(X,Y),_,(Cl,Sh),Succ):-
% All variables of Y are ground. All variables of X will be ground
    nonvar(Y),
    Y = [Z|W],
    varset(W,Varsy),
    ord_union(Sh,Cl,All),
    projected_gvars(All,Varsy,Vars),
    Vars == Varsy,!,
    varset((X,Z),Varsx),
    ord_split_lists_from_list(Varsx,Sh,_Intersect,Sh1),
    take_ground_out_clique_1(Varsx,Cl,Cl1),
    Succ = (Cl1,Sh1).
success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
% X and Y are variables. Therefore, all variables of X can 
% share with all variables of Y
    var(X), var(Y),!,
    sort(Sv_u,Sv),
    Prime = ([],[Sv]),
    extend(not_provided_Sg,Prime,Sv,Call,Succ).
success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
% General case: Either X is f(t1,...,tn) or Y is [G|Something]. 
% We must unify [f,t1,...,tn] = [G|Something]
    ( var(Y) -> G=g ; Y = [G|_] ), !,
    ( var(X) -> Term=[G|X] ; X=..Term ),
    sort(Sv_u,Sv),
    project(not_provided_Sg,Sv,not_provided_HvFv_u,Call,Proj),
    call_to_success_builtin('=/2','='(Term,Y),Sv,Call,Proj,Succ).
success_builtin('=../2',_Sv_u,_,_,_Call,'$bottom').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% REVIEW !!
success_builtin('==/2',Sv_u,p(X,Y),_,Call,Succ):-
% If X and Y are identical, we only need to propagate groundness
    sh_peel(X,Y,Binds-[]),
    sort(Sv_u,Sv),
    Call = (Cl,Sh),
    ord_union(Cl,Sh,All),
    projected_gvars(All,Sv,Ground),  
%% clique-part
    clique_make_decomposition(Binds,Cl,Ground,NewGround,NewSH),
    sort(NewGround,NewGround1),
    NewSH = (Succ_Cl,Sh1),
%       share_clique_normalize(NewSH,(Succ_Cl,Sh1)),
%% sharing-part
    ord_union(Sh,Sh1,Sh0),
    share_make_reduction(Binds,Sh0,NewGround1,NewGround2,Sets-[]),
    sort(NewGround2,NewGround3),
    sort_list_of_lists(Sets,Sets1),
    ord_split_lists_from_list(NewGround3,Sh0,_Intersect,Temp),
    ord_subtract(Temp,Sets1,Succ_Sh),
    Succ = (Succ_Cl,Succ_Sh).
success_builtin(copy_term,_Sv_u,p(X,Y),_,Call,Succ):-
    varset(X,VarsX),
    project(not_provided_Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    sharing_clique:abs_sort(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    project(not_provided_Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    ord_union_w(ProjectedY,ProjectedNewX,TempProjected),
    ord_union_w(ProjectedNewX,Call,TempCall),
    call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                          TempCall,TempProjected,Temp_success),
    Call = (Cl,Sh),                    
    merge_list_of_lists(Cl,VarsCl),   
    merge_list_of_lists(Sh,VarsSh),   
    ord_union(VarsCl,VarsSh,VarsCall),
    project(not_provided_Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

success_builtin(findall,_Sv_u,p(X,Z),_,Call,Succ):-
    Call=(Cl,Sh),
    ord_union(Sh,Cl,All),
    varset(X,Varsx),
    projected_gvars(All,Varsx,Vars),
    Vars == Varsx,!,
    varset(Z,Varsz),
    success_builtin(ground,Varsz,_any,_,Call,Succ).
success_builtin(findall,_Sv_u,_,_,Call,Call).
success_builtin('indep/2',_Sv,p(X,Y),_,(Cl,Sh),(Succ_Cl,Succ_Sh)):-
    varset(X,Xv),
    varset(Y,Yv),
    eliminate_couples_clique_1(Cl,Xv,Yv,Succ_Cl),
    eliminate_couples(Sh,Xv,Yv,Succ_Sh).
success_builtin('indep/2',_Sv,_Condvars,_,_Call,'$bottom').
success_builtin('indep/1',_Sv,p(X),_,Call,Succ):- 
    nonvar(X),
    handle_each_indep(X,share_clique_1,Call,Succ), !.  
success_builtin('indep/1',_,_,_,_,'$bottom').
success_builtin('recorded/3',Sv_u,p(Y,Z),_,Call,Succ):-
    varset(Z,Varsz),
    nrel_clique_1(Varsz,Call,ASub),
    varset(Y,Varsy),
    project(not_provided_Sg,Varsy,not_provided_HvFv_u,ASub,ASub1),!,
    star_clique_1(ASub1,Prime),
    sort(Sv_u,Sv),
    extend(not_provided_Sg,Prime,Sv,Call,Succ).

success_builtin(var,_Sv,p(X),HvFv_u,(Cl,Sh),Succ):-
    sharing_clique:success_builtin(var,_,p(X),HvFv_u,(Cl,Sh),Succ).

%------------------------------------------------------------------------%
% call_to_success_builtin(+,+,+,+,+,-)                    |
% call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)     |
% Handles those builtins for which computing Prime is easier than Succ   |
%------------------------------------------------------------------------%

% TODO: almost like share_clique version
:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom').
call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
    call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
call_to_success_builtin('expand_term/2',expand_term(X,Y),Sv,Call,
                              Proj,Succ):- 
    call_to_success_builtin('arg/3',arg(1,Y,X),Sv,Call,Proj,Succ).
call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
    call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
call_to_success_builtin('arg/3',arg(X,Y,Z),_,Call,Proj,Succ):- 
    varset(X,OldG),
    nrel_clique_1(OldG,Call,TempCall),
    Sg = p(Y,Z),
    Head = p(f(A,_B),A),
    varset(Sg,Sv),
    varset(Head,Hv),
    project(not_provided_Sg,Sv,not_provided_HvFv_u,TempCall,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempCall,Proj,_Prime,Succ). % TODO: add some ClauseKey?

%------------------------------------------------------------------------%
%                      Intermediate operations                           |
%------------------------------------------------------------------------%

insert_not_nil(H,T,Res):-
    ( H = [] ->
      Res = T
    ;
      Res = [H|T]
    ).

take_ground_out_clique_1(Gv,Cl,Cl1):-
    ord_split_lists_from_list(Gv,Cl,Intersect,Disjoint),
    delete_vars_from_list_of_lists(Gv,Intersect,Intersect1),
    split_list_of_lists_singleton(Intersect1,Intersect1_non_sing,_),
    sort_list_of_lists(Intersect1_non_sing,Intersect1_non_sing_s),
    ord_union(Intersect1_non_sing_s,Disjoint,Cl1).

%------------------------------------------------------------------------%
% eliminate_couples_clique_1(+,+,+,-)                                    |
% eliminate_couples_clique_1(Cl,Xv,Yv,NewCl)                             |
%------------------------------------------------------------------------%

eliminate_couples_clique_1(Cl,Xv,Yv,NewCl_non_sing):-
    eliminate_couples_clique(Cl,Xv,Yv,NewCl),
    split_list_of_lists_singleton(NewCl,NewCl_non_sing,_).


