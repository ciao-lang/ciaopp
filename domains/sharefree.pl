:- module(sharefree, [], [assertions, regtypes, isomodes, datafacts]).

:- doc(title, "sharing+freeness (abstract domain)").
% started: 4/2/91
:- doc(author, "Maria Garcia de la Banda").
:- doc(author, "Francisco Bueno").

:- use_module(domain(sharefree_amgu), [
    sharefree_amgu_amgu/4,
    sharefree_amgu_augment_asub/3]).
:- include(ciaopp(plai/plai_domain)).
:- dom_def(shfr).
:- dom_impl(shfr, amgu/4, from(sharefree_amgu)).
:- dom_impl(shfr, augment_asub/3, from(sharefree_amgu)).
:- dom_impl(shfr, call_to_entry/9).
:- dom_impl(shfr, exit_to_prime/7).
:- dom_impl(shfr, project/5).
:- dom_impl(shfr, compute_lub/2).
:- dom_impl(shfr, abs_sort/2).
:- dom_impl(shfr, extend/5).
:- dom_impl(shfr, less_or_equal/2).
:- dom_impl(shfr, glb/3).
:- dom_impl(shfr, call_to_success_fact/9).
:- dom_impl(shfr, special_builtin/5).
:- dom_impl(shfr, success_builtin/6).
:- dom_impl(shfr, call_to_success_builtin/6).
:- dom_impl(shfr, obtain_info/4).
:- dom_impl(shfr, input_interface/4).
:- dom_impl(shfr, input_user_interface/5).
:- dom_impl(shfr, asub_to_native/5).
:- dom_impl(shfr, unknown_call/4).
:- dom_impl(shfr, unknown_entry/3).
:- dom_impl(shfr, empty_entry/3).
% :- dom_impl(shfr, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(shfr, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(shfr, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(shfr, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_impl(shfr, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_impl(shfr, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_impl(shfr, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% :- dom_impl(shfr, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(shfr, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
%
%% shfr_check_cond(_,_,_,_,_).
%% % shfr_compute_lub_el(_,_,_). %% commented out by JNL
%% shfr_convex_hull(_,_,_).
%% shfr_downwards_closed(_,_,_).
%% shfr_extend_free(_,_,_).
%% shfr_hash(_,_,_).
%% shfr_impose_cond(_,_,_,_).
%% shfr_more_instantiate(_,_).
%% shfr_real_conjoin(_,_,_).

%------------------------------------------------------------------------%
%                    Meanning of the Program Variables                   %
%                                                                        %
% _sh      : suffix indicating the sharing component                     %
% _fr      : suffix indicating the freeness component                    %
% Sh and Fr: for simplicity, they will represent ASub_sh and ASub_fr     %
%            respectively                                                %
% BPrime   : similar to the abstract prime constraint: abstract          %
%            subtitution obtained after the analysis of the clause being %
%            considered still projected onto Hv (i.e. just before going  %
%            Sv and thus, to Prime)                                      %
% Binds    : List of primitive bindings corresponding to the unification %
%            of Term1 = Term2.                                           %
% Gv       : set of ground variables (can be added as a prefix of a set  %
%            of variables, e.g. GvHv means the set of ground variables of%
%            the head variables)                                         %
% Tv       : set of variables in a term                                  %
% _args    : Added as a prefix of a term, means the set of variables     %
%            s.t. the i-th set contains the set of variables (ordered) in%
%            the i-th argument of the Term                               %
% Star     : a closure under union of a set of sets (can be added as a   %
%            suffix of a set of sets)                                    %
% ShareArgs: Set of sets of numbers in which each set represents the     %
%            possible set sharing among the argument positions indicated %
%            by the numbers                                              %
% Rest are as in domain_dependent.pl                                     %
%------------------------------------------------------------------------%

%% :- doc(bug,"1. ?- glb(shfr,([[A,B],[A,C]],[A/nf,Z/g,B/nf,C/nf]),
%%    ([[A]],[A/nf,Z/g,B/g,C/g]),X). X = ([],[A/nf,Z/g,B/g,C/g]) ? 
%%    Should be A/g.").
:- doc(bug,"2. With var(F),length([F|L],X) freenes of F is
    unnecessarily lost.").
%% Solved
%% :- doc(bug,"3. shfr_success_builtin for arg(X,Y,Z) is not prepared
%%      for a non-variable Y.").

:- use_module(domain(s_grshfr), 
    [ change_values_if_differ/5,
      change_values_insert/4,
      collect_vars_freeness/2,
      create_values/3,
      member_value_freeness/3, 
      projected_gvars/3,
      var_value/3
    ]).
:- use_module(domain(share_aux)).
:- use_module(domain(sharing), [
    share_project/5, 
    share_less_or_equal/2,
    share_glb/3,
    share_input_user_interface/5,
    share_input_interface/4,
    % TODO: move to other shared module?
    pos/4, 
    project_share/3, 
    script_p_star/3,
    script_p/3
    ]).

:- use_module(library(lists), [append/3, list_to_list_of_lists/2, powerset/2]).
:- use_module(library(lsets), 
    [ closure_under_union/2,
      merge_each/3,
      merge_list_of_lists/2, 
      merge_lists/3,
      ord_intersect_lists/2,
      ord_split_lists/4,
      ord_split_lists_from_list/4,
      powerset_of_set_of_sets/2,
      sort_list_of_lists/2
    ]).
:- use_module(library(sets), 
    [ insert/3, 
      merge/3,
      ord_intersect/2,
      ord_intersection/3,
      ord_intersection_diff/4,
      ord_member/2, 
      ord_subset/2,
      ord_subset_diff/3,
      ord_subtract/3,
      ord_test_member/3
    ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2, varset0/2, varset_in_args/2]).
:- use_module(engine(io_basic)).

% Plai lib, auxiliary
:- use_module(domain(s_eqs), [free_peel/4, simplify_equations/3]).

%------------------------------------------------------------------------%

:- regtype absu(A) # "@var{A} is an abstract substitution".
absu(_). % TODO: define properly for this domain

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfr_project(+,+,+,+,-)                                                %
% shfr_project(Sg,Vars,HvFv_u,ASub,Proj)                                 %
% Proj_sh is obtained as in the sharing domain. Proj_fr is the result of %
% eliminating from Fr all X/Value such that X not int Vars               %
%------------------------------------------------------------------------%

:- export(shfr_project/5).
shfr_project(_Sg,_Vars,_HvFv_u,'$bottom',Proj) :- !,
    Proj = '$bottom'.
shfr_project(_Sg,Vars,_HvFv_u,(Sh,Fr),Proj) :- 
    project_share(Vars,Sh,Proj_sh),
    project_freeness(Vars,Fr,Proj_fr),
    Proj = (Proj_sh,Proj_fr).

%------------------------------------------------------------------------%
% project_freeness(+,+,-)                                                %
% project_freeness(Vars,ListFreenessValues,Proj)                         %
% Eliminates from each list in the second argument any variable/Value    %
% such that the variable is not an element of the first argument         %
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).

:- export(project_freeness/3).
project_freeness([],_,Proj):- !,
    Proj = [].
project_freeness(_,[],Proj):- !,
    Proj = [].
project_freeness([Head1|Tail1],[Head2/Val|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    project_freeness(Order,Head1,Tail1,Head2/Val,Tail2,Proj).

project_freeness(=,_,Tail1,Head1,Tail2,[Head1|Proj]) :-
    project_freeness(Tail1,Tail2,Proj).
project_freeness(>,Head1,Tail1,_,[Head2/Val|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    project_freeness(Order,Head1,Tail1,Head2/Val,Tail2,Proj).

:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfr_call_to_entry(+,+,+,+,+,+,+,-,-)                                  %
% shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)            %
% It obtains the abstract substitution (Entry) which results from adding %
% the abstraction of the Sg = Head to Proj, later projecting the         %
% resulting substitution onto Hv. This is done as follows:               %
%  * If Sg and Head are identical up to renaming it is just a question   %
%    or renaming Proj and adding the Fv                                  %
%  * If Hv = [], Entry is just adding the Fv                             %
%  * Otherwise, it will                                                  %
%    - obtain in Binds the primitive equations corresponding to Sg=Head  %
%    - add to Proj_fr the variables in Hv as free variables (Temp1_fr)   %
%    - update Temp1_fr, Proj_sh (grounding some variables) and Binds     %
%      (eliminating those elements (X,Term,Tv) s.t. X or Term are        %
%       ground), obtaining Temp2_fr, NewProj_sh, and NewBind             %
%    - insert Fv in Temp2_fr as free variables (Temp3_fr)                %
%    - changes any nf(_,_) in temp3_fr to nf (Beta_fr)                   %
%    - projects Beta_fr onto Hv obtaining Entry_fr                       %
%    - Obtains in Share a first approximation of the sharing defined     %
%      over the variables of Sg and Head based on Bindings, NewProj_sh   %
%      and Temp3_fr                                                      %
%    - Projects Share over Hv and obtains in Beta_sh the powerset of each%
%      set in the projected sharing                                      %
%    - then it obtains in ShareArgsStar the star of the sharing among    %
%      the arguments of Sg established by NewProj_sh, and in Head_args   %
%      the set of variables belonging to each argument of Head           %
%    - Then the idea is to obtain Entry_sh by eliminating from Beta_sh   %
%      those sets which are not allowed (they would imply sharing among  %
%      arguments in the head while there is no sharing among those       %
%      arguments in ShareArgsStar)                                       %
%------------------------------------------------------------------------%
:- export(shfr_call_to_entry/9).
shfr_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
    variant(Sg,Head),!,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj)),
    Head = NewTerm,
    shfr_abs_sort(NewProj,(Temp_sh,Temp_fr)),
    change_values_insert(Fv,Temp_fr,Entry_fr,f),    
    list_to_list_of_lists(Fv,Temp1),
    merge(Temp1,Temp_sh,Entry_sh),
    Entry = (Entry_sh,Entry_fr).
shfr_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
    list_to_list_of_lists(Fv,Entry_sh),
    change_values_insert(Fv,[],Entry_fr,f),
    Entry = (Entry_sh,Entry_fr).
shfr_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,(Proj_sh,Proj_fr),Entry,ExtraInfo):-
%%%% freeness and initial sharing
    simplify_equations(Sg,Head,Binds),
    change_values_insert(Hv,Proj_fr,Temp1_fr,f),
    abs_unify_entry(Temp1_fr,Proj_sh,Binds,Hv,Temp2_fr,NewProj_sh,NewBind),
    change_values_insert(Fv,Temp2_fr,Temp3_fr,f),
    collapse_non_freeness(Temp3_fr,Beta_fr),
    merge(Hv,Fv,Cvars),
    project_freeness(Cvars,Beta_fr,Entry_fr),
%%%%%% sharing
    partition_sf(NewBind,Temp3_fr,NewProj_sh,Share),
    project_share(Hv,Share,Project_sh),
    powerset_of_set_of_sets(Project_sh,Beta_sh),
    script_p_star(Sg,NewProj_sh,ShareArgsStar),
    varset_in_args(Head,Head_args),
    list_to_list_of_lists(Fv,Temp1),
    prune(Beta_sh,Head_args,ShareArgsStar,Temp1,Entry_sh),
    Entry = (Entry_sh,Entry_fr),
%%%%% ExtrInfo
    project_freeness_n(Proj_fr,Beta_fr,N_Lda_fr),
    ExtraInfo = ((NewProj_sh,N_Lda_fr),Binds),
    !.

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfr_exit_to_prime(+,+,+,+,+,-,-)                                      %
% shfr_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                 %
% It computes the prime abstract substitution Prime, i.e.  the result of %
% going from the abstract substitution over the head variables (Exit), to%
% the abstract substitution over the variables in the subgoal. It will:  %
% * If Exit is '$bottom', Prime will be also '$bottom'.                  %
% * If Flag = yes (Head and Sg identical up to renaming) it is just a    %
%   question or renaming Exit                                            %
% * If Hv = [], Prime_sh = [] and Prime_fr = {X/g| forall X in Sv}       %
% * Otherwise:                                                           %
%------------------------------------------------------------------------%
:- export(shfr_exit_to_prime/7).
shfr_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
shfr_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    shfr_project(Sg,Hv,not_provided_HvFv_u,Exit,(BPrime_sh,BPrime_fr)),
    copy_term((Head,(BPrime_sh,BPrime_fr)),(NewTerm,NewPrime)),
    Sg = NewTerm,
    shfr_abs_sort(NewPrime,Prime).  
shfr_exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
    list_ground(Sv,Prime_fr),
    Prime = ([],Prime_fr).
shfr_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo = ((Lda_sh,Lda_fr),Binds),
    shfr_project(Sg,Hv,not_provided_HvFv_u,Exit,(BPrime_sh,BPrime_fr)),
    merge(Lda_fr,BPrime_fr,TempFr),
    abs_unify_exit(TempFr,Binds,NewTempFr,NewBinds),
    member_value_freeness(NewTempFr,Gv,g),
    ord_split_lists_from_list(Gv,Lda_sh,_Intersect,Sg_sh),
    merge(Sg_sh,BPrime_sh,Shtemp),
    partition_sf(NewBinds,NewTempFr,Shtemp,Share),
    project_share(Sv,Share,Project_sh),
    powerset_of_set_of_sets(Project_sh,Sup_Prime_sh),
    collapse_non_freeness(NewTempFr,Sup_lda_fr),
    project_freeness(Sv,Sup_lda_fr,Prime_fr),
%%%%% sharing
    script_p(Head,BPrime_sh,ShareArgs),
    varset_in_args(Sg,Sg_args),
    ord_intersection_diff(Sup_Prime_sh,Lda_sh,Intersect,Disjoint),
    covering(Disjoint,Lda_sh,AlsoPossible),
    merge(Intersect,AlsoPossible,Lda_sh_temp),
    prune(Lda_sh_temp,Sg_args,ShareArgs,Prime_sh), 
    Prime = (Prime_sh,Prime_fr),
    !.

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT SORT
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% shfr_abs_sort(+,-)                                                         |
% shfr_abs_sort(Asub,Asub_s)                                                 |
% First sorts the set of set of variables Sh to obtain the Sh_s.Then it  |
% sorts the set of X/Value in Fr obtaining Fr_s.                         |
%-------------------------------------------------------------------------
:- export(shfr_abs_sort/2).        
shfr_abs_sort('$bottom','$bottom').
shfr_abs_sort(ac(Asub_u,Fg),ac(Asub,Fg)):- 
    shfr_abs_sort(Asub_u,Asub).
shfr_abs_sort(d((Sh,Fr),Del),d((Sh_s,Fr_s),Del)):- 
    sort_list_of_lists(Sh,Sh_s),
    sort(Fr,Fr_s).
shfr_abs_sort((Sh,Fr),(Sh_s,Fr_s)):-
    sort_list_of_lists(Sh,Sh_s),
    sort(Fr,Fr_s).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT LUB
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% shfr_compute_lub(+,-)                                                  %
% shfr_compute_lub(ListASub,Lub)                                         %
% It computes the lub of a set of Asub. For each two abstract            %
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   %
% (1) merging the Sh1 and Sh2                                            %
% (2) foreach X/Value1 in Fr1 and X/Value2 in Fr2:                       %
%    - if Value1 == Value2, X/Value1 in Lub_fr                           %
%    - otherwise, X/nf in Lub_fr                                         %
%------------------------------------------------------------------------%
:- export(shfr_compute_lub/2). 
shfr_compute_lub([X],X):- !.
shfr_compute_lub([ASub1,ASub2|Xs],Lub):-
    shfr_compute_lub_el(ASub1,ASub2,ASubLub),
    shfr_compute_lub([ASubLub|Xs],Lub).

:- export(shfr_compute_lub_el/3).  %% commented out by JNL
shfr_compute_lub_el('$bottom',ASub,ASub):- !.
shfr_compute_lub_el((Sh1,Fr1),(Sh2,Fr2),(Lub_sh,Lub_fr)):- !,
    compute_lub_sh(Sh1,Sh2,Lub_sh),
    compute_lub_fr(Fr1,Fr2,Lub_fr).
shfr_compute_lub_el(ASub,_,ASub).

:- export(compute_lub_sh/3).
compute_lub_sh(Sh1,Sh2,Sh1) :-
    Sh1 == Sh2,!.
compute_lub_sh(Sh1,Sh2,Lub) :-
    merge(Sh1,Sh2,Lub).

compute_lub_fr(Fr1,Fr2,Lub):- 
    Fr1 == Fr2, !,
    Lub = Fr1.
compute_lub_fr([Xv|Fr1],[Yv|Fr2],Lub):- 
    Xv == Yv, !,
    Lub = [Xv|Lub_fr],
    compute_lub_fr(Fr1,Fr2,Lub_fr).
compute_lub_fr([X/_|Fr1],[X/_|Fr2],[X/nf|Lub_fr]):-
    compute_lub_fr(Fr1,Fr2,Lub_fr).

%------------------------------------------------------------------------%
% shfr_glb(+,+,-)                                                        %
% shfr_glb(ASub0,ASub1,Glb)                                              %
%------------------------------------------------------------------------%
:- export(shfr_glb/3).       
shfr_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
shfr_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
shfr_glb((Sh1,Fr1),(Sh2,Fr2),Glb):-
    member_value_freeness(Fr1,FVars1,f),
    member_value_freeness(Fr2,FVars2,f),
    member_value_freeness(Fr1,GVars1,g),
    member_value_freeness(Fr2,GVars2,g),
    ord_intersection(FVars1,GVars2,Empty1),
    ord_intersection(FVars2,GVars1,Empty2),
    ( (Empty1 \== []; Empty2 \== [])
    -> Glb = '$bottom'
     ; merge(FVars1,FVars2,FVars),
       merge(GVars1,GVars2,GVars0),
       share_glb(Sh1,Sh2,Glb_sh),
       varset(Fr1,All),
       varset(Glb_sh,Now),
       ord_subtract(All,Now,NewGVars),
       merge(GVars0,NewGVars,GVars),
       ord_intersection(FVars,GVars,Empty),
       ( Empty \== []
       -> Glb = '$bottom'
        ; Glb = (Glb_sh,Glb_fr),
          change_values_insert(FVars,Fr1,TmpFr,f),
          change_values_insert(GVars,TmpFr,Glb_fr,g)
    )  ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% shfr_extend(+,+,+,+,-)                                                 %
% shfr_extend(Sg,Prime,Sv,Call,Succ)                                     %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ.             %
% Otherwise, Succ_sh is computed as in share_extend/5, i.e. it splits    %
% Call_sh into two set of sets: Intersect (those sets containing         %
% at least a variabe in Sv) and Disjunct (the rest). Then it obtains     %
% in Star the closure under union of Intersect. Finally, it prunes Star  %
% with the information in Prime_sh adding, at the end, Disjunct.         %
% Call_fr is computed by:                                                %
%   * obtainig in NewGv the set of variables which have becomed ground   %
%     (those which were not ground in Call but are ground in Succ_sh)    %
%   * adding this NewGv variables to Prime_fr, obtaining Temp1_fr        %
%   * obtaining in BVars the set of nonground variables in Succ which do %
%     not belong to Sg (ar not in Sv)                                    %
%   * Then it obtains in BVarsf the subset of BVars which are free w.r.t %
%     Call_fr, and in Temp2_fr, the result of adding X/nf to Temp1_fr    %
%     for the rest of variables in BVars                                 %
%   * If BVarsf = [],                                                    %
%------------------------------------------------------------------------%
:- export(shfr_extend/5).      
shfr_extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
shfr_extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
shfr_extend(_Sg,(Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),Succ):-
%-extend_sh
    ord_split_lists_from_list(Sv,Call_sh,Intersect,Disjunct),
    closure_under_union(Intersect,Star),
    eliminate_non_element(Sv,Star,Prime_sh,Extended),
    merge(Extended,Disjunct,Succ_sh),
%-extend_fr
    member_value_freeness_differ(Call_fr,NonGvCall,g),
    merge_list_of_lists(Succ_sh,NonGvSucc),
    ord_subtract(NonGvCall,NonGvSucc,NewGv),
    change_values_insert(NewGv,Prime_fr,Temp1_fr,g),
    ord_subtract(NonGvSucc,Sv,BVars),
    non_free_vars(BVars,Call_fr,Temp1_fr,BVarsf,Temp2_fr),
    ( BVarsf = [] ->
      Temp3_fr = Temp2_fr
    ; member_value_freeness(Prime_fr,NonFree,nf),
      propagate_non_freeness(BVarsf,NonFree,Succ_sh,Temp2_fr,Temp3_fr)
    ),
    add_environment_vars(Temp3_fr,Call_fr,Succ_fr),
    Succ = (Succ_sh,Succ_fr), !.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------
:- export(shfr_call_to_success_fact/9).
shfr_call_to_success_fact(_Sg,[],_Head,_K,Sv,Call,_Proj,Prime,Succ) :- 
    Call = (Call_sh,Call_fr),!,
    update_lambda_sf(Sv,Call_fr,Call_sh,Succ_fr,Succ_sh),
    list_ground(Sv,Prime_fr),
    Prime = ([],Prime_fr),
    Succ = (Succ_sh,Succ_fr).
shfr_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,(Sg_sh,Lda_fr),Prime,Succ) :-
% call_to_entry      -------------------------------------------------
    simplify_equations(Sg,Head,Binds), !,
    change_values_insert(Hv,Lda_fr,Lda_fr_all,f),
    abs_unify_entry(Lda_fr_all,Sg_sh,Binds,Hv,New_Lda_fr,New_Sg_sh,E),
    partition_sf(E,New_Lda_fr,New_Sg_sh,Share),
    project_share(Hv,Share,Project_sh),
    powerset_of_set_of_sets(Project_sh,Beta_sh),
    collapse_non_freeness(New_Lda_fr,Entry_fr),
    script_p_star(Sg,New_Sg_sh,ShareArgsStar),
    varset_in_args(Head,Head_args),
    prune(Beta_sh,Head_args,ShareArgsStar,Entry_sh),
% exit_to_prime      -------------------------------------------------
    project_share(Sv,Share,New_Project_sh),
    powerset_of_set_of_sets(New_Project_sh,Sup_Prime_sh),
    project_freeness(Sv,Entry_fr,Prime_fr),
    script_p(Head,Entry_sh,ShareArgs),
    varset_in_args(Sg,Sg_args),
    ord_intersection_diff(Sup_Prime_sh,New_Sg_sh,Intersect,Disjoint),
    covering(Disjoint,New_Sg_sh,AlsoPossible),
    merge(Intersect,AlsoPossible,Lda_sh_temp),
    prune(Lda_sh_temp,Sg_args,ShareArgs,Prime_sh),
    Prime = (Prime_sh,Prime_fr),
    shfr_extend(Sg,Prime,Sv,Call,Succ).
shfr_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%-------------------------------------------------------------------------
% Specialised version of shfr_call_to_success_fact in order to allow     |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%-------------------------------------------------------------------------
:- export(shfr_call_to_prime_fact/6).
shfr_call_to_prime_fact(_,[],_,Sv,_,Prime) :- !,
    list_ground(Sv,Prime_fr),
    Prime = ([],Prime_fr).
shfr_call_to_prime_fact(Sg,Hv,Head,Sv,(Proj_sh,Proj_fr),Prime) :-
% call_to_entry      -------------------------------------------------
    simplify_equations(Sg,Head,Binds), !,
    change_values_insert(Hv,Proj_fr,Proj_fr_all,f),
    abs_unify_entry(Proj_fr_all,Proj_sh,Binds,Hv,NewProj_fr,NewProj_sh,E),
    partition_sf(E,NewProj_fr,NewProj_sh,Share),
    project_share(Hv,Share,Project_sh),
    powerset_of_set_of_sets(Project_sh,Beta_sh),
    collapse_non_freeness(NewProj_fr,Entry_fr),
    script_p_star(Sg,NewProj_sh,ShareArgsStar),
    varset_in_args(Head,Head_args),
    prune(Beta_sh,Head_args,ShareArgsStar,[],Entry_sh),
% exit_to_prime      -------------------------------------------------
    project_share(Sv,Share,NewProject_sh),
    powerset_of_set_of_sets(NewProject_sh,Sup_Prime_sh),
    project_freeness(Sv,Entry_fr,Prime_fr),
    script_p(Head,Entry_sh,ShareArgsHead),
    varset_in_args(Sg,Sg_args),
    closure_under_union(NewProj_sh,Star),
    ord_intersection(Sup_Prime_sh,Star,Lda_sh_temp),
    prune(Lda_sh_temp,Sg_args,ShareArgsHead,[],Prime_sh),
    Prime = (Prime_sh,Prime_fr).
shfr_call_to_prime_fact(_Sg,_Hv,_Head,_Sv,'$bottom','$bottom').

%-------------------------------------------------------------------------
% shfr_unknown_entry(+,+,-)                                              |
% shfr_unknown_entry(Sg,Qv,Call)                                         |
% The top value in Sh for a set of variables is the powerset, in Fr is   |
% X/nf forall X in the set of variables                                  |
%-------------------------------------------------------------------------
:- export(shfr_unknown_entry/3).
shfr_unknown_entry(_Sg,Qv,Call):-
    powerset(Qv,Sh),
    sort_list_of_lists(Sh,Call_sh),
    create_values(Qv,Call_fr,nf),
    Call=(Call_sh,Call_fr).

%-------------------------------------------------------------------------
% shfr_empty_entry(+,+,-)                                                  |
% The empty value in Sh for a set of variables is the list of singletons,
% in Fr is X/f forall X in the set of variables                          |
%-------------------------------------------------------------------------
:- export(shfr_empty_entry/3).
:- pred shfr_empty_entry(+Sg,+Vars,-Entry): callable * list * absu # "Gives the
""empty"" value in this domain for a given set of variables
@var{Vars}, resulting in the abstract substitution @var{Entry}. I.e.,
obtains the abstraction of a substitution in which all variables
@var{Vars} are unbound: free and unaliased. In Sh is the list of
singleton lists of variables and in Fr is X/f forall X in the set of
variables".
shfr_empty_entry(_Sg,Qv,Entry):-
    list_to_list_of_lists(Qv,Entry_sh),
    create_values(Qv,Entry_fr,f),
    Entry=(Entry_sh,Entry_fr).

%------------------------------------------------------------------------%
% shfr_input_user_interface(+,+,-,+,+)                                   %
% shfr_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)          %
% Obtaining the abstract substitution for Sh+Fr from the user supplied   %
% information just consists in taking the Sharing first and the var(Fv)  %
% element of InputUser, and construct from them the Freeness.            %
%------------------------------------------------------------------------%
:- export(shfr_input_user_interface/5).
shfr_input_user_interface((Sh,Fv0),Qv,(Call_sh,Call_fr),Sg,MaybeCallASub):-
    share_input_user_interface(Sh,Qv,Call_sh,Sg,MaybeCallASub),
    may_be_var(Fv0,Fv),
    merge_list_of_lists(Call_sh,SHv),
    ord_subtract(Qv,SHv,Gv),
    ord_subtract(SHv,Fv,NonFv),
    create_values(Fv,Temp1,f),
    change_values_insert(NonFv,Temp1,Temp2,nf),
    change_values_insert(Gv,Temp2,Call_fr,g).

:- export(shfr_input_interface/4).
shfr_input_interface(Info,Kind,(Sh0,Fr),(Sh,Fr)):-
    share_input_interface(Info,Kind,Sh0,Sh), !.
shfr_input_interface(free(X),perfect,(Sh,Fr0),(Sh,Fr)):-
    var(X),
    myinsert(Fr0,X,Fr).

myinsert(Fr0,X,Fr):-
    var(Fr0), !,
    Fr = [X].
myinsert(Fr0,X,Fr):-
    insert(Fr0,X,Fr).

may_be_var(X,X):- ( X=[] ; true ), !.

%% %------------------------------------------------------------------------%
%% % shfr_output_interface(+,-)                                             %
%% % shfr_output_interface(ASub,Output)                                     %
%% % The readible format still close to the internal formal is identical    %
%% % for the Sharing part. The output for Fr is the set of free variables   %
%% %-------------------------------------------------------------------------
%% 
%:- export(shfr_output_interface/2).
%% shfr_output_interface(ac('$bottom',Flag),('$bottom',Flag)) :- !.
%% shfr_output_interface(ac(d((Sh,Fr),Del),Flag),Output) :- 
%%      member_value_freeness(Fr,NewFr,f),
%%      del_output(ac(Del,Flag),(Sh,NewFr),Output).
%% shfr_output_interface(d((Sh,Fr),Del),Output) :- 
%%      member_value_freeness(Fr,NewFr,f),
%%      del_output(Del,(Sh,NewFr),Output).
%% shfr_output_interface((Sh,Fr),(Sh,NewFr)) :-
%%      member_value_freeness(Fr,NewFr,f).
%% shfr_output_interface('$bottom','$bottom').
%% shfr_output_interface([],[]).
%% shfr_output_interface([Succ],OutSucc):- !,
%%      shfr_output_interface(Succ,OutSucc).
%% shfr_output_interface([Succ|LSucc],[OutSucc|LOutSucc]):-
%%      shfr_output_interface(Succ,OutSucc),
%%      shfr_output_interface0(LSucc,LOutSucc).
%% 
%% shfr_output_interface0([],[]).
%% shfr_output_interface0([Succ|LSucc],[OutSucc|LOutSucc]):-
%%      shfr_output_interface(Succ,OutSucc),
%%      shfr_output_interface0(LSucc,LOutSucc).

%------------------------------------------------------------------------%
% shfr_asub_to_native(+,+,+,-,-)                                         %
% shfr_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                   %
% The user friendly format consists in extracting the ground variables   %
% and the free variables                                                 %
%------------------------------------------------------------------------%
:- export(shfr_asub_to_native/5).
shfr_asub_to_native(ASub,_Qv,_OutFlag,Succ,[]) :-
    shfr_asub_to_native_(ASub,Succ).

shfr_asub_to_native_(ac(ASub,Flag),[flag(Flag)|ASub_user]):- 
    shfr_asub_to_native_(ASub,ASub_user).
%% shfr_asub_to_native(ac(ASub,_),ASub_user):- 
%%      shfr_asub_to_native(ASub,ASub_user).
shfr_asub_to_native_(d((Sh,Fr),Del),ASub_user):- 
    shfr_asub_to_native_((Sh,Fr),Info),
    if_not_nil(Del,delayed(Del),Comp,[]),
    ( Comp==[] -> ASub_user=comp(Info,Comp) ; ASub_user=Info ).
shfr_asub_to_native_((Sh,Fr),Info):-
    if_not_nil(Sh,sharing(Sh),Info,Info0),
    member_value_freeness(Fr,Fv,f),
    if_not_nil(Fv,free(Fv),Info0,Info1),
    member_value_freeness(Fr,Gv,g),
    if_not_nil(Gv,ground(Gv),Info1,[]).
% fail:
% shfr_asub_to_native_('$bottom',[solutions(0)]).

%------------------------------------------------------------------------%
% shfr_obtain_info(+,+,+,-)                                              %
% shfr_obtain_info(Prop,Vars,ASub,Info)                                  %
% Prop holds for Info in ASub over Vars                                  %
%------------------------------------------------------------------------%
:- export(shfr_obtain_info/4).
shfr_obtain_info(ground,Vars,(_,Fr),Info):-
    member_value_freeness(Fr,Info0,g),
    ord_intersection(Vars,Info0,Info).
shfr_obtain_info(free,Vars,(_,Fr),Info):-
    member_value_freeness(Fr,Info0,f),
    ord_intersection(Vars,Info0,Info).

%------------------------------------------------------------------------%
% shfr_obtain_info(+,+,-)                                                %
% shfr_obtain_info(Prop,ASub,Info)                                       %
% Prop holds for Info in ASub                                            %
%------------------------------------------------------------------------%
:- export(shfr_obtain_info/3).
shfr_obtain_info(ground,(_,Fr),Info):-
    member_value_freeness(Fr,Info,g).
shfr_obtain_info(free,(_,Fr),Info):-
    member_value_freeness(Fr,Info,f).

%------------------------------------------------------------------------%
% shfr_less_or_equal(+,+)                                                %
% shfr_less_or_equal(ASub0,ASub1)                                        %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%
:- export(shfr_less_or_equal/2).
shfr_less_or_equal('$bottom',_ASub):- !.
shfr_less_or_equal((Sh0,Fr0),(Sh1,Fr1)):-
    share_less_or_equal(Sh0,Sh1),
    member_value_freeness(Fr0,ListFr0,f),
    member_value_freeness(Fr1,ListFr1,f),
    ord_subset(ListFr1,ListFr0).

%% %------------------------------------------------------------------------%
%% % shfr_more_instantiate(+,+)                                             %
%% % shfr_more_instantiate(ASub0,ASub1)                                     %
%% % Succeeds if ASub1 is possibly more instantiated or equal to ASub0. In  %
%% % fact what we want to prove is that ASub1 corresponds to a node in the  %
%% % abstract ADN-OR tree which is greater than that of ASub0 (so it must   %
%% % be more instantiated)                                                  %
%% % By now, this means:                                                    %
%% %        - everything ground in ASub0 is ground in ASub1 (the reason for %
%% %          this is that groundness is downwards closed and thus is not   %
%% %          lost through lub, projection, etc)                            %
%% %        - for each X free in ASub1, X cannot be ground in ASub0, neither%
%% %          nonvar.                                                       %
%% % WARNING, incomplete since definite dependencies in ASub0 afecting      %
%% % variables which are also free in ASub1, must appear in ASub1           %
%% %------------------------------------------------------------------------%
%% 
%:- export(shfr_more_instantiate/2).  
%% shfr_more_instantiate((Sh0,Fr0),(Sh1,Fr1)):-
%%         member_value_freeness(Fr0,ListGr0,g),
%%         member_value_freeness(Fr1,ListGr1,g),
%%         ord_subset(ListGr0,ListGr1),
%%         member_value_freeness(Fr1,ListFr1,f),
%%         ord_intersection(ListFr1,ListGr0,[]),
%%         member_value_freeness(Fr0,ListFr0,f),
%%      ( ListFr1 = [] ->
%%          true
%%      ;  \+ (mynonvar(ListFr1,Sh0,ListFr0))
%%         ),
%%      ord_subtract(Sh1,Sh0,Disj),
%%      merge_list_of_lists(Disj,Vars),
%%      ord_split_lists_from_list(Vars,Sh0,Int,_),
%%      closure_under_union(Int,Star),
%%      ord_subset(Disj,Star),!.

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% shfr_special_builtin(+,+,+,-,-)                                        |
% shfr_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                   |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) new_ground if the builtin makes all variables ground whithout      |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) old_ground if the builtin requires the variables to be ground      |
% (3) old_new_ground" if the builtin requires some variables to be       |
%     ground and grounds the rest                                        |
% (4) unchanged if we cannot infer anything from the builtin, the        |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previous freeness values of the variables.                  |
% (5) some if it makes some variables ground without imposing conditions |
% (6) all_nonfree if the builtin makes all variables possible non free   |
% (6) Sgkey, special handling of some particular builtins                |
%-------------------------------------------------------------------------

:- export(shfr_special_builtin/5).
%-------------------------------------------------------------------------
% metacuts
%% shfr_special_builtin('CHOICE IDIOM/1',_,_,new_ground,_).
%% shfr_special_builtin('CUT IDIOM/1',_,_,old_ground,_).
%% shfr_special_builtin('$metachoice/1',_,_,new_ground,_).
%% shfr_special_builtin('$metacut/1',_,_,old_ground,_).
%% shfr_special_builtin(':/2',(prolog:'$metachoice'(_)),_,new_ground,_).
%% shfr_special_builtin(':/2',(prolog:'$metacut'(_)),_,old_ground,_).
%%%% TODO: Missing cuts in all the following clauses
shfr_special_builtin('metachoice/1',_,_,new_ground,_).
shfr_special_builtin('metacut/1',_,_,old_ground,_).
%-------------------------------------------------------------------------
shfr_special_builtin('current_atom/1',_,_,new_ground,_).
shfr_special_builtin('current_input/1',_,_,new_ground,_).
shfr_special_builtin('current_module/1',_,_,new_ground,_).
shfr_special_builtin('current_output/1',_,_,new_ground,_).
shfr_special_builtin('current_op/3',_,_,new_ground,_).
shfr_special_builtin('depth/1',_,_,new_ground,_).
shfr_special_builtin('get_code/1',_,_,new_ground,_).
shfr_special_builtin('get1_code/1',_,_,new_ground,_).
shfr_special_builtin('seeing/1',_,_,new_ground,_).
shfr_special_builtin('telling/1',_,_,new_ground,_).
shfr_special_builtin('statistics/2',_,_,new_ground,_).
%-------------------------------------------------------------------------
shfr_special_builtin('op/3',_,_,old_ground,_).
shfr_special_builtin('save_event_trace/1',_,_,old_ground,_).
shfr_special_builtin('close/1',_,_,old_ground,_).
%-------------------------------------------------------------------------
shfr_special_builtin('abort/0',_,_,bottom,_).
shfr_special_builtin('fail/0',_,_,bottom,_).
shfr_special_builtin('false/0',_,_,bottom,_).
shfr_special_builtin('halt/0',_,_,bottom,_).
%-------------------------------------------------------------------------
shfr_special_builtin('!/0',_,_,unchanged,_).
shfr_special_builtin('assert/1',_,_,unchanged,_).
shfr_special_builtin('asserta/1',_,_,unchanged,_).
shfr_special_builtin('assertz/1',_,_,unchanged,_).
shfr_special_builtin('debug/0',_,_,unchanged,_).
shfr_special_builtin('debugging/0',_,_,unchanged,_).
shfr_special_builtin('dif/2',_,_,unchanged,_).
shfr_special_builtin('display/1',_,_,unchanged,_).
shfr_special_builtin('flush_output/0',_,_,unchanged,_).
shfr_special_builtin('garbage_collect/0',_,_,unchanged,_).
shfr_special_builtin('gc/0',_,_,unchanged,_).
shfr_special_builtin('listing/0',_,_,unchanged,_).
shfr_special_builtin('listing/1',_,_,unchanged,_).
shfr_special_builtin('nl/0',_,_,unchanged,_).
shfr_special_builtin('nogc/0',_,_,unchanged,_).
shfr_special_builtin('not/1',_,_,unchanged,_).
shfr_special_builtin('print/1',_,_,unchanged,_).
shfr_special_builtin('repeat/0',_,_,unchanged,_).
shfr_special_builtin('start_event_trace/0',_,_,unchanged,_).
shfr_special_builtin('stop_event_trace/0',_,_,unchanged,_).
shfr_special_builtin('seen/0',_,_,unchanged,_).
shfr_special_builtin('told/0',_,_,unchanged,_).
shfr_special_builtin('true/0',_,_,unchanged,_).
shfr_special_builtin('ttyflush/0',_,_,unchanged,_).
shfr_special_builtin('otherwise/0',_,_,unchanged,_).
shfr_special_builtin('ttynl/0',_,_,unchanged,_).
shfr_special_builtin('write/1',_,_,unchanged,_).
shfr_special_builtin('writeq/1',_,_,unchanged,_).
% SICStus3 (ISO)
%meta! (no need) shfr_special_builtin('\\+/1',_,_,unchanged,_).
shfr_special_builtin('\\==/2',_,_,unchanged,_).
% SICStus2.x
% shfr_special_builtin('\+/1',_,_,unchanged,_).
% shfr_special_builtin('\==/2',_,_,unchanged,_).
shfr_special_builtin('@>=/2',_,_,unchanged,_).
shfr_special_builtin('@=</2',_,_,unchanged,_).
shfr_special_builtin('@>/2',_,_,unchanged,_).
shfr_special_builtin('@</2',_,_,unchanged,_).
%
shfr_special_builtin('rt_module_exp/6',_,_,unchanged,_).
%-------------------------------------------------------------------------
shfr_special_builtin('read/1',_,_,all_nonfree,_).
shfr_special_builtin('read/2',read(X,Y),_,read2,p(X,Y)).
%-------------------------------------------------------------------------
shfr_special_builtin('atom/1',_,_,old_ground,_).
shfr_special_builtin('atomic/1',_,_,old_ground,_).
shfr_special_builtin('ensure_loaded/1',_,_,old_ground,_).
shfr_special_builtin('erase/1',_,_,old_ground,_).
shfr_special_builtin('float/1',_,_,old_ground,_).
shfr_special_builtin('flush_output/1',_,_,old_ground,_).
shfr_special_builtin('int/1',_,_,new_ground,_).
shfr_special_builtin('integer/1',_,_,old_ground,_).
shfr_special_builtin('num/1',_,_,new_ground,_).
shfr_special_builtin('number/1',_,_,old_ground,_).
shfr_special_builtin('nl/1',_,_,old_ground,_).
shfr_special_builtin('put_code/1',_,_,old_ground,_).
shfr_special_builtin('put_code/2',_,_,old_ground,_).
shfr_special_builtin('see/1',_,_,old_ground,_).
shfr_special_builtin('tell/1',_,_,old_ground,_).
shfr_special_builtin('tab/1',_,_,old_ground,_).
shfr_special_builtin('tab/2',_,_,old_ground,_).
shfr_special_builtin('ttyput/1',_,_,old_ground,_).
shfr_special_builtin('=:=/2',_,_,old_ground,_).
shfr_special_builtin('>=/2',_,_,old_ground,_).
shfr_special_builtin('>/2',_,_,old_ground,_).
shfr_special_builtin('</2',_,_,old_ground,_).
shfr_special_builtin('=</2',_,_,old_ground,_).
% SICStus3 (ISO)
shfr_special_builtin('=\\=/2',_,_,old_ground,_).
% SICStus2.x
% shfr_special_builtin('=\=/2',_,_,old_ground,_).
shfr_special_builtin('ground/1',_,_,old_ground,_).
%-------------------------------------------------------------------------
shfr_special_builtin('absolute_file_name/2',absolute_file_name(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
shfr_special_builtin('get_code/2',get_code(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
shfr_special_builtin('get1_code/2',get1_code(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
shfr_special_builtin('is/2',is(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,NewG),
    varset(Y,OldG).
shfr_special_builtin('open/3',open(X,Y,Z),_,old_new_ground,(OldG,NewG)):-
    varset(p(X,Y),OldG),
    varset(Z,NewG).
shfr_special_builtin('format/2',format(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
shfr_special_builtin('format/3',format(X,Y,_Z),_,old_new_ground,(OldG,[])):-
    varset(p(X,Y),OldG).
shfr_special_builtin('predicate_property/2',predicate_property(_X,Y),_,old_new_ground,
                                                                    ([],NewG)):-
    varset(Y,NewG).
shfr_special_builtin('print/2',print(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
shfr_special_builtin('prolog_flag/2',prolog_flag(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
shfr_special_builtin('prolog_flag/3',prolog_flag(X,Y,Z),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(f(Y,Z),NewG).
shfr_special_builtin('write/2',write(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
%-------------------------------------------------------------------------
shfr_special_builtin('assert/2',assert(_X,Y),_,some,Vars):-
    varset(Y,Vars).
shfr_special_builtin('assertz/2',assertz(_X,Y),_,some,Vars):-
    varset(Y,Vars).
shfr_special_builtin('asserta/2',asserta(_X,Y),_,some,Vars):-
    varset(Y,Vars).
shfr_special_builtin('recorda/3',recorda(_X,_Y,Z),_,some,Vars):-
    varset(Z,Vars).
shfr_special_builtin('recordz/3',recordz(_X,_Y,Z),_,some,Vars):-
    varset(Z,Vars).
%%%%%%%%%% arg/3
shfr_special_builtin('arg/3',arg(X,Y,Z),_,arg,p(X,Y,Z)).
%%%%%%%%%% expand_term/2
shfr_special_builtin('expand_term/2',expand_term(X,Y),_,exp,p(X,Y)).
%%%%%%%%%% =../2
shfr_special_builtin('=../2','=..'(X,Y),_,'=../2',p(X,Y)).
%%%%%%%%%% recorded/3
shfr_special_builtin('recorded/3',recorded(_X,Y,Z),_,recorded,p(Y,Z)).
shfr_special_builtin('retract/1',retract(X),_,recorded,p(X,a)).
shfr_special_builtin('retractall/1',retractall(X),_,recorded,p(X,a)).
%%%%%%%%%% copy_term
shfr_special_builtin('copy_term/2',copy_term(X,Y),_,copy_term,p(X,Y)).
%%%%%%%%%% current_key/2
shfr_special_builtin('current_key/2',current_key(X,_Y),_,'current_key/2',p(X)).
%%%%%%%%%% current_predicate/2
shfr_special_builtin('current_predicate/2',current_predicate(X,Y),_,
                                           'current_predicate/2',p(X,Y)).
%%%%%%%%%% findall/3
%meta! (but needs special extension)
shfr_special_builtin('findall/3',findall(X,_,Z),_,findall,p(X,Z)).
%%%%%%%%%% functor/3
shfr_special_builtin('functor/3',functor(X,Y,Z),_,'functor/3',p(X,Y,Z)).
%%%%%%%%%% name/2
shfr_special_builtin('name/2',name(X,Y),_,'name/2',p(X,Y)).
%%%%%%%%%% nonvar/1
% shfr_special_builtin('nonvar/1',nonvar(X),_,'not_free/1',p(X)).
shfr_special_builtin('not_free/1',nonvar(X),_,'not_free/1',p(X)).
%%%%%%%%%% numbervars/3
shfr_special_builtin('numbervars/3',numbervars(X,Y,Z),_,'numbervars/3',p(X,Y,Z)).
%%%%%%%%%% compare/3
shfr_special_builtin('compare/3',compare(X,_Y,_Z),_,'compare/3',p(X)).
%%%%%%%%%% indep/2
shfr_special_builtin('indep/2',indep(X,Y),_,'indep/2',p(X,Y)).
%%%%%%%%%% length/2
shfr_special_builtin('length/2',length(X,Y),_,'length/2',p(X,Y)).
%%%%%%%%%% list/1
shfr_special_builtin('list/1',list(X),_,'list/1',p(X)).
%%%%%%%%%% var/1
% shfr_special_builtin('var/1',var(X),_,'free/1',p(X)).
shfr_special_builtin('free/1',free(X),_,'free/1',p(X)).
%%%%%%%%%% indep/1
shfr_special_builtin('indep/1',indep(X),_,'indep/1',p(X)).
%%%%%%%%%% others
shfr_special_builtin(Key,_Goal,_,special(Key),[]):-
    shfr_not_that_special_builtin(Key).

shfr_not_that_special_builtin('==/2').
shfr_not_that_special_builtin('=/2').
shfr_not_that_special_builtin('C/3').
shfr_not_that_special_builtin('keysort/2').
shfr_not_that_special_builtin('sort/2').

%-------------------------------------------------------------------------
% shfr_success_builtin(+,+,+,+,+,-)                                      |
% shfr_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                        |
% Obtains the success for some particular builtins:                      |
%  * If Type = new_ground, it updates Call making all vars in Sv_u ground|
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * If Type = old_ground, if grouds all variables in Sv and checks that |
%              no free variables has becomed ground                      |
%  * If Type = old_ground, if grounds all variables in OldG and checks   |
%              thatno free variables has becomed ground. If so, it       |
%              grounds all variables in NewG                             |
%  * If Type = all_non_free it projects Call onto this variables,        |
%              obatins the closure under union for the Sh, changes in    |
%              Fr all f to nf and later extends the result               |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%-------------------------------------------------------------------------
:- export(shfr_success_builtin/6).
shfr_success_builtin(new_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    Call = (Lda_sh,Lda_fr),
    update_lambda_sf(Sv,Lda_fr,Lda_sh,Succ_fr,Succ_sh), 
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin(bottom,_,_,_,_,'$bottom').
shfr_success_builtin(unchanged,_,_,_,Lda,Lda).
shfr_success_builtin(some,_Sv,NewGr,_,Call,Succ):-
    Call = (Call_sh,Call_fr),
    update_lambda_sf(NewGr,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin(old_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(Sv,Call_fr,Call_sh,Succ_fr,Succ_sh),!,
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin(old_ground,_,_,_,_,'$bottom').
shfr_success_builtin(old_new_ground,_,(OldG,NewG),_,Call,Succ):-
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin(old_new_ground,_,_,_,_,'$bottom').
shfr_success_builtin(all_nonfree,Sv_u,Sg,_,Call,Succ):- !,
    sort(Sv_u,Sv),
    shfr_project(Sg,Sv,not_provided_HvFv_u,Call,(Proj_sh,Proj_fr)),
    closure_under_union(Proj_sh,Prime_sh),
    change_values_if_f(Sv,Proj_fr,Prime_fr,nf),
    shfr_extend(Sg,(Prime_sh,Prime_fr),Sv,Call,Succ).
shfr_success_builtin(arg,_,p(X,Y,Z),_,Call,Succ):-
%% %% PBC: don't understand this... (only if var(Y)?)
%%      Call = (Call_sh,Call_fr),
%%      varset(X,OldG),
%%      update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
%%      var_value(Temp_fr,Y,Value),
%%      Value \== f,!,
    Call = (Call_sh,Call_fr),
    ( integer(X) -> true
    ; var(X),
      var_value(Call_fr,X,Value),
      Value \== f
    ), !,
    update_lambda_non_free([X],Call_fr,Call_sh,Temp_fr,Temp_sh),
    TempASub = (Temp_sh,Temp_fr),
    ( var(Y)->
      any_arg_var(Y,Z,p(f(A,_),A),TempASub,Succ)
     ; functor(Y,_,N),
       ( N=0 -> Succ = '$bottom'
       ; any_arg_all_args(N,Y,Z,TempASub,Succs),
         shfr_compute_lub(Succs,Succ)
       )
    ).
shfr_success_builtin(arg,_,_,_,_,'$bottom').
shfr_success_builtin(exp,_,Sg,_,Call,Succ):-
    Head = p(A,f(A,_B)),
    varset(Sg,Sv),
    varset(Head,Hv),
    shfr_project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    shfr_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
shfr_success_builtin(exp,_,_,_,_,'$bottom').
shfr_success_builtin('=../2',_,p(X,Y),_,(Call_sh,Call_fr),Succ):-
    varset(X,Varsx),
    values_equal(Varsx,Call_fr,g),!,
    varset(Y,VarsY),
    update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('=../2',_,p(X,Y),_,(Call_sh,Call_fr),Succ):-
    varset(Y,VarsY),
    values_equal(VarsY,Call_fr,g),!,
    varset(X,VarsX),
    update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('=../2',Sv_uns,p(X,Y),_,Call,Succ):-
    var(X), var(Y),!,
    sort(Sv_uns,Sv),
    Call = (_,Call_fr),
    project_freeness(Sv,Call_fr,[A/Val1,B/Val2]),
    ( obtain_freeness(Val1,Val2) ->
        shfr_extend(not_provided_Sg,([Sv],[A/nf,B/nf]),Sv,Call,Succ)
    ; Succ = '$bottom'
    ).
shfr_success_builtin('=../2',Sv_uns,p(X,Y),_,Call,Succ):-
    var(X), !,
    sort(Sv_uns,Sv),
    Call = (Call_sh,Call_fr),       
    project_freeness(Sv,Call_fr,Proj_fr),
    Y = [Z|_],
    var_value(Proj_fr,X,ValueX),
    ( var(Z) ->
        var_value(Proj_fr,Z,ValueZ),
        ( ValueZ = f , ValueX = f ->
            Succ = '$bottom'
        ; ord_subtract(Sv,[Z],NewVars),
          project_share(NewVars,Call_sh,Proj_sh),
          ord_subtract(NewVars,[X],VarsY),
          product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
          shfr_extend(not_provided_Sg,(Prime_sh,Prime_fr),Sv,Call,Succ)
        )
    ; project_share(Sv,Call_sh,Proj_sh),
      ord_subtract(Sv,[X],VarsY),
      product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
      shfr_extend(not_provided_Sg,(Prime_sh,Prime_fr),Sv,Call,Succ)
    ).
shfr_success_builtin('=../2',Sv_uns,Sg,_,Call,Succ):- Sg=p(X,Y),
    X =.. T,
    sort(Sv_uns,Sv),
    shfr_project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    shfr_call_to_success_builtin('=/2','='(T,Y),Sv,Call,Proj,Succ).
shfr_success_builtin(read2,Sv_u,Sg,_,Call,Succ):- Sg=p(X,Y),
    varset(X,Varsx),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(Varsx,Call_fr,Call_sh,Temp_fr,Temp_sh),
    ( var(Y) ->
      change_values_if_f([Y],Temp_fr,Succ_fr,nf),
      Succ = (Temp_sh,Succ_fr)
    ; varset(Y,Varsy),
      shfr_project(Sg,Varsy,not_provided_HvFv_u,(Temp_sh,Temp_fr),(Proj_sh,Prime_fr)),
      closure_under_union(Proj_sh,Prime_sh),
      sort(Sv_u,Sv),
      shfr_extend(Sg,(Prime_sh,Prime_fr),Call,Sv,Succ)
    ).
shfr_success_builtin(recorded,_,Sg,_,Call,Succ):- Sg=p(Y,Z),
    varset(Z,NewG),
    varset(Y,VarsY),
    merge(NewG,VarsY,Vars),
    shfr_project(Sg,Vars,not_provided_HvFv_u,Call,(Sh,Fr)),
    update_lambda_sf(NewG,Fr,Sh,TempPrime_fr,TempPrime_sh),
    make_dependence(TempPrime_sh,VarsY,TempPrime_fr,Prime_fr,Prime_sh),
    Prime = (Prime_sh,Prime_fr),
    shfr_extend(Sg,Prime,Vars,Call,Succ).
shfr_success_builtin(copy_term,_,Sg,_,Call,Succ):- Sg=p(X,Y),
    varset(X,VarsX),
    shfr_project(Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    shfr_abs_sort(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    shfr_project(Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    ProjectedY = (ShY,FrY),
    ProjectedNewX = (ShNewX,FrNewX),
    merge(ShY,ShNewX,TempSh),
    merge(FrY,FrNewX,TempFr),
    Call = (ShCall,FrCall),
    merge(ShNewX,ShCall,TempCallSh),
    merge(FrNewX,FrCall,TempCallFr),
    shfr_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
    collect_vars_freeness(FrCall,VarsCall),
    shfr_project(Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
shfr_success_builtin('current_key/2',_,p(X),_,Call,Succ):-
    varset(X,NewG),
    Call = (Call_sh,Call_fr),
    update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('current_predicate/2',_,p(X,Y),_,Call,Succ):-
    var(Y),!,
    Call = (Call_sh,Call_fr),
    change_values_if_f([Y],Call_fr,Temp_fr,nf), 
    varset(X,NewG),
    update_lambda_sf(NewG,Temp_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('current_predicate/2',_,p(X,_Y),_,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    varset(X,NewG),
    update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin(findall,_,p(X,Z),_,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):-
    varset(X,Xs),
    member_value_freeness(Call_fr,GVars,g),
    ord_subset(Xs,GVars), !,
    varset(Z,Zs),
    update_lambda_sf(Zs,Call_fr,Call_sh,Succ_fr,Succ_sh).
shfr_success_builtin(findall,_,p(_,Z),_,Call,Succ):-
    varset(Z,Zs),
    shfr_unknown_call(sg_not_provided,Zs,Call,Succ).
shfr_success_builtin('functor/3',_,p(X,Y,Z),_,Call,Succ):-
    var(X),
    Call = (Call_sh,Call_fr),
    var_value(Call_fr,X,f),!,
    change_values([X],Call_fr,Temp_fr,nf), 
    varset([Y,Z],OldG),
    ( update_lambda_non_free(OldG,Temp_fr,Call_sh,Succ_fr,Succ_sh) ->
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ).
shfr_success_builtin('functor/3',_,p(_X,Y,Z),_,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    varset([Y,Z],NewG),
    update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('name/2',_,p(X,Y),_,Call,Succ):-
    varset(X,OldG),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    varset(Y,NewG),
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('name/2',_,p(X,Y),_,Call,Succ):-
    varset(Y,OldG),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    varset(X,NewG),
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('name/2',_,_,_,_,'$bottom').
shfr_success_builtin('not_free/1',_,p(X),_,Call,Succ):-
    var(X), !,
    Call = (_Call_sh,Call_fr),
    var_value(Call_fr,X,Val),
    ( Val = f ->
      Succ = '$bottom'
    ; Succ = Call
    ).
shfr_success_builtin('not_free/1',_,_,_,Call,Call):- !.
shfr_success_builtin('numbervars/3',_,p(X,Y,Z),_,Call,Succ):-
    Call = (Call_sh,Call_fr),
    varset(Y,OldG),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    varset(p(X,Z),NewG),
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('numbervars/3',_,_,_,_,'$bottom').
shfr_success_builtin('compare/3',_,p(X),_,Call,Succ):- 
    atom(X),!,
    Succ = Call.
shfr_success_builtin('compare/3',_,p(X),_,Call,Succ):- 
    var(X),!,
    Call = (Call_sh,Call_fr),
    update_lambda_sf([X],Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('compare/3',_,_,_,_,'$bottom').
shfr_success_builtin('indep/2',_,p(X,Y),_,Call,Succ):- 
    ( ground(X) ; ground(Y) ), !,
    Succ = Call.
shfr_success_builtin('indep/2',_,p(X,Y),_,Call,Succ):- 
    varset(X,Xv),
    varset(Y,Yv),
    Call = (Call_sh,Call_fr),
    varset(Call_fr,Vars),
    eliminate_couples(Call_sh,Xv,Yv,Succ_sh),
    projected_gvars(Succ_sh,Vars,Ground),
    change_values_if_differ(Ground,Call_fr,Succ_fr,g,f),!,
    Succ = (Succ_sh,Succ_fr).
shfr_success_builtin('indep/2',_,_,_,_,'$bottom').
shfr_success_builtin('indep/1',_,p(X),_,Call,Succ):- 
    nonvar(X),
    handle_each_indep(X,shfr,Call,Succ), !.
shfr_success_builtin('indep/1',_,_,_,_,'$bottom').
shfr_success_builtin('length/2',_,p(X,Y),_,Call,Succ):-
    var(X),var(Y),!,
    Call = (_,Call_fr),
    var_value(Call_fr,X,Valuex),
    var_value(Call_fr,Y,Valuey),
    update_from_values(Valuex,Valuey,X,Y,Call,Succ).
shfr_success_builtin('length/2',_,p(X,_Y),_,Call,Succ):-
    var(X),!,
    Call = (Call_sh,Call_fr),
    take_coupled(Call_sh,[X],Coupled),
    change_values_if_f(Coupled,Call_fr,Succ_fr,nf),
    Succ = (Call_sh,Succ_fr).
% this is wrong: it is the tail of X which might not stay free (PBC):
%% shfr_success_builtin('length/2',_,p(X,Y),_,Call,Succ):-
%%      functor(X,'.',_),
%%      varset0(X,[Z|_]),
%%      Call = (Call_sh,Call_fr),
%%      take_coupled(Call_sh,[Z],Coupled),
%%      change_values_if_f(Coupled,Call_fr,Temp_fr,nf),
%%      update_lambda_sf([Y],Temp_fr,Call_sh,Succ_fr,Succ_sh),
%%      Succ = (Succ_sh,Succ_fr).
%% but this, however, does not solve the problem (bug#2)
shfr_success_builtin('length/2',Sv_uns,p(X,Y),HvFv_u,Call,Succ):-
    functor(X,'.',_),
    X = [_|Z],
    shfr_success_builtin('length/2',Sv_uns,p(Z,Y),HvFv_u,Call,Succ).
shfr_success_builtin('list/1',_,p(X),_,Call,Succ):-
    var(X),!,
    Call = (Call_sh,Call_fr),
    take_coupled(Call_sh,[X],Coupled),
    change_values_if_f(Coupled,Call_fr,Succ_fr,nf),
    Succ = (Call_sh,Succ_fr).
shfr_success_builtin('list/1',_,p(X),_,Call,Succ):-
    functor(X,'.',_), !,
    varset0(X,[Z|_]),
    Call = (Call_sh,Call_fr),
    take_coupled(Call_sh,[Z],Coupled),
    change_values_if_f(Coupled,Call_fr,Succ_fr,nf),
    Succ = (Call_sh,Succ_fr).
shfr_success_builtin('list/1',_,_,_,_Call,'$bottom').
shfr_success_builtin('free/1',[X],p(X),_,Call,Succ) :-
    var(X),
    Call = (Call_sh,Call_fr),
    var_value(Call_fr,X,Valuex),
    Valuex \== g,
    (Valuex == f ->
        Succ = Call % assumed that Call is already consistent and refined
    ;
        member_value_freeness(Call_fr,DefinitelyFreeVars,f),
        insert(DefinitelyFreeVars,X,AssumedFree),
        share_project(not_provided_Sg,AssumedFree,not_provided_HvFv_u,Call_sh,NewSh),
        sh_fv_compatible(NewSh,AssumedFree),
        change_values([X],Call_fr,Succ_fr,f),
        Succ = (Call_sh,Succ_fr)
        % TODO: refine Sh
    ).
shfr_success_builtin('free/1',_,_,_,_,'$bottom').

% the case of arg/3
any_arg_var(Y,Z,Head,TempASub,Succ):-
    Sg = p(Y,Z),
    varset(Sg,Sv),
    varset(Head,Hv),
    shfr_project(Sg,Sv,not_provided_HvFv_u,TempASub,Proj),
    shfr_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?

any_arg_all_args(0,_,_,_ASub,Succs):- !, Succs=[].
any_arg_all_args(N,Y,Z,ASub,[Succ|Succs]):-
    arg(N,Y,NY),
    any_arg_var(NY,Z,p(A,A),ASub,Succ),
    N1 is N-1,
    any_arg_all_args(N1,Y,Z,ASub,Succs).

%-------------------------------------------------------------------------
% shfr_call_to_success_builtin(+,+,+,+,+,-)                              %
% shfr_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)               %
% Handles those builtins for which computing Proj is easier than Succ    %
%-------------------------------------------------------------------------
:- export(shfr_call_to_success_builtin/6). 
shfr_call_to_success_builtin('==/2','=='(X,Y),_Sv,Call,Proj,Succ):-
    var(X),!,
    identical_one_var(X,Y,Call,Proj,Succ).
shfr_call_to_success_builtin('==/2','=='(X,Y),_Sv,Call,Proj,Succ):-
    var(Y),!,
    identical_one_var(Y,X,Call,Proj,Succ).
shfr_call_to_success_builtin('==/2','=='(X,Y),Sv,Call,_Proj,Succ):-
    Call = (Call_sh,Call_fr),
    free_peel(X,Y,Binds,[]),
    extract_ground(Sv,Call_fr,Gv),
    make_reduction(Binds,(Call_sh,Call_fr),Gv,Call_fr,Tfr,NewGv,Elim_u-[]),
    sort(Elim_u,Elim),
    ord_split_lists_from_list(NewGv,Call_sh,_Intersect,Temp_sh),
    ord_subtract(Temp_sh,Elim,Succ_sh),
    update_freeness(Tfr,Succ_sh,Succ_fr),
    non_free_to_ground(Call,(Succ_sh,Succ_fr),Succ).

shfr_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr),Succ):-
    varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
    Call = (Call_sh,Call_fr),
    ord_subtract(Sv,VarsX,VarsY),
    update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr),Succ):-
    varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
    Call = (Call_sh,Call_fr),
    ord_subtract(Sv,VarsY,VarsX),
    update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
shfr_call_to_success_builtin('=/2','='(X,Y),_Sv,Call,Proj,Succ):-
    var(X),var(Y), !,
    Proj = (_,Proj_fr),     
    obtain_prime_var_var(Proj_fr,Call,Succ).
shfr_call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
    var(X), !,
    Proj = (Proj_sh,Proj_fr),       
    ord_subtract(Sv,[X],VarsY),
    var_value(Proj_fr,X,ValueX),
    product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
    Prime= (Prime_sh,Prime_fr),
    shfr_extend(not_provided_Sg,Prime,Sv,Call,Succ).
shfr_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    shfr_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
shfr_call_to_success_builtin('=/2',_,_,_call,_,'$bottom').

shfr_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):- !,
    shfr_call_to_success_builtin('=/2','='(X,[Y|Z]),Sv,Call,Proj,Succ).
shfr_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):-
    shfr_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ).
shfr_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    var(X), !,
    Proj = (_Sh,Fr),
    var_value(Fr,X,Val),
    ( Val = f ->
      Succ = '$bottom'
    ; varset([X,Y],Sv),
      copy_term(Y,Yterm),
      varset(Yterm,Vars),
      shfr_call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),not_provided,Sv,Call,Proj,_Prime,Succ) % TODO: add some ClauseKey?
    ).
shfr_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    functor(X,'.',_), !,
    varset0(X,[Z|_]),
    Call = (Call_sh,Call_fr),
    change_values_if_f([Z],Call_fr,Temp_fr,nf),
    varset([X,Y],Sv),
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,
    varset(Xterm,Vars),
    Proj = (Sh,Fr),
    change_values_if_f([Z],Fr,TFr,nf),
    shfr_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_sh,Temp_fr),(Sh,TFr),_Prime,Succ). % TODO: add some ClauseKey?
shfr_call_to_success_builtin('sort/2',_,_,_,_,'$bottom').

%------------------------------------------------------------------------%
%            Intermediate Functions                                      |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% abs_unify_entry(+,+,+,+,-,-,-)                                         |
% abs_unify_entry(Fr,Sh,Binds,Hv,NewFr,NewSh,NewBinds)                   |
% It will traverse Binds updating Sh (grounding some variables due       |
% to the bindings in Binds), updating Fr and eliminating from Binds      |
% all primitive equations (X,Term,Tv) s.t. X or Term are ground          |
% The fixpoint will be reached when bot Sh and Fr  remain                |
% unchanged through one iteration                                        |
%------------------------------------------------------------------------%
abs_unify_entry(Fr,Sh,Binds,Hv,NewFr,NewSh,NewBinds):-
    aunify_entry(Binds,Fr,Sh,Hv,Fr1,Sh1,Binds1),
    fixpoint_aunify_entry(Fr,Binds,Fr1,Sh1,Binds1,Hv,NewFr,NewSh,NewBinds).

fixpoint_aunify_entry(Fr,Binds,Fr1,Sh1,Binds1,_,NewFr,NewSh,NewBinds):-
    Fr == Fr1, Binds == Binds1, !,
    NewFr = Fr1,
    NewSh = Sh1,
    NewBinds = Binds.
fixpoint_aunify_entry(_,_,Fr1,Sh1,Binds1,Hv,NewFr,NewSh,NewBinds):- 
    abs_unify_entry(Fr1,Sh1,Binds1,Hv,NewFr,NewSh,NewBinds).

%-------------------------------------------------------------------------
% aunify_entry(+,+,+,+,-,-,-)                                            %
% aunify_entry(Binds,Fr,Sh,Hv,NewFr,NewSh,NewBinds)                      %
% Foreach (X,Term,Tv) in Binds:                                          %
%   * If X/g in Fr, it will update Sh, grounding Tv                      %
%     and (X,Term,Tv) will not be in NewBinds                            %
%   * If X/g forall X in Tv, it will update Sh grounding X               %
%     and (X,Term,Tv) will not be in NewBinds                            %
%   * Otherwise (X,Term,Tv) will be in NewBinds, Sh will not             %
%     be updated and the freeness values in Fr will depend on the        %
%     freeness value of X and the characteristics of Term (if it is a    %
%     variable or a compund term)                                        %
%-------------------------------------------------------------------------
aunify_entry([],Fr,Sh,_,Fr,Sh,[]).
aunify_entry([(X,_,Tv)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):-
    var_value(Fr,X,Val),
    Val = g,!,
    decide_update_lambda(Tv,Fr,Sh,Hv,Fr1,L1),
    aunify_entry(Binds,Fr1,L1,Hv,NewFr,NewSh,NewBinds).
aunify_entry([(X,_,Tv)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):-
    values_equal(Tv,Fr,g), !, 
    decide_update_lambda([X],Fr,Sh,Hv,Fr1,L1),
    aunify_entry(Binds,Fr1,L1,Hv,NewFr,NewSh,NewBinds).
aunify_entry([(X,Term,Vars)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):- 
    var(Term),!,
    var_value(Fr,X,ValueX),
    var_value(Fr,Term,ValueTerm),
    table_from_y_entry(ValueX,ValueTerm,X,Term,Sh,Fr,Fr1),
    NewBinds = [(X,Term,Vars)|RestE],
    aunify_entry(Binds,Fr1,Sh,Hv,NewFr,NewSh,RestE).
aunify_entry([(X,Term,Tv)|Binds],Fr,Sh,Hv,NewFr,NewSh,NewBinds):- 
    var_value(Fr,X,ValueX),
    table_from_term_entry(ValueX,X,Term,Sh,Tv,Fr,Fr1),
    NewBinds = [(X,Term,Tv)|RestE],
    aunify_entry(Binds,Fr1,Sh,Hv,NewFr,NewSh,RestE).

%-------------------------------------------------------------------------
% table_from_y_entry(+,+,+,+,+,+,-)                                      %
% table_from_y_entry(ValueX,ValueY,X,Y,Sh,Fr,NewFr)                      %
% Updates the freeness values in Fr as follows:                          %
% If one variable is free (say X) then:                                  %
%    - if ValueY is f, nothing changes                                   %
%    - if ValueY is nf, the freeness value of all variables coupled      %
%      to X is changed to nf (unless they are already ground)            %
%    - if ValueY is nf(_,_), then: if forall variables coupled to X with %
%      freeness value X(_,Term), the Terms are identical, then the       %
%      freeness value of all free variables coupled to X is changed to   %
%      nf(_,Term). Otherwise, the freeness value of Y and all variables  %
%      coupled to X are changed to nf (unless they are already ground)   %
% If ValueX and ValueY are nf(_,Term1) and nf(_,Term2) and Term1==Term2  %
%  (i.e. they are bound to the same term), nothing changes               %
% Otherwise the freeness value of all variables coupled to both X and Y  %
% are changed to nf (unless they are already ground)                     %
%-------------------------------------------------------------------------
table_from_y_entry(f,ValueY,X,Y,Sh,Fr,NewFr):- !,
    table_from_y_entry_f(ValueY,X,Y,Sh,Fr,NewFr).
table_from_y_entry(ValueX,f,X,Y,Sh,Fr,NewFr):- !,
    table_from_y_entry_f(ValueX,Y,X,Sh,Fr,NewFr).
table_from_y_entry(nf(_,Term1),nf(_,Term2),_,_,_,Fr,Fr):-
    Term1 == Term2, !.
table_from_y_entry(_,_,X,Y,Lda_sh,Fr,NewFr):- 
    take_coupled(Lda_sh,[X,Y],Coupled),
    change_values_if_not_g(Coupled,Fr,NewFr,nf).

table_from_y_entry_f(f,_X,_Y,_Sh,Fr,Fr).
table_from_y_entry_f(nf,X,_Y,Sh,Fr,NewFr):-
    take_coupled(Sh,[X],Coupled),
    change_values_if_not_g(Coupled,Fr,NewFr,nf).
table_from_y_entry_f(nf(_,Term),X,Y,Sh,Fr,NewFr):-
    take_coupled(Sh,[X],Coupled),
    split_coupled(Coupled,Fr,FreeCoupled,Terms),
    ( all_terms_identical(Terms,Term) ->
        change_values_if_not_g(FreeCoupled,Fr,NewFr,nf(_,Term))
    ; sort([Y|Coupled],Vars),
      change_values_if_not_g(Vars,Fr,NewFr,nf)
    ).

%-------------------------------------------------------------------------
% table_from_term_entry(+,+,+,+,+,+,-)                                   %
% table_from_term_entry(ValueX,X,Term,Sh,Tv,Fr,NewFr)                    %
% SImilar to the one above, for the case in which Y is a compounf Term   %
%-------------------------------------------------------------------------
table_from_term_entry(f,X,Term,Sh,_,Fr,NewFr):- 
    take_coupled(Sh,[X],Coupled),
    split_coupled(Coupled,Fr,FreeCoupled,Terms),
    ( all_terms_identical(Terms,Term) ->
            change_values_if_not_g(FreeCoupled,Fr,NewFr,nf(_,Term))
    ; change_values_if_not_g(Coupled,Fr,NewFr,nf)
    ).
table_from_term_entry(nf,X,_,Sh,Tv,Fr,NewFr) :- 
    take_coupled(Sh,[X|Tv],Coupled),
    change_values_if_not_g(Coupled,Fr,NewFr,nf).
table_from_term_entry(nf(_,Term1),_,Term,_,_,Fr,Fr) :-
     Term1 == Term, !.
table_from_term_entry(nf(_,_),X,_,Sh,Tv,Fr,NewFr) :-
    take_coupled(Sh,[X|Tv],Coupled),
    change_values_if_not_g(Coupled,Fr,NewFr,nf).

%-------------------------------------------------------------------------
% take_coupled(+,+,-)                                                    |
% take_coupled(Sh,Vars,Coupled)                                          |
% Sh is a list of lists of variables, Vars is a list of variables        |
% Returns in Coupled the list of variables X s.t. exists at least        |
% one list in Sh containing X and at least one element in Vars.          |
%-------------------------------------------------------------------------
:- export(take_coupled/3).
take_coupled(Sh,Vars_u,Coupled):-
    sort(Vars_u,Vars),
    ord_split_lists_from_list(Vars,Sh,Intersect,_),
    merge_list_of_lists(Intersect,IntVars),
    merge(Vars,IntVars,Coupled).

%-------------------------------------------------------------------------
% split_coupled(+,+,-,-)                                                 |
% split_coupled(Vars,Fr,Fv,Terms)                                        |
% It receives as input a sorted list of variables Vars and a sorted lists|
% of freeness values (Var/FreenessValue). It computes:                   |
%   Fv   : list of vars X in Vars such that X/f appears in Fr            |
%   Terms: list of terms Term such that X/nf(_,Term) appears in Fr       |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(split_coupled/4).
split_coupled([],_,[],[]).
split_coupled([X|Xs],[Y/V|Ys],Fv,Terms):-
    compare(Order,X,Y),
    split_coupled(Order,X,Xs,Y/V,Ys,Fv,Terms).

split_coupled(>,X,Xs,_,[Y/V|Ys],Fv,Terms):-
    compare(Order,X,Y),
    split_coupled(Order,X,Xs,Y/V,Ys,Fv,Terms).
split_coupled(=,_X,Xs,Y/Val,Ys,Fv,Terms):-
    decide_coupled(Val,Y,Fv,RestFv,Terms,RestTerms),
    split_coupled(Xs,Ys,RestFv,RestTerms).

:- pop_prolog_flag(multi_arity_warnings).

decide_coupled(nf(_,Term),_Y,Fv,RestFv,Terms,RestTerms):-
    Fv = RestFv,
    Terms = [Term|RestTerms].
decide_coupled(f,Y,Fv,RestFv,Terms,RestTerms):-
    Fv = [Y|RestFv],
    Terms = RestTerms.
decide_coupled(g,_Y,Fv,RestFv,Terms,RestTerms):-
    Fv = RestFv,
    Terms = RestTerms.
decide_coupled(nf,_Y,Fv,RestFv,Terms,RestTerms):-
    Fv = RestFv,
    Terms = RestTerms.
decide_coupled(nv,_Y,Fv,RestFv,Terms,RestTerms):-
    Fv = RestFv,
    Terms = RestTerms.

%-------------------------------------------------------------------------
% decide_update_lambda(+,+,+,+,-,-)                                      %
% decide_update_lambda(Gv,Fr,Sh,Hv,NewFr,NewSh)                          %
% This predicates handles the case in which a set of variables (Gv) have %
% been determined as ground, and it has to:                              %
%   - Update the sharing component eliminating any set in which at least %
%     one of the now ground variables appears                            %
%   - Update the freeness component in order to:                         %
%         - all ground variables appear as ground                        %
%         - those free variables which are coupled (but not are become   %
%           ground) should become non free.                              %
% Since it is call from the unification, we have to know if the variables%
% are from the subgoal or from the head of the clause (recall that if    %
% they are from the head of the clause they do not appear in the sharing %
% component and therefore there is no coupled variable)                  %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

decide_update_lambda([],Fr,Sh,_,Fr,Sh).
decide_update_lambda([X|Xs],Fr,Sh,Hv,NewFr,NewSh):-
    ord_test_member(Hv,X,Flag),
    decide_update_lambda(Flag,X,Xs,Fr,Sh,NewFr,NewSh).

decide_update_lambda(yes,X,Xs,Fr,Sh,NewFr,Sh):-
    change_values([X|Xs],Fr,NewFr,g).
decide_update_lambda(no,X,Xs,Fr,Sh,NewFr,NewSh):- 
    ord_split_lists_from_list([X|Xs],Sh,Intersect,NewSh),
    merge_list_of_lists(Intersect,Coupled),
    merge_list_of_lists(NewSh,NotCoupled),
    ord_intersection_diff(Coupled, NotCoupled,NonFv,NewGv),
    change_values(NewGv,Fr,Temp_Fr,g),
    change_values_if_not_g(NonFv,Temp_Fr,NewFr,nf).

:- pop_prolog_flag(multi_arity_warnings).

:- export(all_terms_identical/2).
all_terms_identical([],_).
all_terms_identical([E|Es],Term) :-
    Term == E, 
    all_terms_identical(Es,Term).

%-------------------------------------------------------------------------
% update_lambda_sf(+,+,+,-,-)                                            |
% update_lambda_sf(Gv,Fr,Sh,NewFr,NewSh)                                 |
% Identical to decide_update_lambda but since it is not call from the    |
% abstract unification, no test on the Hv is needed                      |
%-------------------------------------------------------------------------
:- export(update_lambda_sf/5).
update_lambda_sf([],Fr,Sh,Fr,Sh):- !.
update_lambda_sf(Gv,Fr,Sh,Fr1,Sh1):-
    ord_split_lists_from_list(Gv,Sh,Intersect,Sh1),
    merge_list_of_lists(Intersect,Coupled),
    merge_list_of_lists(Sh1,NotCoupled),
    ord_intersection_diff(Coupled,NotCoupled,NonFv,NewGv),
    change_values(NewGv,Fr,Temp_Fr,g),
    change_values_if_f(NonFv,Temp_Fr,Fr1,nf).

%% update_lambda_g([],Fr,Sh,Fr,Sh):- !.
%% update_lambda_g(Gv,Fr,Sh,Fr1,Sh1):-
%%      ord_split_lists_from_list(Gv,Sh,Intersect,Sh1),
%%      merge_list_of_lists(Intersect,Coupled),
%%      merge_list_of_lists(Sh1,NotCoupled),
%%      ord_intersection_diff(Coupled,NotCoupled,_NonFv,NewGv),
%%      change_values(NewGv,Fr,Fr1,g).

%-------------------------------------------------------------------------
% update_lambda_non_free(+,+,+,-,-)                                      |
% update_lambda_non_free(Gv,Fr,Sh,NewFr,NewSh)                           |
% Identical to update_lambda_sf but:                                     |
% *  it tests that the variables that become ground are not free.        |
%    The reason is that Ground should be ground already, and therefore   |
%    they cannot make a definitely free variable to become ground        |
% *  it does not change the freeness value of any variable from f to nf  |
%    The same reason                                                     |
%-------------------------------------------------------------------------
:- export(update_lambda_non_free/5).
update_lambda_non_free([],Fr,Sh,Fr,Sh).
update_lambda_non_free([X|Xs],Fr,Sh,Fr1,Sh1):-
    ord_split_lists_from_list([X|Xs],Sh,Intersect,Sh1),
    merge_list_of_lists(Intersect,Coupled),
    merge_list_of_lists(Sh1,NotCoupled),
    ord_subtract(Coupled,NotCoupled,NewGv),
    change_values_if_differ(NewGv,Fr,Fr1,g,f).

%-------------------------------------------------------------------------
% partition_sf(+,+,+,-)                                                  %
% partition_sf(Binds,Fr,Sh,NewSh)                                        %
% If Binds is emtpy, then NewSh is                                       %
% { [X] | X/V in Freeness, V neq "g", X \notin vars(Sh)} union Sh        %
% (this is computed by partition_end_sf(Fr,Sh,NewSh))                    %
% Otherwise:                                                             %
%    * First computes TempSh =                                           %
%    {[X] | forall X/V in Fr, V \neq g and \not exists S in Sh, X in S}  %
%    * Then foreach (X,Term,Tv) in Binds, it computes the freeness value %
%       Value of X in Fr                                                 %
%    * If Value = nf(X,Term) then                                        %
%       -  eliminates from TempSh those elements SS such that either     %
%          X in SS or Tv \cap SS \neq emptyset                           %
%       -  adds P1 \cup P2 s.t. X \in P1 , Tv \cap P2 \neq emptyset      %
%    * If Value = nf then                                                %
%       -  eliminates from TempSh those elements SS such that either     %
%          X in SS or Tv \cap SS \neq emptyset                           %
%       -  adds \bigcup P s.t. X \in P or Tv \cap P \neq emptyset        %
%    * If Value = f then (note that then Term is a variable)             %
%       -  eliminates from TempSh those elements SS such that either     %
%          X in SS or Term \in SS                                        %
%       -  adds P1 \cup P2 s.t. X \in P1 Y \notin P1, Y \in P2 X \notin P2%
%-------------------------------------------------------------------------
:- export(partition_sf/4).
partition_sf(Binds,Fr,Sh,NewSh):-
    partition_end_sf(Fr,Sh,TempSh),
    sort(TempSh,TempSh_s),
    partition_sf1(Binds,Fr,TempSh_s,NewSh).

partition_end_sf([],Sh,Sh).
partition_end_sf([_/g|Xs],Sh,NewSh):- !,
    partition_end_sf(Xs,Sh,NewSh).
partition_end_sf([X/_|Xs],Sh,NewSh):- 
    ord_intersect_lists([X],Sh), !,
    partition_end_sf(Xs,Sh,NewSh).
partition_end_sf([X/_|Xs],Sh,[[X]|NewSh]):- 
    partition_end_sf(Xs,Sh,NewSh).

partition_sf1([],_Fr,Sh,Sh).
partition_sf1([(X,Term,Tv)|Binds],Fr,TempSh,NewSh):-
    var_value(Fr,X,ValueX),
    make_partition_from_x(ValueX,X,Term,Tv,TempSh,TempSh1),
    partition_sf1(Binds,Fr,TempSh1,NewSh).

%% first clause for shfrnv
make_partition_from_x(nv,X,_,Tv,TempSh,NewSh):- 
    insert(Tv,X,List),
    ord_split_lists_from_list(List,TempSh,L1,L2),
    merge_list_of_lists(L1,L3),
    merge(L2,[L3],NewSh).
make_partition_from_x(nf,X,_,Tv,TempSh,NewSh):- 
    insert(Tv,X,List),
    ord_split_lists_from_list(List,TempSh,L1,L2),
    merge_list_of_lists(L1,L3),
    merge(L2,[L3],NewSh).
make_partition_from_x(nf(_,_Term1),X,_Term,Tv,TempSh,NewSh):- 
%       Term1 == Term,            %%  Is this the default?? 
                              %% It is not when the occur check is needed!!
    ord_split_lists(TempSh,X,L1,L2),
    ord_split_lists_from_list(Tv,L2,L3,L4),
    merge_lists(L1,L3,L5),
    merge(L4,L5,NewSh).
make_partition_from_x(f,X,Y,_,TempSh,NewSh):- 
    ord_split_lists(TempSh,X,L1,L2),
    ord_split_lists(L2,Y,L3,L4),
    merge_lists(L1,L3,L5),
    merge(L4,L5,NewSh).

%-------------------------------------------------------------------------
% prune(+,+,+,+,-)                                                       %
% prune(Beta_sh,Head_args,ShareArgs,Temp1,Entry)                         %
% Eliminates any set in Beta_sh s.t. the induced sharing on the arguments%
% of Head_args is allowed by ShareArgs                                   %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(prune/5).
prune(Beta_sh,Head_args,Lambda_share,Temp1,Entry) :- 
    prune(Beta_sh,Head_args,Lambda_share,Temp2),
    merge(Temp1,Temp2,Entry).

:- export(prune/4).
prune([],_,_,[]).
prune([Xs|Xss],Head_args,ShareArgs,Entry) :- 
    pos(Head_args,1,Xs,ArgShare),
    ord_test_member(ShareArgs,ArgShare,Flag),
    add_if_member(Flag,Xs,Entry,Temp),
    prune(Xss,Head_args,ShareArgs,Temp).

:- pop_prolog_flag(multi_arity_warnings).

add_if_member(yes,Xs,[Xs|Temp1],Temp1).
add_if_member(no,_Xs,Temp1,Temp1).

%-------------------------------------------------------------------------
% abs_unify_exit(+,+,-,-)                                                %
% abs_unify_exit(Fr,Binds,NewFr,NewBinds)                                %
% Similar to abs_unify_entry. The difference is that Sh is not needed    %
% because the propagation of both groundness and nonfreeness induced by  %
% the subgoal is already present in the Exit. Thus there is no need to   %
% propagate them again.                                                  %
%-------------------------------------------------------------------------

abs_unify_exit(Fr,Binds,NewFr,NewBinds):-
    aunify_exit(Fr,Binds,Fr1,Binds1),
    fixpoint_aunify_exit(Fr,Binds,Fr1,Binds1,NewFr,NewBinds).

fixpoint_aunify_exit(Fr,Binds,Fr1,Binds1,NewFr,NewBinds):- 
    Fr == Fr1, Binds == Binds1, !,
    NewFr = Fr1,
    NewBinds = Binds.
fixpoint_aunify_exit(_Fr,_Binds,Fr1,Binds1,NewFr,NewBinds):- 
    abs_unify_exit(Fr1,Binds1,NewFr,NewBinds).

aunify_exit(Fr,[],Fr,[]):- !.
aunify_exit(Fr,[(X,_,Tv)|More],NewFr,NewBinds):-
    var_value(Fr,X,Val),
    Val = g,!,
    change_values(Tv,Fr,Fr1,g),
    aunify_exit(Fr1,More,NewFr,NewBinds).
aunify_exit(Fr,[(X,_,Tv)|More],NewFr,NewBinds):-
    values_equal(Tv,Fr,g), !, 
    change_values([X],Fr,Fr1,g),    
    aunify_exit(Fr1,More,NewFr,NewBinds).
aunify_exit(Fr,[(X,Y,Vars)|More],NewFr,NewBinds):- 
    var(Y), !,
    var_value(Fr,X,ValueX),
    var_value(Fr,Y,ValueY),
    table_from_y_exit(ValueX,ValueY,X,Y,Fr,Fr1),
    NewBinds = [(X,Y,Vars)|RestBinds],
    aunify_exit(Fr1,More,NewFr,RestBinds).
aunify_exit(Fr,[(X,Term,Tv)|More],NewFr,NewBinds):- !,
    NewBinds = [(X,Term,Tv)|RestBinds],
    var_value(Fr,X,ValueX),
    table_from_term_exit(ValueX,X,Term,Tv,Fr,Fr1),
    aunify_exit(Fr1,More,NewFr,RestBinds).

table_from_y_exit(Valuex,Valuey,_,_,Fr,Fr):- 
    Valuex == Valuey, !.
table_from_y_exit(f,ValueY,X,_,Fr,Fr1):-  !,
    change_values([X],Fr,Fr1,ValueY).
table_from_y_exit(Valuex,f,_,Y,Fr,Fr1):- !,
    change_values([Y],Fr,Fr1,Valuex).
table_from_y_exit(nf,_,_,Y,Fr,Fr1):- !,
    change_values([Y],Fr,Fr1,nf).
table_from_y_exit(_,nf,X,_,Fr,Fr1):- !,
    change_values([X],Fr,Fr1,nf).
table_from_y_exit(_,_,X,Y,Fr,Fr1):- !,
    sort([X,Y],Sorted),
    change_values(Sorted,Fr,Fr1,nf).

table_from_term_exit(f,X,Term,_,Fr,Fr1):- !,
    change_values_if_not_g([X],Fr,Fr1,nf(X,Term)).
table_from_term_exit(nf,_,_,Tv,Fr,Fr1) :- !,
    change_values_if_not_g(Tv,Fr,Fr1,nf).
table_from_term_exit(nf(_,Term1),_,Term,_,Fr,NewFr) :-
    Term1 == Term, !,
    NewFr = Fr.
table_from_term_exit(_,X,_,Tv,Fr,Fr1) :- !,
    insert(Tv,X,LVars),
    change_values_if_not_g(LVars,Fr,Fr1,nf).

%-------------------------------------------------------------------------
% covering(+,+,-)                                                        |
% covering(Disjoint,Sh,AlsoPossible),                                    |
% AlsoPossible={X in Disjoint| \exists S_1,..,S_n in Sh, union S_i = X}  |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(covering/3).
covering([],_Sh,[]).
covering([D|Disjoint],Sh,AlsoPossible):-
    covering(Sh,D,D,AlsoPossible,Tail),
    covering(Disjoint,Sh,Tail).

covering(_Sh,[],El,AlsoPossible,Tail):- !,
    AlsoPossible = [El|Tail].
covering([],_,_,Tail,Tail).
covering([L|Sh],D,El,AlsoPossible,Tail):-
    compare(S,L,D),
    covering(S,L,Sh,D,El,AlsoPossible,Tail).

covering(=,_L,_Sh,_D,El,[El|Tail],Tail).
covering(>,L,Sh,D,El,AlsoPossible,Tail):-
    ord_intersection_diff(D,L,_Intersect,Disjoint),
    covering(Sh,Disjoint,El,AlsoPossible,Tail).
covering(<,L,Sh,D,El,AlsoPossible,Tail):-
    ord_intersection_diff(D,L,_Intersect,Disjoint),
    covering(Sh,Disjoint,El,AlsoPossible,Tail).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
%  eliminate_non_element(+,+,+,-)
%  eliminate_non_element(Sv,Sh1,Sh2,NewSh)
%  NewSh is the result of eliminating from Sh1 (list of lists of
%  variables) those elements which projected over Sv do not appear
%  in Sh2. All ordered.
%-------------------------------------------------------------------------

:- export(eliminate_non_element/4).
eliminate_non_element([],_,_,[]) :- !.
eliminate_non_element(Sv,Sh1,Sh,Extended):-
    eliminate_non_element0(Sh1,Sv,Sh,Extended).

eliminate_non_element0([],_,_,[]).
eliminate_non_element0([L|Ls],[X|Xs],Sh,Extended):-
    L = [Y|Ys],
    compare(D,X,Y),
    has_give_intersection(D,X,Xs,Y,Ys,Flag,Inter,NewVars),
    eliminate_non_element1(Flag,Inter,NewVars,L,Ls,Sh,Extended).

eliminate_non_element1(end,_Inter,_NewVars,_L,_Ls,_Sh,[]).
eliminate_non_element1(no,_Inter,NewVars,_L,Ls,Sh,Extended):-
    eliminate_non_element0(Ls,NewVars,Sh,Extended).
eliminate_non_element1(yes,Inter,NewVars,L,Ls,Sh,Extended):-
    ord_test_member(Sh,Inter,Flag),
    eliminate_non_element3(Flag,L,Ls,NewVars,Sh,Extended).

eliminate_non_element3(yes,L,Ls,NewVars,Sh,[L|Extended]):-
    eliminate_non_element0(Ls,NewVars,Sh,Extended).
eliminate_non_element3(no,_L,Ls,NewVars,Sh,Extended):-
    eliminate_non_element0(Ls,NewVars,Sh,Extended).

%-------------------------------------------------------------------------

:- export(product/8).
product(f,X,VarsY,_,Sh,Lda_fr,Prime_sh,Prime_fr):-
    project_share(VarsY,Sh,Temp),
    insert_each(Temp,X,Temp1),
    sort_list_of_lists(Temp1,Prime_sh),
    take_coupled(Sh,[X],Coupled),
    change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
product(nf,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
    project_share(VarsY,Sh,Temp),
    closure_under_union(Temp,Temp1),
    merge_each([X],Temp1,Temp2),
    sort(Temp2,Prime_sh),
    take_coupled(Sh,Sv,Coupled),
    change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).

:- export(insert_each/3).       
insert_each([],_,[]).
insert_each([L|Ls],X,[[X|L]|Rest]):-
    insert_each(Ls,X,Rest).

%-------------------------------------------------------------------------

:- export(obtain_freeness/2).
obtain_freeness(f,f):- !, fail.
obtain_freeness(_,_).

%-------------------------------------------------------------------------
% identical_one_var(+,+,+,+,-)                                           |
% identical_one_var(X,Y,Call,Proj,Succ)                                  |
% It handles the builtin X == Y, knowing that X is a variable            |
%-------------------------------------------------------------------------

identical_one_var(X,Y,Call,_Proj,Succ):-
    ground(Y),!,
    Call = (Call_sh,Call_fr),
    ( update_lambda_non_free([X],Call_fr,Call_sh,Succ_fr,Succ_sh) ->
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ).
identical_one_var(X,Y,Call,Proj,Succ):-
    var(Y),!,
    Proj = (_Sh,Fr),
    var_value(Fr,X,ValueX),
    var_value(Fr,Y,ValueY),
    identical(ValueX,ValueY,X,Y,Call,Succ).
%%%%% COMMENT the cases in which Y is a complex term missing
identical_one_var(_X,_Y,_Call,_Proj,'$bottom').

%-------------------------------------------------------------------------
% identical(+,+,+,+,+,-)                                                 |
% identical(ValueX,ValueY,X,Y,Call,Succ)                                 |
% It handles the builtin X == Y, knowing that both X and Y are  variables|
%-------------------------------------------------------------------------
identical(g,g,_X,_Y,Proj,Proj):- !.
identical(g,f,_X,_Y,_Call,'$bottom'):- !.
identical(g,nf,_X,Y,Call,Succ):-
    Call = (Call_sh,Call_fr),
    ( update_lambda_non_free([Y],Call_fr,Call_sh,Succ_fr,Succ_sh) ->
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ).
identical(f,g,_X,_Y,_Call,'$bottom'):- !.
identical(nf,g,X,_Y,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    ( update_lambda_non_free([X],Call_fr,Call_sh,Succ_fr,Succ_sh) ->
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ).
identical(nf,nf,X,Y,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,NonPossibleY,PossibleNonXY),
    ord_split_lists(Intersect,Y,PossibleXY,NonPossibleX),
    varset(p(NonPossibleX,NonPossibleY),Coupled),
    varset(p(PossibleXY,PossibleNonXY),NonCoupled),
    ord_subtract(Coupled,NonCoupled,NewGround),
    ( values_differ(NewGround,Call_fr,f) ->
      merge(PossibleXY,PossibleNonXY,Succ_sh),
      Succ = (Succ_sh,Call_fr)
    ; Succ = '$bottom'
    ). 
identical(f,nf,X,Y,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,NonPossibleY,PossibleNonXY),
    ord_split_lists(Intersect,Y,PossibleXY,NonPossibleX),
    varset(p(NonPossibleX,NonPossibleY),Coupled),
    varset(p(PossibleXY,PossibleNonXY),NonCoupled),
    ord_subtract(Coupled,NonCoupled,NewGround),
    ( values_differ(NewGround,Call_fr,f) ->
      merge(PossibleXY,PossibleNonXY,Succ_sh),
      change_values([Y],Call_fr,Succ_fr,f), 
%%%% COMMENT This can introduce inconsistent sharing abstractions
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ). 
identical(nf,f,X,Y,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,NonPossibleY,PossibleNonXY),
    ord_split_lists(Intersect,Y,PossibleXY,NonPossibleX),
    varset(p(NonPossibleX,NonPossibleY),Coupled),
    varset(p(PossibleXY,PossibleNonXY),NonCoupled),
    ord_subtract(Coupled,NonCoupled,NewGround),
    ( values_differ(NewGround,Call_fr,f) ->
      merge(PossibleXY,PossibleNonXY,Succ_sh),
      change_values([X],Call_fr,Succ_fr,f), 
%%%% COMMENT This can introduce impossible sharing abstractions
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ). 
identical(f,f,X,Y,Call,Succ):- !,
    Call = (Call_sh,Call_fr),
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,NonPossibleY,PossibleNonXY),
    ord_split_lists(Intersect,Y,PossibleXY,NonPossibleX),
    varset(p(NonPossibleX,NonPossibleY),Coupled),
    varset(p(PossibleXY,PossibleNonXY),NonCoupled),
    ord_subtract(Coupled,NonCoupled,NewGround),
    ( values_differ(NewGround,Call_fr,f) ->
      merge(PossibleXY,PossibleNonXY,Succ_sh),
%%%% COMMENT This can introduce inconsistent sharing abstractions
      Succ = (Succ_sh,Call_fr)
    ; Succ = '$bottom'
 ).

%-------------------------------------------------------------------------
% obtain_prime_var_var(+,+,-)                                            |
% obtain_prime_var_var([X/V,Y/V],Call,Success)                           |
% handles the case X = Y where both X,Y are variables which freeness     |
% value \== g                                                            |
%-------------------------------------------------------------------------
:- export(obtain_prime_var_var/3).
obtain_prime_var_var([X/f,Y/f],(Call_sh,Call_fr),Succ):- !,
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,OnlyY,NonXY),
    ord_split_lists(Intersect,Y,XY,OnlyX),
    merge_lists(OnlyY,OnlyX,BothXY),
    merge(XY,NonXY,Succ1),
    merge(BothXY,Succ1,Succ_sh),
    Succ = (Succ_sh,Call_fr).
obtain_prime_var_var([X/_,Y/_],Call,Succ):-
    Prime = ([[X,Y]],[X/nf,Y/nf]),
    shfr_extend(not_provided_Sg,Prime,[X,Y],Call,Succ).


%-------------------------------------------------------------------------
% sh_fv_compatible(+,+)                                                  |
% sh_fv_compatible(Sh, Fv)                                                |
% Satisfied if a list of free variables Fv and a potential sharing       |
% set Sh over those variables are compatible. This happens if and        |
% only if there is a subset of Sh that is a disjunt partition of Fv      |
%-------------------------------------------------------------------------
:- export(sh_fv_compatible/2).
sh_fv_compatible(Sh, Fv) :-
    there_is_partition(Sh,Fv).
% TODO: refine Sh by excluding the sets that do not occur in any of
% the possible paritions?

there_is_partition([Ws|Sh],Vs) :-
    ord_subset_diff(Ws,Vs,NewVs),
    (NewVs=[] ; there_is_partition(Sh,NewVs)),
    !.
there_is_partition([_|Sh],Vs) :-
    there_is_partition(Sh,Vs).


non_free_to_ground((_,Lcall_fr),(Lsucc_sh,Lsucc_fr),(Lsucc_sh,Lsucc_fr)):-
    compare_free_to_ground(Lcall_fr,Lsucc_fr), !.
non_free_to_ground(_,_,'$bottom').

compare_free_to_ground([],[]).
compare_free_to_ground([X/Xf|Xs],[X/Yf|Ys]):-
    Xf = f, !,
    Yf \== g,
    compare_free_to_ground(Xs,Ys).
compare_free_to_ground([_|Xs],[_|Ys]):- !,
    compare_free_to_ground(Xs,Ys).

%------------------------------------------------------------------------
% update_from_values(+,+,+,+,+,-)                                       |
% update_from_values(ValueX,ValueY,X,Y,Call,Succ)                       |
% It returns the adecuate values of Success for length(X,Y) when both X |
% and Y are variables. It is based on the freeness values of X and Y.   |
%------------------------------------------------------------------------
update_from_values(g,g,_,_,Proj,Proj):- !.
update_from_values(g,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
    update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).
update_from_values(f,g,X,_Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- !,
    take_coupled(Call_sh,[X],Coupled),
    change_values_if_f(Coupled,Call_fr,Succ_fr,nf),
    Succ_sh = Call_sh.
update_from_values(f,f,_X,_Y,_Proj,'$bottom'):- !.
update_from_values(f,nf,X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
    update_lambda_non_free([Y],Call_fr,Call_sh,Tmp_fr,Succ_sh),!,
    take_coupled(Call_sh,[X],Coupled),
    change_values_if_f(Coupled,Tmp_fr,Succ_fr,nf).
update_from_values(f,nf,_X,_Y,_Proj,'$bottom').
update_from_values(nf,g,_X,_Y,Proj,Proj):- !.
update_from_values(nf,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
    update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).

%-------------------------------------------------------------------------
% make_dependence(+,+,+,-,-)                                             |
% make_dependence(Sh,Vars,Fr,NewFr,NewSh),                               |
% It gives the new sharing and freeness component for the variables in Y |
% (Vars) when recorded(X,Y,Z) was called, once the variables in Z have   |
%  been made ground                                                      |
%-------------------------------------------------------------------------
:- export(make_dependence/5).
make_dependence([],Y,TempPrime_fr,Prime_fr,[]):- 
    change_values(Y,TempPrime_fr,Prime_fr,g).
make_dependence([S|Ss],Y,TempPrime_fr,Prime_fr,Prime_sh):- 
    closure_under_union([S|Ss],Prime_sh),
    change_values_if_f(Y,TempPrime_fr,Prime_fr,nf).

%-------------------------------------------------------------------------
% extract_ground(+,+,-)                                                  |
% extract_ground(Vars,Fr,Gv)                                             |   
% It obtains in Gv the variables in Vars which are ground w.r.t. Fr      |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

extract_ground([],_,[]).
extract_ground([X|Xs],[Y/V|Ys],Gv):-
    compare(D,X,Y),
    extract_ground(D,V,X,Xs,Y,Ys,Gv).

extract_ground(=,g,X,Xs,_Y,Ys,Gv):- !,
    Gv= [X|Rest],
    extract_ground(Xs,Ys,Rest).
extract_ground(=,_,_X,Xs,_Y,Ys,Gv):- 
    extract_ground(Xs,Ys,Gv).
extract_ground(>,_,X,Xs,_,[Y/V|Ys],Gv):-
    compare(D,X,Y),
    extract_ground(D,V,X,Xs,Y,Ys,Gv).

:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------
% It gives the adecuate freeness value for each binding (X,Term) 
% resulting of the unification of A and B when ==(A,B) was called.
% If neither X nor Term in one binding is ground, since they have to 
% be identicals (==), each set S of the sharing component have to 
% satisfied that X is an element of S if and only if at least one 
% variable in Term appears also in S. Therefore, each set in which 
% either only X or only variables of Term appear, has to be eliminated.
%------------------------------------------------------------------------
make_reduction([],_,_,Fr,Fr,[],Y-Y).
make_reduction([(X,_,Tv)|More],(L_sh,L_fr),Ground,Temp_fr,Fr,NewG,Elim):-
    ord_member(X,Ground), !,
    values_differ(Tv,L_fr,f),
    make_reduction(More,(L_sh,L_fr),Ground,Temp_fr,Fr,NewG1,Elim),
    append(Tv,NewG1,NewG).
make_reduction([(X,_,Tv)|More],(L_sh,L_fr),Ground,Temp_fr,Fr,[X|NewG],Elim):-
    ord_subset(Tv,Ground), !,
    values_differ([X],L_fr,f),
    make_reduction(More,(L_sh,L_fr),Ground,Temp_fr,Fr,NewG,Elim).
make_reduction([(X,Y,_)|More],(L_sh,L_fr),Ground,Temp_fr,Fr,NewG,Elim):-
    var(Y), !,
    var_value(L_fr,X,ValueX),
    var_value(L_fr,Y,ValueY),
    make_identicals(X,ValueX,Y,ValueY,Temp_fr,Temp1_fr),
    sort([X,Y],Vars),
    eliminate_if_not_possible(L_sh,Vars,Elim1),
    make_reduction(More,(L_sh,L_fr),Ground,Temp1_fr,Fr,NewG,Elim2),
    append_dl(Elim1,Elim2,Elim).
make_reduction([(X,_,Tv)|More],(L_sh,L_fr),Ground,Temp_fr,Fr,NewG,Elim):-
    var_value(L_fr,X,Val),
    Val = nf,
    ord_subtract(Tv,Ground,List),
    eliminate_if_not_possible(L_sh,X,List,Elim1),
    make_reduction(More,(L_sh,L_fr),Ground,Temp_fr,Fr,NewG,Elim2),
    append_dl(Elim1,Elim2,Elim).

%------------------------------------------------------------------------
% It gives the adecuate freeness value for each binding (X,Term) 
% resulting of the unification of A and B when ==(A,B) was called, 
% if Term was a variable
%------------------------------------------------------------------------
make_identicals(_,Value,_,Value,L_fr,L_fr):- !.
make_identicals(_,f,Y,nf,L_fr,Temp_fr):- !,
    change_values([Y],L_fr,Temp_fr,f).
make_identicals(X,nf,_,f,L_fr,Temp_fr):- !,
    change_values([X],L_fr,Temp_fr,f).

% It updates the freeness component with the new ground variables
% (Note that the freeness value of X in the first component cannot be f)

update_freeness([],_,[]).
update_freeness([X/g|Xs],Temp_sh,[X/g|Temp_fr]):- !,
    update_freeness(Xs,Temp_sh,Temp_fr).
update_freeness([X/Val|Xs],Temp_sh,[X/Val|Temp_fr]):- 
    ord_intersect_lists([X],[Temp_sh]), !,
    update_freeness(Xs,Temp_sh,Temp_fr).
update_freeness([X/Val|Xs],Temp_sh,[X/g|Temp_fr]):- 
    Val \== f,
    update_freeness(Xs,Temp_sh,Temp_fr).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%           ABSTRACT meta_call
%-------------------------------------------------------------------------
:- export(shfr_unknown_call/4).
shfr_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
shfr_unknown_call(_Sg,Vars,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):-
    ord_split_lists_from_list(Vars,Call_sh,Intersect,Rest),
    closure_under_union(Intersect,Star),
    merge(Star,Rest,Succ_sh),
    merge_list_of_lists(Intersect,Nonfree_vars),
    change_values_if_f(Nonfree_vars,Call_fr,Succ_fr,nf).

%%%%%%%%%% ANNOTATION PROCESS
%%
%% %-------------------------------------------------------------------------
%% % update_lambda_non_free_iterative(+,+,+,-,-,-)
%% % update_lambda_non_free_iterative(Ground,Freeness,Sh,NewFreeness,NewSh)
%% % Identical to update_lambda_non_free but:
%% %-------------------------------------------------------------------------
%% 
%% update_lambda_non_free_iterative([],V,L,V,L,[]).
%% update_lambda_non_free_iterative([X|Xs],V,L,V1,L1,NewGi):-
%%      member_value_freeness(V,AlreadyGround,g),
%%      ord_subtract([X|Xs],AlreadyGround,MakeGround),
%%      take_ground_dep(MakeGround,MakeGround,V,L,TestVars,[],NewGround),
%%      ord_split_lists_from_list(TestVars,L,_Intersect,Disjoint),
%%      ord_subtract(MakeGround,NewGround,RestGround),
%%      loop_ground(RestGround,Disjoint,L1,Vars),
%%      merge(TestVars,Vars,NewGi),
%%      change_values(MakeGround,V,V1,g).
%% 
%% loop_ground([],L1,L1,[]).
%% loop_ground([X|RestGround],L,L1,[X|Vars]):-
%%      ord_split_lists(L,X,_Intersect,Disjoint),
%%      merge_list_of_lists(Disjoint,NonGround),
%%      ord_intersection(RestGround,NonGround,RestVars),
%%      loop_ground(RestVars,Disjoint,L1,Vars).
%% 
%% 
%% take_ground_dep([],_,_V,_L,[],G,G).
%% take_ground_dep([X|Xs],Vars,V,L,TestVars,TempG,NewG):-
%%      check_nonvar(X,L,V,Intersect,StronglyCoupled),!,
%%      check_nobody_makes_ground(Vars,X,Intersect,Projected),
%%      (Projected = [[]|_] ->     % nobody in Vars makes X ground
%%       TestVars = [X|RestVars],
%%       ord_intersection(Vars,StronglyCoupled,AlreadyGround),
%%       merge(AlreadyGround,TempG,NewTempG)
%%      ; TestVars = RestVars,
%%        NewTempG = TempG
%%      ),
%%      take_ground_dep(Xs,Vars,V,L,RestVars,NewTempG,NewG).
%% 
%% check_nonvar(X,L,V,Intersect,StronglyCoupled):-
%%      ord_split_lists(L,X,Intersect,Disjoint),        
%%      merge_list_of_lists(Intersect,Coupled),       
%%      merge_list_of_lists(Disjoint,Not_Coupled),
%%      ord_subtract(Coupled,Not_Coupled,StronglyCoupled),
%%      values_differ(StronglyCoupled,V,f).   %% checking nonground
%% 
%% 
%% check_nobody_makes_ground(Vars,X,Intersect,Proj):-
%%      ord_subtract(Vars,[X],Rest),
%%      project_share(Rest,Intersect,Proj).

%-------------------------------------------------------------------------
%   Manipulating Freeness components
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% var_value_rest(+,+,+,-,-)                                              |
% var_value_rest(Fr,X,Value,NewFr,Flag)                                  |
% If the freeness value of X in Fr is Value, then Flag = yes.            |
% Otherwise it is set to no.                                             |
% NewFr is the result of eliminating all Y/V s.t. Y less equal X.        |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

var_value_rest([],_X,_Value,no,[]).
var_value_rest([Y/V|More],X,Value,Rest,Flag):-
    compare(D,X,Y),
    var_value_rest(D,V,More,X,Value,Rest,Flag).

var_value_rest(=,V,More,_X,Value,Rest,Flag):-
    V = Value,!,
    Flag = yes,
    Rest = More.
var_value_rest(=,_V,More,_X,_Value,Rest,Flag):-
    Flag = no,
    Rest = More.
var_value_rest(>,_Elem,More,X,Value,Rest,Flag):-
    var_value_rest(More,X,Value,Rest,Flag).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% values_equal(+,+,+)                                                    |
% values_equal(Vars,Fr,Value)                                            |
% Satisfied if the freeness values of all variables in Vars is equal to  |
% Value.                                                                 |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(values_equal/3).
values_equal([],_,_).
values_equal([X|Xs],[Y/V|Ys],Value):-
    compare(D,X,Y),
    values_equal(D,X,Xs,V,Ys,Value).

values_equal(=,_X,Xs,Value,Ys,Value):-
    values_equal(Xs,Ys,Value).
values_equal(>,X,Xs,_,[Y/V|Ys],Value):-
    compare(D,X,Y),
    values_equal(D,X,Xs,V,Ys,Value).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% values_differ(+,+,+)                                                   |
% values_differ(Vars,Fr,Value)                                           |
% Satisfied if the freeness values of each variable in Vars is different |
% from Value                                                             |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(values_differ/3).
values_differ([],_,_).
values_differ([X|Xs],[Y/V|Ys],Value):-
    compare(D,X,Y),
    values_differ(D,X,Xs,V,Ys,Value).

values_differ(=,_X,Xs,V,Ys,Value):-
    V \== Value, 
    values_differ(Xs,Ys,Value).
values_differ(>,X,Xs,_,[Y/V|Ys],Value):-
    compare(D,X,Y),
    values_differ(D,X,Xs,V,Ys,Value).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% change_values(+,+,-,+)                                                 %
% change_values(Vars,Fr,NewFr,Value)                                     %
% Forall X in Vars, there must exist an X/V in Fr. If so, it             %
% changes V to Value. Otherwise it fails                                 %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(change_values/4).
change_values([],Ys,Ys,_).
change_values([X|Xs],[Y/V|Ys],Z,Value):-
    compare(D,X,Y),
    change_values(D,X,Y/V,Xs,Ys,Z,Value).

change_values(=,X,_,Xs,Ys,[X/Value|Z],Value):-
    change_values(Xs,Ys,Z,Value).
change_values(>,X,Y/Val,Xs,[Y1/V|Ys],[Y/Val|Z],Value):-
    compare(D,X,Y1),
    change_values(D,X,Y1/V,Xs,Ys,Z,Value).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% change_values_if_not_g(+,+,-,+)                                        %
% change_values_if_not_g(Vars,Fr,NewFr,Value)                            %
% Forall X in Vars, there must exist an X/V in Fr. If so:                %
%    * if V is g, X/V remains unchanged                                  %
%    * else, X/V is replaced by X/Value is added                         %
% Otherwise (X/V not in Fr) it fails                                     %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(change_values_if_not_g/4).
change_values_if_not_g([],Xs,Xs,_).
change_values_if_not_g([Y|Ys],[X/V|Xs],Z,Value):- 
    compare(D,Y,X),
    change_values_if_not_g(D,Y,Ys,X/V,Xs,Z,Value).

change_values_if_not_g(=,Y,Ys,_X/V,Xs,Z,Value):-
    change_if_not_g(V,Value,V1),
    Z = [Y/V1|Zs],
    change_values_if_not_g(Ys,Xs,Zs,Value).
change_values_if_not_g(>,Y,Ys,Elem,[X/V|Xs],Z,Value):- 
    Z = [Elem|Zs],
    compare(D,Y,X),
    change_values_if_not_g(D,Y,Ys,X/V,Xs,Zs,Value).

change_if_not_g(g,_,g).
change_if_not_g(f,V,V).
change_if_not_g(nv,V,V).
change_if_not_g(nf,V,V).
change_if_not_g(nf(_,_),V,V).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% change_values_if_f(+,+,-,+)                                            %
% change_values_if_f(Vars,Fr,NewFr,Value)                                %
% Forall X in Vars, there must exist an X/V in Fr. If so:                %
%    * if V is f or nf(_,_), X/V is replaced by X/Value                  %
%    * else, X/V remains unchanged                                       %
% Otherwise (X/V not in Fr) it fails                                     %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(change_values_if_f/4).
change_values_if_f([],Xs,Xs,_).
change_values_if_f([Y|Ys],[X/V|Xs],Z,Value):- 
    compare(D,Y,X),
    change_values_if_f(D,Y,Ys,X/V,Xs,Z,Value).

change_values_if_f(=,Y,Ys,_X/V,Xs,[Y/V1|Zs],Value):-
    ( (V = f; V = nf(_,_)) ->
        V1 = Value
    ;   V1 = V
    ),
    change_values_if_f(Ys,Xs,Zs,Value).
change_values_if_f(>,Y,Ys,Elem,[X/V|Xs],[Elem|Zs],Value):- 
    compare(D,Y,X),
    change_values_if_f(D,Y,Ys,X/V,Xs,Zs,Value).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% member_value_freeness_differ(+,-,+)                                    |
% member_value_freeness_differ(Fr,Vars,Value)                            |
% It returns in Vars the list of variables with freeness value different |
% from Value                                                             |
%-------------------------------------------------------------------------

:- export(member_value_freeness_differ/3).
member_value_freeness_differ([],[],_).
member_value_freeness_differ([X/Valuex|Rest],ListValue,Value):- 
    Valuex \== Value,!,
    ListValue = [X|More],
    member_value_freeness_differ(Rest,More,Value).
member_value_freeness_differ([_|Rest],ListValue,Value):- 
    member_value_freeness_differ(Rest,ListValue,Value).

%-------------------------------------------------------------------------
% collapse_non_freeness(+,-)                                             |
% collapse_non_freeness(Fr,NewFr)                                        |
% Transform any X/nf(_,_) in Freeness into X/nf.                         |
%-------------------------------------------------------------------------
 
collapse_non_freeness([],[]).
collapse_non_freeness([X/nf(_,_)|Xs],Changed):- !,
    Changed = [X/nf|Ys],
    collapse_non_freeness(Xs,Ys).
collapse_non_freeness([X|Xs],[X|Ys]):-
    collapse_non_freeness(Xs,Ys).

%-------------------------------------------------------------------------
% project_freeness_n(+,+,-)                                              |
% project_freeness_n(Fr1,Fr2,Eliminated)                                 |
% Eliminates from Fr2 any X/Value s.t. X is not in Fr1. Also if the value|
% in Fr1 is f and the value in Fr2 is nf, the value in Eliminated will be|
%  f. Otherwise, it will be the value in Fr2                             |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(project_freeness_n/3).
project_freeness_n([],_,[]).
project_freeness_n([X/V1|Xs],[Y/V2|Ys],Eliminated):-
    compare(D,X,Y),
    project_freeness_n(D,X,V1,Xs,Y,V2,Ys,Eliminated).

project_freeness_n(=,_X,f,Xs,Y,nf,Ys,Eliminated):- !,
    Eliminated = [Y/f|Rest],
    project_freeness_n(Xs,Ys,Rest).
project_freeness_n(=,_X,_V1,Xs,Y,V2,Ys,[Y/V2|Eliminated]):-
    project_freeness_n(Xs,Ys,Eliminated).
project_freeness_n(>,X,V1,Xs,_,_,[Y/V2|Ys],Eliminated):-
    compare(D,X,Y),
    project_freeness_n(D,X,V1,Xs,Y,V2,Ys,Eliminated).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% non_free_vars(+,+,+,-,-)                                               %
% non_free_vars(Vars,Fr1,Fr2,Fv,NewFr).                                  %
% NewFr is the result of adding to Fr2 all X/nf s.t. X in Vars and X/nf  %
% in Fr1 (Note that if X in Vars, then X/_ not in Fr2).                  %
% Fv contains the rest of variables in Vars. All Ordered                 %
% The reason is the following: Vars is the set of variables in success   %
% and not in prime. Thus, those variables in Vars with value in Call     %
% different from nf are free, and should be added to BVarsf.             %
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

non_free_vars([],_,Fr2,[],Fr2).
non_free_vars([X|Xs],Fr1,Fr2,BVarsf,NewFr):-
    non_free_vars(Fr2,X,Xs,Fr1,BVarsf,NewFr).

non_free_vars([],X,Xs,[Y/V|Fr1],BVarsf,NewFr):-
    compare(D,X,Y),
    non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
non_free_vars([Y/V|Fr2],X,Xs,Fr1,BVarsf,NewFr):-
    compare(D,X,Y),
    non_free_vars(D,X,Xs,Fr1,Y/V,Fr2,BVarsf,NewFr).

non_free_vars(>,X,Xs,Fr1,Elem,Fr2,BVarsf,[Elem|NewFr]):-
    non_free_vars(Fr2,X,Xs,Fr1,BVarsf,NewFr).
non_free_vars(<,X,Xs,Fr1,Elem,Fr2,BVarsf,NewFr):-
    var_value_rest(Fr1,X,nf,New_Fr1,Flag),
    non_free_vars(Flag,X,Xs,New_Fr1,[Elem|Fr2],BVarsf,NewFr).

non_free_vars1(>,X,Xs,_,[Y/V|Fr1],BVarsf,NewFr):-
    compare(D,X,Y),
    non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
non_free_vars1(=,X,Xs,V,Fr1,BVarsf,NewFr):-
    V = nf,!,
    NewFr = [X/nf|Rest_temp2],
    non_free_vars2(Xs,Fr1,BVarsf,Rest_temp2).
non_free_vars1(=,X,Xs,_V,Fr1,[X|BVarsf],NewFr):-
    non_free_vars2(Xs,Fr1,BVarsf,NewFr).

non_free_vars2([],_Fr1,[],[]).
non_free_vars2([X|Xs],[Y/V|Fr1],BVarsf,NewFr):-
    compare(D,X,Y),
    non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).

non_free_vars(yes,X,Xs,Fr1,Fr2,BVarsf,[X/nf|NewFr]):-
    non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).
non_free_vars(no,X,Xs,Fr1,Fr2,[X|BVarsf],NewFr):-
    non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% propagate_non_freeness(+,+,+,+,-)                                      |
% propagate_non_freeness(Vars,NonFv,Sh,Fr,NewFr)                         |
% NewFr is the result of inserting each variable in Vars with value nf,  |
% if it appears in Sh with a nonfree variable. Otherwise it inserts X/f. |
%-------------------------------------------------------------------------
:- export(propagate_non_freeness/5).
propagate_non_freeness([],_,_,Fr,Fr).
propagate_non_freeness([X|Xs],NonFv,Sh,[Y/Value|Fr],NewFr):-
    X @> Y, !,
    NewFr = [Y/Value|RestNewFr],
    propagate_non_freeness([X|Xs],NonFv,Sh,Fr,RestNewFr).
propagate_non_freeness([X|Xs],NonFv,Sh,Fr,NewFr):-
    ord_split_lists(Sh,X,Sh_Subs,_),
    ord_intersect_lists(NonFv,Sh_Subs), !,
    NewFr = [X/nf|RestNewFr],
    propagate_non_freeness(Xs,NonFv,Sh,Fr,RestNewFr).
propagate_non_freeness([X|Xs],NonFv,Sh,Fr,[X/f|NewFr]):- 
    propagate_non_freeness(Xs,NonFv,Sh,Fr,NewFr).

%-------------------------------------------------------------------------
% add_environment_vars(+,+,-)                                            |
% add_environment_vars(Fr1,Fr2, NewFr).                                  |
% Fr2 contains all variables in Fr1 and possibly new ones (Fr1           |
% corresponds to a prime while Fr2 corresponds to a call)                |
% Then, NewFr = Fr1 + {X/V in Fr2| X/_ \notin Fr1}                       |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

:- export(add_environment_vars/3).
add_environment_vars([],Fr2,Fr2).
add_environment_vars([Y/Vy|Fr1],[X/V|Fr2],NewFr):- 
    compare(D,X,Y),
    add_environment_vars(D,Y/Vy,Fr1,X/V,Fr2,NewFr).

add_environment_vars(=,Elem,Fr1,_,Fr2,[Elem|NewFr]):-
    add_environment_vars(Fr1,Fr2,NewFr).
add_environment_vars(<,Y/Vy,Fr1,El,[X/V|Fr2],[El|NewFr]):-
    compare(D,X,Y),
    add_environment_vars(D,Y/Vy,Fr1,X/V,Fr2,NewFr).

:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
%                        DELAY PREDICATES
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% Assumptions: programs are normalized.
%------------------------------------------------------------------------%

%:- export(shfr_check_cond/5).
%-------------------------------------------------------------------------
% shfr_check_cond(+,+,-)
% shfr_check_cond(Conds,ACns,Flag)
%-------------------------------------------------------------------------
% Conds is a list of elements of the form (Gr,Nv), where Gr and Nv are 
% ordered sets of variables. Conds represents the conditions under which 
% a subgoal will be woken or delayed.
%   * If forall (Gr,Nv), at least one variable in Gr or Nv is non-ground 
%     or variable, respectively, w.r.t. ACons, Flag = d (the goal is 
%     definitely delayed)
%   * If for at least one (Gr,Nv), all variables in Gr and Nv are ground 
%     and non-var, respectively, w.r.t ACons, Flag = w (the goal is 
%     definitely woken)
%   * Otherwise, Flag is the set of abstractions under which the goal will
%     be woken.
% In doing this we will first compute Free, Ground, and NonGround (set of
% variables in ACns which are definitely free, ground, and non-ground, 
% respectively). Then we will examine each element.
%-------------------------------------------------------------------------

%% :- push_prolog_flag(multi_arity_warnings,off).
%% 
%% shfr_check_cond(Conds,(Sh,Fr),Sv,Flag,WConds):-
%%      shfr_check_cond(Conds,(Sh,Fr),Sv,[],Flag,[],WConds).
%% 
%% shfr_check_cond([],_,_,Acc,Flag,WAcc,WConds):-
%%      ( Acc = [] ->
%%          Flag = d
%%      ; Flag = Acc,
%%        WConds = WAcc).
%% shfr_check_cond([(Gr,Nv,Eq)|Rest],ASub,Sv,Acc,Flag,WAcc,WConds):-
%%      ( shfr_make_awoken(ASub,Gr,Nv,Eq,Sv,Flag2) -> 
%%          ( Flag2 = w ->
%%              Flag = w,
%%              WConds = [(Gr,Nv,Eq)]
%%          ;   shfr_check_cond(Rest,ASub,Sv,[Flag2|Acc],Flag,[(Gr,Nv,Eq)|WAcc],WConds))
%%      ; shfr_check_cond(Rest,ASub,Sv,Acc,Flag,WAcc,WConds)).
%% 
%% :- pop_prolog_flag(multi_arity_warnings).
%% 
%% shfr_make_awoken((Sh,Fr),Gr,Nv,Eq,Sv,Flag):-
%%      member_value_freeness(Fr,OldGr,g),
%%      ord_subtract(Gr,OldGr,NewGr),
%%      ( NewGr = [] ->
%%          NewFr = Fr,
%%          NewSh = Sh,
%%          AllGr = OldGr
%%      ; Flag0 = diff,
%%        update_lambda_non_free(NewGr,Fr,Sh,NewFr,NewSh),
%%        member_value_freeness(NewFr,AllGr,g)),
%%      ord_subtract(Nv,AllGr,NewNv),
%%      member_value_freeness(NewFr,Free,f),
%%      ord_intersection(Free,NewNv,[]),
%%      ( mynonvar(NewNv,NewSh,Free) ->
%%             true
%%      ; Flag0 = diff),
%%      ( var(Flag0) ->
%%          shfr_check_eq(Eq,AllGr,Free,NewFr,NewSh,Sv,Flag)
%%      ; shfr_project(not_provided_Sg,Sv,not_provided_HvFv_u,(NewSh,NewFr),Flag)).
%%        
%% shfr_check_eq(Eq,AllGr,_,_,NewSh,_,Flag):-
%%      shfr_satisf_eq(Eq,AllGr,NewSh),!,
%%      Flag = w.
%% shfr_check_eq(Eq,_,Free,_,NewSh,_,_):-
%%      shfr_fail_eq(Eq,Free,NewSh),!,
%%      fail.
%% shfr_check_eq(_,_,_,NewFr,NewSh,Sv,Flag):-
%%      shfr_project(not_provided_Sg,Sv,not_provided_HvFv_u,(NewSh,NewFr),Flag).
%% 
%% :- push_prolog_flag(multi_arity_warnings,off).
%% 
%% shfr_satisf_eq([],_,_).
%% shfr_satisf_eq([eq(X,Y)|Rest],Gr,Sh):-
%%      shfr_satisf_eq(X,Y,Gr,Sh),!,
%%      shfr_satisf_eq(Rest,Gr,Sh).
%% 
%% shfr_satisf_eq(X,Y,Gr,Sh):-
%%      ord_intersection([X,Y],Gr,Int),
%%      ( Int = [_,_] ->
%%          true
%%      ; Int = [],
%%        ord_split_lists_from_list([X,Y],Sh,Intersect,_),
%%        ( ord_split_lists(Intersect,X,_,[]); ord_split_lists(Intersect,Y,_,[]))).
%% 
%% :- pop_prolog_flag(multi_arity_warnings).
%% 
%% shfr_fail_eq([eq(X,Y)|_],Free,Sh):-
%%      ord_intersect([X,Y],Free),
%%      ord_split_lists(Sh,X,Intersect,_),
%%      ord_split_lists(Intersect,Y,[],_).
%% shfr_fail_eq([_|Rest],Free,Sh):-
%%      shfr_fail_eq(Rest,Free,Sh).
%% 
%% %-------------------------------------------------------------------------
%% % shfr_downwards_closed(+,+,-)
%% % shfr_downwards_closed(ACns1,ACns2,ACns)
%% %-------------------------------------------------------------------------
%% % ACns2 must be more instantiated than ACns1 but some downwards closed
%% % properties might have been lost due to a later lub. Thus, those
%% % properties must be returned to ACns2. Iff something free becomes 
%% % ground ACns1 is more instantiated than ACns2 and we fail. Otherwise 
%% % we propagate these properties from ACns1 to ACns2.
%% %-------------------------------------------------------------------------
%% 
%:- export(shfr_downwards_closed/3).  
%% shfr_downwards_closed((_,Fr1),(Sh2,Fr2),(Sh,Fr)):- 
%%      member_value_freeness(Fr1,Gv,g),
%%      collect_vars_freeness(Fr2,Sv),
%%      ord_intersection(Gv,Sv,NewGr),
%%      update_lambda_non_free(NewGr,Fr2,Sh2,Fr,Sh).
%%      
%% %-------------------------------------------------------------------------
%% % shfr_extend_free(+,+,-)
%% % shfr_extend_free(ASub,Vars,NewASub)
%% %-------------------------------------------------------------------------
%% 
%:- export(shfr_extend_free/3).
%% shfr_extend_free((Sh,Fr),Vars,(NSh,NFr)):-
%%      change_values_insert(Vars,Fr,NFr,f),
%%      list_to_list_of_lists(Vars,Temp1),
%%      merge(Temp1,Sh,NSh).
%% 
%% 
%% %------------------------------------------------------------------------%
%% % shfr_hash(+,-)
%% % shfr_hash(ASub,N)
%% %------------------------------------------------------------------------%
%% % Returns an atom which identifies ASub
%% %------------------------------------------------------------------------%
%% 
%:- export(shfr_hash/3).      
%% shfr_hash('$bottom',_,-2).
%% shfr_hash(true,_,0).
%% shfr_hash((Sh,Fr),Fnv,N):-
%%      \+ \+
%%      (  primes(Primes),
%% %%      collect_vars_freeness(Fr,Vars),
%% %%      append(Vars,_,Primes),
%%         append(Fnv,_,Primes),
%%         shfr_hash_fr(Fr,0,N1),
%%         sum_list_of_lists(Sh,N1,N2),
%%         recorda_internal('$hash',N2,_)
%%         ),
%%      recorded_internal('$hash',N,Ref),
%%      erase(Ref).
%% 
%% shfr_hash_fr([],N,N).
%% shfr_hash_fr([X/V|Rest],N0,N):-
%%      ( V = f ->
%%          N1 is N0+X
%%      ; ( V = g ->
%%          N1 is N0-X 
%%        ; N1 = N0
%%           )
%%         ),
%%      shfr_hash_fr(Rest,N1,N).
%% 
%% 
%% %------------------------------------------------------------------------%
%% % shfr_convex_hull(+,+,-)
%% % shfr_convex_hull(Old,New,Hull)
%% %------------------------------------------------------------------------%
%% % Computes the convex hull between the initial abstraction Old and the
%% % more instantiated one New           
%% %------------------------------------------------------------------------%
%% 
%:- export(shfr_convex_hull/3).
%% shfr_convex_hull((OldSh,OldFr),(_,NewFr),(HullSh,HullFr)):- !,
%%      closure_under_union(OldSh,HullSh),
%%      compute_lub_fr(OldFr,NewFr,HullFr).
%% shfr_convex_hull(_,_,'$bottom').
%% 
%% %-------------------------------------------------------------------------
%% % shfr_impose_cond(+,+,+,-)
%% % shfr_impose_cond(Conds,ACns,Sv,LASub)
%% %-------------------------------------------------------------------------
%% 
%:- export(shfr_impos_cond/4).
%% shfr_impose_cond([],_,_,[]).
%% shfr_impose_cond([(Gr,_,_)|Rest],Sv,(Sh,Fr),[ASub1|LASub]):-
%%      update_lambda_sf(Gr,Fr,Sh,Fr1,Sh1),
%%      shfr_project(not_provided_Sg,Sv,not_provided_HvFv_u,(Sh1,Fr1),ASub1),
%%      shfr_impose_cond(Rest,Sv,(Sh,Fr),LASub).
%% 
%% %-------------------------------------------------------------------------
%% % shfr_real_conjoin(+,+,-)
%% % shfr_real_conjoin(ACns1,ACns2,Conj)
%% %-------------------------------------------------------------------------
%% 
%:- export(shfr_real_conjoin/3).
%% shfr_real_conjoin(_,'$bottom','$bottom'):- !.
%% shfr_real_conjoin('$bottom',_,'$bottom').
%% shfr_real_conjoin((ShOld,FrOld),(ShNew,FrNew),(Sh,Fr)):-
%%      member_value_freeness(FrNew,Gv,g),
%%      update_lambda_sf(Gv,FrOld,ShOld,Fr,Sh0),
%%         ( Sh0 == ShNew ->
%%          Sh0 = Sh
%%      ; %write(user,'WARNING: a complete conjunction needed'),
%%        merge(ShNew,Sh0,Sh)).

