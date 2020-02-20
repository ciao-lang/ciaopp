:- module(sharing, [], [assertions, regtypes, isomodes]).

:- doc(title, "sharing (abstract domain)").
:- doc(author, "Kalyan Muthukumar"). % started: 5/2/89
:- doc(author, "Maria Garcia de la Banda").
:- doc(author, "Francisco Bueno").

:- use_module(domain(sharing_amgu), [
    share_amgu_amgu/4,
    share_amgu_augment_asub/3,
    share_amgu_augment_two_asub/3]).
:- include(ciaopp(plai/plai_domain)).
:- dom_def(share).
:- dom_impl(share, amgu/4, from(sharing_amgu:share_amgu)).
:- dom_impl(share, augment_asub/3, from(sharing_amgu:share_amgu)).
:- dom_impl(share, augment_two_asub/3, from(sharing_amgu:share_amgu)).
:- dom_impl(share, call_to_entry/9).
:- dom_impl(share, exit_to_prime/7).
:- dom_impl(share, project/5).
:- dom_impl(share, compute_lub/2).
:- dom_impl(share, abs_sort/2).
:- dom_impl(share, extend/5).
:- dom_impl(share, less_or_equal/2).
:- dom_impl(share, glb/3).
:- dom_impl(share, call_to_success_fact/9).
:- dom_impl(share, special_builtin/5).
:- dom_impl(share, success_builtin/6).
:- dom_impl(share, call_to_success_builtin/6).
:- dom_impl(share, input_interface/4).
:- dom_impl(share, input_user_interface/5).
:- dom_impl(share, asub_to_native/5).
:- dom_impl(share, unknown_call/4).
:- dom_impl(share, unknown_entry/3).
:- dom_impl(share, empty_entry/3).
% :- dom_impl(share, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).

%------------------------------------------------------------------------%
%                    Meanning of the Program Variables                   %
%                                                                        %
% BPrime   : similar to the abstract prime constraint: abstract          %
%            subtitution obtained after the analysis of the clause being %
%            considered still projected onto Hv (i.e. just before going  %
%            Sv and thus, to Prime)                                      %
% Binds    : List of primitive bindings corresponding to the unification %
%            of Term1 = Term2.                                           %
% Gv       : set of ground variables (can be added as a prefix of a set  %
%            of variables, e.g. GvHv means the set of ground variables of%
%            the head variables)                                         %
% Partition: Set of set of variables in which ach variable appears only  %
%            in one set. It is the result of a transitive closure        %
% _args    : Added as a prefix of a term, means the set of variables     %
%            s.t. the i-th set contains the set of variables (ordered) in%
%            the i-th argument of the Term                               %
% Star     : a closure under union of a set of sets (can be added as a   %
%            suffix of a set of sets)                                    %
% ArgShare : Sets of numbers representing the possible set sharing among %
%            the argument positions indicated by the numbers             %
% ShareArgs: Set of sets of numbers in which each set represents the     %
%            possible set sharing among the argument positions indicated %
%            by the numbers                                              %
% Rest are as in domain_dependent.pl                                     %
%------------------------------------------------------------------------%

:- use_module(domain(s_grshfr), [new1_gvars/4, projected_gvars/3]).

:- use_module(library(sets), 
    [ insert/3, 
      merge/3,
      ord_intersect/2,
      ord_intersection/3,
      ord_intersection_diff/4,
      ord_member/2, 
      ord_subset/2, 
      ord_subtract/3
    ]).
:- use_module(library(lsets), 
    [ delete_var_from_list_of_lists/4,
      ord_member_list_of_lists/2, 
      split_lists_from_list/4,
      transitive_closure_lists/3,
      closure_under_union/2,
      ord_split_lists_from_list/4,
      merge_list_of_lists/2, 
      sort_list_of_lists/2
    ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2, varset_in_args/2]).
:- use_module(library(lists), [append/3, list_to_list_of_lists/2, powerset/2]).

% Plai lib, auxiliary
%:- use_module(typeslib(typeslib),[ dz_type_included/2, set_ground_type/1 ]).
:- use_module(typeslib(typeslib), [is_ground_type/1]).
:- use_module(domain(eterms), [eterms_input_interface/4]).
:- use_module(domain(share_aux)).

%------------------------------------------------------------------------%

:- regtype absu(A) # "@var{A} is an abstract substitution".
absu(_). % TODO: define properly for this domain

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% share_project(+,+,+,+,-)                                               |
% share_project(Sg,Vars,HvFv_u,ASub,Proj)                                |
% Eliminates from each element of the list of lists of variables given as|
% second argument any variable which is not an element of the first      |
% argument. Both ordered.                                                |
% i.e. Proj = {Ys | Xs in ASub, Ys = Xs intersect Vars }                 |
%------------------------------------------------------------------------%

:- export(share_project/5).    
share_project(_,_,_,'$bottom','$bottom'):- !.
share_project(_Sg,Vars,_HvFv_u,ASub,Proj) :-
    project_share(Vars,ASub,Proj).

:- export(project_share/3).    
project_share([],_,[]).
project_share([S|Ss],Lda_sh,Proj):-
    project_share0(Lda_sh,[S|Ss],Temp),
    sort(Temp,Proj).

project_share0([],_,[]).
project_share0([L|Ls],[X|Xs],Proj):-
    L = [Y|Ys],
    compare(D,X,Y),
    has_give_intersection(D,X,Xs,Y,Ys,Flag,Proj1,NewVars),
    project_share1(Flag,Proj1,NewVars,Ls,Proj).

project_share1(end,_Proj1,_NewVars,_Ls,[]).
project_share1(no,_Proj1,NewVars,Ls,Proj):-
    project_share0(Ls,NewVars,Proj).
project_share1(yes,Proj1,NewVars,Ls,[Proj1|Proj]):-
    project_share0(Ls,NewVars,Proj).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_call_to_entry(+,+,+,+,+,+,+,-,-)                                 %
% share_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)           %
% It obtains the abstract substitution (Entry) which results from adding %
% the abstraction of the Sg = Head to Proj, later projecting the         %
% resulting substitution onto Hv. This is done as follows:               %
%  * If Sg and Head are identical up to renaming it is just a question   %
%    or renaming Proj and adding the Fv as singletons                    %
%  * If Hv = [], Entry is just the Fv as singletons                      %
%  * Otherwise, it will                                                  %
%       - obtain Gv1 (ground variables in Sv due to Proj)                %
%       - obtain Binds (sorted list of primitive equations corresponding %
%         to the equation Sg = Head)                                     %
%       - obtain Gv2 (variables in Sv or Hv involved in a primitive      %
%         equation with a ground term)                                   %
%       - propagate the groundnes of Gv1 and Gv2 to Proj through Binds   %
%         obtaining NewBinds (grounding bindings eliminated) NewProj     %
%         (ground variables eliinated) Gv (final set of ground variables)%
%         GvSv and GvHv (subset of vars in Gv belonging to Sg and Head   %
%         respectively)                                                  %
%       - then it obtains Partition (the transitive closure of due to    %
%         the sharing established by NewProj) and H_partition (Partition %
%         projected onto the Hv variables)                               %
%       - then it obtains in ShareArgsStar the star of the sharing among %
%         the arguments of Sg established by NewProj, and in Head_args   %
%         the set of variables belonging to each argument of Head        %
%       - Then the idea is to obtain Entry by computing the powerset of  %
%         each equivalence class in H_partition and eliminating those    %
%         sets in the powerset which are not allowed (they would imply   %
%         sharing among arguments in the head while there is no sharing  %
%         among those arguments in ShareArgsStar)
%-------------------------------------------------------------------------

:- export(share_call_to_entry/9).
share_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
    variant(Sg,Head),!,
    ExtraInfo = yes,
    copy_term((Sg,Proj),(NewSg,NewProj)),
    Head = NewSg,
    share_abs_sort(NewProj,Temp),
    list_to_list_of_lists(Fv,Temp1),
    merge(Temp1,Temp,Entry).
share_call_to_entry(_,_,[],_,_K,Fv,_,Entry,ExtraInfo):- !,
    ExtraInfo = no,
    list_to_list_of_lists(Fv,Entry).
share_call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
    projected_gvars(Proj,Sv,Gv1),
    abs_unify(Sg,Head,Binds,Gv2),
    groundness_propagate(Binds,Sv,Gv1,Gv2,Proj,
                                        NewBinds,NewProj,Gv,SvGv,HvGv),
    pd_graph(Sv,Hv,SvGv,HvGv,NewProj,NewBinds,Partition,H_partition),
    script_p_star(Sg,NewProj,ShareArgsStar),
    varset_in_args(Head,Head_args),
    list_to_list_of_lists(Fv,FvSingl),
    compute_entry(H_partition,Head_args,ShareArgsStar,FvSingl,Entry),
    ExtraInfo = (Gv,NewBinds,NewProj,Partition), !.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_exit_to_prime(+,+,+,+,+,+,-)                                     %
% share_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                %
% It computes the prime abstract substitution Prime, i.e.  the result of %
% going from the abstract substitution over the head variables (Exit), to%
% the abstract substitution over the variables in the subgoal. It will:  %
% * If Exit is '$bottom', Prime will be also '$bottom'.                  %
% * If Flag = yes (Head and Sg identical up to renaming) it is just a    %
%   question or renaming Exit                                            %
% * If Hv = [], Prime = []                                               %
% * Otherwise, it will:                                                  %
%      - project Exit onto Hv obtaining BPrime                           %
%      - subtract from Hv those vars which were ground due to the        %
%        equation Head = Sg (Gv) obtaining Hv_rem                        %
%      - obtain the vars Hv_rem which had becomed ground after the       %
%        of the clause (NewGv_Hv)                                        %
%      - Then if NewGv_Hv is \== [], groundness must be propagated       %
%        to obtain ASub                                                  %
%      - Otherwise, ASub is just equal to NewProj                        %
%      - Then Prime is obtained by obtaining New_partition (transitive   %
%        closure of the sharing specified in Bprime) and performing the  %
%        same kind of prunning that in the call_to_entry but in the      %
%        opposite direction.                                             %
%-------------------------------------------------------------------------

:- export(share_exit_to_prime/7).
share_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,'$bottom') :- !.
share_exit_to_prime(Sg,Hv,Head,_Sv,Exit,Flag,Prime):-  
    Flag == yes, !,
    share_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewHead,NewPrime)),
    Sg = NewHead,
    share_abs_sort(NewPrime,Prime).
share_exit_to_prime(_,[],_,_,_,_,[]):- !.
share_exit_to_prime(Sg,Hv,Head,Sv,Exit,(Gv,NewBinds,NewProj,Partition),Prime):-
    share_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    ord_subtract(Hv,Gv,Hv_rem),
    projected_gvars(BPrime,Hv_rem,NewGv_Hv),
    ( NewGv_Hv = [] ->
        transitive_closure_lists(BPrime,Partition,New_partition_u),
        ASub = NewProj
    ; groundness_propagate(NewBinds,Sv,Gv,NewGv_Hv,NewProj,
                                        Binds,ASub,_,SvGv,HvGv),
      ng_vars(Hv,HvGv,[],Part0_head),
      ng_vars(Sv,SvGv,Part0_head,Partition0),
      transitive_closure_lists(ASub,Partition0,Partition1),
      transitive_closure_lists(BPrime,Partition1,Partition2),
      transitive_closure_binds(Binds,Partition2,New_partition_u)
    ),
    sort(New_partition_u,New_partition),
    project_share(Sv,New_partition,S_partition),
    script_p(Head,BPrime,ShareArgs),
    varset_in_args(Sg,Sg_args),
    closure_under_union(ASub,Star),
    compute_success_proj(S_partition,Sg_args,ShareArgs,Star,[],Prime),
    !.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT SORT                                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_abs_sort(+,-)                                                        |
% share_abs_sort(Asub,Asub_s)                                                |
% sorts the set of set of variables ASub to obtaint the Asub_s           |
%-------------------------------------------------------------------------

:- export(share_abs_sort/2).       
share_abs_sort('$bottom','$bottom'):- !.
share_abs_sort(ASub,ASub_s):-
    sort_list_of_lists(ASub,ASub_s).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT LUB                                      %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_compute_lub(+,-)                                                 %
% share_compute_lub(ListASub,Lub)                                        %
% It computes the lub of a set of Asub. For each two abstract            %
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   %
% merging the ASub1 and ASub2.                                           %
%------------------------------------------------------------------------%

:- export(share_compute_lub/2).
share_compute_lub([ASub1,ASub2|Rest],Lub) :-
    share_lub(ASub1,ASub2,ASub3),
    share_compute_lub([ASub3|Rest],Lub).
share_compute_lub([ASub],ASub).

:- export(share_lub/3).      
share_lub(ASub1,ASub2,ASub3):-
    ASub1 == ASub2,!,
    ASub3 = ASub2.
share_lub(ASub1,ASub2,ASub3):-
    merge_subst(ASub1,ASub2,ASub3).

merge_subst('$bottom',Yss,Yss):- !.
merge_subst(Xss,'$bottom',Xss):- !.
merge_subst(Xss,Yss,Zss) :-
    merge(Xss,Yss,Zss).

%------------------------------------------------------------------------%
% share_glb(+,+,-)                                                       %
% share_glb(ASub0,ASub1,Lub)                                             %
% Glb is just intersection.                                              %
%------------------------------------------------------------------------%

:- export(share_glb/3).      
share_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
share_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
share_glb(ASub0,ASub1,Glb):-
    ord_intersection(ASub0,ASub1,ASub),
%%      ( ASub=[], ASub0\==[], ASub1\==[] -> Glb = '$bottom' ; Glb=ASub ).
%% this is not true AADEBUG
    Glb = ASub.
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT EXTEND                                   %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% share_extend(+,+,+,+,-)                                                %
% share_extend(Sg,Prime,Sv,Call,Succ)                                    %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ. Otherwise,  %
% it splits Call into two sets of sets: Intersect (those sets containing %
% at least a variabe in Sv) and Disjunct (the rest). Then is obtains     %
% in Star the closure under union of Intersect. Finally, it prunes Star  %
% with the information in Prime adding, at the end, Disjunct.            %
%------------------------------------------------------------------------%

:- export(share_extend/5).     
share_extend(_Sg,'$bottom',_Hv,_Call,Succ):- !,
    Succ = '$bottom'.
share_extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
share_extend(_Sg,Prime,Sv,Call,Succ) :-
    ord_split_lists_from_list(Sv,Call,Intersect,Disjunct),
    closure_under_union(Intersect,Star),
    prune_success(Star,Prime,Sv,Disjunct,Succ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%

:- export(share_call_to_success_fact/9).
share_call_to_success_fact(_Sg,[],_Head,_K,Sv,Call,_,[],Succ) :- !,
    ord_split_lists_from_list(Sv,Call,_Intersect,Succ).
share_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ) :-
    projected_gvars(Proj,Sv,Gv1),
    abs_unify(Sg,Head,Binds,Gv2),!,
    groundness_propagate(Binds,Sv,Gv1,Gv2,Proj,
                                        NewBinds,NewProj,_,SvGv,HvGv),
    pd_graph(Sv,Hv,SvGv,HvGv,NewProj,NewBinds,Partition,H_partition),
    script_p_star(Sg,NewProj,ShareArgsSgStar),
    varset_in_args(Head,Head_args),
    compute_entry(H_partition,Head_args,ShareArgsSgStar,[],Entry),
%       -------------------------------------------------
    project_share(Sv,Partition,S_partition),
    script_p(Head,Entry,ShareArgsHead),
    varset_in_args(Sg,Sg_args),
    closure_under_union(Proj,ProjStar),
    compute_success_proj(S_partition,Sg_args,ShareArgsHead,ProjStar,[],
                                                                Prime),
    share_extend(Sg,Prime,Sv,Call,Succ).
share_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom').

%-------------------------------------------------------------------------
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%-------------------------------------------------------------------------

:- export(share_call_to_prime_fact/6).
share_call_to_prime_fact(_Sg,[],_Head,_Sv,_Call,Prime) :- !,
    Prime = [].
share_call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
    projected_gvars(Call,Sv,Gv1),
    abs_unify(Sg,Head,Binds,Gv2),
    groundness_propagate(Binds,Sv,Gv1,Gv2,Call,
                                       NewBinds,NewProj,_,SvGv,HvGv),
    pd_graph(Sv,Hv,SvGv,HvGv,NewProj,NewBinds,Partition,H_partition),
    script_p_star(Sg,NewProj,ShareArgsSgStar),
    varset_in_args(Head,Head_args),
    compute_entry(H_partition,Head_args,ShareArgsSgStar,[],Entry),
%       -------------------------------------------------
    share_project(Sg,Sv,not_provided_HvFv_u,Partition,S_partition),
    script_p(Head,Entry,ShareArgsHeadStar),
    varset_in_args(Sg,Sg_args),
    closure_under_union(Call,Star),
    compute_success_proj(S_partition,Sg_args,ShareArgsHeadStar,Star,[],
                                                           Prime).

%-------------------------------------------------------------------------
%            Intermediate Functions                                      %
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% projected_gvars(+,+,-)                                                 |
% projected_gvars(ASub,Vars,Gv)                                          |
% Obtains in Gv the set of variables in Vars which are ground w.r.t. ASub|
%-------------------------------------------------------------------------

% MOVED TO MODULE TOPC

%-------------------------------------------------------------------------
% abs_unify(+,+,-,-)                                                     |
% abs_unify(Term1,Term2,Binds,Gv)                                        |
% First obtains in Temp2 the sorted list of normalized equations         |
% corresponding to the equation Term1 = Term2.                           |
% Then for each X such that exists (X,S) and (X.S') in Temp2, it replaces|
% them by (X [S,S']) obtaining Binds and computes Gv (the variables in   |
%  Sv or Hv involved in a primitive equation with a ground term)         |
%-------------------------------------------------------------------------

abs_unify(Term1,Term2,Binds,Gv) :-
    sh_peel(Term1,Term2,Temp1-[]),
    sort(Temp1,Temp2),
    collect(Temp2,Binds,Gv).

sh_peel(Term1,Term2,Binds) :-
    var(Term1),!,
    sh_peel_var(Term1,Term2,Binds).
sh_peel(Term1,Term2,Binds) :-
    var(Term2),!,
    varset(Term1,List),
    Binds = [(Term2,List)|X]-X.
sh_peel(Term1,Term2,Binds) :- 
    Term1 == Term2, !,
    Binds = X-X.
sh_peel(Term1,Term2,Binds) :-
    functor(Term1,F,N),
    functor(Term2,F,N),
    sh_peel_args(Term1,Term2,0,N,Binds).

sh_peel_var(Term1,Term2,Binds):-
    var(Term2),!,
    Binds = [(Term1,[Term2])|X]-X.
sh_peel_var(Term1,Term2,Binds):-
    varset(Term2,List),
    Binds = [(Term1,List)|X]-X.

sh_peel_args(_,_,N1,N,Binds) :-
    N1 = N, !,
    Binds = X-X.
sh_peel_args(Term1,Term2,N1,N,Binds) :-
    N2 is N1 + 1,
    arg(N2,Term1,A1),
    arg(N2,Term2,A2),
    sh_peel(A1,A2,Bind1),
    sh_peel_args(Term1,Term2,N2,N,Bind2),
    append_dl(Bind1,Bind2,Binds).

collect([(X1,List1),(X2,List2)|Rest],Binds,Gv) :-
    ( List1 = [] ->
        Gv = [X1|G_rest]
    ; Gv = G_rest
    ),
    ( X1 == X2 ->
        collect([(X2,List2)|Rest],[(X2,List)|Bind],G_rest),
        Binds = [(X1,[List1|List])|Bind]
    ; collect([(X2,List2)|Rest],Bind,G_rest),
      Binds = [(X1,[List1])|Bind]
    ).
collect([(X,List)],[(X,[List])],Gv):-
    ( List = [] ->
        Gv = [X]
    ; Gv = []
    ).
collect([],[],[]).

%-------------------------------------------------------------------------
% groundness_propagate(+,+,+,+,+,-,-,-,-,-)                              |
% groundness_propagate(OldBinds,Sv,Gv1,Gv2,Proj,                         |
%                              NewBinds,NewProj,Gv,SvGv,HvGv)            |
% It first propagates the groundness of the variables contained in       |
% Gv1 and Gv2  to OldBinds obtaining Gv. Then it splits Gv into SvGv     |
% and HvGv(i.e. those belonging to the subgoal and head respectively)    |
% Then it substract from SvGv those variables which where known to be    |
% ground in Proj obtaining in New_gvars those which have become ground   |
% due to the unification.                                                |
% Finally, it updates Proj with this information and sorts it            |
%-------------------------------------------------------------------------

groundness_propagate(OldBinds,Sv,Gv1,Gv2,Proj,NewBinds,NewProj,Gv,SvGv,HvGv) :-
    merge(Gv1,Gv2,Gvars),                
    g_propagate(Gvars,OldBinds,Gvars,NewBinds,Gv),
    ord_intersection_diff(Gv,Sv,SvGv,HvGv),
    ord_subtract(SvGv,Gv1,NewGv),
    ord_split_lists_from_list(NewGv,Proj,_Intersect,NewProj).

g_propagate([],OldBinds,Gvars,OldBinds,Gvars).
g_propagate([X|Xs],OldBinds,Gvars,NewBinds,Gv) :-
    new1_gvars(OldBinds,X,Int1_Binds,New1_gvars),
    new2_gvars(Int1_Binds,X,Int2_Binds,New2_gvars),
    append(New1_gvars,New2_gvars,Int_gvars),
    sort(Int_gvars,New_gvars),
    ord_subtract(New_gvars,Gvars,New),
    merge(New,Xs,Queue),
    merge(New,Gvars,GvInt),!,
    g_propagate(Queue,Int2_Binds,GvInt,NewBinds,Gv).


new2_gvars([],_,[],[]).
new2_gvars([(Y,Bind)|Rest],X,[(Y,New_bind)|New_rest],New2_gvars) :-
    delete_var_from_list_of_lists(X,Bind,New_bind,Ans),
    ( Ans = yes ->
        New2_gvars = [Y|Rem_gvars]
    ; New2_gvars = Rem_gvars
    ),
    new2_gvars(Rest,X,New_rest,Rem_gvars).
        
%-------------------------------------------------------------------------
% pd_graph(+,+,+,+,+,+,-,-)                                              |
% pd_graph(Sv,Hv,SvGv,HvGv,NewProj,Binds,Partition,Proj_Partition)       |
% It first obtains in Partition0 a list of singletons in which [X] is    |
% an element of the list if X is in either Hv or Sv and it is non ground |
% (i.e. is not an element of SvGv or HvGv).                              |
% Then it obtains in Partition1 the transitive closure of the sharing    |
% among the Sv and Hv variables specified in NewProj, and then           |
% in Partition it extends the transitive closure of Partition1 due to the|
% new sharing established by Binds. Finally it projects it onto the Hv   |
%-------------------------------------------------------------------------

pd_graph(Sv,Hv,SvGv,HvGv,NewProj,Binds,Partition,Proj_Partition) :-
    ng_vars(Hv,HvGv,[],Part0_head),
    ng_vars(Sv,SvGv,Part0_head,Partition0),
    transitive_closure_lists(NewProj,Partition0,Partition1),
    transitive_closure_binds(Binds,Partition1,Partition_u),
    sort(Partition_u,Partition),
    share_project(not_provided_Sg,Hv,not_provided_HvFv_u,Partition,Proj_Partition).

%-------------------------------------------------------------------------
% ng_vars(+,+,+,-)                                                       |
% ng_vars(Vars,Gv,Tail,Singletons)                                       |
% Obtains in Singletons the [X] corresponding to each X which is in Vars |
% and not in Gv and then adds Tail at the end of the list                |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

ng_vars([], _, Initial,Initial).
ng_vars([X|List], [], Initial,[[X]|New_list]) :- !,
    ng_vars(List, [], Initial,New_list).
ng_vars([Head1|Tail1], [Head2|Tail2], Initial,Intersection) :-
    compare(Order, Head1, Head2),
    ng_vars(Order, Head1, Tail1, Head2, Tail2, Initial,Intersection).

ng_vars(<, X, [], _, _, Initial, [[X]|Initial]) :- !.
ng_vars(<, X, [Head1|Tail1], Head2, Tail2, Initial,[[X]|Intersection]) :-
    compare(Order, Head1, Head2),
    ng_vars(Order, Head1, Tail1, Head2, Tail2, Initial,Intersection).
ng_vars(=, _, Tail1, _, Tail2, Initial, Intersection) :-
    ng_vars(Tail1, Tail2, Initial,Intersection).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% transitive_closure_binds(+,+,-)                                        |
% transitive_closure_binds(Binds,Old_partition,New_partition)            |
% It starts with a transitive closure in Old_partition (each variable    |
% appears only in one set). The aim is to obtain in New_partition the    |
% new transitive closure of the Old_partition due to the bindings in     |
% Binds.                                                                 |
%-------------------------------------------------------------------------

transitive_closure_binds([],Partition,Partition).
transitive_closure_binds([(X,Xss)|Rest],Old_partition,New_partition) :-
    merge_list_of_lists([[X]|Xss],Xs),
    split_lists_from_list(Xs,Old_partition,Intersect,NotIntersect),
    merge_list_of_lists(Intersect,Merged),
    transitive_closure_binds(Rest,[Merged|NotIntersect],New_partition).

%-------------------------------------------------------------------------
% compute_entry(+,+,+,+,-)                                               |
% compute_entry(Partition,Head_args,ShareArgsStar,FvSingl,Entry)         |
% Foreach Xs in Partition it computes the powerset of Xs and prunes the  |
% result with the information available in Head_args and ShareArgsStar   |
% The result is added to FvSingl                                         |
%-------------------------------------------------------------------------

compute_entry([],_Head_args,_ShareArgsStar,Entry,Entry).
compute_entry([Xs|Xss],Head_args,ShareArgsStar,FvSingl,Entry) :-
    powerset(Xs,Powerset),
    prune_entry(Powerset,Head_args,ShareArgsStar,FvSingl,Temp),
    compute_entry(Xss,Head_args,ShareArgsStar,Temp,Entry).

prune_entry([],_Head_args,_ShareArgsStar,Entry,Entry).
prune_entry([Xs|Xss],Head_args,ShareArgsStar,Temp1,Entry) :-
    pos(Head_args,1,Xs,ArgShare),
    ( ord_member(ArgShare,ShareArgsStar) ->
        insert(Temp1,Xs,Temp2)
    ; Temp2 = Temp1
    ),
    prune_entry(Xss,Head_args,ShareArgsStar,Temp2,Entry).

%-------------------------------------------------------------------------
% pos(+,+,+,-)                                                           |
% pos(Xss,Arg,Xs,ArgShare)                                               |
% Xss is a list containing in each Set_i the variables in the i-th       |
% arg of the Term. Arg is the number of the current arg. Xs is a sorted  |
% list of variables. It will obtain ArgShare, the set of arguments in    |
% at least one variable in Xs appears                                    |
%-------------------------------------------------------------------------

:- export(pos/4).
pos([],_,_,[]).
pos([Ys|Yss],N,Xs,ArgShare) :-
    ord_intersect(Xs,Ys),!,
    ArgShare = [N|Rest_share],
    N1 is N+1,
    pos(Yss,N1,Xs,Rest_share).
pos([_Ys|Yss],N,Xs,ArgShare) :-
    N1 is N+1,
    pos(Yss,N1,Xs,ArgShare).

%-------------------------------------------------------------------------
% script_p_star(+,+,-)                                                   |
% script_p_star(Atom,ASub,ShareArgsStar)                                 | 
% It first obtains in ArgSare_info the set of sets of argument numbers   |
% of Atom each one corresponding to each set in ASub. Then it obtains    |
% the closure under union.                                               |
%-------------------------------------------------------------------------

:- export(script_p_star/3).
script_p_star(Atom,ASub,ShareArgsStar) :-
    script_p(Atom,ASub,ShareArgs_info),
    closure_under_union(ShareArgs_info,ShareArgsStar).

:- export(script_p/3).
script_p(Atom,ASub,ShareArgs_info) :-
    varset_in_args(Atom,Xss_args),
    script_p1(ASub,Xss_args,Temp),
    sort(Temp,ShareArgs_info).

script_p1([],_,[]).
script_p1([Xs|Xss],Atom_args,[ArgShare|ShareArgs_info]) :-
    pos(Atom_args,1,Xs,ArgShare),
    script_p1(Xss,Atom_args,ShareArgs_info).

%-------------------------------------------------------------------------
% compute_success_proj(+,+,+,+,+,-)                                      |
% compute_success_proj(Partition,Sg_args,ShareArgsStar,Star,Temp,Prime)  |
% For each element in Partition, it computes its Powerset. Then, for each|
% element Xs in Powerset it computes the corresponding ArgsShare w.r.t   |
% Sg_args. If ArgsShare is in ShareArgsStar and Xs is in Star, Xs is     |
% added to Prime. Otherwise, it is eliminated                            |
%-------------------------------------------------------------------------

compute_success_proj([],_,_,_,Prime,Prime).
compute_success_proj([Xs|Xss],Sg_args,ShareArgsStar,Star,Temp,Prime) :-
    powerset(Xs,Powerset),
    prune_success_proj(Powerset,Sg_args,ShareArgsStar,Star,Temp,Temp1),
    compute_success_proj(Xss,Sg_args,ShareArgsStar,Star,Temp1,Prime).

prune_success_proj([],_,_,_,Prime,Prime).           
prune_success_proj([Xs|Xss],Sg_args,ShareArgsStar,Star,Temp1,Prime) :-
    pos(Sg_args,1,Xs,ArgShare),
    ( ( ord_member(ArgShare,ShareArgsStar), ord_member(Xs,Star) ) ->
          insert(Temp1,Xs,Temp2)
    ; Temp2 = Temp1
    ),
    prune_success_proj(Xss,Sg_args,ShareArgsStar,Star,Temp2,Prime).

%-------------------------------------------------------------------------

prune_success([],_Prime,_Sv,Succ,Succ).
prune_success([Xs|Xss],Prime,Sv,Call,Succ) :-
    ord_intersection(Xs,Sv,Xs_proj),
    ( ord_member(Xs_proj,Prime) ->
        insert(Call,Xs,Temp)
    ; Temp = Call
    ),
    prune_success(Xss,Prime,Sv,Temp,Succ).

%-------------------------------------------------------------------------
% share_unknown_entry(+,+,-)                                             |
% share_unknown_entry(Sg,Qv,Call)                                        |
% The top value in Sharing for a set of variables is the powerset        |
%-------------------------------------------------------------------------

:- export(share_unknown_entry/3).
share_unknown_entry(_Sg,Qv,Call):-
    powerset(Qv,Call_u),
    sort_list_of_lists(Call_u,Call).

:- export(share_empty_entry/3).
:- pred share_empty_entry(+Sg,+Vars,-Entry): callable * list * absu # "Gives the
""empty"" value in this domain for a given set of variables
@var{Vars}, resulting in the abstract substitution @var{Entry}. I.e.,
obtains the abstraction of a substitution in which all variables
@var{Vars} are unbound: free and unaliased. In this domain is the list
of singleton lists of variables".

share_empty_entry(_Sg,Vars,Entry):-
    list_to_list_of_lists(Vars,Entry).

%------------------------------------------------------------------------%
% share_output_interface(+,-)                                            %
% share_output_interface(ASub,Output)                                    %
% The readible format still close to the internal formal is identical    %
% in Sharing                                                             %
%-------------------------------------------------------------------------

%:- export(share_output_interface/2). 
% share_output_interface(Succ,Succ).

%------------------------------------------------------------------------%
% share_asub_to_native(+,+,+,-,-)                                        %
% share_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                  %
% The user friendly format consists in extracting the ground variables   %
%------------------------------------------------------------------------%

:- export(share_asub_to_native/5). 
share_asub_to_native('$bottom',_Qv,_OutFlag,_ASub_user,_Comps):- !, fail.
share_asub_to_native(Succ,Qv,_OutFlag,Info,[]):-
    if_not_nil(Succ,sharing(Succ),Info,Info0),
    projected_gvars(Succ,Qv,Gv),
    if_not_nil(Gv,ground(Gv),Info0,[]).

%------------------------------------------------------------------------%
% share_input_user_interface(+,+,-,+,+)                                  %
% share_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)         %
% Obtaining the abstract substitution for Sharing from the user supplied %
% information just consists in taking the mshare(Sharing) element of     %
% InputUser and sorting it. If there is no such element, get the "top"   %
% sharing for the variables involved.                                    %
%------------------------------------------------------------------------%

:- export(share_input_user_interface/5).  
share_input_user_interface((Gv0,Sh0,Indep0),Qv,Call,_Sg,_MaybeCallASub):-
    may_be_var(Gv0,Gv),
    may_be_var(Sh0,ASub0),
    may_be_var(Indep0,Indep),
    ord_split_lists_from_list(Gv,ASub0,_Intersect,ASub1),
    ord_subtract(Qv,Gv,NGv0),
    merge_list_of_lists(ASub1,Vars),
    ord_subtract(NGv0,Vars,NGv),
    share_unknown_entry(sg_not_provided,NGv,ASub2),
    merge(ASub1,ASub2,ASub),
    handle_each_indep(Indep,share,ASub,Call).

:- export(share_input_interface/4).  
share_input_interface(ground(X),perfect,(Gv0,Sh,I),(Gv,Sh,I)):-
    varset(X,Vs),
    myappend(Gv0,Vs,Gv).
share_input_interface(sharing(X),perfect,(Gv,Sh0,I),(Gv,Sh,I)):-
% should check that X is consistent!
    nonvar(X),
    sort_list_of_lists(X,ASub),
    myappend(ASub,Sh0,Sh).
share_input_interface(indep(X),perfect,(Gv,Sh,I0),(Gv,Sh,I)):-
    nonvar(X),
    sort_list_of_lists(X,I1),
    myappend(I1,I0,I).
share_input_interface(regtype(E),approx,S0,S):-
    eterms_input_interface(regtype(E),perfect,[],[NonPT]),
    functor(NonPT,T,1),
    % set_ground_type(G),
    % dz_type_included(T,G),
    is_ground_type(T),
    share_input_interface(ground(E),_Any,S0,S).

myappend(Vs,V0,V):-
    var(Vs), !,
    V=V0.
myappend(Vs,V0,V):-
    merge(Vs,V0,V).

may_be_var(X,X):- ( X=[] ; true ), !.

%-------------------------------------------------------------------------
% share_unknown_call(+,+,+,-)                                            |
% share_unknown_call(Sg,Vars,Call,Succ)                                  |
% Obtained by selecting those sets in Call for which at least a variable |
% in Vars appears, making the star of those sets, and adding the sets    |
% with empty intersection with Vars                                      |
%-------------------------------------------------------------------------

:- export(share_unknown_call/4).
share_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
share_unknown_call(_Sg,_Vars,[],[]) :- !.
share_unknown_call(_Sg,Vars,[C|Call],Succ) :-
    ord_split_lists_from_list(Vars,[C|Call],Intersect,Rest),
    closure_under_union(Intersect,Star),
    merge(Star,Rest,Succ).

%------------------------------------------------------------------------%
% share_less_or_equal(+,+)                                               %
% share_less_or_equal(ASub0,ASub1)                                       %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

:- export(share_less_or_equal/2).
share_less_or_equal('$bottom',_ASub):- !.
share_less_or_equal(ASub0,ASub1):-
    ASub0 == ASub1, !.
share_less_or_equal(ASub0,ASub1):-
    ord_subset(ASub0,ASub1).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% share_special_builtin(+,+,+,-,-)                                       |
% share_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                  |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) ground : if the builtin makes all variables ground whithout        |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) bottom : if the abstract execution of the builtin returns bottom   |
% (3) unchanged : if we cannot infer anything from the builtin, the      |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previous freeness values of the variables.                  |
% (4) some: if it makes some variables ground without imposing conditions|
% (5) Sgkey: special handling of some particular builtins                |
%-------------------------------------------------------------------------

:- export(share_special_builtin/5).
%-------------------------------------------------------------------------
% metacuts
%% share_special_builtin('CHOICE IDIOM/1',_,_,ground,_).
%% share_special_builtin('CUT IDIOM/1',_,_,ground,_).
%% share_special_builtin('$metachoice/1',_,_,ground,_).
%% share_special_builtin('$metacut/1',_,_,ground,_).
%% share_special_builtin(':/2',(prolog:'$metachoice'(_)),_,ground,_).
%% share_special_builtin(':/2',(prolog:'$metacut'(_)),_,ground,_).
share_special_builtin('metachoice/1',_,_,ground,_).
share_special_builtin('metacut/1',_,_,ground,_).
%-------------------------------------------------------------------------
share_special_builtin('absolute_file_name/2',_,_,ground,_).
share_special_builtin('atom/1',_,_,ground,_).
share_special_builtin('atomic/1',_,_,ground,_).
share_special_builtin('$simplify_unconditional_cges/1',_,_,ground,_).
share_special_builtin('current_atom/1',_,_,ground,_).
share_special_builtin('current_input/1',_,_,ground,_).
share_special_builtin('current_module/1',_,_,ground,_).
share_special_builtin('current_output/1',_,_,ground,_).
share_special_builtin('current_op/3',_,_,ground,_).
share_special_builtin('close/1',_,_,ground,_).
share_special_builtin('depth/1',_,_,ground,_).
share_special_builtin('ensure_loaded/1',_,_,ground,_).
share_special_builtin('erase/1',_,_,ground,_).
share_special_builtin('float/1',_,_,ground,_).
share_special_builtin('flush_output/1',_,_,ground,_).
share_special_builtin('get_code/1',_,_,ground,_).
share_special_builtin('get1_code/1',_,_,ground,_).
share_special_builtin('get_code/2',_,_,ground,_).
share_special_builtin('get1_code/2',_,_,ground,_).
share_special_builtin('ground/1',_,_,ground,_).
share_special_builtin('int/1',_,_,ground,_).
share_special_builtin('integer/1',_,_,ground,_).
share_special_builtin('is/2',_,_,ground,_).
share_special_builtin('name/2',_,_,ground,_).
share_special_builtin('num/1',_,_,ground,_).
share_special_builtin('number/1',_,_,ground,_).
share_special_builtin('numbervars/3',_,_,ground,_).
share_special_builtin('nl/1',_,_,ground,_).
share_special_builtin('open/3',_,_,ground,_).
share_special_builtin('op/3',_,_,ground,_).
share_special_builtin('prolog_flag/2',_,_,ground,_).
share_special_builtin('prolog_flag/3',_,_,ground,_).
share_special_builtin('put_code/1',_,_,ground,_).
share_special_builtin('put_code/2',_,_,ground,_).
share_special_builtin('statistics/2',_,_,ground,_).
share_special_builtin('seeing/1',_,_,ground,_).
share_special_builtin('see/1',_,_,ground,_).
share_special_builtin('telling/1',_,_,ground,_).
share_special_builtin('tell/1',_,_,ground,_).
share_special_builtin('tab/1',_,_,ground,_).
share_special_builtin('tab/2',_,_,ground,_).
share_special_builtin('ttyput/1',_,_,ground,_).
share_special_builtin('save_event_trace/1',_,_,ground,_).
share_special_builtin('=:=/2',_,_,ground,_).
share_special_builtin('>=/2',_,_,ground,_).
share_special_builtin('>/2',_,_,ground,_).
share_special_builtin('</2',_,_,ground,_).
share_special_builtin('=</2',_,_,ground,_).
% SICStus3 (ISO)
share_special_builtin('=\\=/2',_,_,ground,_).
% SICStus2.x
% share_special_builtin('=\=/2',_,_,ground,_).
%-------------------------------------------------------------------------
share_special_builtin('abort/0',_,_,bottom,_).
share_special_builtin('fail/0',_,_,bottom,_).
share_special_builtin('false/0',_,_,bottom,_).
share_special_builtin('halt/0',_,_,bottom,_).
%-------------------------------------------------------------------------
share_special_builtin('!/0',_,_,unchanged,_).
share_special_builtin('assert/1',_,_,unchanged,_).
share_special_builtin('asserta/1',_,_,unchanged,_).
share_special_builtin('assertz/1',_,_,unchanged,_).
share_special_builtin('debug/0',_,_,unchanged,_).
share_special_builtin('debugging/0',_,_,unchanged,_).
share_special_builtin('dif/2',_,_,unchanged,_).
share_special_builtin('display/1',_,_,unchanged,_).
share_special_builtin('flush_output/0',_,_,unchanged,_).
share_special_builtin('garbage_collect/0',_,_,unchanged,_).
share_special_builtin('gc/0',_,_,unchanged,_).
share_special_builtin('listing/0',_,_,unchanged,_).
share_special_builtin('listing/1',_,_,unchanged,_).
share_special_builtin('nl/0',_,_,unchanged,_).
share_special_builtin('nogc/0',_,_,unchanged,_).
share_special_builtin('nonvar/1',_,_,unchanged,_). % needed?
share_special_builtin('not_free/1',_,_,unchanged,_).
share_special_builtin('not/1',_,_,unchanged,_).
share_special_builtin('print/1',_,_,unchanged,_).
share_special_builtin('repeat/0',_,_,unchanged,_).
share_special_builtin('start_event_trace/0',_,_,unchanged,_).
share_special_builtin('stop_event_trace/0',_,_,unchanged,_).
share_special_builtin('true/0',_,_,unchanged,_).
share_special_builtin('ttyflush/0',_,_,unchanged,_).
share_special_builtin('otherwise/0',_,_,unchanged,_).
share_special_builtin('seen/0',_,_,unchanged,_).
share_special_builtin('told/0',_,_,unchanged,_).
share_special_builtin('ttynl/0',_,_,unchanged,_).
share_special_builtin('write/1',_,_,unchanged,_).
share_special_builtin('writeq/1',_,_,unchanged,_).
% SICStus3 (ISO)
%meta! (no need) share_special_builtin('\\+/1',_,_,unchanged,_).
share_special_builtin('\\==/2',_,_,unchanged,_).
% SICStus2.x
% share_special_builtin('\+/1',_,_,unchanged,_).
% share_special_builtin('\==/2',_,_,unchanged,_).
share_special_builtin('@>=/2',_,_,unchanged,_).
share_special_builtin('@=</2',_,_,unchanged,_).
share_special_builtin('@>/2',_,_,unchanged,_).
share_special_builtin('@</2',_,_,unchanged,_).
%-------------------------------------------------------------------------
share_special_builtin('assert/2',assert(_,Z),_,some,Vars):-
    varset(Z,Vars).
share_special_builtin('asserta/2',asserta(_,Z),_,some,Vars):-
    varset(Z,Vars).
share_special_builtin('assertz/2',assertz(_,Z),_,some,Vars):-
    varset(Z,Vars).
share_special_builtin('compare/3',compare(X,_,_),_,some,Vars):-
    varset(X,Vars).
share_special_builtin('format/2',format(X,_Y),_,some,Vars):-
    varset(X,Vars).
share_special_builtin('format/3',format(X,Y,_Z),_,some,List):-
    varset([X,Y],List).
share_special_builtin('functor/3',functor(_X,Y,Z),_,some,List):-
    varset([Y,Z],List).
share_special_builtin('length/2',length(_X,Y),_,some,[Y]).
share_special_builtin('print/2',print(X,_Y),_,some,Vars):-
    varset(X,Vars).
share_special_builtin('recorda/3',recorda(_,_,Z),_,some,Vars):-
    varset(Z,Vars).
share_special_builtin('recordz/3',recordz(_,_,Z),_,some,Vars):-
    varset(Z,Vars).
share_special_builtin('write/2',write(X,_Y),_,some,Vars):-
    varset(X,Vars).
%-------------------------------------------------------------------------
share_special_builtin('=../2','=..'(X,Y),_,'=../2',p(X,Y)).
share_special_builtin('==/2','=='(X,Y),_,'==/2',p(X,Y)).
share_special_builtin('copy_term/2',copy_term(X,Y),_,copy_term,p(X,Y)).
%meta! (but needs special extension)
share_special_builtin('findall/3',findall(X,_,Z),_,findall,p(X,Z)).
share_special_builtin('indep/2',indep(X,Y),_,'indep/2',p(X,Y)).
share_special_builtin('indep/1',indep(X),_,'indep/1',p(X)).
share_special_builtin('recorded/3',recorded(_,Y,Z),_,'recorded/3',p(Y,Z)).
share_special_builtin('retract/1',retract(X),_,'recorded/3',p(X,b)).
share_special_builtin('retractall/1',retractall(X),_,'recorded/3',p(X,b)).
share_special_builtin('read/1',read(X),_,'recorded/3',p(X,b)).
share_special_builtin('read/2',read(X,Y),_,'recorded/3',p(Y,X)).
share_special_builtin('var/1',var(X),_,var,p(X)). % needed?
share_special_builtin('free/1',var(X),_,var,p(X)).
%%%%%%%%%% others
share_special_builtin(Key,_Goal,_,special(Key),[]):-
    share_not_that_special_builtin(Key).

share_not_that_special_builtin('=/2').
share_not_that_special_builtin('C/3').
share_not_that_special_builtin('arg/3').
share_not_that_special_builtin('keysort/2').
share_not_that_special_builtin('sort/2').

%-------------------------------------------------------------------------
% share_success_builtin(+,+,+,+,+,-)                                     |
% share_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                       |
% Obtains the success for some particular builtins:                      |
%  * If Type = ground, it updates Call making all vars in Sv_u ground    |
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%-------------------------------------------------------------------------

:- export(share_success_builtin/6).
share_success_builtin(ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    ord_split_lists_from_list(Sv,Call,_Intersect,Succ).
share_success_builtin(bottom,_,_,_,_,'$bottom').
share_success_builtin(unchanged,_,_,_,Call,Call).
share_success_builtin(some,_,NewGround,_,Call,Succ):-
    ord_split_lists_from_list(NewGround,Call,_Intersect,Succ).
%
share_success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
    varset(X,Varsx),
    projected_gvars(Call,Varsx,Vars),Vars == Varsx,!,
    varset(Y,Varsy),
    ord_split_lists_from_list(Varsy,Call,_Intersect,Succ).
share_success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
    nonvar(Y),
    Y = [Z|W],
    varset(W,Varsy),
    projected_gvars(Call,Varsy,Vars),Vars == Varsy,!,
    varset((X,Z),Varsx),
    ord_split_lists_from_list(Varsx,Call,_Intersect,Succ).
share_success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
    var(X), var(Y),!,
    sort(Sv_u,Sv),
    share_extend(not_provided_Sg,[Sv],Sv,Call,Succ).
share_success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
%%      ( var(Y) ; Y = [_|_] ), !,
%%      ( var(X) -> Term=[g|X] ; X=..Term ),
    ( var(Y) -> G=g ; Y = [G|_] ), !,
    ( var(X) -> Term=[G|X] ; X=..Term ),
    sort(Sv_u,Sv),
    share_project(not_provided_Sg,Sv,not_provided_HvFv_u,Call,Proj),
    share_call_to_success_builtin('=/2','='(Term,Y),Sv,Call,Proj,Succ).
share_success_builtin('=../2',_Sv_u,_,_,_Call,'$bottom').
share_success_builtin('==/2',Sv_u,p(X,Y),_,Call,Succ):-
    sh_peel(X,Y,Binds-[]),
    sort(Sv_u,Sv),
    projected_gvars(Call,Sv,Ground),
    share_make_reduction(Binds,Call,Ground,NewGround,Sets-[]),
    sort(NewGround,NewGround1),
    sort_list_of_lists(Sets,Sets1),
    ord_split_lists_from_list(NewGround1,Call,_Intersect,Temp),
    ord_subtract(Temp,Sets1,Succ).
share_success_builtin(copy_term,_Sv_u,p(X,Y),_,Call,Succ):-
    varset(X,VarsX),
    share_project(not_provided_Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    sort_list_of_lists(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    share_project(not_provided_Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    merge(ProjectedY,ProjectedNewX,TempProjected),
    merge(ProjectedNewX,Call,TempCall),
    share_call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                            TempCall,TempProjected,Temp_success),
    merge_list_of_lists(Call,VarsCall),
    share_project(not_provided_Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
share_success_builtin(findall,_Sv_u,p(X,Z),HvFv_u,Call,Succ):-
    varset(X,Varsx),
    projected_gvars(Call,Varsx,Vars),Vars == Varsx,!,
    varset(Z,Varsz),
    share_success_builtin(ground,Varsz,_any,HvFv_u,Call,Succ).
share_success_builtin(findall,_Sv_u,_,_,Call,Call).
share_success_builtin('indep/2',_Sv,p(X,Y),_,Call,Succ):-
    varset(X,Xv),
    varset(Y,Yv),
    eliminate_couples(Call,Xv,Yv,Succ).
share_success_builtin('indep/2',_Sv,_Condvars,_,_Call,'$bottom').
share_success_builtin('indep/1',_Sv,p(X),_,Call,Succ):- 
    nonvar(X),
    handle_each_indep(X,share,Call,Succ), !.
share_success_builtin('indep/1',_,_,_,_,'$bottom').
share_success_builtin('recorded/3',Sv_u,p(Y,Z),_,Call,Succ):-
    varset(Z,Varsz),
    ord_split_lists_from_list(Varsz,Call,_,ASub),
    varset(Y,Varsy),
    share_project(not_provided_Sg,Varsy,not_provided_HvFv_u,ASub,ASub1),
    closure_under_union(ASub1,Prime),
    sort(Sv_u,Sv),
    share_extend(not_provided_Sg,Prime,Sv,Call,Succ).
share_success_builtin(var,_Sv,p(X),_,Call,Succ):-
    var(X),
    ord_member_list_of_lists(X,Call),!,
    Succ = Call.
share_success_builtin(var,_Sv,_Condvars,_,_Call,'$bottom').

%-------------------------------------------------------------------------
% share_call_to_success_builtin(+,+,+,+,+,-)                             %
% share_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)              %
% Handles those builtins for which computing Prime is easier than Succ   %
%-------------------------------------------------------------------------

:- export(share_call_to_success_builtin/6).
share_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    share_call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
share_call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom').
share_call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
    share_call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
share_call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    share_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
share_call_to_success_builtin('expand_term/2',expand_term(X,Y),Sv,Call,Proj,Succ):- 
    share_call_to_success_builtin('arg/3',arg(1,Y,X),Sv,Call,Proj,Succ).
share_call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
    share_call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
share_call_to_success_builtin('arg/3',arg(X,Y,Z),_,Call,Proj,Succ):- 
    varset(X,OldG),
    ord_split_lists_from_list(OldG,Call,_Intersect,TempCall),
    Sg = p(Y,Z),
    varset(Sg,Sv),
    share_project(not_provided_Sg,Sv,not_provided_HvFv_u,TempCall,Proj),
    ( var(Y)
    -> sh_any_arg_var(Sg,Sv,TempCall,Proj,Succ)
     ; functor(Y,_,N),
       ( N=0 -> Succ = '$bottom'
       ; sh_any_arg_all_args(N,Y,Z,TempCall,Proj,Succs),
         share_compute_lub(Succs,Succ)
       )
    ).

sh_any_arg_var(Sg,Sv,TempCall,Proj,Succ):-
    Head = p(f(A,_B),A),
    varset(Head,Hv),
    share_call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempCall,Proj,_Prime,Succ). % TODO: add some ClauseKey?

sh_any_arg_all_args(0,_,_,_Call,_Proj,Succs):- !, Succs=[].
sh_any_arg_all_args(N,Y,Z,Call,Proj0,[Succ|Succs]):-
    arg(N,Y,NY),
    Sg = p(NY,Z),
    varset(Sg,Sv),
    share_project(not_provided_Sg,Sv,not_provided_HvFv_u,Proj0,Proj),
    sh_any_arg_var(Sg,Sv,Call,Proj,Succ),
    N1 is N-1,
    sh_any_arg_all_args(N1,Y,Z,Call,Proj0,Succs).

%-------------------------------------------------------------------------
% It gives the adecuate abstract substitution 
% resulting of the unification of A and B when ==(A,B) was called.
% If neither X nor Term in one binding is ground, since they have to 
% be identicals (==), each set S of the sharing domain have to 
% satisfied that X is an element of S if and only if at least one 
% variable in Term appears also in S. Therefore, each set in which 
% either only X or only variables of Term appear, has to be eliminated.
%-------------------------------------------------------------------------

share_make_reduction([],_,_,[],Y-Y).
share_make_reduction([(X,VarsTerm)|More],Lambda,Ground,NewGround,Eliminate):-
    ord_member(X,Ground), !,
    share_make_reduction(More,Lambda,Ground,NewGround1,Eliminate),
    append(VarsTerm,NewGround1,NewGround).
share_make_reduction([(X,VarsTerm)|More],Lambda,Ground,[X|NewGround],Eliminate):-
    ord_subset(VarsTerm,Ground), !,
    share_make_reduction(More,Lambda,Ground,NewGround,Eliminate).
share_make_reduction([(X,[Y])|More],Lambda,Ground,NewGround,Eliminate):-
    var(Y), !,
    sort([X,Y],Vars),
    eliminate_if_not_possible(Lambda,Vars,Elim1),
    share_make_reduction(More,Lambda,Ground,NewGround,Elim2),
    append_dl(Elim1,Elim2,Eliminate).
share_make_reduction([(X,VarsTerm)|More],Lambda,Ground,NewGround,Eliminate):-
    ord_subtract(VarsTerm,Ground,List),
    eliminate_if_not_possible(Lambda,X,List,Elim1),
    share_make_reduction(More,Lambda,Ground,NewGround,Elim2),
    append_dl(Elim1,Elim2,Eliminate).

