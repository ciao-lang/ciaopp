:- module(abs_exec_cond,
    [cond/4,
     not_cond/4,
     indep/4,
     not_independent/4,
     ground/3,
     not_ground/3,
     free/3,
     not_free/3,
     abs_exec_reg_type_with_post_info/4,
     abs_exec_reg_type_with_post_info_one_version/5,
     abs_exec_conj_props/3
    ],
    [assertions, isomodes, datafacts, ciaopp(ciaopp_options)]).

:- doc(title,"Abstract Execution of Conditions").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module, "This module contains the implementation of abstract
   executability of expressions using an abstract substitution.").

:- use_module(spec(abs_exec), [abs_exec/4]).

:- use_module(ciaopp(plai/domains), 
    [ concrete/4, less_or_equal_proj/5, abs_sort/3, project/6,
      identical_abstract/3 ]).
:- use_module(domain(sharing), [share_project/5]).
:- use_module(domain(s_grshfr), 
    [ change_values_if_differ/5, member_value_freeness/3, projected_gvars/3,
        var_value/3 ]).
:- use_module(domain(sharefree), [sh_free_vars_compatible/2]).
     
:- use_module(library(lsets), [ord_split_lists/4]).
:- use_module(library(lists), [member/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sets), [insert/3, ord_subtract/3, ord_member/2, merge/3]).

:- use_module(typeslib(typeslib),
              [ dz_type_included/2, type_intersection_2/3, is_ground_type/1,
                is_empty_type/1]).

:- use_module(ciaopp(infer), [get_memo_lub/5]).

:- use_module(ciaopp(plai/plai_db), [memo_table/6]).
:- use_module(library(sort), [sort/2]).

%-------------------------------------------------------------------%
%             programmed by A.German Puebla Sanchez                 %
%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% cond(+,+,+,+)                                                     %
% cond(Cond,AbsInt,Goal,Info)                                       %
%  Succeeds if Cond holds for Goal with abstract domain AbsInt and the%
%  abstract call substitution Info                                  %
%  All the conditions are reduced to determinable tests:            %
%   ground, indep, nonground, unlinked
%-------------------------------------------------------------------%
cond(true,_,_,_).
cond(type_incl(N,Type),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    type_of(AbsInt,ArgN,Info,T),
    dz_type_included(T,Type).
cond(incomp_type(N,Type),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    type_of(AbsInt,ArgN,Info,T),
    type_intersection_2(T,Type,T3),
    is_empty_type(T3).
%       types_are_incompatible(RealType,T).
cond(notvartype(N),AbsInt,Goal,Info):-
    arg(N,Goal,Var),
    ( var(Var) -> 
      \+ type_of(AbsInt,Var,Info,term)
    ;
        true
    ).
cond(all_ground_types,AbsInt,Goal,Info):-
    varset(Goal,Vars),
    all_ground_with_types(Vars,AbsInt,Info).
cond(one_concr_nequal,AbsInt,A = B,Info):-
    varset(A = B,Vars),
    each_concret_one(Vars,AbsInt,Info,Infoconcr),
    copy_term((A = B,Infoconcr),(A1 = B1,Info2concr)),
    apply(Info2concr),
    A1 \== B1.
cond(one_concr_equal,AbsInt,A = B,Info):-
    varset(A = B,Vars),
    each_concret_one(Vars,AbsInt,Info,Infoconcr),
    copy_term((A = B,Infoconcr),(A1 = B1,Info2concr)),
    apply(Info2concr),
    A1 == B1.
% cond(one_concr_nequal,AbsInt,Goal,Info):-
%       arg(1,Goal,Arg1),
%       arg(2,Goal,Arg2),
%       concrete(AbsInt,Arg1,Info,[One]),
%       concrete(AbsInt,Arg2,Info,[Two]),
%       One \== Two.
cond(ground(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    varset(ArgN,L),
    all_ground(L,AbsInt,Info).
cond(free(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    free(AbsInt,ArgN,Info).
cond(free(N,M),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    arg(M,Goal,ArgM),
    free(AbsInt,ArgN,Info),
    free(AbsInt,ArgM,Info).
cond(indep(_N),AbsInt,Goal,Info):- % IG: in practice N = 1 because it is a list
    varset(Goal,Vars),
    list_indep(AbsInt,Vars,Info).
cond(indep(N,M),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    arg(M,Goal,ArgM),
    indep(AbsInt,ArgN,ArgM,Info).
cond(frgr(N,M),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    arg(M,Goal,ArgM),
    free(AbsInt,ArgN,Info),
    ground(AbsInt,ArgM,Info).
cond(frindep(N,M),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    arg(M,Goal,ArgM),
    free(AbsInt,ArgN,Info),
    free(AbsInt,ArgM,Info),
    indep(AbsInt,ArgN,ArgM,Info).
cond(freerec(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    varset(ArgN,Vars),
    member(Var,Vars),
    free(AbsInt,Var,Info).
%        f_rec(ArgN,AbsInt,Info).
%% GP nonground/3 undefined!
%% cond(nonground(N),AbsInt,Goal,Info):-
%%         arg(N,Goal,ArgN),
%%         nonground(AbsInt,ArgN,Info).
%% GP unlinked/4 undefined!
%% cond(unlinked(N,M),AbsInt,Goal,Info):-
%%      arg(N,Goal,ArgN),
%%         arg(M,Goal,ArgM),
%%      unlinked(AbsInt,ArgN,ArgM,Info).
cond(nonvar(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
%% MGB  nonvar(AbsInt,ArgN,Info).
    not_free(AbsInt,ArgN,Info).
cond(not_indep(N,M),AbsInt,Goal,Info):-
    not_cond(indep(N,M),AbsInt,Goal,Info).
cond(not_ground(N),AbsInt,Goal,Info):-
    not_cond(ground(N),AbsInt,Goal,Info).
cond([Cond|_],AbsInt,Goal,Info):-
    cond(Cond,AbsInt,Goal,Info).
cond([_|Conds],AbsInt,Goal,Info):-
    cond(Conds,AbsInt,Goal,Info).
%jcf
cond(leq(Sg,Proj),AbsInt,Goal,Info):-
    abs_sort(AbsInt,Proj,SortedProj),
    varset(Goal,Gv),
    project(AbsInt,Goal,Gv,_,Info,Entry),
    abs_sort(AbsInt,Entry,SortedEntry),
    less_or_equal_proj(AbsInt,Goal,SortedEntry,Sg,SortedProj).
%jcf
%
:- if(defined(has_ciao_ppl)).
cond(polyhedra_constraint,AbsInt,Goal,Info) :-
    % TODO: REWRITE!!! (e.g, using domain operations)
    AbsInt = polyhedra,
    Info = (_Addr, Vars),
    Goal = 'native_props:constraint'(Cons_Sys),
    polyhedra_input_user_interface(Cons_Sys, Vars, GoalASub, Goal, no), % TODO: check that last 2 args are OK
    polyhedra_less_or_equal(Info, GoalASub).
:- endif.

:- if(defined(has_ciao_ppl)).
% TODO: move above, make it modular, etc.
:- use_module(domain(polyhedra), [
    polyhedra_input_user_interface/5,
    polyhedra_less_or_equal/2
]).
:- endif.

%% %-------------------------------------------------------------------%
%% % f_rec(+,+,+)                                                      %
%% % f_rec(Term,AbsInt,Info)                                           %
%% %  Succeeds if Term has at least one variable that can be shown to  %
%% %  be free                                                          %
%% %-------------------------------------------------------------------%
%% f_rec(Term,AbsInt,Info):-
%%         var(Term),
%%         !,
%%         free(AbsInt,Term,Info).
%% f_rec(Term,AbsInt,Info):-
%%         functor(Term,_,2),
%%         !,
%%         arg(1,Term,Arg1),
%%         arg(2,Term,Arg2),
%%         (f_rec(Arg1,AbsInt,Info)
%%     ;
%%         f_rec(Arg2,AbsInt,Info)).
%% f_rec(Term,AbsInt,Info):-
%%         functor(Term,'-',1),
%%         !,
%%         arg(1,Term,Arg1),
%%         f_rec(Arg1,AbsInt,Info).
%% 
%-------------------------------------------------------------------%
% ground(+,+,+)                                                     %
% ground(AbsInt,X,Info)                                             %
% X is a variable. The predicate suceeds if X is ground w.r.t. Info %
%-------------------------------------------------------------------%
ground(son,X,(GroundComponent,_)):-
    ord_member(X,GroundComponent).
ground(share,X,Sharing):-
    ord_split_lists(Sharing,X,[],_Disjoint).
ground(shfr,X,ac(d((_SharingComponent,FreeComponent),_DelComponent),_)):- !,
    var_value(FreeComponent,X,g).
ground(shfr,X,(_SharingComponent,FreeComponent)):-
    var_value(FreeComponent,X,g).
ground(shfrnv,X,ac(d((_SharingComponent,FreeComponent),_DelComponent),_)):- !,
    var_value(FreeComponent,X,g).
ground(shfrnv,X,(_SharingComponent,FreeComponent)):-
    var_value(FreeComponent,X,g).
ground(gr,X,GrComponent):-
    var_value(GrComponent,X,g).
% GPS These domains are not active yet in 1.0
%% ground(aeq,X,ac(d(aeqs(Eqs,_,_,_,NGr),_DelComponent),_)):- !,
%%      avariables_ic_subst(X,Eqs,X_ic),
%%      bitset_intersect(X_ic,NGr,0) .
%% ground(aeq,X,aeqs(Eqs,_,_,_,NGr)):- !,
%%      avariables_ic_subst(X,Eqs,X_ic),
%%      bitset_intersect(X_ic,NGr,0) .
ground(def,X,a(GroundComponent,_DepComponent)):- !,
    ord_member(X,GroundComponent).
ground(def,X,ac(d(a(GroundComponent,_DepComponent),_DelComponent),_)):- 
    ord_member(X,GroundComponent).
%% ground(shareson,X,((GroundComponent,_),_SharingComponent)):-
%%         ord_member(X,GroundComponent).
%% ground(shfrson,X,((GroundComponent,_),_SharingComponent,_FreeComp)):-
%%         ord_member(X,GroundComponent).
%% ground(fd,X,(_F,D)):-
%%      ground(def,X,D).

all_ground([],_AbsInt,_Info).
all_ground([V|Vs],AbsInt,Info):-
    ground(AbsInt,V,Info),
    all_ground(Vs,AbsInt,Info).

%-------------------------------------------------------------------%
% free(+,+,+)                                                       %
% free(AbsInt,Term,Info)                                            %
%  Term can be shown to be free with AbsInt and Info.               %
%-------------------------------------------------------------------%
free(shfr,X,(_,FreeComponent)):- !,
    var_value(FreeComponent,X,f).
free(shfr,X,ac(d((_,FreeComponent),_DelComponent),_)):-
    var_value(FreeComponent,X,f).
free(shfrnv,X,(_,FreeComponent)):- !,
    var_value(FreeComponent,X,f).
free(shfrnv,X,ac(d((_,FreeComponent),_DelComponent),_)):-
    var_value(FreeComponent,X,f).
%% free(aeq,X,aeqs(Eqs,Ann,_,_,_)):- !,
%%      member_key(X,Eqs,'@'(X_ec)),
%%      aref(X_ec,Ann,f).
%% free(aeq,X,ac(d(aeqs(Eqs,Ann,_,_,_),_DelComponent),_)):- !,
%%      member_key(X,Eqs,'@'(X_ec)),
%%      aref(X_ec,Ann,f).
%% free(shfrson,X,(_,_,FreeComponent)):-
%%         var_value(FreeComponent,X,f).
%% free(fr,X,as(Old,New)):-
%%         ord_split_lists(Old,X,[],_DisjointO),
%%         ord_split_lists(New,X,[],_DisjointN).
%% free(fd,X,(_D,as(_G1,Old,_G2,New))):-
%%      free(fr,X,as(Old,New)).
%% 
%-------------------------------------------------------------------%
% indep(+,+,+,+)                                                    %
% indep(AbsInt,Term1,Term2,Info)                                    %
%  Term1 and Term2 can be shown to be independent from each other   %
%-------------------------------------------------------------------%
indep(son,X,Y,(_,DepComponent)):-
    sort([X,Y],Couple),
    \+ord_member(Couple,DepComponent).
indep(share,X,Y,Sharing):-
    ord_split_lists(Sharing,X,IntersectX,_DisjointX),
    ord_split_lists(IntersectX,Y,[],_DisjointY).
indep(shfr,X,Y,(SharingComponent,_)):-
    ord_split_lists(SharingComponent,X,IntersectX,_DisjointX),
    ord_split_lists(IntersectX,Y,[],_DisjointY).
indep(shfr,X,Y,ac(d((SharingComponent,_),_DelComponent),_)):-
    % TODO: old functors of shfr asub???
    ord_split_lists(SharingComponent,X,IntersectX,_DisjointX),
    ord_split_lists(IntersectX,Y,[],_DisjointY).
indep(shareson,X,Y,((_,DepComponent),_)):-
    sort([X,Y],Couple),
    \+ord_member(Couple,DepComponent).
indep(shfrson,X,Y,((_,DepComponent),_,_)):-
    sort([X,Y],Couple),
    \+ord_member(Couple,DepComponent).
indep(fr,X,_,as(Old,New)):-
    ord_split_lists(Old,X,[],_DisjointO),
    ord_split_lists(New,X,[],_DisjointN), !.
indep(fr,_,X,as(Old,New)):-
    ord_split_lists(Old,X,[],_DisjointO),
    ord_split_lists(New,X,[],_DisjointN).
indep(fd,X,Y,(_D,as(_G1,Old,_G2,New))):-
    indep(fr,X,Y,as(Old,New)).

%-------------------------------------------------------------------%
% indep(+,+,+)                                                      %
% indep(AbsInt,Vars,Info)                                           %
%  Vars can be shown to be independent from each other              %
%-------------------------------------------------------------------%
list_indep(shfr, Vars, (SharingAsub,_)) :-
    %%%% the variables in are in different sharing sets.
    all_in_different_sharing_sets(Vars,SharingAsub).

% TODO: PERFORMANCE!, can we take advantage of ordering to reduce the number of
% checks?
% all_in_different_sharing_sets(+,+).
all_in_different_sharing_sets([_V], _Sharing) :- !.
all_in_different_sharing_sets([V0|Vs], Sharing) :-
    ord_split_lists(Sharing, V0, V0SharingSets, _Disjoint),
    vs_not_in_sharing_sets(Vs,V0SharingSets),
    all_in_different_sharing_sets(Vs, Sharing).

vs_not_in_sharing_sets([],_SharingSets).
vs_not_in_sharing_sets([V|Vs],SharingSets) :-
    ord_split_lists(SharingSets,V,[],_Disjoint),
    vs_not_in_sharing_sets(Vs,SharingSets).

%% %-------------------------------------------------------------------%
%% % nonvar(+,+,+)                                                     %
%% % nonvar(AbsInt,Term,Info)                                          %
%% %  Term can be shown not to be nonvar with AbsInt and Info.         %
%% %-------------------------------------------------------------------%
%% nonvar(shfrnv,X,ac(d((_SharingComponent,FreeComponent),_DelComponent),_)):- !,
%%         var_value(FreeComponent,X,nv).
%% nonvar(shfrnv,X,(_SharingComponent,FreeComponent)):-
%%         var_value(FreeComponent,X,nv).

%-------------------------------------------------------------------%
% not_ground(+,+,+)                                                 %
% not_ground(AbsInt,Term,Info)                                      %
%  Term can be shown not to be ground with AbsInt and Info.         %
%-------------------------------------------------------------------%
not_ground(shfr,X,(SharingComponent,FreeComponent)):-
    var_value(FreeComponent,X,Value),
    test_not_ground(Value,X,(SharingComponent,FreeComponent)).
not_ground(shfr,X,ac(d((SharingComponent,FreeComponent),_DelComponent),_)):-
    var_value(FreeComponent,X,Value),
    test_not_ground(Value,X,(SharingComponent,FreeComponent)).
not_ground(shfrnv,X,(SharingComponent,FreeComponent)):-
    var_value(FreeComponent,X,Value),
    test_not_ground(Value,X,(SharingComponent,FreeComponent)).
not_ground(shfrnv,X,ac(d((SharingComponent,FreeComponent),_DelComponent),_)):-
    var_value(FreeComponent,X,Value),
    test_not_ground(Value,X,(SharingComponent,FreeComponent)).
%% not_ground(aeq,X,AEqs):- 
%%      AEqs = aeqs(Eqs,_,_,_,_),!,
%%      member_key(X,Eqs,ATerm),
%%      get_ann_aterm(AEqs,ATerm,AnnT),
%%      ann_non_ground(AnnT).
%% not_ground(aeq,X,ac(d(AEqs,_DelComponent),_)):-
%%      AEqs = aeqs(Eqs,_,_,_,_),!,
%%      member_key(X,Eqs,ATerm),
%%      get_ann_aterm(AEqs,ATerm,AnnT),
%%      ann_non_ground(AnnT).
%% not_ground(shfrson,X,(_Son,SharingComponent,FreeComponent)):-   
%%         not_ground(shfr,X,(SharingComponent,FreeComponent)).
%% not_ground(fr,X,as(Old,New)):-
%%      ord_test_member(Old,[X],no),
%%      ord_test_member(New,[X],no).
%% not_ground(fd,X,(_D,as(_G1,Old,_G2,New))):-
%%      not_ground(fr,X,as(Old,New)).

test_not_ground(f,_,_):-!.
test_not_ground(_,X,(SharingComponent,FreeComponent)):-
    ord_split_lists(SharingComponent,X,Intersect,L1),
    varset(Intersect,Coupled),
    varset(L1,Not_Coupled),
    ord_subtract(Coupled,Not_Coupled,New_Ground),
    \+change_values_if_differ(New_Ground,FreeComponent,_,g,f).
 
%-------------------------------------------------------------------%
% not_free(+,+,+)                                                   %
% not_free(AbsInt,Term,Info)                                        %
%  Term can be shown not to be free with AbsInt and Info.           %
%-------------------------------------------------------------------%
not_free(def,X,a(G,_)):- !,
    ord_member(X,G).
not_free(def,X,ac(d(a(G,_),_),_)):- 
    ord_member(X,G).
not_free(son,X,(GroundComponent,_)):-
    ord_member(X,GroundComponent).
not_free(share,X,Sharing):-
    ord_split_lists(Sharing,X,[],_Disjoint).
not_free(shfr,X,(SharingComponent,FreeComponent)):-
    var_value(FreeComponent,X,Value),
    test_not_free(Value,X,(SharingComponent,FreeComponent)).
not_free(shfr,X,ac(d((SharingComponent,FreeComponent),_DelComponent),_)):-
    var_value(FreeComponent,X,Value),
    test_not_free(Value,X,(SharingComponent,FreeComponent)).
not_free(shfrnv,X,(SharingComponent,FreeComponent)):-
    var_value(FreeComponent,X,Value),
    test_not_free(Value,X,(SharingComponent,FreeComponent)).
not_free(shfrnv,X,ac(d((SharingComponent,FreeComponent),_DelComponent),_)):-
    var_value(FreeComponent,X,Value),
    test_not_free(Value,X,(SharingComponent,FreeComponent)).
%% not_free(aeq,X,AEqs):- 
%%      AEqs = aeqs(Eqs,_,_,_,_),!,
%%      member_key(X,Eqs,ATerm),
%%      get_ann_aterm(AEqs,ATerm,AnnT),
%%      ann_non_free(AnnT).
%% not_free(aeq,X,ac(d(AEqs,_DelComponent),_)):-
%%      AEqs = aeqs(Eqs,_,_,_,_),!,
%%      member_key(X,Eqs,ATerm),
%%      get_ann_aterm(AEqs,ATerm,AnnT),
%%      ann_non_free(AnnT).
%% not_free(shareson,X,((GroundComponent,_),_SharingC)):-
%%         ord_member(X,GroundComponent).
%% not_free(shfrson,X,(_Son,SharingComponent,FreeComponent)):-
%%         not_free(shfr,X,(SharingComponent,FreeComponent)).

test_not_free(g,_,_).
test_not_free(nv,_,_).
test_not_free(nf,X,(SharingComponent,FreeComponent)):-
    member_value_freeness(FreeComponent,FreeVars,f),
    insert(FreeVars,X,AssumedFree),
    share_project(not_provided_Sg,AssumedFree,not_provided_HvFv_u,SharingComponent,NewSh),
    \+ sh_free_vars_compatible(NewSh,AssumedFree).

%-------------------------------------------------------------------%
% not_independent(+,+,+,+)                                          %
% not_independent(AbsInt,Term1,Term2,Info)                             %
%  Term1 and Term2 can be shown to be not independent               %
%-------------------------------------------------------------------%
not_independent(shfr,X,Y,(SharingComponent,FreeComponent)):-
    ord_split_lists(SharingComponent,X,IntersectX,DisjointX),
    ord_split_lists(IntersectX,Y,IntersectXY,DisjointY),
    IntersectXY \== [],
    varset(FreeComponent,Vars),
    merge(DisjointX,DisjointY,NewSh),
    projected_gvars(NewSh,Vars,Ground),
    \+ change_values_if_differ(Ground,FreeComponent,_Succ_fr,g,f).
not_independent(shfr,X,Y,ac(d((SharingComponent,FreeComponent),_DelComponent),_)):-
    ord_split_lists(SharingComponent,X,IntersectX,DisjointX),
    ord_split_lists(IntersectX,Y,IntersectXY,DisjointY),
    IntersectXY \== [],
    varset(FreeComponent,Vars),
    merge(DisjointX,DisjointY,NewSh),
    projected_gvars(NewSh,Vars,Ground),
    \+ change_values_if_differ(Ground,FreeComponent,_Succ_fr,g,f).

not_independent(shfrson,X,Y,(_Son,SharingComponent,FreeComponent)):-
    not_independent(shfr,X,Y,(SharingComponent,FreeComponent)).

%-------------------------------------------------------------------%
% not_cond(+,+,+,+)                                                 %
% not_cond(Cond,AbsInt,Goal,Info)                                   %
%  Cond can be shown not to hold for Goal with abstract domain AbsInt%
%  and abstract call substitution Info                              %
%-------------------------------------------------------------------%
not_cond([L|R],AbsInt,Goal,Info):-
    not_cond(L,AbsInt,Goal,Info),
    not_cond(R,AbsInt,Goal,Info).
not_cond(type_incl(N,Type),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    type_of(AbsInt,ArgN,Info,T),
    type_intersection_2(T,Type,T3),
    is_empty_type(T3).
%       types_are_incompatible(T,Type).
not_cond(incomp_type(N,Type),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    type_of(AbsInt,ArgN,Info,T),
    dz_type_included(T,Type).
not_cond(ground(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    varset(ArgN,Variables),
    member(Var,Variables),
    not_ground(AbsInt,Var,Info).
not_cond(free(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    not_free(AbsInt,ArgN,Info).
not_cond(freerec(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    ground(AbsInt,ArgN,Info).
not_cond(frgr(N,M),AbsInt,Goal,Info):-
    cond(AbsInt,free(N),Goal,Info),
    cond(AbsInt,free(M),Goal,Info).
not_cond(frgr(N,M),AbsInt,Goal,Info):-
    cond(AbsInt,ground(N),Goal,Info),
    cond(AbsInt,ground(M),Goal,Info).
not_cond(free(N,_),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    not_free(AbsInt,ArgN,Info).
not_cond(free(_,N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    not_free(AbsInt,ArgN,Info).
not_cond(frindep(N,_),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    not_free(AbsInt,ArgN,Info).
not_cond(frindep(_,N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    not_free(AbsInt,ArgN,Info).
not_cond(frindep(N,M),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    arg(M,Goal,ArgM),
    not_independent(AbsInt,ArgN,ArgM,Info).
not_cond(indep(N,M),shfr,Goal,Info):-
    arg(N,Goal,ArgN),
    arg(M,Goal,ArgM),
    not_independent(shfr,ArgN,ArgM,Info).
not_cond(not_indep(N,M),shfr,Goal,Info):-
    cond(indep(N,M),shfr,Goal,Info).
not_cond(nonvar(N),AbsInt,Goal,Info):-
    arg(N,Goal,ArgN),
    free(AbsInt,ArgN,Info).

all_ground_with_types([],_,_).
all_ground_with_types([Var|Vars],AbsInt,Info):- 
    type_of(AbsInt,Var,Info,T),
    is_ground_type(T),
    all_ground_with_types(Vars,AbsInt,Info).

type_of(eterms,X,Sust,T):-
    member(Y:(_N,T),Sust),
    X == Y,!.
type_of(etermsvar,X,Sust,T):-
    member(Y:(_N,T),Sust),
    X == Y,!.
type_of(svterms,X,(Sust,_),T):-
    member(Y:(_N,T),Sust),
    X == Y,!.
type_of(evalterms,X,Sust,T):-
    member(Y:(_N,T),Sust),
    X == Y,!.
type_of(ptypes,X,Sust,T):-
    member(Y:T,Sust),
    X == Y,!.
type_of(terms,X,Sust,T):-
    member(Y:T,Sust),
    X == Y,!.

each_concret_one([],_AbsInt,_Info,[]).
each_concret_one([Var|Vars],AbsInt,Info,[Var:A|InfoConcr]):-
    concrete(AbsInt,Var,Info,C),
    C = [A],
    each_concret_one(Vars,AbsInt,Info,InfoConcr).

apply([X:Term|ASub]):-
    X=Term,
    apply(ASub).
apply([]).

:- pred abs_exec_reg_type_with_post_info(K_Pre,K_Post,AbsInt,Sense) 
   # "This predicate allows abstractly executing a literal which is assumed to
   be a call to the regular type. This can be doen even if the literal contains
   functors, i.e., it does not need to be normalized. The implementation is
   surprinsingly simple and efficient. This implementation is correct assuming
   type analysis will always return bottom if the partial instantation in the
   literal is incompatible with the regular type which is being called at that
   program point. With that assumption, the literal can be abstractly executable
   to true iff the abstract substitutions before (@var{K_Pre}) and after the
   literal (@var{K_Post}) are identical. Also, the literal is abstractly
   executable to false iff the abstract substitution in @var{K_Post} is bottom.
   The only problem with this implementation is that it requires both the pre
   and post analysis information for the literal}".

abs_exec_reg_type_with_post_info(K_Pre,K_Post,AbsInt,Sense):-
    get_memo_lub(K_Post,Vars,AbsInt,yes,Info1),
    (Info1 == '$bottom' ->
        Sense = fail
    ;
        get_memo_lub(K_Pre,Vars,AbsInt,yes,Info0),
        identical_abstract(AbsInt,Info0,Info1),
        Sense = true
    ).

:- pred abs_exec_reg_type_with_post_info_one_version(Num,K_Pre,K_Post,AbsInt,Sense)
   # "This predicate is very similar to
   @pred{abs_exec_reg_type_with_post_info/4} but only the information which
   corresponds to one version of analysis, identified by @var{Num} is considered
   instead of the lub of all existing analysis versions for the literal. This is
   needed in multi variant specialization is to be performed.".

abs_exec_reg_type_with_post_info_one_version(Num,K_Pre,K_Post,AbsInt,Sense):-
    current_fact(memo_table(K_Post,AbsInt,Num,_,Vars,[Info_Post_u])),
    (Info_Post_u == '$bottom' ->
        Sense = fail
    ;
        current_fact(memo_table(K_Pre,AbsInt,Num,_,Vars,[Info_Pre_u])),
        abs_sort(AbsInt,Info_Post_u, Info_Post),
        abs_sort(AbsInt,Info_Pre_u, Info_Pre),
        identical_abstract(AbsInt,Info_Pre,Info_Post),
        Sense = true
    ).

:- pred abs_exec_conj_props(+Conj,+AbsInt,+Info)
   # "This predicate succeeds if it can prove that the conjuntion of
     properties represented by the list @var{Conj} is @em{true} in the
     context of @var{Info}, which is an abstract substitution in the
     abstract domain @var{AbsInt}.".

abs_exec_conj_props([],_,_).
abs_exec_conj_props([Prop|Props],AbsInt,Info):-
    abs_exec_prop(Prop,AbsInt,Info),
    abs_exec_conj_props(Props,AbsInt,Info).

abs_exec_prop(Prop,AbsInt,Info):-
    functor(Prop,F,A),
    abs_exec(AbsInt,F/A,true,Condition),
    cond(Condition,AbsInt,Prop,Info).
