:- module(sharefree_non_var, [], [assertions, isomodes]).

:- doc(title, "sharing+freeness+nonvar (abstract domain)").
% started: 23/7/96
:- doc(author, "Maria Garcia de la Banda").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shfrnv, [default]).

:- use_module(domain(sharefree), [
    special_builtin/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3,
    asub_to_native/5,
    input_interface/4,
    input_user_interface/5,
    project/5,
    abs_sort/2
]).
:- dom_impl(_, project/5, [from(sharefree:shfr), noq]).
:- dom_impl(_, abs_sort/2, [from(sharefree:shfr), noq]).
:- dom_impl(_, special_builtin/5, [from(sharefree:shfr), noq]).
:- dom_impl(_, unknown_call/4, [from(sharefree:shfr), noq]).
:- dom_impl(_, unknown_entry/3, [from(sharefree:shfr), noq]).
:- dom_impl(_, empty_entry/3, [from(sharefree:shfr), noq]).

%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
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

:- use_module(library(sets), 
    [ insert/3, 
      merge/3,
      ord_intersection_diff/4,
      ord_subset/2, 
      ord_subtract/3,
      ord_test_member/3
    ]).
:- use_module(library(terms_vars), [varset/2, varset0/2, varset_in_args/2]).
:- use_module(domain(sharing), [
    less_or_equal/2,
    project/5
]).
:- use_module(domain(sharing), [ % TODO: move to other shared module?
    project_share/3,
    script_p_star/3,
    script_p/3
]).
:- use_module(domain(sharefree), [ % TODO: move to other shared module?
    sh_free_vars_compatible/2,
    project_freeness/3,
    project_freeness_n/3,
    propagate_non_freeness/5,
    make_dependence/5,
    add_environment_vars/3,
    all_terms_identical/2,
    change_values/4,
    change_values_if_f/4,
    change_values_if_not_g/4,
    values_differ/3,
    take_coupled/3,
    prune/4,
    prune/5,
    partition_sf/4,
    update_lambda_non_free/5,
    update_lambda_sf/5,
    split_coupled/4,
    values_equal/3,
    compute_lub_sh/3,
    covering/3,
    eliminate_non_element/4,
    insert_each/3,
    member_value_freeness_differ/3,
    obtain_freeness/2
]).
:- use_module(domain(s_grshfr), 
    [ change_values_if_differ/5,
      change_values_insert/4,
      collect_vars_freeness/2,
      member_value_freeness/3, 
      projected_gvars/3,
      var_value/3
    ]).
:- use_module(library(lists), [list_to_list_of_lists/2]).
:- use_module(library(lsets), 
    [ closure_under_union/2,
      merge_each/3,
      merge_list_of_lists/2, 
      merge_lists/3,
      ord_split_lists/4,
      ord_split_lists_from_list/4,
      powerset_of_set_of_sets/2,
      sort_list_of_lists/2
    ]).
:- use_module(domain(s_eqs), [simplify_equations/3]).
    
:- use_module(domain(share_aux)).

:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,-)
% call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)
%------------------------------------------------------------------------%
% The sharing component is computed as for the shfr domain. The freeness %
% component is also computed as in the shfr except for abs_unify_entry/6 %
% (to take nv into account) and collapse_non_freeness (nf(_,_) is        %
% transformed into nv rather than into nf).                              %
%------------------------------------------------------------------------%

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
    variant(Sg,Head),!,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj)),
    Head = NewTerm,
    sharefree:abs_sort(NewProj,(Temp_sh,Temp_fr)),
    change_values_insert(Fv,Temp_fr,Entry_fr,f),    
    list_to_list_of_lists(Fv,Temp1),
    merge(Temp1,Temp_sh,Entry_sh),
    Entry = (Entry_sh,Entry_fr).
call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
    list_to_list_of_lists(Fv,Entry_sh),
    change_values_insert(Fv,[],Entry_fr,f),
    Entry = (Entry_sh,Entry_fr).
call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,(Proj_sh,Proj_fr),Entry,ExtraInfo):-
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
% collapse_non_freeness(+,-)
% collapse_non_freeness(Fr,NewFr)
%-------------------------------------------------------------------------
% Transform any X/nf(_,_) in Freeness into X/nv.                         |
%-------------------------------------------------------------------------
 
collapse_non_freeness([],[]).
collapse_non_freeness([X/V1|Xs],[X/V|Changed]):- 
    ( V1 = nf(Y,_) ->
        ( Y == X ->
           V = nv
        ;  V = nf)
    ;   V = V1
    ),        
    collapse_non_freeness(Xs,Changed).

%-------------------------------------------------------------------------
% abs_unify_entry(+,+,+,+,-,-,-)
% abs_unify_entry(Fr,Sh,Binds,Hv,NewFr,NewSh,NewBinds)
%-------------------------------------------------------------------------
% Identical, the only difference is in aunify_entry/7             %
%-------------------------------------------------------------------------

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
% aunify_entry(+,+,+,+,-,-,-)
% aunify_entry(Binds,Fr,Sh,Hv,NewFr,NewSh,NewBinds)
%-------------------------------------------------------------------------
% Identical except for the cases in which the binding does not ground    %
% one of the terms (last two clauses, table_from_y_entry and             %
% table_from_term_entry, in which nv has to be taken into account).      %
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
%-------------------------------------------------------------------------
% Identical except for:                                                  %
%  * In the last clause, if both values are not nf, at least one must be % 
%    nv or nf(_,_). Thus, X and Y must be nv rather than nf (although    %
%    the coupled are still nf).                                          %
% *  In table_from_y_entry_f, the case of nv has to be considered, and   %
%    if the value is nf(_,_) and all terms are not identical, X and Y    %
%    must be nv rather than nf.                                          %
%-------------------------------------------------------------------------


table_from_y_entry(f,ValueY,X,Y,Sh,Fr,NewFr):- !,
    table_from_y_entry_f(ValueY,X,Y,Sh,Fr,NewFr).
table_from_y_entry(ValueX,f,X,Y,Sh,Fr,NewFr):- !,
    table_from_y_entry_f(ValueX,Y,X,Sh,Fr,NewFr).
table_from_y_entry(nf(_,Term1),nf(_,Term2),_,_,_,Fr,Fr):-
    Term1 == Term2, !.
table_from_y_entry(ValueX,ValueY,X,Y,Lda_sh,Fr,NewFr):-  
    take_coupled(Lda_sh,[X,Y],Coupled),
    change_values_if_f(Coupled,Fr,TmpFr,nf),
    ( ValueX = nf, ValueY = nf ->
        NewFr = TmpFr 
    ;   sort([X,Y],Vars),
        ( ( ValueX = nv ; ValueY = nv; ValueX = nf(A,_), X == A; ValueY = nf(A,_), Y == A) ->
              change_values(Vars,TmpFr,NewFr,nv)
        ;    change_values_if_f(Vars,TmpFr,NewFr,nf))
    ).

table_from_y_entry_f(f,_X,_Y,_Sh,Fr,Fr).
table_from_y_entry_f(nv,X,_Y,Sh,Fr,NewFr):-
    take_coupled(Sh,[X],Coupled),
    change_values_if_f(Coupled,Fr,TmpFr,nf),
    change_values([X],TmpFr,NewFr,nv).
table_from_y_entry_f(nf,X,_Y,Sh,Fr,NewFr):-
    take_coupled(Sh,[X],Coupled),
    change_values_if_f(Coupled,Fr,NewFr,nf).
table_from_y_entry_f(nf(A,Term),X,Y,Sh,Fr,NewFr):-
    take_coupled(Sh,[X],Coupled),
    split_coupled(Coupled,Fr,FreeCoupled,Terms),
    ( all_terms_identical(Terms,Term) ->
        change_values_if_not_g(FreeCoupled,Fr,TmpFr,nf(A,Term)),
        ( A == Y ->
           change_values([X],TmpFr,NewFr,nf(X,Term))
        ;  NewFr = TmpFr)
    ;   change_values_if_f(Coupled,Fr,TmpFr,nf),
        sort([X,Y],Vars),
        ( A == Y ->
            change_values(Vars,TmpFr,NewFr,nv)
         ;  change_values_if_f(Vars,TmpFr,NewFr,nf))
    ).

%-------------------------------------------------------------------------
% table_from_term_entry(+,+,+,+,+,+,-)
% table_from_term_entry(ValueX,X,Term,Sh,Tv,Fr,NewFr)
%-------------------------------------------------------------------------
% Identical, but X must be nv rather than nf                             %
%-------------------------------------------------------------------------

table_from_term_entry(f,X,Term,Sh,_,Fr,NewFr):- 
    take_coupled(Sh,[X],Coupled),
    split_coupled(Coupled,Fr,FreeCoupled,Terms),
    ( all_terms_identical(Terms,Term) ->
            change_values_if_not_g(FreeCoupled,Fr,NewFr,nf(X,Term))
    ; change_values_if_f(Coupled,Fr,TmpFr,nf),
      change_values([X],TmpFr,NewFr,nv)
    ).
table_from_term_entry(nv,X,_,Sh,Tv,Fr,NewFr) :- 
    take_coupled(Sh,[X|Tv],Coupled),
    change_values_if_f(Coupled,Fr,NewFr,nf).
table_from_term_entry(nf,X,_,Sh,Tv,Fr,NewFr) :- 
    take_coupled(Sh,[X|Tv],Coupled),
    change_values_if_f(Coupled,Fr,TmpFr,nf),
    change_values([X],TmpFr,NewFr,nv).
table_from_term_entry(nf(_,Term1),_,Term,_,_,Fr,Fr) :-
     Term1 == Term, !.
table_from_term_entry(nf(_,_),X,_,Sh,Tv,Fr,NewFr) :-
    take_coupled(Sh,[X|Tv],Coupled),
    change_values_if_f(Coupled,Fr,TmpFr,nf),
    change_values([X],TmpFr,NewFr,nv).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)
%------------------------------------------------------------------------%
% The sharing component is computed as for the shfr domain. The freeness %
% component is also computed as in the shfr except for abs_unify_exit/4  %
% (to take nv into account) and collapse_non_freeness (nf(_,_) is        %
% transformed into nv rather than into nf).                              %
%------------------------------------------------------------------------%

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    sharefree:project(Sg,Hv,not_provided_HvFv_u,Exit,(BPrime_sh,BPrime_fr)),
    copy_term((Head,(BPrime_sh,BPrime_fr)),(NewTerm,NewPrime)),
    Sg = NewTerm,
    sharefree:abs_sort(NewPrime,Prime).  
exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
    list_ground(Sv,Prime_fr),
    Prime = ([],Prime_fr).
exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo = ((Lda_sh,Lda_fr),Binds),
    sharefree:project(Sg,Hv,not_provided_HvFv_u,Exit,(BPrime_sh,BPrime_fr)),
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
% abs_unify_exit(+,+,-,-)
% abs_unify_exit(Fr,Binds,NewFr,NewBinds)
%-------------------------------------------------------------------------
% Again, the only diffrences are in table_from_y_exit and in             %
% table_from_term_exit.                                                  %
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
table_from_y_exit(Valuex,Valuey,X,Y,Fr,Fr1):- 
    sort([X,Y],Sorted),
    ( Valuex = nf, Valuey = nf ->
        change_values(Sorted,Fr,Fr1,nf)
    ;   change_values(Sorted,Fr,Fr1,nv)
    ).


table_from_term_exit(f,X,Term,_,Fr,Fr1):- !,
    change_values([X],Fr,Fr1,nf(X,Term)).
table_from_term_exit(nv,_,_,Tv,Fr,Fr1) :- !,
    change_values_if_f(Tv,Fr,Fr1,nf).
table_from_term_exit(nf,_,_,Tv,Fr,Fr1) :- !,
    change_values_if_f(Tv,Fr,Fr1,nf).
table_from_term_exit(nf(_,Term1),_,Term,_,Fr,NewFr) :-
    Term1 == Term, !,
    NewFr = Fr.
table_from_term_exit(_,X,_,Tv,Fr,Fr1) :- !,
    change_values_if_f(Tv,Fr,TmpFr,nf),
    change_values([X],TmpFr,Fr1,nv).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT LUB
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% compute_lub(+,-)
% compute_lub(ListASub,Lub)
%------------------------------------------------------------------------%
% It computes the lub of a set of Asub. For each two abstract            %
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   %
% (1) merging the Sh1 and Sh2  (identical to compute_lub_sh in shfr)     %
% (2) foreach X/Value1 in Fr1 and X/Value2 in Fr2, X/Value in Fr where   %
%     Value is computed from the lattice   f < nf, g < nv < nf           %
%------------------------------------------------------------------------%

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([X],X):- !.
compute_lub([ASub1,ASub2|Xs],Lub):-
    compute_lub_el(ASub1,ASub2,ASubLub),
    compute_lub([ASubLub|Xs],Lub).

compute_lub_el('$bottom',ASub,ASub):- !.
compute_lub_el((Sh1,Fr1),(Sh2,Fr2),(Lub_sh,Lub_fr)):- !,
    compute_lub_sh(Sh1,Sh2,Lub_sh),
    compute_lub_fr(Fr1,Fr2,Lub_fr).
compute_lub_el(ASub,_,ASub).

compute_lub_fr([],[],[]).
compute_lub_fr([X/Value1|Fr1],[X/Value2|Fr2],[X/Value|Lub]):- 
    lub_val(Value1,Value2,Value),
    compute_lub_fr(Fr1,Fr2,Lub).

lub_val(Value,Value,Value):- !.
lub_val(g,Value2,Value):- !,
    ( Value2 = nv ->
        Value = nv
    ;   Value = nf).
lub_val(nv,Value2,Value):- !,
    ( Value2 = g ->
        Value = nv
    ;   Value = nf).
lub_val(_,_,nf).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Extend
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% extend(+,+,+,+,-)
% extend(Sg,Prime,Sv,Call,Succ)
%------------------------------------------------------------------------%
% Identical except for non_free_vars and member_value_freeness_differ.   %
%------------------------------------------------------------------------%

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
extend(_Sg,(Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),Succ):-
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
    ; member_value_freeness_differ(Prime_fr,NonFree,f),
      propagate_non_freeness(BVarsf,NonFree,Succ_sh,Temp2_fr,Temp3_fr)
    ),
    add_environment_vars(Temp3_fr,Call_fr,Succ_fr),
    Succ = (Succ_sh,Succ_fr), !.

%-------------------------------------------------------------------------
% non_free_vars(+,+,+,-,-)
% non_free_vars(Vars,Fr1,Fr2,Fv,NewFr).
%-------------------------------------------------------------------------
% Identical but variables in Vars which appear in Fr1 with value nv are  %
% also added to NewFr                                                    %
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
    var_value_rest(Fr1,X,New_Fr1,Value),
    non_free_vars(Value,X,Xs,New_Fr1,[Elem|Fr2],BVarsf,NewFr).

non_free_vars1(>,X,Xs,_,[Y/V|Fr1],BVarsf,NewFr):-
    compare(D,X,Y),
    non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).
non_free_vars1(=,X,Xs,V,Fr1,BVarsf,NewFr):-
    (V = nf ; V=nv), !,
    NewFr = [X/V|Rest_temp2],
    non_free_vars2(Xs,Fr1,BVarsf,Rest_temp2).
non_free_vars1(=,X,Xs,_V,Fr1,[X|BVarsf],NewFr):-
    non_free_vars2(Xs,Fr1,BVarsf,NewFr).

non_free_vars2([],_Fr1,[],[]).
non_free_vars2([X|Xs],[Y/V|Fr1],BVarsf,NewFr):-
    compare(D,X,Y),
    non_free_vars1(D,X,Xs,V,Fr1,BVarsf,NewFr).

non_free_vars(f,X,Xs,Fr1,Fr2,[X|BVarsf],NewFr):-
    non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).
non_free_vars(nf,X,Xs,Fr1,Fr2,BVarsf,[X/nf|NewFr]):-
    non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).
non_free_vars(nv,X,Xs,Fr1,Fr2,BVarsf,[X/nv|NewFr]):-
    non_free_vars(Xs,Fr1,Fr2,BVarsf,NewFr).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% var_value_rest(+,+,-,-)
% var_value_rest(Fr,X,NewFr,Value)
%-------------------------------------------------------------------------
% The freeness value of X in Fr is Value                                 |
% NewFr is the result of eliminating all Y/V s.t. Y less equal X.        |
%-------------------------------------------------------------------------

var_value_rest([Y/V|More],X,Rest,Value):-
    compare(D,X,Y),
    var_value_rest_(D,V,More,X,Rest,Value).

var_value_rest_(=,Value,More,_,More,Value).
var_value_rest_(>,_,More,X,Rest,Value):-
    var_value_rest(More,X,Rest,Value).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Identical except for abs_unify_entry, collapse_non_freeness and        %
% extend.
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(_Sg,[],_Head,_K,Sv,Call,_Proj,Prime,Succ) :- 
    Call = (Call_sh,Call_fr),!,
    update_lambda_sf(Sv,Call_fr,Call_sh,Succ_fr,Succ_sh),
    list_ground(Sv,Prime_fr),
    Prime = ([],Prime_fr),
    Succ = (Succ_sh,Succ_fr).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,(Sg_sh,Lda_fr),Prime,Succ) :-
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
    extend(Sg,Prime,Sv,Call,Succ).
%
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%------------------------------------------------------------------------%
% input_user_interface(+,+,-,+,+)
% input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)
%------------------------------------------------------------------------%
% identical but taking non_free into account.                            %
%------------------------------------------------------------------------%

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface((Sh,Fr,Nv0),Qv,(Call_sh,Call_fr),Sg,MaybeCallASub):-
    sharefree:input_user_interface((Sh,Fr),Qv,(Call_sh,Call_fr0),Sg,MaybeCallASub),
    may_be_var(Nv0,Nv),
    sort(Nv,NonVar),
    change_values_insert(NonVar,Call_fr0,Call_fr,nv).

:- dom_impl(_, input_interface/4, [noq]).
input_interface(Info,Kind,(Sh0,Fr0,Nv),(Sh,Fr,Nv)):-
    sharefree:input_interface(Info,Kind,(Sh0,Fr0),(Sh,Fr)), !.
input_interface(not_free(X),perfect,(Sh,Fr,Nv0),(Sh,Fr,Nv)):-
    var(X),
    myinsert(Nv0,X,Nv).

myinsert(Fr0,X,Fr):-
    var(Fr0), !,
    Fr = [X].
myinsert(Fr0,X,Fr):-
    insert(Fr0,X,Fr).

may_be_var(X,X):- ( X=[] ; true ), !.

%% %------------------------------------------------------------------------%
%% % output_interface(+,-)                                             %
%% % output_interface(ASub,Output)                                     %
%% %------------------------------------------------------------------------%
%% % The readible format still close to the internal formal is identical    %
%% % for the Sharing part. The output for Fr is the set of free variables   %
%% %-------------------------------------------------------------------------
%% 
%:- export(output_interface/2).  
%% output_interface(ac('$bottom',Flag),('$bottom',Flag)) :- !.
%% output_interface(ac(d(ACons,Del),Flag),Output) :- 
%%      del_output(ac(Del,Flag),ACons,Output).
%% output_interface(d(ACons,Del),Output) :- 
%%      del_output(Del,ACons,Output).
%% output_interface((Sh,Fr),(Sh,Fr)).
%% output_interface('$bottom','$bottom').
%% output_interface([],[]).
%% output_interface([Succ],OutSucc):- !,
%%      output_interface(Succ,OutSucc).
%% output_interface([Succ|LSucc],[OutSucc|LOutSucc]):-
%%      output_interface(Succ,OutSucc),
%%      output_interface0(LSucc,LOutSucc).
%% 
%% output_interface0([],[]).
%% output_interface0([Succ|LSucc],[OutSucc|LOutSucc]):-
%%      output_interface(Succ,OutSucc),
%%      output_interface0(LSucc,LOutSucc).

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)
% asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)
% The user friendly format consists in extracting the nonfree variables  %
% plus ground and free                                                   %
%------------------------------------------------------------------------%

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native((Sh,Fr),Qv,OutFlag,ASub_user,Comps):-
    sharefree:asub_to_native((Sh,Fr),Qv,OutFlag,ASub_user0,Comps),
    member_value_freeness(Fr,Nv,nv),
    if_not_nil(Nv,not_free(Nv),ASub_user,ASub_user0).

%------------------------------------------------------------------------%
% less_or_equal(+,+)
% less_or_equal(ASub0,ASub1)
%------------------------------------------------------------------------%
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal((Sh0,Fr0),(Sh1,Fr1)):-
    sharing:less_or_equal(Sh0,Sh1),
    member_value_freeness(Fr0,ListFr0,f),
    member_value_freeness(Fr1,ListFr1,f),
    ord_subset(ListFr1,ListFr0),
    member_value_freeness(Fr0,ListNv0,nv),
    member_value_freeness(Fr1,ListNv1,nv),
    ord_subset(ListNv1,ListNv0).

%------------------------------------------------------------------------%

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- dom_impl(_, glb/3, [noq]).
glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

%% %------------------------------------------------------------------------%
%% % more_instantiate(+,+)                                           %
%% % more_instantiate(ASub0,ASub1)                                   %
%% %------------------------------------------------------------------------%
%% % Succeeds if ASub1 is possibly more instantiated or equal to ASub0.     %
%% % WARNING, incomplete since definite dependencies in ASub0 afecting      %
%% % variables which are also free in ASub1, must appear in ASub1           %
%% %------------------------------------------------------------------------%
%% 
%:- export(more_instantiate/2). 
%% more_instantiate((Sh0,Fr0),(Sh1,Fr1)):-
%%         member_value_freeness(Fr0,ListGr0,g),
%%         member_value_freeness(Fr1,ListGr1,g),
%%         ord_subset(ListGr0,ListGr1),
%%         member_value_freeness(Fr0,ListNv0,nv),
%%         member_value_freeness(Fr1,ListNv1,nv),
%%      merge(ListNv1,ListGr1,Inst1),
%%         ord_subset(ListNv0,Inst1),
%%         member_value_freeness(Fr1,ListFr1,f),
%%      merge(ListNv0,ListGr0,Inst0),
%%         ord_intersection(ListFr1,Inst0,[]),
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
% success_builtin(+,+,+,+,+,-)                                    |
% success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                      |
%-------------------------------------------------------------------------
% Identical except for when it says %% CHANGED                           %
%-------------------------------------------------------------------------

:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(new_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    Call = (Lda_sh,Lda_fr),
    update_lambda_sf(Sv,Lda_fr,Lda_sh,Succ_fr,Succ_sh), 
    Succ = (Succ_sh,Succ_fr).
success_builtin(bottom,_,_,_,_,'$bottom').
success_builtin(unchanged,_,_,_,Lda,Lda).
success_builtin(some,_Sv,NewGr,_,Call,Succ):-
    Call = (Call_sh,Call_fr),
    update_lambda_sf(NewGr,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin(old_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(Sv,Call_fr,Call_sh,Succ_fr,Succ_sh),!,
    Succ = (Succ_sh,Succ_fr).
success_builtin(old_ground,_,_,_,_,'$bottom').
success_builtin(old_new_ground,_,(OldG,NewG),_,Call,Succ):-
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin(old_new_ground,_,_,_,_,'$bottom').
success_builtin(all_nonfree,Sv_u,Sg,_,Call,Succ):- !,
    sort(Sv_u,Sv),
    sharefree:project(Sg,Sv,not_provided_HvFv_u,Call,(Proj_sh,Proj_fr)),
    closure_under_union(Proj_sh,Prime_sh),
    change_values_if_f(Sv,Proj_fr,Prime_fr,nf), 
    extend(Sg,(Prime_sh,Prime_fr),Sv,Call,Succ).
success_builtin(arg,_,Sg0,_,Call,Succ):- Sg0=p(X,Y,Z),
    Call = (Call_sh,Call_fr),
    varset(X,OldG),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
    var_value(Temp_fr,Y,Value),
    Value \== f,!,
    Sg = p(Y,Z),
    Head = p(f(A,_B),A),
    varset(Sg,Sv),
    varset(Head,Hv),
    TempASub = (Temp_sh,Temp_fr),
    sharefree:project(Sg,Sv,not_provided_HvFv_u,TempASub,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
success_builtin(arg,_,_,_,_,'$bottom').
success_builtin(exp,_,Sg,_,Call,Succ):-
    Head = p(A,f(A,_B)),
    varset(Sg,Sv),
    varset(Head,Hv),
    sharefree:project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
success_builtin(exp,_,_,_,_,'$bottom').
success_builtin('=../2',_,p(X,Y),_,(Call_sh,Call_fr),Succ):-
    varset(X,Varsx),
    values_equal(Varsx,Call_fr,g),!,
    varset(Y,VarsY),
    update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('=../2',_,p(X,Y),_,(Call_sh,Call_fr),Succ):-
    varset(Y,VarsY),
    values_equal(VarsY,Call_fr,g),!,
    varset(X,VarsX),
    update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('=../2',Sv_uns,p(X,Y),_,Call,Succ):-
    var(X), var(Y),!,
    sort(Sv_uns,Sv),
    Call = (_,Call_fr),
    project_freeness(Sv,Call_fr,[A/Val1,B/Val2]),
    ( obtain_freeness(Val1,Val2) ->
        extend(not_provided_Sg,([Sv],[A/nv,B/nv]),Sv,Call,Succ) %% CHANGED
    ; Succ = '$bottom'
    ).
success_builtin('=../2',Sv_uns,p(X,Y),_,Call,Succ):-
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
          product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr), %% CHANGED
          extend(not_provided_Sg,(Prime_sh,Prime_fr),Sv,Call,Succ)
        )
    ; project_share(Sv,Call_sh,Proj_sh),
      ord_subtract(Sv,[X],VarsY),
      product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr), %% CHANGED
      extend(not_provided_Sg,(Prime_sh,Prime_fr),Sv,Call,Succ)
    ).
success_builtin(read2,Sv_u,Sg,_,(Call_sh,Call_fr),Succ):- Sg=p(X,Y),
    varset(X,Varsx),
    update_lambda_non_free(Varsx,Call_fr,Call_sh,Temp_fr,Temp_sh),
    ( var(Y) ->
      change_values_if_f([Y],Temp_fr,Succ_fr,nf), 
      Succ = (Temp_sh,Succ_fr)
    ; varset(Y,Varsy),
      sharefree:project(Sg,Varsy,not_provided_HvFv_u,(Temp_fr,Temp_sh),(Proj_sh,Prime_fr)),
      closure_under_union(Proj_sh,Prime_sh),
      sort(Sv_u,Sv),
      extend(Sg,(Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),Succ)
    ).
success_builtin(recorded,_,Sg,_,Call,Succ):- Sg=p(Y,Z),
    varset(Z,NewG),
    varset(Y,VarsY),
    merge(NewG,VarsY,Vars),
    sharefree:project(Sg,Vars,not_provided_HvFv_u,Call,(Sh,Fr)),
    update_lambda_sf(NewG,Fr,Sh,TempPrime_fr,TempPrime_sh),
    make_dependence(TempPrime_sh,VarsY,TempPrime_fr,Prime_fr,Prime_sh),
    Prime = (Prime_sh,Prime_fr),
    extend(Sg,Prime,Vars,Call,Succ).
success_builtin(copy_term,_,Sg,_,Call,Succ):- Sg=p(X,Y),
    varset(X,VarsX),
    sharefree:project(Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    sharefree:abs_sort(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    sharefree:project(Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    ProjectedY = (ShY,FrY),
    ProjectedNewX = (ShNewX,FrNewX),
    merge(ShY,ShNewX,TempSh),
    merge(FrY,FrNewX,TempFr),
    Call = (ShCall,FrCall),
    merge(ShNewX,ShCall,TempCallSh),
    merge(FrNewX,FrCall,TempCallFr),
    call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
    collect_vars_freeness(FrCall,VarsCall),
    sharefree:project(Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
success_builtin('current_key/2',_,p(X),_,Call,Succ):-
    varset(X,NewG),
    Call = (Call_sh,Call_fr),
    update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('current_predicate/2',_,p(X,Y),_,Call,Succ):-
    var(Y),!,
    Call = (Call_sh,Call_fr),
    change_values_if_f([Y],Call_fr,Temp_fr,nf), 
    varset(X,NewG),
    update_lambda_sf(NewG,Temp_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('current_predicate/2',_,p(X,_Y),_,Call,Succ):- 
    Call = (Call_sh,Call_fr),
    varset(X,NewG),
    update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin(findall,_,p(X,Z),_,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):-
    varset(X,Xs),
    member_value_freeness(Call_fr,GVars,g),
    ord_subset(Xs,GVars), !,
    varset(Z,Zs),
    update_lambda_sf(Zs,Call_fr,Call_sh,Succ_fr,Succ_sh).
success_builtin(findall,_,_,_,Call,Call).
success_builtin('functor/3',_,p(X,Y,Z),_,Call,Succ):-
    var(X),
    Call = (Call_sh,Call_fr),
    var_value(Call_fr,X,f),!,
    change_values([X],Call_fr,Temp_fr,nv),  %% CHANGED
    varset([Y,Z],OldG),
    ( update_lambda_non_free(OldG,Temp_fr,Call_sh,Succ_fr,Succ_sh) ->
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ).
success_builtin('functor/3',_,p(_X,Y,Z),_,Call,Succ):- 
    Call = (Call_sh,Call_fr),
    varset([Y,Z],NewG),
    update_lambda_sf(NewG,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('name/2',_,p(X,Y),_,Call,Succ):-
    varset(X,OldG),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    varset(Y,NewG),
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('name/2',_,p(X,Y),_,Call,Succ):-
    varset(Y,OldG),
    Call = (Call_sh,Call_fr),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    varset(X,NewG),
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('name/2',_,_,_,_,'$bottom').
success_builtin('nonvar/1',_,p(X),_,Call,Succ):-
    var(X), !,
    Call = (Call_sh,Call_fr),
    var_value(Call_fr,X,Val),
    ( Val = f ->
      Succ = '$bottom'
    ; change_values_if_not_g([X],Call_fr,Succ_fr,nv),
      Succ = (Call_sh,Succ_fr)
    ).
success_builtin('nonvar/1',_,_,_,Call,Call):- !.
success_builtin('not_free/1',_,p(X),_,Call,Succ):-
    success_builtin('nonvar/1',_,p(X),_,Call,Succ).
success_builtin('numbervars/3',_,p(X,Y,Z),_,Call,Succ):-
    Call = (Call_sh,Call_fr),
    varset(Y,OldG),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),!,
    varset(p(X,Z),NewG),
    update_lambda_sf(NewG,Temp_fr,Temp_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('numbervars/3',_,_,_,_,'$bottom').
success_builtin('compare/3',_,p(X),_,Call,Succ):- 
    atom(X),!,
    Succ = Call.
success_builtin('compare/3',_,p(X),_,Call,Succ):- 
    var(X),!,
    Call = (Call_sh,Call_fr),
    update_lambda_sf([X],Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('compare/3',_,_,_,_,'$bottom').
success_builtin('indep/2',_,p(X,Y),_,Call,Succ):- 
    ( ground(X) ; ground(Y) ), !,
    Succ = Call.
success_builtin('indep/2',_,p(X,Y),_,Call,Succ):- 
    varset(X,Xv),
    varset(Y,Yv),
    Call = (Call_sh,Call_fr),
    varset(Call_fr,Vars),
    eliminate_couples(Call_sh,Xv,Yv,Succ_sh),
    projected_gvars(Succ_sh,Vars,Ground),
    change_values_if_differ(Ground,Call_fr,Succ_fr,g,f),!,
    Succ = (Succ_sh,Succ_fr).
success_builtin('indep/2',_,_,_,_,'$bottom').
success_builtin('indep/1',_,p(X),_,Call,Succ):- 
    nonvar(X),
    handle_each_indep(X,shfrnv,Call,Succ), !.
success_builtin('indep/1',_,_,_,_,'$bottom').
success_builtin('length/2',_,p(X,Y),_,Call,Succ):-
    var(X),var(Y),!,
    Call = (_,Call_fr),
    var_value(Call_fr,X,Valuex),
    var_value(Call_fr,Y,Valuey),
    update_from_values(Valuex,Valuey,X,Y,Call,Succ). %% CHANGED
success_builtin('length/2',_,p(X,_Y),_,Call,Succ):-
    var(X),!,
    Call = (Call_sh,Call_fr),
    take_coupled(Call_sh,[X],Coupled),
    change_values_if_f(Coupled,Call_fr,Tmp_fr,nf),
    change_values_if_not_g([X],Tmp_fr,Succ_fr,nv), %% CHANGED
    Succ = (Call_sh,Succ_fr).
success_builtin('length/2',_,p(X,Y),_,Call,Succ):-
    functor(X,'.',_),
    varset0(X,[Z|_]),
    Call = (Call_sh,Call_fr),
    take_coupled(Call_sh,[Z],Coupled),
    change_values_if_f(Coupled,Call_fr,Temp_fr,nf),
    change_values_if_not_g([X],Temp_fr,Temp1_fr,nv),  %% CHANGED
    update_lambda_sf([Y],Temp1_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
success_builtin('var/1',[X],p(X),_,Call,Succ) :-
    var(X),
    Call = (Call_sh,Call_fr),
    var_value(Call_fr,X,Valuex),
    Valuex \== g, Valuex \== nv, %% CHANGED
    (Valuex == f ->
        Succ = Call
    ;
        member_value_freeness(Call_fr,DefinitelyFreeVars,f),
        insert(DefinitelyFreeVars,X,AssumedFree),
        sharing:project(not_provided_Sg,AssumedFree,not_provided_HvFv_u,Call_sh,NewSh),
        sh_free_vars_compatible(NewSh,AssumedFree),
        change_values([X],Call_fr,Succ_fr,f),
        Succ = (Call_sh,Succ_fr)
    ).
success_builtin('var/1',_,_,_,_,'$bottom').
success_builtin('free/1',[X],p(X),_,Call,Succ):-
    success_builtin('var/1',[X],p(X),_,Call,Succ).

%-------------------------------------------------------------------------
% call_to_success_builtin(+,+,+,+,+,-)                              %
% call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)               %
%-------------------------------------------------------------------------

:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin('==/2','=='(X,Y),_Sv,Call,Proj,Succ):-
    var(X),!,
    identical_one_var(X,Y,Call,Proj,Succ).
call_to_success_builtin('==/2','=='(X,Y),_Sv,Call,Proj,Succ):-
    var(Y),!,
    identical_one_var(Y,X,Call,Proj,Succ).
%% call_to_success_builtin('==/2','=='(X,Y),Sv,Call,_Proj,Succ):-
%%      Call = (Call_sh,Call_fr),
%%      free_peel(X,Y,Binds,[]),
%%      extract_ground(Sv,Call_fr,Gv),
%%      make_reduction(Binds,(Call_sh,Call_fr),Gv,Call_fr,Tfr,NewGv,Elim_u-[]),
%%      sort(Elim_u,Elim),
%%      ord_split_lists_from_list(NewGv,Call_sh,_Intersect,Temp_sh),
%%      ord_subtract(Temp_sh,Elim,Succ_sh),
%%      update_freeness(Tfr,Succ_sh,Succ_fr),
%%      non_free_to_ground(Call,(Succ_sh,Succ_fr),Succ).
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr),Succ):-
    varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
    Call = (Call_sh,Call_fr),
    ord_subtract(Sv,VarsX,VarsY),
    update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr),Succ):-
    varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
    Call = (Call_sh,Call_fr),
    ord_subtract(Sv,VarsY,VarsX),
    update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
call_to_success_builtin('=/2','='(X,Y),_Sv,Call,Proj,Succ):-
    var(X),var(Y), !,
    (
        X==Y -> Call=Succ
      ;
        Proj = (_,Proj_fr),
	obtain_prime_var_var(Proj_fr,Call,Succ)
    ).
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
    var(X), !,
    Proj = (Proj_sh,Proj_fr),       
    ord_subtract(Sv,[X],VarsY),
    var_value(Proj_fr,X,ValueX),
    product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
    Prime= (Prime_sh,Prime_fr),
    extend(not_provided_Sg,Prime,Sv,Call,Succ).
call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('=/2',_,_,_call,_,'$bottom').
call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):- !,
    call_to_success_builtin('=/2','='(X,[Y|Z]),Sv,Call,Proj,Succ).
call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):-
    call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ).
call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    var(X), !,
    Proj = (_Sh,Fr),
    var_value(Fr,X,Val),
    ( Val = f ->
      Succ = '$bottom'
    ; varset([X,Y],Sv),
      copy_term(Y,Yterm),
      varset(Yterm,Vars),
      call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),not_provided,Sv,Call,Proj,_Prime,Succ) % TODO: add some ClauseKey?
    ).
call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    functor(X,'.',_), !,
    varset0(X,[Z|_]),
    Call = (Call_sh,Call_fr),
    change_values_if_not_g([Z],Call_fr,Temp_fr,nv),
    varset([X,Y],Sv),
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,
    varset(Xterm,Vars),
    Proj = (Sh,Fr),
    change_values_if_not_g([Z],Fr,TFr,nv),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_sh,Temp_fr),(Sh,TFr),_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('sort/2',_,_,_,_,'$bottom').

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%            Intermediate Functions                                      %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% decide_update_lambda(+,+,+,+,-,-)                               %
% decide_update_lambda(Gv,Fr,Sh,Hv,NewFr,NewSh)                   %
%-------------------------------------------------------------------------
% identical except for change_values_if_f                                %
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
    change_values_if_f(NonFv,Temp_Fr,NewFr,nf).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------

product(f,X,VarsY,_,Sh,Lda_fr,Prime_sh,Prime_fr):-
    project_share(VarsY,Sh,Temp),
    insert_each(Temp,X,Temp1),
    sort_list_of_lists(Temp1,Prime_sh),
    take_coupled(Sh,[X],Coupled),
    change_values_if_f(Coupled,Lda_fr,Tmp_fr,nf),
    change_values([X],Tmp_fr,Prime_fr,nv).
product(nv,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
    project_share(VarsY,Sh,Temp),
    closure_under_union(Temp,Temp1),
    merge_each([X],Temp1,Temp2),
    sort(Temp2,Prime_sh),
    take_coupled(Sh,Sv,Coupled),
    change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
product(nf,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
    project_share(VarsY,Sh,Temp),
    closure_under_union(Temp,Temp1),
    merge_each([X],Temp1,Temp2),
    sort(Temp2,Prime_sh),
    take_coupled(Sh,Sv,Coupled),
    change_values_if_f(Coupled,Lda_fr,Tmp_fr,nf),
    change_values([X],Tmp_fr,Prime_fr,nv).
    
%-------------------------------------------------------------------------
% identical_one_var(+,+,+,+,-)                                    |
% identical_one_var(X,Y,Call,Proj,Succ)                           |
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
% identical(+,+,+,+,+,-)                                          |
% identical(ValueX,ValueY,X,Y,Call,Succ)                          |
%-------------------------------------------------------------------------

identical(g,f,_X,_Y,_Call,'$bottom'):- !.
identical(f,g,_X,_Y,_Call,'$bottom'):- !.
identical(nv,f,_X,_Y,_Call,'$bottom'):- !.
identical(f,nv,_X,_Y,_Call,'$bottom'):- !.
identical(g,g,_X,_Y,Proj,Proj):- !.
identical(ValueX,ValueY,X,Y,Call,Succ):-
    (ValueX=g;ValueY=g),!,
    Call = (Call_sh,Call_fr),
    ( update_lambda_non_free([X,Y],Call_fr,Call_sh,Succ_fr,Succ_sh) ->
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ).
identical(ValueX,ValueY,X,Y,(Call_sh,Call_fr),Succ):- 
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,NonPossibleY,PossibleNonXY),
    ord_split_lists(Intersect,Y,PossibleXY,NonPossibleX),
    varset(p(NonPossibleX,NonPossibleY),Coupled),
    varset(p(PossibleXY,PossibleNonXY),NonCoupled),
    ord_subtract(Coupled,NonCoupled,NewGround),
    ( values_differ(NewGround,Call_fr,f) ->
      merge(PossibleXY,PossibleNonXY,Succ_sh),
      less(ValueX,ValueY,Val),
      sort([X,Y],Vars),
      change_values(Vars,Call_fr,Succ_fr,Val), 
%%%% COMMENT This can introduce inconsistent sharing abstractions
      Succ = (Succ_sh,Succ_fr)
    ; Succ = '$bottom'
    ). 

less(nv,_,nv):- !.
less(_,nv,nv):- !.
less(f,_,f):- !.
less(_,f,f):- !.
less(nf,nf,nf).

%-------------------------------------------------------------------------
% obtain_prime_var_var(+,+,-)                                            |
% obtain_prime_var_var([X/V,Y/V],Call,Success)                           |
%-------------------------------------------------------------------------

obtain_prime_var_var([X/f,Y/f],(Call_sh,Call_fr),Succ):- !,
    ord_split_lists(Call_sh,X,Intersect,Disjoint),
    ord_split_lists(Disjoint,Y,OnlyY,NonXY),
    ord_split_lists(Intersect,Y,XY,OnlyX),
    merge_lists(OnlyY,OnlyX,BothXY),
    merge(XY,NonXY,Succ1),
    merge(BothXY,Succ1,Succ_sh),
    Succ = (Succ_sh,Call_fr).
obtain_prime_var_var([X/VX,Y/VY],Call,Succ):-
    ( (VX=nv; VY=nv) ->
        Prime = ([[X,Y]],[X/nv,Y/nv])
    ;   Prime = ([[X,Y]],[X/nf,Y/nf])),
    extend(not_provided_Sg,Prime,[X,Y],Call,Succ).
 
%% non_free_to_ground((_,Lcall_fr),(Lsucc_sh,Lsucc_fr),(Lsucc_sh,Lsucc_fr)):-
%%      compare_free_to_ground(Lcall_fr,Lsucc_fr), !.
%% non_free_to_ground(_,_,'$bottom').
%% 
%% compare_free_to_ground([],[]).
%% compare_free_to_ground([X/Xf|Xs],[X/Yf|Ys]):-
%%      Xf = f, !,
%%      Yf \== g, Yf \== nv, %% CHNAGED
%%      compare_free_to_ground(Xs,Ys).
%% compare_free_to_ground([_|Xs],[_|Ys]):- !,
%%      compare_free_to_ground(Xs,Ys).

%------------------------------------------------------------------------
% update_from_values(+,+,+,+,+,-)                                |
% update_from_values(ValueX,ValueY,X,Y,Call,Succ)                |
%------------------------------------------------------------------------
% It returns the adecuate values of Success for length(X,Y) when both X |
% and Y are variables. It is based on the freeness values of X and Y.   |
%------------------------------------------------------------------------

update_from_values(g,g,_,_,Proj,Proj):- !.
update_from_values(g,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):-
    update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).
update_from_values(f,g,X,_Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- !,
    take_coupled(Call_sh,[X],Coupled),
    change_values_if_f(Coupled,Call_fr,Tmp_fr,nf),
    change_values([X],Tmp_fr,Succ_fr,nv),
    Succ_sh = Call_sh.
update_from_values(f,f,_X,_Y,_Proj,'$bottom'):- !.
update_from_values(f,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
    update_lambda_non_free([Y],Call_fr,Call_sh,Tmp_fr,Succ_sh),!,
    take_coupled(Succ_sh,[X],Coupled),
    change_values_if_f(Coupled,Tmp_fr,Tmp1_fr,nf),
    change_values([X],Tmp1_fr,Succ_fr,nv).
update_from_values(f,_,_X,_Y,_Proj,'$bottom').
update_from_values(nv,g,_X,_Y,Proj,Proj):- !.
update_from_values(nv,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
    update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).
update_from_values(nf,g,_X,_Y,Proj,Proj):- !.
update_from_values(nf,_,_X,Y,(Call_sh,Call_fr),(Succ_sh,Succ_fr)):- 
    update_lambda_sf([Y],Call_fr,Call_sh,Succ_fr,Succ_sh).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%
% :- dom_impl(_, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(_, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(_, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(_, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_impl(_, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_impl(_, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
% :- dom_impl(_, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub), [from(sharefree:shfr)]).
% :- dom_impl(_, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(_, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
%
%% check_cond(_,_,_,_,_).
%% compute_lub_el(_,_,_).  
%% convex_hull(_,_,_).
%% downwards_closed(_,_,_). 
%% hash(_,_,_).    
%% impose_cond(_,_,_,_).
%% more_instantiate(_,_). 
%% real_conjoin(_,_,_).

%% %%%%%%%%%% ANNOTATION PROCESS
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
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
%                        DELAY PREDICATES
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% Assumptions: programs are normalized.
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% check_cond(+,+,-)
% check_cond(Conds,ACns,Flag)
%-------------------------------------------------------------------------
% Identical, but nonvar variables help in definitely woken (5th clause)  %
%-------------------------------------------------------------------------

%% :- push_prolog_flag(multi_arity_warnings,off).
%% 
%:- export(check_cond/5).
%% check_cond(Conds,(Sh,Fr),Sv,Flag,WConds):-
%%      check_cond(Conds,(Sh,Fr),Sv,[],Flag,[],WConds).
%% 
%% check_cond([],_,_,Acc,Flag,WAcc,WConds):-
%%      ( Acc = [] ->
%%          Flag = d
%%      ; Flag = Acc,
%%        WConds = WAcc).
%% check_cond([(Gr,Nv,Eq)|Rest],ASub,Sv,Acc,Flag,WAcc,WConds):-
%%      ( make_awoken(ASub,Gr,Nv,Eq,Sv,Flag2) -> 
%%          ( Flag2 = w ->
%%              Flag = w,
%%              WConds = [(Gr,Nv,Eq)]
%%          ;   check_cond(Rest,ASub,Sv,[Flag2|Acc],Flag,[(Gr,Nv,Eq)|WAcc],WConds))
%%      ; check_cond(Rest,ASub,Sv,Acc,Flag,WAcc,WConds)).
%% 
%% :- pop_prolog_flag(multi_arity_warnings).
%% 
%% make_awoken((Sh,Fr),Gr,Nv,Eq,Sv,Flag):-
%%      member_value_freeness(Fr,OldGr,g),
%%      ord_subtract(Gr,OldGr,NewGr),
%%      ( NewGr = [] ->
%%          TmpFr = Fr,
%%          NewSh = Sh,
%%          AllGr = OldGr
%%      ; Flag0 = diff,
%%        update_lambda_non_free(NewGr,Fr,Sh,TmpFr,NewSh),
%%        member_value_freeness(TmpFr,AllGr,g)),
%%      member_value_freeness(TmpFr,OldNv,nv),
%%      ord_subtract(Nv,AllGr,TmpNv),
%%      ord_subtract(TmpNv,OldNv,NewNv),
%%      member_value_freeness(TmpFr,Free,f),
%%      ord_intersection(Free,NewNv,[]),
%%      ( mynonvar(NewNv,NewSh,Free) ->
%%          NewFr = TmpFr
%%      ; Flag0 = diff,
%%        change_values(NewNv,TmpFr,NewFr,nv)),
%%      ( var(Flag0) ->
%%          sharefree:check_eq(Eq,AllGr,Free,NewFr,NewSh,Sv,Flag)
%%      ; sharefree:project(not_provided_Sg,Sv,not_provided_HvFv_u,(NewSh,NewFr),Flag)).
%%        
%%      
%% %% check_cond([(Gr,_)|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %%   ord_intersect(Gr,NonGround),!, % definitely delays 
%% %%   check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag).
%% %% check_cond([(_,Nv)|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %%   ord_intersect(Nv,Free),!,      % definitely delays 
%% %%   check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag).
%% %% check_cond([(Gr,Nv)|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %%   ord_subtract(Gr,Ground,PossibleNonG),
%% %%   PossibleNonG \== [],!,         % possibly woken
%% %%   update_lambda_non_free(PossibleNonG,Fr,Sh,TmpFr,SuccSh),
%% %%   change_values_if_not_g(Nv,TmpFr,SuccFr,nv),
%% %%   sharefree:project(not_provided_Sg,Sv,not_provided_HvFv_u,(SuccSh,SuccFr),Proj),
%% %%   Acc0 = [Proj|Acc],
%% %%   check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc0,Flag).
%% %% check_cond([(_,Nv)|_],Free,_,NonVar,_,Sh,_,_,_,Flag):-
%% %%   ord_subtract(Nv,NonVar,PossibleFree),
%% %%   mynonvar(PossibleFree,Sh,Free),!, % definitely woken
%% %%   Flag = w.
%% %% check_cond([_|Rest],Free,Ground,NonVar,NonGround,Sh,Fr,Sv,Acc,Flag):-
%% %%   sharefree:project(not_provided_Sg,Sv,not_provided_HvFv_u,(Sh,Fr),Proj),
%% %%   check_cond(Rest,Free,Ground,NonVar,NonGround,Sh,Fr,Sv,[Proj|Acc],Flag).
%% 
%% %-------------------------------------------------------------------------
%% % downwards_closed(+,+,-)
%% % downwards_closed(ACns1,ACns2,ACns)
%% %-------------------------------------------------------------------------
%% % ACns2 must be more instantiated than ACns1 but some downwards closed
%% % properties might have been lost due to a later lub. Thus, those
%% % properties must be returned to ACns2. Iff something non ground becomes 
%% % ground or something free becomes non-free in ACns2, ACns1 is more 
%% % instantiated than ACns2 and we fail. Otherwise we propagate these
%% %  properties from ACns1 to ACns2.
%% %-------------------------------------------------------------------------
%% 
%:- export(downwards_closed/3). 
%% downwards_closed((_,Fr1),(Sh2,Fr2),(Sh,Fr)):- 
%%      member_value_freeness(Fr1,Gv,g),
%%      collect_vars_freeness(Fr2,Sv),
%%      ord_intersection(Gv,Sv,NewGr),
%%      update_lambda_non_free(NewGr,Fr2,Sh2,TmpFr,Sh),
%%      member_value_freeness(Fr1,Nv,nv),
%%      member_value_freeness(TmpFr,Free,f),
%%      ord_intersection(Free,Nv,[]),
%%         change_values_if_not_g(Nv,TmpFr,Fr,nv).
%%      
%% 
%% %------------------------------------------------------------------------%
%% % hash(+,-)
%% % hash(ASub,N)
%% %------------------------------------------------------------------------%
%% % Returns an atom which identifies ASub
%% %------------------------------------------------------------------------%
%% 
%:- export(hash/3).    
%% hash('$bottom',_,-2).
%% hash(true,_,0).
%% hash((Sh,Fr),Fnv,N):-
%%      \+ \+
%%      (  primes(Primes),
%% %%      collect_vars_freeness(Fr,Vars),
%% %%      append(Vars,_,Primes),
%%         append(Fnv,_,Primes),
%%         hash_fr(Fr,0,N1),
%%         sum_list_of_lists(Sh,N1,N2),
%%         recorda_internal('$hash',N2,_)
%%         ),
%%      recorded_internal('$hash',N,Ref),
%%      erase(Ref).
%% 
%% hash_fr([],N,N).
%% hash_fr([X/V|Rest],N0,N):-
%%      ( V = f ->
%%          N1 is N0+X
%%      ; ( V = g ->
%%          N1 is N0-X 
%%        ; ( V = nv ->
%%            N1 is N0+ (2*X)
%%          ; N1 = N0
%%          )
%%           )
%%         ),
%%      hash_fr(Rest,N1,N).
%% 
%% %------------------------------------------------------------------------%
%% % convex_hull(+,+,-)
%% % convex_hull(Old,New,Hull)
%% %------------------------------------------------------------------------%
%% % Computes the convex hull between the initial abstraction Old and the
%% % more instantiated one New           
%% %------------------------------------------------------------------------%
%% 
%:- export(convex_hull/3).
%% convex_hull((OldSh,OldFr),(_,NewFr),(HullSh,HullFr)):- !,
%%      closure_under_union(OldSh,HullSh),
%%      hull(OldFr,NewFr,HullFr).
%% convex_hull(_,_,'$bottom').
%% 
%% hull([],[],[]).
%% hull([X/V1|OldFr],[Y/V2|NewFr],[X/V|HullFr]):-
%%      X == Y,
%%      hull0(V1,V2,V),
%%      hull(OldFr,NewFr,HullFr).
%%      
%% hull0(nf,_,nf).
%% hull0(g,_,g).
%% hull0(f,f,f):- !.
%% hull0(f,_,nf).
%% hull0(nv,_,nv).
%% 
%% %-------------------------------------------------------------------------
%% % impose_cond(+,+,+,-)
%% % impose_cond(Conds,ACns,Sv,LASub)
%% %-------------------------------------------------------------------------
%% 
%:- export(impose_cond/4).
%% impose_cond([],_,_,[]).
%% impose_cond([(Gr,Nv,_)|Rest],Sv,(Sh,Fr),[ASub1|LASub]):-
%%      update_lambda_sf(Gr,Fr,Sh,Fr1,Sh1),
%%         change_values_if_not_g(Nv,Fr1,Fr2,nv),
%%      sharefree:project(not_provided_Sg,Sv,not_provided_HvFv_u,(Sh1,Fr2),ASub1),
%%      impose_cond(Rest,Sv,(Sh,Fr),LASub).
%% 
%% 
%% %-------------------------------------------------------------------------
%% % real_conjoin(+,+,-)
%% % real_conjoin(ACns1,ACns2,Conj)
%% %-------------------------------------------------------------------------
%% 
%:- export(real_conjoin/3).
%% real_conjoin(_,'$bottom','$bottom'):- !.
%% real_conjoin('$bottom',_,'$bottom').
%% real_conjoin((ShOld,FrOld),(ShNew,FrNew),(Sh,Fr)):-
%%      member_value_freeness(FrNew,Gv,g),
%%      update_lambda_sf(Gv,FrOld,ShOld,TmpFr,Sh0),
%%      member_value_freeness(FrNew,Nv,nv),
%%         change_values_if_not_g(Nv,TmpFr,Fr,nv),
%%         ( (Sh0 == ShNew;all_singletons(ShNew)) ->
%%          Sh = Sh0
%%      ; %write(user,'WARNING: a complete conjunction needed'),
%%        merge(ShNew,Sh0,Sh)).
%% 
%% all_singletons([]).
%% all_singletons([[_]|Rest]):-
%%      all_singletons(Rest).
