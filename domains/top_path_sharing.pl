:- module(top_path_sharing, [], [assertions, modes_extra]).

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 10 May 1994                          %
%        programmers: F. Bueno and M. Garcia de la Banda                 %
%                                                                        %
%------------------------------------------------------------------------%
/*             Copyright (C)1990-94 UPM-CLIP                            */

%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
% ASub   : abstract substitution. It is a set of sets, each element      %
%          being a set of elements with the form p(X,Path)               %
%          Path is a list                                                %
%------------------------------------------------------------------------%

:- doc(title, "path (abstract domain)").
:- doc(stability, devel).

:- doc(bug,"Don't know how to do a topmost. This affects correctness
    of unknown_entry/3, unknown_call/4, and input_interface/4.").
:- doc(bug,"Don't know how to treat different paths, e.g.: A=f(_),
    A=g(_,_). This is related to the topmost (how many paths does A have?)
    and affects correctness of compute_lub.").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(path, [default]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(domain(s_eqs), [keys_and_values/3, simplify_equations/3]).
:- use_module(domain(share_aux), [if_not_nil/4]).
%
:- use_module(library(idlists), [memberchk/2, subtract/3]).
:- use_module(library(keys), [key_lookup/4]).
:- use_module(library(lists), [append/3, list_to_list_of_lists/2, reverse/2]).
:- use_module(library(lsets), 
    [ merge_list_of_lists/2, ord_split_lists_from_list/4,
      sort_list_of_lists/2, transitive_closure_lists/3
    ]).
:- use_module(library(sets), 
    [ insert/3, merge/3, ord_subtract/3, ord_union_symdiff/4 ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(io_basic)).

depth_k(K):- current_pp_flag(depth,K).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(_, init_abstract_domain/1, [noq]).
init_abstract_domain([variants,multi_success]) :-
    push_pp_flag(variants,off),
    push_pp_flag(multi_success,on).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,-)                                       %
% call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)                 %
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
    variant(Sg,Head),!,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    sort_list_of_lists(NewProj_u,NewProj),
    list_to_free_abstraction(Fv,Free),
    merge(Free,NewProj,Entry).
call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
    list_to_free_abstraction(Fv,Entry).
call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
    simplify_equations(Sg,Head,Binds),
    list_to_free_abstraction(Hv,TmpASub),
    merge(TmpASub,Proj,NewProj),
    mge(Binds,NewProj,TotalASub),
%       project(Sg,Hv,not_provided_HvFv_u,TotalASub,TmpEntry),
    project(Sg,Hv,not_provided_HvFv_u,TotalASub,TmpEntry0),
    path_transitive_closure(TmpEntry0,TmpEntry_u),
    sort_list_of_lists(TmpEntry_u,TmpEntry),
    list_to_free_abstraction(Fv,TmpFv),
    merge(TmpFv,TmpEntry,Entry),
    ExtraInfo = (Binds,TotalASub).

list_to_free_abstraction([],[]).
list_to_free_abstraction([X|Fv],[[p(X,[])]|Free]):-
    list_to_free_abstraction(Fv,Free).

path_transitive_closure([],[]):- !.
path_transitive_closure(ASub0,ASub):-
    merge_list_of_lists(ASub0,List),
    list_to_list_of_lists(List,Singletons),
    transitive_closure_lists(ASub0,Singletons,ASub).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)                                           %
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                      %
% It computes the prime abstract substitution Prime, i.e.  the result of %
% going from the abstract substitution over the head variables (Exit), to%
% the abstract substitution over the variables in the subgoal. It will:  %
% * If Exit is '$bottom', Prime will be also '$bottom'.                  %
% * If Flag = yes (Head and Sg identical up to renaming) it is just a    %
%   question of renaming Exit                                            %
% * If Hv = [], Prime = []                                               %
% * Otherwise:                                                           %
%      * we merge Exit and TotalASub(the absstract substitution after    %
%        the head unification)                                           %
%      * then call mge/3 with the bindings obtained in call_to_entry     %
%      * project over Sv obtaining Prime                                 %
%------------------------------------------------------------------------%
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    sort_list_of_lists(NewPrime,Prime).     
exit_to_prime(_Sg,[],_Head,_Sv,_Exit,_ExtraInfo,Prime):- !,
    Prime = [].
exit_to_prime(Sg,Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo = (_Binds,TotalASub),
    varset(Exit,NonGrExit),
    ord_subtract(Hv,NonGrExit,NewGr),
    ord_split_paths_from_list(NewGr,TotalASub,_,Disjoint),          
    extend(Sg,Exit,Hv,Disjoint,TmpPrime),
    project(Sg,Sv,not_provided_HvFv_u,TmpPrime,Prime).
%% 
%% 
%%      merge(Disjoint,Exit,TmpASub),
%%      mge(Binds,TmpASub,TmpPrime),
%%      project(Sg,Sv,not_provided_HvFv_u,TmpPrime,Prime).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Extend
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% extend(+,+,+,+,-)                                                      %
% extend(Sg,Prime,Sv,Call,Succ)                                          %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ.             %
%------------------------------------------------------------------------%
:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
extend(_Sg,Prime,Sv,Call,Succ):-
    depth_k(K),
%       depth_k(K0), K is K0+1,
    ord_split_paths_from_list(Sv,Call,Int,Disjoint),        
    scale_all(Prime,K,Int,[],TmpSucc_u,[]),
    sort_list_of_lists(TmpSucc_u,TmpSucc),
    occ_mge(Prime,TmpSucc,TmpSucc1,[]),
    merge(Disjoint,TmpSucc1,Succ).

occ_mge([],_Tmp,Tail,Tail) :- !.
occ_mge(_Tmp,[],Tail,Tail):- !.
occ_mge([Occ|Prime],Tmp,[Merged|Succ],Tail):-
    ord_split_lists_from_list(Occ,Tmp,Int,_),
    merge_list_of_lists(Int,Merged),
    occ_mge(Prime,Tmp,Succ,Tail).

scale_all([],_K,_Int,_,Tail,Tail).
scale_all([Occ|Prime],K,Int,Already,TmpSucc,Tail):-
    ord_subtract(Occ,Already,Rest),
    scale_each_occ(Rest,K,Int,TmpSucc,NewTail),
    merge(Rest,Already,NewAlready),
    scale_all(Prime,K,Int,NewAlready,NewTail,Tail).

scale_each_occ([],_K,_Int,Tail,Tail).
scale_each_occ([p(X,P)|Occ],K,Int,Succ,Tail):-
    scale_each_var(Int,X,P,K,Succ,NewTail),
    scale_each_occ(Occ,K,Int,NewTail,Tail).

scale_each_var([],_X,_P,_K,Tail,Tail).
scale_each_var([Occ|Int],X,P,K,ASub,Tail):-
    is_prefix(Occ,X,P,Su),!,
    path_add_suffix(Occ,Su,K,NewOcc),
    ASub = [NewOcc|NewASub],
    scale_each_var(Int,X,P,K,NewASub,Tail).
scale_each_var([_Occ|Int],X,P,K,ASub,Tail):-
    scale_each_var(Int,X,P,K,ASub,Tail).

:- push_prolog_flag(multi_arity_warnings,off).

is_prefix([p(Y,PY)|Occ],X,P,Su):-
    compare(Order,Y,X),
    is_prefix(Order,Y,PY,Occ,X,P,Su).

is_prefix(=,_Y,PY,_Occ,_X,P,Su):-
    top_suffix(PY,Su,P).
is_prefix(<,_,_,[p(Y,PY)|Occ],X,P,Su):-
    compare(Order,Y,X),
    is_prefix(Order,Y,PY,Occ,X,P,Su).

:- pop_prolog_flag(multi_arity_warnings).

path_add_suffix([],_Su,_K,[]).
path_add_suffix([p(X,P)|Occ],Su,K,[p(X,PSu)|NewOcc]):-
    append_depth(P,Su,K,PSu),
    path_add_suffix(Occ,Su,K,NewOcc).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% project(+,+,+,+,-)                                                     %
% project(Sg,Vars,HvFv_u,ASub,Proj)                                      %
%------------------------------------------------------------------------%
:- dom_impl(_, project/5, [noq]).
project(_,_,_,'$bottom',Proj):- !,
    Proj = '$bottom'.
project(_Sg,[],_HvFv_u,_ASub,[]):- !.
project(_Sg,Vars,_HvFv_u,ASub,Entry):-
    project1(ASub,Vars,TmpEntry),
    sort(TmpEntry,Entry).

project1([],_Vars,[]).
project1([Xs|ASub],Vars,Entry):-
    restrict(Xs,Vars,Set),
    decide_project(Set,Entry,NewEntry),
    project1(ASub,Vars,NewEntry).

decide_project([],Entry,Entry):- !.
decide_project(Set,[Set|Entry],Entry).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT SORT
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% abs_sort(+,-)                                                          %
% abs_sort(Asub_u,Asub)                                                  %
% Sorts the set of sets of elements in ASub_u yielding ASub.             %
%-------------------------------------------------------------------------

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom'):- !.
abs_sort(ASub_u,ASub):-
    sort_list_of_lists(ASub_u,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT LUB                                      %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% path_compute_lub(+,-)                                                  %
% path_compute_lub(ListASub,Lub)                                         %
% It computes the lub of a set of ASub. Since it is just set union, as   %
% in share, it calls share_compute_lub/2.                                %
%-------------------------------------------------------------------------

:- dom_impl(_, compute_lub/2, [noq]).
% TODO: doesn't work!
%% compute_lub(ListASub,Lub):-
%%      share_compute_lub(ListASub,Lub).
compute_lub([],[]).
compute_lub([ASub|ListASub],Lub):-
    compute_lub_(ASub,Lub,Lub0),
    compute_lub(ListASub,Lub0).

compute_lub_('$bottom',Lub,Lub):- !.
compute_lub_(ASub,[ASub|Lub],Lub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------
:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom') :- !.
call_to_success_fact(_Sg,[],_Head,_K,Sv,Call,_Proj,Prime,Succ) :- !,
    ord_split_paths_from_list(Sv,Call,_,Succ),
    Prime = [].
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ) :-
    simplify_equations(Sg,Head,Binds),
    list_to_free_abstraction(Hv,TmpASub),
    merge(TmpASub,Proj,NewProj),
    mge(Binds,NewProj,TmpSucc),
    varset(Call,Vars),
%       project(Sg,Vars,not_provided_HvFv_u,TmpSucc,Succ),
    project(Sg,Vars,not_provided_HvFv_u,TmpSucc,Succ0),
    path_transitive_closure(Succ0,Succ),
    project(Sg,Sv,not_provided_HvFv_u,Succ,Prime).

%-------------------------------------------------------------------------
% unknown_call(+,+,+,-)                                                  |
% unknown_call(Sg,Qv,Call,Succ)                                          |
%-------------------------------------------------------------------------
% This is clearly wrong!!!!

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,_Qv,Call,Call).

%-------------------------------------------------------------------------
% unknown_entry(+,+,-)                                                   |
% unknown_entry(Sg,Qv,Call)                                              |
%-------------------------------------------------------------------------
% This is clearly wrong!!!!

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Qv,Call):-
    list_to_free_abstraction(Qv,Call).

%-------------------------------------------------------------------------
% empty_entry(+,+,-)                                                     |
% empty_entry(Sg,Qv,Call)                                                |
%-------------------------------------------------------------------------
:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(_Sg,Qv,Call):-
    list_to_free_abstraction(Qv,Call).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      USER INTERFACE
%-------------------------------------------------------------------------

%------------------------------------------------------------------------%
% input_user_interface(+,+,-,+,+)                                        %
% input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)               %
% Obtaining the abstract substitution for Path from the user supplied    %
% information                                                            %
%------------------------------------------------------------------------%
% For now, only either ground or free variables are accepted
% should use sharing, and do a topmost for the rest of Qv

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface((_Sh,Fr),_Qv,Call,_Sg,_MaybeCallASub):-
    may_be_var(Fr),
    list_to_free_abstraction(Fr,Call).

%% input_interface(Info,Kind,(Sh0,Fr),(Sh,Fr)):-
%%      share_input_interface(Info,Kind,Sh0,Sh), !.
:- dom_impl(_, input_interface/4, [noq]).
input_interface(free(X),perfect,(Sh,Fr0),(Sh,Fr)):-
    var(X),
    myinsert(Fr0,X,Fr).

myinsert(Fr0,X,Fr):-
    var(Fr0), !,
    Fr = [X].
myinsert(Fr0,X,Fr):-
    insert(Fr0,X,Fr).

may_be_var(X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)                                              %
% asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                        %
%------------------------------------------------------------------------%

:- dom_impl(_, asub_to_native/5, [noq]).
%% asub_to_native('$bottom',_Qv,_OutFlag,[],[]):- !.
%% asub_to_native(ASub,_Qv,_OutFlag,ASub,[]).
%
asub_to_native(ASub,Qv,_OutFlag,ASub_user,[]):-
    path_vars(ASub,NonGv,[]),
    subtract(Qv,NonGv,Gv),
    member_value_path(ASub,Fv,[]),
    keys_and_values(NonGv,_Values,Eqs),
    path_asub_to_share(ASub,Eqs,ShSets,Any_u,[]),
    varset(ShSets,RealVars),
    varset(Eqs,AllVars),
    ord_subtract(AllVars,RealVars,FakeVars),
    sort(Any_u,AnyVars),
    ord_subtract(RealVars,AnyVars,Free),
    eqs_to_univ(Eqs,Univ),
    append(Univ,Info,ASub_user),
    if_not_nil(ShSets,sharing(ShSets),Info,Info0),
    if_not_nil(FakeVars,ground(FakeVars),Info0,Info1),
    if_not_nil(Free,free(Free),Info1,Info2),
    if_not_nil(Gv,ground(Gv),Info2,Info3),
    if_not_nil(Fv,free(Fv),Info3,[]).

% TODO: Missing cuts
path_vars([P|Ps],Vars,Tail):-
    P=[_|_],
    path_vars(P,Vars,Vars0),
    path_vars(Ps,Vars0,Tail).
path_vars([[]|Ps],Vars,Tail):-
    path_vars(Ps,Vars,Tail).
path_vars([p(V,_)|Ps],[V|Vars],Tail):-
    path_vars(Ps,Vars,Tail).
path_vars([],Vars,Vars).

path_asub_to_share([Set|Sets],Eqs,[ShSet|ShSets],Any,Tail):-
    path_asub_to_set(Set,Eqs,ShSet,Any,Any0),
    path_asub_to_share(Sets,Eqs,ShSets,Any0,Tail).
path_asub_to_share([],_Eqs,[],Any,Any).

path_asub_to_set([p(X,Path)|ATerms],Eqs,[V|Vs],Any,Tail):-
    key_lookup(X,Eqs,Term,_),
    do_path(Path,Term,V,Any,Any0),
    path_asub_to_set(ATerms,Eqs,Vs,Any0,Tail).
path_asub_to_set([],_Eqs,[],Any,Any).

do_path([P|Path],Term,V,Any,Tail):-
    pos_of_term(P,Term,Pos,Any,Any0),
    do_path(Path,Pos,V,Any0,Tail).
do_path([],V,V,Any,Any).

:- push_prolog_flag(multi_arity_warnings,off).

pos_of_term(top,Var,Var,[Var|Any],Any):- !.
pos_of_term(P,Term,Pos,Any,Any):-
    pos_of_term(P,1,Term,Pos).

pos_of_term(N,N,[P|_],P):- !.
pos_of_term(N,N1,[_|Term],Pos):-
    N2 is N1+1,
    pos_of_term(N,N2,Term,Pos).

:- pop_prolog_flag(multi_arity_warnings).

eqs_to_univ([X=Y|Eqs],[X=..Y|Univ]):-
    eqs_to_univ(Eqs,Univ).
eqs_to_univ([],[]).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                                     %
% less_or_equal(ASub0,ASub1)                                             %
%------------------------------------------------------------------------%

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal(ASub,ASub):-
    throw(unimplemented(path_less_or_equal/2)).

%------------------------------------------------------------------------%

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- dom_impl(_, glb/3, [noq]).
glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% special_builtin(+,+,+,-,-)                                             |
% special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                        |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) new_ground if the builtin makes all variables ground whithout      |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) old_ground if the builtin requires the variables to be ground      |
% (3) old_new_ground if the builtin requires some variables to be        |
%     ground and grounds the rest                                        |
% (4) unchanged if we cannot infer anything from the builtin, the        |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previous freeness values of the variables.                  |
% (5) some if it makes some variables ground without imposing conditions |
% (6) all_nonfree if the builtin makes all variables possible non free   |
% (6) Sgkey, special handling of some particular builtins                |
%-------------------------------------------------------------------------

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin('CHOICE IDIOM/1',_,_,new_ground,_).
special_builtin('$metachoice/1',_,_,new_ground,_).
special_builtin('current_atom/1',_,_,new_ground,_).
special_builtin('current_input/1',_,_,new_ground,_).
special_builtin('current_module/1',_,_,new_ground,_).
special_builtin('current_output/1',_,_,new_ground,_).
special_builtin('current_op/3',_,_,new_ground,_).
special_builtin('depth/1',_,_,new_ground,_).
special_builtin('get_code/1',_,_,new_ground,_).
special_builtin('get1_code/1',_,_,new_ground,_).
special_builtin('seeing/1',_,_,new_ground,_).
special_builtin('telling/1',_,_,new_ground,_).
special_builtin('statistics/2',_,_,new_ground,_).
special_builtin(':/2',(prolog:'$metachoice'(_)),_,new_ground,_).
%
special_builtin('CUT IDIOM/1',_,_,old_ground,_).
special_builtin('$metacut/1',_,_,old_ground,_).
special_builtin(':/2',(prolog:'$metacut'(_)),_,old_ground,_).
special_builtin('op/3',_,_,old_ground,_).
special_builtin('save_event_trace/1',_,_,old_ground,_).
special_builtin('close/1',_,_,old_ground,_).
%
special_builtin('atom/1',_,_,old_ground,_).
special_builtin('atomic/1',_,_,old_ground,_).
special_builtin('ensure_loaded/1',_,_,old_ground,_).
special_builtin('erase/1',_,_,old_ground,_).
special_builtin('float/1',_,_,old_ground,_).
special_builtin('flush_output/1',_,_,old_ground,_).
special_builtin('integer/1',_,_,old_ground,_).
special_builtin('number/1',_,_,old_ground,_).
special_builtin('nl/1',_,_,old_ground,_).
special_builtin('put_code/1',_,_,old_ground,_).
special_builtin('put_code/2',_,_,old_ground,_).
special_builtin('see/1',_,_,old_ground,_).
special_builtin('tell/1',_,_,old_ground,_).
special_builtin('tab/1',_,_,old_ground,_).
special_builtin('tab/2',_,_,old_ground,_).
special_builtin('ttyput/1',_,_,old_ground,_).
special_builtin('=:=/2',_,_,old_ground,_).
special_builtin('>=/2',_,_,old_ground,_).
special_builtin('>/2',_,_,old_ground,_).
special_builtin('</2',_,_,old_ground,_).
special_builtin('=</2',_,_,old_ground,_).
% SICStus3 (ISO)
special_builtin('=\\=/2',_,_,old_ground,_).
% SICStus2.x
% special_builtin('=\=/2',_,_,old_ground,_).
special_builtin('ground/1',_,_,old_ground,_).
%
special_builtin('absolute_file_name/2',absolute_file_name(X,Y),
                                       _,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('get_code/2',get_code(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('get1_code/2',get1_code(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('is/2',is(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,NewG),
    varset(Y,OldG).
special_builtin('open/3',open(X,Y,Z),_,old_new_ground,(OldG,NewG)):-
    varset(p(X,Y),OldG),
    varset(Z,NewG).
special_builtin('format/2',format(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
special_builtin('format/3',format(X,Y,_Z),_,old_new_ground,(OldG,[])):-
    varset(p(X,Y),OldG).
special_builtin('predicate_property/2',predicate_property(_X,Y),
                                               _,old_new_ground,([],NewG)):-
    varset(Y,NewG).
special_builtin('print/2',print(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
special_builtin('prolog_flag/2',prolog_flag(X,Y),_,old_new_ground,
                                                           (OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('prolog_flag/3',prolog_flag(X,Y,Z),_,old_new_ground,
                                                           (OldG,NewG)):-
    varset(X,OldG),
    varset(f(Y,Z),NewG).
special_builtin('write/2',write(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
%
special_builtin('abort/0',_,_,bottom,_).
special_builtin('fail/0',_,_,bottom,_).
special_builtin('false/0',_,_,bottom,_).
special_builtin('halt/0',_,_,bottom,_).
%
special_builtin('!/0',_,_,unchanged,_).
special_builtin('assert/1',_,_,unchanged,_).
special_builtin('asserta/1',_,_,unchanged,_).
special_builtin('assertz/1',_,_,unchanged,_).
special_builtin('debug/0',_,_,unchanged,_).
special_builtin('debugging/0',_,_,unchanged,_).
special_builtin('dif/2',_,_,unchanged,_).
special_builtin('display/1',_,_,unchanged,_).
special_builtin('garbage_collect/0',_,_,unchanged,_).
special_builtin('gc/0',_,_,unchanged,_).
special_builtin('listing/0',_,_,unchanged,_).
special_builtin('listing/1',_,_,unchanged,_).
special_builtin('nl/0',_,_,unchanged,_).
special_builtin('nogc/0',_,_,unchanged,_).
special_builtin('not/1',_,_,unchanged,_).
special_builtin('print/1',_,_,unchanged,_).
special_builtin('repeat/0',_,_,unchanged,_).
special_builtin('start_event_trace/0',_,_,unchanged,_).
special_builtin('stop_event_trace/0',_,_,unchanged,_).
special_builtin('seen/0',_,_,unchanged,_).
special_builtin('told/0',_,_,unchanged,_).
special_builtin('true/0',_,_,unchanged,_).
special_builtin('ttyflush/0',_,_,unchanged,_).
special_builtin('otherwise/0',_,_,unchanged,_).
special_builtin('ttynl/0',_,_,unchanged,_).
special_builtin('write/1',_,_,unchanged,_).
special_builtin('writeq/1',_,_,unchanged,_).
% SICStus3 (ISO)
special_builtin('\\+/1',_,_,unchanged,_).
% SICStus2.x
% special_builtin('\+/1',_,_,unchanged,_).
% this may not be correct!!!!!!!!
% SICStus3 (ISO)
special_builtin('\\==/2',_,_,unchanged,_).
% SICStus2.x
% special_builtin('\==/2',_,_,unchanged,_).
special_builtin('@>=/2',_,_,unchanged,_).
special_builtin('@=</2',_,_,unchanged,_).
special_builtin('@>/2',_,_,unchanged,_).
special_builtin('@</2',_,_,unchanged,_).
%
special_builtin('assert/2',assert(_X,Y),_,some,Vars):-
    varset(Y,Vars).
special_builtin('assertz/2',assertz(_X,Y),_,some,Vars):-
    varset(Y,Vars).
special_builtin('asserta/2',asserta(_X,Y),_,some,Vars):-
    varset(Y,Vars).
special_builtin('recorda/3',recorda(_X,_Y,Z),_,some,Vars):-
    varset(Z,Vars).
special_builtin('recordz/3',recordz(_X,_Y,Z),_,some,Vars):-
    varset(Z,Vars).
%
special_builtin('=/2','='(X,Y),_,'=/2',p(X,Y)).

%-------------------------------------------------------------------------
% success_builtin(+,+,+,+,+,-)                                           %
% success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                      %
% Obtains the success for some particular builtins:                      %
%  * If Type = new_ground, it updates Call making all vars in Sv_u ground%
%  * If Type = bottom, Succ = '$bottom'                                  %
%  * If Type = unchanged, Succ = Call                                    %
%  * If Type = some, it updates Call making all vars in Condv ground     %
%  * If Type = old_ground, if grouds all variables in Sv and checks that %
%              no free variables has becomed ground                      %
%  * If Type = old_new_ground, if grounds all variables in OldG and      |
%              cchecks that no free variables has becomed ground. If so, |
%              it grounds all variables in NewG                          |
%-------------------------------------------------------------------------

:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(new_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    ord_split_paths_from_list(Sv,Call,_,Succ).
success_builtin(bottom,_,_,_,_,'$bottom').
success_builtin(unchanged,_,_,_,ASub,ASub).
success_builtin(some,_Sv,NewGr,_,Call,Succ):-
    ord_split_paths_from_list(NewGr,Call,_,Succ).
success_builtin(old_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    can_be_ground(Call,Sv),!,
    ord_split_paths_from_list(Sv,Call,_,Succ).
success_builtin(old_ground,_,_,_,_,'$bottom').
success_builtin(old_new_ground,_,(OldG,NewG),_,Call,Succ):-
    can_be_ground(Call,OldG),!,
    merge(OldG,NewG,Vars),
    ord_split_paths_from_list(Vars,Call,_,Succ).
success_builtin(old_new_ground,_,_,_,_,'$bottom').
%
success_builtin('=/2',_Sv,p(X,Y),_,Call,Succ):-
    simplify_equations(X,Y,Binds),
%       mge(Binds,Call,Succ).
    mge(Binds,Call,Succ0),
    path_transitive_closure(Succ0,Succ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT UNIFICATION                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% mge(+,+,-)                                                             %
% mge(Eqs,ASub0,ASub)                                                    %
% It recursively adds the abstract information contained in each         %
% equation of Eqs to the abstract substitution ASub0, resulting in ASub  %
%------------------------------------------------------------------------%

mge(Eqs,ASub0,ASub):-
    depth_k(K),
%       depth_k(K0), K is K0+1,
    mge_k(Eqs,K,ASub0,ASub).

mge_k([],_K,ASub,ASub).
mge_k([(X,T,VarsT)|Eqs],K,ASub0,ASub):-
    solve(X,T,VarsT,K,ASub0,ASub1),
    mge_k(Eqs,K,ASub1,ASub).

%------------------------------------------------------------------------%
% solve(+,+,+,+,-)                                                       %
% solve(X,T,VarsT,K,ASub0,ASub)                                          %
% It adds the abstract information contained in the equation X = T       %
% to the abstract substitution ASub0, resulting in ASub. Note that X     %
% must be a variable, and T can be any term. VarsT is the set of         %
% variables in T.                                                        %
%------------------------------------------------------------------------%
% Since paths allow to reason about linearity, there is no need of a
% closure here: just replace sh-sets in ASub0 related via X=T with the
% corresponding sh-set relating them. Closure can be done afterwards (see
% call_to_entry)

solve(X,T,VarsT,K,ASub0,ASub):-
    vt([_=T],VT_u,[]),
    sort(VT_u,VT),
    rel([X],ASub0,RelX),
    rel(VarsT,ASub0,RelT),
    ord_union_symdiff(RelX,RelT,Union,Diff),
%       close(X,VT,VarsT,RelX,RelT,Union,K,ASubXT),
    iterate_extend(RelX,RelT,X,VT,K,ASubXT_u,[]),
    sort_list_of_lists(ASubXT_u,ASubXT),
    ord_subtract(ASubXT,Diff,ASubXT_Diff),
    ord_subtract(ASub0,Union,ASub1),
    merge(ASubXT_Diff,ASub1,ASub).

%------------------------------------------------------------------------%
% vt(+,-,?)                                                              %
% vt(Eqs,VT,TailVT)                                                      %
% For each equation X=T in Eqs, it traverses T. For each variable Y in T %
% it obtaines the path P for finding Y in T and adds p(Y,Path) to VT     %
% Example: if T is g(f(Y),Z,f(f(W))), Ps will be                         %
%          VT = [p(Y,[1,1]),p(Z,[2]),p(W,[3,1,1])]                       %
%------------------------------------------------------------------------%

vt([_=T|Eqs],VT,TailVT):-
    peel_set_paths(T,[],VT,NewTailVT),
    vt(Eqs,NewTailVT,TailVT).
vt([],VT,VT).

peel_set_paths(T,P,VT,TailVT):-
    var(T), !,
    reverse(P,Path),
    VT = [p(T,Path)|TailVT].
peel_set_paths(T,_P,VT,TailVT):-
    atomic(T), !,
    VT = TailVT.
peel_set_paths(T,P,VT,TailVT):-
    functor(T,_,A),
    peel_set_arg_paths(1,A,T,P,VT,TailVT).

peel_set_arg_paths(N,A,_T,_P,VT,TailVT):-
    N > A, !,
    VT = TailVT.
peel_set_arg_paths(N,A,T,P,VT,TailVT):-
    arg(N,T,Arg),
    N1 is N+1,
    peel_set_paths(Arg,[N|P],VT,NewTailVT),
    peel_set_arg_paths(N1,A,T,P,NewTailVT,TailVT).

%------------------------------------------------------------------------%
% rel(+,+,-)                                                             %
% rel(Vars,ASub,Rel),                                                    %
% Obtains in Rel all elements in ASub in which there is at least an      %
% element p(X,Path) s.t. X appears in the list of variables Vars         %
%------------------------------------------------------------------------%

rel([],_,[]).
rel([X|Xs],Xss,Int):-
    coupled_paths1(Xss,[X|Xs],Int).

coupled_paths1([],_,[]).
coupled_paths1([Xs|Xss],Ys,Int):-
    appears(Xs,Ys,Flag),
    decide_appears(Flag,Xs,Int,Int1),
    coupled_paths1(Xss,Ys,Int1).

decide_appears(yes,L,[L|Intersect],Intersect).
decide_appears(no,_L,Intersect,Intersect).

:- push_prolog_flag(multi_arity_warnings,off).

appears([p(X,P)|Xs],[Y|Ys],Flag):- !,
    compare(Order,X,Y),
    appears(Order,p(X,P),Xs,Y,Ys,Flag).
appears(_,_,no).

appears(=,_X,_Xs,_Y,_Ys,yes).
appears(>,X,Xs,_Y,Ys,Flag):-
    appears([X|Xs],Ys,Flag).
appears(<,_X,Xs,Y,Ys,Flag):-
    appears(Xs,[Y|Ys],Flag).

:- pop_prolog_flag(multi_arity_warnings).

%% %------------------------------------------------------------------------%
%% % close(+,+,+,+,+,+,-)                                                   %
%% % close(X,VT,RelX,RelT,Union,K,ASubXT)                                   %
%% % It receives the information about the equation X = T whose information %
%% % is being added to the abstract substitution Union. I.e., it receives   %
%% % the set RelX of elements in Union which are coupled to X, the set RelT %
%% % of elements in Union which are coupled to T,  the abstraction VT of T, %
%% % and the set of variables in T. The information about the equation is   %
%% % added by iterate_extend. Note that the information is added in such a  %
%% % way that a fixpoint computation is needed.                             %
%% %------------------------------------------------------------------------%
%% 
%% close(X,VT,VarsT,RelX,RelT,Union,K,ASubXT):-
%%      iterate_extend(RelX,RelT,X,VT,K,ASubXT0_u,[]),
%%      sort_list_of_lists(ASubXT0_u,ASubXT0),
%%      merge(Union,ASubXT0,ASubXT1),
%%      close_fixpoint(X,VT,VarsT,RelX,RelT,Union,K,ASubXT1,ASubXT0,ASubXT).
%% 
%% close_fixpoint(_X,_VT,_VarsT,_RelX,_RelT,Union,_K,ASubXT1,_ASubXT0,ASubXT):-
%%      ASubXT1 == Union,!,
%%      ASubXT = ASubXT1.
%% close_fixpoint(X,VT,VarsT,RelX,RelT,_Union,K,ASubXT1,ASubXT0,ASubXT):-
%%      rel([X],ASubXT0,TmpRelX),
%%      rel(VarsT,ASubXT0,TmpRelT),
%%      merge(TmpRelX,RelX,NewRelX),
%%      merge(TmpRelT,RelT,NewRelT),
%%      close(X,VT,VarsT,NewRelX,NewRelT,ASubXT1,K,ASubXT).

%------------------------------------------------------------------------%
% iterate_extend(+,+,+,+,+,-,?)                                          %
% iterate_extend(RelX,RelT,X,VT,K,ASubXT0,Tail)                          %
% It propagates the unification of X and T trough the elements of RelX   %
% and RelT obtaining the new sets in ASubXTo.                            %
% This is done recursively by considering each element OccX in RelX and  %
% each element OccT in RelT.                                             %
%------------------------------------------------------------------------%
iterate_extend([],_RelT,_X,_VT,_K,Tail,Tail):- !.
iterate_extend(_RelX,[],_X,_VT,_K,Tail,Tail):- !.
iterate_extend([OccX|RelX],RelT,X,VT,K,ASubXT0,Tail):-
    iterate_extend0(RelT,OccX,X,VT,K,ASubXT0,NewTail),
    iterate_extend(RelX,RelT,X,VT,K,NewTail,Tail).

iterate_extend0([],_OccX,_X,_VT,_K,Tail,Tail).
iterate_extend0([OccT|RelT],OccX,X,VT,K,ASubXT,Tail):-
    and_extend(X,VT,OccX,OccT,K,OccXT),
    eliminate_nil(OccXT,ASubXT,TailASubXT),
    iterate_extend0(RelT,OccX,X,VT,K,TailASubXT,Tail).

eliminate_nil([],Tail,Tail):- !.
eliminate_nil(OccXT,[OccXT|Tail],Tail).

%------------------------------------------------------------------------%
% and_extend(+,+,+,+,+,-)                                                %
% and_extend(X,VT,OccX,OccT,K,OccXT)                                     %
% extends OccX and OccT (related to X and T, respectively, in X=T) with  %
% new sharing sets which arise, via the abstraction VT of X=T, from this %
% equation, and with the new paths this equation implies                 %
%------------------------------------------------------------------------%
% In fact, we don't need to extend, but to replace (see solve)

and_extend(X,VT,OccX,OccT,K,OccXT):-
    intersect_paths_common_vars(VT,OccT,TPs),
    restrict(OccX,[X],XPs),
    and_extend_each(XPs,TPs,Sx,[],St,[]),
%%      scale(OccX,St,K,OccT,OccXT,Tail1),
%%      scale(OccT,Sx,K,OccX,Tail1,[]).
    scale(OccX,St,K,[],OccXT,Tail1),
    scale(OccT,Sx,K,[],Tail1,[]).

and_extend_each([p(_,P)|OccX],OccT,Su,TailSu,St,TailSt):-
    and_extend_each0(OccT,P,Su,NTailSu,St,NTailSt),
    and_extend_each(OccX,OccT,NTailSu,TailSu,NTailSt,TailSt).
and_extend_each([],_OccT,Su,Su,St,St).

and_extend_each0([p(_,RQ)|OccT],P,Su,TailSu,St,TailSt):-
    and_extend_decide(P,RQ,Su,NTailSu,St,NTailSt),
    and_extend_each0(OccT,P,NTailSu,TailSu,NTailSt,TailSt).
and_extend_each0([],_P,Su,Su,St,St).

%% S is a suffix of P to give RQ (Sp) or of RQ to give P (Srq)

and_extend_decide(P,RQ,Sp,TailSp,Srq,TailSrq):-
    top_suffix(RQ,S,P), !,
    Sp = [S|TailSp],
    Srq = [[]|TailSrq].
and_extend_decide(P,RQ,Sp,TailSp,Srq,TailSrq):-
    top_suffix(P,S,RQ), !,
    Srq = [S|TailSrq],
    Sp = [[]|TailSp].
and_extend_decide(_P,_RQ,Sp,Sp,Srq,Srq).

%% top_suffix(A,B,C) iff A.B=C

top_suffix([],S,S).
top_suffix([top],[top],_P):- !.
top_suffix([X|RQ],S,[X|P]):-
    top_suffix(RQ,S,P).

%------------------------------------------------------------------------%
% intersect_paths_common_vars(+,+,-)                                     %
% intersect_paths_common_vars(T1,T2,TPs)                                 %
% yields p(V,P1.P2) for all p(V,P1) in T1 and p(V,P2) in T2              %
%------------------------------------------------------------------------%

intersect_paths_common_vars([p(H1,P1)|T1],[p(H2,P2)|T2],TPs):- !,
    compare(Order,H1,H2),
    intersect_paths(Order,H1,P1,T1,H2,P2,T2,TPs0),
    common_vars_paths(TPs0,TPs).
intersect_paths_common_vars(_,_,[]).

intersect_paths(<,_,_,[p(H1,P1)|T1],H2,P2,T2,TPs):- !,
    compare(Order,H1,H2),
    intersect_paths(Order,H1,P1,T1,H2,P2,T2,TPs).
intersect_paths(<,_,_,[],_,_,_,[]).
intersect_paths(=,H1,P1,T1,H2,P2,T2,[p(H1,P1,[P2|P2s])|TPs]):-
    intersect_paths_equal(T2,H2,P2s),
    intersect_paths(<,H1,P1,T1,H2,P2,T2,TPs).
intersect_paths(>,H1,P1,T1,_,_,[p(H2,P2)|T2],TPs):- !,
    compare(Order,H1,H2),
    intersect_paths(Order,H1,P1,T1,H2,P2,T2,TPs).
intersect_paths(>,_,_,_,_,_,[],[]).

intersect_paths_equal([p(H2,P2)|T2],H,P2s):-
    compare(Order,H,H2),
    intersect_paths_equal0(Order,H,P2,T2,P2s).
intersect_paths_equal([],_,[]).

intersect_paths_equal0(=,H,P2,T2,[P2|P2s]):-
    intersect_paths_equal(T2,H,P2s).
intersect_paths_equal0(<,_,_,_,[]).

common_vars_paths([p(V,P,Ps)|TPs0],TPs):-
    append_paths(Ps,P,V,TPs,Tail),
    common_vars_paths(TPs0,Tail).
common_vars_paths([],[]).

append_paths([P|Ps],P0,V,[p(V,VPs)|TPs],Tail):-
    append(P0,P,VPs),
    append_paths(Ps,P0,V,TPs,Tail).
append_paths([],_P,_V,TPs,TPs).

%------------------------------------------------------------------------%
% restrict(+,+,-)                                                        %
% restrict(Occ,Vs,OccVs)                                                 %
% restricts Occ to elements having variables of Vs                       %
%------------------------------------------------------------------------%

restrict([p(U,P)|Occ],[V|Vs],OccVs):- !,
    compare(Order,U,V),
    restrict0(Order,U,P,Occ,V,Vs,OccVs).
restrict(_Occ,_Vs,[]).

restrict0(<,_,_,[p(U,P)|Occ],V,Vs,OccVs):- !,
    compare(Order,U,V),
    restrict0(Order,U,P,Occ,V,Vs,OccVs).
restrict0(<,_,_,[],_V,_Vs,[]).
restrict0(=,U,P,Occ,V,Vs,[p(U,P)|OccVs]):-
    restrict(Occ,[V|Vs],OccVs).
restrict0(>,U,P,Occ,_,[V|Vs],OccVs):- !,
    compare(Order,U,V),
    restrict0(Order,U,P,Occ,V,Vs,OccVs).
restrict0(>,_,_,_,_,[],[]).

%------------------------------------------------------------------------%
% scale(+,+,+,+,-,?)                                                     %
% scale(OccA,Ps,K,OccB,OccTot,Tail)                                      %
% OccTot has each of the elements of OccA augmented with a path of Ps    %
% plus the elements of OccB plus Tail                                    %
%------------------------------------------------------------------------%
scale([],_Ps,_K,Occ,OccTot,Tail):- !,
    append(Occ,Tail,OccTot).
scale(_,[],_K,_Occ,Tail,Tail):- !.
scale([p(X,XP)|Occs],Ps,K,Occ,OccTot,Tail):-
    scale_each(Ps,X,XP,K,OccTot,Tail1),
    scale(Occs,Ps,K,Occ,Tail1,Tail).

scale_each([P|Ps],X,XP,K,[p(X,NewXP)|OccTot],Tail):-
    append_depth(XP,P,K,NewXP),
    scale_each(Ps,X,XP,K,OccTot,Tail).
scale_each([],_X,_XP,_K,OccTot,OccTot).

append_depth([top],_P,_K,[top]):- !.
append_depth([],P,K,NewXP):-
    append_depth0(K,P,NewXP).
append_depth([X|XP],P,K,[X|NewXP]):-
    K1 is K-1,
    append_depth(XP,P,K1,NewXP).

append_depth0(0,[],[]):- !.
append_depth0(0,[_|_],[top]):- !.
append_depth0(K,[P|Ps],[P|NewPs]):- !,
    K1 is K-1,
    append_depth0(K1,Ps,NewPs).
append_depth0(_K,[],[]).

%-------------------------------------------------------------------------
%                               BASICS
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% ord_split_paths_from_list(+,+,-,-)
% ord_split_paths_from_list(Vars,ASub,Intersect,Disjunct)
% Split the list of lists in the second argument into two lists: in
% the third argument gives the lists containing at least one variable
% of the list in the first argument, in the fourth  argument gives the
% lists which do not contain any variable of it (Not necessarily ordered)
%-------------------------------------------------------------------------
ord_split_paths_from_list([],Xss,[],Xss):- !.
ord_split_paths_from_list(Xs,Xss,Intersect,Disjunct):-
    ord_split_paths_from_list1(Xss,Xs,Intersect,Disjunct).
    
ord_split_paths_from_list1([],_,[],[]).
ord_split_paths_from_list1([L|Ls],Vars,Intersect,Disjunct):-
    Vars = [X|Xs],
    L = [p(Y,_)|Ys],
    compare(D,X,Y),
    has_intersection_path(D,X,Xs,Y,Ys,Flag,NewVars),
    ord_split_paths_from_list2(Flag,NewVars,L,Ls,Intersect,Disjunct).

ord_split_paths_from_list2(end,_NewVars,L,Ls,[],[L|Ls]).
ord_split_paths_from_list2(yes,NewVars,L,Ls,[L|Intersect],Disjunct):-
    ord_split_paths_from_list1(Ls,NewVars,Intersect,Disjunct).
ord_split_paths_from_list2(no,NewVars,L,Ls,Intersect,[L|Disjunct]):-
    ord_split_paths_from_list1(Ls,NewVars,Intersect,Disjunct).

has_intersection_path(=,X,Xs,_Y,_Ys,yes,[X|Xs]).
has_intersection_path(<,_X,[],_Y,_Ys,Flag,_NewVars):- !,
    Flag = end.
has_intersection_path(<,_,[X|Xs],Y,Ys,Flag,NewVars):-
    compare(D,X,Y),
    has_intersection_path(D,X,Xs,Y,Ys,Flag,NewVars).
has_intersection_path(>,X,Xs,_Y,[],Flag,NewVars):- !,
    NewVars = [X|Xs],
    Flag = no.
has_intersection_path(>,X,Xs,_,[p(Y,_)|Ys],Flag,NewVars):- 
    NewVars = [X|Xs],
    compare(D,X,Y),
    has_intersection_next_path(D,X,Xs,Y,Ys,Flag).

has_intersection_next_path(=,_X,_Xs,_Y,_Ys,yes).
has_intersection_next_path(<,_X,[],_Y,_Ys,Flag):- !,
    Flag = no.
has_intersection_next_path(<,_,[X|Xs],Y,Ys,Flag):-
    compare(D,X,Y),
    has_intersection_next_path(D,X,Xs,Y,Ys,Flag).
has_intersection_next_path(>,_X,_Xs,_Y,[],Flag):- !,
    Flag = no.
has_intersection_next_path(>,X,Xs,_,[p(Y,_)|Ys],Flag):-
    compare(D,X,Y),
    has_intersection_next_path(D,X,Xs,Y,Ys,Flag).
    
%-------------------------------------------------------------------------
% member_value_path(+,-,+)                                               |
% member_value_path(ASub,Vars,Value)                                     |
% It returns in Vars the list of variables with path value: Value        |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

member_value_path([],[],_).
member_value_path([Occ|Rest],ListValue,Value):- !,
    member_value_path(Occ,Value,ListValue,Tail),
    member_value_path(Rest,Tail,Value).

member_value_path([],_,Tail,Tail).
member_value_path([p(X,Value)|Rest],Value,ListValue,Tail):- !,
    ListValue = [X|More],
    member_value_path(Rest,Value,More,Tail).
member_value_path([_|Rest],Value,ListValue,Tail):- 
    member_value_path(Rest,Value,ListValue,Tail).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% can_be_ground(+,+)                                                     %
% can_be_ground(ASub,Vars)                                               %
% Succeed if it is possible that all variable sin Vars are ground        %
% according to ASub                                                      %
%-------------------------------------------------------------------------
can_be_ground([],_OldG).
can_be_ground([Occ|ASub],OldG):-
    can_be_ground0(Occ,OldG),
    can_be_ground(ASub,OldG).

can_be_ground0(_,[]):- !.
can_be_ground0([],_).
can_be_ground0([p(X,P)|Occ],[G|OldG]):-
    compare(Order,X,G),
    can_be_ground1(Order,X,P,Occ,G,OldG).

can_be_ground1(<,_X,_P,Occ,G,OldG):-
    can_be_ground0(Occ,[G|OldG]).
can_be_ground1(>,X,P,Occ,_G,OldG):-
    can_be_ground0([p(X,P)|Occ],OldG).
can_be_ground1(=,_X,P,Occ,_G,OldG):-
    memberchk(top,P),
    can_be_ground0(Occ,OldG).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- push_prolog_flag(multi_arity_warnings,off).

:- export(path_to_shfr/3).
path_to_shfr(ASub,Sh,Fr):-
    path_to_shfr0(ASub,Sh0,Fr0,[],[]),
    sort_list_of_lists(Sh0,Sh),
    sort(Fr0,Fr).

path_to_shfr0([ASub|ASubs],Sh,Fr,ShT,FrT):-
    path_to_shfr(ASub,Sh,Fr,Sh0,Fr0),
    path_to_shfr0(ASubs,Sh0,Fr0,ShT,FrT).
path_to_shfr0([],Sh,Fr,Sh,Fr).

path_to_shfr([ASub|ASubs],Sh,Fr,ShT,FrT):-
    path_to_sh_fr(ASub,Sh,Fr,Sh0,Fr0),
    path_to_shfr(ASubs,Sh0,Fr0,ShT,FrT).
path_to_shfr([],Sh,Fr,Sh,Fr).

:- pop_prolog_flag(multi_arity_warnings).

path_to_sh_fr([Set|ASub],[ShSet|Sh],Fr,ShT,FrT):-
    path_set_to_sh_set(Set,ShSet,Fr,Fr0),
    path_to_sh_fr(ASub,Sh,Fr0,ShT,FrT).
path_to_sh_fr([],Sh,Fr,Sh,Fr).

path_set_to_sh_set([p(X,P)|Set],[X|Sh],Fr,FrT):-
    if_free(P,X,Fr,Fr0),
    path_set_to_sh_set(Set,Sh,Fr0,FrT).
path_set_to_sh_set([],[],Fr,Fr).

if_free([],X,[X/f|Fr],Fr).
if_free([_|_],X,[X/nf|Fr],Fr).
