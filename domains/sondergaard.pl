:- module(sondergaard,
    [ son_call_to_entry/9,
      son_call_to_success_builtin/6, 
      son_call_to_success_fact/9, 
      son_call_to_prime_fact/6, 
      son_compute_lub/2,  
      son_exit_to_prime/7,
      son_extend/5,       
      son_glb/3,        
      son_input_user_interface/5, 
      son_input_interface/4, 
      son_less_or_equal/2,
      son_lub/3,        
      son_asub_to_native/5,
      son_project/5,      
      son_abs_sort/2,         
      son_special_builtin/5,
      son_success_builtin/6,
      son_unknown_call/4,
      son_unknown_entry/3,
      son_empty_entry/3,
    %
      propagate_to_sh/4,
      propagate_to_son/4,
    %
      share_to_son/3,
      son_to_share/4
    ],
    [ assertions ] ).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(son).
:- dom_impl(son, call_to_entry/9).
:- dom_impl(son, exit_to_prime/7).
:- dom_impl(son, project/5).
:- dom_impl(son, compute_lub/2).
:- dom_impl(son, abs_sort/2).
:- dom_impl(son, extend/5).
:- dom_impl(son, less_or_equal/2).
:- dom_impl(son, glb/3).
:- dom_impl(son, call_to_success_fact/9).
:- dom_impl(son, special_builtin/5).
:- dom_impl(son, success_builtin/6).
:- dom_impl(son, call_to_success_builtin/6).
:- dom_impl(son, input_interface/4).
:- dom_impl(son, input_user_interface/5).
:- dom_impl(son, asub_to_native/5).
:- dom_impl(son, unknown_call/4).
:- dom_impl(son, unknown_entry/3).
:- dom_impl(son, empty_entry/3).
% :- dom_impl(son, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).

:- use_module(domain(sharing), [
    input_interface/4,
    input_user_interface/5
]).
:- use_module(domain(s_grshfr), [new1_gvars/4]).
:- use_module(domain(share_aux), [if_not_nil/4,append_dl/3,handle_each_indep/4]).

% Ciao lib
:- use_module(library(lists), [append/3, list_to_list_of_lists/2]).
:- use_module(library(llists), [collect_singletons/2]).
:- use_module(library(lsets), 
    [ closure_under_union/2,
      ord_split_lists/4,
      ord_split_lists_from_list/4,
      sort_list_of_lists/2
    ]).
:- use_module(library(sets), 
    [ insert/3, 
      merge/3,
      ord_delete/3,
      ord_intersect/2,
      ord_intersection/3,
      ord_member/2, 
      ord_subset/2, 
      ord_subtract/3,
      ord_union/3,
      ord_union_diff/4,
      setproduct/3
    ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2]).

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 22/10/92                             %
%                       programmer: M.J. Garcia de la Banda              %
%                                                                        %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
% _sh      : suffix indicating the sharing component                     %
% _gr      : suffix indicating the groundness component                  %
% Sh and Gr: for simplicity, they will represent ASub_sh and ASub_gr     %
%            respectively                                                %
% Binds    : List of primitive bindings corresponding to the unification %
%            of Term1 = Term2.                                           %
% Gv       : set of ground variables (can be added as a prefix of a set  %
%            of variables, e.g. GvHv means the set of ground variables of%
%            the head variables)                                         %
% BPrime   : similar to the abstract prime constraint: abstract          %
%            subtitution obtained after the analysis of the clause being %
%            considered still projected onto Hv (i.e. just before going  %
%            Sv and thus, to Prime)                                      %
% Rest are as in domain_dependent.pl                                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
% son_project(+,+,+,+,-)                                                 |
% son_project(Sg,Vars,HvFv_u,ASub,Proj)                                  |
% Proj_gr will the the intersection among Vars and Gv. Proj_sh will      |
% be { Xs in Sh| Xs \subseteq Vars}                                      |
%-------------------------------------------------------------------------

son_project(_Sg,_Vars,_HvFv_u,'$bottom',Proj):- !,
    Proj = '$bottom'.
son_project(_Sg,[],_HvFv_u,_,Proj):- !,
    Proj = ([],[]).
son_project(_Sg,Vars,_HvFv_u,(Gr,Sh),(Proj_gr,Proj_sh)):-
    ord_intersection(Gr,Vars,Proj_gr),
    son_project_subst(Sh,Vars,Proj_sh).

son_project_subst([],_,[]).
son_project_subst([Xs|Xss],Vars,Proj_sh):-
    ord_subset(Xs,Vars), !,
    Proj_sh = [Xs|Rest],
    son_project_subst(Xss,Vars,Rest).
son_project_subst([_|Xss],Vars,Proj_sh):-
    son_project_subst(Xss,Vars,Proj_sh).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% son_call_to_entry(+,+,+,+,+,+,+,-,-)                                   %
% son_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)             %
% It obtains the abstract substitution (Entry) which results from adding %
% the abstraction of the Sg = Head to Proj, later projecting the         %
% resulting substitution onto Hv. This is done as follows:               %
%  * If Sg and Head are identical up to renaming it is just a question   %
%    or renaming Proj                                                    %
%  * If Hv = [], Entry is just ([],[])                                   %
%  * Otherwise, it will                                                  %
%    - Obtain in Binds the set of primitive equations corresponding to   %
%      the equation Sg = Head                                            %
%    - obtain Gv1 (variables in Sg or Heag involved in a primitive       %
%      equation with a ground term)                                      %
%    - propagate the groundnes of Gv1 to Proj through Binds obtaining    %
%      NewBinds (grounding bindings eliminated) TempSh (sharing part of  %
%      thee abstract domain) and GvAll (ground variables in both Sg and  %
%      head                                                              %
%    - Entry_gr  will be the result of intersecting GvAll and Hv         %
%    - obtain in NonLinear the set of possibly non linear variables      %
%      w.r.t. TempSh                                                     %
%    - perform the abstract unification for each binding given in Binds  %
%      starting from Sh and the list of non linear variables NonLinear   %
%      in Sh, obtaining NewSh.                                           %
%    - Entry_sh will be the result of projeecting NewSh onto Hv          %
%------------------------------------------------------------------------%

son_call_to_entry(_Sv,Sg,_Hv,Head,_K,_Fv,Proj,Entry,yes):-
    variant(Sg,Head),!,
    copy_term((Sg,Proj),(NewTerm,NewEntry)),
    Head = NewTerm,
    son_abs_sort(NewEntry,Entry).
son_call_to_entry(_Sv,_Sg,[],_Head,_K,_Fv,_Proj,([],[]),no):- !.
son_call_to_entry(_Sv,Sg,Hv,Head,_K,_Fv,(Proj_gr,Proj_sh),Entry,(NewBinds,GvAll)):-
    son_abs_unify(Sg,Head,Binds,Gv1),
    son_groundness_propagate(Binds,Proj_gr,Gv1,Proj_sh,NewBinds,TempSh,
                                                                  GvAll),
    ord_intersection(GvAll,Hv,Entry_gr),
    collect_singletons(TempSh,NonLinear),
    unify_list_binds(NewBinds,TempSh,NonLinear,NewSh),
    son_project_subst(NewSh,Hv,Entry_sh),
    Entry = (Entry_gr,Entry_sh).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------|
% son_exit_to_prime(+,+,+,+,+,+,-)                                       |
% son_exit_to_prime(Sg,Hv,Head,_,Exit,ExtraInfo,Prime)                   |
% * If Exit is '$bottom', Prime will be also '$bottom'.                  %
% * If Flag = yes (Head and Sg identical up to renaming) it is just a    %
%   question or renaming Exit                                            %
% * If Hv = [], Sh_Prime = [] and Prime_gr = Sv                          %
% * Otherwise:                                                           %
%     - Projects Exit onto Hv obtaining (Gv and Sh)                      %
%     - Propagates through Binds the groundness of Gv and Gv_1 (all      %
%       variables ground after abstracting Sg = Head) to Sh, obtaining   %
%      NewBinds (grounding bindings eliminated) TempSh (sharing part of  %
%      thee abstract domain) and GvAll (ground variables in both Sg and  %
%      head)                                                             %
%    - Entry_gr  will be the result of intersecting GvAll and Hv         %
%    - obtains in NonLinear the set of possibly non linear variables     %
%      w.r.t. TempSh                                                     %
%    - perform the abstract unification for each binding given in Binds  %
%      starting from Sh and the list of non linear variables NonLinear   %
%      in Sh, obtaining NewSh.                                           %
%    - Entry_sh will be the result of projecting NewSh onto Hv           %
%------------------------------------------------------------------------%

son_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom') :- !.
son_exit_to_prime(Sg,Hv,Head,_,Exit,Flag,Prime):- 
    Flag == yes, !,
    son_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    son_abs_sort(NewPrime,Prime).
son_exit_to_prime(_,[],_,Sv,_,_,(Sv,[])):- !.
son_exit_to_prime(Sg,Hv,_,Sv,Exit,(Binds,Gv_1),Prime):-
    son_project(Sg,Hv,not_provided_HvFv_u,Exit,(Gv,Sh)),
    son_groundness_propagate(Binds,Gv,Gv_1,Sh,NewBinds,TempSh,GvAll),
    ord_intersection(GvAll,Sv,Gv_prime),
    collect_singletons(TempSh,NonLinear),
    unify_list_binds(NewBinds,TempSh,NonLinear,NewSh),
    son_project_subst(NewSh,Sv,Prime_sh),
    Prime = (Gv_prime,Prime_sh).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT SORT
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% son_abs_sort(+,-)                                                          |
% son_abs_sort(ASub_u,ASub)                                                  |
% First sorts the set of variables in Gr, then it sorts the set of set   |
% of variables Sh.                                                       |
%-------------------------------------------------------------------------

son_abs_sort('$bottom','$bottom').
son_abs_sort((Gr,Sh),(Gr_s,Sh_s)):-
    sort(Gr,Gr_s),
    sort_list_of_lists(Sh,Sh_s).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT LUB
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% son_compute_lub(+,-)                                                   %
% son_compute_lub(ListASub,Lub)                                          %
% It computes the lub of a set of Asub. For each two abstract            %
% substitutions ASub1 and ASub2 in ListASub, obtaining the lub is just   %
% (1) intersecting Gr1 and Gr2                                           %
% (2) merging Sh1 and Sh2                                                %
%------------------------------------------------------------------------%

son_compute_lub([Xss,Yss|Rest],Lub) :- !,
    son_lub(Xss,Yss,Zss),
    son_compute_lub([Zss|Rest],Lub).
son_compute_lub([X],X).

son_lub('$bottom',Yss,Yss):- !.
son_lub(Xss,'$bottom',Xss):- !.
son_lub(Xss,Yss,Zss) :-
    Xss == Yss,!,
    Zss = Xss.
son_lub((Gx,Shx),(Gy,Shy),(Gz,Shz)) :-
    ord_intersection(Gx,Gy,Gz),
    merge(Shx,Shy,Shz).

%------------------------------------------------------------------------%
% son_glb(+,+,-)                                                         %
% son_glb(ASub0,ASub1,Lub)                                               %
%------------------------------------------------------------------------%

son_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
son_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
son_glb(Xss,Yss,Zss) :-
    Xss == Yss, !,
    Zss = Xss.
son_glb((Gx,Shx),(Gy,Shy),(Gz,Shz)) :-
    ord_union(Gx,Gy,Gz),
    ord_intersection(Shx,Shy,Shz).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Extend
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% son_extend(+,+,+,+,-)                                                  %
% son_extend(Sg,Prime,Sv,Call,Succ)                                      %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ.             %
% Otherwise:                                                             %
%  * Succ_gr is the result of merging Prime_gr and Call_gr               %
%  * Then, it obtains in Temp_sh the result of eliminating the couples   %
%    in Sh in which a ground variables appears                           %
%  * Projects Temp_sh onto Sv and obtaining Temp1                        %
%------------------------------------------------------------------------%

son_extend(_Sg,'$bottom',_,_,'$bottom'):- !.
son_extend(_Sg,_,[],Call,Succ):- !,
    Succ = Call.
son_extend(_Sg,(Prime_gr,Prime_sh),Sv,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):-
    merge(Prime_gr,Call_gr,Succ_gr),
    ord_split_lists_from_list(Prime_gr,Call_sh,_Intersect,Temp_Sh),
    son_project_subst(Temp_Sh,Sv,Temp1),
    ord_subtract(Temp1,Prime_sh,Eliminate),
    ord_subtract(Temp_Sh,Eliminate,Temp1_Sh),
    son_unify_each_exit(Prime_sh,Temp1_Sh,[],Succ_sh).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------

son_call_to_success_fact(_,[],_Head,_K,Sv,(Call_gr,Call_sh),_,Prime,Succ):- !,
    Prime = (Sv,[]),
    merge(Call_gr,Sv,Succ_gr),
    ord_split_lists_from_list(Sv,Call_sh,_Intersect,Succ_sh),
    Succ = (Succ_gr,Succ_sh). 
son_call_to_success_fact(Sg,_,Head,_K,Sv,Call,(Gv,Sh),(Prime_gr,Prime_sh),Succ):-
    son_abs_unify(Sg,Head,Binds,Gv_1),
    son_groundness_propagate(Binds,Gv,Gv_1,Sh,NewBinds,TempSh,GvAll),
    collect_singletons(TempSh,NonLinear),
    unify_list_binds(NewBinds,TempSh,NonLinear,NewSh),
    son_project_subst(NewSh,Sv,Prime_sh),
    ord_intersection(GvAll,Sv,Prime_gr),
    son_extend(Sg,(Prime_gr,Prime_sh),Sv,Call,Succ).

%------------------------------------------------------------------------- |
% son_call_to_prime_fact/6 obtains the abstract prime substitution         |
% from the lambda for a fact. (it is a combination of the call_to_entry and|
% exit_to_prime functions) only needed in the combinations of domains      |
%------------------------------------------------------------------------- |

son_call_to_prime_fact(_,[],_,Sv,_,(Sv,[])):- !.
son_call_to_prime_fact(Sg,_,Head,Sv,(Gv,Sh),(Prime_gr,Prime_sh)):-
    son_abs_unify(Sg,Head,Binds,Gv_1),
    son_groundness_propagate(Binds,Gv,Gv_1,Sh,New_Binds,Temp_Sh,
                                                           Gv_final),
    collect_singletons(Temp_Sh,NonLinear),
    unify_list_binds(New_Binds,Temp_Sh,NonLinear,New_Sh),
    ord_intersection(Gv_final,Sv,Prime_gr),
    son_project_subst(New_Sh,Sv,Prime_sh).

%-------------------------------------------------------------------------
% son_unknown_call(+,+,+,-)                                                |
% son_unknown_call(Sg,Vars,Call,Succ)                                       |
% Succ_gr is identical to Call_gr. Succ_sh is obtained by selecting the  |
% non ground variables in Vars, and obtaining all possible couples and   |
% singletons.                                                            |
%-------------------------------------------------------------------------

son_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
son_unknown_call(_Sg,Vars,(Call_gr,_Call_sh),Succ):-
    ord_subtract(Vars,Call_gr,TopVars),
    couples_and_singletons(TopVars,Succ_sh,[]),
    Succ = (Call_gr,Succ_sh).
    
%-------------------------------------------------------------------------
% son_unknown_entry(+,+,-)                                               |
% son_unknown_entry(Sg,Qv,Call)                                          |
% The top value in Sh for a set of variables is the powerset, in Fr is   |
% X/nf forall X in the set of variables                                  |
%-------------------------------------------------------------------------

son_unknown_entry(_Sg,Qv,([],Sh)):-
    couples_and_singletons(Qv,Sh1,[]),
    sort_list_of_lists(Sh1,Sh).

%-------------------------------------------------------------------------
% son_empty_entry(+,+,-)                                                   |
% The empty value in Sh for a set of variables is the list of singletons,
% in Fr is X/f forall X in the set of variables.                         |
% So, here, all linear and independent: i.e., [].                        |
%-------------------------------------------------------------------------

son_empty_entry(_Sg,_Qv,([],[])).

%------------------------------------------------------------------------%
% son_asub_to_native(+,+,+,-,-)                                          %
% son_asub_to_native(ASub,Qv,OutFlag,ASub_user,Comps)                    %
% The user friendly format consists in extracting the ground variables   %
% (Gr) the linear variables (those which do not appear as singletons in  %
% Sh. The rest is the way in which pair sharing is transformed into set  %
% sharing                                                                %
%------------------------------------------------------------------------%

son_asub_to_native((Gr,SSon),Qv,_OutFlag,ASub_user,[]):-
    son_to_share((Gr,SSon),Qv,SetSh,LinearVars0),
    ord_subtract(LinearVars0,Gr,LinearVars),
    if_not_nil(Gr,ground(Gr),ASub_user,ASub_user0),
    if_not_nil(LinearVars,linear(LinearVars),ASub_user0,ASub_user1),
    if_not_nil(SetSh,sharing(SetSh),ASub_user1,[]).

%-------------------------------------------------------------------------
% son_input_user_interface(+,+,-,+,+)                                    %
% son_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)           %
% Gr is the set of variables which are in Qv but not in Sharing          %
% (share(Sharing) given by the user). Sh is computed as follows:         %
%  - Linear is the set of linear variables given by the user (if any)    %
%  - a first approximation to the non linear variables is Qv minus Linear%
%  - Then (since the ground and free variables are also linear) they are %
%    also subtracted in order to allow the user not to explicit them,    %
%    obtaining the final NonLinear.                                      %
%  - Those nonlinear variables are transformed into singletons.          %
%  - Finally the (set) Sharing given by the user is transformed into our %
%    (pair) sharing Sh                                                   %
%-------------------------------------------------------------------------

son_input_user_interface((Sh0,Lin0),Qv,(Gr,Sh),Sg,MaybeCallASub):-
    sharing:input_user_interface(Sh0,Qv,SH,Sg,MaybeCallASub),
    varset(SH,SHv),
    ord_subtract(Qv,SHv,Gr),
    may_be_var(Lin0,Linear),
    ord_subtract(Qv,Linear,NonLinear1),
    ord_subtract(NonLinear1,Gr,NonLinear),
    list_to_list_of_lists(NonLinear,Singletons),
    share_to_son(SH,Sh_u,Singletons),
    sort_list_of_lists(Sh_u,Sh).

son_input_interface(Info,Kind,(Sh0,Lin),(Sh,Lin)):-
    sharing:input_interface(Info,Kind,Sh0,Sh), !.
son_input_interface(free(X),approx,(Sh,Lin0),(Sh,Lin)):-
    var(X),
    may_be_var(Lin0,Lin1),
    insert(Lin1,X,Lin).
son_input_interface(linear(X),perfect,(Sh,Lin0),(Sh,Lin)):-
    varset(X,Xs),
    may_be_var(Lin0,Lin1),
    merge(Lin1,Xs,Lin).

may_be_var(X,X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------%
% son_less_or_equal(+,+)                                                 %
% son_less_or_equal(ASub0,ASub1)                                         %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

son_less_or_equal(ASub0,ASub1):-
    ASub0 == ASub1, !.
son_less_or_equal((Gr0,Sh0),(Gr1,Sh1)):-
    ord_subset(Gr1,Gr0),
    ord_subset(Sh0,Sh1).


%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% son_special_builtin(+,+,+,-,-)                                         |
% son_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                    |
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

%-------------------------------------------------------------------------
son_special_builtin('absolute_file_name/2',_,_,ground,_).
son_special_builtin('abolish/2',_,_,ground,_).
son_special_builtin('atom/1',_,_,ground,_).
son_special_builtin('atomic/1',_,_,ground,_).
%son_special_builtin('CHOICE IDIOM/1',_,_,ground,_).
son_special_builtin('internals:$metachoice/1',_,_,ground,_).
son_special_builtin('$simplify_unconditional_cges/1',_,_,ground,_).
son_special_builtin('compare/3',_,_,ground,_).
son_special_builtin('current_atom/1',_,_,ground,_).
son_special_builtin('current_input/1',_,_,ground,_).
son_special_builtin('current_module/1',_,_,ground,_).
son_special_builtin('current_output/1',_,_,ground,_).
son_special_builtin('current_op/3',_,_,ground,_).
%son_special_builtin('CUT IDIOM/1',_,_,ground,_).
son_special_builtin('internals:$metacut/1',_,_,ground,_).
son_special_builtin('close/1',_,_,ground,_).
son_special_builtin('depth/1',_,_,ground,_).
son_special_builtin('ensure_loaded/1',_,_,ground,_).
son_special_builtin('erase/1',_,_,ground,_).
son_special_builtin('float/1',_,_,ground,_).
son_special_builtin('flush_output/1',_,_,ground,_).
son_special_builtin('get_code/1',_,_,ground,_).
son_special_builtin('get1_code/1',_,_,ground,_).
son_special_builtin('get_code/2',_,_,ground,_).
son_special_builtin('get1_code/2',_,_,ground,_).
son_special_builtin('ground/1',_,_,ground,_).
son_special_builtin('int/1',_,_,ground,_).
son_special_builtin('integer/1',_,_,ground,_).
son_special_builtin('is/2',_,_,ground,_).
son_special_builtin('name/2',_,_,ground,_).
son_special_builtin('number/1',_,_,ground,_).
son_special_builtin('num/1',_,_,ground,_).
son_special_builtin('numbervars/3',_,_,ground,_).
son_special_builtin('nl/1',_,_,ground,_).
son_special_builtin('open/3',_,_,ground,_).
son_special_builtin('op/3',_,_,ground,_).
son_special_builtin('prolog_flag/2',_,_,ground,_).
son_special_builtin('prolog_flag/3',_,_,ground,_).
son_special_builtin('put_code/1',_,_,ground,_).
son_special_builtin('put_code/2',_,_,ground,_).
son_special_builtin('statistics/2',_,_,ground,_).
son_special_builtin('seeing/1',_,_,ground,_).
son_special_builtin('see/1',_,_,ground,_).
son_special_builtin('telling/1',_,_,ground,_).
son_special_builtin('tell/1',_,_,ground,_).
son_special_builtin('tab/1',_,_,ground,_).
son_special_builtin('tab/2',_,_,ground,_).
son_special_builtin('ttyput/1',_,_,ground,_).
%son_special_builtin(':/2',(prolog:'$metachoice'(_)),_,ground,_).
%son_special_builtin(':/2',(prolog:'$metacut'(_)),_,ground,_).
son_special_builtin('save_event_trace/1',_,_,ground,_).
son_special_builtin('=:=/2',_,_,ground,_).
son_special_builtin('>=/2',_,_,ground,_).
son_special_builtin('>/2',_,_,ground,_).
son_special_builtin('</2',_,_,ground,_).
son_special_builtin('=</2',_,_,ground,_).
% SICStus3 (ISO)
son_special_builtin('=\\=/2',_,_,ground,_).
% SICStus2.x
% son_special_builtin('=\=/2',_,_,ground,_).
%-------------------------------------------------------------------------
son_special_builtin('abort/0',_,_,bottom,_).
son_special_builtin('fail/0',_,_,bottom,_).
son_special_builtin('false/0',_,_,bottom,_).
son_special_builtin('halt/0',_,_,bottom,_).
%-------------------------------------------------------------------------
son_special_builtin('!/0',_,_,unchanged,_).
son_special_builtin('assert/1',_,_,unchanged,_).
son_special_builtin('asserta/1',_,_,unchanged,_).
son_special_builtin('assertz/1',_,_,unchanged,_).
son_special_builtin('debug/0',_,_,unchanged,_).
son_special_builtin('debugging/0',_,_,unchanged,_).
son_special_builtin('dif/2',_,_,unchanged,_).
son_special_builtin('display/1',_,_,unchanged,_).
son_special_builtin('flush_output/0',_,_,unchanged,_).
son_special_builtin('garbage_collect/0',_,_,unchanged,_).
son_special_builtin('gc/0',_,_,unchanged,_).
son_special_builtin('listing/0',_,_,unchanged,_).
son_special_builtin('listing/1',_,_,unchanged,_).
son_special_builtin('nl/0',_,_,unchanged,_).
son_special_builtin('nogc/0',_,_,unchanged,_).
son_special_builtin('nonvar/1',_,_,unchanged,_). % needed?
son_special_builtin('not_free/1',_,_,unchanged,_).
son_special_builtin('not/1',_,_,unchanged,_).
son_special_builtin('print/1',_,_,unchanged,_).
son_special_builtin('repeat/0',_,_,unchanged,_).
son_special_builtin('start_event_trace/0',_,_,unchanged,_).
son_special_builtin('stop_event_trace/0',_,_,unchanged,_).
son_special_builtin('seen/0',_,_,unchanged,_).
son_special_builtin('told/0',_,_,unchanged,_).
son_special_builtin('true/0',_,_,unchanged,_).
son_special_builtin('ttyflush/0',_,_,unchanged,_).
son_special_builtin('otherwise/0',_,_,unchanged,_).
son_special_builtin('ttynl/0',_,_,unchanged,_).
son_special_builtin('write/1',_,_,unchanged,_).
son_special_builtin('writeq/1',_,_,unchanged,_).
% SICStus3 (ISO)
%meta! (no need) son_special_builtin('\\+/1',_,_,unchanged,_).
son_special_builtin('\\==/2',_,_,unchanged,_).
% SICStus2.x
% son_special_builtin('\+/1',_,_,unchanged,_).
% son_special_builtin('\==/2',_,_,unchanged,_).
son_special_builtin('@>=/2',_,_,unchanged,_).
son_special_builtin('@=</2',_,_,unchanged,_).
son_special_builtin('@>/2',_,_,unchanged,_).
son_special_builtin('@</2',_,_,unchanged,_).
%-------------------------------------------------------------------------
son_special_builtin('format/2',format(X,_Y),_,some,[X]).
son_special_builtin('format/3',format(X,Y,_Z),_,some,List):-
    varset([X,Y],List).
son_special_builtin('functor/3',functor(_X,Y,Z),_,some,List):-
    varset([Y,Z],List).
son_special_builtin('length/2',length(_X,Y),_,some,List):-
    varset(Y,List).
son_special_builtin('print/2',print(X,_Y),_,some,[X]).
son_special_builtin('predicate_property/2',predicate_property(_X,Y),_,some,Vars):-
    varset(Y,Vars).
son_special_builtin('recorda/3',recorda(_,_,Z),_,some,Vars):-
    varset(Z,Vars).
son_special_builtin('recordz/3',recordz(_,_,Z),_,some,Vars):-
    varset(Z,Vars).
son_special_builtin('assert/2',assert(_X,Y),_,some,Vars):-
    varset(Y,Vars).
son_special_builtin('asserta/2',asserta(_X,Y),_,some,Vars):-
    varset(Y,Vars).
son_special_builtin('assertz/2',assertz(_X,Y),_,some,Vars):-
    varset(Y,Vars).
son_special_builtin('write/2',write(X,_Y),_,some,Vars):-
    varset(X,Vars).
%%%%%%%%%% '=../2'
son_special_builtin('=../2','=..'(X,Y),_,'=../2',p(X,Y)).
%%%%%%%%%% 'recorded/3'
son_special_builtin('recorded/3',recorded(_,Y,Z),_,'recorded/3',p(Y,Z)).
son_special_builtin('retract/1',retract(X),_,'recorded/3',p(X,a)).
son_special_builtin('retractall/1',retractall(X),_,'recorded/3',p(X,a)).
%%%%%%%%%% 'read/1'
son_special_builtin('read/1',read(X),_,'read/1',p(X)).
%%%%%%%%%% 'read/2'
son_special_builtin('read/2',read(X,Y),_,'read/2',p(X,Y)).
%%%%%%%%%% 'copy_term/2'
son_special_builtin('copy_term/2',copy_term(X,Y),_,copy_term,p(X,Y)).
%%%%%%%%%% 'var/1'
son_special_builtin('var/1',var(X),_,var,p(X)). % needed?
son_special_builtin('free/1',var(X),_,var,p(X)).
%%%%%%%%%% 'indep/2'
son_special_builtin('indep/2',indep(X,Y),_,'indep/2',p(X,Y)).
%%%%%%%%%% 'indep/1'
son_special_builtin('indep/1',indep(X),_,'indep/1',p(X)).
%%%%%%%%%% 'arg/3'
son_special_builtin('arg/3',arg(X,Y,Z),_,'arg/3',p(X,Y,Z)).
%%%%%%%%%% '==/2'
son_special_builtin('==/2','=='(X,Y),_,'==/2',p(X,Y)).
%%%%%%%%%% reducible to '=/2'
son_special_builtin('=/2','='(X,Y),_,'=/2',p(X,Y)).
son_special_builtin('C/3','C'(X,Y,Z),_,'=/2',p(X,[Y|Z])).
son_special_builtin('expand_term/2',expand_term(X,Y),_,'arg/3',p(1,Y,X)).
son_special_builtin('keysort/2',keysort(X,Y),_,'=/2',p(X,Y)).
son_special_builtin('sort/2',sort(X,Y),_,'=/2',p(X,Y)).

%-------------------------------------------------------------------------
% son_success_builtin(+,+,+,+,+,-)                                       |
% son_success_builtin(Type,Sv_u,Condv,_HvFv_u,Call,Succ)                         |
% Obtains the success for some particular builtins:                      |
%  * If Type = ground, it updates Call making all vars in Sv_u ground    |
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%-------------------------------------------------------------------------

son_success_builtin(ground,Sv_u,_,_,(Gv,Sh),(Succ_gr,Succ_sh)):-
    sort(Sv_u,Sv),
    merge(Sv,Gv,Succ_gr),
    ord_split_lists_from_list(Sv,Sh,_Intersect,Succ_sh).
son_success_builtin(bottom,_,_,_,_,'$bottom').
son_success_builtin(unchanged,_,_,_,Call,Call).
son_success_builtin(some,_,NewGround,_HvFv_u,(Gr,Sh),(Succ_gr,Succ_sh)):-
    merge(Gr,NewGround,Succ_gr),
    ord_split_lists_from_list(NewGround,Sh,_Intersect,Succ_sh).
son_success_builtin('=../2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):-
    varset(X,Varsx),
    ord_subset(Varsx,Call_gr),!,
    varset(Y,Varsy),
    merge(Varsy,Call_gr,Succ_gr),
    ord_split_lists_from_list(Varsy,Call_sh,_Intersect,Succ_sh).
son_success_builtin('=../2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):-
    varset(Y,Varsy),
    ord_subset(Varsy,Call_gr),!,
    varset(X,Varsx),
    merge(Varsx,Call_gr,Succ_gr),
    ord_split_lists_from_list(Varsx,Call_sh,_Intersect,Succ_sh).
son_success_builtin('=../2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),Succ):-
    var(X), var(Y),!,
    sort([[X],[Y]],NonLinear),
    ( ord_intersect(NonLinear,Call_sh) ->
      sort_list_of_lists([[X],[X,Y],[Y]],Prime)
    ; sort([X,Y],T),
      Prime = [T]
    ),
    son_unify_each_exit(Prime,Call_sh,[],Succ_sh),
    Succ = (Call_gr,Succ_sh).
son_success_builtin('=../2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):-
    var(X), !,
    Y = [Z|R],
    (var(Z) ->
        ord_split_lists_from_list([Z],Call_sh,_Intersect,Prime_sh),
        insert(Call_gr,Z,Succ_gr)
    ; Prime_sh = Call_sh,
      Succ_gr = Call_gr
    ),
    son_abs_unify(X,R,Binds,_),
    collect_singletons(Prime_sh,NonLinear),
    unify_list_binds(Binds,Prime_sh,NonLinear,Succ_sh).
son_success_builtin('recorded/3',_,p(Y,Z),_HvFv_u,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):-
    varset(Z,VarsZ),
    ord_split_lists_from_list(VarsZ,Call_sh,_Intersect,Disjoint),
    merge(VarsZ,Call_gr,Succ_gr),
    varset(Y,Varsy),
    ord_subtract(Varsy,Succ_gr,NonGround),
    couples_and_singletons(NonGround,Prime_sh,[]),
    son_unify_each_exit(Prime_sh,Disjoint,[],Succ_sh).
son_success_builtin('read/1',_,p(X),_HvFv_u,(Call_gr,Call_sh),(Call_gr,Succ_sh)):-
    varset(X,Varsx),
    ord_subtract(Varsx,Call_gr,NonGround),
    couples_and_singletons(NonGround,Prime_sh,[]),
    son_unify_each_exit(Prime_sh,Call_sh,[],Succ_sh).
son_success_builtin('read/2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):-
    varset(X,Varsx),
    merge(Varsx,Call_gr,Succ_gr),
    varset(Y,Varsy),
    ord_subtract(Varsy,Succ_gr,NonGround),
    couples_and_singletons(NonGround,Prime_sh,[]),
    son_unify_each_exit(Prime_sh,Call_sh,[],Succ_sh).
son_success_builtin(copy_term,Sv_u,p(X,Y),HvFv_u,Call,Succ):-
    copy_term(Y,NewY),
    varset(NewY,Hv),
    varset(X,Xv),
    son_project(not_provided_Sg,Xv,not_provided_HvFv_u,Call,Proj),
    son_call_to_entry(Xv,X,Hv,NewY,not_provided,[],Proj,(Entry_gr,Entry_sh),_), % TODO: add some ClauseKey?
    Call = (Call_gr,Call_sh),
    merge(Call_gr,Entry_gr,TempCall_gr),
    merge(Call_sh,Entry_sh,TempCall_sh),
    varset(Y,Yv),
    merge(Hv,Yv,TempSv),
    son_success_builtin('=/2',TempSv,p(NewY,Y),HvFv_u,(TempCall_gr,TempCall_sh),
                              TempSucc),
    varset(Call,Callv),
    sort(Sv_u,Sv),
    merge(Callv,Sv,Vars),
    son_project(not_provided_Sg,Vars,not_provided_HvFv_u,TempSucc,Succ).
son_success_builtin(var,_,p(X),_HvFv_u,(Call_gr,_),Succ):-
    ord_member(X,Call_gr), !,
    Succ = '$bottom'.
son_success_builtin(var,_,p(X),_HvFv_u,(Call_gr,Call_sh),(Call_gr,Succ_sh)):-
    ord_subtract(Call_sh,[[X]],Succ_sh).
son_success_builtin('indep/2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),Succ):-
    varset(X,Varsx),
    varset(Y,Varsy),
    setproduct(Varsx,Varsy,Dependent),
    collect_singletons(Dependent,Gv),
    merge(Call_gr,Gv,Succ_gr),
    ord_split_lists_from_list(Gv,Call_sh,_Intersect,TempSh),
    ord_subtract(TempSh,Dependent,Succ_sh),
    Succ = (Succ_gr,Succ_sh).
son_success_builtin('indep/1',_,p(X),_HvFv_u,Call,Succ):- 
    nonvar(X),
    handle_each_indep(X,son,Call,Succ), !.
son_success_builtin('indep/1',_,_,_,_,'$bottom').
son_success_builtin('arg/3',_,p(X,Y,Z),_HvFv_u,(Call_gr,Call_sh),Succ):- 
    varset(Y,Varsy),
    ord_subset(Varsy,Call_gr), !,
    varset([X,Z],Vars),
    ord_split_lists_from_list(Vars,Call_sh,_Intersect,Succ_sh),
    merge(Vars,Call_gr,Succ_gr),
    Succ = (Succ_gr,Succ_sh).
son_success_builtin('arg/3',_,p(X,_,Z),_HvFv_u,(Call_gr,Call_sh),Succ):- 
    varset(Z,Varsz),
    ord_subset(Varsz,Call_gr), !,
    varset(X,Varsx),
    ord_split_lists_from_list(Varsx,Call_sh,_Intersect,Succ_sh),
    merge(Call_gr,Varsx,Succ_gr),
    Succ = (Succ_gr,Succ_sh).
son_success_builtin('arg/3',_,p(X,Y,Z),_HvFv_u,(Call_gr,Call_sh),(Succ_gr,Succ_sh)):- 
    varset(X,Varsx),
    merge(Call_gr,Varsx,Succ_gr),
    ord_split_lists_from_list(Varsx,Call_sh,_Intersect,TempSh),
    varset([Y,Z],Vars),
    list_to_list_of_lists(Vars,Singletons),
    ( ord_intersect(Singletons,TempSh) ->
      couples_and_singletons(Vars,Prime,[])
    ; couples(Vars,Prime,[])
    ),
    son_unify_each_exit(Prime,Call_sh,[],Succ_sh).
son_success_builtin('=/2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),Succ):-
    son_abs_unify(X,Y,Binds,Gr1),
    merge(Gr1,Call_gr,Gr2),
    son_g_propagate(Gr2,Binds,Gr2,NewBinds,Succ_gr),
    ord_subtract(Succ_gr,Call_gr,NewGv),
    ord_split_lists_from_list(NewGv,Call_sh,_Intersect,Temp_Sh),
    collect_singletons(Temp_Sh,NonLinear),
    unify_list_binds(NewBinds,Temp_Sh,NonLinear,Succ_sh), !,
    Succ = (Succ_gr,Succ_sh).
son_success_builtin('=/2',_,_,_,_,'$bottom').
son_success_builtin('==/2',_,p(X,Y),_HvFv_u,(Call_gr,Call_sh),Succ):-
%?      sh_peel(X,Y,Binds-[]),
    son_peel(X,Y,Binds-[]),
    son_make_reduction(Binds,(Call_gr,Call_sh),Ground,Eliminate), !,
    sort(Ground,Ground1),
    merge(Ground1,Call_gr,Succ_gr),
    sort_list_of_lists(Eliminate,Eliminate1),
    ord_subtract(Call_sh,Eliminate1,TempSh),
    ord_split_lists_from_list(Succ_gr,TempSh,_Intersect,Succ_sh),
    Succ = (Succ_gr,Succ_sh).
son_success_builtin('==/2',_,_,_,_,'$bottom').

%-------------------------------------------------------------------------
% son_call_to_success_builtin(+,+,+,+,+,-)                               |
% son_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)                |
% If it gets here, the call for the builtin is bound to fail, so ...     |
%-------------------------------------------------------------------------

son_call_to_success_builtin(_SgKey,_Sg,_Sv,_Call,_Proj,'$bottom').

%-------------------------------------------------------------------------
%            Intermediate Functions                                      %
%-------------------------------------------------------------------------

share_to_son([],T,T).
share_to_son([[_]|Sharing],PairSharing,T):- !,
    share_to_son(Sharing,PairSharing,T).
share_to_son([[X,Y]|Sharing],[[X,Y]|PairSharing],T):- !,
    share_to_son(Sharing,PairSharing,T).
share_to_son([Set|Sharing],PairSharing,T):-
    couples(Set,PairSharing,Tail),
    share_to_son(Sharing,Tail,T).

son_to_share((Gr,SSon),Qv,SetSh,LinearVars):-
    collect_singletons(SSon,NonLinearVars),
    ord_subtract(Qv,NonLinearVars,LinearVars),
    closure_under_union(SSon,Star),
    sort_list_of_lists(Star,Star_s),
    propagate_to_sh(Star_s,SSon,NewSSon,_),
    ord_subtract(Qv,Gr,NonGv),
    list_to_list_of_lists(NonGv,ShSingletons),      
    merge(ShSingletons,NewSSon,SetSh).

%-------------------------------------------------------------------------
% propagate_to_sh(+,+,-,-)                                               |
% propagate_to_sh(ASub_sh,SSon,NewASub_sh,Allowed_sh,Tail)               |
% Eliminates the redundancies in ASub_sh using SSon. This is done by for |
% each set Xs in ASub_sh                                                 |
%  (1) obtaining in NewXss_a the sorted set of all sorted couples in Xs  |
%  (2) If NewXss_s subseteq SSon, Xs is not redundant and thus it is     |
%      added to NewASub_sh and to Allowed_sh. Otherwise it is eliminated |
%-------------------------------------------------------------------------

propagate_to_sh([],_,[],[]).
propagate_to_sh([Xs|Xss],SSon,NewASub_sh,Allowed_sh):-
    couples(Xs,NewXss,[]),
    sort(NewXss,NewXss_s),
    decide_couples(Xss,Xs,NewXss_s,SSon,NewASub_sh,Allowed_sh).

decide_couples(Xss,Xs,NewXss,SSon,NewASub_sh,NewAllowed_sh):-
    ord_subset(NewXss,SSon),!,
    NewASub_sh = [Xs|Rest],
    propagate_to_sh(Xss,SSon,Rest,Allowed_sh),
    merge(NewXss,Allowed_sh,NewAllowed_sh).
decide_couples(Xss,_,_,SSon,NewASub_sh,Allowed_sh):-
    propagate_to_sh(Xss,SSon,NewASub_sh,Allowed_sh).

%-------------------------------------------------------------------------
% propagate_to_son(+,+,+,-)                                              |
% propagate_to_sh(SSon,Allowed_sh,NewGSon,NewSSon)                       |
% Eliminates the redundancies in SSon using Allowed_sh and NewGSon.      |
% This is done by for each set Xs in SSon                                |
%  (1) if Xs is a singleton [X] and X is ground, Xs is eliminated        |
%  (3) If Xs is a couple and is not in Allowed_sh it is eliminated       |
%  (3) Otherwise Xs will be added to NewSSon                             |
%-------------------------------------------------------------------------

propagate_to_son([],_,_,[]).
propagate_to_son([[X]|Xss],Allowed_sh,NewGSon,NewSSon):-
    ord_member(X,NewGSon),!,
    propagate_to_son(Xss,Allowed_sh,NewGSon,NewSSon).
propagate_to_son([[X]|Xss],Allowed_sh,NewGSon,[[X]|NewSSon]):- !,
    propagate_to_son(Xss,Allowed_sh,NewGSon,NewSSon).
propagate_to_son([Xs|Xss],Allowed_sh,NewGSon,NewSSon):-
    ord_member(Xs,Allowed_sh),!,
    NewSSon = [Xs|Rest],
    propagate_to_son(Xss,Allowed_sh,NewGSon,Rest).
propagate_to_son([_|Xss],Allowed_sh,NewGSon,NewSSon):- !,
    propagate_to_son(Xss,Allowed_sh,NewGSon,NewSSon).

%-------------------------------------------------------------------------
% son_groundness_propagate(+,+,+,+,-,-,-)                                |
% son_groundness_propagate(OldBinds,Gv1,Gv2,Proj,NewBinds,NewProj,Gv)    |
% It first propagates the groundness of the variables contained in       |
% Gv1 and Gv2 to OldBinds obtaining NewBinds (grounding equations        |
% eliminated) and GvAll (set of all ground variables in Sg and Hv).      |
% Then it updates Proj with this information and sorts it                |
%                                                                        |
% The following have been redefined from sharing.pl in order to deal with|
% the flag which indicates the linearity or non linearity and which is   |
% part of the list of bindings                                           |
%-------------------------------------------------------------------------

son_groundness_propagate(OldBinds,Gv1,Gv2,Proj,NewBinds,NewProj,GvAll) :-
    merge(Gv1,Gv2,Gv),                
    son_g_propagate(Gv,OldBinds,Gv,NewBinds,GvAll),
    ord_split_lists_from_list(GvAll,Proj,_Intersect,NewProj).

son_g_propagate([],Old_Binds,Gvars,Old_Binds,Gvars).
son_g_propagate([X|Xs],Old_Binds,Gvars,New_Binds,GvAll) :-
    new1_gvars(Old_Binds,X,Int1_Binds,New1_gvars),
    son_new2_gvars(Int1_Binds,X,Int2_Binds,New2_gvars),
    append(New1_gvars,New2_gvars,Int_gvars),
    sort(Int_gvars,New_gvars),
    ord_subtract(New_gvars,Gvars,New),
    merge(New,Xs,Queue),
    merge(New,Gvars,GvInt),!,
    son_g_propagate(Queue,Int2_Binds,GvInt,New_Binds,GvAll).

son_new2_gvars([],_,[],[]).
son_new2_gvars([(Y,Bind)|Rest],X,[(Y,New_bind)|New_rest],New2_gvars) :-
    son_delete_var_from_list_of_lists(Bind,X,New_bind,Ans),
    ( Ans = yes ->
        New2_gvars = [Y|Rem_gvars]
    ; New2_gvars = Rem_gvars
    ),
    son_new2_gvars(Rest,X,New_rest,Rem_gvars).

%-------------------------------------------------------------------------
% son_abs_unify(+,+,-,-)                                                 |
% son_abs_unify(Term1,Term2,Binds,Gv)                                    |
% It first obtains in Temp2 the sorted list of normalized equations      |
% corresponding to the equation Term1 = Term2.                           |
% Then for each X such that exists (X,S1,F1) and (X,S2,F2) in            |
% Temp2, it replaces them by (X [[F1|S2],[F2|S2]]) obtaining Binds.      |
% Also it obtains the set of ground variables Gv                         |
%-------------------------------------------------------------------------

son_abs_unify(Term1,Term2,Binds,Gv) :-
    son_peel(Term1,Term2,Temp1-[]),
    sort(Temp1,Temp2),
    son_collect(Temp2,Binds,Gv).

%-------------------------------------------------------------------------
% son_peel(+,+,-)                                                        |
% son_peel(Term1,Term2,Binds)                                            |
% It obtains in Binds the list of normalized equations corresponding to  |
% the equation Term1 = Term2. Those normalized equations have the form:  |
% (X,Xs,Flag). It corresponds to an equation X = Term, in which S is the |
% set of variables in Term, and Flag is 'yes' if Term is linear or 'no'  |
% if it is not.
%-------------------------------------------------------------------------

son_peel(Term1,Term2,Binds) :-
    var(Term1),!,
    son_peel_var(Term1,Term2,Binds).
son_peel(Term1,Term2,Binds) :-
    var(Term2),!,
    collect_vars_is_linear(Term1,List,Flag),
    Binds = [(Term2,List,Flag)|X]-X. 
son_peel(Term1,Term2,Binds) :- 
    Term1 == Term2, !,
    Binds = X-X.
son_peel(Term1,Term2,Binds) :-
    functor(Term1,F,N),
    functor(Term2,F,N),
    son_peel_args(Term1,Term2,0,N,Binds).

son_peel_var(Term1,Term2,Binds):-
    var(Term2),!,
    Binds = [(Term1,[Term2],yes)|X]-X.
son_peel_var(Term1,Term2,Binds):-
    collect_vars_is_linear(Term2,List,Flag),
    Binds = [(Term1,List,Flag)|X]-X.

son_peel_args(_,_,N1,N,Binds) :-
    N1 = N, !,
    Binds = X-X.
son_peel_args(Term1,Term2,N1,N,Binds) :-
    N2 is N1 + 1,
    arg(N2,Term1,A1),
    arg(N2,Term2,A2),
    son_peel(A1,A2,Bind1),
    son_peel_args(Term1,Term2,N2,N,Bind2),
    append_dl(Bind1,Bind2,Binds).

%-------------------------------------------------------------------------
% son_collect(+,-,-)                                                     |
% son_collect(OldBinds,Binds,Gv)                                         |
% For each X such that exists (X,S1,F1) and (X,S2,F2) in OldBinds, it    |
% replaces them by (X [[F1|S2],[F2|S2]]) obtaining Binds.                |
% Also it obtains the set of ground variables Gv i.e. those which        |
% s.t. (X,[],_) appears in OldBinds                                      |
%-------------------------------------------------------------------------

son_collect([],[],[]).
son_collect([(X1,List1,Flag1),(X2,List2,Flag2)|Rest],Binds,Gv) :-
    test_ground(List1,X1,Gv,G_rest),
    insert(List1,Flag1,NewList),
    ( X1 == X2 ->
        son_collect([(X2,List2,Flag2)|Rest],[(X2,List)|Bind],G_rest),
        Binds = [(X1,[NewList|List])|Bind]
    ; son_collect([(X2,List2,Flag2)|Rest],Bind,G_rest),
      Binds = [(X1,[NewList])|Bind]
    ).
son_collect([(X,List,Flag)],[(X,[NewList])],Gv):-
    insert(List,Flag,NewList),
    test_ground(List,X,Gv,[]).

test_ground([],X1,[X1|G_rest],G_rest).
test_ground([_|_],_,G_rest,G_rest).

%-------------------------------------------------------------------------
% unify_list_binds(+,+,+,-)                                              |
% unify_list_binds(Binds,Sh,NonLinear,NewSh)                             |
% It performs the abstract unification for each binding given in Binds   |
% starting from Sh and the list of non linear variables NonLinear in Sh. |
%-------------------------------------------------------------------------

unify_list_binds([],Sh,_,Sh).
unify_list_binds([(X,List)|Xs],Sh,NonLinear,NewSh):-
    compute_abstract(List,X,NonLinear,Sh,NewNonLinear,TempSh),
    unify_list_binds(Xs,TempSh,NewNonLinear,NewSh).

%-------------------------------------------------------------------------
% compute_abstract(+,+,+,+,-,-)                                          |
% compute_abstract(Yss,X,NonLinear,Share,NewNonLinear,NewSh)             |
% Performs the unification for each binding given in Yss.                |
%-------------------------------------------------------------------------

compute_abstract([],_,NonLinear,Sh,NonLinear,Sh).
compute_abstract([Ys|Yss],X,NonLinear,Sh,NewNonLinear,NewSh):-
    compute_one(Ys,X,NonLinear,Sh,TempNonLinear,TempSh),
    compute_abstract(Yss,X,TempNonLinear,TempSh,NewNonLinear,NewSh).


%-------------------------------------------------------------------------
% compute_one(+,+,+,+,-,-)                                               |
% compute_one(Ys,X,NonLinear,Sh,NewNonLinear,NewSh) performs the         |
% unification represented by X and Ys. It does the following:            |
%   - If X is a nonlinear variable in Sh (appears in NonLinear):         |
%         - inserts X in Ys obtaining Vars.                              |
%         - obtains the (Vars)^2, i.e. the list of (Y,Z) for each        |
%           Y,Z (possibly the same variable) in Vars. This is            |
%           the abstraction of the equation                              |
%         - Finally it adds this abstraction with Sh obtaining           |
%           The new Sh and the new list of non linear variables          |
%   - If X is a linear variable in Sh:                                   |
%         - obtains the the list of (X,Y) for each                       |
%           Y in Vars obtaining TemSubs. Also it obtains in Flag the     |
%           atom indicating if the Term to which X is bound (i.e. the Term
%           to which the set of variables Ys belongs) is linear or not   |
%         - Depending if the Term is linear or not, it inserts [X]       |
%           in TempSubs, obtaining Subs. This is the abstraction.        |
%         - Finally it adds this abstraction with Sh obtaining           |
%           The new Sh and the new list of non linear variables          |
%-------------------------------------------------------------------------


compute_one(Ys,X,NonLinear,Sh,NewNonLinear,NewSh):-
    ord_member(X,NonLinear),!,
    eliminate_flag_insertx(Ys,X,Vars),
    couples_and_singletons(Vars,Sh1,[]),
    son_unify_each(Sh1,Sh,[],NewNonLinear,NewSh).
compute_one(Ys,X,NonLinear,Sh,NewNonLinear,NewSh):-
    ord_setproduct_linear([X],Ys,TempSubs,Flag),
    decide_linearx(Flag,X,Ys,NonLinear,Sh,TempSubs,Sh1),
    son_unify_each(Sh1,Sh,[],NewNonLinear,NewSh).


eliminate_flag_insertx([_],X,[X]):- !.
eliminate_flag_insertx([Y|Ys],X,Vars):-
    X @< Y, !,
    Vars = [X,Y|Rest],
    eliminate_flag(Ys,Rest).
eliminate_flag_insertx([Y|Ys],X,[Y|Vars]):-
    eliminate_flag_insertx(Ys,X,Vars).

eliminate_flag([_],[]):- !.
eliminate_flag([Y|Ys],[Y|Rest]):-
    eliminate_flag(Ys,Rest).

%-------------------------------------------------------------------------
% ord_setproduct_linear(+,+,-,-)                                         |
% ord_setproduct_linear(Set1, Set2, SetProduct,Flag)                     |
% is true when SetProduct is the cartesian product of Set1 and Set2. The |
% product is represented as pairs [Elem1,Elem2], where Elem1 is an element
% from Set1 and Elem2 is an element from Set2. It also returns in Flag   |
% the last element of the list if it is not a variable.                  |
%-------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

ord_setproduct_linear([], _, [],_).
ord_setproduct_linear([Head|Tail], Set, SetProduct,Flag)  :-
    ord_setproduct_linear(Set, Head, SetProduct, Rest,Flag),
    ord_setproduct_linear(Tail, Set, Rest,Flag).

ord_setproduct_linear([Head|_], _, SetProduct, Rest, Flag) :-
    nonvar(Head),!,
    SetProduct = Rest,
    Flag = Head.
ord_setproduct_linear([Head|Tail], X, [Set|TailX], Tl,Flag) :-
    sort([Head,X],Set),
    ord_setproduct_linear(Tail, X, TailX, Tl,Flag).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% decide_linearx(+,+,+,-,-)                                              |
% decide_linearx(Flag,X,Set,NonLinear,TempSubs,Subs)                     |
% depending on if the Term is linear or not, it inserts [X] in TempSubs, |
% obtaining Subs. If Flag is 'no' the term is non linear in Sh. If the   |
% Flag is 'yes' it cheks if there is at least a variable in term (Set),  |
% which is non linear. Otherwise, [X] is not inserted.                   |
%-------------------------------------------------------------------------

decide_linearx(no,X,_,_,_,TempSubs,Subs):-
    insert(TempSubs,[X],Subs).
decide_linearx(yes,X,Set,NonLinear,_,TempSubs,Subs):-
    ord_intersect(Set,NonLinear),!,
    insert(TempSubs,[X],Subs).
decide_linearx(yes,X,Set,_,Sh,TempSubs,Subs):-
    son_project_subst(Sh,Set,Sh_projected),
    at_least_one_couple(Sh_projected),!,
    insert(TempSubs,[X],Subs).
decide_linearx(yes,_,_,_,_,Subs,Subs).


at_least_one_couple([X|_]):-
    X = [_,_],!.
at_least_one_couple([_|Xs]):-
    at_least_one_couple(Xs).

%------------------------------------------------------------------------- |
% son_unify_each(+,+,+,-,-)                                                |
% son_unify_each(S1h,Sh2,[],NewNonLinear,NewSh)                            |
% It obtains the abstract substitution which results from adding the       |
% information contained in Sh1 to Sh2. This is done by adding each couple  |
% in Sh1 to [] recursively. At the end it is merged with Sh into NewSh and |
% the nonlinear variables of NewSh are collected in NewNonLinear.          |
% Since the groundness propagation has been made before, there is no ground|
% variable in Unif_Sh.                                                     |
%------------------------------------------------------------------------- |

son_unify_each([],Sh2,Temp,NonLinear,NewSh):-
    merge(Sh2,Temp,NewSh),
    collect_singletons(NewSh,NonLinear).
son_unify_each([Xs|Xss],Sh2,Temp,NewNonLinear,NewSh):-
    son_unify_one(Xs,Sh2,Temp1),
    merge(Temp1,Temp,Temp2),
    son_unify_each(Xss,Sh2,Temp2,NewNonLinear,NewSh).

%------------------------------------------------------------------------- |
% son_unify_one(+,+,-)                                                     |
% son_unify_one(Element,Sh,Temp)                                           |
% It obtains the abstract substitution which results from adding the       |
% information contained in Element to Sh. Element can be a singleton or a  |
% couple. Note that the resulting abstract information will not be (by now)|
% added to Sh. This is because each couple need to deal just with the      |
% information contained in Sh BEFORE adding the information of the rest of |
% couples (in order not to lose information.                               |
% If it is the singleton [X]:                                              |
%      - For all Y,Z (possible the same) such that [X,Y],[X,Z] is in       |
%        Sh, [Y,Z] must be in Temp (note that then for all Y               |
%        such that [X,Y] exists in Sh, [Y] will be added. Finally,         |
%        [X] will be also added.                                           |
% If it is the couple [X,Y]:                                               |
%      - For all Z,W (possible the same) such that [X,Z],[Y,W] is in       |
%        Sh, [Z,W] must be in Temp (note that then for all U               |
%        such that [X,U],[Y,U] exists in Sh, [U] will be added.            |
%        Finally, [X,Y] will be also added.                                |
%        (Note that if X or Y are nonlinear, this information is not       |
%        propagated at this step. There must be another element [X] or [Y] |
%        and another call to son_unify_one with they as arguments)         |
%------------------------------------------------------------------------- |

son_unify_one([X],Sh,Temp):-
    ord_split_lists(Sh,X,Interesting,_),
    varset([X|Interesting],Vars),
    couples_and_singletons(Vars,Temp,[]).
son_unify_one([X,Y],Sh,Temp):-
    ord_split_lists(Sh,X,IntersectX,_),
    varset([X|IntersectX],VarsX),
    ord_split_lists(Sh,Y,IntersectY,_),
    varset([Y|IntersectY],VarsY),
    setproduct(VarsY,VarsX,Temp1),
    sort(Temp1,Temp).

%------------------------------------------------------------------------- |
% son_unify_each_exit(+,+,+,-)                                             |
% son_unify_each_exit(Sh1,Sh2,[],NewSh)                                    |
% Identical to son_unify_each/5 but without computing the set of nonlinear |
% variables since it is not needed in the exit to success operation.       |
%------------------------------------------------------------------------- |

son_unify_each_exit([],Sh2,Temp,NewSh):-
    merge(Sh2,Temp,NewSh).
son_unify_each_exit([Xs|Xss],Sh2,Temp,NewSh):-
    son_unify_one(Xs,Sh2,Temp1),
    merge(Temp1,Temp,Temp2),
    son_unify_each_exit(Xss,Sh2,Temp2,NewSh).

%-------------------------------------------------------------
%  predicates for manipulation of variables
%-------------------------------------------------------------

son_delete_var_from_list_of_lists([],_,[],no).
son_delete_var_from_list_of_lists([Ys|Yss],X,List_of_lists,Ans) :-
    ord_delete(Ys,X,New_Ys),
    ( empty(New_Ys) ->
        Ans = yes,
        List_of_lists = New_Yss
    ; Ans = Ans1,
      List_of_lists = [New_Ys|New_Yss]
     ),
    son_delete_var_from_list_of_lists(Yss,X,New_Yss,Ans1).
 
empty([]).
empty([X]):- nonvar(X), !. 

%------------------------------------------------------------------------- |
% It gives the adecuate abstract substitution 
% resulting of the unification of A and B when ==(A,B) was called.
% If neither X nor Term in one binding is ground, since they have to 
% be identicals (==), each set S of the sharing domain have to 
% satisfied that X is an element of S if and only if at least one 
% variable in Term appears also in S. Therefore, each set in which 
% either only X or only variables of Term appear, has to be eliminated.
%------------------------------------------------------------------------- |


son_make_reduction([],_,[],[]).
son_make_reduction([(X,VarsTerm)|More],(Gv,Sh),TGv,Eliminate):-
    ord_member(X,Gv), !,
    son_make_reduction(More,(Gv,Sh),TempGv,Eliminate),
    append(VarsTerm,TempGv,TGv).
son_make_reduction([(X,VarsTerm)|More],(Gv,Sh),[X|TGv],Eliminate):-
    ord_subset(VarsTerm,Gv), !,
    son_make_reduction(More,(Gv,Sh),TGv,Eliminate).
son_make_reduction([(X,[Y])|More],(Gv,Sh),TGv,Eliminate):-
    var(Y), !,
    son_make_reduction_vars(X,Y,(Gv,Sh),TGv1,TElim1),
    son_make_reduction(More,(Gv,Sh),TempGv,TempElim),
    append(TempGv,TGv1,TGv),
    append(TElim1,TempElim,Eliminate).
son_make_reduction([(X,VarsTerm)|More],(Gv,Sh),TGv,Eliminate):-
    ord_subtract(VarsTerm,Gv,List),
    ord_split_lists(Sh,X,IntersectX,NotIntersect),
    varset(IntersectX,VarsX),
    ord_subtract(VarsX,[X],VarsX1),
    son_make_reduction_term(List,X,VarsX1,NotIntersect,Sh,NewGv,NewElim),
    son_make_reduction(More,(Gv,Sh),TGv1,TElim1),
    append(TGv1,NewGv,TGv),
    append(NewElim,TElim1,Eliminate).


son_make_reduction_vars(X,Y,(_,Sh),[],NewEliminate):-
    sort([[X],[Y]],List),
    ord_intersection(List,Sh,Temp), 
    test_temp(Temp,List),
    ord_split_lists(Sh,X,IntersectX,NotIntersect),
    varset(IntersectX,VarsX),
    ord_member(Y,VarsX),!,
    ord_split_lists(NotIntersect,Y,IntersectY,_),
    varset(IntersectY,VarsY),
    sort([X,Y],Vars),
    ord_subtract(VarsX,Vars,VarsX1),
    ord_union_diff(VarsY,VarsX1,_,Difference),
    setproduct(Vars,Difference,NewEliminate).
son_make_reduction_vars(X,Y,_,Vars,[]):-
    sort([X,Y],Vars).

test_temp([],_).
test_temp([X|Xs],List):-
    [X|Xs] == List.

son_make_reduction_term([],_,_,_,_,[],[]).
son_make_reduction_term([Y|Ys],X,VarsX,NotIntersectX,Sh,NewGv,NewSh):-
    sort([[X],[Y]],List),
    ord_intersection(List,Sh,Temp), 
    Temp \== [[Y]],
    ord_member(Y,VarsX),!,
    ord_split_lists(NotIntersectX,Y,IntersectY,_),
    varset(IntersectY,VarsY),
    ord_subtract(VarsY,VarsX,Difference),
    setproduct([Y],Difference,Product),
    son_make_reduction_term(Ys,X,VarsX,NotIntersectX,Sh,NewGv,NewSh1),
    append(Product,NewSh1,NewSh).
son_make_reduction_term([Y|Ys],X,VarsX,NotIntersectX,Sh,[Y|NewGv],NewSh):-
    son_make_reduction_term(Ys,X,VarsX,NotIntersectX,Sh,NewGv,NewSh).

% -------------------------------------------------------------------------
% AUXILIARY
% -------------------------------------------------------------------------

%-------------------------------------------------------------------------
% couples(+,-,+/-)                                                       |
% couples(Xs,Xss,Tail)                                                   |
% Obtains Xss = { [X,Y] | X,Y in Xs }. If X=Y then [X,X] in Xss.         |
% Note that Xss is an incomplete list.                                   |
%-------------------------------------------------------------------------

couples([],Xss,Xss).
couples([X|Xs],Xss,Tail):-
    each_couple(Xs,X,Xss,Tail0),
    couples(Xs,Tail0,Tail).

each_couple([],_,Yss,Yss).
each_couple([Y|Ys],X,[[X,Y]|Yss],Tail):-
    each_couple(Ys,X,Yss,Tail).
    
%-------------------------------------------------------------------------
% couples_and_singletons(+,-,+/-)                                        |
% couples_and_singletons(Xs,Xss,Tail)                                    |
% Obtains Xss = { [X,Y] | X,Y in Xs }. If X=Y then [X] in Xss.           |
% Note that Xss is an incomplete list.                                   |
%-------------------------------------------------------------------------

couples_and_singletons([],Xss,Xss).
couples_and_singletons([X|Xs],[[X]|Xss],Tail):-
    each_couple(Xs,X,Xss,Tail0),
    couples_and_singletons(Xs,Tail0,Tail).

%-------------------------------------------------------------------------
% collect_vars_is_linear(+,-,-)                                          |
% collect_vars_is_linear(Term,Xs,Flag)                                   |
% Collects variables appearing in Term. Flag will be "yes" if Term is    |
% linear and "no" if it is not.                                          |
%-------------------------------------------------------------------------

collect_vars_is_linear(Term,Xs,Flag) :- 
    collect_vars_is_linear1(Term,[],Xs,TempFlag),
    decide_flag(TempFlag,Flag).

collect_vars_is_linear1(Term,Vars,NewVars,Flag) :- 
    var(Term),!, 
    look_for_linear(Term,Vars,Flag),
    insert(Vars,Term,NewVars).
collect_vars_is_linear1(Term,Temp_vars,Vars,Flag) :-
    functor(Term,_,A),
    go_inside_is_linear(A,Term,Temp_vars,Vars,Flag),!.
collect_vars_is_linear1(_,V,V,_) :- !.

look_for_linear(Term,Vars,Flag):-
    ord_member(Term,Vars), !,
    Flag = no.
look_for_linear(_,_,_).

go_inside_is_linear(0,_,V,V,_) :- !.
go_inside_is_linear(N,T,V,Vars,Flag) :-
    Nth is N-1,
    go_inside_is_linear(Nth,T,V,V1,Flag),
    arg(N,T,ARG),
    collect_vars_is_linear1(ARG,V1,Vars,Flag).

decide_flag(Term,Flag):- var(Term),!,Flag = yes.
decide_flag(no,no).
