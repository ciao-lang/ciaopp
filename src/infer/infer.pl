:- module(infer,
    [ get_info/5,
      get_absint/4,
      type2measure/3,
      type_holds/3,
      type_fails/3,
      get_memo_lub/5,
      get_completes_lub/6,
      get_completes/4,
      kind_of_info/7  %% JNL
    ],
    [assertions, datafacts, ciaopp(ciaopp_options)]).

:- use_module(ciaopp(infer/infer_db),  [inferred/3]).
:- use_module(ciaopp(infer/infer_dom), [asub_to_props/4, knows_of/2]).
:- use_module(ciaopp(infer/inferseff), [side_effect_builtin/2]).
:- use_module(ciaopp(infer/vartypes),  [get_vartype/4]).

:- use_module(typeslib(typeslib), [
    dz_type_included/2, insert_rule/2, new_type_symbol/1]).
:- use_module(ciaopp(plai/domains), 
    [abs_sort/3,asub_to_info/5,call_to_entry/10,
     compute_lub/3, %do_compute_lub/3,
     obtain_info/5,
     asub_to_native/6,
     needs/2
    ]).
:- use_module(ciaopp(plai/plai_db)).
:- use_module(ciaopp(pool)).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3, predkey_from_sg/2]).

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars),  [varset/2]).
:- use_module(ciaopp(preprocess_flags),  [current_pp_flag/2]).

%------------------------------------------------------------------------%
:- doc(title,"Analysis Information Server").

:- doc(module,"This module provides the other parts of the compiler
    with the information they require on properties of the program,
    either inferred or from the assertions.").

:- doc(bug,"1. Needs major revision. Specially for types.").
:- doc(bug,"2. Add predicates for generic access to the info: if there
    is no analysis info, should go to the trusts.").
:- doc(bug,"3. Check whether fail or return void.").
:- doc(bug,"4. Have to put in common with prepare_ai_ouput").
:- doc(bug,"5. Solve the clash of compute_lub, do_compute_lub and 
    compute_lub_el").
:- doc(bug,"6. Check the type names used in type2measure2_").

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

get_absint(pred,AbsInt,Goal,(Proj,Prime)):- 
    current_pp_flag(collapse_ai_vers,on),!,
    predkey_from_sg(Goal,Key),
    get_completes_lub(Key,Goal,AbsInt,yes,Proj,Prime).
get_absint(pred,AbsInt,Goal,(Proj,Prime)):- !,
    predkey_from_sg(Goal,Key),
    get_completes(Key,Goal,AbsInt,Completes),
    get_proj_prime_pair(Completes,Key,Goal,Proj,Prime).

get_absint(Key,AbsInt,Vars,ASub):-
    current_pp_flag(collapse_ai_vers,on),!,
    get_memo_lub(Key,Vars,AbsInt,yes,ASub).
get_absint(Key,AbsInt,Vars,ASub):-
    get_memo_entry(Key,Vars,AbsInt,ASub0),
    %LUB of successes
    do_compute_lub(ASub0,AbsInt,ASub).


%------------------------------------------------------------------------%
% get_info(Form,Level,Key,Aux,Info)
% what's the available Info about Form at point Key given Aux?

:- if(defined(has_ciaopp_cost)).
:- use_module(domain(resources/plai2infer)).
:- endif.

get_info(vartypes,pred,Key,Goal,(Call,Succ)):- !,
    get_vartype(Key,Goal,Call,Succ).
get_info(seff,pred,_Key,Goal,Type):- !,
    get_info_seff(Goal,Type).
get_info(nonfail,Pred,Key,Goal,Info):-
    get_info(nfg,Pred,Key,Goal,Info),!.
get_info(nonfail,Pred,Key,Goal,Info):-   %%% JNL 
    get_info(nf,Pred,Key,Goal,Info).
get_info(nf,pred,_Key,Goal,Info):-       %%% JNL 
    current_fact(complete(_,nf,Goal0,_,LPrime,_,_)),
    compute_lub(nf,LPrime,Abs),
    variant(Goal,Goal0),
    asub_to_props(nf,Goal,Abs,Info).
get_info(nf,point,Key,Goal,Info):- !,
    get_memo_lub(Key,_Vars,nf,yes,Asub),
    ( Asub == '$bottom' ->
        Info = [fails(Goal)]
    ;
        asub_to_native(nf,Asub,Goal,yes,_A,Info) ).
get_info(trusted,_Pred,_Key,_Goal,[]):- !. % not implemented yet!!!!
get_info(Prop,pred,_Key,Goal,Info):- % inferred is pred level % TODO:[new-resources] move later! add cuts!
    current_fact(inferred(Prop,Goal0,Abs)),
    variant(Goal,Goal0),
    asub_to_props(Prop,Goal,Abs,Info).
:- if(defined(has_ciaopp_cost)).
get_info(res_plai,pred,Key,Goal,Info):-
    current_fact(complete(Key,res_plai,Goal0,X1,LPrime,X2,X3)),
    X2 \== no, % it is not a builtin ??
    translate_resource_info(complete(Key,res_plai,Goal0,X1,LPrime,_,X3),inferred(_DDD,GoalInf,Abs)),
    %current_fact(inferred(Prop,Goal0,Abs)),
    variant(Goal,GoalInf),
    asub_to_props(resources,Goal,Abs,Info).
    %_Info = [complete(GoalInf,MCall,[MSuccess],Key,lub)],
    %_asserta_fact(inferred(DDD,GoalInf,Abs)).
    %asub_to_props(resources,Goal,Abs,Info).
get_info(res_plai_stprf,pred,Key,Goal,Info):-
    current_fact(complete(Key,res_plai_stprf,Goal0,_X1,LPrime,X2,_X3)),
    X2 \== no, % it is not a builtin ??
    compute_lub(res_plai_stprf,LPrime, Abs),
%       translate_resource_info(complete(Key,res_plai,Goal0,X1,LPrime,_,X3),inferred(_DDD,GoalInf,Abs)),
    %current_fact(inferred(Prop,Goal0,Abs)),
    variant(Goal,Goal0),
    varset(Goal,Gv),
    asub_to_native(res_plai_stprf,Abs,Gv,no,Succ,Comps),
    Info = [Succ,Comps].
%       asub_to_props(res_plai_stprf,Goal,Abs,Info).
    %_Info = [complete(GoalInf,MCall,[MSuccess],Key,lub)],
    %_asserta_fact(inferred(DDD,GoalInf,Abs)).
    %asub_to_props(resources,Goal,Abs,Info).
:- endif.
get_info(Prop,Level,Key,Aux,Info):-
    get_info_(Level,Prop,Key,Aux,Info).

get_info_(point,Prop,Key,Vars,Info):-
    get_point_info(Prop,Key,Vars,Info_u),
    adapt_info(Prop,Info_u,Info).
get_info_(pred,Prop,Key,Goal,(Call,Succ)):-
    get_pred_info(Prop,Key,Goal,Call_u,Succ_u),
    adapt_info(Prop,Call_u,Call),
    adapt_info(Prop,Succ_u,Succ).

adapt_info(regtypes,I,I).
adapt_info(ground,I,O):- sort(I,O).
adapt_info(free,I,O):- sort(I,O).
adapt_info(is_det,I,I).

get_info_seff(Goal,Type):-
    current_fact(inferred(seff,Goal,Type)), !.
get_info_seff(Goal,Type):-
    functor(Goal,F,A),
    side_effect_builtin(F/A,Type).

get_point_info(Prop,Key,Vars,GndVars):-
    knows_of(Prop,AbsInt),
    get_memo_lub(Key,Vars,AbsInt,yes,ASub),!,
    obtain_info(AbsInt,Prop,Vars,ASub,GndVars).
get_point_info(_Prop,_Key,_Vars,[]).

get_pred_info(Prop,Key,Goal,Pre,Post):-
    current_pp_flag(collapse_ai_vers,off),!,
    knows_of(Prop,AbsInt),
    get_completes(Key,Goal,AbsInt,Completes),
    get_proj_prime_pair(Completes,Key,Goal,Proj,Prime),
    varset(Goal,Vars),
    kind_of_info(Prop,AbsInt,Vars,Proj,Prime,Pre,Post).
get_pred_info(Prop,Key,Goal,Pre,Post):-
    current_pp_flag(collapse_ai_vers,on),!,
    knows_of(Prop,AbsInt),
    get_completes_lub(Key,Goal,AbsInt,yes,Proj,Prime), !,
    varset(Goal,Vars),
    kind_of_info(Prop,AbsInt,Vars,Proj,Prime,Pre,Post).

%% Do not uncomment next line unless you verify everything is ok (EMM) !!!
% get_pred_info(_Prop,_Key,_Goal,[],[]).

get_proj_prime_pair([complete(G,Proj,[Prime|_T],K,_)|_R],K,G,Proj,Prime).
get_proj_prime_pair([complete(G,Proj,[_Prime|T],K,_)|R],K,G,Proj,Prime):-
    T \== [],
    get_proj_prime_pair([complete(G,Proj,T,K,_)|R],K,G,Proj,Prime).
get_proj_prime_pair([_|R],K,G,Proj,Prime):-
    get_proj_prime_pair(R,K,G,Proj,Prime).

kind_of_info(regtypes,AbsInt,Vars,Proj0,Prime0,Pre,Post):- !,
    ( needs(AbsInt,split_combined_domain) ->
        obtain_info(AbsInt,regtypes,Vars,Proj0,Pre0),
        obtain_info(AbsInt,regtypes,Vars,Prime0,Post0)
    ; asub_to_info(AbsInt,Proj0,Vars,Pre0,_),
      asub_to_info(AbsInt,Prime0,Vars,Post0,_)
    ),
    inline_type_names(Pre0,Pre),
    inline_type_names(Post0,Post).
kind_of_info(Prop,AbsInt,Vars,Proj,Prime,Pre,Post):-
    obtain_info(AbsInt,Prop,Vars,Proj,Pre),
    obtain_info(AbsInt,Prop,Vars,Prime,Post).

inline_type_names([T|Ts],[T1|T1s]):-
    inline_type_name(T,T1),
    inline_type_names(Ts,T1s).
inline_type_names([],[]).

inline_type_name(X=T,Type):- !,
    new_type_symbol(T1),
    insert_rule(T1,[T]),
    Type =.. [T1,X].
inline_type_name(T,T).

%------------------------------------------------------------------------%

get_memo_entry(Key,Vars,AbsInt,Subst):-
            current_fact(memo_table(Key,AbsInt,_,_,Vars,Subst)).

:- pred get_memo_lub(Key,Vars,AbsInt,Lub,ASub)
   : ( gnd(Key), term(Vars), gnd(AbsInt), var(Lub), var(ASub) )
   => ( gnd(Key), list(var,Vars), gnd(AbsInt), nonvar(Lub), nonvar(ASub) )
   # "Obtains program point info inferred by domain @var{AbsInt} at point @var{Key}.".

%? get_memo_lub('$bottom',_,_,_,'$bottom'):- !.
get_memo_lub(Key,Vars,AbsInt,Lub,ASub):-
    current_fact(memo_lub(Key,AbsInt,Lub,Vars,ASub)), !.
get_memo_lub(Key,Vars,AbsInt,Lub,ASub):-
    collect_point_info(Key,Vars,AbsInt,Lub,ASub),
    asserta_fact(memo_lub(Key,AbsInt,Lub,Vars,ASub)).

get_completes_lub(Key,Goal,AbsInt,Lub,Proj,Prime):-
    current_fact(lub_complete(Key,AbsInt,Lub,Goal,Proj,Prime)), !.
get_completes_lub(Key,Goal,AbsInt,Lub,Proj,Prime):-
    collect_complete_info(Key,Goal,AbsInt,Lub,Proj,Prime),
    asserta_fact(lub_complete(Key,AbsInt,Lub,Goal,Proj,Prime)).

%----------------------------------------------------------------------
% get_completes(+,+,+,-)
% returns a set of completes rather than their LUB;
% needed for multi-variant assertion checking
%----------------------------------------------------------------------

get_completes(Key,Goal,AbsInt,Completes):-
    findall(complete(Goal,Call,Succs,Key,Id),  
             (complete(Key,AbsInt,Goal,CallU,SuccsU,Id,_),
              sort_list_subs([CallU|SuccsU], AbsInt, [Call|Succs],[])
             % ,compute_lub(AbsInt,MVSuccs,Succs) % if we need lubbed successes
              ),
            Completes),
            Completes \== []. % TODO:[new-resources] why not empty?

%---------------------------------------------------------------------------
% collect_point_info(+,+,+,+,+,-)
% collect_point_info(Key,Vars,AbsInt,Lub,Subst)
% Subst is the LUB of all the informations obtained by the interpreter for 
% the program point indicated by Key 
%---------------------------------------------------------------------------

collect_point_info(Key,Vars,AbsInt,Lub,Subst):-
    findall(entry(Vars,Subst), 
            current_fact(memo_table(Key,AbsInt,_,_,Vars,Subst)),
            SubstList_uns),
    SubstList_uns \== [],
    sort_all_substs_lub(Lub,SubstList_uns,AbsInt,Vars,Subst).

sort_all_substs_lub(yes,SubstList_uns,AbsInt,Vars,Subst):- !,
    sort_all_substs(SubstList_uns,AbsInt,Vars,SubstList),
    do_compute_lub(SubstList,AbsInt,Subst).
sort_all_substs_lub(no,SubstList_uns,AbsInt,Vars,Substs):-
    sort_flatten_all_substs(SubstList_uns,AbsInt,Vars,Substs,[]).

% TODO: different definition at domain_dep.pl
%% May not be correct!!!
do_compute_lub([],_AbsInt,'$bottom'):- !.
do_compute_lub(SubstList,AbsInt,Subst):-
    compute_lub(AbsInt,SubstList,Subst).
    
sort_all_substs([],_AbsInt,_Vars,[]).
sort_all_substs([Entry|EntryList],AbsInt,Vars,Substs):-
    Entry=entry(Vars,Subst_uns),
    sort_list_subs(Subst_uns,AbsInt,Substs,Substs1),
    sort_all_substs(EntryList,AbsInt,Vars,Substs1).

sort_flatten_all_substs([],_AbsInt,_Vars,Tail,Tail).
sort_flatten_all_substs([Entry|EntryList],AbsInt,Vars,Substs,Tail):-
    Entry=entry(Vars,Subst_uns),
    sort_list_subs(Subst_uns,AbsInt,Substs,NewTail),
    sort_flatten_all_substs(EntryList,AbsInt,Vars,NewTail,Tail).

sort_list_subs([Subst_uns|Substs_uns],AbsInt,[Subst|Substs],Tail):-
    abs_sort(AbsInt,Subst_uns,Subst),
    sort_list_subs(Substs_uns,AbsInt,Substs,Tail).
sort_list_subs([],_AbsInt,Tail,Tail).

%---------------------------------------------------------------------------
% collect_complete_info(+,+,+,+,-,-)
% collect_complete_info(Key,Goal,AbsInt,Lub,Proj,Prime):-
% (Proj,Prime) is the unique call-pattern, LUB of all the informations
% obtained by the interpreter for the (most general) Goal indicated by Key 
%---------------------------------------------------------------------------

collect_complete_info(Key,Goal,AbsInt,Lub,Proj,Prime):-
    findall(complete(Goal,Call,Succs),
            current_fact(complete(Key,AbsInt,Goal,Call,Succs,_,_)),
            Completes),
    Completes \== [],
    varset(Goal,Gv),
    ( Lub=yes ->
      lub_of_calls(Completes,AbsInt,Goal,Gv,'$bottom','$bottom',Proj,Prime)
    ; group_calls(Completes,AbsInt,Goal,Gv,[],[],Proj,Prime)
    ).
%%      ( ( AbsInt==terms ; AbsInt==ptypes ; AbsInt==eterms ) ->
%% fails!!          simplify_step2
%%       ; true
%%      ).

lub_of_calls([],_AbsInt,_Goal,_Gov,Call,Succ,Call,Succ).
lub_of_calls([complete(Goal1,Call1,Succs)|Calls],AbsInt,Goal,Gov,
          TmpCall,TmpSucc,NCall,NSucc):-
    sort_list_subs(Succs,AbsInt,Succs_s,[]),
    compute_lub(AbsInt,Succs_s,Succ1),
    most_general_goal(Goal1,Call1,Succ1,AbsInt,Goal,Gov,Call,Succ),
    compute_lub(AbsInt,[Call,TmpCall],Call2),
    compute_lub(AbsInt,[Succ,TmpSucc],Succ2),
    lub_of_calls(Calls,AbsInt,Goal,Gov,Call2,Succ2,NCall,NSucc).

% TODO:[new-resources] missing cuts
%
% A better solution should be found anyway.
% For res_plai, fails calling call_to_entry with
% a success substitution as the call, because
% it cannot recover the success substitution of
% etermsvar.
most_general_goal(Goal1,Call1,Succ1,res_plai,Goal,Gov,Call,Succ_s):- !, % TODO:[new-resources] remove ad-hoc, add hook if needed (JF) -- see other comments like this
    abs_sort(res_plai,Call1,Call_s),
    abs_sort(res_plai,Succ1,Succ_s),
    varset(Goal1,Go1v),
    decide_call_to_entry(Call_s,res_plai,Go1v,Goal1,Gov,Goal,[],Call).
    %decide_call_to_entry(Succ_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Succ).
most_general_goal(Goal1,Call1,Succ1,res_plai_stprf,Goal,Gov,Call,Succ_s):- !, % TODO:[new-resources] remove ad-hoc, add hook if needed (JF) -- see other comments like this
    abs_sort(res_plai_stprf,Call1,Call_s),
    abs_sort(res_plai_stprf,Succ1,Succ_s),
    varset(Goal1,Go1v),
    decide_call_to_entry(Call_s,res_plai_stprf,Go1v,Goal1,Gov,Goal,[],Call).
    %decide_call_to_entry(Succ_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Succ).
% most_general_goal(Goal1,Call1,Succ1,sized_types,Goal,Gov,Call,Succ_s):-
%       abs_sort(sized_types,Call1,Call_s),
%       abs_sort(sized_types,Succ1,Succ_s),
%       varset(Goal1,Go1v),
%       decide_call_to_entry(Call_s,sized_types,Go1v,Goal1,Gov,Goal,[],Call).
    %decide_call_to_entry(Succ_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Succ).
%
% TODO: duplicated
most_general_goal(Goal1,Call1,Succ1,AbsInt,Goal,Gov,Call,Succ):-
    abs_sort(AbsInt,Call1,Call_s),
    abs_sort(AbsInt,Succ1,Succ_s),
    varset(Goal1,Go1v),
    decide_call_to_entry(Call_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Call),
    decide_call_to_entry(Succ_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Succ).

% TODO: duplicated
decide_call_to_entry('$bottom',_AbsInt,_Go1v,_Goal1,_Gov,_Goal,_,'$bottom'):-!.
decide_call_to_entry(Call_s,AbsInt,Go1v,Goal1,Gov,Goal,[],Call):-
    call_to_entry(AbsInt,Go1v,Goal1,Gov,Goal,not_provided,[],Call_s,Call,_). % TODO: add ClauseKey? (JF)

%------------------------------------------------------------------------%
% does the typing TypeList hold for Goal at point K?
%    K is in [call,succ]
%    Goal is a most general atom
%    TypeList is a list of types for variables in Goal

type_holds(K,Goal,TypeList):-
%        message("CALL: type_holds(~q, ~q, ~q) ~n", [K,Goal,TypeList]),
    functor(Goal,F,A),
    functor(Goal0,F,A),
    get_predkey(F,A,Key), %% AADEBUG
    recorded_internal(Key,complete_type(Goal0,Call,Succ),_),
    ( K == call -> TypeList0=Call ; K == succ, TypeList0=Succ ),
%        message("CALL: ~q ~n", [type_assignments_included(TypeList, Goal, TypeList0, Goal0)]),
    type_assignments_included(TypeList, Goal, TypeList0, Goal0).

%------------------------------------------------------------------------%
% is the typing TypeList false for Goal at point K?

type_fails(K,Goal,TypeList):-
    functor(Goal,F,A),
    functor(Goal0,F,A),
    get_predkey(F,A,Key), %% AADEBUG
    recorded_internal(Key,complete_type(Goal0,Call,Succ),_),
    ( K == call -> TypeList0=Call ; K == succ, TypeList0=Succ ),
    type_assignments_incompatible(TypeList0, Goal0, TypeList, Goal).


%------------------------------------------------------------------------%
% translate types to measures

% untestable type2measure/3 EMM
type2measure(Goal0,Typings0,Measures):-
    % TODO: ugly, load this type somewhere else
    %( get_type_rule('$$list',_) -> true
    %; insert_rule('$$list',[[],[term|'$$list']]) ),
    insert_rule('$$list',[[],[term|'$$list']]), % TODO: insert_rule/2 already checks if type is defined twice (JFMC)
    %
    copy_term((Goal0,Typings0),(Goal,Typings)),
    type_names(Typings),
    functor(Goal,_,A),
    type2measure_(0,A,Goal,Measures).

type_names([T|Ts]):-
    (type_of_goal(builtin(BT),T) -> true ; BT = T),
    functor(BT,F,A),
    (arg(A,BT,F)->true;true), % The variable is the last argument of parametric types (new hiord).
    type_names(Ts).
type_names([]).

type2measure_(A,A,_Type,[]).
type2measure_(N,A,Type,Measures):- N < A, !,
    N1 is N+1,
    arg(N1,Type,T),
    Measures=[M|Measures0],
    type2measure2(T,M),
    type2measure_(N1,A,Type,Measures0).

type2measure2(T,M):-
    type2measure2_(T,M), !.
type2measure2(_,size) :- !.
type2measure2(_,void).

%% Be careful whith the type names

%% Gallagher's
 %% type2measure2_(integer,int).
 %% type2measure2_(numeric,int).
 %% type2measure2_(number,int).
 %% type2measure2_(numexpr,int).
 %% 

% untestable type2measure2_/2 EMM
type2measure2_(var, size):-!.
type2measure2_('term_typing:var', size):-!.
type2measure2_(int, int):-!.
type2measure2_(num, int):-!.
type2measure2_(rat, int):-!.
type2measure2_(nnegint, int):-!.
type2measure2_(flt, int):-!.
type2measure2_(numexpr,int):-!.
type2measure2_('arithmetic:arithexpression', size):-!.
% The next clauses are not testable (yet)
type2measure2_(T, int):-
    dz_type_included(T,num),
    !.
type2measure2_(T,length):-
    dz_type_included(T,'$$list'),
    !.  % list!
type2measure2_(T, size):-
    dz_type_included(T,'arithmetic:arithexpression'),
    !.

%% length_measure((T1;T2),T):- !,
%%      length_measure0(T1,T),
%%      length_measure(T2,T).
%% length_measure(T1,T):-
%%      length_measure0(T1,T).
%% 
%% %% OJO: t1::=[any|t2], t2::=[any|t1] hacen que esto se embucle!!!
%% length_measure0([],_T).
%% length_measure0([_|T],T):- !.
%% length_measure0([_|T1],_T):-
%%      type2measure2_(T1,length).

%% % Gerda's
%% type2measure2_(numeric,int).
%% type2measure2_(list,length).
%% type2measure2_(nil,length).
%% type2measure2_(oR(T1,T2),M):-
%%      type2measure2(T1,M1),
%%      type2measure2(T2,M2),
%%      lub_measure(M1,M2,M).
%% 
%% lub_measure(M1,M2,M1):- eq_measure(M1,M2), !.
%% lub_measure(_1,_2,size).
%%  %% lub_measure(M1,M2,M2):- leq_measure(M1,M2).
%%  %% lub_measure(M1,M2,M1):- leq_measure(M2,M1).
%% 
%% eq_measure(M1,M2):- M1 == M2.
%% 
%% leq_measure(int,lenght).
%% leq_measure(int,size).
%% leq_measure(lenght,size).


