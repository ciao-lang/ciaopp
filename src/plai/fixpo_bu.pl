/*             Copyright (C)2000-2005 UPM-CLIP                          */

:- module(fixpo_bu,
    [ tp/1,
      init_fixpoint/0,
      cleanup_fixpoint/1,
      bu_output/1,      % for debugging purposes
      iterate/2,        % for debugging purposes
      debug_complete/6  % for debugging purposes
    ],
    [ assertions, datafacts, ciaopp(ciaopp_options)]).

:- use_module(engine(messages_basic)).
:- use_module(library(messages), [debug_message/2]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(sets), [ord_subtract/3]).
:- use_module(engine(runtime_control), [garbage_collect/0]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).
:- use_module(ciaopp(plai/plai_db), [complete/7, cleanup_plai_db/1]).
:- use_module(ciaopp(plai/apply_assertions_old), [cleanup_trusts/1]).
:- use_module(ciaopp(plai/domains)).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]).
:- if(defined(has_ciaopp_extra)).
:- use_module(domain(bshare/bshare), [bshare_output/0, bshare_crack/2]).
:- endif.

%------------------------------------------------------------------------%
:- doc(author,"Francisco Bueno").
:- doc(author,"Jorge Navas (Modifications to integrate it into CiaoPP)").
:- doc(module,"This module implements a bottom-up fixpoint.").

:- doc(stability, devel).

:- doc(bug,"Completely naive fixpoint.").
:- doc(bug,"Lacking treatment of assertions. In particular, does not use trusts.").
%------------------------------------------------------------------------%
:- multifile issue_debug_messages/1.
:- data issue_debug_messages/1.
%% Only for debugging purposes, uncomment these lines.
%issue_debug_messages(bshare).
%issue_debug_messages(fixpo_bu).
%------------------------------------------------------------------------%
:- data continue/0.
:- data iterate/2.

init_fixpoint:-
    retractall_fact(continue),
    retractall_fact(incr_id(_,_)).

cleanup_fixpoint(AbsInt):-
    cleanup_plai_db(AbsInt),
    cleanup_trusts(AbsInt),
    retractall_fact(iterate(_,_)),
    retractall_fact(debug_complete(_,_,_,_,_,_)),
    init_fixpoint.

tp(AbsInt):-
    pp_statistics( walltime, _ ),
    is_analysis(AbsInt),
    asserta_fact(continue),
    repeat,
       ( ( retract_fact(continue), incr_iterate(AbsInt,1) ) -> 
          trans_clause(SgKey,_R,clause(Head,Vars_u,K,Body)),
          one_iteration(SgKey,K,Head,Vars_u,Body,AbsInt),
          garbage_collect,
          fail
        ; 
          true
       ),
    !,
    pp_statistics( walltime, [ _, T1 ] ),
    is_analysis_option(AbsInt,AbsIntOpt),
    message(inform, ['{analyzed by bu using ', ~~(AbsIntOpt), ' in ', ~~(T1), ' msec}']).

one_iteration(SgKey,ClKey,Head,Vars_u,Body,AbsInt):-
    varset(Head,Hv),
    sort(Vars_u,Vars),
    ord_subtract(Vars,Hv,Fv),
    unknown_entry(AbsInt,Head,Hv,Call0),
    augment_asub(AbsInt,Call0,Fv,Call_u),
    abs_sort(AbsInt,Call_u,Call),
    show_if_debug(Call,'unknown_entry + add body vars',SgKey,AbsInt),
    one_clause_body(Body,Vars,Call,AbsInt,Exit_u),
    abs_sort(AbsInt,Exit_u,Exit),
    project(AbsInt,Head,Hv,_Vars,Exit,Prime),
    project(AbsInt,Head,Hv,_Vars,Call,Entry),
    show_if_debug(Entry,project,SgKey,AbsInt),      
    show_if_debug(Prime,project,SgKey,AbsInt),      
    store_absint(SgKey,ClKey,Head,Entry,AbsInt,Prime).

store_absint(SgKey,ClKey,Head,Entry,AbsInt,Prime1):-
    current_fact(complete(SgKey,AbsInt,H,Entry0,[Prime0],_,_),Ref),
    identical_proj(AbsInt,Head,Entry,H,Entry0),!,
    show_if_debug(Prime0,'compute_lub: first abs',SgKey,AbsInt),
    show_if_debug(Prime1,'compute_lub: second abs',SgKey,AbsInt),
    compute_lub(AbsInt,[Prime0,Prime1],Prime),
    show_if_debug(Prime,compute_lub,SgKey,AbsInt),!,
    (  identical_abstract(AbsInt,Prime,Prime0) -> 
       true
     ; 
       erase(Ref),
       update_continue(SgKey,ClKey,AbsInt,Head,Entry,Prime)
    ).
store_absint(SgKey,ClKey,Head,Entry,AbsInt,Prime):-
    update_continue(SgKey,ClKey,AbsInt,Head,Entry,Prime).

:- data debug_complete/6.
% this fact is used for debugging purposes (ClKey)
:- data key_id/2.

incr_id(AbsInt,Val):-
    retract_fact(key_id(AbsInt,V)),!,
    Val is V + 1,
    asserta_fact(key_id(AbsInt,Val)).
incr_id(AbsInt,1):-
    asserta_fact(key_id(AbsInt,1)).


update_continue(SgKey,_ClKey,AbsInt,Head,Entry,Prime):-
    current_fact(continue), !,
    asserta_fact(complete(SgKey,AbsInt,Head,Entry,[Prime],_,_)),
    incr_id(AbsInt,Id),
    asserta_fact(debug_complete(SgKey,Id,AbsInt,Head,Entry,[Prime])).
update_continue(SgKey,_ClKey,AbsInt,Head,Entry,Prime):-
    asserta_fact(continue),
    asserta_fact(complete(SgKey,AbsInt,Head,Entry,[Prime],_,_)),
    incr_id(AbsInt,Id),
    asserta_fact(debug_complete(SgKey,Id,AbsInt,Head,Entry,[Prime])).


one_clause_body(g(_,[],'$built'(_,true,_),'true/0',true),_,Entry,_AbsInt,Exit):- !,
    Exit = Entry.
one_clause_body((Atom,Body),Vars,Entry,AbsInt,Exit):- !,
    Atom=g(_Key,Sv,Info,SgKey,Sg),
    one_clause_atom(Info,SgKey,Sg,Sv,Vars,Entry,AbsInt,Entry1),
    one_clause_body(Body,Vars,Entry1,AbsInt,Exit).
one_clause_body(Atom,Vars,Entry,AbsInt,Exit):-
    Atom=g(_Key,Sv,Info,SgKey,Sg),
    one_clause_atom(Info,SgKey,Sg,Sv,Vars,Entry,AbsInt,Exit).

one_clause_atom('$built'(T,Tg,Vs),SgKey,_Sg,Sv,_Vars,Call,AbsInt,Succ):-
    body_succ_builtin(AbsInt,T,Tg,Vs,Sv,_HvFv_u,Call,Call,Succ),!,
    show_if_debug(Succ,success_builtin,SgKey,AbsInt).
one_clause_atom(_Info,SgKey,Sg,_Sv,Vars,Entry,AbsInt,Entry1):-
    current_fact(complete(SgKey,AbsInt,H,_,[Exit0],_,_)),!,
    augment_two_asub(AbsInt,Exit0,Entry,ASub_u),
    abs_sort(AbsInt,ASub_u,ASub),
    show_if_debug(ASub,augment_two_asub,SgKey,AbsInt),      
    amgu(AbsInt,Sg,H,ASub,ASub1),
    show_if_debug(ASub1,amgu,SgKey,AbsInt), 
    project(AbsInt,Sg,Vars,Vars,ASub1,Entry1),
    show_if_debug(Entry1,project,SgKey,AbsInt).

:- if(defined(has_ciaopp_extra)).
is_analysis(bshare).
:- endif.
is_analysis(share_amgu).
is_analysis(AbsInt):- 
    throw(error(unsupported_domain(AbsInt), 'fixpo_bu:is_analysis'/1)).

incr_iterate(AbsInt,Val):-
    retract_fact(iterate(AbsInt,V)),!,
    NVal is V + Val,
    asserta_fact(iterate(AbsInt,NVal)).
incr_iterate(AbsInt,Val):-
    asserta_fact(iterate(AbsInt,Val)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEBUGGING
debugging(not).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

show_if_debug(_ASub,_Op,_SgKey,_AbsInt):-
    debugging(not),!.
:- if(defined(has_ciaopp_extra)).
show_if_debug(ASub,Op,SgKey,bshare):-
    debugging(yes),!,
    ASub = (_NSh,Vars),
    bshare_crack(ASub,Sh),
    debug_message("[~q - ~q] (~q,~q) \n",[Op,SgKey,Sh,Vars]).
:- endif.
show_if_debug(Sh,Op,SgKey,share_amgu):-
    debugging(yes),!,
    debug_message("[~q - ~q] ~q \n",[Op,SgKey,Sh]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Note: This output is only for debugging purposes.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bu_output(AbsInt):-
    current_fact(iterate(AbsInt,N)),
    message(inform, ['{Number of iterations: ', ~~(N), '}']),
    bu_output_(AbsInt).
:- if(defined(has_ciaopp_extra)).
bu_output_(bshare):-
    bshare_output.
:- endif.
bu_output_(share_amgu):-
    current_fact(complete(_SgKey,share_amgu,Sg,Proj,[Prime],_Id,_Parents)),
    message(inform, ['{', ~~(Sg) ,': ', ~~(Proj), ' -> ', ~~(Prime), '}']),
    fail.
bu_output_(_).

is_analysis_option(share_amgu,share_amgu).
:- if(defined(has_ciaopp_extra)).
is_analysis_option(bshare,AbsInt):-
    current_pp_flag(bshare_option,Opt),
    atom_concat([bshare,'-',Opt],AbsInt).
:- endif.

    

