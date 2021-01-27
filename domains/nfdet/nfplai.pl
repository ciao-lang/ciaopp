:- module(nfplai, [
    nf_init_abstract_domain/1,
    nf_call_to_entry/9,
    nf_exit_to_prime/7,
    nf_project/5,
    nf_extend/5,
    nf_widen/3,
    nf_widencall/3,
    nf_compute_lub/2,
    nf_compute_clauses_lub/3,
    nf_glb/3,
    nf_eliminate_equivalent/2,
    nf_less_or_equal/2,
    nf_identical_abstract/2,
    nf_abs_sort/2,
    nf_call_to_success_fact/9,
    nf_split_combined_domain/3,
    nf_special_builtin/5,
    nf_combined_special_builtin0/2,
    nf_success_builtin/6,
    % nf_call_to_success_builtin/6,
    nf_input_interface/4,
    nf_input_user_interface/5,
    nf_asub_to_native/5,
    nf_unknown_call/4,
    nf_unknown_entry/3,
    nf_empty_entry/3,
    nf_dom_statistics/1
], [assertions,regtypes,basicmodes]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(nf).
:- dom_impl(nf, init_abstract_domain/1).
:- dom_impl(nf, call_to_entry/9).
:- dom_impl(nf, exit_to_prime/7).
:- dom_impl(nf, project/5).
:- dom_impl(nf, widencall/3).
:- dom_impl(nf, needs/1).
:- dom_impl(nf, widen/3).
:- dom_impl(nf, compute_lub/2). 
:- dom_impl(nf, compute_clauses_lub/3).
:- dom_impl(nf, identical_abstract/2).
:- dom_impl(nf, abs_sort/2).
:- dom_impl(nf, extend/5).
:- dom_impl(nf, less_or_equal/2).
:- dom_impl(nf, glb/3).
:- dom_impl(nf, eliminate_equivalent/2).
:- dom_impl(nf, call_to_success_fact/9).
:- dom_impl(nf, special_builtin/5).
:- dom_impl(nf, combined_special_builtin0/2).
:- dom_impl(nf, split_combined_domain/3).
:- dom_impl(nf, success_builtin/6).
:- dom_impl(nf, input_interface/4).
:- dom_impl(nf, input_user_interface/5).
:- dom_impl(nf, asub_to_native/5).
:- dom_impl(nf, unknown_call/4).
:- dom_impl(nf, unknown_entry/3).
:- dom_impl(nf, empty_entry/3).
:- dom_impl(nf, dom_statistics/1).

:- use_module(domain(eterms)).
:- use_module(domain(sharefree)).
:- use_module(domain(nfdet/nfabs)).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(sets), [ord_subtract/3]).
:- use_module(library(sort), [sort/2]).

% Solved: 
%:- doc(bug,"1. Some asubs carry $bottom within the nf/3 representation.").
% was because of builtins; solution: the if-then-elses in split_back

%------------------------------------------------------------------------%

%% asub('$bottom','$bottom',_Modes,_NonF):- !.
%% asub('$bottom',_Types,'$bottom',_NonF):- !.
%% asub('$bottom',_Types,_Modes,'$bottom'):- !.
asub(nf(Types,Modes,NonF),Types,Modes,NonF).

%------------------------------------------------------------------------%

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

nf_init_abstract_domain([variants,widen]) :-
    push_pp_flag(variants,off),
    push_pp_flag(widen,on).

%------------------------------------------------------------------------%
% nf_call_to_entry(+,+,+,+,+,+,+,-,-)                                    %
% nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)              %
%------------------------------------------------------------------------%

nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo):-
    asub(Proj,PTypes,PModes,PNonF),
    shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PModes,EModes,ExtraInfoModes),
    eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PTypes,ETypes,ExtraInfoTypes),
    ( ETypes = '$bottom' ->
        Entry = '$bottom'
    ; nfabs:nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PNonF,ENonF,_Extra),
      shfr_obtain_info(free,Sv,PModes,FVars),
      ord_subtract(Sv,FVars,InVars),
      asub(Entry,ETypes,EModes,ENonF)
    ),
    asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,InVars).

%------------------------------------------------------------------------%
% nf_exit_to_prime(+,+,+,+,+,-,-)                                        %
% nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                   %
%------------------------------------------------------------------------%

nf_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom'):- !.
nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    asub(Exit,ETypes,EModes,ENonF),
    asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,ExtraInfoNonF),
    shfr_exit_to_prime(Sg,Hv,Head,Sv,EModes,ExtraInfoModes,PModes),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,ETypes,ExtraInfoTypes,PTypes),
    ( PTypes = '$bottom' ->
        Prime = '$bottom'
    ; nfabs:nf_exit_to_prime(Sg,Hv,Head,Sv,ENonF,ExtraInfoNonF,PNonF),
      ( PNonF = '$bottom' ->
          Prime = '$bottom'
      ; asub(Prime,PTypes,PModes,PNonF)
      )
    ).

%------------------------------------------------------------------------%
% nf_project(+,+,+,+,-)                                                  %
% nf_project(Sg,Vars,HvFv_u,ASub,Proj)                                   %
%------------------------------------------------------------------------%

nf_project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
nf_project(Sg,Vars,HvFv_u,ASub,Proj):-
    asub(ASub,ATypes,AModes,ANonF),
    shfr_project(Sg,Vars,HvFv_u,AModes,PModes),
    eterms_project(Sg,Vars,HvFv_u,ATypes,PTypes),
    nfabs:nf_project(Sg,Vars,HvFv_u,ANonF,PNonF),
    asub(Proj,PTypes,PModes,PNonF).

%------------------------------------------------------------------------%
% nf_extend(+,+,+,+,-)                                                   %
% nf_extend(Sg,Prime,Sv,Call,Succ)                                       %
%------------------------------------------------------------------------%

nf_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
nf_extend(Sg,Prime,Sv,Call,Succ):-
    asub(Prime,PTypes,PModes,PNonF),
    asub(Call,CTypes,CModes,CNonF),
    shfr_extend(Sg,PModes,Sv,CModes,SModes),
    eterms_extend(Sg,PTypes,Sv,CTypes,STypes),
    nfabs:nf_extend(Sg,PNonF,Sv,CNonF,SNonF),
    asub(Succ,STypes,SModes,SNonF).

nf_needs(clauses_lub) :- !.
nf_needs(split_combined_domain) :- !.
nf_needs(X) :-
    eterms_needs(X), !.
nf_needs(X) :-
    shfr_needs(X).

%------------------------------------------------------------------------%
% nf_widen(+,+,-)                                                        %
% nf_widen(ASub1,ASub2,ASub)                                             %
%------------------------------------------------------------------------%

nf_widen('$bottom',ASub1,ASub):- !, ASub=ASub1.
nf_widen(ASub0,'$bottom',ASub):- !, ASub=ASub0.
nf_widen(ASub0,ASub1,ASub):-
    asub(ASub0,ATypes0,AModes0,ANonF0),
    asub(ASub1,ATypes1,AModes1,ANonF1),
    shfr_compute_lub([AModes0,AModes1],AModes),
    eterms_widen(ATypes0,ATypes1,ATypes),
    nfabs:nf_compute_lub([ANonF0,ANonF1],ANonF),
    asub(ASub,ATypes,AModes,ANonF).

%------------------------------------------------------------------------%
% nf_widencall(+,+,-)                                                    %
% nf_widencall(ASub1,ASub2,ASub)                                         %
%------------------------------------------------------------------------%

nf_widencall('$bottom',ASub1,ASub):- !, ASub=ASub1.
nf_widencall(ASub0,'$bottom',ASub):- !, ASub=ASub0.
nf_widencall(ASub0,ASub1,ASub):-
    asub(ASub0,ATypes0,_AModes0,_ANonF0),
    asub(ASub1,ATypes1,AModes1,ANonF1),
    % assuming _AModes0 =< AModes1 and _ANonF0 =< ANonF1
    eterms_widencall(ATypes0,ATypes1,ATypes),
    asub(ASub,ATypes,AModes1,ANonF1).

%------------------------------------------------------------------------%
% nf_compute_lub(+,-)                                                    %
% nf_compute_lub(ListASub,Lub)                                           %
%------------------------------------------------------------------------%

nf_compute_lub(ListASub,Lub):-
    split(ListASub,LTypes,LModes,LNonF),
    shfr_compute_lub(LModes,LubModes),
    eterms_compute_lub(LTypes,LubTypes),
    nfabs:nf_compute_lub(LNonF,LubNonF),
    asub(Lub,LubTypes,LubModes,LubNonF).

split([],[],[],[]).
split(['$bottom'|ListASub],LTypes,LModes,LNonF):- !,
    split(ListASub,LTypes,LModes,LNonF).
split([ASub|ListASub],[ATypes|LTypes],[AModes|LModes],[ANonF|LNonF]):-
    asub(ASub,ATypes,AModes,ANonF),
    split(ListASub,LTypes,LModes,LNonF).

nf_split_combined_domain(ListASub,[LTypes,LModes,LNonF],[eterms,shfr,nf]):-
    ( var(LTypes) ->
        split(ListASub,LTypes,LModes,_LNonF),
        LNonF=ListASub
    ; split_back(ListASub,LTypes,LModes,LNonF)
    ).

split_back([],[],[],[]).
split_back([ASub|ListASub],[ATypes|LTypes],[AModes|LModes],[ASubNonF|LNonF]):-
    ( ATypes == '$bottom' -> ASub = '$bottom'
    ; AModes == '$bottom' -> ASub = '$bottom'
    ; asub(ASub,ATypes,AModes,ANonF),
      asub(ASubNonF,_ATypes,_AModes,ANonF)
    ),
    split_back(ListASub,LTypes,LModes,LNonF).

%------------------------------------------------------------------------%
% nf_compute_clauses_lub(+,-)                                            %
% nf_compute_clauses_lub(ListASub,Lub)                                   %
%------------------------------------------------------------------------%

nf_compute_clauses_lub(['$bottom'],_Proj,[]):- !.
nf_compute_clauses_lub([ASub],Proj,[Lub]):-
    asub(ASub,ATypes,AModes,ANonFList),
    asub(Proj,PTypes,PModes,_PNonFList),
    compute_modetypes(PTypes,PModes,_Head,ModeTypes),
    nf_compute_covering(ModeTypes,ANonFList,LubNonF),
    asub(Lub,ATypes,AModes,LubNonF).

compute_modetypes(Types,Modes,Head,MTypes):-
    % shfr_obtain_info(free,_Vars,Modes,FVars), % PLG
    shfr_obtain_info(free,Modes,FVars), % Added PLG
    sort(Types,Types_s),
    compute_modetypes0(Types_s,FVars,Vars,ModeTypes),
    Head =.. [p|Vars],
    MTypes =.. [p|ModeTypes].

compute_modetypes0([],_FVars,[],[]).
compute_modetypes0([Var:(_,T)|Types],FVars,[Var|Vars],[M:T|ModeTypes]):-
    get_mode(Var,FVars,M),
    compute_modetypes0(Types,FVars,Vars,ModeTypes).

get_mode(Var,FVars,M):-
    memberchk(Var,FVars), !,
    M = out.
get_mode(_Var,_GVars,in).

%------------------------------------------------------------------------%
% nf_glb(+,+,-)                                                          %
% nf_glb(ASub0,ASub1,Glb)                                                %
%------------------------------------------------------------------------%

nf_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
nf_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
nf_glb(ASub0,ASub1,Glb):-
    asub(ASub0,ATypes0,AModes0,ANonF0),
    asub(ASub1,ATypes1,AModes1,ANonF1),
    shfr_glb(AModes0,AModes1,GModes),
    eterms_glb(ATypes0,ATypes1,GTypes),
    nfabs:nf_glb(ANonF0,ANonF1,GNonF),
    asub(Glb,GTypes,GModes,GNonF).

%------------------------------------------------------------------------%

nf_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)

%------------------------------------------------------------------------%
% nf_less_or_equal(+,+)                                                  %
% nf_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%

nf_less_or_equal('$bottom','$bottom'):- !.
nf_less_or_equal(ASub0,ASub1):-
    asub(ASub0,ATypes0,AModes0,ANonF0),
    asub(ASub1,ATypes1,AModes1,ANonF1),
    shfr_less_or_equal(AModes0,AModes1),
    eterms_less_or_equal(ATypes0,ATypes1),
    nfabs:nf_less_or_equal(ANonF0,ANonF1).

%------------------------------------------------------------------------%
% nf_identical_abstract(+,+)                                             %
% nf_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%

nf_identical_abstract('$bottom','$bottom'):- !.
nf_identical_abstract(ASub0,ASub1):-
    asub(ASub0,ATypes0,AModes0,ANonF0),
    asub(ASub1,ATypes1,AModes1,ANonF1),
    AModes0 == AModes1,
    eterms_identical_abstract(ATypes0,ATypes1),
    nfabs:nf_identical_abstract(ANonF0,ANonF1).

%------------------------------------------------------------------------%
% nf_abs_sort(+,-)                                                           %
% nf_abs_sort(ASub0,ASub1)                                                   %
%------------------------------------------------------------------------%

nf_abs_sort('$bottom','$bottom'):- !.
nf_abs_sort(ASub0,ASub1):-
    asub(ASub0,ATypes0,AModes0,ANonF0),
    shfr_abs_sort(AModes0,AModes1),
    eterms_abs_sort(ATypes0,ATypes1),
    nfabs:nf_abs_sort(ANonF0,ANonF1),
    asub(ASub1,ATypes1,AModes1,ANonF1).

%------------------------------------------------------------------------%
% nf_call_to_success_fact(+,+,+,+,+,+,+,-,-)                               %
% nf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)            %
%-------------------------------------------------------------------------

nf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    asub(Call,CTypes,CModes,CNonF),
    asub(Proj,PTypes,PModes,PNonF),
    shfr_call_to_success_fact(Sg,Hv,Head,K,Sv,CModes,PModes,RModes,SModes),
    eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,CTypes,PTypes,RTypes,STypes),
    nfabs:nf_call_to_success_fact(Sg,Hv,Head,K,Sv,CNonF,PNonF,RNonF,SNonF),
    asub(Prime,RTypes,RModes,RNonF),
    asub(Succ,STypes,SModes,SNonF).


%-------------------------------------------------------------------------
% nf_special_builtin(+,+,+,-,-)                                          |
% nf_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                     |
%-------------------------------------------------------------------------

nf_special_builtin(SgKey,Sg,_Subgoal,SgKey,Sg):-
    nfabs:nf_special_builtin(SgKey).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [special_builtin/6]).

nf_combined_special_builtin0(SgKey,Domains) :-
    % TODO: refactor (define a nondet pred with combined domains instead)
    ( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nf]
    ; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nf]
    ; special_builtin(nf,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nf]
    ; fail
    ).

%-------------------------------------------------------------------------
% nf_success_builtin(+,+,+,+,+,-)                                        |
% nf_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                          |
%-------------------------------------------------------------------------

nf_success_builtin(Type,_Sv_u,Sg,HvFv_u,Call,Succ):-
    asub(Call,Types,Modes,CallNonF),
    nfabs:nf_success_builtin(Type,Modes,Sg,HvFv_u,CallNonF,SuccNonF),
    asub(Succ,Types,Modes,SuccNonF).

%-------------------------------------------------------------------------
% nf_call_to_success_builtin(+,+,+,+,+,-)                                %
% nf_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)                 %
%-------------------------------------------------------------------------
% Not used

%------------------------------------------------------------------------%
% nf_input_interface(+,+,+,-)                                            %
% nf_input_interface(InputUser,Kind,StructI,StructO)                     %
%------------------------------------------------------------------------%

nf_input_interface(InputUser,Kind,StructI,StructO):-
    ( nonvar(Kind) ->
        KModes=Kind, KTypes=Kind, KNonF=Kind
    ; true
    ),
    asub(StructI,ITypes,IModes,INonF),
    shfr_input_interface_(InputUser,KModes,IModes,OModes),
    eterms_input_interface_(InputUser,KTypes,ITypes,OTypes),
    nf_input_interface_(InputUser,KNonF,INonF,ONonF),
    asub(StructO,OTypes,OModes,ONonF).

shfr_input_interface_(InputUser,Kind,IModes,OModes):-
    shfr_input_interface(InputUser,Kind,IModes,OModes), !.
shfr_input_interface_(_InputUser,_Kind,IModes,IModes).

eterms_input_interface_(InputUser,Kind,ITypes,OTypes):-
    eterms_input_interface(InputUser,Kind,ITypes,OTypes), !.
eterms_input_interface_(_InputUser,_Kind,ITypes,ITypes).

nf_input_interface_(InputUser,Kind,INonF,ONonF):-
    nfabs:nf_input_interface(InputUser,Kind,INonF,ONonF), !.
nf_input_interface_(_InputUser,_Kind,INonF,INonF).

%------------------------------------------------------------------------%
% nf_input_user_interface(+,+,-,+,+)                                     %
% nf_input_user_interface(InputUser,Qv,ASub)                             %
%------------------------------------------------------------------------%

nf_input_user_interface(Struct,Qv,ASub,Sg,MaybeCallASub):-
    asub(Struct,Types,Modes,NonF),
    shfr_input_user_interface(Modes,Qv,AModes,Sg,MaybeCallASub),
    eterms_input_user_interface(Types,Qv,ATypes,Sg,MaybeCallASub),
    nfabs:nf_input_user_interface(NonF,Qv,ANonF,Sg,MaybeCallASub),
    asub(ASub,ATypes,AModes,ANonF).

%------------------------------------------------------------------------%
% nf_asub_to_native(+,+,+,-,-)                                           %
% nf_asub_to_native(ASub,Qv,OutFlag,Stat,Comp)                              %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!

nf_asub_to_native(ASub,Qv,OutFlag,Props,CompProps):-
    asub(ASub,ATypes,AModes,ANonF),
    shfr_asub_to_native(AModes,Qv,OutFlag,Props1,_),
    eterms_asub_to_native(ATypes,Qv,OutFlag,Props2,_),
    nfabs:nf_asub_to_native(ANonF,Qv,CompProps),
    append(Props1,Props2,Props).

:- dom_impl(nf, collect_auxinfo_asub/3).
:- export(nf_collect_auxinfo_asub/3).
nf_collect_auxinfo_asub(Struct,Types,Types1) :-
    asub(Struct,ATypes,_,_),
    eterms_collect_auxinfo_asub(ATypes,Types,Types1).

:- dom_impl(nf, rename_auxinfo_asub/3).
:- export(nf_rename_auxinfo_asub/3).
nf_rename_auxinfo_asub(ASub, Dict, RASub) :-
    asub(ASub,ATypes,AModes,ANonf),
    eterms_rename_auxinfo_asub(ATypes, Dict,RATypes),
    asub(RASub,RATypes,AModes,ANonf).

%------------------------------------------------------------------------%
% nf_unknown_call(+,+,+,-)                                               %
% nf_unknown_call(Sg,Vars,Call,Succ)                                     %
%------------------------------------------------------------------------%

nf_unknown_call(Sg,Vars,Call,Succ):-
    asub(Call,CTypes,CModes,CNonF),
    shfr_unknown_call(Sg,Vars,CModes,SModes),
    eterms_unknown_call(Sg,Vars,CTypes,STypes),
    nfabs:nf_unknown_call(Sg,Vars,CNonF,SNonF),
    asub(Succ,STypes,SModes,SNonF).

%------------------------------------------------------------------------%
% nf_unknown_entry(+,+,-)                                                %
% nf_unknown_entry(Sg,Vars,Entry)                                        %
%------------------------------------------------------------------------%

nf_unknown_entry(Sg,Vars,Entry):-
    shfr_unknown_entry(Sg,Vars,EModes),
    eterms_unknown_entry(Sg,Vars,ETypes),
    nfabs:nf_unknown_entry(Sg,Vars,ENonF),
    asub(Entry,ETypes,EModes,ENonF).

%------------------------------------------------------------------------%
% nf_empty_entry(+,+,-)                                                  %
% nf_empty_entry(Sg,Vars,Entry)                                          %
%------------------------------------------------------------------------%

nf_empty_entry(Sg,Vars,Entry):-
    shfr_empty_entry(Sg,Vars,EModes),
    eterms_empty_entry(Sg,Vars,ETypes),
    nfabs:nf_empty_entry(Sg,Vars,ENonF),
    asub(Entry,ETypes,EModes,ENonF).

%-----------------------------------------------------------------------

nf_dom_statistics(Info):- nfabs_dom_statistics(Info).
