:- module(detplai, [
    det_init_abstract_domain/1,
    det_call_to_entry/9,
    det_exit_to_prime/7,
    det_project/5,
    det_extend/5,
    det_widen/3,
    det_widencall/3,
    det_compute_lub/2,
    det_compute_clauses_lub/3,
    det_glb/3,
    det_eliminate_equivalent/2,
    det_less_or_equal/2,
    det_identical_abstract/2,
    det_abs_sort/2,
    det_call_to_success_fact/9,
    det_split_combined_domain/3,
    det_special_builtin/5,
    det_combined_special_builtin0/2,
    det_success_builtin/6,
    %  det_call_to_success_builtin/6,
    det_input_interface/4,
    det_input_user_interface/5,
    det_asub_to_native/5,
    det_unknown_call/4,
    det_unknown_entry/3,
    det_empty_entry/3,
    det_dom_statistics/1,
    det_obtain_info/4
], [assertions,regtypes,basicmodes]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(det).
:- dom_impl(det, init_abstract_domain/1).
:- dom_impl(det, call_to_entry/9).
:- dom_impl(det, exit_to_prime/7).
:- dom_impl(det, project/5).
:- dom_impl(det, widencall/3).
:- dom_impl(det, needs/1).
:- dom_impl(det, widen/3).
:- dom_impl(det, compute_lub/2).
:- dom_impl(det, compute_clauses_lub/3).
:- dom_impl(det, identical_abstract/2).
:- dom_impl(det, abs_sort/2).
:- dom_impl(det, extend/5).
:- dom_impl(det, less_or_equal/2).
:- dom_impl(det, glb/3).
:- dom_impl(det, eliminate_equivalent/2).
:- dom_impl(det, call_to_success_fact/9).
:- dom_impl(det, special_builtin/5).
:- dom_impl(det, combined_special_builtin0/2).
:- dom_impl(det, split_combined_domain/3).
:- dom_impl(det, success_builtin/6).
:- dom_impl(det, obtain_info/4).
:- dom_impl(det, input_interface/4).
:- dom_impl(det, input_user_interface/5).
:- dom_impl(det, asub_to_native/5).
:- dom_impl(det, unknown_call/4).
:- dom_impl(det, unknown_entry/3).
:- dom_impl(det, empty_entry/3).
:- dom_impl(det, dom_statistics/1).

:- use_module(domain(eterms)).
:- use_module(domain(sharefree)).
:- use_module(domain(nfdet/detabs)).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(lists), [append/3]).
% :- use_module(library(sets), [ord_subtract/3]). % Commented out. Aug 24, 2012. Not used anymore -PLG 
:- use_module(library(sort), [sort/2]).

% Solved: 
%:- doc(bug,"1. Some asubs carry $bottom within the nf/3 representation.").
% was because of builtins; solution: the if-then-elses in split_back

%------------------------------------------------------------------------%

%% asub('$bottom','$bottom',_Modes,_Det):- !.
%% asub('$bottom',_Types,'$bottom',_Det):- !.
%% asub('$bottom',_Types,_Modes,'$bottom'):- !.
asub(det(Types,Modes,Det),Types,Modes,Det).

%------------------------------------------------------------------------%

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

det_init_abstract_domain([variants,widen]) :-
    push_pp_flag(variants,off),
    push_pp_flag(widen,on).

%------------------------------------------------------------------------%
% det_call_to_entry(+,+,+,+,+,+,+,-,-)                                   %
% det_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)             %
%------------------------------------------------------------------------%

det_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo):-
    asub(Proj,PTypes,PModes,PDet),
    shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PModes,EModes,ExtraInfoModes),
    eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PTypes,ETypes,ExtraInfoTypes),
    ( ETypes = '$bottom' ->
        Entry = '$bottom'
    ; detabs:det_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PDet,EDet,_Extra),
      shfr_obtain_info(ground,Sv,PModes,InVars), % Added. Aug 24, 2012 -PLG 
      % shfr_obtain_info(free,Sv,PModes,FVars),  % Commented out. Aug 24, 2012. Not a safe asumption. -PLG 
      % ord_subtract(Sv,FVars,InVars),      % Commented out. Aug 24, 2012 -PLG 
      asub(Entry,ETypes,EModes,EDet)
    ),
    asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,InVars).

%------------------------------------------------------------------------%
% det_exit_to_prime(+,+,+,+,+,-,-)                                        %
% det_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                   %
%------------------------------------------------------------------------%

det_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom'):- !.
det_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    asub(Exit,ETypes,EModes,EDet),
    asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,ExtraInfoDet),
    shfr_exit_to_prime(Sg,Hv,Head,Sv,EModes,ExtraInfoModes,PModes),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,ETypes,ExtraInfoTypes,PTypes),
    ( PTypes = '$bottom' ->
        Prime = '$bottom'
    ; detabs:det_exit_to_prime(Sg,Hv,Head,Sv,EDet,ExtraInfoDet,PDet),
      ( PDet = '$bottom' ->
          Prime = '$bottom'
      ; asub(Prime,PTypes,PModes,PDet)
      )
    ).

%------------------------------------------------------------------------%
% det_project(+,+,+,+,-)                                                 %
% det_project(Sg,Vars,HvFv_u,ASub,Proj)                                  %
%------------------------------------------------------------------------%

det_project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
det_project(Sg,Vars,HvFv_u,ASub,Proj):-
    asub(ASub,ATypes,AModes,ADet),
    shfr_project(Sg,Vars,HvFv_u,AModes,PModes),
    eterms_project(Sg,Vars,HvFv_u,ATypes,PTypes),
    detabs:det_project(Sg,Vars,HvFv_u,ADet,PDet),
    asub(Proj,PTypes,PModes,PDet).

%------------------------------------------------------------------------%
% det_extend(+,+,+,+,-)                                                  %
% det_extend(Sg,Prime,Sv,Call,Succ)                                      %
%------------------------------------------------------------------------%

det_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
det_extend(Sg,Prime,Sv,Call,Succ):-
    asub(Prime,PTypes,PModes,PDet),
    asub(Call,CTypes,CModes,CDet),
    shfr_extend(Sg,PModes,Sv,CModes,SModes),
    eterms_extend(Sg,PTypes,Sv,CTypes,STypes),
    detabs:det_extend(Sg,PDet,Sv,CDet,SDet),
    asub(Succ,STypes,SModes,SDet).

det_needs(clauses_lub) :- !.
det_needs(split_combined_domain) :- !.
det_needs(X) :-
    eterms_needs(X), !.
det_needs(X) :-
    shfr_needs(X).

%------------------------------------------------------------------------%
% det_widen(+,+,-)                                                        %
% det_widen(ASub1,ASub2,ASub)                                             %
%------------------------------------------------------------------------%

det_widen('$bottom',ASub1,ASub):- !, ASub=ASub1.
det_widen(ASub0,'$bottom',ASub):- !, ASub=ASub0.
det_widen(ASub0,ASub1,ASub):-
    asub(ASub0,ATypes0,AModes0,ADet0),
    asub(ASub1,ATypes1,AModes1,ADet1),
    shfr_compute_lub([AModes0,AModes1],AModes),
    eterms_widen(ATypes0,ATypes1,ATypes),
    detabs:det_compute_lub([ADet0,ADet1],ADet),
    asub(ASub,ATypes,AModes,ADet).

%------------------------------------------------------------------------%
% det_widencall(+,+,-)                                                    %
% det_widencall(ASub1,ASub2,ASub)                                         %
%------------------------------------------------------------------------%

det_widencall('$bottom',ASub1,ASub):- !, ASub=ASub1.
det_widencall(ASub0,'$bottom',ASub):- !, ASub=ASub0.
det_widencall(ASub0,ASub1,ASub):-
    asub(ASub0,ATypes0,_AModes0,_ADet0),
    asub(ASub1,ATypes1,AModes1,ADet1),
    % assuming _AModes0 =< AModes1 and _ANonF0 =< ANonF1
    eterms_widencall(ATypes0,ATypes1,ATypes),
    asub(ASub,ATypes,AModes1,ADet1).

%------------------------------------------------------------------------%
% det_compute_lub(+,-)                                                    %
% det_compute_lub(ListASub,Lub)                                           %
%------------------------------------------------------------------------%

det_compute_lub(ListASub,Lub):-
    split(ListASub,LTypes,LModes,LDet),
    shfr_compute_lub(LModes,LubModes),
    eterms_compute_lub(LTypes,LubTypes),
    detabs:det_compute_lub(LDet,LubDet),
    asub(Lub,LubTypes,LubModes,LubDet).

split([],[],[],[]).
split([ASub|ListASub],OutATypes,OutAModes,OutADet):-
    ( ASub == '$bottom' -> OutATypes = LTypes, 
        OutAModes = LModes, 
        OutADet  = LDet
    ; asub(ASub,ATypes,AModes,ADet),
      OutATypes = [ATypes|LTypes], 
      OutAModes = [AModes|LModes], 
      OutADet  = [ADet|LDet]
    ),
    split(ListASub,LTypes,LModes,LDet).

det_split_combined_domain(ListASub,[LTypes,LModes,LDet],[eterms,shfr,det]):-
    ( var(LTypes) ->
        split(ListASub,LTypes,LModes,_LDet),
        LDet=ListASub
    ; split_back(ListASub,LTypes,LModes,LDet)
    ).

split_back([],[],[],[]).
split_back([ASub|ListASub],[ATypes|LTypes],[AModes|LModes],[ASubDet|LDet]):-
    ( ATypes == '$bottom' -> ASub = '$bottom'
    ; AModes == '$bottom' -> ASub = '$bottom'
    ; asub(ASub,ATypes,AModes,ADet),
      asub(ASubDet,_ATypes,_AModes,ADet)
    ),
    split_back(ListASub,LTypes,LModes,LDet).

%------------------------------------------------------------------------%
% det_compute_clauses_lub(+,-)                                           %
% det_compute_clauses_lub(ListASub,Lub)                                  %
%------------------------------------------------------------------------%

det_compute_clauses_lub(['$bottom'],_Proj,['$bottom']):- !.
det_compute_clauses_lub([ASub],Proj,[Lub]):-
    asub(ASub,ATypes,AModes,ADetList),
    asub(Proj,PTypes,PModes,_PDetList),
    compute_modetypes(PTypes,PModes,_Head,ModeTypes),
    det_compute_mut_exclusion(ModeTypes,ADetList,LubDet),
    asub(Lub,ATypes,AModes,LubDet).

compute_modetypes(Types,Modes,Head,MTypes):-
    shfr_obtain_info(ground,Modes,FVars), % Added. Aug 24, 2012 -PLG
    % shfr_obtain_info(free,Modes,FVars), % Commented out. Aug 24, 2012. Not a safe asumption -PLG. 
    sort(Types,Types_s),
    compute_modetypes0(Types_s,FVars,Vars,ModeTypes),
    Head =.. [p|Vars],
    MTypes =.. [p|ModeTypes].

compute_modetypes0([],_FVars,[],[]).
compute_modetypes0([Var:(_,T)|Types],FVars,[Var|Vars],[M:T|ModeTypes]):-
    get_mode(Var,FVars,M),
    compute_modetypes0(Types,FVars,Vars,ModeTypes).

get_mode(Var,FVars,M):-          % Added. Aug 24, 2012 -PLG
    memberchk(Var,FVars), !,
    M = in.
get_mode(_Var,_GVars,out).

% get_mode(Var,FVars,M):-       % Commented out. Aug 24, 2012. Not a safe asumption -PLG. 
%       memberchk(Var,FVars), !,
%       M = out.
% get_mode(_Var,_GVars,in).

%------------------------------------------------------------------------%
% det_glb(+,+,-)                                                         %
% det_glb(ASub0,ASub1,Glb)                                               %
%------------------------------------------------------------------------%

det_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
det_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
det_glb(ASub0,ASub1,Glb):-
    asub(ASub0,ATypes0,AModes0,ADet0),
    asub(ASub1,ATypes1,AModes1,ADet1),
    shfr_glb(AModes0,AModes1,GModes),
    eterms_glb(ATypes0,ATypes1,GTypes),
    detabs:det_glb(ADet0,ADet1,GDet),
    asub(Glb,GTypes,GModes,GDet).

%------------------------------------------------------------------------%

det_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)

%------------------------------------------------------------------------%
% det_less_or_equal(+,+)                                                  %
% det_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%

det_less_or_equal('$bottom','$bottom'):- !.
det_less_or_equal(ASub0,ASub1):-
    asub(ASub0,ATypes0,AModes0,ADet0),
    asub(ASub1,ATypes1,AModes1,ADet1),
    shfr_less_or_equal(AModes0,AModes1),
    eterms_less_or_equal(ATypes0,ATypes1),
    detabs:det_less_or_equal(ADet0,ADet1).

%------------------------------------------------------------------------%
% det_identical_abstract(+,+)                                             %
% det_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%

det_identical_abstract('$bottom','$bottom'):- !.
det_identical_abstract(ASub0,ASub1):-
    asub(ASub0,ATypes0,AModes0,ADet0),
    asub(ASub1,ATypes1,AModes1,ADet1),
    AModes0 == AModes1,
    eterms_identical_abstract(ATypes0,ATypes1),
    detabs:det_identical_abstract(ADet0,ADet1).

%------------------------------------------------------------------------%
% det_abs_sort(+,-)                                                           %
% det_abs_sort(ASub0,ASub1)                                                   %
%------------------------------------------------------------------------%

det_abs_sort('$bottom','$bottom'):- !.
det_abs_sort(ASub0,ASub1):-
    asub(ASub0,ATypes0,AModes0,ADet0),
    shfr_abs_sort(AModes0,AModes1),
    eterms_abs_sort(ATypes0,ATypes1),
    detabs:det_abs_sort(ADet0,ADet1),
    asub(ASub1,ATypes1,AModes1,ADet1).

%------------------------------------------------------------------------%
% det_call_to_success_fact(+,+,+,+,+,+,+,-,-)                            %
% det_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)         %
%-------------------------------------------------------------------------

det_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    asub(Call,CTypes,CModes,CDet),
    asub(Proj,PTypes,PModes,PDet),
    shfr_call_to_success_fact(Sg,Hv,Head,K,Sv,CModes,PModes,RModes,SModes),
    eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,CTypes,PTypes,RTypes,STypes),
    detabs:det_call_to_success_fact(Sg,Hv,Head,K,Sv,CDet,PDet,RDet,SDet),
    asub(Prime,RTypes,RModes,RDet),
    asub(Succ,STypes,SModes,SDet).


%-------------------------------------------------------------------------
% det_special_builtin(+,+,+,-,-)                                         |
% det_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                    |
%-------------------------------------------------------------------------

det_special_builtin(SgKey,Sg,_Subgoal,SgKey,Sg):-
    detabs:det_special_builtin(SgKey).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [special_builtin/6]).

% TODO: [IG] special_builtin requires Sg to be instantiated
% TODO: why are we not collecting the info for each domain?
det_combined_special_builtin0(SgKey,Domains) :-
    % TODO: refactor (define a nondet pred with combined domains instead)
    ( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,det]
    ; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,det]
    ; special_builtin(det,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,det]
    ; fail
    ).

%-------------------------------------------------------------------------
% det_success_builtin(+,+,+,+,+,-)                                        |
% det_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                          |
%-------------------------------------------------------------------------

det_success_builtin(Type,_Sv_u,Sg,HvFv_u,Call,Succ):-
    asub(Call,Types,Modes,CallDet),
    detabs:det_success_builtin(Type,Modes,Sg,HvFv_u,CallDet,SuccDet),
    asub(Succ,Types,Modes,SuccDet).

%-------------------------------------------------------------------------
% det_call_to_success_builtin(+,+,+,+,+,-)                                %
% det_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)                 %
%-------------------------------------------------------------------------
% Not used

%------------------------------------------------------------------------%
% det_input_interface(+,+,+,-)                                            %
% det_input_interface(InputUser,Kind,StructI,StructO)                     %
%------------------------------------------------------------------------%

det_input_interface(InputUser,Kind,StructI,StructO):-
    ( nonvar(Kind) -> 
        KModes=Kind, KTypes=Kind, KDet=Kind
    ; true
    ),
    asub(StructI,ITypes,IModes,IDet),
    shfr_input_interface_(InputUser,KModes,IModes,OModes),
    eterms_input_interface_(InputUser,KTypes,ITypes,OTypes),
    det_input_interface_(InputUser,KDet,IDet,ODet),
    asub(StructO,OTypes,OModes,ODet).

shfr_input_interface_(InputUser,Kind,IModes,OModes):-
    shfr_input_interface(InputUser,Kind,IModes,OModes), !.
shfr_input_interface_(_InputUser,_Kind,IModes,IModes).

eterms_input_interface_(InputUser,Kind,ITypes,OTypes):-
    eterms_input_interface(InputUser,Kind,ITypes,OTypes), !.
eterms_input_interface_(_InputUser,_Kind,ITypes,ITypes).

det_input_interface_(InputUser,Kind,IDet,ODet):-
    detabs:det_input_interface(InputUser,Kind,IDet,ODet), !.
det_input_interface_(_InputUser,_Kind,IDet,IDet).

%------------------------------------------------------------------------%
% det_input_user_interface(+,+,-,+,+)                                    %
% det_input_user_interface(InputUser,Qv,ASub)                            %
%------------------------------------------------------------------------%

det_input_user_interface(Struct,Qv,ASub,Sg,MaybeCallASub):-
    asub(Struct,Types,Modes,Det),
    shfr_input_user_interface(Modes,Qv,AModes,Sg,MaybeCallASub),
    eterms_input_user_interface(Types,Qv,ATypes,Sg,MaybeCallASub),
    detabs:det_input_user_interface(Det,Qv,ADet,Sg,MaybeCallASub),
    asub(ASub,ATypes,AModes,ADet).

%------------------------------------------------------------------------%
% det_asub_to_native(+,+,+,-,-)                                           %
% det_asub_to_native(ASub,Qv,OutFlag,Stat,Comp)                              %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!

det_asub_to_native(ASub,Qv,OutFlag,Props,CompProps):-
    asub(ASub,ATypes,AModes,ADet),
    shfr_asub_to_native(AModes,Qv,OutFlag,Props1,_),
    eterms_asub_to_native(ATypes,Qv,OutFlag,Props2,_),
    detabs:det_asub_to_native(ADet,Qv,CompProps),
    append(Props1,Props2,Props).

:- dom_impl(det, collect_auxinfo_asub/3).
:- export(det_collect_auxinfo_asub/3).
det_collect_auxinfo_asub(Struct,Types,Types1) :-
    asub(Struct,ATypes,_,_),
    eterms_collect_auxinfo_asub(ATypes,Types,Types1).

:- dom_impl(det, rename_auxinfo_asub/3).
:- export(det_rename_auxinfo_asub/3).
det_rename_auxinfo_asub(ASub, Dict, RASub) :-
    asub(ASub,ATypes,AModes,ADet),
    eterms_rename_auxinfo_asub(ATypes, Dict, RATypes),
    asub(RASub,RATypes,AModes,ADet).

%------------------------------------------------------------------------%
% det_unknown_call(+,+,+,-)                                              %
% det_unknown_call(Sg,Vars,Call,Succ)                                    %
%------------------------------------------------------------------------%

det_unknown_call(Sg,Vars,Call,Succ):-
    asub(Call,CTypes,CModes,CDet),
    shfr_unknown_call(Sg,Vars,CModes,SModes),
    eterms_unknown_call(Sg,Vars,CTypes,STypes),
    detabs:det_unknown_call(Sg,Vars,CDet,SDet),
    asub(Succ,STypes,SModes,SDet).

%------------------------------------------------------------------------%
% det_unknown_entry(+,+,-)                                               %
% det_unknown_entry(Sg,Vars,Entry)                                       %
%------------------------------------------------------------------------%

det_unknown_entry(Sg,Vars,Entry):-
    shfr_unknown_entry(Sg,Vars,EModes),
    eterms_unknown_entry(Sg,Vars,ETypes), 
    detabs:det_unknown_entry(Sg,Vars,EDet),
    asub(Entry,ETypes,EModes,EDet).

%------------------------------------------------------------------------%
% det_empty_entry(+,+,-)                                                 %
% det_empty_entry(Sg,Vars,Entry)                                         %
%------------------------------------------------------------------------%

det_empty_entry(Sg,Vars,Entry):-
    shfr_empty_entry(Sg,Vars,EModes),
    eterms_empty_entry(Sg,Vars,ETypes),
    detabs:det_empty_entry(Sg,Vars,EDet),
    asub(Entry,ETypes,EModes,EDet).

%-----------------------------------------------------------------------

det_dom_statistics(Info):- detabs:detabs_dom_statistics(Info).

%-----------------------------------------------------------------------

det_obtain_info(Prop,Vars,ASub,Info):- detabs:det_obtain_info(Prop,Vars,ASub,Info).

% det_obtain_info(Prop,Vars,ASub,Info) :- !, 
%       asub_to_info(det,ASub,Vars,_OutputUser,CompProps),
%       CompProps = Info.
