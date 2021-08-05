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
    nf_dom_statistics/1,
    nf_obtain_info/4
], [assertions,regtypes,basicmodes,hiord]).

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
:- dom_impl(nf, obtain_info/4).

:- use_module(domain(eterms)).
:- use_module(domain(sharefree), [
    obtain_info/3,
    obtain_info/4,
    call_to_entry/9,
    exit_to_prime/7,
    project/5,
    extend/5,
    needs/1,
    compute_lub/2,
    glb/3,
    less_or_equal/2,
    abs_sort/2,
    call_to_success_fact/9,
    input_interface/4,
    input_user_interface/5,
    asub_to_native/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3
]).
:- use_module(domain(nfdet/nfabs)).

:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(sets), [ord_subtract/3]).
:- use_module(library(sort), [sort/2]).

% Solved: 
%:- doc(bug,"1. Some asubs carry $bottom within the nf/3 representation.").
% was because of builtins; solution: the if-then-elses in split_back

%------------------------------------------------------------------------%

:- export(nf_par_asub/2).

:- doc(nf_par_asub(NfTyp,ASub), "@var{ASub} is an abstract substitution
   term used in the combined domain @tt{nf}. It contains types, modes
   and nonfailure information of type @tt{NfTyp}.").

:- regtype nf_par_asub(NfTyp,ASub)
   # "@var{ASub} is an abstract substitution term used in the combined
   domain @tt{nf}. It contains types, modes and nonfailure information
   of type @tt{NfTyp}.".

:- meta_predicate nf_par_asub(pred(1), ?).

nf_par_asub(_,'$bottom').
nf_par_asub(NfTyp, nf(Types,Modes,NonFail)) :-
    term(Types),
    term(Modes),
    NfTyp(NonFail).

:- export(nf_asub/1).

:- doc(nf_asub(ASub), "@var{ASub} is an abstract substitution term
   used in the combined domain @tt{nf}. It contains types, modes and
   nonfailure information.").

:- regtype nf_asub(ASub)
   # "@var{ASub} is an abstract substitution term used in the combined
     domain @tt{nf}. It contains types, modes and nonfailure
     information.".

nf_asub(ASub):- nf_par_asub(nfabs_asub,ASub).

:- export(nf_pred_asub/1).

:- regtype nf_pred_asub(ASub)

   # "@var{ASub} is a compact representation for a set of abstract
     substitutions used in the combined domain @tt{nf}. Each of the
     substitutions in that set has the same modes and types. However,
     the nonfailure information gathers together the clause tests of
     those abstract substitutions as a list, meaning the disjunction
     of all of them (named a @tt{predicate test}, which is needed for
     performing the @tt{covering check}).".

nf_pred_asub(ASub):- nf_par_asub(nfabs_pred_asub,ASub).

:- export(nf_pred_asub_sl/1).

:- regtype nf_pred_asub_sl/1.

nf_pred_asub_sl([Asub]):- nf_pred_asub(Asub).

%% asub('$bottom','$bottom',_Modes,_NonF):- !.
%% asub('$bottom',_Types,'$bottom',_NonF):- !.
%% asub('$bottom',_Types,_Modes,'$bottom'):- !.

:- export(asub/4).

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
    nfplai:asub(Proj,PTypes,PModes,PNonF),
    sharefree:call_to_entry(Sv,Sg,Hv,Head,K,Fv,PModes,EModes,ExtraInfoModes),
    eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PTypes,ETypes,ExtraInfoTypes),
    ( ETypes = '$bottom' ->
        Entry = '$bottom'
    ; sharefree:obtain_info(free,Sv,PModes,FVars),
      ord_subtract(Sv,FVars,InVars),
      nfabs:nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PNonF,InVars,ENonF0,_Extra),
      ( nfabs:possibly_fail_unif_tests(ENonF0, PModes) ->
          nfabs:nf_unknown_call(Sg,InVars,ENonF0,ENonF)
      ; ENonF0 = ENonF
      ),
      nfplai:asub(Entry,ETypes,EModes,ENonF)
    ),
    nfplai:asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,InVars).

%------------------------------------------------------------------------%
% nf_exit_to_prime(+,+,+,+,+,-,-)                                        %
% nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                   %
%------------------------------------------------------------------------%

nf_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom'):- !.
nf_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    nfplai:asub(Exit,ETypes,EModes,ENonF),
    nfplai:asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,ExtraInfoNonF),
    sharefree:exit_to_prime(Sg,Hv,Head,Sv,EModes,ExtraInfoModes,PModes),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,ETypes,ExtraInfoTypes,PTypes),
    ( PTypes = '$bottom' ->
        Prime = '$bottom'
    ; nfabs:nf_exit_to_prime(Sg,Hv,Head,Sv,ENonF,ExtraInfoNonF,PNonF),
      ( PNonF = '$bottom' ->
          Prime = '$bottom'
      ; nfplai:asub(Prime,PTypes,PModes,PNonF)
      )
    ).

%------------------------------------------------------------------------%
% nf_project(+,+,+,+,-)                                                  %
% nf_project(Sg,Vars,HvFv_u,ASub,Proj)                                   %
%------------------------------------------------------------------------%

nf_project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
nf_project(Sg,Vars,HvFv_u,ASub,Proj):-
    nfplai:asub(ASub,ATypes,AModes,ANonF),
    sharefree:project(Sg,Vars,HvFv_u,AModes,PModes),
    eterms_project(Sg,Vars,HvFv_u,ATypes,PTypes),
    nfabs:nf_project(Sg,Vars,HvFv_u,ANonF,PNonF),
    nfplai:asub(Proj,PTypes,PModes,PNonF).

%------------------------------------------------------------------------%
% nf_extend(+,+,+,+,-)                                                   %
% nf_extend(Sg,Prime,Sv,Call,Succ)                                       %
%------------------------------------------------------------------------%

nf_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
nf_extend(Sg,Prime,Sv,Call,Succ):-
    nfplai:asub(Prime,PTypes,PModes,PNonF),
    nfplai:asub(Call,CTypes,CModes,CNonF),
    sharefree:extend(Sg,PModes,Sv,CModes,SModes),
    eterms_extend(Sg,PTypes,Sv,CTypes,STypes),
    nfabs:nf_extend(Sg,PNonF,Sv,CNonF,SNonF),
    nfplai:asub(Succ,STypes,SModes,SNonF).

nf_needs(clauses_lub) :- !.
nf_needs(split_combined_domain) :- !.
nf_needs(X) :-
    eterms_needs(X), !.
nf_needs(X) :-
    sharefree:needs(X).

%------------------------------------------------------------------------%
% nf_widen(+,+,-)                                                        %
% nf_widen(ASub1,ASub2,ASub)                                             %
%------------------------------------------------------------------------%

nf_widen('$bottom',ASub1,ASub):- !, ASub=ASub1.
nf_widen(ASub0,'$bottom',ASub):- !, ASub=ASub0.
nf_widen(ASub0,ASub1,ASub):-
    nfplai:asub(ASub0,ATypes0,AModes0,ANonF0),
    nfplai:asub(ASub1,ATypes1,AModes1,ANonF1),
    sharefree:compute_lub([AModes0,AModes1],AModes),
    eterms_widen(ATypes0,ATypes1,ATypes),
    nfabs:nf_widen(ANonF0,ANonF1,ANonF),
    nfplai:asub(ASub,ATypes,AModes,ANonF).

%------------------------------------------------------------------------%
% nf_widencall(+,+,-)                                                    %
% nf_widencall(ASub1,ASub2,ASub)                                         %
%------------------------------------------------------------------------%

nf_widencall('$bottom',ASub1,ASub):- !, ASub=ASub1.
nf_widencall(ASub0,'$bottom',ASub):- !, ASub=ASub0.
nf_widencall(ASub0,ASub1,ASub):-
    nfplai:asub(ASub0,ATypes0,_AModes0,_ANonF0),
    nfplai:asub(ASub1,ATypes1,AModes1,ANonF1),
    % assuming _AModes0 =< AModes1 and _ANonF0 =< ANonF1
    eterms_widencall(ATypes0,ATypes1,ATypes),
    nfplai:asub(ASub,ATypes,AModes1,ANonF1).

%------------------------------------------------------------------------%
% nf_compute_lub(+,-)                                                    %
% nf_compute_lub(ListASub,Lub)                                           %
%------------------------------------------------------------------------%

nf_compute_lub(ListASub0,Lub):-
    filter_non_bottom(ListASub0,ListASub),
    nf_compute_lub_(ListASub,Lub).

nf_compute_lub_([],'$bottom'):- !.
nf_compute_lub_(ListASub,Lub):-
    split(ListASub,LTypes,LModes,LNonF),
    sharefree:compute_lub(LModes,LubModes),
    eterms_compute_lub(LTypes,LubTypes),
    nfabs:nf_compute_lub(LNonF,LubNonF),
    nfplai:asub(Lub,LubTypes,LubModes,LubNonF).

split([],[],[],[]).
split(['$bottom'|ListASub],LTypes,LModes,LNonF):- !,
    split(ListASub,LTypes,LModes,LNonF).
split([ASub|ListASub],[ATypes|LTypes],[AModes|LModes],[ANonF|LNonF]):-
    nfplai:asub(ASub,ATypes,AModes,ANonF),
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
    ; nfplai:asub(ASub,ATypes,AModes,ANonF),
      nfplai:asub(ASubNonF,_ATypes,_AModes,ANonF)
    ),
    split_back(ListASub,LTypes,LModes,LNonF).

filter_non_bottom([],[]).
filter_non_bottom(['$bottom'|L0],L1) :- !,
    filter_non_bottom(L0,L1).
filter_non_bottom([ASub|L0],[ASub|L1]) :-
    filter_non_bottom(L0,L1).

%------------------------------------------------------------------------%
% nf_compute_clauses_lub(+,-)                                            %
% nf_compute_clauses_lub(ListASub,Lub)                                   %
%------------------------------------------------------------------------%

:- pred nf_compute_clauses_lub(ASubL,Proj,LubL)
   :  (nf_pred_asub_sl(ASubL), nf_asub(Proj), var(LubL))
   => (nf_pred_asub_sl(ASubL), nf_asub(Proj), nf_pred_asub_sl(LubL))
   # "Performs the covering check that decides if the predicate test
   encoded in @var{ASubL} covers the types/modes represented in
   @var{Proj}. The predicate test is a conjunction of clause tests
   (corresponding to those clauses that do not fail so far).  The
   modes/types, taken from @var{Proj}, corresponds to the parent goal,
   i.e., the one that unifies with the heads the clauses whose tests
   are represented in @var{ASubL}. The covering and nonfailure
   information derived from the covering check is represented in
   @var{LubL}".

nf_compute_clauses_lub(['$bottom'],_Proj,['$bottom']):- !.
nf_compute_clauses_lub([ASub],Proj,[Lub]):-
    nfplai:asub(ASub,ATypes,AModes,ANonFList),
    nfplai:asub(Proj,PTypes,PModes,_PNonFList),
    compute_modetypes(PTypes,PModes,_Head,ModeTypes),
    nf_compute_covering(ModeTypes,ANonFList,LubNonF),
    nfplai:asub(Lub,ATypes,AModes,LubNonF).

compute_modetypes(Types,Modes,Head,MTypes):-
    % sharefree:obtain_info(free,_Vars,Modes,FVars), % PLG
    sharefree:obtain_info(free,Modes,FVars), % Added PLG
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
    nfplai:asub(ASub0,ATypes0,AModes0,ANonF0),
    nfplai:asub(ASub1,ATypes1,AModes1,ANonF1),
    sharefree:glb(AModes0,AModes1,GModes),
    eterms_glb(ATypes0,ATypes1,GTypes),
    nfabs:nf_glb(ANonF0,ANonF1,GNonF),
    nfplai:asub(Glb,GTypes,GModes,GNonF).

%------------------------------------------------------------------------%

nf_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)

%------------------------------------------------------------------------%
% nf_less_or_equal(+,+)                                                  %
% nf_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%

nf_less_or_equal('$bottom','$bottom'):- !.
nf_less_or_equal(ASub0,ASub1):-
    nfplai:asub(ASub0,ATypes0,AModes0,ANonF0),
    nfplai:asub(ASub1,ATypes1,AModes1,ANonF1),
    sharefree:less_or_equal(AModes0,AModes1),
    eterms_less_or_equal(ATypes0,ATypes1),
    nfabs:nf_less_or_equal(ANonF0,ANonF1).

%------------------------------------------------------------------------%
% nf_identical_abstract(+,+)                                             %
% nf_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%

nf_identical_abstract('$bottom','$bottom'):- !.
nf_identical_abstract(ASub0,ASub1):-
    nfplai:asub(ASub0,ATypes0,AModes0,ANonF0),
    nfplai:asub(ASub1,ATypes1,AModes1,ANonF1),
    AModes0 == AModes1,
    eterms_identical_abstract(ATypes0,ATypes1),
    nfabs:nf_identical_abstract(ANonF0,ANonF1).

%------------------------------------------------------------------------%
% nf_abs_sort(+,-)                                                           %
% nf_abs_sort(ASub0,ASub1)                                                   %
%------------------------------------------------------------------------%

nf_abs_sort('$bottom','$bottom'):- !.
nf_abs_sort(ASub0,ASub1):-
    nfplai:asub(ASub0,ATypes0,AModes0,ANonF0),
    sharefree:abs_sort(AModes0,AModes1),
    eterms_abs_sort(ATypes0,ATypes1),
    nfabs:nf_abs_sort(ANonF0,ANonF1),
    nfplai:asub(ASub1,ATypes1,AModes1,ANonF1).

%------------------------------------------------------------------------%
% nf_call_to_success_fact(+,+,+,+,+,+,+,-,-)                               %
% nf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)            %
%-------------------------------------------------------------------------

nf_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    nfplai:asub(Call,CTypes,CModes,CNonF),
    nfplai:asub(Proj,PTypes,PModes,PNonF),
    sharefree:call_to_success_fact(Sg,Hv,Head,K,Sv,CModes,PModes,RModes,SModes),
    eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,CTypes,PTypes,RTypes,STypes),
    nfabs:nf_call_to_success_fact(Sg,Hv,Head,K,Sv,CNonF,PNonF,RNonF,SNonF),
    nfplai:asub(Prime,RTypes,RModes,RNonF),
    nfplai:asub(Succ,STypes,SModes,SNonF).


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
    nfplai:asub(Call,Types,Modes,CallNonF),
    nfabs:nf_success_builtin(Type,Modes,Sg,HvFv_u,CallNonF,SuccNonF),
    nfplai:asub(Succ,Types,Modes,SuccNonF).

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
    nfplai:asub(StructI,ITypes,IModes,INonF),
    shfr_input_interface_(InputUser,KModes,IModes,OModes),
    eterms_input_interface_(InputUser,KTypes,ITypes,OTypes),
    nf_input_interface_(InputUser,KNonF,INonF,ONonF),
    nfplai:asub(StructO,OTypes,OModes,ONonF).

shfr_input_interface_(InputUser,Kind,IModes,OModes):-
    sharefree:input_interface(InputUser,Kind,IModes,OModes), !.
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
    nfplai:asub(Struct,Types,Modes,NonF),
    sharefree:input_user_interface(Modes,Qv,AModes,Sg,MaybeCallASub),
    eterms_input_user_interface(Types,Qv,ATypes,Sg,MaybeCallASub),
    nfabs:nf_input_user_interface(NonF,Qv,ANonF,Sg,MaybeCallASub),
    nfplai:asub(ASub,ATypes,AModes,ANonF).

%------------------------------------------------------------------------%
% nf_asub_to_native(+,+,+,-,-)                                           %
% nf_asub_to_native(ASub,Qv,OutFlag,Stat,Comp)                              %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!

nf_asub_to_native(ASub,Qv,OutFlag,Props,CompProps):-
    nfplai:asub(ASub,ATypes,AModes,ANonF),
    sharefree:asub_to_native(AModes,Qv,OutFlag,Props1,_),
    eterms_asub_to_native(ATypes,Qv,OutFlag,Props2,_),
    nfabs:nf_asub_to_native(ANonF,Qv,CompProps),
    append(Props1,Props2,Props).

:- dom_impl(nf, collect_auxinfo_asub/3).
:- export(nf_collect_auxinfo_asub/3).
nf_collect_auxinfo_asub(Struct,Types,Types1) :-
    nfplai:asub(Struct,ATypes,_,_),
    eterms_collect_auxinfo_asub(ATypes,Types,Types1).

:- dom_impl(nf, rename_auxinfo_asub/3).
:- export(nf_rename_auxinfo_asub/3).
nf_rename_auxinfo_asub(ASub, Dict, RASub) :-
    nfplai:asub(ASub,ATypes,AModes,ANonf),
    eterms_rename_auxinfo_asub(ATypes, Dict,RATypes),
    nfplai:asub(RASub,RATypes,AModes,ANonf).

%------------------------------------------------------------------------%
% nf_unknown_call(+,+,+,-)                                               %
% nf_unknown_call(Sg,Vars,Call,Succ)                                     %
%------------------------------------------------------------------------%

nf_unknown_call(Sg,Vars,Call,Succ):-
    nfplai:asub(Call,CTypes,CModes,CNonF),
    sharefree:unknown_call(Sg,Vars,CModes,SModes),
    eterms_unknown_call(Sg,Vars,CTypes,STypes),
    nfabs:nf_unknown_call(Sg,Vars,CNonF,SNonF),
    nfplai:asub(Succ,STypes,SModes,SNonF).

%------------------------------------------------------------------------%
% nf_unknown_entry(+,+,-)                                                %
% nf_unknown_entry(Sg,Vars,Entry)                                        %
%------------------------------------------------------------------------%

nf_unknown_entry(Sg,Vars,Entry):-
    sharefree:unknown_entry(Sg,Vars,EModes),
    eterms_unknown_entry(Sg,Vars,ETypes),
    nfabs:nf_unknown_entry(Sg,Vars,ENonF),
    nfplai:asub(Entry,ETypes,EModes,ENonF).

%------------------------------------------------------------------------%
% nf_empty_entry(+,+,-)                                                  %
% nf_empty_entry(Sg,Vars,Entry)                                          %
%------------------------------------------------------------------------%

nf_empty_entry(Sg,Vars,Entry):-
    sharefree:empty_entry(Sg,Vars,EModes),
    eterms_empty_entry(Sg,Vars,ETypes),
    nfabs:nf_empty_entry(Sg,Vars,ENonF),
    nfplai:asub(Entry,ETypes,EModes,ENonF).

%-----------------------------------------------------------------------

nf_dom_statistics(Info):- nfabs_dom_statistics(Info).

%-----------------------------------------------------------------------

nf_obtain_info(Prop,Vars,ASub0,Info) :- knows_of(Prop,eterms), !,
    nfplai:asub(ASub0,ASub,_,_),
    eterms_obtain_info(Prop,Vars,ASub,Info).
nf_obtain_info(Prop,Vars,ASub0,Info) :- knows_of(Prop,shfr), !,
    nfplai:asub(ASub0,_,ASub,_),
    sharefree:obtain_info(Prop,Vars,ASub,Info).
nf_obtain_info(Prop,_Vars,ASub0,Info) :- knows_of(Prop,nf), !,
    nfplai:asub(ASub0,_,_,ASub),
    nfabs:nf_asub_to_native(ASub,_,Info).
