:- module(nfdet, [
    nfdet_init_abstract_domain/1,
    nfdet_call_to_entry/9,
    nfdet_exit_to_prime/7,
    nfdet_project/5,
    nfdet_extend/5,
    nfdet_widen/3,
    nfdet_widencall/3,
    nfdet_compute_lub/2,
    nfdet_compute_clauses_lub/3,
    nfdet_glb/3,
    nfdet_eliminate_equivalent/2,
    nfdet_less_or_equal/2,
    nfdet_identical_abstract/2,
    nfdet_abs_sort/2,
    nfdet_call_to_success_fact/9,
    nfdet_split_combined_domain/3,
    nfdet_special_builtin/5,
    nfdet_combined_special_builtin0/2,
    nfdet_success_builtin/6,
    % nfdet_call_to_success_builtin/6,
    nfdet_input_interface/4,
    nfdet_input_user_interface/5,
    nfdet_asub_to_native/5,
    nfdet_unknown_call/4,
    nfdet_unknown_entry/3,
    nfdet_empty_entry/3,
    nfdet_dom_statistics/1,
    nfdet_obtain_info/4
], [assertions,regtypes,basicmodes]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(nfdet).
:- dom_impl(nfdet, init_abstract_domain/1).
:- dom_impl(nfdet, call_to_entry/9).
:- dom_impl(nfdet, exit_to_prime/7).
:- dom_impl(nfdet, project/5).
:- dom_impl(nfdet, widencall/3).
:- dom_impl(nfdet, needs/1).
:- dom_impl(nfdet, widen/3).
:- dom_impl(nfdet, compute_lub/2).
:- dom_impl(nfdet, compute_clauses_lub/3).
:- dom_impl(nfdet, identical_abstract/2).
:- dom_impl(nfdet, abs_sort/2).
:- dom_impl(nfdet, extend/5).
:- dom_impl(nfdet, less_or_equal/2).
:- dom_impl(nfdet, glb/3).
:- dom_impl(nfdet, eliminate_equivalent/2).
:- dom_impl(nfdet, call_to_success_fact/9).
:- dom_impl(nfdet, special_builtin/5).
:- dom_impl(nfdet, combined_special_builtin0/2).
:- dom_impl(nfdet, split_combined_domain/3).
:- dom_impl(nfdet, success_builtin/6).
:- dom_impl(nfdet, input_interface/4).
:- dom_impl(nfdet, input_user_interface/5).
:- dom_impl(nfdet, asub_to_native/5).
:- dom_impl(nfdet, unknown_call/4).
:- dom_impl(nfdet, unknown_entry/3).
:- dom_impl(nfdet, empty_entry/3).
:- dom_impl(nfdet, dom_statistics/1).
:- dom_impl(nfdet, obtain_info/4).

:- doc(title, "Nonfailure+Determinism Abstract Domain").

:- doc(author, "V@'{i}ctor P@'{e}rez").
:- doc(author, "Francisco Bueno").
:- doc(author, "Pedro Lopez-Garcia").
:- doc(author, "Manuel Hermenegildo").
:- doc(author, "Jose F. Morales").

:- doc(module, "This module provides the abstract operations of a
nonfailure+determinism domain, @tt{nfdet}, by merging the @tt{nf} and
@tt{det} abstract domains into a combined domain. The @tt{nf} domain
@cite{nfplai-flops04} originated as a re-cast of the @tt{nfg}
non-failure analysis @cite{non-failure-iclp97}, by writing the
corresponding abstract operations for the PLAI framework. @tt{nfg} was
the first non-failure analysis algorithm (which had a specific
fixpoint) implemented in CiaoPP. Similarly, the @tt{det} abstract
domain originated as a re-cast for PLAI of the @tt{detg} determinacy
analysis @cite{determinacy-ngc09,determ-lopstr04}. The @tt{detg} and
@tt{det} implementations reused most of the code of @tt{nfg} and
@tt{nf} respectively.

Abstract operations of this @{nfdet} domain are a tuple of
@tt{(@var{Types},@var{SharingFreeness},@var{Nonfailure},@var{Determinism})}
elements, where @var{Types} carries types info, @var{SharingFreeness},
sharing+freeness info; @var{Nonfailure}, nonfailure info; and
@var{Determinism}, determinism info.

The abstract domain lattice for nonfailure+determinism, covering and
mutual exclusion are (property - interval describing number of solutions):

@begin{verbatim}
          nondet [0,inf]
          /        \\
         /          \\
     semidet [0,1]  multi [1,inf]
        /       \\     /
       /         \\   /     
    fails [0,0]   det [1,1]  
            \\      /
             \\    /
          bottom (non reachable)
@end{verbatim}

@begin{itemize}
@item @tt{semidet} = 0 or 1 solutions
@item @tt{multi} = 1 or more solutions
@item @tt{det} = 1 solution
@item @tt{fails} = 0 solutions
@end{itemize}

").

%% The following table explains the properties in this domain w.r.t. the
%% properties used initially in CiaoPP in nf and det domains:
%% 
%% @begin{verbatim}
%% ----------------+---------------------------------
%%  nf/det         | is_det   possibly_nondet/nondet
%%                 | (0 or 1) (top/2 or more)
%% ----------------+---------------------------------
%%  $bottom/fails  | fails    fails
%%  not_fails      | det      multi
%%  possibly_fails | semidet  nondet
%% ----------------+---------------------------------
%% @end{verbatim}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(domain(eterms)).
:- use_module(domain(sharefree)).
:- use_module(domain(nfdet/nfabs)).
:- use_module(domain(nfdet/detabs)).

:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(sets), [ord_subtract/3]).
:- use_module(library(sort), [sort/2]).

%------------------------------------------------------------------------%

:- export(nfdet_asub/1).

:- doc(nfdet_asub(ASub), "@var{ASub} is an abstract substitution term
   used in nf. It contains types, modes, nonfailure and determinism
   information.").

:- regtype nfdet_asub(ASub)
   # "@var{ASub} is an abstract substitution term used in nfdet.".

nfdet_asub('$bottom').
nfdet_asub(nfdet(Types,Modes,Nf,Det)) :-
    term(Types),
    term(Modes),
    nfabs_asub(Nf),
    detabs_asub(Det).

:- export(asub/5).

asub(nfdet(Types,Modes,NonF,Det), Types, Modes, NonF, Det).

%------------------------------------------------------------------------%

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

nfdet_init_abstract_domain([variants,widen]) :-
    push_pp_flag(variants, off),
    push_pp_flag(widen, on).

%------------------------------------------------------------------------%
% nfdet_call_to_entry(+,+,+,+,+,+,+,-,-)                                 %
% nfdet_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)           %
%------------------------------------------------------------------------%

nfdet_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) :-
    nfdet:asub(Proj,PTypes,PModes,PNonF,PDet),
    shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PModes,EModes,ExtraInfoModes),
    eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PTypes,ETypes,ExtraInfoTypes),
    ( ETypes = '$bottom' ->
        Entry = '$bottom'
    ; % Obtaining invars for nf
      shfr_obtain_info(free,Sv,PModes,FVars),
      ord_subtract(Sv,FVars,InVarsNf),
      % Obtaining invars for det
      shfr_obtain_info(ground,Sv,PModes,InVarsDet),
      detabs:det_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PDet,InVarsDet,EDet,_ExtraDet),
      %
      nfabs:nf_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PNonF,InVarsNf,ENonF0,_ExtraNf),
      ( nfabs:possibly_fail_unif_tests(ENonF0,PModes) ->
          nfabs:nf_unknown_call(Sg,InVarsNf,ENonF0,ENonF)
      ; ENonF0 = ENonF
      ),
      nfdet:asub(Entry,ETypes,EModes,ENonF,EDet)
    ),
    nfdet:asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,InVarsNf,InVarsDet).

%------------------------------------------------------------------------%
% nfdet_exit_to_prime(+,+,+,+,+,-,-)                                     %
% nfdet_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                %
%------------------------------------------------------------------------%

nfdet_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom') :- !.
nfdet_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) :-
    nfdet:asub(Exit,ETypes,EModes,ENonF,EDet),
    nfdet:asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes,ExtraInfoNonF,ExtraInfoDet),
    shfr_exit_to_prime(Sg,Hv,Head,Sv,EModes,ExtraInfoModes,PModes),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,ETypes,ExtraInfoTypes,PTypes),
    ( PTypes = '$bottom' ->
        Prime = '$bottom'
    ; detabs:det_exit_to_prime(Sg,Hv,Head,Sv,EDet,ExtraInfoDet,PDet),
      nfabs:nf_exit_to_prime(Sg,Hv,Head,Sv,ENonF,ExtraInfoNonF,PNonF),
      ( ( PNonF = '$bottom' ; PDet = '$bottom') ->
          Prime = '$bottom'
      ; nfdet:asub(Prime,PTypes,PModes,PNonF,PDet)
      )
    ).

%------------------------------------------------------------------------%
% nfdet_project(+,+,+,+,-)                                               %
% nfdet_project(Sg,Vars,HvFv_u,ASub,Proj)                                %
%------------------------------------------------------------------------%

nfdet_project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom') :- !.
nfdet_project(Sg,Vars,HvFv_u,ASub,Proj) :-
    nfdet:asub(ASub,ATypes,AModes,ANonF,ADet),
    shfr_project(Sg,Vars,HvFv_u,AModes,PModes),
    eterms_project(Sg,Vars,HvFv_u,ATypes,PTypes),
    nfabs:nf_project(Sg,Vars,HvFv_u,ANonF,PNonF),
    detabs:det_project(Sg,Vars,HvFv_u,ADet,PDet),
    nfdet:asub(Proj,PTypes,PModes,PNonF,PDet).

%------------------------------------------------------------------------%
% nfdet_extend(+,+,+,+,-)                                                %
% nfdet_extend(Sg,Prime,Sv,Call,Succ)                                    %
%------------------------------------------------------------------------%

nfdet_extend(_Sg,'$bottom',_Sv,_Call,'$bottom') :- !.
nfdet_extend(Sg,Prime,Sv,Call,Succ) :-
    nfdet:asub(Prime,PTypes,PModes,PNonF,PDet),
    nfdet:asub(Call,CTypes,CModes,CNonF,CDet),
    shfr_extend(Sg,PModes,Sv,CModes,SModes),
    eterms_extend(Sg,PTypes,Sv,CTypes,STypes),
    nfabs:nf_extend(Sg,PNonF,Sv,CNonF,SNonF),
    detabs:det_extend(Sg,PDet,Sv,CDet,SDet),
    nfdet:asub(Succ,STypes,SModes,SNonF,SDet).

nfdet_needs(clauses_lub) :- !.
nfdet_needs(split_combined_domain) :- !.
nfdet_needs(X) :-
    eterms_needs(X),!.
nfdet_needs(X) :-
    shfr_needs(X).

%------------------------------------------------------------------------%
% nfdet_widen(+,+,-)                                                     %
% nfdet_widen(ASub1,ASub2,ASub)                                          %
%------------------------------------------------------------------------%

nfdet_widen('$bottom',ASub1,ASub) :- !,ASub = ASub1.
nfdet_widen(ASub0,'$bottom',ASub) :- !,ASub = ASub0.
nfdet_widen(ASub0,ASub1,ASub):-
    nfdet:asub(ASub0,ATypes0,AModes0,ANonF0,ADet0),
    nfdet:asub(ASub1,ATypes1,AModes1,ANonF1,ADet1),
    shfr_compute_lub([AModes0,AModes1],AModes),
    eterms_widen(ATypes0,ATypes1,ATypes),
    nfabs:nf_widen(ANonF0,ANonF1,ANonF),
    detabs:det_compute_lub([ADet0,ADet1],ADet),
    nfdet:asub(ASub,ATypes,AModes,ANonF,ADet).

%------------------------------------------------------------------------%
% nfdet_widencall(+,+,-)                                                 %
% nfdet_widencall(ASub1,ASub2,ASub)                                      %
%------------------------------------------------------------------------%

nfdet_widencall('$bottom',ASub1,ASub) :- !,ASub = ASub1.
nfdet_widencall(ASub0,'$bottom',ASub) :- !,ASub = ASub0.
nfdet_widencall(ASub0,ASub1,ASub):-
    nfdet:asub(ASub0,ATypes0,_AModes0,_ANonF0,_ADet0),
    nfdet:asub(ASub1,ATypes1,AModes1,ANonF1,ADet1),
    % assuming _AModes0 =< AModes1,_ANonF0 =< ANonF1 and _ADet0 =< ADet1
    eterms_widencall(ATypes0,ATypes1,ATypes),
    nfdet:asub(ASub,ATypes,AModes1,ANonF1,ADet1).

%------------------------------------------------------------------------%
% nfdet_compute_lub(+,-)                                                 %
% nfdet_compute_lub(ListASub,Lub)                                        %
%------------------------------------------------------------------------%

nfdet_compute_lub(ListASub,Lub):-
    split(ListASub,LTypes,LModes,LNonF,LDet),
    shfr_compute_lub(LModes,LubModes),
    eterms_compute_lub(LTypes,LubTypes),
    nfabs:nf_compute_lub(LNonF,LubNonF),
    detabs:det_compute_lub(LDet,LubDet),
    nfdet:asub(Lub,LubTypes,LubModes,LubNonF,LubDet).

split([],[],[],[],[]).
split(['$bottom'|ListASub],LTypes,LModes,LNonF,LDet):- !,
    split(ListASub,LTypes,LModes,LNonF,LDet).
split([ASub|ListASub],[ATypes|LTypes],[AModes|LModes],[ANonF|LNonF],[ADet|LDet]) :-
    nfdet:asub(ASub,ATypes,AModes,ANonF,ADet),
    split(ListASub,LTypes,LModes,LNonF,LDet).

nfdet_split_combined_domain(ListASub,[LTypes,LModes,LNonFDet],[eterms,shfr,nfdet]):-
    ( var(LTypes) ->
        split(ListASub,LTypes,LModes,_LNonF,_LDet),
        LNonFDet = ListASub
    ; split_back(ListASub,LTypes,LModes,LNonFDet)
    ).

split_back([],[],[],[]).
split_back([ASub|ListASub],[ATypes|LTypes],[AModes|LModes],[ASubNonFDet|LNonFDet]) :-
    ( ATypes == '$bottom' -> ASub = '$bottom'
    ; AModes == '$bottom' -> ASub = '$bottom'
    ; nfdet:asub(ASub,ATypes,AModes,ANonF,ADet),
      nfdet:asub(ASubNonFDet,_ATypes,_AModes,ANonF,ADet)
    ),
    split_back(ListASub,LTypes,LModes,LNonFDet).

%------------------------------------------------------------------------%
% nfdet_compute_clauses_lub(+,-)                                         %
% nfdet_compute_clauses_lub(ListASub,Lub)                                %
%------------------------------------------------------------------------%

nfdet_compute_clauses_lub(['$bottom'],_Proj,['$bottom']):- !.
nfdet_compute_clauses_lub([ASub],Proj,[Lub]):-
    nfdet:asub(ASub,ATypes,AModes,ANonFList,ADetList),
    nfdet:asub(Proj,PTypes,PModes,_PNonFList,_PDetList),
    % Modetypes for covering computation:
    compute_modetypes_nf(PTypes,PModes,_Head,ModeTypesNf),
    % Modetypes for mutual exclusion computation:
    compute_modetypes_det(PTypes,PModes,_Head,ModeTypesDet),
    nf_compute_covering(ModeTypesNf,ANonFList,LubNonF),
    det_compute_mut_exclusion(ModeTypesDet,ADetList,LubDet),
    nfdet:asub(Lub,ATypes,AModes,LubNonF,LubDet).

compute_modetypes_nf(Types,Modes,Head,MTypes):-
    % shfr_obtain_info(free,_Vars,Modes,FVars), % PLG
    shfr_obtain_info(free,Modes,FVars), % Added PLG
    sort(Types,Types_s),
    compute_modetypes0_nf(Types_s,FVars,Vars,ModeTypes),
    Head =.. [p|Vars],
    MTypes =.. [p|ModeTypes].

compute_modetypes0_nf([],_FVars,[],[]).
compute_modetypes0_nf([Var:(_,T)|Types],FVars,[Var|Vars],[M:T|ModeTypes]):-
    get_mode_nf(Var,FVars,M),
    compute_modetypes0_nf(Types,FVars,Vars,ModeTypes).

get_mode_nf(Var,FVars,M):-
    memberchk(Var,FVars), !,
    M = out.
get_mode_nf(_Var,_GVars,in).

compute_modetypes_det(Types,Modes,Head,MTypes):-
    shfr_obtain_info(ground,Modes,FVars), % Added. Aug 24, 2012 -PLG
    % shfr_obtain_info(free,Modes,FVars), % Commented out. Aug 24, 2012. Not a safe asumption -PLG.
    sort(Types,Types_s),
    compute_modetypes0_det(Types_s,FVars,Vars,ModeTypes),
    Head =.. [p|Vars],
    MTypes =.. [p|ModeTypes].

compute_modetypes0_det([],_FVars,[],[]).
compute_modetypes0_det([Var:(_,T)|Types],FVars,[Var|Vars],[M:T|ModeTypes]):-
    get_mode_det(Var,FVars,M),
    compute_modetypes0_det(Types,FVars,Vars,ModeTypes).

get_mode_det(Var,FVars,M):-          % Added. Aug 24, 2012 -PLG
    memberchk(Var,FVars), !,
    M = in.
get_mode_det(_Var,_GVars,out).

%------------------------------------------------------------------------%
% nfdet_glb(+,+,-)                                                       %
% nfdet_glb(ASub0,ASub1,Glb)                                             %
%------------------------------------------------------------------------%

nfdet_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
nfdet_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
nfdet_glb(ASub0,ASub1,Glb):-
    nfdet:asub(ASub0,ATypes0,AModes0,ANonF0,ADet0),
    nfdet:asub(ASub1,ATypes1,AModes1,ANonF1,ADet1),
    shfr_glb(AModes0,AModes1,GModes),
    eterms_glb(ATypes0,ATypes1,GTypes),
    nfabs:nf_glb(ANonF0,ANonF1,GNonF),
    detabs:det_glb(ADet0,ADet1,GDet),
    nfdet:asub(Glb,GTypes,GModes,GNonF,GDet).

%------------------------------------------------------------------------%

nfdet_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)

%------------------------------------------------------------------------%
% nfdet_less_or_equal(+,+)                                               %
% nfdet_less_or_equal(ASub0,ASub1)                                       %
%------------------------------------------------------------------------%

nfdet_less_or_equal('$bottom','$bottom'):- !.
nfdet_less_or_equal(ASub0,ASub1):-
    nfdet:asub(ASub0,ATypes0,AModes0,ANonF0,ADet0),
    nfdet:asub(ASub1,ATypes1,AModes1,ANonF1,ADet1),
    shfr_less_or_equal(AModes0,AModes1),
    eterms_less_or_equal(ATypes0,ATypes1),
    nfabs:nf_less_or_equal(ANonF0,ANonF1),
    detabs:det_less_or_equal(ADet0,ADet1).

%------------------------------------------------------------------------%
% nfdet_identical_abstract(+,+)                                          %
% nfdet_identical_abstract(ASub1,ASub2)                                  %
%------------------------------------------------------------------------%

nfdet_identical_abstract('$bottom','$bottom'):- !.
nfdet_identical_abstract(ASub0,ASub1):-
    nfdet:asub(ASub0,ATypes0,AModes0,ANonF0,ADet0),
    nfdet:asub(ASub1,ATypes1,AModes1,ANonF1,ADet1),
    AModes0 == AModes1,
    eterms_identical_abstract(ATypes0,ATypes1),
    nfabs:nf_identical_abstract(ANonF0,ANonF1),
    detabs:det_identical_abstract(ADet0,ADet1).

%------------------------------------------------------------------------%
% nfdet_abs_sort(+,-)                                                    %
% nfdet_abs_sort(ASub0,ASub1)                                            %
%------------------------------------------------------------------------%

nfdet_abs_sort('$bottom','$bottom'):- !.
nfdet_abs_sort(ASub0,ASub1):-
    nfdet:asub(ASub0,ATypes0,AModes0,ANonF0,ADet0),
    shfr_abs_sort(AModes0,AModes1),
    eterms_abs_sort(ATypes0,ATypes1),
    nfabs:nf_abs_sort(ANonF0,ANonF1),
    detabs:det_abs_sort(ADet0,ADet1),
    nfdet:asub(ASub1,ATypes1,AModes1,ANonF1,ADet1).

%------------------------------------------------------------------------%
% nfdet_call_to_success_fact(+,+,+,+,+,+,+,-,-)                          %
% nfdet_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)       %
%-------------------------------------------------------------------------

nfdet_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    nfdet:asub(Call,CTypes,CModes,CNonF,CDet),
    nfdet:asub(Proj,PTypes,PModes,PNonF,PDet),
    shfr_call_to_success_fact(Sg,Hv,Head,K,Sv,CModes,PModes,RModes,SModes),
    eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,CTypes,PTypes,RTypes,STypes),
    nfabs:nf_call_to_success_fact(Sg,Hv,Head,K,Sv,CNonF,PNonF,RNonF,SNonF),
    detabs:det_call_to_success_fact(Sg,Hv,Head,K,Sv,CDet,PDet,RDet,SDet),
    nfdet:asub(Prime,RTypes,RModes,RNonF,RDet),
    nfdet:asub(Succ,STypes,SModes,SNonF,SDet).


%-------------------------------------------------------------------------
% nfdet_special_builtin(+,+,+,-,-)                                       |
% nfdet_special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                  |
%-------------------------------------------------------------------------

nfdet_special_builtin(SgKey,Sg,_Subgoal,SgKey,Sg):-
    nfabs:nf_special_builtin(SgKey).
nfdet_special_builtin(SgKey,Sg,_Subgoal,SgKey,Sg):-
    detabs:det_special_builtin(SgKey).

%-------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [special_builtin/6]).

nfdet_combined_special_builtin0(SgKey,Domains) :-
    % TODO: refactor (define a nondet pred with combined domains instead)
    ( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nfdet]
    ; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nfdet]
    ; special_builtin(nf,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nfdet]
    ; special_builtin(det,SgKey,_Sg,SgKey,_Type,_Condvars) ->
        Domains=[eterms,shfr,nfdet]
    ; fail
    ).

%-------------------------------------------------------------------------
% nfdet_success_builtin(+,+,+,+,+,-)                                     %
% nfdet_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)                %
%-------------------------------------------------------------------------

nfdet_success_builtin(Type,_Sv_u,Sg,HvFv_u,Call,Succ):-
    nfdet:asub(Call,Types,Modes,CallNonF,CallDet),
    nfabs:nf_success_builtin(Type,Modes,Sg,HvFv_u,CallNonF,SuccNonF),
    detabs:det_success_builtin(Type,Modes,Sg,HvFv_u,CallDet,SuccDet),
    nfdet:asub(Succ,Types,Modes,SuccNonF,SuccDet).

%-------------------------------------------------------------------------
% nfdet_call_to_success_builtin(+,+,+,+,+,-)                             %
% nfdet_call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)              %
%-------------------------------------------------------------------------
% Not used

%------------------------------------------------------------------------%
% nfdet_input_interface(+,+,+,-)                                         %
% nfdet_input_interface(InputUser,Kind,StructI,StructO)                  %
%------------------------------------------------------------------------%

nfdet_input_interface(InputUser,Kind,StructI,StructO):-
    ( nonvar(Kind) ->
        KModes=Kind, KTypes=Kind, KNonF=Kind, KDet = Kind
    ; true
    ),
    nfdet:asub(StructI,ITypes,IModes,INonF,IDet),
    shfr_input_interface_(InputUser,KModes,IModes,OModes),
    eterms_input_interface_(InputUser,KTypes,ITypes,OTypes),
    nf_input_interface_(InputUser,KNonF,INonF,ONonF),
    det_input_interface_(InputUser,KDet,IDet,ODet),
    nfdet:asub(StructO,OTypes,OModes,ONonF,ODet).

shfr_input_interface_(InputUser,Kind,IModes,OModes):-
    shfr_input_interface(InputUser,Kind,IModes,OModes), !.
shfr_input_interface_(_InputUser,_Kind,IModes,IModes).

eterms_input_interface_(InputUser,Kind,ITypes,OTypes):-
    eterms_input_interface(InputUser,Kind,ITypes,OTypes), !.
eterms_input_interface_(_InputUser,_Kind,ITypes,ITypes).

nf_input_interface_(InputUser,Kind,INonF,ONonF):-
    nfabs:nf_input_interface(InputUser,Kind,INonF,ONonF), !.
nf_input_interface_(_InputUser,_Kind,INonF,INonF).

det_input_interface_(InputUser,Kind,IDet,ODet):-
    detabs:det_input_interface(InputUser,Kind,IDet,ODet), !.
det_input_interface_(_InputUser,_Kind,IDet,IDet).

%------------------------------------------------------------------------%
% nfdet_input_user_interface(+,+,-,+,+)                                  %
% nfdet_input_user_interface(InputUser,Qv,ASub)                          %
%------------------------------------------------------------------------%

nfdet_input_user_interface(Struct,Qv,ASub,Sg,MaybeCallASub):-
    nfdet:asub(Struct,Types,Modes,NonF,Det),
    shfr_input_user_interface(Modes,Qv,AModes,Sg,MaybeCallASub),
    eterms_input_user_interface(Types,Qv,ATypes,Sg,MaybeCallASub),
    nfabs:nf_input_user_interface(NonF,Qv,ANonF,Sg,MaybeCallASub),
    detabs:det_input_user_interface(Det,Qv,ADet,Sg,MaybeCallASub),
    nfdet:asub(ASub,ATypes,AModes,ANonF,ADet).

%------------------------------------------------------------------------%
% nfdet_asub_to_native(+,+,+,-,-)                                        %
% nfdet_asub_to_native(ASub,Qv,OutFlag,Stat,Comp)                        %
%------------------------------------------------------------------------%
% Qv should be the goal for comp-props!!!!!

nfdet_asub_to_native(ASub,Qv,OutFlag,Props,CompProps):-
    nfdet:asub(ASub,ATypes,AModes,ANonF,ADet),
    shfr_asub_to_native(AModes,Qv,OutFlag,Props1,_),
    eterms_asub_to_native(ATypes,Qv,OutFlag,Props2,_),
    nfabs:nf_asub_to_native(ANonF,Qv,NfProps),
    detabs:det_asub_to_native(ADet,Qv,DetProps),
    combine_nfdet_info(NfProps,DetProps,CompProps),
    append(Props1,Props2,Props).

combine_nfdet_info([PropF,PropC],[PropD,PropM],[PropFD,PropC,PropM]) :-
    PropF =.. [F|Vars],
    PropD =.. [D|_],
    combine_nfdet_info_(F,D,FD),
    PropFD =.. [FD|Vars].

% Unreachable:
%% combine_nfdet_info_(fails,_,_) :- !, fail.
combine_nfdet_info_(not_fails,is_det,det) :- !.
combine_nfdet_info_(possibly_fails,is_det,semidet) :- !.
combine_nfdet_info_(not_fails,_,multi) :- !.
combine_nfdet_info_(possibly_fails,_,nondet).

:- dom_impl(nfdet, collect_auxinfo_asub/3).
:- export(nfdet_collect_auxinfo_asub/3).
nfdet_collect_auxinfo_asub(Struct,Types,Types1) :-
    nfdet:asub(Struct,ATypes,_,_,_),
    eterms_collect_auxinfo_asub(ATypes,Types,Types1).

:- dom_impl(nfdet, rename_auxinfo_asub/3).
:- export(nfdet_rename_auxinfo_asub/3).
nfdet_rename_auxinfo_asub(ASub, Dict, RASub) :-
    nfdet:asub(ASub,ATypes,AModes,ANonf,ADet),
    eterms_rename_auxinfo_asub(ATypes, Dict,RATypes),
    nfdet:asub(RASub,RATypes,AModes,ANonf,ADet).

%------------------------------------------------------------------------%
% nf_unknown_call(+,+,+,-)                                               %
% nf_unknown_call(Sg,Vars,Call,Succ)                                     %
%------------------------------------------------------------------------%

nfdet_unknown_call(Sg,Vars,Call,Succ):-
    nfdet:asub(Call,CTypes,CModes,CNonF,CDet),
    shfr_unknown_call(Sg,Vars,CModes,SModes),
    eterms_unknown_call(Sg,Vars,CTypes,STypes),
    nfabs:nf_unknown_call(Sg,Vars,CNonF,SNonF),
    detabs:det_unknown_call(Sg,Vars,CDet,SDet),
    nfdet:asub(Succ,STypes,SModes,SNonF,SDet).

%------------------------------------------------------------------------%
% nfdet_unknown_entry(+,+,-)                                             %
% nfdet_unknown_entry(Sg,Vars,Entry)                                     %
%------------------------------------------------------------------------%

nfdet_unknown_entry(Sg,Vars,Entry):-
    shfr_unknown_entry(Sg,Vars,EModes),
    eterms_unknown_entry(Sg,Vars,ETypes),
    nfabs:nf_unknown_entry(Sg,Vars,ENonF),
    detabs:det_unknown_entry(Sg,Vars,EDet),
    nfdet:asub(Entry,ETypes,EModes,ENonF,EDet).

%------------------------------------------------------------------------%
% nfdet_empty_entry(+,+,-)                                               %
% nfdet_empty_entry(Sg,Vars,Entry)                                       %
%------------------------------------------------------------------------%

nfdet_empty_entry(Sg,Vars,Entry):-
    shfr_empty_entry(Sg,Vars,EModes),
    eterms_empty_entry(Sg,Vars,ETypes),
    nfabs:nf_empty_entry(Sg,Vars,ENonF),
    detabs:det_empty_entry(Sg,Vars,EDet),
    nfdet:asub(Entry,ETypes,EModes,ENonF,EDet).

%-----------------------------------------------------------------------

nfdet_dom_statistics(Info) :-
    nfabs:nfabs_dom_statistics(InfoNf),
    detabs:detabs_dom_statistics(InfoDet),
    append(InfoNf,InfoDet,Info).

%-----------------------------------------------------------------------

nfdet_obtain_info(Prop,Vars,ASub0,Info) :- knows_of(Prop,eterms), !,
    nfdet:asub(ASub0,ASub,_,_,_),
    eterms_obtain_info(Prop,Vars,ASub,Info).
nfdet_obtain_info(Prop,Vars,ASub0,Info) :- knows_of(Prop,shfr), !,
    nfdet:asub(ASub0,_,ASub,_,_),
    shfr_obtain_info(Prop,Vars,ASub,Info).
nfdet_obtain_info(Prop,_Vars,ASub0,Info) :- knows_of(Prop,nf), !,
    nfdet:asub(ASub0,_,_,ASub,_),
    nfabs:nf_asub_to_native(ASub,_,Info).
nfdet_obtain_info(Prop,_Vars,ASub0,Info) :- knows_of(Prop,det),
    nfdet:asub(ASub0,_,_,_,ASub),
    detabs:det_asub_to_native(ASub,_,Info).
