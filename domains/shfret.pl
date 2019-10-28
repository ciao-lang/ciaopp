:- module(shfret,
	[ shfret_init_abstract_domain/1,
	  shfret_call_to_entry/9,
	  shfret_exit_to_prime/7,
	  shfret_project/5,
	  shfret_extend/5,
	  shfret_widen/3,
	  shfret_widencall/3,
	  shfret_compute_lub/2,
	  shfret_glb/3,
	  shfret_eliminate_equivalent/2,
	  shfret_less_or_equal/2,
	  shfret_identical_abstract/2,
	  shfret_abs_sort/2,
	  shfret_call_to_success_fact/9,
	  shfret_combined_special_builtin0/2,
	  shfret_split_combined_domain/3,
	  shfret_input_interface/4,
	  shfret_input_user_interface/5,
	  shfret_asub_to_native/5,
	  shfret_unknown_call/4,
	  shfret_unknown_entry/3,
	  shfret_empty_entry/3
	],
	[ assertions,regtypes,basicmodes
	]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shfret).
:- dom_impl(shfret, init_abstract_domain/1).
:- dom_impl(shfret, call_to_entry/9).
:- dom_impl(shfret, exit_to_prime/7).
:- dom_impl(shfret, project/5).
:- dom_impl(shfret, widencall/3).
:- dom_impl(shfret, widen/3).
:- dom_impl(shfret, compute_lub/2).
:- dom_impl(shfret, identical_abstract/2).
:- dom_impl(shfret, abs_sort/2).
:- dom_impl(shfret, extend/5).
:- dom_impl(shfret, less_or_equal/2).
:- dom_impl(shfret, glb/3).
:- dom_impl(shfret, eliminate_equivalent/2).
:- dom_impl(shfret, call_to_success_fact/9).
:- dom_impl(shfret, combined_special_builtin0/2).
:- dom_impl(shfret, split_combined_domain/3).
:- dom_impl(shfret, input_interface/4).
:- dom_impl(shfret, input_user_interface/5).
:- dom_impl(shfret, asub_to_native/5).
:- dom_impl(shfret, unknown_call/4).
:- dom_impl(shfret, unknown_entry/3).
:- dom_impl(shfret, empty_entry/3).

:- use_module(domain(eterms)).
:- use_module(domain(sharefree)).

%% :- use_module(library(idlists),[memberchk/2]).
:- use_module(library(lists), [append/3]).
%% :- use_module(library(sets),[ord_subtract/3]).
%% :- use_module(library(sort),[sort/2]).

asub(comb(Types,Modes),Types,Modes).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

shfret_init_abstract_domain([variants,widen]) :-
	push_pp_flag(variants,off),
	push_pp_flag(widen,on).

%------------------------------------------------------------------------%
% shfret_call_to_entry(+,+,+,+,+,+,+,-,-)                                %
% shfret_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)          %
%------------------------------------------------------------------------%
shfret_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo):-
	asub(Proj,PTypes,PModes),
	shfr_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PModes,EModes,ExtraInfoModes),
	eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,PTypes,ETypes,ExtraInfoTypes),
	( ETypes = '$bottom'
	-> Entry = '$bottom'
	 ; asub(Entry,ETypes,EModes)
	),
	asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes).

%------------------------------------------------------------------------%
% shfret_exit_to_prime(+,+,+,+,+,-,-)                                        %
% shfret_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                   %
%------------------------------------------------------------------------%
shfret_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom'):- !.
shfret_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
	asub(Exit,ETypes,EModes),
	asub(ExtraInfo,ExtraInfoTypes,ExtraInfoModes),
	shfr_exit_to_prime(Sg,Hv,Head,Sv,EModes,ExtraInfoModes,PModes),
	eterms_exit_to_prime(Sg,Hv,Head,Sv,ETypes,ExtraInfoTypes,PTypes),
	( PTypes = '$bottom'
	-> Prime = '$bottom'
	 ; asub(Prime,PTypes,PModes)
	).

%------------------------------------------------------------------------%
% shfret_project(+,+,+,+,-)                                              %
% shfret_project(Sg,Vars,HvFv_u,ASub,Proj)                               %
%------------------------------------------------------------------------%
shfret_project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
shfret_project(Sg,Vars,HvFv_u,ASub,Proj):-
	asub(ASub,ATypes,AModes),
	shfr_project(Sg,Vars,HvFv_u,AModes,PModes),
	eterms_project(Sg,Vars,HvFv_u,ATypes,PTypes),
	asub(Proj,PTypes,PModes).

%------------------------------------------------------------------------%
% shfret_extend(+,+,+,+,-)                                               %
% shfret_extend(Sg,Prime,Sv,Call,Succ)                                   %
%------------------------------------------------------------------------%
shfret_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
shfret_extend(Sg,Prime,Sv,Call,Succ):-
	asub(Prime,PTypes,PModes),
	asub(Call,CTypes,CModes),
	shfr_extend(Sg,PModes,Sv,CModes,SModes),
	eterms_extend(Sg,PTypes,Sv,CTypes,STypes),
	asub(Succ,STypes,SModes).

%------------------------------------------------------------------------%
% shfret_widen(+,+,-)                                                        %
% shfret_widen(ASub1,ASub2,ASub)                                             %
%------------------------------------------------------------------------%
shfret_widen('$bottom',ASub1,ASub):- !, ASub=ASub1.
shfret_widen(ASub0,'$bottom',ASub):- !, ASub=ASub0.
shfret_widen(ASub0,ASub1,ASub):-
	asub(ASub0,ATypes0,AModes0),
	asub(ASub1,ATypes1,AModes1),
	shfr_compute_lub([AModes0,AModes1],AModes),
	eterms_widen(ATypes0,ATypes1,ATypes),
	asub(ASub,ATypes,AModes).

%------------------------------------------------------------------------%
% shfret_widencall(+,+,-)                                                    %
% shfret_widencall(ASub1,ASub2,ASub)                                         %
%------------------------------------------------------------------------%
shfret_widencall('$bottom',ASub1,ASub):- !, ASub=ASub1.
shfret_widencall(ASub0,'$bottom',ASub):- !, ASub=ASub0.
shfret_widencall(ASub0,ASub1,ASub):-
	asub(ASub0,ATypes0,_AModes0),
	asub(ASub1,ATypes1,AModes1),
	eterms_widencall(ATypes0,ATypes1,ATypes),
	asub(ASub,ATypes,AModes1).

%------------------------------------------------------------------------%
% shfret_compute_lub(+,-)                                                    %
% shfret_compute_lub(ListASub,Lub)                                           %
%------------------------------------------------------------------------%
shfret_compute_lub(ListASub,Lub):-
	split(ListASub,LTypes,LModes),
	shfr_compute_lub(LModes,LubModes),
	eterms_compute_lub(LTypes,LubTypes),
	asub(Lub,LubTypes,LubModes).

split([],[],[]).
split([ASub|ListASub],[ATypes|LTypes],[AModes|LModes]):-
	asub(ASub,ATypes,AModes),
	split(ListASub,LTypes,LModes).

shfret_split_combined_domain(ListASub,[LTypes,LModes],[eterms,shfr]):-
	split(ListASub,LTypes,LModes).

%------------------------------------------------------------------------%
% shfret_glb(+,+,-)                                                          %
% shfret_glb(ASub0,ASub1,Glb)                                                %
%------------------------------------------------------------------------%
shfret_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
shfret_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
shfret_glb(ASub0,ASub1,Glb):-
	asub(ASub0,ATypes0,AModes0),
	asub(ASub1,ATypes1,AModes1),
	shfr_glb(AModes0,AModes1,GModes),
	eterms_glb(ATypes0,ATypes1,GTypes),
	asub(Glb,GTypes,GModes).

%------------------------------------------------------------------------%

shfret_eliminate_equivalent(LSucc,LSucc). % TODO: wrong or not needed? (JF)

%------------------------------------------------------------------------%
% shfret_less_or_equal(+,+)                                                  %
% shfret_less_or_equal(ASub0,ASub1)                                          %
%------------------------------------------------------------------------%
shfret_less_or_equal('$bottom','$bottom'):- !.
shfret_less_or_equal(ASub0,ASub1):-
	asub(ASub0,ATypes0,AModes0),
	asub(ASub1,ATypes1,AModes1),
	shfr_less_or_equal(AModes0,AModes1),
	eterms_less_or_equal(ATypes0,ATypes1).

%------------------------------------------------------------------------%
% shfret_identical_abstract(+,+)                                             %
% shfret_identical_abstract(ASub1,ASub2)                                     %
%------------------------------------------------------------------------%
shfret_identical_abstract('$bottom','$bottom'):- !.
shfret_identical_abstract(ASub0,ASub1):-
	asub(ASub0,ATypes0,AModes0),
	asub(ASub1,ATypes1,AModes1),
	AModes0 == AModes1,
	eterms_identical_abstract(ATypes0,ATypes1).

%------------------------------------------------------------------------%
% shfret_abs_sort(+,-)                                                           %
% shfret_abs_sort(ASub0,ASub1)                                                   %
%------------------------------------------------------------------------%
shfret_abs_sort('$bottom','$bottom'):- !.
shfret_abs_sort(ASub0,ASub1):-
	asub(ASub0,ATypes0,AModes0),
	shfr_abs_sort(AModes0,AModes1),
	eterms_abs_sort(ATypes0,ATypes1),
	asub(ASub1,ATypes1,AModes1).

%------------------------------------------------------------------------%
% shfret_call_to_success_fact(+,+,+,+,+,+,+,-,-)                         %
% shfret_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)      %
%------------------------------------------------------------------------%
shfret_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
	asub(Call,CTypes,CModes),
	asub(Proj,PTypes,PModes),
	shfr_call_to_success_fact(Sg,Hv,Head,K,Sv,CModes,PModes,RModes,SModes),
	eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,CTypes,PTypes,RTypes,STypes),
	asub(Prime,RTypes,RModes),
	asub(Succ,STypes,SModes).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [special_builtin/6, body_builtin/9]).

shfret_combined_special_builtin0(SgKey,Domains) :-
	% TODO: refactor (define a nondet pred with combined domains instead)
	( special_builtin(eterms,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr]
	; special_builtin(shfr,SgKey,_Sg,SgKey,_Type,_Condvars) ->
	    Domains=[eterms,shfr]
	; fail
	).

%------------------------------------------------------------------------%
% shfret_input_interface(+,+,+,-)                                            %
% shfret_input_interface(InputUser,Kind,StructI,StructO)                     %
%------------------------------------------------------------------------%
shfret_input_interface(InputUser,Kind,StructI,StructO):-
        ( nonvar(Kind) ->
            KModes=Kind, KTypes=Kind
        ; true ),
          asub(StructI,ITypes,IModes),
          shfr_input_interface_(InputUser,KModes,IModes,OModes),
          eterms_input_interface_(InputUser,KTypes,ITypes,OTypes),
          asub(StructO,OTypes,OModes).

shfr_input_interface_(InputUser,Kind,IModes,OModes):-
	shfr_input_interface(InputUser,Kind,IModes,OModes), !.
shfr_input_interface_(_InputUser,_Kind,IModes,IModes).

eterms_input_interface_(InputUser,Kind,ITypes,OTypes):-
	eterms_input_interface(InputUser,Kind,ITypes,OTypes), !.
eterms_input_interface_(_InputUser,_Kind,ITypes,ITypes).

%------------------------------------------------------------------------%
% shfret_input_user_interface(+,+,-,+,+)                                 %
% shfret_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)        %
%------------------------------------------------------------------------%
shfret_input_user_interface(Struct,Qv,ASub,Sg,MaybeCallASub):-
	asub(Struct,Types,Modes),
	shfr_input_user_interface(Modes,Qv,AModes,Sg,MaybeCallASub),
	eterms_input_user_interface(Types,Qv,ATypes,Sg,MaybeCallASub),
	asub(ASub,ATypes,AModes).

%------------------------------------------------------------------------%
% shfret_asub_to_native(+,+,+,-,-)                                       %
% shfret_asub_to_native(ASub,Qv,Flag,Props,Comps)                        %
%------------------------------------------------------------------------%
shfret_asub_to_native(ASub,Qv,Flag,Props,Comps):-
	asub(ASub,ATypes,AModes),
	shfr_asub_to_native(AModes,Qv,Flag,Props1,Comps1),
	eterms_asub_to_native(ATypes,Qv,Flag,Props2,Comps2),
	append(Props1,Props2,Props),
	append(Comps1,Comps2,Comps).

%------------------------------------------------------------------------%
% shfret_unknown_call(+,+,+,-)                                           %
% shfret_unknown_call(Sg,Vars,Call,Succ)                                 %
%------------------------------------------------------------------------%
shfret_unknown_call(Sg,Vars,Call,Succ):-
	asub(Call,CTypes,CModes),
	shfr_unknown_call(Sg,Vars,CModes,SModes),
	eterms_unknown_call(Sg,Vars,CTypes,STypes),
	asub(Succ,STypes,SModes).

%------------------------------------------------------------------------%
% shfret_unknown_entry(+,+,-)                                            %
% shfret_unknown_entry(Sg,Vars,Entry)                                    %
%------------------------------------------------------------------------%
shfret_unknown_entry(Sg,Vars,Entry):-
	shfr_unknown_entry(Sg,Vars,EModes),
	eterms_unknown_entry(Sg,Vars,ETypes),
	asub(Entry,ETypes,EModes).

%------------------------------------------------------------------------%
% shfret_empty_entry(+,+,-)                                              %
% shfret_empty_entry(Sg,Vars,Entry)                                      %
%------------------------------------------------------------------------%
shfret_empty_entry(Sg,Vars,Entry):-
	shfr_empty_entry(Sg,Vars,EModes),
	eterms_empty_entry(Sg,Vars,ETypes),
	asub(Entry,ETypes,EModes).
