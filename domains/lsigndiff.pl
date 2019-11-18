:- module(lsigndiff,
    [ difflsign_call_to_entry/9,  
      difflsign_call_to_success_fact/9,
      difflsign_compute_lub/2,
      difflsign_exit_to_prime/7,  
      difflsign_extend/5,
      difflsign_input_user_interface/5,
      difflsign_input_interface/4,
      difflsign_asub_to_native/5,
      difflsign_less_or_equal/2, 
      difflsign_glb/3,
      difflsign_project/5,
      difflsign_abs_sort/2,
      difflsign_special_builtin/5,
      difflsign_success_builtin/6, 
      difflsign_unknown_call/4, 
      difflsign_unknown_entry/3, 
      difflsign_empty_entry/3
    ], [assertions]).

:- doc(title, "lsigndiff domain").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(difflsign).
:- dom_impl(difflsign, call_to_entry/9).
:- dom_impl(difflsign, exit_to_prime/7).
:- dom_impl(difflsign, project/5).
:- dom_impl(difflsign, compute_lub/2).
:- dom_impl(difflsign, abs_sort/2).
:- dom_impl(difflsign, extend/5).
:- dom_impl(difflsign, less_or_equal/2).
:- dom_impl(difflsign, glb/3).
:- dom_impl(difflsign, call_to_success_fact/9).
:- dom_impl(difflsign, special_builtin/5).
:- dom_impl(difflsign, success_builtin/6).
:- dom_impl(difflsign, input_interface/4).
:- dom_impl(difflsign, input_user_interface/5).
:- dom_impl(difflsign, asub_to_native/5).
:- dom_impl(difflsign, unknown_call/4).
:- dom_impl(difflsign, unknown_entry/3).
:- dom_impl(difflsign, empty_entry/3).

% simple lsign domain

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 5/5/95                               %
%                       programmer: M. Garcia de la Banda                %
%                                                                        %
%------------------------------------------------------------------------%

:- use_module(domain(lsign)).

:- use_module(domain(s_grshfr), 
    [ change_values_insert/4,
      collect_vars_freeness/2
    ]).

:- use_module(library(sets), 
    [ ord_subtract/3,
      ord_union_diff/4
    ]).
:- use_module(library(sort)).
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

%------------------------------------------------------------------------%
% difflsign_project(+,+,+,+,-)                                        |
% difflsign_project(Sg,Vars,HvFv_u,ACons,Proj)                        |
%-------------------------------------------------------------------------

difflsign_project(Sg,Vars,HvFv_u,p(_,_,Tot),Proj):-
    lsign_project(Sg,Vars,HvFv_u,Tot,Proj).

%------------------------------------------------------------------------%

difflsign_compute_lub(ListASub,LubASub) :- lsign_compute_lub(ListASub,LubASub).

%------------------------------------------------------------------------%
% difflsign_call_to_entry(+,+,+,+,+,+,+,-,-)                          %
% difflsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)    %
%------------------------------------------------------------------------%

difflsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo):-
    lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry1,ExtraInfo),
    Entry1 = a(G,_,_),
    Entry = p(Entry1,a(G,[],[]),Entry1).

%------------------------------------------------------------------------%
% difflsign_exit_to_prime(+,+,+,+,+,+,-)                                 |
% difflsign_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)            |
%------------------------------------------------------------------------%

difflsign_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom') :- !.
difflsign_exit_to_prime(Sg,Hv,Head,Sv,p(_,Exit,_),ExtraInfo,Prime):-
    lsign_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime).

%-------------------------------------------------------------------------
% difflsign_extend(+,+,+,+,-)                                         %
% difflsign_extend(Sg,Prime,Sv,Call,Succ)                             %
%------------------------------------------------------------------------%

difflsign_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
difflsign_extend(_Sg,[],_Sv,Call,Succ):- !,
    Succ = Call.
difflsign_extend(_Sg,Prime,_Sv,p(In,DACons,TACons),Succ):- 
    lsign_sum(Prime,TACons,STACons),
    lsign_sum(Prime,DACons,SDACons),
    STACons = a(G,_,_),
    SDACons = a(_,L,Non),
    Succ = p(In,a(G,L,Non),STACons).

%-------------------------------------------------------------------------
% difflsign_abs_sort(+,-)                                                 |
% difflsign_abs_sort(ACons_u,ACons)                                       |
%-------------------------------------------------------------------------

difflsign_abs_sort(p(_,_,ACons_u),Sorted):- !,
    lsign_abs_sort(ACons_u,ACons),
    ACons = a(G,_,_),
    Sorted = p(ACons,a(G,[],[]),ACons).
difflsign_abs_sort(ACons_u,ACons):-
    lsign_abs_sort(ACons_u,ACons).

%-------------------------------------------------------------------------
% difflsign_unknown_entry(+,+,-)                                      |
% difflsign_unknown_entry(Sg,Qv,Call)                                 |
%-------------------------------------------------------------------------

difflsign_unknown_entry(Sg,Qv,p(Call,a([],[],[]),Call)):-
    lsign_unknown_entry(Sg,Qv,Call).

difflsign_unknown_call(_Sg,_Qv,_Call,_Succ):-
    throw(not_implemented(difflsign_unknown_call)).

difflsign_empty_entry(_Sg,_Qv,_Call):-
    throw(not_implemented(difflsign_empty_entry)).

difflsign_less_or_equal(_ACons0,_ACons1):-
    throw(not_implemented(difflsign_less_or_equal)).

difflsign_glb(_ASub0,_ASub1,_ASub) :-
    compiler_error(op_not_implemented(glb)), fail.

difflsign_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) :- lsign_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ).

difflsign_special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :- lsign_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

%-------------------------------------------------------------------------
% difflsign_input_user_interface(+,+,-,+,+)                           %
% difflsign_input_user_interface(InputUser,Qv,ACons,Sg,MaybeCallASub) %
%-------------------------------------------------------------------------

difflsign_input_user_interface(Info,Qv,ACons,Sg,MaybeCallASub):-
    lsign_input_user_interface(Info,Qv,In,Sg,MaybeCallASub),
    In = a(G,_,_),
    ACons = p(In,a(G,[],[]),In).

%------------------------------------------------------------------------%
% difflsign_output_interface(+,-)                                     %
% difflsign_output_interface(ACons,Output)                            %
%-------------------------------------------------------------------------

difflsign_asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :-
    difflsign_output_interface(ASub,OutputUser).

difflsign_output_interface(p(_,_,Tot),Output):- !,
    lsign_output_interface(Tot,Output).
difflsign_output_interface(ACons,Output):-
    lsign_output_interface(ACons,Output).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% difflsign_success_builtin(+,+,+,+,-,-)                              |
% difflsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)         |
%-------------------------------------------------------------------------
 
difflsign_success_builtin(Type,Sv_u,Condv,HvFv_u,p(In,Diff,Tot),Succ):-
    lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Tot,NewTot),
    ( NewTot = '$bottom' -> 
        Succ = '$bottom'    
    ; difflsign_success_builtin0(Type,Sv_u,Condv,HvFv_u,Diff,NewDiff),
      Succ = p(In,NewDiff,NewTot)
    ).

%-------------------------------------------------------------------------
% lsign_success_builtin(+,+,+,+,-,-) 
% lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ) 
%-------------------------------------------------------------------------
% Adds the information of builtins
%-------------------------------------------------------------------------

difflsign_success_builtin0(is,Sv_u,is(X,Y),HvFv_u,Call,Succ):-  !,
    Call = a(S,AEqIn,Non),
    sort(Sv_u,Vars),
    collect_vars_freeness(S,Ground),
    ord_subtract(Vars,Ground,NewGround),
    change_values_insert(NewGround,S,NewS,t),
    ord_union_diff(S,NewS,Union,Diff),
    lsign_propagate_fixpoint(Diff,AEqIn,Non,NAEqIn,NNon,Union,NS,F),
    ( F = cons ->
        lsign_success_builtin('=/2',_,p(X,Y),HvFv_u,a(NS,NAEqIn,NNon),Succ)
    ; Succ = '$bottom'
    ).
difflsign_success_builtin0(Type,Sv_u,Condv,HvFv_u,Call,Succ):-
    lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ).

%-------------------------------------------------------------------------

difflsign_input_interface(InputUser,Kind,Struct0,Struct1) :- lsign_input_interface(InputUser,Kind,Struct0,Struct1).

