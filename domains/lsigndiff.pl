%------------------------------------------------------------------------%
%                                                                        %
%                          started: 5/5/95                               %
%                       programmer: M. Garcia de la Banda                %
%                                                                        %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% simple_lsign_project(+,+,+,+,-)                                        |
% simple_lsign_project(Sg,Vars,HvFv_u,ACons,Proj)                        |
%-------------------------------------------------------------------------

simple_lsign_project(_Sg,Vars,HvFv_u,p(_,_,Tot),Proj):-
	lsign_project(Tot,Vars,HvFv_u,Proj).

%------------------------------------------------------------------------%
% simple_lsign_call_to_entry(+,+,+,+,+,+,+,-,-)                          %
% simple_lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)    %
%------------------------------------------------------------------------%

simple_lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo):-
	lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry1,ExtraInfo),
	Entry1 = a(G,_,_),
	Entry = p(Entry1,a(G,[],[]),Entry1).

%------------------------------------------------------------------------%
% simple_lsign_exit_to_prime(+,+,+,+,+,-)                                |
% simple_lsign_exit_to_prime(Sg,Hv,Head,Exit,ExtraInfo,Prime)            |
%------------------------------------------------------------------------%

simple_lsign_exit_to_prime(_,_,_,'$bottom',_,'$bottom') :- !.
simple_lsign_exit_to_prime(Sg,Hv,Head,p(_,Exit,_),ExtraInfo,Prime):-
	lsign_exit_to_prime(Sg,Hv,Head,Exit,ExtraInfo,Prime).

%-------------------------------------------------------------------------
% simple_lsign_extend(+,+,+,+,-)                                         %
% simple_lsign_extend(Sg,Prime,Sv,Call,Succ)                             %
%------------------------------------------------------------------------%

simple_lsign_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
simple_lsign_extend(_Sg,[],_Sv,Call,Succ):- !,
	Succ = Call.
simple_lsign_extend(_Sg,Prime,_Sv,p(In,DACons,TACons),Succ):- 
	lsign_sum(Prime,TACons,STACons),
	lsign_sum(Prime,DACons,SDACons),
	STACons = a(G,_,_),
	SDACons = a(_,L,Non),
	Succ = p(In,a(G,L,Non),STACons).

%-------------------------------------------------------------------------
% simple_lsign_sort(+,-)                                                 |
% simple_lsign_sort(ACons_u,ACons)                                       |
%-------------------------------------------------------------------------

simple_lsign_sort(p(_,_,ACons_u),Sorted):- !,
	lsign_sort(ACons_u,ACons),
	ACons = a(G,_,_),
	Sorted = p(ACons,a(G,[],[]),ACons).
simple_lsign_sort(ACons_u,ACons):-
	lsign_sort(ACons_u,ACons).

%-------------------------------------------------------------------------
% simple_lsign_unknown_entry(+,-)                                        |
% simple_lsign_unknown_entry(Qv,Call)                                    |
%-------------------------------------------------------------------------

simple_lsign_unknown_entry(Qv,p(Call,a([],[],[]),Call)):-
	lsign_unknown_entry(Qv,Call).

simple_lsign_unknown_call(_Sg,_Qv,_Call,_Succ):-
	throw(not_implemented(simple_lsign_unknown_call)).

simple_lsign_empty_entry(_Qv,_Call):-
	throw(not_implemented(simple_lsign_empty_entry)).

simple_lsign_less_or_equal(_ACons0,_ACons1):-
	throw(not_implemented(simple_lsign_less_or_equal)).

%-------------------------------------------------------------------------
% simple_lsign_input_user_interface(+,+,-)                               %
% simple_lsign_input_user_interface(InputUser,Qv,ACons)                  %
%-------------------------------------------------------------------------

simple_lsign_input_user_interface(Info,Qv,ACons):-
	lsign_input_user_interface(Info,Qv,In),
	In = a(G,_,_),
	ACons = p(In,a(G,[],[]),In).

%------------------------------------------------------------------------%
% simple_lsign_output_interface(+,-)                                     %
% simple_lsign_output_interface(ACons,Output)                            %
%-------------------------------------------------------------------------

simple_lsign_output_interface(p(_,_,Tot),Output):- !,
	lsign_output_interface(Tot,Output).
simple_lsign_output_interface(ACons,Output):-
	lsign_output_interface(ACons,Output).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
% simple_lsign_success_builtin(+,+,+,+,-,-)                              |
% simple_lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)         |
%-------------------------------------------------------------------------
 
simple_lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,p(In,Diff,Tot),Succ):-
 	lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Tot,NewTot),
 	( NewTot = '$bottom' -> 
	    Succ = '$bottom'	
	; simple_lsign_success_builtin0(Type,Sv_u,Condv,HvFv_u,Diff,NewDiff),
	  Succ = p(In,NewDiff,NewTot)
	).


%-------------------------------------------------------------------------
% lsign_success_builtin(+,+,+,+,-,-) 
% lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ) 
%-------------------------------------------------------------------------
% Adds the information of builtins
%-------------------------------------------------------------------------

simple_lsign_success_builtin0(is,Sv_u,is(X,Y),HvFv_u,Call,Succ):-  !,
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
simple_lsign_success_builtin0(Type,Sv_u,Condv,HvFv_u,Call,Succ):-
	lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ).
