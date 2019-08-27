/*             Copyright (C)1990-91-92-93 UPM-CLIP                      */
/*                          1993 Katholieke Universiteit Leuven.        */

:- module(fd,
	[ fd_call_to_entry/6,
	  fd_call_to_success_fact/8,
	  fd_compute_lub/2,   
	%  fd_compute_lub_general/2,
	  fd_exit_to_prime/7,
	  fd_extend/4,        
	  fd_identical_abstract/2, 
	  fd_input_user_interface/3,  
	  fd_input_interface/4,  
	  fd_less_or_equal/2,
	  fd_asub_to_native/5,
	  fd_project/3,       
	  fd_sort/2,          
	  fd_success_builtin/5,
	  fd_unknown_call/3,
	  fd_unknown_entry/2,
	  fd_empty_entry/2
	],
	[ ] ).

:- use_module(domain(def)).
:- use_module(domain(fr_sets)).
:- use_module(domain(fr_shared)).

:- use_module(library(lists), [member/2]).
:- use_module(library(sets), [insert/3, merge/3, ord_subtract/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- include(domain(fd_top)).
:- include(domain(fd_aux)).

% This file contains the domain dependent abstract functions for the
% combination of the freeness analyser developed at KUL and the
% definiteness analyser developed by Madrid
%
% Comments are not included since the purpose of each function
% has been already commented in the domain_dependent.file

%%% VD adjusted 31/05/94
% fd_decide_continue_entry : D added as third arg
% (also vero_call_to_entry : G added)
% fd_decide_continue_exit  : D_exit added
% (also vero_exit_to_prime : G_exit added)

% added fd_unknown_entry/2, fd_less_or_equal/2  16/01/95
% added fd_reverse/2                            16/01/95
% corrected fd_decide_continue_exit             16/01/95

%------------------------------------------------------------------------------

fd_call_to_entry(Sg,Hv,Head,(F,D),Entry,ExtraInfo):-
        def_call_to_entry(Sg,Hv,Head,D,D_entry,ExtraInfo),
        fd_decide_continue_entry(D_entry,F,D,Sg,Hv,Head,F_entry),
        fd_decide_bottom(F_entry,D_entry,Entry).

fd_decide_continue_entry('$bottom',_F,_D,_Sg,_Hv,_Head,'$bottom').
fd_decide_continue_entry(a(G_entry,_R),F,a(G,_),Sg,Hv,Head,F_entry):-
        vero_call_to_entry(Sg,Hv,Head,G,F,G_entry,F_entry).

fd_decide_bottom('$bottom',_D_entry,'$bottom'):- !.
fd_decide_bottom(F_entry,D_entry,(F_entry,D_entry)).

%------------------------------------------------------------------------------

fd_exit_to_prime('$bottom',_Sg,_Hv,_Head,_Sv,_ExtraInfo,'$bottom').
fd_exit_to_prime((F_exit,D_exit),Sg,Hv,Head,Sv,ExtraInfo,Prime):-
        def_exit_to_prime(D_exit,ExtraInfo,Hv,Sv,Head,Sg,D_prime),
        fd_decide_continue_exit(D_prime,D_exit,F_exit,Sg,Hv,Head,Sv,F_prime),
        fd_decide_bottom(F_prime,D_prime,Prime).

fd_decide_continue_exit('$bottom',_D_exit,_F_exit,_Sg,_Hv,_Head,_Sv,'$bottom').
fd_decide_continue_exit(a(G_prime,_R),a(G_exit,_),F_exit,Sg,Hv,Head,Sv,F_prime):-
        vero_exit_to_prime(F_exit,G_exit,Sg,Hv,Head,Sv,G_prime,F_prime).

%------------------------------------------------------------------------------

fd_project('$bottom',_,'$bottom'):- !.
fd_project((F_call,D_call),Vars,(F_proj,D_proj)):-
        def_project(D_call,Vars,D_proj),
        vero_project(F_call,Vars,F_proj).

%------------------------------------------------------------------------------

fd_compute_lub(ListASub,LubASub):-
        fd_split_information(ListASub,F,D),
        fd_decide_bottom_lub(F,D,LubASub).

fd_decide_bottom_lub([],[],'$bottom'):- !.
fd_decide_bottom_lub(F,D,(F_lub,D_lub)):-
        def_compute_lub(D,D_lub),
        D_lub = a(G_lub,_),
        vero_compute_lub(F,G_lub,F_lub).

%% fd_compute_lub_general(ListASub,LubASub):-
%%         fd_split_information(ListASub,F,D),
%%         fd_decide_bottom_general(F,D,LubASub).
%% 
%% fd_decide_bottom_general([],[],'$bottom'):- !.
%% fd_decide_bottom_general(F,D,(F_lub,D_lub)):-
%%         def_compute_lub(D,D_lub),
%%         D_lub = a(G_lub,_),
%%         vero_compute_lub_general(F,G_lub,F_lub).

fd_split_information([],[],[]).
fd_split_information(['$bottom'|ListASub],F,D):- !,
        fd_split_information(ListASub,F,D).
fd_split_information([H|ListASub],[F|RestF],[D|RestD]):-
        H = (F,D),
        fd_split_information(ListASub,RestF,RestD).

%------------------------------------------------------------------------------

fd_identical_abstract('$bottom', '$bottom'):- !.
fd_identical_abstract((F1,D1),(F2,D2)):-
        D1 == D2,
        vero_identical_abstract(F1,F2).

%------------------------------------------------------------------------------

fd_sort('$bottom','$bottom').
fd_sort((F,D),(F_s,D_s)):-
        def_sort(D,D_s),
        vero_sort(F,F_s).

%------------------------------------------------------------------------------

fd_extend('$bottom',_,_Call,'$bottom').
fd_extend((F_prime,D_prime),Sv,(F_call,D_call),Succ):-
        def_extend(D_prime,D_call,D_succ),
        fd_decide_continue_extend(D_succ,F_prime,F_call,Sv,F_succ),
        fd_decide_bottom(F_succ,D_succ,Succ).

fd_decide_continue_extend('$bottom',_F_prime,_F_call,_Sv,'$bottom'):- !.
fd_decide_continue_extend(a(G_succ,_R),F_prime,F_call,Sv,F_succ):-
        vero_extend(F_prime,G_succ,Sv,F_call,F_succ).

%------------------------------------------------------------------------------

fd_call_to_success_fact('$bottom',_Sg,_Hv,_Head,_Sv,_Call,'$bottom','$bottom').
fd_call_to_success_fact((F_proj,D_proj),Sg,Hv,Head,Sv,(F_call,D_call),
                                                               Prime,Succ):-
        def_call_to_success_fact(D_proj,Hv,Head,Sv,Sg,D_call,D_prime,D_succ),
        fd_decide_continue_fact(D_succ,F_call,F_proj,D_proj,Hv,Head,Sv,Sg,
                                                             F_prime,F_succ),
        fd_decide_bottom(F_prime,D_prime,Prime),
        fd_decide_bottom(F_succ,D_succ,Succ).

fd_decide_continue_fact('$bottom',_F_call,_F_proj,_D_proj,
                                     _Hv,_Head,_Sv,_Sg,'$bottom','$bottom').
fd_decide_continue_fact(a(G_succ,_),F_call,F_proj,a(G_proj,_),
                                      Hv,Head,Sv,Sg,F_prime,F_succ):-
        vero_call_to_success_fact(F_proj,G_proj,G_succ,Hv,Head,Sv,Sg,
                                                F_call,F_prime,F_succ).

%------------------------------------------------------------------------------

fd_success_builtin((F_type,D_type),Sv_u,(InfoF,InfoD),(F_call,D_call),Succ):-
        def_success_builtin(D_type,InfoD,D_call,D_succ),
        fd_decide_builtin(D_succ,F_type,Sv_u,InfoF,F_call,F_succ),
        fd_decide_bottom(F_succ,D_succ,Succ).

fd_decide_builtin('$bottom',_Type,_Sv_u,_InfoF,_F_call,'$bottom').
fd_decide_builtin(a(G_succ,_),Type,Sv_u,InfoF,F_call,F_succ):-
        vero_success_builtin(Type,Sv_u,InfoF,F_call,G_succ,F_succ).

%------------------------------------------------------------------------------

fd_input_user_interface((InfoF,InfoD),Vars,(F,D)):-
        def_input_user_interface(InfoD,D),
        vero_input_user_interface(InfoF,Vars,F).

fd_input_interface(Prop,Kind,(F0,D0),(F,D)):-
        def_input_interface(Prop,Kind0,D0,D),
        paco_input_interface(Prop,Kind1,F0,F),
	compose_kind(Kind0,Kind1,Kind).

compose_kind(approx,approx,approx):- !.
compose_kind(_Kind0,_Kind1,perfect).

%------------------------------------------------------------------------------

%fail: fd_asub_to_native('$bottom',_,_,'$bottom',[]).
fd_asub_to_native((F,D),Qv,OutFlag,Succ,Comps):-
	def_asub_to_native(D,Qv,OutFlag,Succ1,Comps1),
	( member(ground(Gv),Succ1) -> true ; Gv=[] ),
        sort(Qv,Qv_s),
        ord_subtract(Qv_s,Gv,Rest),
        F = as(_Do,Po,_Dn,Pn),
        get_free_vars(Rest,Po,Pn,Fv),
        vero_output_interface(F,[Dep]),
        arg(1,Dep,Free_dep),
	if_not_nil(Fv,free(Fv),Succ,Succ0),
	if_not_nil(Free_dep,posdeps(Free_dep),Succ0,Succ1),
	Comps = Comps1.

if_not_nil([],_,Xs,Xs):- !.
if_not_nil(_,X,[X|Xs],Xs).

%------------------------------------------------------------------------------

fd_unknown_call((CallF,CallD),Vars,(F,D)):-
        def_unknown_call(CallD,Vars,D),
        vero_unknown_call(CallF,Vars,F).

%------------------------------------------------------------------------------

fd_unknown_entry(Vars,(F,D)):-
        def_unknown_entry(Vars,D),
        vero_unknown_entry(Vars,F).

fd_empty_entry(_, _):-
	throw(not_implemented(fd_empty_entry)).

%------------------------------------------------------------------------------

fd_less_or_equal((F1,D1),(F2,D2)):-
        def_less_or_equal(D1,D2),
        vero_less_or_equal(F1,F2).

%------------------------------------------------------------------------------

get_free_vars([],_,_,[]).
get_free_vars([X|Xs],Po,Pn,Fv) :-
        ss_is_in([X],Po),!,
        get_free_vars(Xs,Po,Pn,Fv).
get_free_vars([X|Xs],Po,Pn,Fv) :-
        ss_is_in([X],Pn),!,
        get_free_vars(Xs,Po,Pn,Fv).
get_free_vars([X|Xs],Po,Pn,[X|Rest]) :-
        get_free_vars(Xs,Po,Pn,Rest).

%------------------------------------------------------------------------------

% fd_reverse((F,D),(Frev,D)):-
%         vero_reverse(F,Frev).
