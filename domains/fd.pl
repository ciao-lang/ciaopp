/*             Copyright (C)1990-91-92-93 UPM-CLIP                      */
/*                          1993 Katholieke Universiteit Leuven.        */

:- module(fd,
	[ frdef_call_to_entry/9,
	  frdef_call_to_success_fact/9,
	  frdef_compute_lub/2,   
	  frdef_exit_to_prime/7,
	  frdef_extend/5,        
	  frdef_identical_abstract/2, 
	  frdef_input_user_interface/5,  
	  frdef_input_interface/4,  
	  frdef_less_or_equal/2,
	  frdef_glb/3,
	  frdef_asub_to_native/5,
	  frdef_project/5,
	  frdef_abs_sort/2,          
	  frdef_special_builtin/5,
	  frdef_success_builtin/6,
	  frdef_unknown_call/4,
	  frdef_unknown_entry/3,
	  frdef_empty_entry/3
	],
	[ ] ).

:- use_module(domain(def)).
:- use_module(domain(fr_sets)).
:- use_module(domain(fr_shared)).
:- use_module(domain(fr_top), [fr_special_builtin/5]).

:- use_module(library(lists), [member/2]).
:- use_module(library(sets), [insert/3, merge/3, ord_subtract/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- use_module(domain(share_aux), [if_not_nil/4]).

:- include(domain(fd_top)).
:- include(domain(fd_aux)).

% This file contains the domain dependent abstract functions for the
% combination of the freeness analyser developed at KUL and the
% definiteness analyser developed by Madrid
%
% Comments are not included since the purpose of each function
% has been already commented in the domain_dependent.file

%%% VD adjusted 31/05/94
% frdef_decide_continue_entry : D added as third arg
% (also vero_call_to_entry : G added)
% frdef_decide_continue_exit  : D_exit added
% (also vero_exit_to_prime : G_exit added)

% added frdef_unknown_entry/2, frdef_less_or_equal/2  16/01/95
% added frdef_reverse/2                            16/01/95
% corrected frdef_decide_continue_exit             16/01/95

%------------------------------------------------------------------------------

frdef_call_to_entry(Sv,Sg,Hv,Head,K,Fv,(F,D),Entry,ExtraInfo):-
        def_call_to_entry(Sv,Sg,Hv,Head,Fv,K,D,D_entry,ExtraInfo),
        frdef_decide_continue_entry(D_entry,F,D,Sv,Sg,Hv,Head,K,F_entry),
        frdef_decide_bottom(F_entry,D_entry,Entry).

frdef_decide_continue_entry('$bottom',_F,_D,_Sv,_Sg,_Hv,_Head,_K,'$bottom').
frdef_decide_continue_entry(a(G_entry,_R),F,a(G,_),Sv,Sg,Hv,Head,K,F_entry):-
        vero_call_to_entry(Sv,Sg,Hv,Head,K,G,F,G_entry,F_entry).

frdef_decide_bottom('$bottom',_D_entry,'$bottom'):- !.
frdef_decide_bottom(F_entry,D_entry,(F_entry,D_entry)).

%------------------------------------------------------------------------------

frdef_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,'$bottom') :- !.
frdef_exit_to_prime(Sg,Hv,Head,Sv,(F_exit,D_exit),ExtraInfo,Prime):-
        def_exit_to_prime(Sg,Hv,Head,Sv,D_exit,ExtraInfo,D_prime),
        frdef_decide_continue_exit(D_prime,D_exit,F_exit,Sg,Hv,Head,Sv,F_prime),
        frdef_decide_bottom(F_prime,D_prime,Prime).

frdef_decide_continue_exit('$bottom',_D_exit,_F_exit,_Sg,_Hv,_Head,_Sv,'$bottom').
frdef_decide_continue_exit(a(G_prime,_R),a(G_exit,_),F_exit,Sg,Hv,Head,Sv,F_prime):-
        vero_exit_to_prime(F_exit,G_exit,Sg,Hv,Head,Sv,G_prime,F_prime).

%------------------------------------------------------------------------------

frdef_project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom'):- !.
frdef_project(Sg,Vars,HvFv_u,(F_call,D_call),(F_proj,D_proj)):-
        def_project(Sg,Vars,HvFv_u,D_call,D_proj),
        vero_project(F_call,Vars,F_proj).

%------------------------------------------------------------------------------

frdef_compute_lub(ListASub,LubASub):-
        frdef_split_information(ListASub,F,D),
        frdef_decide_bottom_lub(F,D,LubASub).

frdef_decide_bottom_lub([],[],'$bottom'):- !.
frdef_decide_bottom_lub(F,D,(F_lub,D_lub)):-
        def_compute_lub(D,D_lub),
        D_lub = a(G_lub,_),
        vero_compute_lub(F,G_lub,F_lub).

%% :- export(frdef_compute_lub_general/2).
%% frdef_compute_lub_general(ListASub,LubASub):-
%%         frdef_split_information(ListASub,F,D),
%%         frdef_decide_bottom_general(F,D,LubASub).
%% 
%% frdef_decide_bottom_general([],[],'$bottom'):- !.
%% frdef_decide_bottom_general(F,D,(F_lub,D_lub)):-
%%         def_compute_lub(D,D_lub),
%%         D_lub = a(G_lub,_),
%%         vero_compute_lub_general(F,G_lub,F_lub).

frdef_split_information([],[],[]).
frdef_split_information(['$bottom'|ListASub],F,D):- !,
        frdef_split_information(ListASub,F,D).
frdef_split_information([H|ListASub],[F|RestF],[D|RestD]):-
        H = (F,D),
        frdef_split_information(ListASub,RestF,RestD).

%------------------------------------------------------------------------------

frdef_identical_abstract('$bottom', '$bottom'):- !.
frdef_identical_abstract((F1,D1),(F2,D2)):-
        D1 == D2,
        vero_identical_abstract(F1,F2).

%------------------------------------------------------------------------------

frdef_abs_sort('$bottom','$bottom').
frdef_abs_sort((F,D),(F_s,D_s)):-
        def_abs_sort(D,D_s),
        vero_sort(F,F_s).

%------------------------------------------------------------------------------

frdef_extend(_Sg,'$bottom',_,_Call,'$bottom') :- !.
frdef_extend(Sg,(F_prime,D_prime),Sv,(F_call,D_call),Succ):-
        def_extend(Sg,D_prime,Sv,D_call,D_succ),
        frdef_decide_continue_extend(D_succ,F_prime,F_call,Sv,F_succ),
        frdef_decide_bottom(F_succ,D_succ,Succ).

frdef_decide_continue_extend('$bottom',_F_prime,_F_call,_Sv,'$bottom'):- !.
frdef_decide_continue_extend(a(G_succ,_R),F_prime,F_call,Sv,F_succ):-
        vero_extend(F_prime,G_succ,Sv,F_call,F_succ).

%------------------------------------------------------------------------------

frdef_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,'$bottom','$bottom','$bottom') :- !.
frdef_call_to_success_fact(Sg,Hv,Head,K,Sv,(F_proj,D_proj),(F_call,D_call),Prime,Succ):-
        def_call_to_success_fact(Sg,Hv,Head,K,Sv,D_call,D_proj,D_prime,D_succ),
        frdef_decide_continue_fact(D_succ,F_call,F_proj,D_proj,Hv,Head,K,Sv,Sg,F_prime,F_succ),
        frdef_decide_bottom(F_prime,D_prime,Prime),
        frdef_decide_bottom(F_succ,D_succ,Succ).

frdef_decide_continue_fact('$bottom',_F_call,_F_proj,_D_proj,_Hv,_Head,_K,_Sv,_Sg,'$bottom','$bottom').
frdef_decide_continue_fact(a(G_succ,_),F_call,F_proj,a(G_proj,_),Hv,Head,K,Sv,Sg,F_prime,F_succ):-
        vero_call_to_success_fact(F_proj,G_proj,G_succ,Hv,Head,K,Sv,Sg,F_call,F_prime,F_succ).

%------------------------------------------------------------------------------

frdef_special_builtin(SgKey,Sg,Subgoal,(TypeF,TypeD),(CondF,CondD)) :-
	def_special_builtin(SgKey,Sg,Subgoal,TypeD,CondD),
	fr_special_builtin(SgKey,Sg,Subgoal,TypeF,CondF).
% TODO: body_succ_builtin/9: (old comment) these do not have special(_), so ok: AbsInt \== def, AbsInt \== fr, AbsInt \== frdef

%------------------------------------------------------------------------------

frdef_success_builtin((F_type,D_type),Sv_u,(InfoF,InfoD),HvFv_u,(F_call,D_call),Succ):-
        def_success_builtin(D_type,Sv_u,InfoD,HvFv_u,D_call,D_succ),
        frdef_decide_builtin(D_succ,F_type,Sv_u,InfoF,F_call,F_succ),
        frdef_decide_bottom(F_succ,D_succ,Succ).

frdef_decide_builtin('$bottom',_Type,_Sv_u,_InfoF,_F_call,'$bottom').
frdef_decide_builtin(a(G_succ,_),Type,Sv_u,InfoF,F_call,F_succ):-
        vero_success_builtin(Type,Sv_u,InfoF,F_call,G_succ,F_succ).

%------------------------------------------------------------------------------

frdef_input_user_interface((InfoF,InfoD),Vars,(F,D),Sg,MaybeCallASub):-
        def_input_user_interface(InfoD,Vars,D,Sg,MaybeCallASub),
        vero_input_user_interface(InfoF,Vars,F,Sg,MaybeCallASub).

frdef_input_interface(Prop,Kind,(F0,D0),(F,D)):-
        def_input_interface(Prop,Kind0,D0,D),
        paco_input_interface(Prop,Kind1,F0,F),
	compose_kind(Kind0,Kind1,Kind).

compose_kind(approx,approx,approx):- !.
compose_kind(_Kind0,_Kind1,perfect).

%------------------------------------------------------------------------------

%fail: frdef_asub_to_native('$bottom',_,_,'$bottom',[]).
frdef_asub_to_native((F,D),Qv,OutFlag,Succ,Comps):-
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

%------------------------------------------------------------------------------

frdef_unknown_call(Sg,Vars,(CallF,CallD),(F,D)):-
        def_unknown_call(Sg,Vars,CallD,D),
        vero_unknown_call(Sg,Vars,CallF,F).

%------------------------------------------------------------------------------

frdef_unknown_entry(Sg,Vars,(F,D)):-
        def_unknown_entry(Sg,Vars,D),
        vero_unknown_entry(Sg,Vars,F).

frdef_empty_entry(_,_,_):-
	throw(not_implemented(frdef_empty_entry)).

%------------------------------------------------------------------------------

frdef_less_or_equal((F1,D1),(F2,D2)):-
        def_less_or_equal(D1,D2),
        vero_less_or_equal(F1,F2).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).
frdef_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

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

% frdef_reverse((F,D),(Frev,D)):-
%         vero_reverse(F,Frev).

