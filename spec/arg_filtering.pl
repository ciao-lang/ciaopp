:- module(arg_filtering,
	[create_filters/2,
	 create_filters_exported/2,
	 clean_up_filters/0,
	 filter/3,
	 arg_filtering/5,
	 list_exported/3,
	 filter_args/2
	], [assertions, datafacts]).

:- use_module(spec(global_control), 
 	[ 
 	  spec_def_for/8,
 	  spec_wrt/3
 	]).

:- use_module(ciaopp(plai/fixpo_ops), 
 	[ 
 	  collect_exported_completes/2
 	]).

:- use_module(ciaopp(p_unit/itf_db), 
 	[ 
 	  assert_itf/5
 	]).

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(terms),      [copy_args/3]). 
:- use_module(library(terms_vars), [varset/2]). 
:- use_module(library(vndict),     [create_pretty_dict/2]). 
:- use_module(library(lists),      [member/2, length/2]). 
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]). 
:- use_module(library(aggregates), [findall/3]). 


:- data filter/3.


create_filters(Init_sp,AbsInt):-
	current_fact(spec_def_for(_Key,Sg,_Sv,_Proj,AbsInt,Id,NewName,Arity)),
	functor(NSg,NewName,Arity),
	copy_args(Arity,Sg,NSg),
	(member(Id,Init_sp) ->
	    asserta_fact(filter(Id,NSg,Sg)),
	    fail
	;
	    filter_args(NSg,Filter),
	    asserta_fact(filter(Id,NSg,Filter)),
	    functor(Filter,F,A),
	    assert_itf(defined,_M,F,A,_),
	    fail).
create_filters(_Init_sp,_AbsInt).

create_filters_exported([],_AbsInt).
create_filters_exported([Id|Ids],AbsInt):-
	current_fact(spec_def_for(_Key,Sg,_Sv,_Proj,AbsInt,Id,NewName,Arity)),
	functor(NSg,NewName,Arity),
	copy_args(Arity,Sg,NSg),
	asserta_fact(filter(Id,NSg,Sg)),
	create_filters_exported(Ids,AbsInt).

clean_up_filters:-
 	retractall_fact(filter(_,_,_)).
	
filter_args(Goal,FGoal):-
	varset(Goal,Vars),
%	reverse(Vars_r,Vars),
	functor(Goal,F,_A),
	length(Vars,L),
	functor(FGoal,F,L),
	build_fgoal(Vars,1,FGoal).

build_fgoal([],_,_FGoal).
build_fgoal([V|Vars],Pos,FGoal):-
	arg(Pos,FGoal,V),
	Pos1 is Pos + 1,
	build_fgoal(Vars,Pos1,FGoal).


arg_filtering(Cls,_Ds,AbsInt,NCls,NDs):-
	pp_statistics(runtime,_),
	collect_exported_completes(AbsInt,Init),
	list_exported(Init,AbsInt,Init_sp),
	create_filters(Init_sp,AbsInt),
	arg_filt(Cls,NCls,NDs),
	pp_statistics(runtime,[_,T]),
	message(inform, ['{transformed by arg_filtering in ', ~~(T),' msec.}']).


:- pred list_exported(+Init,+AbsInt,-Init_sp) # "@var{Init_sp} is the
	list of implemented versions which are exported by the
	module. This is needed because due to global control, the
	exported specialized definitions may not always coincide with
	the exported completes.".

list_exported(Init,AbsInt,Init_sp):-
	findall(OldId,
	        (member(Id,Init),
		 spec_wrt(Id,AbsInt,OldId)),
		 Init_sp).
	
arg_filt([],[],[]).
arg_filt([Cl|Cls],[NCl|NCls],[ND|NDs]):-
	Cl = clause(Head,Body):Clid,
	(current_fact(filter(_,Head,NHead)) ->
	    true
	;
	    NHead = Head),
	arg_filt_body(Body,NBody),
	NCl = clause(NHead,NBody):Clid,
	create_pretty_dict(NCl,ND),
	arg_filt(Cls,NCls,NDs).

arg_filt_body((L,R),(NL,NR)):-!,
	arg_filt_atom(L,NL),
	arg_filt_body(R,NR).
arg_filt_body(R,NR):-
	arg_filt_atom(R,NR).

arg_filt_atom(L:Key,NL:Key):-
	current_fact(filter(_,L,NL)),!.
arg_filt_atom(Atom,Atom).

