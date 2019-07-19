:- module(dumper,
	[ acc_auxiliary_info/2,
	  dump_auxiliary_info/1,
	  imp_auxiliary_info/4,
	  restore_auxiliary_info/2
	],
	[assertions, hiord, datafacts]).

:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).
:- use_module(ciaopp(plai/domains), [collect_types_in_abs/4, rename_types_in_abs/4]).
:- use_module(typeslib(typeslib), 
	[get_necessary_rules/2,insert_renamed_type_defs/2,new_type_symbol/1,
	 is_param_type_symbol/1, new_param_type_symbol/1,internally_defined_type_symbol/2,
	 param_type_symbol_renaming/2,compute_transitive_closure/3,
	 assert_just_param_renaming/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(p_unit/itf_db), [current_itf/3]).
:- use_module(ciaopp(p_unit/aux_filenames), [is_library/1]).

:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(assoc), [ord_list_to_assoc/2]).
:- use_module(library(lists), [append/3]).

:- doc(module,"This library helps in managing auxiliary info that has
	to be saved together with plai's analysis info when this one is
	stored in separate buffers, e.g., copied in a separate table,
	saved to a file, etc. The process of saving the info is called
	a dump, the process of recovering the info is called a restore.").

:- data all_the_types/1. % accumulates required types
:- data all_the_type_renamings/4.
			 % accumulates necessary dictionaries

retract_if_still(_,X,_):- retract_fact(X), !.
retract_if_still(X,_,X).

:- doc(acc_auxiliary_info(AbsInt,ASubs),"Accumulates auxiliary info
	from the list of abstract substitutions @var{ASubs} of domain
	@var{AbsInt}. It is expected that you issue a call to this one
	for every item you dump.").

acc_auxiliary_info(AbsInt,ASubs):-
	knows_of(regtypes,AbsInt), !,
	retract_if_still([],all_the_types(AbsTypes0),AbsTypes0),
	collect_all_types_in_abs(ASubs,AbsInt,AbsTypes0,AbsTypes),
	asserta_fact(all_the_types(AbsTypes)).
acc_auxiliary_info(_AbsInt,_ASubs).


collect_all_types_in_abs([ASub|More],AbsInt,AbsTypes0,AbsTypes):-
	collect_types_in_abs(ASub,AbsInt,AbsTypes0,AbsTypes1),
	( current_pp_flag(types, deftypes) ->
	  compute_transitive_closure(AbsTypes1,[],AbsTypes15),
	  filter_out_lib_types(AbsTypes15,AbsTypes2)	  
	; AbsTypes1 = AbsTypes2
	),
	collect_all_types_in_abs(More,AbsInt,AbsTypes2,AbsTypes).
collect_all_types_in_abs([],_AbsInt,AbsTypes,AbsTypes).

filter_out_lib_types([],[]).
filter_out_lib_types([T|Ts],FTs) :-
	( accept_type(T) ->
	  FTs = [T|FTs0]	  
	; FTs = FTs0
	),
	filter_out_lib_types(Ts,FTs0).

accept_type(T) :-
	is_param_type_symbol(T).
accept_type(T) :-
	internally_defined_type_symbol(T,_),!.
accept_type(T) :-
	user_defined_type(T).

user_defined_type(T) :-
	module_split(T,M,_),
	\+ ( current_itf(defines_module,M,Base), is_library(Base) ).


:- doc(dump_auxiliary_info(Goal),"Dumps auxiliary info collected
	previously. The dumping is performed by calling @var{Goal}(Info)
	on every Info item collected. It is expected that you issue a call
	to this one after you have finished processing your own items you
	are going to dump. It can be either before or after actually dumping
	them.").
:- meta_predicate dump_auxiliary_info(pred(1)).

dump_auxiliary_info(Goal):-
	retract_if_still([],all_the_types(AbsTypes),AbsTypes),
	get_necessary_rules(AbsTypes,UsedRules0),
	( current_pp_flag(types, deftypes) ->
	  filter_out_rules(UsedRules0,UsedRules1),
	  get_necessary_param_renamings(AbsTypes,UsedRules1,UsedRules)
	; UsedRules = UsedRules0
	),
	asserta_all(UsedRules,Goal), !. 
dump_auxiliary_info(_Goal).

filter_out_rules([],[]).
filter_out_rules([typedef(T,Def)|Rules],FRules) :-
	( accept_type(T) ->
	  FRules = [typedef(T,Def)|FRules1]
	; FRules = FRules1
	),
	filter_out_rules(Rules,FRules1).

get_necessary_param_renamings([],R,R).
get_necessary_param_renamings([T|Ts],Rens0,Rens) :-
	( param_type_symbol_renaming(Ren,T) ->
	  Rens1 = [param_type_symbol_renaming(Ren,T)|Rens0]
	; Rens1 = Rens0
	),
	get_necessary_param_renamings(Ts,Rens1,Rens).

%% get_necessary_rules_non_param(Types,Rules) :-
%% 	remove_param_types(Types,NParamTypes),
%% 	get_necessary_rules(NParamTypes,Rules).
%% 
%% remove_param_types([],[]).
%% remove_param_types([T|Ts],NParam) :-
%% 	( param_type_symbol_renaming(_,T) ->
%% 	  NParam = NParam1
%% 	; NParam = [T|NParam1]
%% 	),
%% 	remove_param_types(Ts,NParam1).

asserta_all([],_Goal).
asserta_all([X|Xs],Goal):-
	Goal(X),
	asserta_all(Xs,Goal).

:- doc(restore_auxiliary_info(Goal,Dict),"Restores the auxiliary
	info dumped with dump_auxiliary_info. The dumped info is obtained
	calling @var{Goal}(Info). Some data necessary for processing your
	own items upon restoring them is collected and output in @var{Dict}.
        Thus, it is expected that you issue a call to this one before you
	actually restore your own items, since they will need to be
	processed with @var{Dict} by imp_auxiliary_info. However, you have
	to guarantee that the single call @var{Goal}(Info) issued here will
        actually succeed in obtain all the dumped auxiliary items on
        backtracking (and fail afterwards).").
:- meta_predicate restore_auxiliary_info(pred(1),?).

restore_auxiliary_info(Goal,_Dict):-
	Goal(typedef(Type,Def)),
        % if there are none, should have failed at this point
	retract_if_still(([],[],[],[]),
	        all_the_type_renamings(LRens0,TyDefs0,ParRens0,Names0),
	                 (LRens0,TyDefs0,ParRens0,Names0)),
	smart_new_type_symbol(Type,Goal,TypeRen,ParRen),
	LRens = [Type-TypeRen|LRens0],
	TyDefs = [TypeRen-Def|TyDefs0],
	ParRens = [TypeRen-ParRen|ParRens0],
	asserta_fact(all_the_type_renamings(LRens,TyDefs,ParRens,Names0)),
	fail.
restore_auxiliary_info(_Goal,Dict):-
	retract_if_still(([],[],[],[]),
	        all_the_type_renamings(LRens0,TyDefs,ParRens,Names),
	                 (LRens0,TyDefs,ParRens,Names)),
	!,
	Dict = (Rens,Names),
	sort(LRens0,LRens),
	ord_list_to_assoc(LRens,Rens),
	insert_renamed_type_defs(TyDefs,Rens),
	all_assert_param_renamings(ParRens).
restore_auxiliary_info(_Goal,_Dict).

all_assert_param_renamings([]).
all_assert_param_renamings([T-Def|Rens]) :-
	( Def \= nopar -> 
	  assert_just_param_renaming(Def,T)
	; true
	),
	all_assert_param_renamings(Rens).

smart_new_type_symbol(Type,Goal,RenType,Def) :-
	is_param_type_symbol(Type),
	Goal(param_type_symbol_renaming(Def,Type)),!,
	(  param_type_symbol_renaming(Def,RenType) ->
	   true
	;  new_param_type_symbol(RenType)
	).
smart_new_type_symbol(Type,_Goal,RenType,nopar) :-
	is_param_type_symbol(Type),!,
	new_param_type_symbol(RenType).
%	display(smart_new_type_symbol_FAIL(Type)),nl.
smart_new_type_symbol(Type,_,RenType,nopar) :-
	internally_defined_type_symbol(Type,_),!,
	new_type_symbol(RenType).
smart_new_type_symbol(Type,_,Type,nopar).

:- doc(imp_auxiliary_info(AbsInt,Dict,ASubs,NewASubs),"Processes the 
	list of abstract substitutions @var{ASubs} of domain @var{AbsInt}
	through the auxiliary info structure @var{Dict}, obtaining the list
	@var{NewASubs} in the same order. The latter should replace the
	former in your items being restored. Thus, you have to issue a call
	to this one for every item you restore and before actually restoring
	it.").

imp_auxiliary_info(AbsInt,Dict,ASubs,NewASubs):-
	rename_all_types_in_abs(ASubs,AbsInt,Dict,NewASubs).

rename_all_types_in_abs([ASub0|More0],AbsInt,Dict,[ASub|More]):-
	rename_types_in_abs(ASub0,AbsInt,Dict,ASub),
	rename_all_types_in_abs(More0,AbsInt,Dict,More).
rename_all_types_in_abs([],_AbsInt,_Dict,[]).

%% % Sample Use Code:
%% 
%% :- module(dump_example,[dump/1,restore/1]).
%% 
%% :- use_module(ciaopp(plai/plai_db), [complete/7]).
%% :- use_module(typeslib(dumper)).
%% 
%% :- data my_complete/7.  % stores copies of complete/7
%% :- data aux/1.          % stores required type definitions
%% 
%% dump(AbsInt):-
%% 	current_fact(complete(SgKey,AbsInt,Sg,Proj,Primes,Id,Parents)),
%% 	asserta_fact(my_complete(SgKey,AbsInt,Sg,Proj,Primes,Id,Parents)),
%% 	acc_auxiliary_info(AbsInt,[Proj|Primes]),
%% 	fail.
%% dump(AbsInt):-
%% 	dump_auxiliary_info(AbsInt,asserta_if_not_yet).
%% 
%% asserta_if_not_yet(X):- current_fact(aux(X)), !.
%% asserta_if_not_yet(X):- asserta_fact(aux(X)).
%% 
%% restore_aux(X):- retract_fact(aux(X)).
%% 
%% restore(AbsInt):-
%% 	restore_auxiliary_info(restore_aux,Dict),
%% 	retract_fact(my_complete(SgKey,AbsInt,Sg,Proj0,Primes0,Id,Parents)),
%% 	imp_auxiliary_info(AbsInt,Dict,[Proj0|Primes0],[Proj|Primes]),
%% 	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Primes,Id,Parents)),
%% 	fail.
%% restore(_AbsInt).
%% 

