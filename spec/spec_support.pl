:- module(spec_support,
	[simplify_indep/4,
	 simplify_ground/4,
	 special_simp_indep/4,
	 special_simp_ground/4,
	 no_repetitions/5,
	 group_predicate/8,
	 record_latest_replacement/3,
	 change_call/3,
	 do_spec/0,
	 set_spec_flag/1,
	 get_last/2,
	 get_simplif/2,
	 add_simplif/3,
	 replace/3,
         simp/2,
	 prepare_ai_info/2,
	 non_static/1
	],
	[assertions, nortchecks, datafacts]).

:- use_module(spec(abs_exec_cond), 
	[
	    indep/4,
	    not_independent/4,
	    ground/3,
	    not_ground/3
	]).
:- use_module(library(sort)).
:- use_module(library(aggregates),      [findall/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(plai/plai_db),            [complete/7]).
:- use_module(ciaopp(plai/fixpo_ops),          [remove_useless_info/1]).
:- use_module(ciaopp(plai/domains),            [abs_sort/3]).
:- use_module(ciaopp(plai/plai_db),            [memo_table/6]).
:- use_module(library(terms),           [copy_args/3]).
:- use_module(ciaopp(p_unit),          [type_of_goal/2]).
:- use_module(ciaopp(pool),             [there_is_delay/0]).
:- use_module(ciaopp(plai/plai_errors),        [compiler_error/1]).

special_ground_acc([],_,_,_).
special_ground_acc([(N,Info)|MoreAcc],K,L,Abs):-
	simplify_ground(L,Abs,Info,NL),
	!,
	(NL \== L ->
	    add_simplif(N,K,ground(L,NL))
	;
	true),
	special_ground_acc(MoreAcc,K,L,Abs).
special_ground_acc([(N,_)|MoreAcc],K,L,Abs):-
	add_simplif(N,K,fail),
	special_ground_acc(MoreAcc,K,L,Abs).

%-------------------------------------------------------------------%
% simplify_indep(+,+,+,_)                                           %
% simplify_indep(List,Abs,Info,NewList)                             %
%  NewList is the simplified list of couples obtained from List     %
% using Info. It fails if any of the couples is not independent.    %
%-------------------------------------------------------------------%
simplify_indep([],_,_,[]).
simplify_indep([[X,Y]|_],Abs,Info,_):-
	not_independent(Abs,X,Y,Info),
	!,
	fail.
simplify_indep([[X,Y]|L],Abs,Info,NewL):-
	indep(Abs,X,Y,Info),
	!,
	simplify_indep(L,Abs,Info,NewL).
simplify_indep([[X,Y]|L],Abs,Info,[[X,Y]|NewL]):-
	simplify_indep(L,Abs,Info,NewL).
%-------------------------------------------------------------------
simplify_ground([],_,_,[]).
simplify_ground([X|L],Abs,Info,NewL):-
	ground(Abs,X,Info),
	!,
	simplify_ground(L,Abs,Info,NewL).
simplify_ground([X|_],Abs,Info,_):-
	not_ground(Abs,X,Info),
	!,
	fail.
simplify_ground([X|L],Abs,Info,[X|NewL]):-
	simplify_ground(L,Abs,Info,NewL).

%-------------------------------------------------------------------%
% special_simp_indep(+,+,+,-)                                       %
% special_simp_indep(K,Vars,Abs,NewL)                              %
%  Here we find all the memo_table entries for this program point   %
% and the call special_indep_acc that tries particular simplifica-  %
% tions in each of the special versions                             %
%-------------------------------------------------------------------%
special_simp_indep(K,Vars,Abs,NewL):-
	current_fact(do_spec),!,
	findall((Num,Vars,S),
	        (current_fact(memo_table(K,Abs,Num,no,Vars,[S]))),AccessList),
	no_repetitions(AccessList,[],Abs,Vars,NewAccessList),
% turbo
 %% 	length(AccessList,L),
 %% 	length(NewAccessList,NL),
 %% 	( L \== NL ->
 %% 	    write(user,'memo_tables_repetidos '),write(user,K),nl(user),
 %% 	    write(AccessList),nl(user),write(user,special_simp_indep),nl(user),
 %% 	    write(NewAccessList),nl(user)
 %% 	;
 %% 	    true),
	special_indep_acc(NewAccessList,K,NewL,Abs).
special_simp_indep(_,_,_,_).
	
special_indep_acc([],_,_,_).
special_indep_acc([(N,Info)|MoreAcc],K,L,Abs):-
	simplify_indep(L,Abs,Info,NL),
	!,
	(NL \== L ->  
	   add_simplif(N,K,indep(L,NL))
	;
	   true),
	special_indep_acc(MoreAcc,K,L,Abs).
special_indep_acc([(N,_)|MoreAcc],K,L,Abs):-
	add_simplif(N,K,fail),
	special_indep_acc(MoreAcc,K,L,Abs).

%------------------------------------------------------------------
special_simp_ground(K,Vars,Abs,NewL):-
	current_fact(do_spec),!,
	findall((Num,Vars,S),
	         (current_fact(memo_table(K,Abs,Num,no,Vars,[S]))),AccessList),
	no_repetitions(AccessList,[],Abs,Vars,NewAccessList),
% turbo
 %% 	length(AccessList,L),
 %% 	length(NewAccessList,NL),
 %% 	( L \== NL ->
 %% 	    write(user,'memo_tables_repetidos '),write(user,K),nl(user),
 %% 	    write(AccessList),nl(user),write(user,simp_ground),nl(user),
 %% 	    write(NewAccessList),nl(user)
 %% 	;
 %% 	    true),
	special_ground_acc(NewAccessList,K,NewL,Abs).
special_simp_ground(_,_,_,_).

%-------------------------------------------------------------------%
% no_repetitions(+,+,+,+,-)                                         %
% no_repetitions(AccessList,Acum,Abs,Vars,InfoList)                 %
%  InfoList is the list of abstract substitutions without repetitions
% obtained from AccessList.                                         %
%  Each abstract substitution must be sorted for Vars               %
%-------------------------------------------------------------------%
no_repetitions([],List,_,_,List).
% turbo
 %% no_repetitions([(C,_,_)|Xs],AcList,Abs,Vars,List):-
 %% 	member((C,_),AcList),!,
 %% 	no_repetitions(Xs,AcList,Abs,Vars,List).
no_repetitions([(Num,Vars,Info)|Xs],AcList,Abs,Vars,Ys):-
	abs_sort(Abs,Info,S_Info),
	no_repetitions(Xs,[(Num,S_Info)|AcList],Abs,Vars,Ys).


%----------------------------------------------------------------------
% We first group all the clauses in a row for the same predicate and
% then generate as many versions as necessary
group_predicate([],[],_,_,[],[],[],[]).
group_predicate([clause(H,B):Clid|Cs],[D|Ds],N,A,Pred,Dict,MoreCs,MoreDs):-
	functor(H,N,A),!,
	Pred = [clause(H,B):Clid|NCs],
	Dict = [D|NDs],
	group_predicate(Cs,Ds,N,A,NCs,NDs,MoreCs,MoreDs).
group_predicate(Cs,Ds,_,_,[],[],Cs,Ds).

:- data replace/3.

%-------------------
record_latest_replacement(GoalKey,Version,Name):-
	current_fact(replace(GoalKey,Version,Name1)),
	Name1 \== Name,!,
	compiler_error(diff_replace_reg),
	asserta_fact(replace(GoalKey,Version,Name)). %only for debugging

record_latest_replacement(GoalKey,Version,Name):-
	asserta_fact(replace(GoalKey,Version,Name)). 

%-------------------------------------------------------------------%
% change_call(+,-,+)                                                %
% change_call(Goal,NewGoal,NewName)                                 %
%  This predicates changes the call to a predicate into the call to %
% the special version with NewName. We must take special care of    %  
% meta_calls                                                        %
%-------------------------------------------------------------------%

change_call(Goal,NewGoal,NewName):-
	functor(Goal,when,2),!,
	functor(NewGoal,when,2),
	arg(1,Goal,Cond),
	arg(1,NewGoal,Cond),
	arg(2,Goal,Call),
	arg(2,NewGoal,NewCall),
	change_call(Call,NewCall,NewName).
change_call(Goal,NewGoal,NewName):-
	type_of_goal(metapred(_,_),Goal),
	!,
%	change_metacall(Goal,NewGoal,NewName).
	functor(Goal,Name,Arity),
	functor(NewGoal,Name,Arity),
	( Arity == 1 ->
	    Arg = 1
	;
	    Arg = 2,
	    arg(1,Goal,Var),
	    arg(1,NewGoal,Var),
	    arg(3,Goal,List),
	    arg(3,NewGoal,List)),
	arg(Arg,Goal,Call),
	arg(Arg,NewGoal,NewCall),
	change_call(Call,NewCall,NewName).

change_call(Goal,NewGoal,NewName):-
	functor(Goal,_,Arity),
	functor(NewGoal,NewName,Arity),
	copy_args(Arity,Goal,NewGoal).

%% change_metacall(Goal,NewGoal,NewName):-
%% 	functor(Goal,call,Arity), !,
%% 	arg(1,Goal,Call),
%% 	( var(Call)
%% 	-> Goal =.. [call,Call|Rest],
%% 	   Galo =.. [call|Rest],
%% 	   Arity1 is Arity-1,
%% 	   functor(NewGoal,NewName,Arity1),
%% 	   copy_args(Arity1,Galo,NewGoal)
%% 	 ; arg(1,NewGoal,NewCall),
%% 	   change_call(Call,NewCall,NewName) ).
%% change_metacall(Goal,NewGoal,NewName):-
%% 	functor(Goal,Name,Arity),
%% 	functor(NewGoal,Name,Arity),
%% 	( Arity == 1 ->
%% 	    Arg = 1
%% 	;
%% 	    Arg = 2,
%% 	    arg(1,Goal,Var),
%% 	    arg(1,NewGoal,Var),
%% 	    arg(3,Goal,List),
%% 	    arg(3,NewGoal,List)),
%% 	arg(Arg,Goal,Call),
%% 	arg(Arg,NewGoal,NewCall),
%% 	change_call(Call,NewCall,NewName).

%-------------------------------------------------------------------%
% We only look for specialization in analysis  versions if          %
% specialization has been requested and it is not a delay analysis  %
%-------------------------------------------------------------------%
:- data do_spec/0.
set_spec_flag(spec):-
	retractall_fact(do_spec),
	\+ there_is_delay,!,
	asserta_fact(do_spec).
set_spec_flag(_).

%-------------------------------------------------------------------%
% get_last(+,-)                                                     %
% get_last(List,Last)                                               %
%  Last is the last element of List before (error:'$bottom')        %
%-------------------------------------------------------------------%
get_last([Last,(error:'$bottom')],Last):-!.
get_last([_|Rest],Last):-
        get_last(Rest,Last).
%-------------------------------------------------------------------% 
% add_simplif(+,+,+)                                                %
% add_simplif(Num,Literal,Sense)                                    %
%-------------------------------------------------------------------%     
:- data simp/2.

add_simplif(Num,Literal,Sense):-
	current_fact(simp(Num,L),Ref),!,
        erase(Ref),
	asserta_fact(simp(Num,[(Literal,Sense)|L])).
add_simplif(Num,Literal,Sense):-
	asserta_fact(simp(Num,[(Literal,Sense)])).
%-------------------------------------------------------------------% 
% get_simplif(+,+)                                                  %
% get_simplif(Num,Simplifications)                                  %
%-------------------------------------------------------------------%     
get_simplif(Num,S):-
	current_fact(simp(Num,S)),!.
get_simplif(_,[]).

:- doc(prepare_ai_info(Keys,Abs), "Removes analysis info and makes
     sure that the results of specialization is the same regardless of
     the fixpoint algorithm used. ").

prepare_ai_info(Keys,Abs):-
	remove_useless_info(Abs),
	(current_pp_flag(reuse_fixp_id,on) ->
	    order_completes_by_ids(Keys,Abs)
	;
	    true).


:- doc(order_completes_by_ids(Keys), "(Re-) asserts the
           completes for each predicate in the order of their Id
           number. The aim is that the program generated is the same
           independently of the fixpoint algorithm which analysis has
           used. This should facilitate comparison of analysis
           results.").

order_completes_by_ids([],_).
order_completes_by_ids([Key|Keys],Abs):-
	findall(Id, current_fact(complete(Key,Abs,_,_,_,Id,_)), Ids_u),
	re_assert(Ids_u,Key,Abs),
	order_completes_by_ids(Keys,Abs).

re_assert([],_Key,_Abs).
re_assert([_],_Key,_Abs):-!.
re_assert(Ids_u,Key,Abs):-
	sort(Ids_u,Ids),
	re_assert_(Ids,Key,Abs).

re_assert_([],_Key,_Abs).
re_assert_([Id|Ids],Key,Abs):-
	current_fact(complete(Key,Abs,C,D,E,Id,G),Ref),
	erase(Ref),
	assertz_fact(complete(Key,Abs,C,D,E,Id,G)),
	re_assert_(Ids,Key,Abs).


% We cannot assume anything on predicates whose code is not statically 
% determinable
non_static(Goal):-
	type_of_goal(dynamic,Goal),!.
non_static(Goal):-
	type_of_goal(multifile,Goal),!.
non_static(Goal):-
	type_of_goal(impl_defined,Goal).

%----------------------------------------------
% This stuff is no longer used
%% count_versions(Keys):-
%% 	count_each_version(Keys,Orig,Vers,Spec,Spureous),
%% 	format(user,"~d&Orig~n~d&Vers~n~d&Spec~n~d&Spureous~n",
%% 	                                   [Orig,Vers,Spec,Spureous]).
%% count_each_version([],0,0,0,0).
%% count_each_version([Key|Keys],Orig,Vers,Spec,Spureous):-
%% 	current_fact(versions(Key,L)),
%% 	count_this_version(L,O,V,S,Spur),
%% 	count_each_version(Keys,Os,Vs,Ss,Spurs),
%% 	Orig is O + Os,
%% 	Vers is V + Vs,
%% 	Spec is S + Ss,
%% 	Spureous is Spur + Spurs.
%% 
%% count_this_version([],0,0,0,0).
%% count_this_version(L,1,V,S,Spur):-
%% 	inspect(L,V,S,Spur,[]).
%% inspect([],0,0,0,_).
%% inspect([(Ver,Simp)|Versions],V,S,Spur,Simps):-
%% 	inspect(Versions,V1,S1,Spur1,[Simp|Simps]),
%% 	length(Ver,V2),
%% 	V is V1 + V2,
%%         S is S1 + 1,
%% 	(member(Simp,Simps)->
%% 	    Spur2 is 1
%% 	;
%% 	    Spur2 is 0),
%% 	Spur is Spur1 + Spur2.
