/*             Copyright (C)1990-2002 UPM-CLIP				*/
:- module(fixpo_plai,
	[ query/8,
	  init_fixpoint/0,
	  cleanup_fixpoint/1,
	  entry_to_exit/9,
	  % for debugging purposes
	  approx/6,
	  fixpoint/6,
	  '$depend_list'/3	
	],
	[assertions, datafacts]).

:- use_package(.(notrace)). % inhibits the tracing

% Ciao library
:- use_module(library(aggregates), [bagof/3, (^)/2]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(messages)).

% CiaoPP library
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

% Plai library
:- use_module(ciaopp(plai/fixpo_ops), [inexistent/2, variable/2, bottom/1, 
	singleton/2, fixpoint_id_reuse_prev/5, fixpoint_id/1, fixp_id/1,
	each_abs_sort/3,
	% each_concrete/4,
	each_extend/6, each_project/6, each_exit_to_prime/8, each_unknown_call/4,
	each_body_succ_builtin/12, body_succ_meta/7, reduce_equivalent/3,
	each_apply_trusted/7,	widen_succ/4,	decide_memo/6,clause_applies/2,
	abs_subset_/3, fixpoint_get_new_id/5]).

:- use_module(ciaopp(plai/domains)).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7, cleanup/0]).
:- use_module(ciaopp(plai/plai_db), 
	[ complete/7, memo_call/5, memo_table/6, cleanup_plai_db/1, patch_parents/6 ]).
:- use_module(ciaopp(plai/psets), [update_if_member_idlist/3]).
:- use_module(ciaopp(plai/re_analysis), [erase_previous_memo_tables_and_parents/4]).
:- use_module(ciaopp(plai/transform), [body_info0/4, trans_clause/3]).
:- use_module(ciaopp(plai/apply_assertions_old),
	[ apply_trusted0/7, 
 	  cleanup_trusts/1 ]).

%% :- use_module(spec(unfold), 
%% 	[ init_unfold/0 ]).

:- doc(author,"Kalyan Muthukumar").
:- doc(author,"Maria Garcia de la Banda").
:- doc(author,"Francisco Bueno").

:- doc(module,"This module implements the top-down fixpoint 
	algorithm of PLAI, both in its mono-variant and multi-variant
	on successes versions. It is always multi-variant on calls.
        The algorithm is parametric on the particular analysis domain.").

:- doc(stability, alpha).

:- doc(bug,"1. Check analysis of meta_calls works after introducing
        fixpoint_reuse_prev_id/5. See, e.g., mmatrix_parallelized.").
:- doc(bug,"2. Add support for mono-variance on calls, in two
	fashions: (1) one call-pattern per predicate, (2) one 
	call-pattern per predicate atom in the program.").
:- doc(bug,"3. Check support for analyzing meta-calls: it does not work
	in success multivariance, and also the constants should be 
	module-expanded. Also, what about [Body|...] in a meta-call?"). 
:- doc(bug,"4. Check analysis of bagof(X,Y^T,Z)").
:- doc(bug,"5. Add support for approximating non-native properties in 
	trusts.").
:- doc(bug,"6. Should we assert complete for meta-calls?").
:- doc(bug,"7. Revise treatment of builtins. Specially when not
	supported by the domain.").
:- doc(bug,"8. Revise all the treatment of bottom. Should probably stop
	inmmediately.").
:- doc(bug,"9. Check the processing for success multivariance.").
:- doc(bug,"10. $meta has extra variables because of the meta-terms. 
        This is confusing (specially on output, maybe also for analysis
        -- see body_succ0). Should not be there, and only added to
	analyze the meta-term.").

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 1/12/90                              %
%                       programmer: Kalyan Muthukumar,                   %
%                          completed: 15/10/92                           %
%              programmers:    M. Garcia de la Banda, F. Bueno           %
%                                                                        %
%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
%  AbsInt  : identifier of the abstract interpreter being used           %
%  Sg      : Subgoal being analysed                                      %
%  SgKey   : Subgoal key (represented by functor/arity)                  %
%  Head    : Head of one of the clauses which define the Sg predicate    %
%  Sv      : Subgoal variables                                           %
%  Hv      : Head variables                                              %
%  Fv      : Free variables in the body of the clause being considered   %
%  HvFv    : Clause variables (Hv + Fv)                                  %
%  Qv      : Q variables                                                 %
%  Vars    : Any possible set of variables                               %
%  Call    : Abstract call substitution                                  %
%  Proj    : Call projected onto Sv                                      %
%  Entry   : Abstract entry substitution (i.e. the abstract subtitution  %
%            obtained after the abstract unification of Sg and Head      %
%            projected onto HvFv)                                        %
%  Exit    : Abstract exit substitution (i.e. the abstract subtitution   %
%            obtained after the analysis of the clause being considered  %
%            projected onto Hv)                                          %
%  Prime   : Abstract prime substitution (i.e. the abstract subtitution  %
%            obtained after the analysis of the clause being considered  %
%            projected onto Sv)                                          %
%  Succ    : Abstract success substitution (i.e. the abstract subtitution%
%            obtained after the analysis of the clause being considered  %
%            extended to the variables of the clause in which Sg appears)%
%  RFlag   : Flag which represents the recursive characteristics of a    %
%            predicate. It will be "nr" in case the predicate be non     % 
%            recursive. Otherwise it will be r (recursive)               %
% List     : (can be represented as OldList,List,AddList,IdList,NewList) %
%            the current list of nodes which a given node depends on.    %
% _s       : The suffix _s means that the term to which the variable is  %
%            bound to has been sorted. By default they are always sorted %
%            thus _s is added only when it appears neccessary to say it  %
%            explicitely                                                 %
% _u       : The suffix _u means that the term to which the variable is  %
%            bound is not sorted                                         %
% ExtraInfo: Info computed during the call_to_entry that can be reused   %
%            during the exit_to_prime step                               %
%   F      : Literal that originated the call (Father)                   %
%   N      : Number of specialized version of the father predicate       %
%  NewN    : Number of specialized version of this predicate             %
%   Id     : Id of the and-or graph node in analysis                     %
%------------------------------------------------------------------------%

:- data '$depend_list'/3.
:- data ch_id/2.

:- data approx/6.
:- data fixpoint/6.
:- data fixpoint_variant/6.
:- data approx_variant/7.

:- doc(init_fixpoint/0,"Cleanups the database of analysis of
	temporary information.").

init_fixpoint:-
	retractall_fact(approx(_,_,_,_,_,_)),
	retractall_fact(fixpoint(_,_,_,_,_,_)),
	retractall_fact('$depend_list'(_,_,_)),
	retractall_fact(ch_id(_,_)),
	retractall_fact(fixpoint_variant(_,_,_,_,_,_)),
	retractall_fact(approx_variant(_,_,_,_,_,_,_)),
	trace_fixp:cleanup.
%	init_unfold.

:- doc(cleanup_fixpoint(AbsInt),"Cleanups the database of analysis, of both
	temporary as well as permanent information regarding abstract
	domain @var{AbsInt}.").

cleanup_fixpoint(AbsInt):-
	cleanup_plai_db(AbsInt),
	cleanup_trusts(AbsInt),
	retractall_fact(fixp_id(_)),
	asserta_fact(fixp_id(0)), % there is no way to recover this 
	init_fixpoint.            % if several analysis coexist!

approx_to_completes(AbsInt):-
	current_fact(approx(SgKey,Sg,Proj,Prime,Pid,Fs),Ref),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Pid,Fs)),
	erase(Ref),
	fail.
approx_to_completes(AbsInt):-
	current_fact(approx_variant(_Id,Pid,SgKey,Sg,Proj,Prime,Fs),Ref),	
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Pid,Fs)),
	erase(Ref),
	fail.
approx_to_completes(_AbsInt).

%------------------------------------------------------------------------%
% call_to_success(+,+,+,+,+,+,+,-,-,+,+,+)                               %
% call_to_success(RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,List,F,N,NewN) %
% It obtains the Succ for a given Sg and Call, and the List.             %
%  * If complete information for the same Sg and Call (i.e. for the same %
%    node) has been already inferred, the first clause will be used.     %
%  * else if Sg is non recursive the second clause will be used          %
%  * else if Sg is already in a fixpoint, (i.e. some parent              %
%    initiated a fixpoint with same Call and Sg) the third clause will   %
%    detect it in order not to start an infinite computation.            %
%  * else if Sg with the same Call has been already analyzed but it      %
%    depends on some other nodes whose fixpoint is not completed, and    %
%    therefore the its information is labeled as "approx" then 4th clause%
%    will be used. This clause distinguishes two cases:                  %
%     - The information on which the predicate depends on has not        %
%       been modified. Then nothing must be done.                        %
%     - The information on which the predicate depends on has been modified
%       Then the label of the register approx(Sg,Proj,Prime,Id) is       %
%       changed to fixpoint(Sg,Proj,Prime,Id) and a new fixpoint         %
%       computation is started. After the computation the register       %
%       fixpoint(Sg,Proj,Prime,Id) is changed to either                  %
%       complete(Sg,Proj,NewPrime,Id) if the list of nodes which the     %
%       predicate depends on is empty, or to                             %
%       approx(Sg,Proj,NewPrime,Id) if it is not                         %
% In order to maintain the dependencies among nodes (i.e. each recursive %
% predicate with each abstract call substitution) during the computations%
% the following things are done:                                         %
%     - any time that the approximate information (TempPrime) of a       %
%       fixpoint node changes, it updates a number in the data base      %
%       increasing in one (for example, if the node was the 3 it reads   %
%       something like ch_id(3,Num), erases it, increases Num in one     %
%       obtaining Num', and records ch_id(3,Num').                       %
%     - any time a node uses the information of another recursive        %
%       node, it reads in the data base the associated number and keeps  %
%       it in the list of nodes (for example, if the node 4 is using     %
%       information of the node 3, it reads ch_id(3,Num), and keeps 3/Num%
%       in the list of nodes).                                           %
% The way to see if the information on which the predicate depends on    %
% has been modified or not is the following:                             %
%     - the approx node depend_list is read (the list of                 %
%       node/num it depends on) and checks if the correspondent          %
%       ch_id(node,num) register exists. If this is the case, the        %
%       information has not changed. Otherwise it has changed.           %
% * Finally, if a fixpoint computation for a Sg has to be started, the   %
%   5th clause will be used. First the non recursive clauses are analyzed%
%   Then the registers fixpoint(Sg,Proj,TempPrime,Id1) and ch_id(Id1,1)  %
%   are recordered. Then fixpoint computation is started. After the      %
%   computation the register fixpoint(Sg,Proj,TempPrime,Id1) is changed  %
%   to either "complete" if the list of nodes to which the predicate     %
%   depends on is empty, or to "approx" if it is not. Also, the register %
%   ch_id(Id1,1) is erased.
%------------------------------------------------------------------------%

call_to_success(_RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id):-
%w	write('c'),
	% ClId = number identifying the clause?... for an entry point is 0...
	% F = program point of the call. clauseId+/0 for an entry call
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),R),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1), !,
	patch_parents(R,complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Ps),F,N,Ps,Fs),
	List = [],
	fixpoint_trace('complete used',N,Id,SgKey,Sg,Prime1,_),
	each_abs_sort(Prime1,AbsInt,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(r,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id) :-
	current_fact(approx(SgKey,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1), !,
	fixpoint_trace('approx used',N,Id,SgKey,Sg,Prime1,_),
	each_abs_sort(Prime1,AbsInt,TempPrime),
	current_fact('$depend_list'(Id,SgKey,IdList)),
	call_to_success_approx(SgKey,Subg,Call,Proj,Proj1,Sg,Sv,AbsInt,F,N,Fs,
	                       Id,Ref,IdList,Prime1,TempPrime,List,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(r,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id):-
	current_fact(fixpoint(SgKey,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1), !,
	patch_parents(Ref,fixpoint(SgKey,Subg,Proj1,Prime1,Id,Ps),F,N,Ps,Fs),
	fixpoint_trace('fixpoint used',N,Id,SgKey,Sg,Prime1,_),
	current_fact(ch_id(Id,Num)),
	List = [Id/Num],
	each_abs_sort(Prime1,AbsInt,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(_RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id):-
%w	write('c'),
	current_pp_flag(variants,on),
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,_Id1,_Fs),_R),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2), !,
  fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	each_abs_sort(Prime2,AbsInt,Prime),
	List = [],
	fixpoint_trace('complete used',N,Id,SgKey,Sg,Prime2,_),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(r,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id) :-
	current_pp_flag(variants,on),
	current_fact(approx(SgKey,Subg,Proj1,Prime1,Id1,Fs),Ref),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2), !,
	fixpoint_trace('approx used',N,Id1,SgKey,Sg,Prime1,_),
	each_abs_sort(Prime2,AbsInt,TempPrime),
	current_fact('$depend_list'(Id1,SgKey,IdList)),
	call_to_success_approx_variant(SgKey,Subg,Call,Proj,Proj1,Sg,Sv,AbsInt,F,N,Fs,
	                       Id,Id1,Ref,IdList,Prime1,TempPrime,List,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(r,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id):-
	current_pp_flag(variants,on),
	current_fact(fixpoint(SgKey,Subg,Proj1,Prime1,Id1,_Fs),_Ref),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2), !,
	(
	    current_fact(fixpoint_variant(Id1,Id,SgKey,Sgv,Projv,Fsv),Refv),
	    identical_proj(AbsInt,Sg,Proj,Sgv,Projv) ->
	    patch_parents(Refv,fixpoint_variant(Id1,Id,SgKey,Sgv,Projv,Ps),F,N,Ps,Fsv)
	;
        fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
        asserta_fact(fixpoint_variant(Id1,Id,SgKey,Sg,Proj,[(F,N)]))
	),
	each_abs_sort(Prime2,AbsInt,Prime),
	fixpoint_trace('fixpoint used',N,Id1,SgKey,Sg,Prime2,_),
	current_fact(ch_id(Id1,Num)),
	List = [Id1/Num],
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(r,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,List,F,N,Id) :-
	init_fixpoint0(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,[(F,N)],Id,List,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(nr,SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,Succ,[],F,N,Id):-
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	fixpoint_trace('non-recursive initiated',Id,N,SgKey,Sg,Proj,_),
	proj_to_prime_nr(SgKey,Sg,Sv,Call,Proj,AbsInt,ClId,Prime,Id), 
	fixpoint_trace('non-recursive completed',Id,N,SgKey,Sg,Prime,_),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).

call_to_success_approx(SgKey,Subg,_Call,Proj,Proj1,Sg,_Sv,_AbsInt,F,N,Fs,
	                     Id,Ref,IdList,Prime1,TempPrime,List,Prime):-
	not_modified(IdList), !,
	fixpoint_trace('approx unchanged',N,Id,SgKey,Sg,Proj,_),
	patch_parents(Ref,approx(SgKey,Subg,Proj1,Prime1,Id,Ps),F,N,Ps,Fs),
	Prime = TempPrime,
	List = IdList.
call_to_success_approx(SgKey,_Subg,Call,Proj,_Proj1,Sg,Sv,AbsInt,F,N,Fs,
	                     Id,Ref,_IdList,_Prime1,TempPrime,List,Prime):-
	erase(Ref),
	init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,
	                     TempPrime,List,Prime).

aproxs_to_fixpoint_variant(Id):-
	current_fact(approx_variant(Id,Idv,SgKey,Sgv,Projv,_Primev,Fs),Ref),!,
	erase(Ref),
	asserta_fact(fixpoint_variant(Id,Idv,SgKey,Sgv,Projv,Fs)),
	aproxs_to_fixpoint_variant(Id).
aproxs_to_fixpoint_variant(_).

call_to_success_approx_variant(SgKey,_Subg,_Call,Proj,_Proj1,Sg,_Sv,AbsInt,F,N,_Fs,
	                     Id,Id1,_Ref,IdList,_Prime1,TempPrime,List,Prime):-
	not_modified(IdList), !,
	(
	    current_fact(approx_variant(Id1,Id,SgKey,Sgv,Projv,Primev,Fsv),Refv),
	    identical_proj(AbsInt,Sg,Proj,Sgv,Projv) ->
	    patch_parents(Refv,approx_variant(Id1,Id,SgKey,Sgv,Projv,Primev,Ps),F,N,Ps,Fsv) 
	;
	    fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	    asserta_fact(approx_variant(Id1,Id,SgKey,Sg,Proj,TempPrime,[(F,N)]))
	),
	fixpoint_trace('approx unchanged',N,Id1,SgKey,Sg,Proj,_),
	Prime = TempPrime,
	List = IdList.
call_to_success_approx_variant(SgKey,Subg,Call,Proj,Proj1,Sg,Sv,AbsInt,F,N,Fs,
	                     Id,Id1,Ref,_IdList,Prime1,_TempPrime,List,Prime):-
	(
	    current_fact(approx_variant(Id1,Id,SgKey,Sgv,Projv,_Primev,Fsv),Refv),
	    identical_proj(AbsInt,Sg,Proj,Sgv,Projv) ->
	    erase(Refv),
	    ( member((F,N),Fsv) -> NewFs = Fsv ; NewFs = [(F,N)|Fsv] )
	;
	    fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	    NewFs = [(F,N)]
	),
        aproxs_to_fixpoint_variant(Id1),
	erase(Ref),
	asserta_fact(fixpoint_variant(Id1,Id,SgKey,Sg,Proj,NewFs)),
	varset(Subg,Subv),
	init_fixpoint_(SgKey,Call,Proj1,Subg,Subv,AbsInt,F,N,Fs,Id1,
	                     Prime1,List,Prime0),
	each_exit_to_prime(Prime0,AbsInt,Sg,Subv,Subg,Sv,(no,Proj),Prime).		% ver


init_fixpoint0(SgKey,Call,Proj0,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime):-
	current_pp_flag(widen,on),
	current_pp_flag(multi_success,off),
	widen_call(AbsInt,SgKey,Sg,F,N,Proj0,Proj), !,
	init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime).
init_fixpoint0(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime):-
	init_fixpoint2(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime).

init_fixpoint1(SgKey,_Call,Proj,Sg,_Sv,AbsInt,F,N,_Fs0,Id,List,Prime):-
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),R),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1), !,
	patch_parents(R,complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Ps),F,N,Ps,Fs),
	List = [],
	fixpoint_trace('complete used',N,Id,SgKey,Sg,Prime1,_),
	each_abs_sort(Prime1,AbsInt,Prime).
init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,_Fs0,Id,List,Prime):-
	current_fact(approx(SgKey,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1), !,
	fixpoint_trace('approx used',N,Id,SgKey,Sg,Prime1,_),
	each_abs_sort(Prime1,AbsInt,TempPrime),
	current_fact('$depend_list'(Id,SgKey,IdList)),
	call_to_success_approx(SgKey,Subg,Call,Proj,Proj1,Sg,Sv,AbsInt,F,N,Fs,
	                       Id,Ref,IdList,Prime1,TempPrime,List,Prime).
init_fixpoint1(SgKey,_,Proj,Sg,_Sv,AbsInt,F,N,_Fs0,Id,List,Prime):-
	current_fact(fixpoint(SgKey,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1), !,
	patch_parents(Ref,fixpoint(SgKey,Subg,Proj1,Prime1,Id,Ps),F,N,Ps,Fs),
	fixpoint_trace('fixpoint used',N,Id,SgKey,Sg,Prime1,_),
	current_fact(ch_id(Id,Num)),
	List = [Id/Num],
	each_abs_sort(Prime1,AbsInt,Prime).
init_fixpoint1(SgKey,_Call,Proj,Sg,_Sv,AbsInt,F,N,_Fs0,Id,List,Prime):-
	current_pp_flag(variants,on),
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,_Id1,_Fs),_R),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2), !,
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
  each_abs_sort(Prime2,AbsInt,Prime),
	List = [],
	fixpoint_trace('complete used',N,Id,SgKey,Sg,Prime2,_),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])).
init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,_Fs0,Id,List,Prime):-
	current_pp_flag(variants,on),
	current_fact(approx(SgKey,Subg,Proj1,Prime1,Id1,Fs),Ref),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2), !,
	fixpoint_trace('approx used',N,Id1,SgKey,Sg,Prime1,_),
	each_abs_sort(Prime2,AbsInt,TempPrime),
	current_fact('$depend_list'(Id1,SgKey,IdList)),
	call_to_success_approx_variant(SgKey,Subg,Call,Proj,Proj1,Sg,Sv,AbsInt,F,N,Fs,
	                       Id,Id1,Ref,IdList,Prime1,TempPrime,List,Prime).
init_fixpoint1(SgKey,_,Proj,Sg,_Sv,AbsInt,F,N,_Fs0,Id,List,Prime):-
	current_pp_flag(variants,on),
	current_fact(fixpoint(SgKey,Subg,Proj1,Prime1,Id1,_Fs),_Ref),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2), !,
	(
	    current_fact(fixpoint_variant(Id1,Id,SgKey,Sgv,Projv,Fsv),Refv),
	    identical_proj(AbsInt,Sg,Proj,Sgv,Projv) ->
	    patch_parents(Refv,fixpoint_variant(Id1,Id,SgKey,Sgv,Projv,Ps),F,N,Ps,Fsv)
	;
	    fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	    asserta_fact(fixpoint_variant(Id1,Id,SgKey,Sg,Proj,[(F,N)]))
	),
	each_abs_sort(Prime2,AbsInt,Prime),
	fixpoint_trace('fixpoint used',N,Id1,SgKey,Sg,Prime2,_),
	current_fact(ch_id(Id1,Num)),
	List = [Id1/Num].
init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime):-
	init_fixpoint2(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime).

init_fixpoint2(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,List,Prime):-
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	asserta_fact(ch_id(Id,1)),
	fixpoint_trace('non-recursive initiated',Id,N,SgKey,Sg,Proj,_),
	proj_to_prime_r(SgKey,Sg,Sv,Call,Proj,AbsInt,TempPrime,Id), 
	fixpoint_trace('non-recursive completed',Id,N,SgKey,Sg,TempPrime,_),
	init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,
	                     TempPrime,List,Prime).

init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Fs,Id,Prime0,List,Prime):-
	normalize_asub0(AbsInt,Prime0,TempPrime),
	asserta_fact(fixpoint(SgKey,Sg,Proj,TempPrime,Id,Fs)),
	bagof(X, X^(trans_clause(SgKey,r,X)),Clauses),!, % TODO: why cut?
	fixpoint_trace('fixpoint initiated',Id,N,SgKey,Sg,Proj,Clauses),
	fixpoint_compute(Clauses,SgKey,Sg,Sv,Call,Proj,
	                    AbsInt,_LEntry,TempPrime,Prime1,Id,TempList),
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime1,Prime), % it was commented
%	Prime1=Prime,
	current_fact(fixpoint(SgKey,Sg,_,_,Id,Fs2),Ref),
	erase(Ref),
	( current_fact('$depend_list'(Id,SgKey,_),RefDep) ->
	  erase(RefDep)
	; true
	),
	update_if_member_idlist(TempList,Id,AddList),
	( member((F,N),Fs2) -> NewFs = Fs2 ; NewFs = [(F,N)|Fs2] ),
	decide_approx(AddList,Id,NewFs,AbsInt,SgKey,Sg,Proj,Prime),
	List = AddList.

widen_call(AbsInt,SgKey,Sg,F1,Id0,Proj1,Proj):-
	( current_pp_flag(widencall,off) -> fail ; true ),
	widen_call0(AbsInt,SgKey,Sg,F1,Id0,[Id0],Proj1,Proj), !,
	fixpoint_trace('result of widening',Id0,F1,SgKey,Sg,Proj,_),
	true.

widen_call0(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	widen_call1(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj), !.
widen_call0(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	current_pp_flag(widencall,com_child),
	widen_call2(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj).

widen_call1(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
        % current_fact(fixpoint(SgKey0,Sg0,Proj0,_Prime0,Id0,Fs0)),
        ( current_fact(fixpoint(SgKey,Sg0,Proj0,_Prime0,Id0,Fs0)) -> SgKey = SgKey0 % fast
        ; current_fact(fixpoint(SgKey0,Sg0,Proj0,_Prime0,Id0,Fs0)) % TODO: slow! fix indexing by Id0
        ),
        %
	( SgKey=SgKey0,
          % same program point:
	  member((F1,_NewId0),Fs0)
	-> Sg0=Sg,
	   abs_sort(AbsInt,Proj0,Proj0_s),
	   abs_sort(AbsInt,Proj1,Proj1_s),
	   widencall(AbsInt,Proj0_s,Proj1_s,Proj)
%	   widencall(AbsInt,Proj1_s,Proj0_s,Proj)
	 ; % continue with the parents:
	   member((_F1,NewId0),Fs0),
	   \+ member(NewId0,Ids),
	   widen_call1(AbsInt,SgKey,Sg,F1,NewId0,[NewId0|Ids],Proj1,Proj)
	).


% widen_call2(AbsInt,SgKey,Sg,F1,Id0,_Ids,Proj1,Proj):-
% 	current_fact(complete(SgKey,AbsInt,Sg0,Proj0,_Prime0,_Id0,Fs0)),
% 	member((F1,Id0),Fs0),
% 	Sg0=Sg,
% 	abs_sort(AbsInt,Proj0,Proj0_s),
% 	abs_sort(AbsInt,Proj1,Proj1_s),
% 	widencall(AbsInt,Proj0_s,Proj1_s,Proj).
% widen_call2(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
% 	current_fact(fixpoint(_SgKey0,_Sg0,_Proj0,_Prime0,Id0,Fs0)),
% 	member((_F1,NewId0),Fs0),
% 	\+ member(NewId0,Ids),
% 	widen_call2(AbsInt,SgKey,Sg,F1,NewId0,[NewId0|Ids],Proj1,Proj).

widen_call2(AbsInt,SgKey,Sg,F1,_Id,_Ids,Proj1,Proj):-
	current_fact(complete(SgKey,AbsInt,Sg0,Proj0,_Prime0,_Id0,Fs0)),
	member((F1,Id0),Fs0),
	Sg0=Sg,
	same_fixpoint_ancestor(Id0,[Id0],AbsInt),
	abs_sort(AbsInt,Proj0,Proj0_s),
	abs_sort(AbsInt,Proj1,Proj1_s),
	widencall(AbsInt,Proj0_s,Proj1_s,Proj).
%	widencall(AbsInt,Proj1_s,Proj0_s,Proj).

same_fixpoint_ancestor(Id0,_Ids,_AbsInt):-
	current_fact(fixpoint(_SgKey0,_Sg0,_Proj0,_Prime0,Id0,_Fs0)), !.
same_fixpoint_ancestor(Id0,_Ids,_AbsInt):-
	current_fact(approx(_SgKey0,_Sg0,_Proj0,_Prime0,Id0,_Fs0)), !.
same_fixpoint_ancestor(Id0,Ids,AbsInt):-
	current_fact(complete(_SgKey0,AbsInt,_Sg0,_Proj0,_Prime0,Id0,Fs0)),
	member((_F1,Id),Fs0),
	\+ member(Id,Ids),
	same_fixpoint_ancestor(Id,[Id|Ids],AbsInt).

%-------------------------------------------------------------------------
% decide_approx(+,+,+,+,+,+,+,+)                                         %
% decide_approx(AddList,Id,Fs,AbsInt,SgKey,Sg,Proj,Prime)                %
% If the first argument is empty it deletes from the data base the       %
% register ch_id corresponding to Id, updates the dependent lists of     %
% those nodes which depends on Id and recorders the information for Id   %
% with the label "complete"                                              %
% Otherwise, it creates the new dependent list for Id and recorders the  %
% information for Id with label "approx"                                 %
%------------------------------------------------------------------------%

fixpoint_variants_update(Id,AbsInt,Sg,Prime):-
	current_fact(fixpoint_variant(Id,Idv,SgKey,Sgv,Projv,Fs),Ref),!,
	erase(Ref),
	varset(Sg,Hv),
	varset(Sgv,Hvv),
	each_exit_to_prime(Prime,AbsInt,Sgv,Hv,Sg,Hvv,(no,Projv),Prime2), % ver
	asserta_fact(complete(SgKey,AbsInt,Sgv,Projv,Prime2,Idv,Fs)),	
	fixpoint_variants_update(Id,AbsInt,Sg,Prime). 
fixpoint_variants_update(_,_,_,_).

approx_variants_update(Id,AbsInt,Sg,Prime):-
	current_fact(fixpoint_variant(Id,Idv,SgKey,Sgv,Projv,Fs),Ref),!,
	erase(Ref),
	varset(Sg,Hv),
	varset(Sgv,Hvv),
	each_exit_to_prime(Prime,AbsInt,Sgv,Hv,Sg,Hvv,(no,Projv),Prime2),  % ver
	asserta_fact(approx_variant(Id,Idv,SgKey,Sgv,Projv,Prime2,Fs)),	
	approx_variants_update(Id,AbsInt,Sg,Prime). 
approx_variants_update(_,_,_,_).
	

decide_approx([],Id,Fs,AbsInt,SgKey,Sg,Proj,Prime):- !,
	current_fact(ch_id(Id,_),Ref3),
	erase(Ref3),
        % Not needed for correctness: only book-keeping
%	update_depend_list_approx(Id,AbsInt),
	fixpoint_trace('fixpoint completed',Id,o,SgKey,Sg,Prime,_),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Fs)),
	(
	    current_pp_flag(variants,on) -> 
	    each_abs_sort(Prime,AbsInt,Prime_s),
	    fixpoint_variants_update(Id,AbsInt,Sg,Prime_s)
	;
	    true
	).
decide_approx(AddList,Id,Fs,_AbsInt,SgKey,Sg,Proj,Prime):-
	asserta_fact('$depend_list'(Id,SgKey,AddList)),
	fixpoint_trace('fixpoint approximated',Id,o,SgKey,Sg,Prime,_),
	asserta_fact(approx(SgKey,Sg,Proj,Prime,Id,Fs),_),
	(
	    current_pp_flag(variants,on) -> 
	    each_abs_sort(Prime,AbsInt,Prime_s),
	    approx_variants_update(Id,AbsInt,Sg,Prime_s)
	;
	    true
	).

%-------------------------------------------------------------------------
% update_depend_list_approx(+,+)
% This predicate is used when a fixpoint computation for a node Id has
% finished yielding "complete", i.e. it does not depend on information on
% any other node. Therefore, if any node depends on the node Id, this
% dependency has to be eliminated; if no other dependency is left, the
% node has to be updated to "complete" instead of "approx". The way this
% is done is by:
%      - collecting the dependence list of each node 
%      - selecting those which after eliminating Id are empty; those
%         which are not selected are just updated in the database
%      - updating the approx register to a complete one, and
%      - recursively calling to update_depend_list/1 for the ones selected
% Note that when
% updating the approx register to a complete one it can happen that
% there is no approx register. The reason is that it can be due to a node
% which is approx but is in the middle of a computation, and therefore
% it appears as a fixpoint register. Therefore it ensures that the 
% recordered lists are those of which are approx nodes.
%-------------------------------------------------------------------------

%% update_depend_list_approx(Id,AbsInt) :-
%% 	collect_depend_lists_approx(List),
%% 	select_depend_lists([Id],List,AbsInt,New_List),
%% 	create_depend_lists(New_List).
%% 
%% collect_depend_lists_approx([l(X,SgKey,List)|Rest]):-
%% 	current_fact('$depend_list'(X,SgKey,List),Ref),
%% 	current_fact(approx(SgKey,_,_,_,X,_),_),!,
%% 	erase(Ref),
%% 	collect_depend_lists_approx(Rest).
%% collect_depend_lists_approx([]).
%% 
%% select_depend_lists([],List,_AbsInt,List).
%% select_depend_lists([Id|Ids],List,AbsInt,More):-
%% 	collect_completes(List,Id,New_List,TempCompletes),
%% 	approx_to_complete(TempCompletes,AbsInt,NewCompletes),
%% 	merge(Ids,NewCompletes,Completes),
%% 	select_depend_lists(Completes,New_List,AbsInt,More).
%% 
%% approx_to_complete([],_AbsInt,[]).
%% approx_to_complete([l(Pid,SgKey)|Completes],AbsInt,[Pid|NewCompletes]):-
%% 	current_fact(approx(SgKey,Sg,Proj,Prime,Pid,Fs),Ref),
%% 	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Pid,Fs)),
%% 	erase(Ref),
%% 	approx_to_complete(Completes,AbsInt,NewCompletes).
%% 
%% collect_completes([],_Id,[],[]).
%% collect_completes([l(X,Key,[Id/_])|Rest],Id,New_list,[l(X,Key)|Comp]):- !,
%% 	collect_completes(Rest,Id,New_list,Comp).
%% collect_completes([l(X,Key,List)|Rest],Id,[l(X,Key,Temp)|New_list],Comp):- 
%% 	select_all(List,Id,Temp), !,
%% 	collect_completes(Rest,Id,New_list,Comp).
%% collect_completes([l(X,Key,List)|Rest],Id,[l(X,Key,List)|New_list],Comp):- 
%% 	collect_completes(Rest,Id,New_list,Comp).
%% 
%% create_depend_lists([]).
%% create_depend_lists([l(X,SgKey,List)|New_List]):-
%% 	asserta_fact('$depend_list'(X,SgKey,List)),
%% 	create_depend_lists(New_List).
%% 
%% select_all([],_,[]).
%% select_all([Head/V|Tail], Element, [Head/V|Rest]) :-
%% 	Head < Element,!,
%% 	select_all(Tail, Element, Rest).
%% select_all([Element/_|Tail], Element, Rest):- !,
%% 	select_all(Tail, Element, Rest).
%% select_all([Head|Tail],_, [Head|Tail]).

%-------------------------------------------------------------------------
% not_modified(+)                                                        %
% Succeed if the information on which the predicate depends on (i.e. the %
% list of nodes given as argument) has not been modified                 %
%-------------------------------------------------------------------------

not_modified([]).
not_modified([Id/N|List]):-
	current_fact(ch_id(Id,N)), !,
	not_modified(List).

%-------------------------------------------------------------------------
% proj_to_prime(+,+,+,+,+,+,-,+,+,+)                                     %
% proj_to_prime(SgKey,Sg,Sv,Call,Proj,AbsInt,ListPrime,F,N,Id)           %
% This predicate obtains the list of Prime corresponding to each non     %
% recursive clause of Sg for a given Call. It first reads those non      %
% recursive clauses by means of a bagof and then proccess each one with  %
% a loop. If there is no non recursive clause, the answer will be        %
% ['$bottom'].                                                           %
%-------------------------------------------------------------------------

proj_to_prime_nr(SgKey,Sg,Sv,Call,Proj,AbsInt,_ClId,LPrime,Id) :-
	bagof(X, X^(trans_clause(SgKey,nr,X)),Clauses), !,
	proj_to_prime(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LPrime1,Id),
	compute_clauses_lub(AbsInt,Proj,LPrime1,LPrime).
proj_to_prime_nr(SgKey,Sg,Sv,_Call,Proj,AbsInt,ClId,LPrime,_Id) :-
	apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,ClId,Prime), !,
	singleton(Prime,LPrime).
proj_to_prime_nr(_SgKey,Sg,Sv,Call,_Proj,AbsInt,_ClId,LSucc,_Id) :-
	% In Java programs, mode and type information is known for any method.
	% Therefore, in case of a method with unavailable code we can still
	% infer useful information.
	current_pp_flag(prog_lang,java), !,
  unknown_call(AbsInt,Sg,Sv,Call,Succ),
  singleton(Succ,LSucc).
 %fixpoint_trace('external call completed',_Id,_N,SgKey,Sg,LSucc,_).
proj_to_prime_nr(SgKey,_Sg,_Sv,_Call,_Proj,_AbsInt,ClId,Bot,_Id) :-
	bottom(Bot), % TODO: leaves choicepoints
	inexistent(SgKey,ClId).

proj_to_prime_r(SgKey,Sg,Sv,Call,Proj,AbsInt,Prime,Id) :-
	bagof(X, X^(trans_clause(SgKey,nr,X)),Clauses), !,
	proj_to_prime(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,Prime,Id).
proj_to_prime_r(_SgKey,_Sg,_Sv,_Call,_Proj,_AbsInt,Bot,_Id):-
	bottom(Bot). % TODO: leaves choicepoints

proj_to_prime(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,Prime,Id) :-
	fixpoint_trace('non-recursive clauses',Id,_N,SgKey,Sg,Proj,Clauses),
	proj_to_prime_loop(Clauses,Sg,Sv,Call,Proj,AbsInt,ListPrime0,Id),
	reduce_equivalent(ListPrime0,AbsInt,ListPrime1),
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,ListPrime1,Prime).

proj_to_prime_loop([],_,_,_,_,_,[],_).
proj_to_prime_loop([Clause|Rest],Sg,Sv,Call,Proj,AbsInt,Primes,Id):-
	do_nr_cl(Clause,Sg,Sv,Call,Proj,AbsInt,Primes,TailPrimes,Id),!,
	proj_to_prime_loop(Rest,Sg,Sv,Call,Proj,AbsInt,TailPrimes,Id).

do_nr_cl(Clause,Sg,Sv,Call,Proj,AbsInt,Primes,TailPrimes,Id):-
	Clause = clause(Head,Vars_u,K,Body),
	clause_applies(Head,Sg), !,
	varset(Head,Hv),
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	process_body(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,Call,Proj,LPrime,Id),
	append_(LPrime,TailPrimes,Primes).
do_nr_cl(_Clause,_Sg,_Sv,_Call,_Proj,_AbsInt,Primes,Primes,_Id).

append_([Prime],TailPrimes,Primes):- !, Primes=[Prime|TailPrimes].
append_(LPrime,TailPrimes,Primes):- append(LPrime,TailPrimes,Primes).

process_body(Body,K,AbsInt,Sg,Hv,Fv,_,Head,Sv,Call,Proj,LPrime,Id):- 
	Body = g(_,[],'$built'(_,true,_),'true/0',true), !,
	Help=(Sv,Sg,Hv,Fv,AbsInt),
	singleton(Prime,LPrime),
	fixpoint_trace('visit fact',Id,_N,K,Head,Proj,Help),
	call_to_success_fact(AbsInt,Sg,Hv,Head,K,Sv,Call,Proj,Prime,_Succ),
	fixpoint_trace('exit fact',Id,_N,K,Head,Prime,Help),
	( current_pp_flag(fact_info,on) -> 
 	  call_to_entry(AbsInt,Sv,Sg,Hv,Head,K,[],Prime,Exit,_),
	  decide_memo(AbsInt,K,Id,no,Hv,[Exit])
	;
	  true
	).
process_body(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,_,Proj,Prime,Id):-
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo),
	fixpoint_trace('visit clause',Id,_N,K,Head,Entry,Body),
	singleton(Entry,LEntry),
	entry_to_exit(Body,K,LEntry,Exit,[],_,Vars_u,AbsInt,Id),
	fixpoint_trace('exit clause',Id,_N,K,Head,Exit,_),
	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime).

%-------------------------------------------------------------------------
% fixpoint_compute(+,+,+,+,+,+,+,+,+,-,+,-)                              %
% fixpoint_compute(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf        %
%                                       TempPrime,Prime,Id,List)         %
% It obtains the Prime for the recursive predicate Sg with Call (which   %
% has been assigned to node Id), and the list of nodes it depends on     %
% In doing this it performs an iteration over the recursive clauses of Sg%
% by calling to compute/13 and then checks if the fixpoint has been      %
% reached by calling to fixpoint/13. Fixpoint is reached if either       %
% NewList is empty (it means that Id does not depend on any node) or if  %
% Flag is a variable (it means that the information has not been         %
% modified within the iteration)                                         %
% LEntryInf is the list of (Entry,ExtraInfo) couples for each Clause. It %
% will be computed in the first iteration and used in subsequent ones    %
%-------------------------------------------------------------------------

fixpoint_compute(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,
	         Prime0,Prime,Id,List) :-
	fixpoint_compute_(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,
	                  Prime0,Prime1,Id,List),
	compute_clauses_lub(AbsInt,Proj,Prime1,Prime).

fixpoint_compute_(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,
	         TempPrime,Prime,Id,List) :-
        compute(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,
	         TempPrime,Prime1,Id,[],NewList,Flag),
%	widen_succ(AbsInt,TempPrime,Prime1,NewPrime),
%	decide_flag(AbsInt,TempPrime,NewPrime,SgKey,Sg,Id,Proj,Flag),
	fixpoint(NewList,Flag,Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,
	         Prime1,Prime,Id,List), !.
%	         NewPrime,Prime,Id,List), !.

fixpoint([],_,_,_,_,_,_,_,_,_,Prime1,Prime,_,List):- !,
	Prime = Prime1,
	List = [].
fixpoint(NewList,Flag,_,_,_,_,_,_,_,_,Prime1,Prime,_,List):- 
        var(Flag),!,
	Prime = Prime1,
	List = NewList.
fixpoint(_,_,Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,Prime1,Prime,Id,
                                                      List):-
        fixpoint_trace('fixpoint iteration',Id,_N,SgKey,Sg,Prime1,_),
        fixpoint_compute_(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,
	         Prime1,Prime,Id,List).

% some domains need normalization to perform the widening:
normalize_asub0(AbsInt,Prime0,Prime):-
	current_pp_flag(widen,on), !,
	normalize_asub(AbsInt,Prime0,Prime).
normalize_asub0(_AbsInt,Prime,Prime).

%% %% not needed since normalization is done only for nr initial value:
%% %% it is assumed that Prime is normalized thereafter
%% 
%% normalize_asub0(AbsInt,SgKey,Sg,Proj,Prime0,Id,Prime):-
%% 	current_pp_flag(widen,on), !,
%% 	normalize_asub(AbsInt,Prime0,Prime),
%% 	replace_fixpoint_record(SgKey,Sg,Proj,Prime0,Id,Prime).
%% normalize_asub0(_AbsInt,_SgKey,_Sg,_Proj,Prime,_Id,Prime).
%% 
%% replace_fixpoint_record(_SgKey,_Sg,_Proj,Prime,_Id,NewPrime):-
%% 	Prime==NewPrime, !.
%% replace_fixpoint_record(SgKey,Sg,Proj,Prime,Id,NewPrime):-
%% 	current_fact(fixpoint(SgKey,Sg,Proj0,Prime0,Id,L),Ref),
%% 	Proj0==Proj,
%% %	Prime0==Prime, may have changed!
%% 	% If normalization was done also in each fixp iteration
%% 	erase(Ref),
%% 	asserta_fact(fixpoint(SgKey,Sg,Proj,NewPrime,Id,L)).

%-------------------------------------------------------------------------
% compute(+,+,+,+,+,+,+,+,+,-,+,+,-,-)                                   %
% compute(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf                 %
%	                TempPrime,Prime,Id,List,NewList,Flag)            %
% It analyses each clause. If after the computation the                  %
% approximate abstract prime substitution changes, the Flag is changed to%
% 'notend' and erases the register ch_id(Id,Num), increases Num by one   %
% and records ch_id(Id,Num1), otherwise everything remains unchanged.    %
%-------------------------------------------------------------------------

compute([],_,_,_,_,_,_,[],Prime,Prime,_,List,List,_).
compute([Clause|Rest],SgKey,Sg,Sv,Call,Proj,AbsInt,[EntryInf|LEntryInf],
	                  TempPrime,Prime,Id,List,NewList,Flag) :-
	do_r_cl(Clause,SgKey,Sg,Sv,Proj,AbsInt,EntryInf,Id,List,IntList,
	                                   TempPrime,NewPrime,Flag),
	compute(Rest,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf,NewPrime,Prime,
	                                   Id,IntList,NewList,Flag).

do_r_cl(Clause,SgKey,Sg,Sv,Proj,AbsInt,EntryInf,Id,OldL,List,TempPrime,
	                                               NewPrime,Flag):-
	Clause=clause(Head,Vars_u,K,Body),
	clause_applies(Head,Sg), !,
	erase_previous_memo_tables_and_parents(Body,AbsInt,K,Id),
	varset(Head,Hv),
	reuse_entry(EntryInf,Vars_u,AbsInt,Sv,Sg,Hv,Head,K,Proj,Entry,ExtraInfo),
	fixpoint_trace('visit clause',Id,_N,K,Head,Entry,Body),
	singleton(Entry,LEntry),
	entry_to_exit(Body,K,LEntry,Exit,OldL,List,Vars_u,AbsInt,Id),
	fixpoint_trace('exit clause',Id,_N,K,Head,Exit,_),
	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime1),
	widen_succ(AbsInt,TempPrime,Prime1,NewPrime),
	decide_flag(AbsInt,TempPrime,NewPrime,SgKey,Sg,Id,Proj,Flag).
do_r_cl(_,_,_,_,_,_,_,_,List,List,Prime,Prime,_).

widen_succ_off(AbsInt,Prime0,Prime1,LPrime):-
	current_pp_flag(multi_success,on), !,
	reduce_equivalent([Prime0,Prime1],AbsInt,LPrime).
widen_succ_off(AbsInt,Prime0,Prime1,Prime):-
	singleton(P0,Prime0),
	singleton(P1,Prime1),
	singleton(P,Prime), 
	compute_lub(AbsInt,[P0,P1],P).

reuse_entry(EntryInf,Vars_u,AbsInt,Sv,Sg,Hv,Head,K,Proj,Entry,ExtraInfo):-
	var(EntryInf), !,
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo),
	EntryInf = (Entry,ExtraInfo).
reuse_entry(EntryInf,_Vars_u,_AbsInt,_Sv,_Sg,_Hv,_Head,_K,_Proj,Entry,ExtraInfo):-
	EntryInf = (Entry,ExtraInfo).

decide_flag(AbsInt,TempPrime,NewPrime,_SgKey,_Sg,_Id,_Proj,_Flag):-
	abs_subset_(NewPrime,AbsInt,TempPrime), !.
decide_flag(_AbsInt,TempPrime,NewPrime,SgKey,Sg,Id,Proj,Flag):-
	Flag = notend,
	merge_(NewPrime,TempPrime,LPrime),
	current_fact(fixpoint(SgKey,Sg,_,_,Id,Fs),Ref),
	erase(Ref),
	asserta_fact(fixpoint(SgKey,Sg,Proj,LPrime,Id,Fs)),  
	current_fact(ch_id(Id,Num),Ref3),
	erase(Ref3),
	Num1 is Num+1,
	asserta_fact(ch_id(Id,Num1)).

merge_([NewPrime],_TempPrime,LPrime):- !, LPrime=[NewPrime].
merge_(NewPrime,TempPrime,LPrime):-
	merge(NewPrime,TempPrime,LPrime).

%-------------------------------------------------------------------------
% entry_to_exit(+,+,+,-,+,-,+,+,+)                                       %
% entry_to_exit(Body,Key,Call,Exit,OldList,NewList,Vars_u,AbsInt,NewN)   %
% Traverses the body of a clause (first argument) obtaining the Exit for %
% a given Entry (represented by Call, since it is both the Entry of the  %
% clause and the Call for the first subgoal). Also it obtains the list of%
% nodes whose information has been used during the analysis of the clause%
%-------------------------------------------------------------------------

entry_to_exit((Sg,Rest),K,Call,Exit,OldList,NewList,Vars_u,AbsInt,NewN):- !,
	body_succ(Call,Sg,Succ,OldList,IntList,Vars_u,AbsInt,K,NewN,_),
	entry_to_exit(Rest,K,Succ,Exit,IntList,NewList,Vars_u,AbsInt,NewN).
entry_to_exit(true,_,Call,Call,List,List,_,_,_):- !.
%entry_to_exit(g(_,[],'$built'(_,true,_),'true/0',true),_,Call,Call,List,List,_,_,_):- !.
entry_to_exit(Sg,Key,Call,Exit,OldList,NewList,Vars_u,AbsInt,NewN):- 
	body_succ(Call,Sg,Exit,OldList,NewList,Vars_u,AbsInt,Key,NewN,_),
	decide_memo(AbsInt,Key,NewN,no,Vars_u,Exit),!. 

%-------------------------------------------------------------------------
% body_succ(+,+,-,+,-,+,+,+,+,-)                                         %
% body_succ(Call,Atom,Succ,List,NewList,HvFv,AbsInt,ClId,ParentId,ChildId)
% Atom has the form [Key,Sv,(I1,I2,Sg)]                                  %
% First, the lub between the abstract call substitution and the already  %
% computed information for this program point (if any) is computed. Then %
% the lub is recordered.                                                 %
% If the abstract call substitution is bottom (case handled by the first %
% clause) the success abstract substitution is also bottom and nothing   %
% more is needed. Otherwise (second clause) the computation of the       %
% success abstract substitution procceeds.                               %
%-------------------------------------------------------------------------

body_succ(Call,Atom,Succ,List,List,HvFv_u,AbsInt,_ClId,ParentId,no):-
	bottom(Call), !,
%	bottom(Succ),
	Succ = Call,
	Atom=g(Key,_Av,_I,_SgKey,_Sg),
	asserta_fact(memo_table(Key,AbsInt,ParentId,no,HvFv_u,Succ)).
body_succ(Call,Atom,Succ,List,NewList,HvFv_u,AbsInt,ClId,ParentId,Id):- 
	Atom=g(Key,Sv,Info,SgKey,Sg),
	fixpoint_trace('visit goal',ParentId,ClId,Key,Sg,Call,AbsInt),
	body_succ_(Info,SgKey,Sg,Sv,HvFv_u,Call,Succ,List,NewList,AbsInt,
	           ClId,Key,ParentId,Id),
	fixpoint_trace('exit goal',Id,ParentId,(SgKey,Key),Sg,Succ,AbsInt),
%	fixpoint_trace('exit goal',ParentId,ClId,(SgKey,Key),Sg,Succ,AbsInt),
	decide_memo(AbsInt,Key,ParentId,Id,HvFv_u,Call).

body_succ_(Info,SgKey,Sg,Sv,HFv,Call,Succ,L,NewL,AbsInt,ClId,Key,PId,Id):-
	Info = [_|_], !,
	split_combined_domain(AbsInt,Call,Calls,Domains),
	map_body_succ(Info,SgKey,Sg,Sv,HFv,Calls,Succs,L,NewL,Domains,
	              ClId,Key,PId,Id),
	split_combined_domain(AbsInt,Succ,Succs,Domains).
body_succ_(Info,SgKey,Sg,Sv,HFv,Call,Succ,L,NewL,AbsInt,ClId,Key,PId,Id):-
	body_succ0(Info,SgKey,Sg,Sv,HFv,Call,Succ,L,NewL,AbsInt,
	           ClId,Key,PId,Id).

% L=NewL and Id=no is not quite correct!!!
map_body_succ([],_SgKey,_Sg,_Sv,_HFv,[],[],L,L,[],_ClId,_Key,_PId,no).
map_body_succ([I|Info],SgKey,Sg,Sv,HFv,[Call|Calls],[Succ|Succs],L,NewL,
	      [AbsInt|Domains],ClId,Key,PId,Id):-
	body_succ0(I,SgKey,Sg,Sv,HFv,Call,Succ,L,_NewL,AbsInt,
	           ClId,Key,PId,_Id), !,
	map_body_succ(Info,SgKey,Sg,Sv,HFv,Calls,Succs,L,NewL,Domains,
	           ClId,Key,PId,Id).

%-------------------------------------------------------------------------
% body_succ0(+,+,+,+,+,+,-,+,-,+,+,+,-)                                  %
% body_succ0(RFlag,SgKey,Sg,Sv,HvFv,Call,Succ,List0,List,AbsInt,F,NewN,Id)%
% This predicate handles the special cases of the subgoals, i.e. when    %
% the subgoal is a builtin (also when it is a constraint since they are) %
% internally represented as builtins). Otherwise, computation proceeds.  %
%-------------------------------------------------------------------------

%% body_succ0('$var',_SgKey,Sg,_Sv_u,_HvFv_u,Call,Succ,List0,List,AbsInt,
%% 	    ClId,F,_N,Id):-
%% 	!,
%% 	variable(F,ClId),
%% 	Id=no,
%% 	List=List0,
%% 	each_unknown_call(Call,AbsInt,[Sg],Succ). % Sg is a variable
body_succ0('$var',SgKey,Sg,_Sv_u,HvFv_u,Calls,Succs,List0,List,AbsInt,
	    ClId,F,_N,Id):-
        !,
	( Calls=[Call],
	  concrete(AbsInt,Sg,Call,Concretes),
	  concretes_to_body(Concretes,SgKey,AbsInt,B)
	-> fixpoint_id(Id),
	   meta_call(B,HvFv_u,Calls,[],Succs,List0,List,AbsInt,ClId,Id,Ids),
	   assertz_fact(memo_call(F,Id,AbsInt,Concretes,Ids))
	 ; Id=no,
	   List=List0,
	   variable(F,ClId),
	   each_unknown_call(Calls,AbsInt,[Sg],Succs) % Sg is a variable
	).
body_succ0('$meta'(T,B,_),SgKey,Sg,Sv_u,HvFv_u,Call,Succ,List0,List,AbsInt,
	    ClId,F,N,Id):-
        !,
	(current_pp_flag(reuse_fixp_id,on) ->
	   ( Call=[C]
	     -> sort(Sv_u,Sv),
	        project(AbsInt,Sg,Sv,HvFv_u,C,Proj),
		fixpoint_id_reuse_prev(SgKey,AbsInt,Sg,Proj,Id)
              ; true
	   )
	;
	    fixpoint_id(Id)
	),
	meta_call(B,HvFv_u,Call,[],Exits,List0,List,AbsInt,ClId,Id,_Ids),
	( body_succ_meta(T,AbsInt,Sv_u,HvFv_u,Call,Exits,Succ) ->
      ( Call=[C] ->
          sort(Sv_u,Sv),
          project(AbsInt,Sg,Sv,HvFv_u,C,Proj),
          each_project(Exits,AbsInt,Sg,Sv,HvFv_u,Prime),
          asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)]))
	    ; true
	   )
	; % for the trusts, if any:
	  varset(Sg,Sv_r), % Sv_u contains extra vars (from meta-term)
                           % which will confuse apply_trusted
	  body_succ0(nr,SgKey,Sg,Sv_r,HvFv_u,Call,Succ,[],_List,AbsInt,
		        ClId,F,N,Id0),  % TODO: Why forced nr? Can this make the fixpoint not to finish?
	  retract_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id0,Ps)), % missing cut? (Id instantiated?)
	  asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps))
	).
%asserta_complete(K,AbsInt,Sg,Sv_u,HvFv_u,Call,Succ,Id,F,N).
body_succ0('$built'(T,Tg,Vs),SgKey,Sg,Sv_u,HvFv_u,Call,Succ,List0,List,AbsInt,
	    _ClId,F,N,Id):-
	!,
	Id=no,
	List=List0,
	sort(Sv_u,Sv),
	each_body_succ_builtin(Call,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,
	                       F,N,Succ).
body_succ0(RFlag,SgKey,Sg,Sv_u,HvFv_u,Call,Succ,List0,List,AbsInt,
	   ClId,F,N,Id):-
	sort(Sv_u,Sv),
	each_call_to_success(Call,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,
                             Succ,List0,List,F,N,Id).

each_call_to_success([Call],RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,Succ,L0,L,
	             F,N,Id):-
	!,
	project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
	call_to_success(RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,Succ,L1,F,N,Id),

	merge(L1,L0,L).
each_call_to_success(LCall,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,L0,L,
                     F,N,Id):-
	each_call_to_success0(LCall,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,
                              LSucc,L0,L,F,N,Id).

each_call_to_success0([],_Flag,_SgK,_Sg,_Sv,_HvFv,_AbsInt,_,[],L,L,_F,_N,_NN).
each_call_to_success0([Call|LCall],RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,
	              LSucc,L0,L,F,N,NewN):-
	project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
	call_to_success(RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,LSucc0,L1,F,N,_),
	merge(L0,L1,L2),
	append(LSucc0,LSucc1,LSucc),
	each_call_to_success0(LCall,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,
	                      LSucc1,L2,L,F,N,NewN).

%GP if the list of Bodies is empty, then there is nothing to analyze 
%   and we can make Succ = Call. Some more thinking is welcome
meta_call([],_HvFv_u,Call,[],Call,List,List,_AbsInt,_ClId,_Id,[]).
meta_call([Body|Bodies],HvFv_u,Call,Succ0,Succ,L0,List,AbsInt,ClId,Id,Ids):-
	meta_call_([Body|Bodies],HvFv_u,Call,Succ0,Succ,L0,List,AbsInt,ClId,Id,Ids).

meta_call_([Body|Bodies],HvFv_u,Call,Succ0,Succ,L0,List,AbsInt,ClId,Id,Ids):-
	meta_call_body(Body,ClId,Call,Succ1,L0,L1,HvFv_u,AbsInt,Id,Ids0),
%	widen_succ(AbsInt,Succ0,Succ1,Succ2),
	append(Succ0,Succ1,Succ2),
	append(Ids0,Ids1,Ids),
	meta_call_(Bodies,HvFv_u,Call,Succ2,Succ,L1,List,AbsInt,ClId,Id,Ids1).
meta_call_([],_HvFv_u,_Call,Succ,Succ,List,List,_AbsInt,_ClId,_Id,[]).

meta_call_body((Sg,Rest),K,Call,Exit,OldList,NewList,Vars_u,AbsInt,PId,CIds):-
	!,
	CIds=[Id|Ids],
	body_succ(Call,Sg,Succ,OldList,IntList,Vars_u,AbsInt,K,PId,Id),
	meta_call_body(Rest,K,Succ,Exit,IntList,NewList,Vars_u,AbsInt,PId,Ids).
meta_call_body(true,_,Call,Call,List,List,_,_,_,[no]):- !.
meta_call_body(Sg,Key,Call,Exit,OldList,NewList,Vars_u,AbsInt,PId,[Id]):- 
	body_succ(Call,Sg,Exit,OldList,NewList,Vars_u,AbsInt,Key,PId,Id).

concretes_to_body([],_SgKey,_AbsInt,[]).
concretes_to_body([Sg|Sgs],SgKey,AbsInt,[B|Bs]):-
	% have to module-expand Sg!!!!
	body_info0(Sg:SgKey,[],AbsInt,B),
	concretes_to_body(Sgs,SgKey,AbsInt,Bs).

%-------------------------------------------------------------------------
% query(+,+,+,+,+,+,+,-)
%-------------------------------------------------------------------------

:- doc(query(AbsInt,QKey,Query,Qv,RFlag,N,Call,Succ),
	"The success pattern of @var{Query} with @var{Call} is
         @var{Succ} in the analysis domain @var{AbsInt}. The predicate
         called is identified by @var{QKey}, and @var{RFlag} says if it
         is recursive or not. The goal @var{Query} has variables @var{Qv},
         and the call pattern is uniquely identified by @var{N}.").

query(AbsInt,QKey,Query,Qv,RFlag,N,Call,Succ) :-
	project(AbsInt,Query,Qv,Qv,Call,Proj),
	fixpoint_trace('init fixpoint',N,N,QKey,Query,Proj,_),
	call_to_success(RFlag,QKey,Call,Proj,Query,Qv,AbsInt,0,Succ,_,N,0,Id), %N = Call point key
	!,
	fixpoint_trace('exit goal',Id,query(N),(QKey,QKey),Query,Succ,AbsInt),
	approx_to_completes(AbsInt).


query(_AbsInt,_QKey,_Query,_Qv,_RFlag,_N,_Call,_Succ):-
% should never happen, but...
	error_message("SOMETHING HAS FAILED!").
