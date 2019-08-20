:- module(fixpo_di,
	[ query/8,
	  init_fixpoint/0,
	  cleanup_fixpoint/1,
	  entry_to_exit/7
	],
	[assertions, datafacts,isomodes,nativeprops]).

:- use_package(.(notrace)). % inhibits the tracing
:- use_package(spec(nomem_usage)).
% :- use_module(spec(mem_usage), [update_mem_usage/0]).
:- use_package(spec(no_debug)).

:- doc(title,"A Depth Independent Fixpoint Algorithm").

:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains the implementation of the
  @em{depth independent} algorithm for incremental analysis of programs
  described in @cite{inc-fixp-sas}.  ").

:- use_module(spec(global_control), [spec_definition/8]).
:- use_module(spec(unfold_operations), [orig_pred_name/2]).
:- use_module(spec(modular_spec), 
	[ generate_abs_execs_from_equivs/0, reset_equivs/0]).
:- use_module(library(terms), [copy_args/3]).

:- include(.(fixpo_dx_common)).

:- use_module(ciaopp(plai/acc_ops)).

:- use_module(ciaopp(p_unit/program_keys), [decode_litkey/5]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(ciaopp(plai/intermod_success), [apply_success_policy/9]).
:- use_module(ciaopp(plai/domains), [unknown_call/4]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [member/2, dlist/3]).
:- use_module(library(messages)).

:- use_module(ciaopp(plai/apply_assertions_old), [apply_trusted/7]).
%------------------------------------------------------------------------%
:- doc(stability, devel).
:- doc(bug,"Check analysis of meta_calls works after introducing
        fixpoint_reuse_prev_id/5").
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 1/12/90                              %
%                       programmer: Kalyan Muthukumar,                   %
%                          completed: 15/10/92                           %
%              programmers:    M. Garcia de la Banda, F. Bueno           %
%                                                                        %
%                          modified:  22/Sep/94                          %
%              programmer :    A. G. Puebla Sanchez                      %
% -----------------------------------------------------------------------%
% This is a new fixpoint algorithm that tries to be both incremental and %
% more efficient than the previous one. Much of the code used is directly%
% taken from that version.                                               %
%  In this version the registers fixpoint and approx disappear. We only  %
% use the register complete together with $change_list. Every approx that%
% does not have a $change_list is a complete (at least by now)
%------------------------------------------------------------------------%

:- data complete_variant/8.

:- doc(init_fixpoint/0,"Cleanups the database of analysis of
	temporary information.").

init_fixpoint:-
	retractall_fact(complete_variant(_,_,_,_,_,_,_,_)),
	( current_pp_flag(reduced_cert,on) -> init_relevant_entries ; true),
	trace_fixp:cleanup,
	current_pp_flag(abs_spec_defs,ASD),
	( member(ASD,[exec,all]) ->
	    reset_equivs,
	    generate_abs_execs_from_equivs
	;
	    true)
%	init_unfold
        .

variants_to_completes(AbsInt):-
	current_fact(complete_variant(_,SgKey,AbsInt,Sg,Proj,Prime,Pid,Fs),Ref),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Pid,Fs)),
	erase(Ref),
	fail.
variants_to_completes(_AbsInt).

%------------------------------------------------------------------------%
% call_to_success(+,+,+,+,+,+,-,-,+,+)                                   %
% call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,F,N,NewN)            %
% It obtains the Succ for a given Sg and Call.                           %
%  This fixpoint algorithm uses the information in complete even if it   %
% is not really complete. Whenever a change in a complete is detected    %
% analysis starts for each clause that uses that complete from the       %
% literal that uses the complete. This makes incremental analysis        %
% in a bottom-up way. Each change in a complete forces a re-analysis of  %
% all the completes that used it and so recursively. The danger of       %
% bottom-up strategy is that it can re-analyse completes that may not be %
% needed. This introduces extra-work. The advantaje of bottom-up strategy%
% over top-down is that if the effect of the change is local, the        %
% analysis time will be small in general.                                %
%------------------------------------------------------------------------%
call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,F,N,Id) :-
%w	write('c'),
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1),!,
	reuse_complete(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Fs,Prime1,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,F,N,Id) :-
%w	write('c'),
	current_pp_flag(variants,on),
	current_fact(complete_variant(Id_o,SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1),!,
	reuse_complete_variant(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Id_o,Fs,Prime1,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,F,N,Id) :-
%w	write('c'),
	current_pp_flag(variants,on),
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id1,_Fs),_Ref),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2),!,
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	each_abs_sort(Prime2,AbsInt,Prime),
	asserta_fact(complete_variant(Id1,SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,Succ,F,N,Id) :-
	init_fixpoint0(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).


reuse_complete_variant(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Id_o,Fs,Prime1,Prime):-
	each_abs_sort(Prime1,AbsInt,Prime),
	check_if_parent_needed(Fs,F,N,NewFs,Flag),
	( Flag == needed ->
	    erase(Ref),
	    asserta_fact(complete_variant(Id_o,SgKey,AbsInt,Sg,Proj,Prime,Id,NewFs))
	;
	    true
	).

reuse_complete(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Fs,Prime1,Prime):-
	each_abs_sort(Prime1,AbsInt,Prime),
	check_if_parent_needed(Fs,F,N,NewFs,Flag),
	( Flag == needed ->
	    erase(Ref),
	    asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,NewFs))
	;
	    true
	),
        ( ( current_pp_flag(widen,on) -> 
	     current_fact(complete_parent(Id,FsP),RefP),
	     check_if_parent_needed(FsP,F,N,NewFsP,FlagP),
	      ( FlagP == needed ->
		  erase(RefP),
		  asserta_fact(complete_parent(Id,NewFsP))
	      ;
		  true
	      )
	    )
	;
	    true
	).

init_fixpoint0(SgKey,Call,Proj0,Sg,Sv,AbsInt,ClId,F,N,Id,Prime):-
	current_pp_flag(widen,on),
	current_pp_flag(multi_success,off),
	widen_call(AbsInt,SgKey,Sg,F,N,Proj0,Proj), !,
	init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,Prime).
init_fixpoint0(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,Prime):-
	init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,Prime).

init_fixpoint1(SgKey,_Call,Proj,Sg,_Sv,AbsInt,_ClId,F,N,Id,Prime):-
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1),!,
	reuse_complete(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Fs,Prime1,Prime).
init_fixpoint1(SgKey,_Call,Proj,Sg,_Sv,AbsInt,_ClId,F,N,Id,Prime):-
	current_pp_flag(variants,on),
	current_fact(complete_variant(Id_o,SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1),!,
	reuse_complete_variant(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Id_o,Fs,Prime1,Prime).
init_fixpoint1(SgKey,_Call,Proj,Sg,_Sv,AbsInt,_ClId,F,N,Id,Prime):-
	current_pp_flag(variants,on),
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id1,_Fs),_Ref),
	identical_proj_1(AbsInt,Sg,Proj,Subg,Proj1,Prime1,Prime2),!,
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	each_abs_sort(Prime2,AbsInt,Prime),
	asserta_fact(complete_variant(Id1,SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])).
init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,Prime):-	
	init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,Prime).

init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,F,N,Id,Prime):-
	bagof(X, Y^X^(trans_clause(SgKey,Y,X)),Clauses), !,
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	debug('SD '),
	(
	    (current_pp_flag(widen,on) ;
	     current_pp_flag(global_trees,on) )->
	    asserta_fact(complete_parent(Id,[(F,N)]))
	; 
	    true
	),
	spec_definition(Sg,Sv,Proj,AbsInt,Id,Clauses,NClauses,NSg),
	initial_guess(SgKey,AbsInt,Sg,Sv,Proj,InitialPrime,Id),
       	compute(NClauses,SgKey,NSg,Sv,Call,Proj,AbsInt,InitialPrime,_,Id),
	current_fact(complete(SgKey,AbsInt,Sg,_,Prime_u,Id,Fs2),Ref),
	reuse_complete(Ref,SgKey,Proj,Sg,AbsInt,F,N,Id,Fs2,Prime_u,Prime),
	((current_pp_flag(an_orig_def,on),
	  current_pp_flag(local_control,LC),
	  LC \== off) ->
	    compute_no_lub(Clauses,Sg,Sv,Call,Proj,AbsInt,Id)
	;
	    true).
init_fixpoint_(SgKey,_Call,Proj,Sg,Sv,AbsInt,ClId,F,N,Id,LPrime) :-
	apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,ClId,Prime), !,
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	singleton(Prime,LPrime),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,LPrime,Id,[(F,N)])),
	( current_pp_flag(widen,on) ->
	    asserta_fact(complete_parent(Id,[(F,N)]))
	; 
	    true
	).
init_fixpoint_(SgKey,_Call,_Proj,_Sg,_Sv,_AbsInt,ClId,_F,_N,_Id,Bot) :-
	bottom(Bot),
	inexistent(SgKey,ClId).

%------------------------------------------------------------------------
% initial_guess(+,+,+,+,+,-,+)
initial_guess(SgKey,AbsInt,Sg,Sv,Proj,[InitialPrime],Id):-
	( type_of_goal(multifile,Sg) 
	; type_of_goal(dynamic,Sg) 
	; type_of_goal(impl_defines,Sg) ), 
	!,
	unknown_call(AbsInt,Sv,Proj,Prime0),
	( apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime0,InitialPrime) ->
	  true
	; InitialPrime = Prime0
	),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,[InitialPrime],Id,[])).
initial_guess(SgKey,AbsInt,Sg,Sv,Proj,[InitialGuess],Id):-
	current_pp_flag(initial_guess,Guess),
	( Guess = bottom ->
	    Patterns = []
	;
	    findall((SgProj0,Proj0,Succ0), complete(SgKey,AbsInt,SgProj0,Proj0,[Succ0],_,_), Patterns)
	),
	apply_success_policy(Guess,AbsInt,SgKey,Sg,Sv,Proj,Patterns,InitialGuess,_),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,[InitialGuess],Id,[])).

%------------------------------------------------------------------------
% check_if_parent_needed(+,+,+,-,-)
% check_if_parent_needed(Old_parents,F,N,NewParents,Flag)
% This way if inserting parents makes them be in the same order as they were inserted 
% thus avoiding having to reverse the list of parents

check_if_parent_needed([],F,N,[(F,N)],needed).
check_if_parent_needed([(F,N)|Fs],F,N,[(F,N)|Fs],not):-!.
check_if_parent_needed([(F1,N1)|Fs],F,N,[(F1,N1)|NewFs],Flag):-
	check_if_parent_needed(Fs,F,N,NewFs,Flag).

%-------------------------------------------------------------------------
% compute(+,+,+,+,+,+,+,+).                                              %
% compute(Clauses,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Id)                  %
% It analyses each recursive clause. After each clause, we check if the  %
% new Prime substitution is more general than it was when the previous   %
% clause was analyzed. In this case we execute compute_each_change.      %
% Note that the prime in the corresponding complete may have been modified
% due to a compute_each_change and be more general than TempPrime. This is
% the reason why call_to_success does not trust the Prime computed here  %
% and looks for it in the complete. No compute_each_change is needed     %
% because if compute_each_change has updated the complete it has already %
% recursively called compute_each_change for this complete.              %
%-------------------------------------------------------------------------

compute([],_,_,_,_,_,_,Prime,Prime,_).
compute([Clause|Rest],SgKey,Sg,Sv,Call,Proj,AbsInt,TempPrime,Prime,Id) :-
	do_cl(Clause,SgKey,Sg,Sv,Call,Proj,AbsInt,Id,TempPrime,Prime1),
	compute(Rest,SgKey,Sg,Sv,Call,Proj,AbsInt,Prime1,Prime,Id).

compute_no_lub([],_,_,_,_,_,_).
compute_no_lub([Clause|Rest],Sg,Sv,Call,Proj,AbsInt,Id) :-
	do_cl_no_lub(Clause,Sg,Sv,Call,Proj,AbsInt,Id),
	compute_no_lub(Rest,Sg,Sv,Call,Proj,AbsInt,Id).

do_cl(Clause,SgKey,Sg,Sv,Call,Proj,AbsInt,Id,TempPrime,Prime):-
	Clause=clause(Head,Vars_u,K,Body),
	clause_applies(Head,Sg), !, 
	varset(Head,Hv),
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	process_body(Body,K,AbsInt,Sg,SgKey,Hv,Fv,Vars_u,Head,Sv,Call,Proj,TempPrime,Prime,Id).
do_cl(_,_,_,_,_,_,_,_,Primes,Primes).

do_cl_no_lub(Clause,Sg,Sv,Call,Proj,AbsInt,Id):-
	Clause=clause(Head,Vars_u,K,Body),
	clause_applies(Head,Sg), !, 
	varset(Head,Hv),
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	process_body_no_lub(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,Call,Proj,Id).
do_cl_no_lub(_,_,_,_,_,_,_).

call_to_entry_fact_each(_,_,_,_,_,[],[]).
call_to_entry_fact_each(AbsInt,Sv,Sg,Hv,Head,[P|Ps],[E|Ex]):-
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,[],P,E,_),
	call_to_entry_fact_each(AbsInt,Sv,Sg,Hv,Head,Ps,Ex).

%process_body(true,
process_body(Body,K,AbsInt,Sg,SgKey,Hv,Fv,_Vars_u,Head,Sv,Call,Proj,TempPrime,Prime,Id):-
	Body = g(_,[],'$built'(_,true,_),'true/0',true),!,
	Help=(Sv,Sg,Hv,Fv,AbsInt),
	fixpoint_trace('visit fact',Id,_N,K,Head,Proj,Help),
	update_mem_usage,
	call_to_success_fact(AbsInt,Sg,Hv,Head,K,Sv,Call,Proj,One_Prime,_Succ),
	singleton(One_Prime,Prime1),
	fixpoint_trace('exit fact',Id,_N,K,Head,Prime,Help),
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime1,Prime2),
	widen_succ(AbsInt,TempPrime,Prime2,NewPrime),
	decide_re_analyse(AbsInt,TempPrime,NewPrime,Prime,SgKey,Sg,Id,Proj),
	( current_pp_flag(fact_info,on) ->
	    call_to_entry_fact_each(AbsInt,Sv,Sg,Hv,Head,Prime,Exit),
	    decide_memo(AbsInt,K,Id,no,Hv,Exit)
	;
	    true
	).
process_body(Body,K,AbsInt,Sg,SgKey,Hv,Fv,Vars_u,Head,Sv,_Call,Proj,TempPrime,Prime,Id):-
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,Entry,ExtraInfo),
%	erase_previous_memo_tables_and_parents(Body,K,Id),
% not needed as it is the first time this clause is analysed (?)
	fixpoint_trace('visit clause',Id,_N,K,Head,Entry,Body),
	singleton(Entry,LEntry),
	entry_to_exit(Body,K,LEntry,Exit,Vars_u,AbsInt,Id),
	fixpoint_trace('exit clause',Id,_N,K,Head,Exit,_),
	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime1),
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime1,Prime2),
	widen_succ(AbsInt,TempPrime,Prime2,NewPrime),
	decide_re_analyse(AbsInt,TempPrime,NewPrime,Prime,SgKey,Sg,Id,Proj).

process_body_no_lub(Body,_K,_AbsInt,_Sg,_Hv,_Fv,_Vars_u,_Head,_Sv,_Call,_Proj,_Id):-
	Body = g(_,[],'$built'(_,true,_),'true/0',true),!.
%% 	Help=(Sv,Sg,Hv,Fv,AbsInt),
%% 	fixpoint_trace('visit fact',Id,_N,K,Head,Proj,Help),
%% 	update_mem_usage,
%% 	call_to_success_fact(AbsInt,Sg,Hv,Head,K,Sv,Call,Proj,One_Prime,_Succ),
%% 	singleton(One_Prime,Prime1),
%% 	fixpoint_trace('exit fact',Id,_N,K,Head,Prime,Help),
%% 	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime1,Prime2),
%% 	widen_succ(AbsInt,TempPrime,Prime2,NewPrime),
%% 	decide_re_analyse(AbsInt,TempPrime,NewPrime,Prime,SgKey,Sg,Id,Proj).
process_body_no_lub(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,_Call,Proj,Id):-
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,Entry,_ExtraInfo),
	fixpoint_trace('visit clause',Id,_N,K,Head,Entry,Body),
	singleton(Entry,LEntry),
	entry_to_exit(Body,K,LEntry,_Exit,Vars_u,AbsInt,Id).
%% 	fixpoint_trace('exit clause',Id,_N,K,Head,Exit,_),
%% 	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime1),
%% 	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime1,Prime2),
%% 	widen_succ(AbsInt,TempPrime,Prime2,NewPrime),
%% 	decide_re_analyse(AbsInt,TempPrime,NewPrime,Prime,SgKey,Sg,Id,Proj).

%-------------------------------------------------------------------------
% body_succ(+,+,-,+,-,+,+,+,+)                                           %
% body_succ(Call,[Key,Sv,(I1,I2,Sg)],Succ,Hv,Fv,AbsInt,NewN)             %
% First, the lub between the abstract call substitution and the already  %
% computed information for this program point (if any) is computed. Then %
% the lub is recordered.                                                 %
% If the abstract call substitution is bottom (case handled by the first %
% clause) the success abstract substitution is also bottom and nothing   %
% more is needed. Otherwise (second clause) the computation of the       %
% success abstract substitution procceeds.                               %
%-------------------------------------------------------------------------
body_succ(Call,Atom,Succ,HvFv_u,AbsInt,_ClId,ParentId,no):- 
	bottom(Call), !,
	bottom(Succ),
%	Succ = Call,
	Atom=g(Key,_Av,_I,_SgKey,_Sg),
	asserta_fact(memo_table(Key,AbsInt,ParentId,no,HvFv_u,Succ)).
body_succ(Call,Atom,Succ,HvFv_u,AbsInt,ClId,ParentId,Id):- 
	Atom=g(Key,Sv,Info,SgKey,Sg),
	fixpoint_trace('visit goal',ParentId,ClId,Key,Sg,Call,AbsInt),
	body_succ0(Info,SgKey,Sg,Sv,HvFv_u,Call,Succ,AbsInt,ClId,Key,ParentId,Id),
	fixpoint_trace('exit goal',Id,ParentId,(SgKey,Key),Sg,Succ,AbsInt),
	decide_memo(AbsInt,Key,ParentId,Id,HvFv_u,Call).

% change_son_if_necessary(no,_,_,_,_,_):-!.
% change_son_if_necessary(NewId,Key,NewN,Vars_u,Call,AbsInt):-
%         current_fact(memo_table(Key,AbsInt,NewN,Id,_,_),Ref),
%         (Id = NewId ->
%             true
%         ;
%             erase(Ref),
%             decide_memo(AbsInt,Key,NewN,NewId,Vars_u,Call)).            

%-------------------------------------------------------------------------

% if Prime computed for this clause is not more general than the 
% information we already had there is no need to compare with the info
% in complete which will always be more general (and no compute_change needed)
decide_re_analyse(AbsInt,TempPrime,NewPrime,Prime,_SgKey,_Sg,_Id,_Proj):-
%w	write(r),
%%	write(user,'identical abstract'),nl(user),
	abs_subset_(NewPrime,AbsInt,TempPrime),!,
	Prime = NewPrime.
decide_re_analyse(AbsInt,_TempPrime,NewPrime,Prime,SgKey,Sg,Id,Proj):-
%w	write(n),
	current_fact(complete(SgKey,AbsInt,OldSg,_,OldPrime_u,Id,Fs),Ref),
	functor(OldSg,_,A),
	copy_args(A,Sg,OldSg),
	each_abs_sort(OldPrime_u,AbsInt,OldPrime),
	widen_succ(AbsInt,OldPrime,NewPrime,Prime), 	
 	(abs_subset_(Prime,AbsInt,OldPrime)->
%	    write(user,'OK, no change needed'),write(user,Fs),nl(user)
	    true
	;
%%	    write(user,'lub needed '),nl(user),
	    erase(Ref),
	    asserta_fact(complete(SgKey,AbsInt,OldSg,Proj,Prime,Id,Fs)),
	    findall(Refv,current_fact(complete_variant(Id,SgKey,AbsInt,_,_,_,_,_),Refv),Variants),
	    dlist(Fs,FS,Tail),
	    acc_relevant_entry(Fs,Id),
            update_each_variant(Variants,OldSg,Prime,AbsInt,Tail),	    
	    compute_each_change(FS,AbsInt)).

:- doc(acc_relevant_entry(Fs,Id),"This predicate adds a fact
relevant @var{Id} to database when the complete for @var{Id} is
relevant for ACC, i.e., it has dependencies in @var{Fs}. It is only
executed when the flag for reduced certificates @var{reduced_cert} is
set to on").
acc_relevant_entry(Fs,Id):-
	    Fs \== [], 
	    current_pp_flag(reduced_cert,on),   
	    add_relevant(relevant(Id)),!.
acc_relevant_entry(_Fs,_Id).

update_each_variant([],_,_,_,[]).
update_each_variant([Ref|Variants],OldSg,Prime,AbsInt,NewFs):-
	current_fact(complete_variant(Id,SgKey,AbsInt,Sgv,Projv,_Primev,Idv,Fs),Ref),
	erase(Ref),
	varset(Sg,Hv),
	varset(Sgv,Hvv),
	each_exit_to_prime(Prime,AbsInt,Sgv,Hv,Sg,Hvv,(no,_),Prime2),
	asserta_fact(complete_variant(Id,SgKey,AbsInt,Sgv,Projv,Prime2,Idv,Fs)),
	dlist(Fs,NewFs,Tail),
	update_each_variant(Variants,OldSg,Prime,AbsInt,Tail).


compute_each_change([],_AbsInt).
compute_each_change([(Literal,Id)|Changes],AbsInt):-
%%	write(user,'Rec: '), write(user, Literal), nl(user),
	debug('+'),
	decode_litkey(Literal,N,A,Cl,_),
	get_predkey(N,A,SgKey),
	findout_sgkey_and_name(N,A,Old_SgKey,Old_N),
	current_fact(complete(Old_SgKey,AbsInt,Sg,Proj1,TempPrime1,Id,_),_),!,
	varset(Sg,Sv),
	abs_sort(AbsInt,Proj1,Proj),
	each_abs_sort(TempPrime1,AbsInt,TempPrime),
	current_fact(memo_table(Literal,AbsInt,Id,_,Vars_u,Entry),_),
	each_abs_sort(Entry,AbsInt,S_Entry),
	make_atom([N,A,Cl],Clid),
	trans_clause(SgKey,_,clause(Head,Vars_u,Clid,Body)),
	advance_in_body(Literal,Body,NewBody),
	varset(Head,Hv),
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	functor(Orig_Head,Old_N,A),
	copy_args(A,Head,Orig_Head),
	call_to_entry(AbsInt,Sv,Sg,Hv,Orig_Head,not_provided,Fv,Proj,_,ExtraInfo),
	erase_previous_memo_tables_and_parents(NewBody,AbsInt,Clid,Id),
	entry_to_exit(NewBody,Clid,S_Entry,Exit,Vars_u,AbsInt,Id),
	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Orig_Head,Sv,ExtraInfo,Prime1),
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime1,Prime2),
	widen_succ(AbsInt,TempPrime,Prime2,NewPrime),
	decide_re_analyse(AbsInt,TempPrime,NewPrime,_,Old_SgKey,Sg,Id,Proj),
	compute_each_change(Changes,AbsInt).
compute_each_change([_|Changes],AbsInt):- % no complete stored. Nothing
	compute_each_change(Changes,AbsInt). %need be recomputed.

findout_sgkey_and_name(N,A,SgKey,New_N):-
	current_pp_flag(local_control,off),!,
	get_predkey(N,A,SgKey),
	New_N = N.

findout_sgkey_and_name(N,A,SgKey,New_N):-
	orig_pred_name(N,New_N),
	get_predkey(New_N,A,SgKey).

% RFlag not needed (second argument). Kept for compatibility with dd.
each_call_to_success([Call],_,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,Succ,F,N,Id):- !,
	project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
	debug('C2S '),
	debug(Sg),
	update_mem_usage,
	call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,Succ,F,N,Id).
each_call_to_success(LCall,_,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,F,N,Id):-
	each_call_to_success0(LCall,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,F,N,Id).

each_call_to_success0([],_SgK,_Sg,_Sv,_HvFv,_AbsInt,_ClId,[],_F,_N,_NN).
each_call_to_success0([Call|LCall],SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,F,N,NewN):-
	project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
	update_mem_usage,
	call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,LSucc0,F,N,_Id),
	append(LSucc0,LSucc1,LSucc),
	each_call_to_success0(LCall,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc1,F,N,NewN).

widen_call(AbsInt,SgKey,Sg,F1,Id0,Proj1,Proj):-
	( current_pp_flag(widencall,off) -> fail ; true ),
	widen_call0(AbsInt,SgKey,Sg,F1,Id0,[Id0],Proj1,Proj), !,
	fixpoint_trace('result of widening',Id0,F1,SgKey,Sg,Proj,_).

widen_call0(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	widen_call1(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj).
widen_call0(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	current_pp_flag(widencall,com_child),
	widen_call2(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj).

widen_call1(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	current_fact(complete(SgKey0,AbsInt,Sg0,Proj0,_Prime0,Id0,_)),
	current_fact(complete_parent(Id0,Fs0)),
	( SgKey=SgKey0,
	  member((F1,_NewId0),Fs0)
	-> Sg0=Sg,
	   abs_sort(AbsInt,Proj0,Proj0_s),
	   abs_sort(AbsInt,Proj1,Proj1_s),
	   widencall(AbsInt,Proj0_s,Proj1_s,Proj)
	 ; member((_F1,NewId0),Fs0),
	   \+ member(NewId0,Ids),
	   widen_call1(AbsInt,SgKey,Sg,F1,NewId0,[NewId0|Ids],Proj1,Proj)
	).

widen_call2(AbsInt,SgKey,Sg,F1,_Id,_Ids,Proj1,Proj):-
	current_fact(complete(SgKey,AbsInt,Sg0,Proj0,_Prime0,_,Fs0)),
	member((F1,_Id0),Fs0),
	Sg0=Sg,
%	same_fixpoint_ancestor(Id0,[Id0],AbsInt),
	abs_sort(AbsInt,Proj0,Proj0_s),
	abs_sort(AbsInt,Proj1,Proj1_s),
	widencall(AbsInt,Proj0_s,Proj1_s,Proj).

%-------------------------------------------------------------------------

:- doc(query(AbsInt,QKey,Query,Qv,RFlag,N,Call,Succ),
	"The success pattern of @var{Query} with @var{Call} is
         @var{Succ} in the analysis domain @var{AbsInt}. The predicate
         called is identified by @var{QKey}, and @var{RFlag} says if it
         is recursive or not. The goal @var{Query} has variables @var{Qv},
         and the call pattern is uniquely identified by @var{N}.").
query(AbsInt,QKey,Query,Qv,_RFlag,N,Call,Succ) :-
	project(AbsInt,Query,Qv,Qv,Call,Proj),
	fixpoint_trace('init fixpoint',N,N,QKey,Query,Proj,_),
	update_mem_usage,
	call_to_success(QKey,Call,Proj,Query,Qv,AbsInt,0,Succ,N,0,Id),
	!,
 	fixpoint_trace('exit goal',_Id,query(N),(QKey,QKey),Query,Succ,AbsInt),
	asserta_fact(memo_table(N,AbsInt,0,Id,Qv,Succ)),
	variants_to_completes(AbsInt).
query(_AbsInt,_QKey,_Query,_Qv,_RFlag,_N,_Call,_Succ):-
% should never happen, but...
	error_message("SOMETHING HAS FAILED!"),
	fail.
