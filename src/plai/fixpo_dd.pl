/*             Copyright (C)1990-2002 UPM-CLIP				*/
:- module(fixpo_dd,
	[ query/8,
	  init_fixpoint/0,
	  cleanup_fixpoint/1,
	  entry_to_exit/7
	],
	[assertions, nativeprops, datafacts, isomodes, regtypes]).

:- use_package(.(notrace)). % inhibits the tracing
:- use_package(spec(no_debug)).

:- include(fixpo_dx_common).

:- use_module(ciaopp(plai/tarjan), [recursive_class/2]).

:- use_module(ciaopp(p_unit/program_keys),
	[decode_litkey/5, decode_predkey/3, is_entrykey/1, get_predkey/3, get_clkey/4]).

:- use_module(library(messages)).
:- use_module(engine(messages_basic), [display_list/1]).

:- use_module(ciaopp(plai/apply_assertions),
	[apply_assrt_no_source/6,apply_assrt_call_to_success/8,apply_assrt_exit/7]).
:- use_module(ciaopp(plai/incanal/plai_db_comparator), [check_same_success/3]).
:- use_module(ciaopp(plai/fixpo_ops), [process_analyzed_clause/7, get_singleton/2]).
% IG: added this to correct comparison between Primes.

:- use_module(ciaopp(plai/plai_db)).

:- use_module(library(lists), [member/2]).

%------------------------------------------------------------------------%

:- doc(stability, devel).
% TODO: The following bugs may be fixed
:- doc(bug,"Check analysis of meta_calls works after introducing
        fixpoint_reuse_prev_id/5").
:- doc(bug,"Possibly incorrect results at program point for warplan.").
:- doc(bug, "singleton/1 is leaving choicepoints.").
%------------------------------------------------------------------------%

:- export('$change_list'/2).
:- data '$change_list'/2.
:- data computing_change/1.

:- doc(init_fixpoint/0,"Cleanups the database of analysis of
	temporary information.").
init_fixpoint:-
	retractall_fact('$change_list'(_,_)),
	retractall_fact(computing_change(_)),
	trace_fixp:cleanup.

%------------------------------------------------------------------------%
% TODO: fix modes, it was: call_to_success(+,+,-,+,+,+,+,-,+,+,+,?)
:- pred call_to_success(+RFlag,+SgKey,+Call,+Proj,+Sg,+Sv,+AbsInt,?ClId,-Succ,+F,+N,-Id)
        : (atm(AbsInt), list(Sv))
 => (int(N), nonvar(Succ), nonvar(Call), dd_id(Id)) + not_fails
 #"It obtains the Succ for a given Sg and Call.
   Before computing the Succ we check if it has already been computed.
   If it has but there is a $change_list associated this means that this
   Succ was computed using information that was not yet final and has
   changed. Thus we recompute as needed to have the final Succ
   If no Succ has already been computed (there is no complete for it)
   we compute it from scratch.".
   
call_to_success(_RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,F,N,Id) :-
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),Ref),
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1),!,
	reuse_complete(Ref,SgKey,Proj,Sg,Sv,AbsInt,F,N,Id,Fs,Prime1,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).
call_to_success(nr,SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,Succ,F,N,Id):-
        fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
        fixpoint_trace('non-recursive initiated',Id,N,SgKey,Sg,Proj,_),
        proj_to_prime_nr(SgKey,Sg,Sv,Call,Proj,AbsInt,ClId,Prime,Id),
        fixpoint_trace('non-recursive completed',Id,N,SgKey,Sg,Prime,_),
        ( Id = '$bottom_call' ->
            Succ = Prime, Call = Prime
        ;
            asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])),
            each_extend(Sg,Prime,AbsInt,Sv,Call,Succ)
        ).
call_to_success(r,SgKey,Call,Proj,Sg,Sv,AbsInt,_ClId,Succ,F,N,Id) :-
	init_fixpoint0(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime),
	each_extend(Sg,Prime,AbsInt,Sv,Call,Succ).

%------------------------------------------------------------------------%
:- pred reuse_complete(+Ref,+SgKey,+Proj,+Sg,+Sv,+AbsInt,+F,+N,+Id,+Fs,+Prime1,-Prime)
        : (atm(SgKey), list(Sv), atm(AbsInt), atm(F), int(N), plai_db_id(Id), list(Fs))
 => nonvar(Prime) + not_fails
 #"This predicate tries to reuse a complete with id
   @var{Id}. @var{Prime} is the success pattern obtained from
   performing the fixpoint.

   The predicate works as follows:
   1. If there are changes:
      The fixpoint is computed considering those changes,
      as a result, a complete for the call to be analyzed has been asserted.
      This complete is kept as is except for adding F,N to the list of callers
      if they were not added.
   
   2. If there are no changes:
      The complete is stored with the success pattern ordered and adding F,N
      to the list of callers of that complete @var{Fs}.".
reuse_complete(Ref,SgKey,Proj,Sg,Sv,AbsInt,F,N,Id,Fs,Prime1,Prime):-
	each_abs_sort(Prime1,AbsInt,TempPrime),
	( current_fact('$change_list'(Id,ChList),Ref2) ->
	    erase(Ref2),
	    fixpoint_compute_change(ChList,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id),
	    current_fact(complete(SgKey,AbsInt,A,B,C,Id,Fs2),Ref3),
	    patch_parents(Ref3,complete(SgKey,AbsInt,A,B,C,Id,Ps),F,N,Ps,Fs2)
	;
	    Prime = TempPrime,
      patch_parents(Ref,complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps),F,N,Ps,Fs)
	).

:- pred init_fixpoint0/10 + not_fails.
init_fixpoint0(SgKey,Call,Proj0,Sg,Sv,AbsInt,F,N,Id,Prime):-
	current_pp_flag(widen,on),
	current_pp_flag(multi_success,off),
	widen_call(AbsInt,SgKey,Sg,F,N,Proj0,Proj), !,
	init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime).
init_fixpoint0(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime):-
	init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime).

init_fixpoint1(SgKey,_Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime):-
	current_fact(complete(SgKey,AbsInt,Subg,Proj1,Prime1,Id,Fs),Ref), % backtracking here
	identical_proj(AbsInt,Sg,Proj,Subg,Proj1),!,
	reuse_complete(Ref,SgKey,Proj,Sg,Sv,AbsInt,F,N,Id,Fs,Prime1,Prime).
init_fixpoint1(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime):-
	init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime).

init_fixpoint_(SgKey,Call,Proj,Sg,Sv,AbsInt,F,N,Id,Prime):-
	fixpoint_get_new_id(SgKey,AbsInt,Sg,Proj,Id),
	( current_pp_flag(widen,on) ->
	    asserta_fact(complete_parent(Id, [(F,N)]))
	; true),
    fixpoint_trace('non-recursive initiated',Id,N,SgKey,Sg,Proj,_),
	proj_to_prime_r(SgKey,Sg,Sv,Call,Proj,AbsInt,TempPrime,Id),
  fixpoint_trace('non-recursive completed',Id,N,SgKey,Sg,TempPrime,_),
	asserta_fact(complete(SgKey,AbsInt,Sg,Proj,TempPrime,Id,[])),
	bagof(X, X^(trans_clause(SgKey,r,X)),Clauses),!,
	fixpoint_trace('fixpoint initiated',Id,N,SgKey,Sg,Proj,Clauses),
  compute(Clauses,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime1,Id),
	fixpoint_ch(SgKey,Sg,Sv,Proj,AbsInt,Prime1,Prime2,Id), % !.
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime2,Prime3),
	get_complete(SgKey,AbsInt,Sg,_Proj,Prime4_u,Id,Fs2,Ref),
	each_abs_sort(Prime4_u,AbsInt,Prime4),
  process_analyzed_clause(AbsInt,Sg,Sv,Proj,Prime3,Prime4,Prime),
	% Code for debugging % TODO: use toggleable debug/1
	( \+ check_same_success(AbsInt, Prime2, Prime) -> % TODO: debug
	    write('something going wrong\n'),
	    display_list([SgKey,': ',Sg,'\n', 'Proj: ', Proj, '\n', 'Prime2: ',Prime2,'\n','Prime3: ',Prime3,'\n']),
      display_list(['Prime4: ',Prime4,'\n','Prime: ',Prime,'\n\n'])
	;
        true
  ),
  patch_parents(Ref,complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps),F,N,Ps,Fs2).

%-------------------------------------------------------------------------
% [IG] add compute_clauses_lub (resources) and ready to merge with fixpo_plai
:- export(proj_to_prime_nr/9).
:- pred proj_to_prime_nr(+SgKey,+Sg,+Sv,+Call,+Proj,+AbsInt,+Clid,-ListPrime,+Id)
 : (atm(SgKey), list(Sv,var), atm(AbsInt), plai_db_id(Id))
 => (list(ListPrime)) + not_fails
 #"This predicate obtains the list of Prime corresponding to each non
   recursive clause of Sg for a given Call. It first reads those non
   recursive clauses by means of a bagof and then proccess each one with
   a loop. If there is no non recursive clause, the answer will be
   @tt{['$bottom']}.
   @begin{alert} @var{Clid} may be 0 also (see @pred{fixpo_ops:inexistent/1}.
   @end{alert}".
proj_to_prime_nr(SgKey,Sg,Sv,Call,Proj,AbsInt,_ClId,LPrime,Id) :-
	bagof(X, X^(trans_clause(SgKey,nr,X)),Clauses), !,
	proj_to_prime(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LPrime,Id).
%	compute_clauses_lub(AbsInt,LPrime1,Proj,LPrime).
proj_to_prime_nr(SgKey,Sg,Sv,_Call,Proj,AbsInt,_ClId,LPrime,_Id) :-
	apply_assrt_no_source(SgKey,AbsInt,Sg,Sv,Proj,Prime), !,
	get_singleton(Prime,LPrime).
proj_to_prime_nr(_SgKey,Sg,Sv,Call,_Proj,AbsInt,_ClId,LSucc,_Id) :-
	% In Java programs, mode and type information is known for any method.
	% Therefore, in case of a method with unavailable code we can still
	% infer useful information.
	current_pp_flag(prog_lang,java), !,
	unknown_call(AbsInt,Sg,Sv,Call,Succ),
	get_singleton(Succ,LSucc).
proj_to_prime_nr(SgKey,_Sg,_Sv,_Call,_Proj,_AbsInt,ClId,Bot,_Id) :-
	bottom(Bot), !, % TODO: fix, it should not leave choice points
	inexistent(SgKey,ClId).

:- export(proj_to_prime_r/8).
:- pred proj_to_prime_r/8 + not_fails.
proj_to_prime_r(SgKey,Sg,Sv,Call,Proj,AbsInt,Prime,Id) :-
	bagof(X, X^(trans_clause(SgKey,nr,X)),Clauses), !,
	proj_to_prime(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,Prime,Id).
proj_to_prime_r(_SgKey,_Sg,_Sv,_Call,_Proj,_AbsInt,Bot,_Id):-
	bottom(Bot), !. % TODO: fix, it should not leave choice points

:- export(proj_to_prime/9).
:- pred proj_to_prime(+Clauses,+SgKey,+Sg,+Sv,+Call,+Proj,+AbsInt,Prime,+Id)
        : (list(Clauses), atm(SgKey), list(Sv), atm(AbsInt)) + not_fails.
proj_to_prime(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,Prime,Id) :-
	fixpoint_trace('non-recursive clauses',Id,_N,SgKey,Sg,Proj,Clauses),
	proj_to_prime_loop(Clauses,Sg,Sv,Call,Proj,AbsInt,ListPrime0,Id),
	reduce_equivalent(ListPrime0,AbsInt,ListPrime1),
	each_apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,ListPrime1,Prime).

:- pred proj_to_prime_loop/8 + not_fails.
proj_to_prime_loop([],_,_,_,_,_,[],_).
proj_to_prime_loop([Clause|Rest],Sg,Sv,Call,Proj,AbsInt,Primes,Id):-
	do_nr_cl(Clause,Sg,Sv,Call,Proj,AbsInt,Primes,TailPrimes,Id),!,
	proj_to_prime_loop(Rest,Sg,Sv,Call,Proj,AbsInt,TailPrimes,Id).

:- pred do_nr_cl/9 + not_fails.
do_nr_cl(Clause,Sg,Sv,Call,Proj,AbsInt,Primes,TailPrimes,Id):-
	Clause = clause(Head,Vars_u,ClKey,Body),
	clause_applies(Head,Sg), !,
	varset(Head,Hv),
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	process_body(Body,ClKey,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,Call,Proj,TPrime,Id),
  store_raw_success(ClKey,AbsInt,Id,Sg,Proj,TPrime),
  apply_assrt_exit(AbsInt,Sg,Sv,Proj,TPrime,LPrime,_),
	append_(LPrime,TailPrimes,Primes).
do_nr_cl(_Clause,_Sg,_Sv,_Call,_Proj,_AbsInt,Primes,Primes,_Id).

append_([Prime],TailPrimes,Primes):- !, Primes=[Prime|TailPrimes].
append_(LPrime,TailPrimes,Primes):- append(LPrime,TailPrimes,Primes).

:- pred process_body/13 + not_fails.
process_body(Body,K,AbsInt,Sg,Hv,_Fv,_,Head,Sv,Call,Proj,LPrime,Id):- 
	Body = g(_,[],'$built'(_,true,_),'true/0',true),!,
	Help=(Sv,Sg,Hv,_Fv,AbsInt),
	fixpoint_trace('visit fact',Id,_N,K,Head,Proj,Help),
	call_to_success_fact(AbsInt,Sg,Hv,Head,K,Sv,Call,Proj,Prime,_Succ),
	get_singleton(Prime,LPrime),
	( current_pp_flag(fact_info,on) ->
	    call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,[],Prime,Exit,_),
	    decide_memo(AbsInt,K,Id,no,Hv,[Exit])
	;
	    true
	),
	fixpoint_trace('exit fact',Id,_N,K,Head,Prime,Help).
process_body(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,_,Proj,Prime,Id):-
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,Entry,ExtraInfo),
	fixpoint_trace('visit clause',Id,_N,K,Head,Entry,Body),
	get_singleton(Entry,LEntry),
	entry_to_exit(Body,K,LEntry,Exit,Vars_u,AbsInt,Id),
	fixpoint_trace('exit clause',Id,_N,K,Head,Exit,_),
	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime).

%------------------------------------------------------------------------
:- pred body_succ(+Call,+Literal,-Succ,+HvFv_u,+AbsInt,+ClId,+ParentId,-Id)
        : (list(HvFv_u), atm(AbsInt), plai_db_id(ParentId))
        => (nonvar(Succ), dd_id(Id))+ not_fails
#"First, the lub between the abstract call substitution and the already
  computed information for this program point (if any) is computed. Then
  the lub is recordered.
  If the abstract call substitution is bottom (case handled by the first
  clause) the success abstract substitution is also bottom and nothing
  more is needed. Otherwise (second clause) the computation of the       
  success abstract substitution procceeds.".
body_succ(Call,Atom,Succ,HvFv_u,AbsInt,_ClId,ParentId,no):-
	bottom(Call), !,
	Succ = Call,
	Atom=g(Key,_Av,_I,_SgKey,_Sg),
	asserta_fact(memo_table(Key,AbsInt,ParentId,no,HvFv_u,Succ)).
body_succ(Call,Atom,Succ,HvFv_u,AbsInt,ClId,ParentId,Id):- 
        Atom=g(Key,Sv,Info,SgKey,Sg),
        fixpoint_trace('visit goal',ParentId,ClId,Key,Sg,Call,AbsInt),
        decide_memo(AbsInt,Key,ParentId,no,HvFv_u,Call),
        body_succ0(Info,SgKey,Sg,Sv,HvFv_u,Call,Succ,AbsInt,ClId,Key,ParentId,Id),
        fixpoint_trace('exit goal',Id,ParentId,(SgKey,Key),Sg,Succ,AbsInt),
        change_son_if_necessary(Id,Key,ParentId,HvFv_u,Call,AbsInt).

change_son_if_necessary(no,_,_,_,_,_):-!.
change_son_if_necessary(NewId,Key,NewN,Vars_u,Call,AbsInt):-
    current_fact(memo_table(Key,AbsInt,NewN,Id,_,_),Ref),
    (Id = NewId ->
       true
    ;
       erase(Ref),
       decide_memo(AbsInt,Key,NewN,NewId,Vars_u,Call)).

%------------------------------------------------------------------------
:- export(compute/9).
:- pred compute(+Clauses,+SgKey,+Sg,+Sv,+Proj,+AbsInt,+TempPrime,-Prime,+Id)
        : (atm(SgKey), list(Sv), atm(AbsInt), plai_db_id(Id))
        => nonvar(Prime) + not_fails
#" It analyses each clause. If after the computation the                  
   approximate abstract prime substitution changes, the Flag is changed to
   'notend' and erases the register ch_id(Id,Num), increases Num by one
   and recorders ch_id(Id,Num1), otherwise everything remains unchanged.".
compute([],_,_,_,_,_,Prime,Prime,_).
compute([Clause|Rest],SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id) :-
	do_r_cl(Clause,SgKey,Sg,Sv,Proj,AbsInt,Id,TempPrime,NewPrime),
	compute(Rest,SgKey,Sg,Sv,Proj,AbsInt,NewPrime,Prime,Id).

:- pred do_r_cl/9 + not_fails.
do_r_cl(Clause,SgKey,Sg,Sv,Proj,AbsInt,Id,TempPrime,Prime):-
	Clause=clause(Head,Vars_u,ClKey,Body),
	clause_applies(Head,Sg), !, 
	varset(Head,Hv),
	sort(Vars_u,Vars),
	ord_subtract(Vars,Hv,Fv),
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,Entry,ExtraInfo),
%	erase_previous_memo_tables_and_parents(Body,AbsInt,K,Id),
	fixpoint_trace('visit clause',Id,_N,ClKey,Head,Entry,Body),
	get_singleton(Entry,LEntry),
	entry_to_exit(Body,ClKey,LEntry,Exit,Vars_u,AbsInt,Id),
  fixpoint_trace('exit clause',Id,_N,ClKey,Head,Exit,_),
  each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime1),
  store_raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime1),
  process_analyzed_clause(AbsInt,Sg,Sv,Proj,TempPrime,Prime1,Prime),
	decide_mark_parents(AbsInt,TempPrime,Prime,SgKey,Sg,Id,Proj).
do_r_cl(_,_,_,_,_,_,_,Prime,Prime).

:- pred decide_mark_parents/7 + not_fails.
decide_mark_parents(AbsInt,TempPrime,NewPrime,_SgKey,_Sg,_Id,_Proj):-
	abs_subset_(NewPrime,AbsInt,TempPrime),!.
decide_mark_parents(AbsInt,_TempPrime,NewPrime,SgKey,Sg,Id,Proj):-
        get_complete(SgKey,AbsInt,Sg,_,_,Id,Fs,Ref), % Id is unique
        erase(Ref),
        asserta_fact(complete(SgKey,AbsInt,Sg,Proj,NewPrime,Id,Fs)),
        decode_predkey(SgKey,P,A),
        ( recursive_class(P/A,Class) ->
            mark_parents_change_list(Fs,Class,AbsInt)
        ;
            td_mark_parents_change_list(Fs,AbsInt)
        ).

% in analysis after annotation
% the recursivity classes are not updated for newly introduced predicates

%----------------------------------------------------------------------
:- pred td_mark_parents_change_list(+Parents,+AbsInt)
        : list * atm + not_fails
 #"This complete has changed. So we add the change in the $change_list
   of all parents.".
td_mark_parents_change_list([],_).
td_mark_parents_change_list([(EntryKey,_)|Rest],AbsInt) :-
	is_entrykey(EntryKey), !,
	td_mark_parents_change_list(Rest,AbsInt).
td_mark_parents_change_list([(Literal,C)|Rest],AbsInt) :-
	get_parent_key(Literal,C,AbsInt,CKey),
	get_complete(CKey,AbsInt,_,_,_,C,Parents,_), !,
	decode_litkey(Literal,N,A,Cl,L),
	add_change(C,Literal,N/A/Cl/L,Parents,AbsInt),
	td_mark_parents_change_list(Rest,AbsInt).
td_mark_parents_change_list([_|Rest],AbsInt):- % in case we have erased
	td_mark_parents_change_list(Rest,AbsInt).        % the complete

%------------------------------------------------------------------------
:- export(add_change/5).
:- pred add_change(+C,Lit_Key,+Literal,+Parents,+AbsInt)
        : ( plai_db_id(C), atm(Lit_Key)) + not_fails
	#"@var{C}: Id of the complete of the predicate that changed
      @var{Lit_Key}: Key of the @var{Literal} of the complete that needs recomputing.
      @var{Literal}: @var{Literal} with the term @tt{F/A/C/L}.
      @var{Parents}: Program points in which the literal is called (0 means an entry)
                                          @var{AbsInt}: Abstract Domain.".
add_change(C,Lit_Key,Literal,Parents,AbsInt) :-
        insert_in_changelist(C,Lit_Key,Literal,MFlag),
        ( MFlag = marked ->
            true % this avoids infinite loops (already marked)
        ;
            td_mark_parents_change_list(Parents,AbsInt)
        ).

:- pred insert_in_changelist/4 + not_fails.
insert_in_changelist(C,Lit_Key,Literal,MFlag) :-
        current_fact('$change_list'(C,ChList),Ref),!,
        insert_literal(ChList,Lit_Key,Literal,NewList,Flag),
        (Flag == yes ->
           erase(Ref),
           asserta_fact('$change_list'(C,NewList)),
           MFlag = not_marked
        ;
            MFlag = marked
        ).
insert_in_changelist(C,Lit_Key,Literal,not_marked) :-
        asserta_fact('$change_list'(C,[(Lit_Key,Literal)])).

insert_literal([], Lit_Key, Literal,[(Lit_Key,Literal)],yes).
insert_literal([(Head_Key,Head_Lit)|Tail], Lit_Key,Literal,Set,Flag) :-
	compare(Order, Head_Lit, Literal),
	insert_literal_(Order,Head_Key,Head_Lit,Tail,Lit_Key,Literal,Set,Flag).

insert_literal_(<,_Head_Key,N/A/C/_G1,_Tail,_Lit_Key,N/A/C/_G2,_NewList,no):-!.
insert_literal_(<, Head_Key,Head_Lit, Tail,Lit_Key, Literal, [Head|Set],Flag) :-
	Head = (Head_Key,Head_Lit),
	insert_literal(Tail,Lit_Key, Literal, Set,Flag).
insert_literal_(=, _Head_Key,_Head_Lit, _Tail, _,_, _NewList,no).
insert_literal_(>,_Head_Key,N/A/C/_G1,Tail,Lit_Key,N/A/C/G2,NewList,yes):-!,
	NewList = [(Lit_Key,N/A/C/G2)|Tail].
insert_literal_(>,Head_Key,Head_Lit,Tail,Lit_Key,Literal,NewList,yes):-
	NewList = [(Lit_Key,Literal),(Head_Key,Head_Lit)|Tail].

%------------------------------------------------------------------------
:- pred mark_parents_change_list(+Parents,+SCC,+AbsInt)
        : list * list * atm + not_fails
 #"This complete has changed. So we add the change in the $change_list
   of all parents. If the parent is in the same SCC then we recursively
   mark its parents as well.".
mark_parents_change_list([],_,_).
mark_parents_change_list([(EntryKey,_)|Rest],SCC,AbsInt):-
	% Is this working when we have more than one query?
        is_entrykey(EntryKey), !,
        mark_parents_change_list(Rest,SCC,AbsInt).
mark_parents_change_list([(LitKey,C)|Rest],SCC,AbsInt):-
	get_parent_key(LitKey,C,AbsInt,Key),
	decode_litkey(LitKey,N,A,Cl,G),
	( member(N/A,SCC) ->
    get_complete(Key,AbsInt,_,_,_,C,Parents,_),
    add_change_(C,LitKey,N/A/Cl/G,Parents,SCC,AbsInt)
	;
	    ( ('$change_list'(C,_) ; computing_change(C)) ->
	        % The parent the parent that is not in the same SCC comes from a
	        % different entry, so it was added previously to the change list.
	        true
	    ;
          % This complete is not expected to be in the parents list, only
          % the ones that appear during the fixpoint of predicate @var{Key}
          throw(error(unexpected_parent(LitKey,C,SCC)))
	    )
	),
	mark_parents_change_list(Rest,SCC,AbsInt).

%------------------------------------------------------------------------
:- pred add_change_(+C,+Lit_Key,+Literal,+Parents,+SCC,+AbsInt)
        : int * atm * term * list * list * atm + not_fails.
add_change_(C,Lit_Key,Literal,Parents,SCC,AbsInt):-
        insert_in_changelist(C,Lit_Key,Literal,MFlag),
        ( MFlag = marked ->
          true % this avoids infinite loops (already marked)
        ;
            mark_parents_change_list(Parents,SCC,AbsInt)
        ).

%------------------------------------------------------------------------
:- export(fixpoint_compute_change/9).
:- pred fixpoint_compute_change(+Changes,+SgKey,+Sg,+Sv,+Proj,+AbsInt,+TempPrime,-Prime,+Id)
        : (atm(SgKey), list(Sv), atm(AbsInt), plai_db_id(Id))
        => nonvar(Prime) + not_fails
#" It obtains the Prime for the recursive predicate Sg with Call (which
   has been assigned to node Id), and the list of nodes it depends on
   In doing this it performs an iteration over the recursive clauses of Sg
   by calling to compute_change/13 and then checks if the fixpoint has
   been reached by calling to fixpoint/13. Fixpoint is reached if either
   NewList is empty (it means that Id does not depend on any node) or if
   Flag is a variable (it means that the information has not been         
   modified within the iteration)
   LEntryInf is the list of (Entry,ExtraInfo) couples for each Clause. It 
   will be computed in the first iteration and used in subsequent ones".
fixpoint_compute_change(Changes,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id) :-
	assertz_fact(computing_change(Id)),
	compute_change(Changes,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime1,Id),
	( retract_fact(computing_change(Id)) -> true ; fail),
	fixpoint_ch(SgKey,Sg,Sv,Proj,AbsInt,Prime1,Prime,Id),!.

%------------------------------------------------------------------------
:- pred fixpoint_ch(+SgKey,+Sg,+Sv,+Proj,+AbsInt,+Prime1,-Prime,+Id)
        : (atm(SgKey), list(Sv), atm(AbsInt), int(Id))
        => nonvar(Prime) + not_fails
#"Decides whether we should keep on iterating (the information the 
 complete depends on has changed or not).".
fixpoint_ch(SgKey,Sg,Sv,Proj,AbsInt,Prime1,Prime,Id):-
	current_fact('$change_list'(Id,Changes),Ref),
	erase(Ref),
	fixpoint_compute_change(Changes,SgKey,Sg,Sv,Proj,AbsInt,Prime1,Prime,Id), !.
fixpoint_ch(_,_,_,_,_,Prime,Prime,_).

%------------------------------------------------------------------------
:- pred compute_change(+Changes,+SgKey,+Sg,+Sv,+Proj,+AbsInt,+TempPrime,-Prime,+Id)
        : (list(Changes), atm(SgKey), list(Sv), atm(AbsInt), plai_db_id(Id))
        => nonvar(Prime) + not_fails
 #"We compute a fixpoint iteration.".
compute_change([],_,_,_,_,_,Prime,Prime,_).
% the literal N/A/C/0 means that this literal has been introduced during 
% incremental addition. So the clause must be first checked to see if it 
% applies for the corresponding Subgoal. If it does, it is analyzed entirely
compute_change([(_,N/A/C/0)|Rest],SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id) :-!,
  get_clkey(N,A,C,ClKey),
	trans_clause(SgKey,_,clause(Head,Vars_u,ClKey,Body)),
	( clause_applies(Head,Sg)->
	    varset(Head,Hv),
	    sort(Vars_u,Vars),
	    ord_subtract(Vars,Hv,Fv),
	    call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,Entry,ExtraInfo),
%	    erase_previous_memo_tables_and_parents(Body,AbsInt,ClKey,Id),
%  not needed as it is the first time we analyze this clause
	    get_singleton(Entry,LEntry),
	    entry_to_exit(Body,ClKey,LEntry,Exit,Vars_u,AbsInt,Id),
	    each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime1),
      store_raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime1),
      process_analyzed_clause(AbsInt,Sg,Sv,Proj,TempPrime,Prime1,TrustedPrime),
	    decide_mark_parents(AbsInt,TempPrime,TrustedPrime,SgKey,Sg,Id,Proj)
 ;
        TrustedPrime = TempPrime % the CP head does not unify with the new clause
 ),
 compute_change(Rest,SgKey,Sg,Sv,Proj,AbsInt,TrustedPrime,Prime,Id).
compute_change([(Ch_Key,N/A/C/_)|Rest],SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id) :-
	current_fact(memo_table(Ch_Key,AbsInt,Id,_,Vars_u,Entry)),
	each_abs_sort(Entry,AbsInt,S_Entry),
	get_clkey(N,A,C,ClKey),
	trans_clause(SgKey,_,clause(Head,Vars_u,ClKey,Body)),
	advance_in_body(Ch_Key,Body,NewBody), !, % IG this cut should be after trans_clause
	varset(Head,Hv),
	sort(Vars_u,Vars),
 	ord_subtract(Vars,Hv,Fv),
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,_,ExtraInfo), % only for the ExtraInfo?
	erase_previous_memo_tables_and_parents(NewBody,AbsInt,ClKey,Id),
	entry_to_exit(NewBody,ClKey,S_Entry,Exit,Vars_u,AbsInt,Id),
	each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime1),
  store_raw_success(ClKey,AbsInt,Id,Sg,Proj,Prime1),
  process_analyzed_clause(AbsInt,Sg,Sv,Proj,TempPrime,Prime1,TrustedPrime),
	decide_mark_parents(AbsInt,TempPrime,TrustedPrime,SgKey,Sg,Id,Proj),
	compute_change(Rest,SgKey,Sg,Sv,Proj,AbsInt,TrustedPrime,Prime,Id).
% The change is within a meta_call that is not defined in the loaded
% modules e.g. findall/3, catch/3, etc... (no trans_clause/3 available)
compute_change([_|Rest],SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id) :-
	% The memo_table was already erased
	apply_assrt_no_source(SgKey,AbsInt,Sg,Sv,Proj,NPrime),
  get_singleton(NPrime,NLPrime),
  decide_mark_parents(AbsInt,TempPrime,NLPrime,SgKey,Sg,Id,Proj),
  compute_change(Rest,SgKey,Sg,Sv,Proj,AbsInt,TempPrime,Prime,Id).

:- pred each_call_to_success/12 + not_fails.
each_call_to_success([Call0],RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,Succ,F,N,Id):- !,
	project(AbsInt,Sg,Sv,HvFv_u,Call0,Proj0),
	apply_assrt_call_to_success(AbsInt,Sg,Sv,Proj0,HvFv_u,Call0,Proj,Call),
  ( bottom(Proj) ->
      Succ = Proj,
      Id = '$bottom_call',
      % annotate that the assertion is incompatible
      add_invalid_call(SgKey,AbsInt,F,N,Sg,Call0)
  ;
      call_to_success(RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,Succ,F,N,Id)
  ).
each_call_to_success(LCall,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,F,N,Id):-
	each_call_to_success0(LCall,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,F,N,Id).

% TODO: This predicate is for multivariant, not integrated with applying
% assertions during fixpoint [IG]
each_call_to_success0([],_Flag,_SgK,_Sg,_Sv,_HvFv,_AbsInt,_ClId,[],_F,_N,_NN).
each_call_to_success0([Call0|LCall],RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc,F,N,NewN):-
	project(AbsInt,Sg,Sv,HvFv_u,Call0,Proj0),
	apply_assrt_call_to_success(AbsInt,Sg,Sv,Proj0,HvFv_u,Call0,Proj,Call),
  call_to_success(RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,ClId,LSucc0,F,N,_Id),
	append(LSucc0,LSucc1,LSucc),
	each_call_to_success0(LCall,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,LSucc1,F,N,NewN).

widen_call(AbsInt,SgKey,Sg,F1,Id0,Proj1,Proj):-
	( current_pp_flag(widencall,off) -> fail ; true ),
	widen_call0(AbsInt,SgKey,Sg,F1,Id0,[Id0],Proj1,Proj), !,
	fixpoint_trace('result of widening',Id0,F1,SgKey,Sg,Proj,_).

widen_call0(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	widen_call1(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj), !.
widen_call0(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
	current_pp_flag(widencall,com_child),
	widen_call2(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj).

widen_call1(AbsInt,SgKey,Sg,F1,Id0,Ids,Proj1,Proj):-
        % current_fact(complete(SgKey0,AbsInt,Sg0,Proj0,_Prime0,Id0,_)),
        ( current_fact(complete(SgKey,AbsInt,Sg0,Proj0,_Prime0,Id0,_)) -> SgKey = SgKey0 % fast
        ; current_fact(complete(SgKey0,AbsInt,Sg0,Proj0,_Prime0,Id0,_)) % TODO: slow! fix indexing by Id0
        ),
        %
        current_fact(complete_parent(Id0,Fs0)),
        ( SgKey=SgKey0,
          member((F1,_NewId0),Fs0)
        -> Sg0=Sg,
        abs_sort(AbsInt,Proj0,Proj0_s),
        abs_sort(AbsInt,Proj1,Proj1_s),
        widencall(AbsInt,Proj0_s,Proj1_s,Proj)
        ; ( member((_F1,NewId0),Fs0) -> true ; fail),
          \+ member(NewId0,Ids),
          widen_call1(AbsInt,SgKey,Sg,F1,NewId0,[NewId0|Ids],Proj1,Proj)
        ).

widen_call2(AbsInt,SgKey,Sg,F1,_Id,_Ids,Proj1,Proj):-
	current_fact(complete(SgKey,AbsInt,Sg0,Proj0,_Prime0,_,Fs0)),
	( member((F1,_Id0),Fs0) -> true ; fail ),
	Sg0=Sg,
%	same_fixpoint_ancestor(Id0,[Id0],AbsInt),
	abs_sort(AbsInt,Proj0,Proj0_s),
	abs_sort(AbsInt,Proj1,Proj1_s),
	widencall(AbsInt,Proj0_s,Proj1_s,Proj).

%-------------------------------------------------------------------------
% TODO: fix modes, it was: query(+,+,+,+,+,+,+,-)
:- pred query(+AbsInt,+QKey,+Query,+Qv,+RFlag,?N,+Call,-Succ)
        : atm * atm * term * list * atm * term * term * term + not_fails
 #"The success pattern of @var{Query} with @var{Call} is
      @var{Succ} in the analysis domain @var{AbsInt}. The predicate
      called is identified by @var{QKey}, and @var{RFlag} says if it
      is recursive or not. The goal @var{Query} has variables @var{Qv},
      and the call pattern is uniquely identified by @var{N}.".
query(AbsInt,QKey,Query,Qv,RFlag,N,Call0,Succ) :-
	project(AbsInt,Query,Qv,Qv,Call0,Proj0),
	fixpoint_trace('init fixpoint',N,N,QKey,Query,Proj0,_),
 	apply_assrt_call_to_success(AbsInt,Query,Qv,Proj0,Qv,Call0,Proj,Call),
  call_to_success(RFlag,QKey,Call,Proj,Query,Qv,AbsInt,0,Succ,N,0,_Id),
	!,
 	fixpoint_trace('exit goal',_Id,query(N),(QKey,QKey),Query,Succ,AbsInt).
query(_AbsInt,_QKey,Query,Qv,_RFlag,_N,_Call,_Succ):-
% should never happen, but...
	error_message("~q:~q SOMETHING HAS FAILED!~n",[Query,Qv]),
	throw(bug).

% --------------------------------------------------
%%% Code added by IG
:- use_module(ciaopp(plai/domains), [less_or_equal/3]).
:- use_module(ciaopp(plai/incanal/incanal_driver), [td_rec_delete_complete/3]).

% Added for changes in completes during modular analysis
:- export(add_external_complete_change/6).
:- pred add_external_complete_change(+AbsInt,+NewPrime,+SgKey,+Sg,+Id,+Proj)
	: (atm(AbsInt), list(NewPrime), atm(SgKey), plai_db_id(Id)) + not_fails
#"This predicate updates analysis information given a complete that
has changed externally. Typically this is used for updating completes
that are outdated as a consequence of modular analysis (the analysis
of a module was improved). The complete that has change has key
@var{SgKey} and id @var{Id}. The new answer for the complete is
@var{NewPrime} and refers to domain @var{AbsInt}.

Changes in answers are updated as follows:

@begin{itemize}

@item If the new answer is more general than the previous one, the update is
as simple as replacing the answer in the complete and adding an
event.

@item If the new answer is more specific or incompatible, the
information that depends on it has to be deleted and recomputed. We
are removing the information with a top-down deletion strategy,
although a bottom-up deletion strategy could more efficient. The
fixpoint has to be runned after this deletion.

@end{itemize}
        ".
add_external_complete_change(AbsInt,NewPrime,SgKey,Sg,Id,Proj):-
	get_complete(SgKey,AbsInt,Sg,_,OldPrime,Id,Fs,Ref), !,
	each_abs_sort(OldPrime, AbsInt, OldPrime_s),
	each_abs_sort(NewPrime, AbsInt, NewPrime_s),
	( each_less_or_equal(AbsInt, OldPrime_s, NewPrime_s) ->
	    erase(Ref),
	    asserta_fact(complete(SgKey,AbsInt,Sg,Proj,NewPrime,Id,Fs)),
	    td_mark_parents_change_list(Fs,AbsInt)
	;
	    td_rec_delete_complete(Id, SgKey, AbsInt)
	).
add_external_complete_change(_,_,_,_,_,_).
% This case means that the complete was removed earlier

% TODO: duplicated (similar code in fixpo_ops)
each_less_or_equal(_, [], []) :- !.
each_less_or_equal(AbsInt, [S1|S1s], [S2|S2s]) :-
	less_or_equal(AbsInt, S1, S2),
	each_less_or_equal(AbsInt, S1s, S2s).

:- regtype dd_id/1.
dd_id('$bottom_call').
dd_id(X) :-
        plai_db_id(X).