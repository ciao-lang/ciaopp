:- module(apply_assertions_inc, [], [assertions,datafacts,isomodes,nativeprops]).

:- doc(title, "Incrementally applying assertion during fixpoint").

:- doc(author, "Isabel Garcia-Contreras").

% TODO: doc
:- doc(bug, "Work in progress.").
:- doc(bug, "Assuming that the analysis is monotonic!!!").
:- doc(bug, "Potential errors in parents of meta_calls").

:- use_package(.(notrace)). % inhibits the tracing

:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(aggregates), [(^)/2, bagof/3, findall/3]).
:- use_module(library(terms_check), [variant/2]).

:- use_module(ciaopp(plai/apply_assertions)).
:- use_module(ciaopp(plai/plai_db)).
:- use_module(ciaopp(plai/fixpo_dd), [add_change/5]).
:- use_module(ciaopp(plai/domains), [project/6, exit_to_prime/8, identical_abstract/3,
    glb/4, less_or_equal/3, compute_lub/3, unknown_entry/4]).
:- use_module(ciaopp(plai/fixpo_ops), [get_singleton/2, fixpoint_get_new_id/5, advance_in_body/3]).
:- use_module(ciaopp(plai/transform), [trans_clause/3]).

:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7]).

:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(library(compiler/p_unit/p_unit_db), [assertion_read/9, assertion_type/2]).
:- use_module(library(compiler/p_unit/program_keys)).

:- use_module(ciaopp(plai/incanal/incanal_driver), [td_rec_delete_complete/3]).

:- export(cleanup_applied_assertions_inc/1).
:- pred cleanup_applied_assertions_inc/1 + not_fails.
cleanup_applied_assertions_inc(AbsInt) :-
    cleanup_applied_assertions(AbsInt).

:- export(update_assertions_pred/3).
:- pred update_assertions_pred(+Pred, +AbsInt, +Assrts) + not_fails.
update_assertions_pred(F/A, AbsInt, Assrts) :-  % This predicate splits in call an success
    get_predkey(F,A,SgKey),
    % if the assertion has no completes, do not update
%    ( \+ \+ complete(SgKey, AbsInt,_,_,_,_,_) ->
        % split in call and success assertions
        split_assrts_by_type(Assrts,CallAs,SuccAs),
        ( CallAs = [_|_] ->
            update_assertions_pred_calls(SgKey,F/A,AbsInt)
        ; true ),
        % calls are processed before success because they may invalidate success
        ( SuccAs = [_|_] ->
            update_assertions_pred_success(SgKey,AbsInt)
        ; true ).
 %   ; true ).

split_assrts_by_type([],[],[]).
split_assrts_by_type([DA|As],[DA|CallAs],SuccAs) :-
    extract_assertion(DA,A),
    assertion_type(A,calls), !,
    split_assrts_by_type(As,CallAs,SuccAs).
split_assrts_by_type([DA|As],CallAs,[DA|SuccAs]) :-
    extract_assertion(DA,A),
    assertion_type(A,success), !,
    split_assrts_by_type(As,CallAs,SuccAs).
split_assrts_by_type([_|As],CallAs,SuccAs) :- % currently we do not process comp
    split_assrts_by_type(As,CallAs,SuccAs).

extract_assertion(ins(_,A), A).
extract_assertion(del(_,A), A).

% ----------------------------------------------------------------------
:- doc(section, "Update calls").

update_assertions_pred_calls(SgKey,F/A,AbsInt) :-
    functor(Head,F,A),
    get_old_call_assertions_proj(SgKey,Head,AbsInt,OldAProj), % using cached abstraction
    retractall_fact(call_asr(SgKey,_,_,AbsInt,_)), % force reabstrating
    get_new_call_abstraction(SgKey,Head,AbsInt,NewAProj),
    \+ identical_abstract(AbsInt,NewAProj,OldAProj),
    % changes may affect the analysis result
    ( % failure-driven loop
      enum_calls_pred(AbsInt,SgKey,LitKey,CId,LitSg,LitProj,OldId,OldALitProj),
    % rechecking the assertion for that program point LitKey
    apply_abstraction(AbsInt,LitSg,LitProj,Head,NewAProj,NewALitProj),
    ( OldALitProj \== '$bottom' ->
        apply_abstraction(AbsInt,LitSg,LitProj,Head,OldAProj,OldALitProj)
    ; true),
    % check if reapplying the assertions produces the same result
    \+ identical_abstract(AbsInt,NewALitProj,OldALitProj),
    % assert that something needs to be reanalyzed
    fixpoint_trace('[incanal] change', OldId,_,LitKey,LitSg,NewALitProj,_),
    update_literal_call_in_completes(AbsInt,SgKey,LitKey,CId,OldId,LitSg,OldALitProj,NewALitProj),
    fail
    ; true
    ).
update_assertions_pred_calls(_SgKey,_,_AbsInt).

:- pred enum_calls_pred(+AbsInt,+SgKey,-LitKey,-CId,LitSg,-LitProj,-OldId,?OldALitProj). %+ non_det.
enum_calls_pred(AbsInt,SgKey,LitKey,CId,LitSg,LitProj,OldId,_OldALitProj) :-
    complete(SgKey,AbsInt,_,_,_,OldId,Ps),
    member((LitKey,CId),Ps),
    get_memo_table(LitKey,AbsInt,CId,OldId,ClauseVars_u,ListCall,_),
    get_literal(LitKey,ClauseVars_u,LitSg,LitVars),
    get_singleton(Call,ListCall),
    project(AbsInt,LitSg,LitVars,ClauseVars_u,Call,LitProj).
enum_calls_pred(AbsInt,SgKey,LitKey,CId,LitSg,LitProj,_OldId,'$bottom') :-
    invalid_call(SgKey,AbsInt,LitKey,CId,LitSg,LitProj).

update_literal_call_in_completes(AbsInt,SgKey,LitKey,CId,OldId,LitSg,OldALitProj,NewALitProj) :-
    ( NewALitProj = '$bottom' ->
        NId = OldId % remove old memo_tables when deleting the complete
        % invalid_call will be annotated during fixpoint
    ; get_existing_call(AbsInt,SgKey,LitSg,NewALitProj,Id1) ->
        % change Id in memo_table
        ( get_memo_table(LitKey,AbsInt,CId,_,Vars_u,Call,MemoRef) -> 
            erase(MemoRef),
            assertz_fact(memo_table(LitKey,AbsInt,CId,Id1,Vars_u,Call))
        ; true % there is no memo_table if prev Proj was '$bottom'
        ),
        % remove parent CId from parent
        add_parent_complete(SgKey,AbsInt,Id1,CId,LitKey),
        ParentsChange = [(LitKey,CId)], NId = Id1 % in case we need to mark
    ; % no complete exists for this call pattern
        fixpoint_get_new_id(SgKey,AbsInt,LitSg,NewALitProj,NId),
        ParentsChange = [(LitKey,CId)],
        assertz_fact(complete(SgKey,AbsInt,LitSg,NewALitProj,['$bottom'],NId,ParentsChange))
        % this complete may not be necessary
    ),
    % Assuming monotonicity (no widening)!!, otherwise we should remove in both cases
    ( less_or_equal(AbsInt,OldALitProj,NewALitProj) ->
        td_add_complete_call_change(SgKey,AbsInt,NId,ParentsChange)
    ;
        td_rec_delete_complete(NId,SgKey,AbsInt)
    ),
    ( nonvar(OldId) ->
      % this has to be done after deleting the complete or the case of the
      % new literal being bot will not work
      del_parent_complete(SgKey,AbsInt,OldId,CId,LitKey,_NFs)
    ; true).


:- pred apply_abstraction(+AbsInt,+Sg0,+Proj0,+Sg1,+Proj1,-NProj0)
    #" Perform the abstract unification of terms @var{Sg0} and @var{Sg1}
    with abstract substitutions @var{Proj0} and @var{Proj1}. @var{NProj0} in
    term of the variables of @var{Sg0}. Assuming that @var{Sg1}:@var{Proj1} is
    normalized.".
% using the same number when they refer to the same variables
apply_abstraction(AbsInt,Sg0,Proj0,Sg1,Proj1,NProj0) :-
    varset(Sg0,Sv0),
    abs_normalize(AbsInt,Sg0,Sv0,Proj0,Head1,Hv1,NProj1,ExtraInfo),
    Head1 = Sg1, % unification to be able to perform the domain operation
    glb(AbsInt,NProj1,Proj1,AProj1),
    exit_to_prime(AbsInt,Sg0,Hv1,Head1,Sv0,AProj1,ExtraInfo,NProj0).

:- pred get_literal(+LitKey,+ClauseVars_u,-Sg,-LitVars) + is_det.
get_literal(LitKey,ClauseVars_u,Sg,LitVars) :-
    decode_litkey(LitKey,F,A,N,_),
    get_predkey(F,A,SgKey),
    get_clkey(F,A,N,ClKey),
    trans_clause(SgKey,_,clause(_Head,ClauseVars_u,ClKey,Body)),
    advance_in_body(LitKey,Body,NBody),
    ( NBody = g(LitKey,LitVars,_Info,_SgKey,Sg)
    ; NBody = (g(LitKey,LitVars,_Info,_SgKey,Sg),_)
    ), !.

:- pred get_old_call_assertions_proj(SgKey,Head,AbsInt,-AProj)
    : (atm(SgKey), atm(AbsInt)) + (not_fails, is_det).
get_old_call_assertions_proj(SgKey,Head,AbsInt,AProj) :-
    get_applicable_status(Head,calls,Sts),
    call_asr(SgKey,_,Sts,AbsInt,_), !, % some assertion was applied
    get_call_assertions_asub(Head,SgKey,Sts,AbsInt,AProj).
get_old_call_assertions_proj(_SgKey,Head,AbsInt,AProj) :-
    varset(Head,Hv),
    unknown_entry(AbsInt,Head,Hv,AProj).

:- pred get_new_call_abstraction(SgKey,Head,AbsInt,-AsrProj)
    : (atm(SgKey), atm(AbsInt)) + (not_fails, is_det).
get_new_call_abstraction(SgKey,Head,AbsInt,AsrProj) :-
    get_applicable_status(Head,call,Sts),
    get_call_assertions_asub(Head,SgKey,Sts,AbsInt,AsrProj), !.
get_new_call_abstraction(_SgKey,Head,AbsInt,AsrProj) :-
    varset(Head,Hv),
    unknown_entry(AbsInt,Head,Hv,AsrProj).

get_existing_call(AbsInt,SgKey,Sg,AProj,Id) :-
    complete(SgKey,AbsInt,Sg0,Proj,_,Id,_),
    \+ \+ (variant(Sg,Sg0), Sg = Sg0, identical_abstract(AbsInt,Proj,AProj)), !.

% ----------------------------------------------------------------------
:- doc(section, "Update successes").

update_assertions_pred_success(SgKey,AbsInt) :-
    store_current_success_asr(SgKey,AbsInt),
    ( % failure-driven loop
      complete(SgKey,AbsInt,Sg,Proj,_OldPredPrime,Id,Parents),
    varset(Sg,Sv),
    abs_normalize(AbsInt,Sg,Sv,Proj,Head,Hv,NormProj,_ExtraInfo),
    get_old_assertions_succ(SgKey,Head,Hv,AbsInt,NormProj,OldAPrime), % using cached abstraction
    get_new_succ_abstraction(SgKey,Head,Hv,AbsInt,NormProj,NewAPrime),
    \+ identical_abstract(AbsInt,NewAPrime,OldAPrime),
    findall(ClKey,trans_clause(SgKey,_,clause(_,_,ClKey,_)), ClKeys),
    ( % failure-driven loop
      member(ClKey,ClKeys),
        get_raw_success(ClKey,AbsInt,Id,Sg,Proj,LRawPrime),
        get_singleton(RawPrime,LRawPrime),
        apply_abstraction(AbsInt,Sg,RawPrime,Head,NewAPrime,NewClPrime),
        apply_abstraction(AbsInt,Sg,RawPrime,Head,OldAPrime,OldClPrime),
        \+ identical_abstract(AbsInt,NewClPrime,OldClPrime),
        ( less_or_equal(AbsInt,OldClPrime,NewClPrime) ->
            decode_clkey(ClKey,F,A,N),
            add_change(Id,_,F/A/N/0,Parents,AbsInt),
            retract_fact(memo_table(ClKey,AbsInt,Id,_,_,_))
        ;
            % This can be refined and not remove nr clauses
            td_rec_delete_complete(Id,SgKey,AbsInt)
        ),
        fail
    ; true % TODO: check the whole predicate (for precision)
    % OldPredPrime \= lub({ClPrime_1,ClPrime_2,ClPrime_n})
    ),
    fail
    ; true
    ).
update_assertions_pred_success(_,_).

:- data old_success_asr_/6.
store_current_success_asr(SgKey,AbsInt) :-
    retractall_fact(old_success_asr_(SgKey,_,_,AbsInt,_,_)),
    ( % failure-driven loop
      retract_fact(success_asr(SgKey, Sg, Status, AbsInt, Call, Succ)),
        assertz_fact(old_success_asr_(SgKey, Sg, Status, AbsInt, Call, Succ)),
        fail
    ; true ).

get_old_assertions_succ(SgKey,Head,_Hv,AbsInt,Proj,OldAPrime) :-
    get_applicable_status(Head,success,Sts),
    old_success_asr(SgKey,Head,Proj,AbsInt,Sts,OldAPrime), !.
get_old_assertions_succ(_SgKey,Head,Hv,AbsInt,_Proj,OldAPrime) :-
    unknown_entry(AbsInt,Head,Hv,OldAPrime).

get_new_succ_abstraction(SgKey,Head,Hv,AbsInt,Proj,NewAPrime) :-
    get_applicable_status(Head,success,Sts),
    get_succ_assertion_asubs(SgKey,Head,Hv,Sts,AbsInt,Proj,NewAPrime), !.
get_new_succ_abstraction(_SgKey,Head,Hv,AbsInt,_Proj,NewAPrime) :-
    unknown_entry(AbsInt,Head,Hv,NewAPrime).

old_success_asr(SgKey,Head,Proj,AbsInt,Sts,Prime0) :-
    old_success_asr_(SgKey,Head,Sts,AbsInt,Proj0,Prime0), % backtracking here
    identical_abstract(AbsInt,Proj0,Proj), !.

td_add_complete_call_change(SgKey,AbsInt,Id,Parents) :-
    % mark to analyze all clauses
    bagof(X, X^(trans_clause(SgKey,_RFlag,X)),Clauses),
    mark_clauses(Clauses,AbsInt,Id,Parents).

mark_clauses([],_,_,_).
mark_clauses([clause(_Head,_Vars_u,Clid,_Body)|Cls],AbsInt,Id,Parents) :-
    decode_clkey(Clid, P, A, C), !,
    get_litkey(P,A,C,0,LitKey),
    add_change(Id,LitKey,P/A/C/0,Parents,AbsInt),
    % It's 0 because it is a new call, 1 assumes that there are already
    % memo_table entries
    mark_clauses(Cls,AbsInt,Id,Parents).
