:- module(apply_assertions, [], [assertions,isomodes,datafacts,nativeprops]).

:- doc(title, "Applying assertions during fixpoint").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, "This module contains the logic of what assertions need
to be applied depending on the analysis step.

This module reads the values of the following flags:
@begin{itemize}
        @item @code{fixp_stick_to_success}: whether to use the value of the
        success assertions instead of what was inferred for the fixpoint (not
        working for eterms).

         For a module:
         @begin{verbatim}
:- module(_,_,[assertions]).

:- pred p(X) => atm(X).
p(X) :- X = a.
          @end{verbatim}

 If @code{fixp_stick_to_success} is set to @tt{on}, the analysis result will be:
         @begin{verbatim}
:- module(_,_,[assertions]).

:- true pred p(X) => atm(X).
p(X) :- X = a.
          @end{verbatim}

 Because the value of the assertion is used as it is.
If it is set to @tt{off}, it will use the assertion only when it allows to gain precision (useless in this case).
          @begin{verbatim}
:- module(_,_,[assertions,regtypes]).

:- true pred p(X) => rta(X).
p(X) :- X = a.

:- regtype rta/1.
rta(a).
          @end{verbatim}

    @item @code{fixp_stick_to_calls}: @bf{not implemented yet}, whether to use
    the value of the calls assertion instead of what was inferred by the
    fixpoint. This is harder than the success case since the heads of the
    analysis information may not be normalized.

For example in the following module:
                 @begin{verbatim}
:- module(_,_,[assertions]).

main :-
        p(a).

:- pred p(X) : atm(X).
p(X).
          @end{verbatim}

 Since the plai does not normalize heads it is imposible to generalize @tt{p(a)}
 to @tt{p(X) : atm(X)}, the variables that the abstract substitution
 approximates must be in the head. However @tt{p(X) : rta(X)} can be generalized
 only by changing the abstract substitution because the variable is already in
 the head.

The fixpoint would have to be modified so that
 applying assertions can change the goals

@item @code{use_check_as_trust}: To activate the runtime semantics of the check assertions, i.e., use them as trust in the fixpoint.
@end{itemize}

@begin{note}
Program point assertions are not processed here.
@end{note}
").

% TODO:
:- doc(bug, "Use full_info_to_asub, in order not to use assertions that a domain
	     does not understand, in the case of losing precision, otherwise it is not
 necessary.").

:- doc(bug, "Run-time checks for normalized terms could be very useful to debug.
A normalized head/term (f(A1,...,An) where A1,...An are distinct vars) could be
a native property. Then we could use it for rtchecks in this module.").

:- use_package(.(notrace)). % inhibits the tracing

:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [member/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9, assertion_body/7]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(ciaopp(p_unit/p_abs), [get_module_from_sg/2]).
:- use_module(ciaopp(p_unit/aux_filenames), [is_library/1]).
:- use_module(ciaopp(p_unit/itf_db), [current_itf/3]).

:- use_module(ciaopp(plai/fixpo_ops), [bottom/1, get_singleton/2]).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7]).
:- use_module(ciaopp(plai/apply_assertions_old),
	[apply_trusted0/7, apply_trusted_modular/6]).
:- use_module(ciaopp(plai/domains), [info_to_asub/6, info_to_asub/7,
	extend/6, project/6, exit_to_prime/8, compute_lub/3,
	identical_abstract/3, call_to_entry/9, glb/4,
	less_or_equal/3, unknown_call/4]).

:- use_module(ciaopp(plai/plai_errors), [invalid_trust_message/4]).

% -------------------------------------------------------------------
:- export(call_asr/5).
:- data call_asr/5.
% call_asr(SgKey, Sg, Status, AbsInt, Call).
% Status is the list of applicable status

:- export(success_asr/6).
:- data success_asr/6.
% success_asr(SgKey, Sg, Status, AbsInt, Call, Succ).

% TODO: review cleanup_applied_assertions, it is cleaned several times!!!
:- export(cleanup_applied_assertions/1).
:- doc(cleanup_applied_assertions/1, "Cleans the cached assertions").
cleanup_applied_assertions(AbsInt) :-
	retractall_fact(call_asr(_,_,_,AbsInt,_)),
	retractall_fact(success_asr(_,_,_,AbsInt,_,_)).

% -------------------------------------------------------------------
:- export(apply_assrt_call_to_success/8).
:- pred apply_assrt_call_to_success(+AbsInt,+Sg,+Sv,+Proj0,+HvFv_u,+Call,-NewProj,-NewCall)
        : (atm(AbsInt), list(Sv), list(HvFv_u)) + not_fails
    #"@var{NewProj} and @var{NewCall} are the result of applying
      the assertions that correspond to the @tt{call_to_success} analysis point.

      Currently, the implementation has only one option which is applying
      @tt{true} and @tt{trust} call assertions, and @tt{true} success assertions
(that are applicable to @var{Sg}:@var{Proj}).".
apply_assrt_call_to_success(_,_,_,'$bottom',_,_,'$bottom','$bottom') :- !.
apply_assrt_call_to_success(AbsInt,Sg,Sv,Proj0,HvFv_u,Call,NewProj,NewCall) :-
	current_pp_flag(old_trusts, off),
  assertions_for_sg(calls,Sg), !, % avoid unnecessary normalization
  fixpoint_trace('trust',call_to_success,_,_,Sg,Proj0,_),
  abs_normalize(AbsInt,Sg,Sv,Proj0,Head,Hv,NormProj,ExtraInfo),
  get_applicable_status(Head, call, Sts),
  predkey_from_sg(Head, SgKey),
	glb_calls(Sts,SgKey,AbsInt,Head,NormProj,NProj,AppliedF),
  ( var(AppliedF) -> % no assertions applied
      NewProj=Proj0, NewCall=Call
  ;
      invalid_trust_message(calls,NProj,Head:NormProj,Sg),
      ( NProj = '$bottom' ->
          NewProj = ['$bottom'],
          NewCall = ['$bottom']
      ;
          exit_to_prime(AbsInt,Sg,Hv,Head,Sv,NProj,ExtraInfo,Prime),
          % Extend the results to all the variables in the clause (Call)
          extend(AbsInt,Sg,Prime,Sv,Call,NewCall),
          project(AbsInt,Sg,Sv,HvFv_u,NewCall,NewProj)
      ),
      fixpoint_trace('applied trust',call_to_success,_,_,Sg,Proj0,_)
  ).
apply_assrt_call_to_success(_,_,_,Proj,_,Call,Proj,Call).

:- export(apply_assrt_exit/7).
:- pred apply_assrt_exit(+AbsInt,+Sg,+Sv,+Proj0,+LPrime,-NLPrime,?Applied)
        : ( atm(AbsInt), list(Sv), list(LPrime) ) => list(NLPrime).
apply_assrt_exit(_,_,_,_,['$bottom'],['$bottom'],no) :- !.
% if no assertions, do nothing
apply_assrt_exit(_,Sg,_,_,LPrime,LPrime,no) :-
        \+ assertions_for_sg(success,Sg), !.
% apply assertions losing precision
apply_assrt_exit(AbsInt,Sg,Sv,Proj0,LPrime,NLPrime,yes) :-
	current_pp_flag(old_trusts,off),
	current_pp_flag(multi_success,off),
	current_pp_flag(fixp_stick_to_success, on), !,
  fixpoint_trace('trust',exit,_,_,Sg,Proj0,_),
	abs_normalize(AbsInt,Sg,Sv,Proj0,Head,Hv,NProj,ExtraInfo),
  get_applicable_status(Head, success, Sts),
  predkey_from_sg(Sg,SgKey),
	( get_succ_assertion_asubs(SgKey,Head,Hv,Sts,AbsInt,NProj,Exit) ->
      exit_to_prime(AbsInt,Sg,Hv,Head,Sv,Exit,ExtraInfo,NPrime),
      invalid_trust_message(success,NPrime,Sg:LPrime,Sg),
	    get_singleton(NPrime,NLPrime),
      fixpoint_trace('applied trust',exit,_,_,Sg,NLPrime,_)
	;
        NLPrime = LPrime
  ).
% apply assertions gaining precision
apply_assrt_exit(AbsInt,Sg,Sv,Proj0,LPrime,NLPrime,AppliedF) :-
	current_pp_flag(multi_success,off),
 	current_pp_flag(old_trusts,off), !,
	get_singleton(Prime,LPrime),
	fixpoint_trace('trust',exit,_,_,Sg,Proj0,_),
 	abs_normalize(AbsInt,Sg,Sv,Proj0,Head,Hv,NormProj,_),
 	abs_normalize(AbsInt,Sg,Sv,Prime,Head,Hv,NormPrime,ExtraInfo),
  get_applicable_status(Head, success, Sts),
  predkey_from_sg(Sg,SgKey),
 	glb_successes(SgKey,Sts,NormProj,Head,Hv,AbsInt,NormPrime,TExit,AppliedF0),
	( var(AppliedF0) ->
      NLPrime = LPrime,
      AppliedF = no
	;
        % TODO: doc why this is done
        exit_to_prime(AbsInt,Sg,Hv,Head,Sv,TExit,ExtraInfo,NPrime),
        invalid_trust_message(success,NPrime,Sg:LPrime,Sg),
        get_singleton(NPrime,NLPrime),
        AppliedF = yes,
        fixpoint_trace('applied trust',exit,_,_,Sg,NLPrime,_)
	).
apply_assrt_exit(_,_,_,_,Prime,Prime,no).

:- export(apply_assrt_no_source/6).
:- pred apply_assrt_no_source(+SgKey,+AbsInt,+Sg,+Sv,+Proj,-Prime)
        : (atm(SgKey), atm(AbsInt), list(Sv)) => nonvar(Prime)
        #"Succeeds if there are applicable assertions to @var{Sg:Proj}
         understood by domain @var{AbsInt} and @var{Prime} is the answer
pattern.".
apply_assrt_no_source(_,_,_,_,'$bottom','$bottom') :- !.
apply_assrt_no_source(SgKey,AbsInt,Sg,Sv,Proj,Prime) :-
	current_pp_flag(old_trusts, off), !,
  fixpoint_trace('trust',no_source,_,_,Sg,Proj,_),
	% get modular information
	predkey_from_sg(Sg,SgKey),
  ( apply_trusted_modular(Proj,SgKey,Sg,Sv,AbsInt,Prime) ->
      true
	;
        abs_normalize(AbsInt,Sg,Sv,Proj,Head,Hv,NProj,ExtraInfo),
        get_applicable_status(Head, success, Sts),
        ( get_succ_assertion_asubs(SgKey,Head,Hv,Sts,AbsInt,NProj,TExit) ->
	          true
        ;   % do topmost abstraction if no assertions are available
            unknown_call(AbsInt,Hv,NProj,TExit)
        ),
        exit_to_prime(AbsInt,Sg,Hv,Head,Sv,TExit,ExtraInfo,Prime)
	).
apply_assrt_no_source(SgKey,AbsInt,Sg,Sv,Proj,Prime) :-
	apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,_,Prime), !.

% --------------------------------------------------
:- pred glb_calls(+Sts,+SgKey,+AbsInt,+Head,+Proj,-NewProj,-AppliedF)
        : (atm(AbsInt), list(Sts), atm(SgKey)) => nonvar(NewProj)
	#"Applies the trusted calls of normalized @var{Head} with call
         pattern @var{Proj} to produce @var{NewProj}. If some
         assertion was applied flag @var{AppliedF} is set to @code{yes}.".
glb_calls(Sts,SgKey,AbsInt,Head,Proj,NewProj,yes) :-
        get_call_assertions_asub(Head,SgKey,Sts,AbsInt,AProj), !,
        glb(AbsInt,Proj,AProj,NewProj).
glb_calls(_,_,_,_,Proj,Proj,_).

:- export(get_call_assertions_asub/5).
:- pred get_call_assertions_asub(+Head,SgKey,Sts, AbsInt, -AsrProj)
        : (list(Sts), atm(SgKey), atm(AbsInt)) => nonvar(AsrProj).
get_call_assertions_asub(Head,SgKey,Sts, AbsInt, AsrProj) :-
        findall(call_asr(Head,A), call_asr(SgKey,Head,Sts,AbsInt,A), As),
        \+ As = [], !,
        compute_lub_assrts(As,AbsInt,Head,AsrProj).
get_call_assertions_asub(Head,SgKey,Sts, AbsInt, A) :-
        findall(Body, (assertion_read(Head,_,S,calls,Body,_,_,_,_), member(S,Sts)), As),
        \+ As = [], % fail if there are no assertions
        gather_calls_assertions(As,SgKey,Head,Sts,AbsInt,AsrProjs),
        compute_lub(AbsInt,AsrProjs,A).

compute_lub_assrts([],_,_,'$bottom').
compute_lub_assrts([call_asr(Head,A)|As],AbsInt,Head,AsrProj) :-
        compute_lub_assrts(As,AbsInt,Head,AsrProj0),
        compute_lub(AbsInt,[A,AsrProj0],AsrProj).

gather_calls_assertions([Body],SgKey,Head,Sts,AbsInt,[AsrProj]) :- !,
        abstract_calls_assertion(Body,SgKey,Head,Sts,AbsInt,AsrProj).
gather_calls_assertions([B|Bs],SgKey,Head,Sts,AbsInt,[AsrProj|APs]) :-
        abstract_calls_assertion(B,SgKey,Head,Sts,AbsInt,AsrProj),
        gather_calls_assertions(Bs,SgKey,Head,Sts,AbsInt,APs).

abstract_calls_assertion(Body,SgKey,Head,Sts,AbsInt,AsrProj) :-
        assertion_body(Head,_Compat,InfoCall,_Succ,_Comp,_Comm,Body),
        varset(Head, Hv),
        info_to_asub(AbsInt,_Kind,InfoCall,Hv,AsrProj,Head),
        assertz_fact(call_asr(SgKey, Head, Sts, AbsInt, AsrProj)).

glb_successes(SgKey,Status,Proj,Head,Hv,AbsInt,Prime0,NewPrime,yes) :-
        get_succ_assertion_asubs(SgKey,Head, Hv, Status, AbsInt, Proj,AsrPrime), !,
        glb(AbsInt, Prime0, AsrPrime, NewPrime).
glb_successes(_,_,_,_,_,_,Prime,Prime,_).

:- export(get_succ_assertion_asubs/7). % for inc assertions
:- pred get_succ_assertion_asubs(+SgKey,+Head,+Hv,+Sts,+AbsInt,+Proj,-Prime)
        : (atm(SgKey), list(Hv), list(Sts), atm(AbsInt)) => nonvar(Prime)
	#"This predicate succeeds if there are assertions that are
          applicable to @var{Head}:@var{Proj} (normalized). If no @var{Sts} is
          specified all trusted status are returned".
% Head:Proj is already normalized
get_succ_assertion_asubs(SgKey,Head,_Hv,Sts,AbsInt,Proj,AsrPrime) :-
        success_asr(SgKey, Head, Sts, AbsInt, AsrProj, AsrPrime),
        identical_abstract(AbsInt, Proj, AsrProj), !.
get_succ_assertion_asubs(SgKey,Head,Hv,Sts,AbsInt,Proj,AsrPrime) :-
	( % enumerate all read assrt and gather conditions
    assertion_read(Head,_M,St,success,Body,_Dict,_Src,_LB,_LE),
      member(St, Sts),
      assertion_body(Head,_Compat,InfoCall,InfoSucc,_Comp,_Comm,Body),
	    info_to_asub(AbsInt,_Kind,InfoCall,Hv,AsrProj,Head),
	    less_or_equal(AbsInt, Proj, AsrProj),
	    info_to_asub(AbsInt,_Kind,InfoSucc,Hv,Prime,Head),
	    predkey_from_sg(Head, SgKey),
	    add_success_asr(SgKey, Head, Sts, AbsInt, Proj, Prime),
	    fail
	;
        success_asr(SgKey, Head, Sts, AbsInt, AsrProj, AsrPrime),
        identical_abstract(AbsInt, Proj, AsrProj), !
	).

% Accumulate in one predicate
:- export(add_success_asr/6). % exported for apply_assertions_inc
:- pred add_success_asr(+SgKey,+Head, +Sts, +AbsInt, +AsrProj, +AsrPrime)
        : (atm(SgKey), list(Sts), atm(AbsInt)) + not_fails
        #"Joins an abstract success pattern from an assertion with a previous
         value for the call pattern @var{Head}:@var{AsrProj}.".
add_success_asr(SgKey, Head, Sts, AbsInt, AsrProj, AsrPrime) :-
        current_fact(success_asr(SgKey, Head, Sts, AbsInt, Proj0, Prime0), Ref),
        identical_abstract(AbsInt, Proj0, AsrProj), !,
        glb(AbsInt, AsrPrime, Prime0, NewPrime),
        erase(Ref),
        assertz_fact(success_asr(SgKey, Head, Sts, AbsInt, Proj0, NewPrime)).
add_success_asr(SgKey, Head, Sts, AbsInt, AsrProj, AsrPrime) :-
        assertz_fact(success_asr(SgKey, Head, Sts, AbsInt, AsrProj, AsrPrime)).

% TODO: move to domains?
:- export(abs_normalize/8).
:- pred abs_normalize(+AbsInt,+Sg,+Sv,+ASub0,?Head,?Hv,-ASub,-ExtraInfo)
        : (atm(AbsInt), list(Sv)) => nonvar(ASub) + not_fails.
% "abstract unification/normalization"
%    e.g., (p(a), [],[]) ---> (p(X), [], [X/g])
abs_normalize(_AbsInt,Sg,_Sv,'$bottom',Head,Hv,'$bottom',_) :- !,
	functor(Sg,F,A),
	functor(Head,F,A),
  varset(Head, Hv).
abs_normalize(AbsInt,Sg,Sv,ASub0,Head,Hv,ASub,ExtraInfo) :-
	functor(Sg,F,A),
	functor(Head,F,A),
  varset(Head, Hv),
  % variant case already optimized in call_to_entry (using copy_term)
  call_to_entry(AbsInt,Sv,Sg,Hv,Head,[],ASub0,TmpCall,ExtraInfo),
  project(AbsInt,Head,Hv,Hv,TmpCall,ASub), !. % TODO: Is this necessary?

:- export(get_applicable_status/3).
get_applicable_status(Head,Type,Sts) :-
        findall(Status, applicable_status(Head,Type,Status), Sts).

applicable_status(_, _, true). % TODO: reconsider allowing this for analysis
applicable_status(_, _, checked). % TODO: reconsider allowing this
applicable_status(_, _, trust).
applicable_status(_, _, check) :-
	current_pp_flag(use_check_as_trust,on), !.
applicable_status(Sg, _, check) :-
	current_pp_flag(use_check_assrt,on),
	type_of_goal(imported,Sg), !.
applicable_status(Sg, _, check) :-
	current_pp_flag(use_check_assrt,libraries),
	type_of_goal(imported,Sg), % choicepoints
	get_module_from_sg(Sg,Module),
	current_itf(defines_module,Module,Base), !, % choicepoints
	is_library(Base).

% Check if there are assertions for a head
assertions_for_sg(AssrType, Sg) :-
        functor(Sg, F, A),
        functor(Head, F, A),
        get_applicable_status(Sg,AssrType,Sts),
        assertion_read(Head,_,St,AssrType,_,_,_,_,_),
        member(St,Sts), !.
