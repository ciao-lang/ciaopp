:- module(tr_ctrt, [], [doccomments, assertions, regtypes, datafacts]).

%! \title CTRT transformation
%  \subtitle Feed analysis with _check_ assertions
%  \author Jose F. Morales

%! \module 
%    This is a program transformation that enables the use of _check_
%    assertions during analysis (not as a separate step in ctchecks).
%
%    This transformation preserves the program behavior when rtchecks
%    (run-time checks of _check_ assertions) are enabled during
%    execution and may improve the precision and cost of the analysis.
%
%    The transformation modifies all predicates with check
%    assertions. The original predicate is renamed (called _inner_)
%    and replaced by a single clause wrapper predicate (called _link_
%    clause), which calls the inner predicate.
%
%    During analysis the link clause is ignored so that no new call
%    patters are added to inner (this is implemented with a call to an
%    unknown `impl_defined` predicate).
%
%    Assertions are copied for both the link and inner predicate,
%    including their status, marking as `trust` the following (see
%    `link_assrt/3` and `inner_assrt/4`):
%
%     - success assertions in link pred
%     - calls assertions in inner pred
%
%    That is, given a predicate and assertions:
%
%    ```ciao
%    :- calls HEAD : PRE.
%    :- success HEAD : PRE => POST.
%    HEAD :- BODY.
%    ```
%
%    The analysis produces:
%
%    ```ciao
%    % (the link clause)
%    :- calls HEAD : PRE.
%    :- trust success HEAD : PRE => POST.
%    HEAD :- '$ctrt_nocall'(HEAD_). % (trick)
%      
%    % (the inner predicate)
%    :- entry HEAD_(X,Y) : PRE.
%    :- calls HEAD_(X,Y) : PRE.
%    :- success HEAD_(X,Y) : PRE => POST.
%    HEAD_(X,Y) :- BODY.
%    ```
%
%    *Lemma*: If rtchecks are enabled this transformation is correct.
%
%    *Proof*: It is not possible that the execution reaches the
%    inner predicate with a wrong call pattern if rtchecks are
%    enabled, thus we can trust calls in inner. In the same way, it is
%    not possible that the execution exits (without errors) the inner
%    pred, so we can trust success in link.
%
%    **NOTES**:
%     - The output needs some postprocessing to be executed (removal of
%       $ctrt_nocall/1)
%     - Analysis may lose precision. This can be detected if the analysis
%       infers more precise information for the trust assertions above.
%       This should be notified to the user.
%     - We mark some assertions after the transformation as `true`, not
%       `trust`. Reminder of `trust` vs `true` assertions:
%        - `true` means that the assertion has been proved (either
%          automatically with some analysis or externally -- although
%          it is not implemented the design accepts some associated
%          info about the domain or the proof)
%        - `trust` are assumed in the analysis **without** a proof
%          (so rtchecks must be added)
%       At least in the current implementation of the analysis,
%       replacing `check` by `trust` does not have the same effect as
%       the ctrt transformation.
%
%    # Examples of use
%
%    ```ciao
%    ?- module(rtenh), transform(ctrt), analyze(shfr), analyze(eterms), acheck, output.
%    ```

:- doc(bug, "The transformation is not able to add trivial
   entries/calls if they were not in the program! (see wff in
   boyerf.pl code)").

:- doc(bug, "Study with more detail if replacing check by trust
   assertions produces a similar effect than this transformation.").

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- use_module(ciaopp(p_unit), [replace_program/2]).
:- use_module(ciaopp(tr_syntax/tr_syntax), [traverse_clauses/5]).
%:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(p_unit/program_keys),
	[ clause_key/2, rewrite_source_clause/3
%	  inverse_rewrite_source_program/2
	]).
:- use_module(ciaopp(p_unit), [add_directive/1]).
:- use_module(ciaopp(p_unit/clause_db), [maybe_clause_locator/2, add_clause_locator/2]).
:- use_module(library(vndict), [create_pretty_dict/2]). 
:- use_module(ciaopp(p_unit/assrt_db), [
	assertion_body/7,
	assertion_read/9,
	add_assertion_read/9,
	pgm_assertion_read/9]).
:- use_module(library(lists), [member/2]).
:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(engine(internals), [module_concat/3]).

:- push_prolog_flag(multi_arity_warnings, off).

:- data seen_pred/2.
:- data nocall_added/1.

cleanup_ctrt :-
	retractall_fact(seen_pred(_,_)),
	retractall_fact(nocall_added(_)).

:- multifile transformation/4.
transformation(ctrt,Cls,Ds,_Info) :-
	cleanup_ctrt, % (just in case...)
	% % take all keys out
	% inverse_rewrite_source_program(Cls0,Cls1),
	% Rewrite clauses
	rewrite_clauses(Cls, Ds, NewCls, NewDs),
	replace_program(NewCls, NewDs),
	cleanup_ctrt.

:- multifile transformation/1.
transformation(ctrt).

:- pop_prolog_flag(multi_arity_warnings).

% Add wrappers
rewrite_clauses([], [], [], []).
rewrite_clauses([clause(H,B):Key|Cs0], [D|Ds0], Cs, Ds) :-
	functor(H, N, A),
	pred_needs_wrapper(N, A),
	!,
	( maybe_clause_locator(Key, Loc) -> true ; throw(no_locator(Key)) ),
	% Assertions and link clause (only first time)
	( seen_pred(N, A) ->
	    Cs = Cs1,
	    Ds = Ds1
	; assertz_fact(seen_pred(N, A)),
	  rewrite_assertions(N, A),
	  % TODO: Add impl_defined link for analysis and recover it later!
	  add_link_clause(N, A, Loc, Cs, Cs1, Ds, Ds1)
	),
	% Renamed as inner clauses
	add_inner_clause(H, B, D, Loc, Cs1, Cs2, Ds1, Ds2),
	%
	rewrite_clauses(Cs0, Ds0, Cs2, Ds2).
rewrite_clauses([C|Cs0], [D|Ds0], [C|Cs], [D|Ds]) :-
	rewrite_clauses(Cs0, Ds0, Cs, Ds).

:- use_module(ciaopp(p_unit/itf_base_db), [defines/3, impl_defines/2]).

:- use_module(ciaopp(p_unit/clause_db), [source_clause/3]).

% % TODO: Adding impl_defined of the predicate does not work: assertions are not written
% add_link_clause(N, A, Loc, Cs, Cs1, Ds, Ds1) :-
% 	% 
% 	( current_fact(itf_base_db:defines(N,A,_)) ->
% 	    add_impl_defined(N, A, Loc)
% 	; throw(not_defined(N,A))
% 	),
% 	Cs = Cs1,
% 	Ds = Ds1.
%
add_link_clause(N, A, Loc, Cs, Cs1, Ds, Ds1) :-
	% Ensure that '$ctrt_nocall'/1 is defined
	( nocall_added(NoCall) ->
	    true
	; module_split(N, M, _),
	  module_concat(M,'$ctrt_nocall',NoCall),
	  add_impl_defined(NoCall, 1, Loc),
	  assertz_fact(nocall_added(NoCall))
	),
	% Link clause
	get_link(N, A, Hlink, Blink),
	goal_module_split(Blink, _, Blink0),
	Blink2 =.. [NoCall,Blink0], % 'M:$ctrt_nocall'(Blink0)
	clause_key(Hlink, KeyLink), % create new key and copy locator
	add_clause_locator(KeyLink, Loc),
	rewrite_source_clause(clause(Hlink,Blink2),KeyLink,Clink), % add keys to atoms
	Cs = [Clink:KeyLink|Cs1],
	create_pretty_dict(Clink,Dlink),
	Ds = [Dlink|Ds1].

add_inner_clause(H, B, D, Loc, Cs1, Cs2, Ds1, Ds2) :-
	% make sure it is defined
	get_inner(H, Hinner),
	functor(Hinner, N, A),
	ensure_defined(N, A),
	clause_key(Hinner, KeyInner), % create new key and copy locator
	add_clause_locator(KeyInner, Loc),
	Cinner = clause(Hinner, B), % TODO: rewrite keys using KeyInner? (use inverse_rewrite_source_body/2)
	Cs1 = [Cinner:KeyInner|Cs2],
	Ds1 = [D|Ds2].

% (ctchecks looks at defined predicates)
ensure_defined(N, A) :-
	module_split(N, M, _),
	( current_fact(itf_base_db:defines(N,A,M)) ->
	    true
	; assertz_fact(itf_base_db:defines(N,A,M))
	).

% N/A needs a wrapper if it has any check calls or success assertion
pred_needs_wrapper(N, A) :-
	functor(Goal, N, A),
	assertion_read(Goal,_M,Status,Type,_Body,_Dict,_Source,_LB,_LE),
	Status = check,
	( Type = calls ; Type = success ),
	!.

:- use_module(library(aggregates), [findall/3]).

% (See transformation example above for details)
rewrite_assertions(N, A) :-
	functor(Goal, N, A),
	% Get all assertions
	findall(a(Goal,M,Status,Type,Body,Dict,Source,LB,LE),
	        retract_fact(pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)),
		As),
	% Assert them back
	( member(Asrt, As),
	    rewrite_assertion(Asrt),
	    fail
	; true
	).

rewrite_assertion(a(Goal,M,Status,Type,Body,Dict,Source,LB,LE)) :-
	assertion_body(Goal,Compat,Call,Succ,Comp,Comm,Body),
	get_inner(Goal, NewGoal),
	assertion_body(NewGoal,Compat,Call,Succ,Comp,Comm,NewBody),
	( link_assrt(Status, Type, Status2),
	    add_assertion_read(Goal,M,Status2,Type,Body,Dict,Source,LB,LE),
	    fail
	; true
	),
	( inner_assrt(Status, Type, Status2, Type2),
	    add_assertion_read(NewGoal,M,Status2,Type2,NewBody,Dict,Source,LB,LE),
	    fail
	; true
	).

% Trust success in link clause
link_assrt(check, success, Status) :- !, Status = true.
link_assrt(Status, _Type, Status).

% Trust calls in inner clause
inner_assrt(check, calls, Status, Type) :- !,
	( Status = check, Type = entry
	; Status = check, Type = calls
	).
% TODO: using 'trust' (to use more precise info if available) does not work as expected
%inner_assrt(check, calls, Status, Type) :- !,
%	Status = trust, Type = calls.
inner_assrt(_, entry, _Status, _Type) :- !, fail. % omit user 'entry' in inner
inner_assrt(Status, Type, Status, Type).

% ---------------------------------------------------------------------------
% Wrapper predicates
%
%   (H :- B) ==> (Hlink :- Blink), (Hinner :- B)

% Obtain Hlink and Blink
get_link(N, A, Hlink, Blink) :-
	inner_name(N, Ninner),
	functor(Hlink, N, A),
	Hlink =.. [_|Vs],
	Blink =.. [Ninner|Vs].

% Obtain Hinner
get_inner(H, Hinner) :-
	% get renamed head
	functor(H, N, _A),
	H =.. [_|As],
	inner_name(N, Ninner),
	Hinner =.. [Ninner|As].

inner_name(N, Ninner) :-
	atom_concat(N, '/i', Ninner).

% ---------------------------------------------------------------------------

% Add a impl_defined
% TODO: move to other module
add_impl_defined(MN, A, _Loc) :-
	module_split(MN, M, N),
	functor(Goal, MN, A),
	assertz_fact(itf_base_db:impl_defines(Goal,M)),
	add_directive(impl_defined([N/A])).

% ---------------------------------------------------------------------------

% TODO: duplicated?
goal_module_split(MG, M, G) :-
	MG =.. [MN|As],
	module_split(MN, M, N),
	G =.. [N|As].

