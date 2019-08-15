:- module(apply_assertions_old,
    [apply_trusted/7, apply_trusted0/7, apply_trusted_each/7, cleanup_trusts/1],
     [assertions, isomodes, datafacts]).

:- use_module(library(lists), [append/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(messages), [warning_message/3,warning_message/2]).

:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9, assertion_body/7]).
:- use_module(ciaopp(p_unit/clause_db), [maybe_clause_locator/2]).
:- use_module(ciaopp(p_unit), [type_of_goal/2, dynamic_or_unknown_predicate/1,
	                       get_call_from_call_assrt/7]).
:- use_module(ciaopp(plai/domains), 
	[ abs_sort/3, asub_to_native/6,
	  compute_lub/3, glb/4, less_or_equal/3, unknown_call/4,
	  call_to_entry/9, full_info_to_asub/5, info_to_asub/6, info_to_asub/7,
	  contains_parameters/2, unknown_entry/3,
	  extend/6, project/6, exit_to_prime/8, identical_abstract/3]).
:- use_module(typeslib(typeslib), [set_param_matching_mode/1]).

:- use_module(ciaopp(plai/intermod_success), [get_success_info/7]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2, current_itf/3]).
:- use_module(ciaopp(p_unit/aux_filenames), [get_loaded_module_name/3]).
:- use_module(ciaopp(p_unit/p_abs), [module_is_processable/1, get_module_from_sg/2]).
:- use_module(ciaopp(p_unit/aux_filenames), [is_library/1]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

%-----------------------------------------------------------------------------

%% :- doc(bug,"1. We now get the FIRST trust which is applicable 
%% 	- to do better, 
%% 	we should get the best approximation of those applicable. Done.").
:- doc(bug,"2. Check that trusts are ok for recursive predicates!").
:- doc(bug,"3. Check that top trusts (i.e., empty InfoSucc) are treated 
	correctly.").
:- doc(bug,"4. Treating downwards closed info via unknown_call can be very 
	inefficient").
:- doc(bug,"5. The second case of complementation is not implemented yet.").
:- doc(bug,"6. The second case of use might be incorrect if not all
	trusts are applicable in the analysis domain.").
:- doc(bug,"7. The question of normalized goal patterns in assertions needs
	be sorted out!.").
:- doc(bug,"8. When an imported goal is a prop, its code should be
	analyzed."). % done in modular analysis??
:- doc(bug,"9. When AbsInt is a computational domain (det, nf), comp
	assertions should also be used.").
% bug#9 is now solved, but the check for AbsInt should be generalized!

%-----------------------------------------------------------------------------

:- pred cleanup_trusts(AbsInt) :: atm(AbsInt) 
	# "Cleans up trust handling internal information.".
cleanup_trusts(AbsInt):-
	retractall_fact(cached_trust(AbsInt,_)),
	retractall_fact(trust(_SgKey,_,_,AbsInt,_,_)),
	retractall_fact(approx(_SgKey,_,AbsInt,_)).

%-----------------------------------------------------------------------------

:- pred apply_trusted(+Proj,+SgKey,+Sg,+Sv,+AbsInt,+Prime0,-Prime) 
# "@var{Prime} is the success substitution for @var{Proj} call
  substitution of @var{Sg} goal, when analysis results @var{Prime0}
  are available. @var{Prime} is the glb of the inferred success
  substitution @var{Prime0} and the composition (glb) of the success
  substitucions defined by the applicable trust assertions.

  If the trust information is incompatible with the inferred
  substitution, a warning message is raised.".

% Having analysis info
apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime0,Prime):-
	trusted(SgKey,Proj,Sg,Sv,AbsInt,Loc,Prime1),
	apply_glb_inferred(AbsInt,Sg,Sv,Loc,Prime0,abs,Prime1,Prime).

%-----------------------------------------------------------------------------

:- pred apply_trusted0(+Proj,+SgKey,+Sg,+Sv,+AbsInt,+ClId,-Prime)
# "@var{Prime} is the success substitution for @var{Proj} call
  substitution of @var{Sg} goal, when analysis results are not
  available. @var{Prime} is the glb of the topmost substitution of
  @var{Sg} and the composition (glb) of the success substitucions
  defined by the applicable trust assertions. @var{ClId} is the goal
  location in the program code.".

% Not having analysis info
apply_trusted0('$bottom',_SgKey,_Sg,_Sv,_AbsInt,_ClId,Prime):- !,
	Prime = '$bottom'.
%%jcf-07.04.2005-begin
apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,_ClId,Prime):-
	apply_trusted_modular(Proj,SgKey,Sg,Sv,AbsInt,Prime), !.
% apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,_ClId,Prime):-
% 	( type_of_goal(impl_defines,Sg)
% 	; type_of_goal(multifile,Sg) 
% 	; type_of_goal(dynamic,Sg) ), 
% 	!,
% 	unknown_call(AbsInt,Sv,Proj,Prime0),
% 	%% Applying trust info if there is any.
% 	( 
% 	    apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime0,Prime) ->
% 	    true
% 	; 
% 	    Prime = Prime0
% 	).
%%jcf-07.04.2005-end
apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,_ClId,Prime):-
	trusted(SgKey,Proj,Sg,Sv,AbsInt,Loc,Prime1), !,
	unknown_call(AbsInt,Sv,Proj,Prime0),
	apply_glb_inferred(AbsInt,Sg,Sv,Loc,Prime0,unk,Prime1,Prime).
apply_trusted0(Proj,_SgKey,Sg,Sv,AbsInt,ClId,Prime):-
  dynamic_or_unknown_predicate(Sg),
	( functor(Sg,_,0) ->
	    Prime = Proj
	 ; 
	    ( current_pp_flag(verbosity,very_high) ->
		maybe_clause_locator(ClId,Loc),
		asub_to_native(AbsInt,Proj,Sv,no,Output,_Comp),
		warning_message(Loc,"Cannot analyze one version of ~w
 i.e., there is no trust for call pattern:~n   ~q",[Sg,Output])
	    ;
		true
	    ),
	    unknown_call(AbsInt,Sv,Proj,Prime)
	).

:- export(apply_trusted_modular/6).
apply_trusted_modular(Proj,SgKey,Sg,Sv,AbsInt,Prime) :-
	\+ current_pp_flag(intermod,off),
	type_of_goal(imported,Sg),
	current_itf(imports,Sg,IM), atom(IM), % IG: leaving unnecesary choicepoints?
	get_loaded_module_name(IM,AbsoluteName,AbsBase),
	\+ itf_db:curr_file(AbsoluteName,_), %% If imported module has been loaded,it must be analyzed.
	!,
	%% Obtaining success information.
	( get_success_info(Proj,SgKey,Sg,Sv,AbsInt,Prime0,PatternsApplied) ->
	    true
	;
	    unknown_call(AbsInt,Sv,Proj,Prime0),
	    PatternsApplied = no
	),
	%% Applying trust info if there is any.
	( apply_trusted(Proj,SgKey,Sg,Sv,AbsInt,Prime0,Prime) ->
	    true
	;
	    Prime = Prime0,
	    ( current_pp_flag(verbosity,very_high) ->
		( PatternsApplied == no, \+ module_is_processable(AbsBase) ->
		    asub_to_native(AbsInt,Proj,Sv,no,Output,_Comp),
		    warning_message("In ~q ~n there is no trust for call pattern:~n   ~q
~n Assumed success substitution:~n    ~q",[Sg,Output,Prime])
	        ;  true
		)
	    ;   true
	    )
	).

%-----------------------------------------------------------------------------

:- pred apply_trusted_each(+Proj,+SgKey,+Sg,+Sv,+AbsInt,+ListPrime,-LPrime)
# "@var{LPrime} is the list of success substitutions for @var{Proj}
  call substitution of @var{Sg} goal, when the list of analysis
  results @var{ListPrime} is available. Every element of the list
  @var{LPrime} is the glb of the corresponding element of the inferred
  success substitution list @var{ListPrime} and the composition (glb)
  of the success substitutions defined by the applicable trust
  assertions.

  If the trust information is incompatible with the inferred
  substitution, a warning message is raised.".

% Having analysis info
apply_trusted_each(Proj,SgKey,Sg,Sv,AbsInt,ListPrime,LPrime):-
	trusted(SgKey,Proj,Sg,Sv,AbsInt,Loc,Prime), !,
	replace_each_trusted(ListPrime,AbsInt,Sg,Sv,Loc,Prime,LPrime).
apply_trusted_each(_Proj,_SgKey,_Sg,_Sv,_AbsInt,ListPrime,ListPrime).

replace_each_trusted([Prime0|ListPrime0],AbsInt,Sg,Sv,Loc,Prime1,
	             [Prime|ListPrime]):-
	apply_glb_inferred(AbsInt,Sg,Sv,Loc,Prime0,abs,Prime1,Prime),
	replace_each_trusted(ListPrime0,AbsInt,Sg,Sv,Loc,Prime1,ListPrime).
replace_each_trusted([],_AbsInt,_Sg,_Sv,_Loc,_Prime1,[]).

%-----------------------------------------------------------------------------

:- pred apply_glb_inferred(+AbsInt,+Sg,+Sv,+Loc,+Prime0,+Switch,+Prime1,-Prime) 
	#"@var{Prime} is the result of applying the glb operation to abstract
          substitutions @var{Prime0} and @var{Prime1} corresponding to call
          @var{Sg} with @var{Sv} set of variables. @var{Loc} is the call program
          point location.".
apply_glb_inferred(AbsInt,Sg,Sv,Loc,Prime0,Switch,Prime1,Prime):-
	glb(AbsInt,Prime1,Prime0,Prime2), !,
	( Prime2='$bottom', Prime1\=='$bottom', Prime0\=='$bottom',
	  Switch=abs -> 
	  asub_to_native(AbsInt,Prime0,Sv,no,Output0,_Comp0),
	  asub_to_native(AbsInt,Prime1,Sv,no,Output1,_Comp1),
	  warning_message(Loc,
	  "invalid trust for ~w:~n   ~w~n analysis infers:~n   ~w",
	  [Sg,Output1,Output0]),
	  Prime=Prime0
	; Prime=Prime2
	).
%% apply_glb_inferred(_AbsInt,_SgKey,Loc,Prime,Prime1,Prime):-
%% 	error_message(Loc,"no glb for ~q and ~q",[Prime1,Prime]).

trusted_assertion_status(trust).
trusted_assertion_status(check) :-
	% type_of_goal(imported,Sg)
	% [IG] according to the flag, the previous line shold be uncommented
	\+ current_pp_flag(use_check_assrt,off).
trusted_assertion_status(true).
trusted_assertion_status(checked).

%-----------------------------------------------------------------------------
% trusted(+,+,+,+,+,-)
% trusted(SgKey,Proj,Sg,Sv,AbsInt,Prime)
% Gets the Succ information given by the user (which we "trust") which is
% applicable to Sg and Proj. If there is none, it fails
%-----------------------------------------------------------------------------

:- data cached_trust/2.
:- data the_trusts/4.
:- data trust/6.
:- data approx/4.

trusted(SgKey,Proj,Sg,Sv,AbsInt,Loc,Prime):-
	look_trust(AbsInt,SgKey,Sg,Sv,Proj,Loc,Prime), !.
trusted(SgKey,_Proj,_Sg,_Sv,AbsInt,_Loc,_Prime):-
	current_fact(cached_trust(AbsInt,SgKey)), !,
	fail.
trusted(SgKey,_Proj,Sg0,_Sv,AbsInt,_Loc,_Prime):-
         assertz_fact(cached_trust(AbsInt,SgKey)),
         functor(Sg0,F,A),
         functor(Sg,F,A),
	 trusted_assertion_status(Status),
         varset(Sg,Sv),
	 (
	     (AbsInt = res_plai;AbsInt = res_plai_stprf;AbsInt = sized_types),
	      assertion_read(Sg,_,Status,comp,BodyC,_,Source,_,_),
	      assertion_body(Sg,_,IC,_,IComp,_,BodyC),
	      (
		  % ULQ: The following assertion_body in 'then' can fail
		  % for multiple trust assertions (calling patterns) for
		  % same Sg, since the preceding assertion_read for
		  % 'success' doesn't necessarily link to 'comp'
		  % assertion_read before.  Moved assertion_body/7
		  % literal from 'then' part to 'if' to fix the
		  % bug. Better solution is the linking assertions with
		  % same call pattern with unique assertion id.
		  %
		  % assertion_read(Sg,_,Status,success,BodyS,_,_Source,LB,LE)->
		  % assertion_body(Sg,Ip,IC,ISuccS,_,Cm,BodyS); Ip =
		  % [],ISuccS=[],Cm=[]
		  ( assertion_read(Sg,_,Status,success,BodyS,_,_Source,LB,LE),
		    assertion_body(Sg,Ip,IC,ISuccS,_,Cm,BodyS)
		  )
	      ->
	          true
	      ;
		  Ip = [], ISuccS=[], Cm=[]
	      ),
	      append(IComp,ISuccS,ISucc),
	      assertion_body(Sg,Ip,IC,ISucc,[],Cm,Body)
	 ;
	     ( AbsInt = det ; AbsInt = nf ), % IG: choice points ?
	       assertion_read(Sg,_M,Status,comp,Body0,_Dict,Source,LB,LE),
	       assertion_body(Sg,Ip,IC,IS,Comp,Cm,Body0),
	       assertion_body(Sg,Ip,IC,Comp,IS,Cm,Body)
	 % deprecated exit assertions
       % ; assertion_read(Sg,_M,Status,exit,Body,_Dict,Source,LB,LE)
         ;  % [IG] done in apply_trust_success
	     current_pp_flag(old_trusts, on),
	     (AbsInt \= res_plai, AbsInt \= res_plai_stprf, AbsInt \= sized_types),
	      assertion_read(Sg,_M,Status,success,Body,_Dict,Source,LB,LE),
	      ( Status == check ->
		(
		    current_pp_flag(use_check_assrt,on),
		    type_of_goal(imported,Sg)
		;
		    current_pp_flag(use_check_assrt,libraries),
		    type_of_goal(imported,Sg), %PP it's only about imported % IG unnecessary choicepoints?
		    get_module_from_sg(Sg,Module),
		    current_itf(defines_module,Module,Base), % IG unnecessary choicepoints?
		    is_library(Base)
	         )
              ; true
 	      )
         ;  % [IG] done in apply_trust_calls
	     current_pp_flag(old_trusts, on),
	     get_call_from_call_assrt(Sg,_,Status,InfoCall,Source,LB,LE),
	     InfoSucc = []
         ),
	 assertion_body(Sg,_Compat,InfoCall,InfoSucc,_Comp,_Comm,Body),
         % approx default trust
         info_to_asub(AbsInt,_approx1,InfoCall,Sv,Appr,Sg),
         info_to_asub(AbsInt,_approx2,InfoSucc,Sv,Succ0,Sg,Appr),
         unknown_call(AbsInt,Sv,Appr,Appr0),
         glb(AbsInt,Appr0,Succ0,Trust0),
         ( retract_fact(approx(SgKey,Sg,AbsInt,Trust1)) ->
	     compute_lub(AbsInt,[Trust0,Trust1],Trust)
	 ; Trust = Trust0
         ),
	 ( contains_parameters(AbsInt,Trust) ->
	     retract_fact(cached_trust(AbsInt,SgKey))
	 ; assertz_fact(approx(SgKey,Sg,AbsInt,Trust))
	 ),
         % applicable trust
         ( full_info_to_asub(AbsInt,InfoCall,Sv,Call,Sg) ->
	     unknown_call(AbsInt,Sv,Call,Call0),
	     glb(AbsInt,Call0,Succ0,Succ),
	     % ???
	     Succ \== '$bottom',
	     assertz_fact(trust(SgKey,Sg,Call,AbsInt,Succ,loc(Source,LB,LE)))
	 ;
	     % full_info_to_asub/5 failed since InfoCall is not relevant
	     % to the domain
	     true
	 ),
         fail.
trusted(SgKey,Proj,Sg,Sv,AbsInt,Loc,Prime):-
	trusted(SgKey,Proj,Sg,Sv,AbsInt,Loc,Prime).

look_trust(AbsInt,SgKey,Sg,Sv,Proj,Loc,Prime):-
	do_trust(AbsInt,lt,SgKey,Sg,Sv,Proj,Loc,Prime), !.
% look_trust(AbsInt,SgKey,Sg,Sv,Proj,Loc,Prime):-
% 	do_trust(AbsInt,gt,SgKey,Sg,Sv,Proj,Loc,Prime), !.
look_trust(AbsInt,SgKey,Sg,Sv,Proj,loc(nofile,0,0),Prime):-
	current_fact(approx(SgKey,SgCopy,AbsInt,Prime0)),
  unknown_entry(AbsInt,Sv,Top),
	do_trust_(AbsInt,top,SgCopy,Top,Prime0,Sg,Sv,Proj,Prime).

do_trust(AbsInt,Step,SgKey,Sg,Sv,Proj,_Loc,_Prime):-
	retractall_fact(the_trusts(_,_,_,_)),
	functor(Sg,F,A),
	functor(SgCopy,F,A),
	one_trust(SgKey,SgCopy,Call,AbsInt,Succ,Loc),
	do_trust_(AbsInt,Step,SgCopy,Call,Succ,Sg,Sv,Proj,Prime),
	( current_fact(the_trusts(_,Sv,Projs0,Primes0),Ref) ->
	    more_concrete(Projs0,Primes0,AbsInt,Step,Proj,Prime,Projs,Primes,Flag),
	    ( var(Flag) -> true
	    ; erase(Ref),
	      asserta_fact(the_trusts(Loc,Sv,Projs,Primes))
	    )
	; asserta_fact(the_trusts(Loc,Sv,[Proj],[Prime]))
	),
	fail.
do_trust(AbsInt,_Step,_SgKey,_Sg,Sv,_Proj,Loc,Prime):-
	retract_fact(the_trusts(Loc,Sv,_,Primes)),
	compute_lub(AbsInt,Primes,Prime).

do_trust_(AbsInt,Step,SgCopy,Call0,Succ,Sg,_Sv,Proj,Prime):-
	variant(SgCopy,Sg), !,
	SgCopy=Sg,
  abs_sort(AbsInt,Call0,Call),
	set_param_matching_mode(on),
	( less_or_equal_(Step,AbsInt,Proj,Call) -> 
	  true
	; set_param_matching_mode(off),
	  fail
	),
	set_param_matching_mode(off),
  abs_sort(AbsInt,Succ,Prime).
do_trust_(AbsInt,Step,SgCopy,Call,Succ,Sg,Sv,Proj,Exit):-
	varset(SgCopy,Gv),
	set_param_matching_mode(on),
	( call_to_entry_(Step,AbsInt,Gv,SgCopy,Sv,Sg,[],Call,Entry),
	  less_or_equal_(Step,AbsInt,Proj,Entry) ->
	  true
	; set_param_matching_mode(off),
	  fail
	),
	set_param_matching_mode(off),
	call_to_entry(AbsInt,Gv,SgCopy,Sv,Sg,[],Succ,Exit,_).

one_trust(SgKey,SgCopy,Call,AbsInt,Succ,Loc):-
	current_fact(trust(SgKey,SgCopy,Call,AbsInt,Succ,Loc)),
	retract_if_parametric(trust(SgKey,SgCopy,Call,AbsInt,Succ,Loc),AbsInt,Succ).

retract_if_parametric(Trust,AbsInt,Succ) :-
	contains_parameters(AbsInt,Succ),!,
	retract_fact(Trust).
retract_if_parametric(_,_,_).

%%jcf-27.11.03-begin
%%jcf%one_trust(SgKey,SgCopy,Call,AbsInt,Succ,loc('0',0,0)):-
%%jcf%	succ_pattern(AbsInt,SgCopy,Call,Succ),
%%jcf%	predkey_from_sg(SgCopy,SgKey).
%%jcf-27.11.03-end

%%PBC-24.10.2003-begin
%%PBC% more_concrete([],[],_AbsInt,_Step,_Proj,_Prime,[],[],_Flag).
%%PBC% more_concrete([Proj0|Projs0],[Prime0|Primes0],AbsInt,Step,Proj,Prime,Cs,Ss,y):-
%%PBC% 	less_or_equal_(Step,AbsInt,Proj,Proj0), !,
%%PBC% 	( less_or_equal_(Step,AbsInt,Proj0,Proj)
%%PBC% 	-> glb(AbsInt,Prime,Prime0,Prime1),
%%PBC% 	   Cs=[Proj|Cs1],
%%PBC% 	   Ss=[Prime1|Ss1]
%%PBC% 	 ; Cs=[Proj0|Cs1],
%%PBC% 	   Ss=[Prime0|Ss1]
%%PBC% 	),
%%PBC% 	more_concrete(Projs0,Primes0,AbsInt,Step,Proj,Prime,Cs1,Ss1,_).
%%PBC% more_concrete([Proj0|Projs0],[Prime0|Primes0],AbsInt,Step,Proj,Prime,
%%PBC% 	      [Proj0|Cs],[Prime0|Ss],Flag):-
%%PBC% 	more_concrete(Projs0,Primes0,AbsInt,Step,Proj,Prime,Cs,Ss,Flag).
more_concrete([],[],_AbsInt,_Step,Proj,Prime,[Proj],[Prime],y).
more_concrete([Proj0|Projs0],[Prime0|Primes0],AbsInt,Step,Proj,Prime,Cs,Ss,y):-
        less_or_equal_(Step,AbsInt,Proj,Proj0), !,
        ( less_or_equal_(Step,AbsInt,Proj0,Proj) ->
	    glb(AbsInt,Prime,Prime0,Prime1),
	    Cs=[Proj|Cs1],
	    Ss=[Prime1|Ss1]
	; Cs=[Proj|Cs1],
	    Ss=[Prime|Ss1]
	),
	cleanup(Projs0,Primes0,AbsInt,Step,Proj,Cs1,Ss1).
more_concrete([Proj0|Projs],[Prime0|Primes],AbsInt,Step,Proj,_Prime,Cs,Ss,_):-
        less_or_equal_(Step,AbsInt,Proj0,Proj), !,
        Cs=[Proj0|Projs],
        Ss=[Prime0|Primes].
more_concrete([Proj0|Projs0],[Prime0|Primes0],AbsInt,Step,Proj,Prime,
              [Proj0|Cs],[Prime0|Ss],Flag):-
        more_concrete(Projs0,Primes0,AbsInt,Step,Proj,Prime,Cs,Ss,Flag).

cleanup([],[],_AbsInt,_Step,_Proj,[],[]).
cleanup([Proj0|Projs],[Prime0|Primes],AbsInt,Step,Proj,Cs,Ss):-
        ( less_or_equal_(Step,AbsInt,Proj,Proj0) ->
	    Cs=Cs1,
	    Ss=Ss1
         ; Cs=[Proj0|Cs1],
           Ss=[Prime0|Ss1]
         ),
        cleanup(Projs,Primes,AbsInt,Step,Proj,Cs1,Ss1).  
%%PBC-24.10.2003-end

less_or_equal_(lt,AbsInt,Proj,Entry):-
	less_or_equal(AbsInt,Proj,Entry).
less_or_equal_(gt,AbsInt,Proj,Entry):-
	less_or_equal(AbsInt,Entry,Proj).
less_or_equal_(top,_AbsInt,_Proj,_Entry).

call_to_entry_(top,_AbsInt,_Gv,_SgCopy,_Sv,_Sg,_Vs,_Call,_Entry):- !.
call_to_entry_(_ny,AbsInt,Gv,SgCopy,Sv,Sg,Vs,Call,Entry):-
	call_to_entry(AbsInt,Gv,SgCopy,Sv,Sg,Vs,Call,Entry,_).
