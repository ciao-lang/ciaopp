/*             Copyright (C)1990-2003 UPM-CLIP				*/

:- use_package(datafacts).

% Ciao library
:- use_module(library(write), [write/1, write/2]).
:- use_module(library(lists), [append/3]).
:- use_module(library(aggregates), [(^)/2, bagof/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(sets), [ord_subtract/3]).

% CiaoPP library
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2, set_pp_flag/2]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3, predkey_from_sg/2]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(ciaopp(plai/fixpo_ops), [fixpoint_id_reuse_prev_success/6, 
        each_identical_abstract/3, each_project/6, fixpoint_get_new_id/5]).

% Plai library
:- use_module(ciaopp(plai/fixpo_ops), [inexistent/2, variable/2, bottom/1, 
	singleton/2, fixpoint_id_reuse_prev/5, fixpoint_id/1, fixp_id/1,
	each_abs_sort/3,
	each_extend/6,
	each_exit_to_prime/8,
	each_apply_trusted/7,
	each_body_succ_builtin/12,
	body_succ_meta/7,
%	applicable/3,
	reduce_equivalent/3,
	widen_succ/4,
	decide_memo/6,
	each_unknown_call/5,
	clause_applies/2,
	abs_subset_/3
 ]).
:- use_module(ciaopp(plai/domains)).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7, cleanup/0]).
:- use_module(ciaopp(plai/plai_db), 
	[complete/7,memo_call/5,memo_table/6,cleanup_plai_db/1,complete_parent/2]).
:- use_module(ciaopp(plai/re_analysis), [erase_previous_memo_tables_and_parents/4]).
:- use_module(ciaopp(plai/transform), [body_info0/4, trans_clause/3]).
:- use_module(ciaopp(plai/apply_assertions_old), [apply_trusted0/7, cleanup_trusts/1]).
:- use_module(ciaopp(plai/apply_assertions), [cleanup_applied_assertions/1]).
:- use_module(ciaopp(plai/fixpo_dx_check_basic)).
:- use_module(spec(global_control), [cleanup_unfolds/0]).


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

:- pred cleanup_fixpoint(?AbsInt) + not_fails
        #"Cleanups the database of analysis, of both temporary as well as
          permanent information regarding abstract domain @var{AbsInt}.".
cleanup_fixpoint(AbsInt):-
	cleanup_plai_db(AbsInt),
	cleanup_trusts(AbsInt),
  cleanup_applied_assertions(AbsInt),
	retractall_fact(fixp_id(_)),
	asserta_fact(fixp_id(0)), % there is no way to recover this 
	init_fixpoint,            % if several analysis coexist!
	cleanup_unfolds.

%------------------------------------------------------------------------
:- pred body_succ0(+RInfo,+SgKey,?Sg,?Sv_u,+HvFv_u,+Call,-Succ,+AbsInt,+ClId,+F,+NewN,-Id) + not_fails
  #"This predicate handles the special cases of the subgoals, i.e. when
    the subgoal is a builtin (also when it is a constraint since they are)
    internally represented as builtins). Otherwise, computation proceeds.".
body_succ0('$var',SgKey,Sg,_Sv_u,HvFv_u,Calls,Succs,AbsInt,ClId,F,_,Id):-
	!,
	( Calls=[Call],
	  concrete(AbsInt,Sg,Call,Concretes),
	  concretes_to_body(Concretes,SgKey,AbsInt,B)
	-> fixpoint_id(Id),
	   meta_call(B,HvFv_u,Calls,[],Succs,AbsInt,ClId,Id,Ids),
	   assertz_fact(memo_call(F,Id,AbsInt,Concretes,Ids))
	 ; Id=no,
	   variable(F,ClId),
	   each_unknown_call(Calls,AbsInt,Sg,[Sg],Succs) % Sg is a variable % TODO: use call(Sg) or similar? (JF)
	).
% TODO: Add apply trust calls assertions
body_succ0('$meta'(T,B,_),SgKey,Sg,Sv_u,HvFv_u,Call,Succ,AbsInt,ClId,F,N,Id):-
	!,
	( current_pp_flag(reuse_fixp_id,on) ->
	    ( Call=[C] ->
	        sort(Sv_u,Sv),
          project(AbsInt,Sg,Sv,HvFv_u,C,Proj),
          fixpoint_id_reuse_prev(SgKey,AbsInt,Sg,Proj,Id)
	    ; true
	    )
	;
	    fixpoint_id(Id)
	),
	meta_call(B,HvFv_u,Call,[],Exits,AbsInt,ClId,Id,_Ids),
	( body_succ_meta(T,AbsInt,Sv_u,HvFv_u,Call,Exits,Succ) ->
	    ( Call=[C] ->
	        sort(Sv_u,Sv),
		project(AbsInt,Sg,Sv,HvFv_u,C,Proj),
		each_project(Exits,AbsInt,Sg,Sv,HvFv_u,Prime),
		asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,[(F,N)])) % TODO: IG check duplicates
	    ; true
	    )
	 ; % for the trusts, if any:  % not apply trust here??
	    varset(Sg,Sv_r),
	    body_succ0(nr,SgKey,Sg,Sv_r,HvFv_u,Call,Succ,AbsInt,ClId,F,N,Id0),
	    retract_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id0,Ps)),
	    asserta_fact(complete(SgKey,AbsInt,Sg,Proj,Prime,Id,Ps)),
	    ( retract_fact(complete_parent(Id0,Fs)) ->
	        asserta_fact(complete_parent(Id,Fs))     % for fixpo_di/dd
	    ;
          true                                     % for the rest of fixpo_dx
	    )
	).
body_succ0('$built'(T,Tg,Vs),SgKey,Sg,Sv_u,HvFv_u,Call,Succ,AbsInt,_ClId,F,N,Id):-
	!,
	Id=no,
	sort(Sv_u,Sv),
	each_body_succ_builtin(Call,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,F,N,Succ).
body_succ0(RFlag,SgKey,Sg,Sv_u,HvFv_u,Call,Succ,AbsInt,ClId,F,N,Id):-
	sort(Sv_u,Sv),
	each_call_to_success(Call,RFlag,SgKey,Sg,Sv,HvFv_u,AbsInt,ClId,Succ,F,N,Id).

%GP if the list of Bodies is empty, then there is nothing to analyze 
%   and we can make Succ = Call. Some more thinking is welcome
meta_call([],_HvFv_u,Call,[],Call,_AbsInt,_ClId,_Id,[]).
meta_call([Body|Bodies],HvFv_u,Call,Succ0,Succ,AbsInt,ClId,Id,Ids):-
        meta_call_([Body|Bodies],HvFv_u,Call,Succ0,Succ,AbsInt,ClId,Id,Ids).

meta_call_([Body|Bodies],HvFv_u,Call,Succ0,Succ,AbsInt,ClId,Id,Ids):-
	meta_call_body(Body,ClId,Call,Succ1,HvFv_u,AbsInt,Id,Ids0),
%	widen_succ(AbsInt,Succ0,Succ1,Succ2),
	append(Succ0,Succ1,Succ2),
	append(Ids0,Ids1,Ids),
	meta_call_(Bodies,HvFv_u,Call,Succ2,Succ,AbsInt,ClId,Id,Ids1).
meta_call_([],_HvFv_u,_Call,Succ,Succ,_AbsInt,_ClId,_Id,[]).

meta_call_body((Sg,Rest),K,Call,Exit,Vars_u,AbsInt,PId,CIds):-
	!,
	CIds=[Id|Ids],
	body_succ(Call,Sg,Succ,Vars_u,AbsInt,K,PId,Id),
	meta_call_body(Rest,K,Succ,Exit,Vars_u,AbsInt,PId,Ids).
meta_call_body(true,_,Call,Call,_,_,_,[no]):- !.
meta_call_body(Sg,Key,Call,Exit,Vars_u,AbsInt,PId,[Id]):- 
	body_succ(Call,Sg,Exit,Vars_u,AbsInt,Key,PId,Id).

concretes_to_body([],_SgKey,_AbsInt,[]).
concretes_to_body([Sg|Sgs],SgKey,AbsInt,[B|Bs]):-
	% have to module-expand Sg!!!!
	body_info0(Sg:SgKey,[],AbsInt,B),
	concretes_to_body(Sgs,SgKey,AbsInt,Bs).
