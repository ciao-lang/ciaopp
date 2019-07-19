:- module(abs_exec,
	[ abs_exec/4,
	  dyn_abs_exec/4,
	  determinable/2
	],
	[ ]).

:- use_package(assertions).

:- use_module(spec(static_abs_exec_table), 
	[abs_ex/4]).

:- use_module(spec(abs_exec_ops), 
 	[abs_exec_regtype/3]).

%% :- use_module(spec(unfold_builtins),
%% 	[peel_call/2]).

:- use_module(spec(modular_spec), 
	[dyn_abs_spec/5]).

:- use_module(ciaopp(p_unit), 
	[native_prop/2]).

:- use_module(library(assertions/assrt_lib), 
	[denorm_goal_prop/3]).


	    
/*             Copyright (C)1990-94 UPM-CLIP			   */

%-------------------------------------------------------------------%
%                                                                   %
%                      started: October 93                          %
%              programmed: A.German Puebla Sanchez                  %
%                                                                   %
%-------------------------------------------------------------------% 


% builtins that can be abstractly evaluated, 
% and the conditions required


%-------------------------------------------------------------------%
% abs_exec(+,+,+,-)                                                 %
% abs_exec(Abs,Pred,Sense,Cond)                                     %
%  Pred is abstractly executable to Sense with abstract domain Abs  %
%  if Cond holds                                                    %
%-------------------------------------------------------------------%
%-------------------------------------------------------------------%
% predicates directly simplificable                                 %
%-------------------------------------------------------------------%
abs_exec(Abs,F/A,Sense,Cond):-
	find_original_pred_if_needed(F,A,OrigF,OrigA),
	functor(Pred,OrigF,OrigA),
	native_prop(Pred,NPred),
	functor(NPred,NF,NA),
	(NF == regtype ->
	    determinable(Abs,types),
	    arg(1,NPred,SPred),
	    denorm_goal_prop(SPred,TypeSymbol,_),
	    abs_exec_regtype(TypeSymbol,Sense,Cond)
	;
	    abs_exec_(Abs,NF/NA,Sense,Cond)
	).

find_original_pred_if_needed(F,A,OrigF,OrigA):-
%% 	current_pp_flag(local_control,Unf),
%% 	(Unf \== off ->
%% 	    current_fact(spec_def_for(_,Sg,_,_,_,_,F,A)),
%% 	    functor(Sg,OrigF,OrigA)
%% 	;
	    OrigF = F, OrigA = A
%%	)
	.


abs_exec_(_,true/0,true,true).
abs_exec_(_,otherwise/0,true,true).
abs_exec_(_,fail/0,fail,true). % in any domain
abs_exec_(_,false/0,fail,true).
% rest of builtin predicates
abs_exec_(Domain,Pred,Sense,Cond):-
	abs_ex(Pred,Determ,Sense,Cond),
	determinable(Domain,Determ).

dyn_abs_exec(Domain,/(Name,Arity),imported(SpecName),leq(Sg,Proj)):-
	functor(Sg,Name,Arity),
	dyn_abs_spec(_Module,Sg,Domain,Proj,SpecName).


% abs_exec_(Domain,/(Name,Arity),Sense,Cond):-
%         functor(Pred,Name,Arity),
% 	determinable(Domain,types),
% 	findall((Pred:-Body),
%         clause_read(_Base,Pred,Body,_Dict,_S,_LB,_LE),
% 	Cls),
% 	regular_type_pred_definition(Cls),
% 	denorm_goal_prop(Pred,TypeSymbol,_),
% 	pred_to_typedef(Cls,TypeSymbol,TypeRule),
% 	assert_type_definition(TypeSymbol,TypeRule),
% 	asserta_fact(user_type(Pred)),
% 	abs_ex(/(Name,Arity),types,Sense,Cond).

%% GPS ignored blocks by now
%% %-------------------------------------------------------------------%
%% % Predicates with a block declaration                               %
%% %-------------------------------------------------------------------%
%% abs_exec_(def,F/A,Sense,Cond):-
%% 	recorded_internal(block_cond,b(F/A,Conditions),_),!,
%% 	Sense = block_cond(Conditions),
%% 	Cond = true.
%% abs_exec_(shfr,F/A,Sense,Cond):-
%% 	recorded_internal(block_cond,b(F/A,Conditions),_),!,
%% 	Sense = block_cond(Conditions),
%% 	Cond = true.
%% abs_exec_(shfrnv,F/A,Sense,Cond):-
%% 	recorded_internal(block_cond,b(F/A,Conditions),_),!,
%% 	Sense = block_cond(Conditions),
%% 	Cond = true.
%% abs_exec_(aeq,F/A,Sense,Cond):-
%% 	recorded_internal(block_cond,b(F/A,Conditions),_),!,
%% 	Sense = block_cond(Conditions),
%% 	Cond = true.

%-------------------------------------------------------------------%
% We express abstract executability in terms of simpler domains     %
%-------------------------------------------------------------------%
determinable(_,true):-!.
determinable(_,false):-!.

determinable(terms,types).
determinable(eterms,types).
determinable(etermsvar,types).
determinable(svterms,types).
determinable(ptypes,types).
determinable(evalterms,types).
determinable(svterms,types).
determinable(deftypes,types).

determinable(def,ground).

determinable(share,ground).
determinable(share,indep).

determinable(son,ground).
determinable(son,indep).

determinable(shfr,ground).
determinable(shfr,indep).
determinable(shfr,free).
determinable(shfr,not_indep).
determinable(shfr,not_ground).

determinable(sharefree_amgu,X):-
	determinable(shfr,X).

determinable(sharefree_clique,X):-
	determinable(shfr,X).

determinable(sharefree_clique_def,X):-
	determinable(shfr,X).

determinable(shfrnv,X):-
	determinable(shfr,X).
determinable(shfrnv,nonvar).

determinable(shfrson,X):-
	determinable(shfr,X).

determinable(aeq,ground).
determinable(aeq,indep).
determinable(aeq,free).
determinable(aeq,not_indep).

determinable(fr,indep).
determinable(fr,free).
determinable(fr,not_ground).
%determinable(fr,unconstrained). cannot be used in any optimization by now

determinable(fd,ground).
determinable(fd,indep).
determinable(fd,free).
determinable(fd,not_ground).
%determinable(fd,unconstrained). cannot be used in any optimization by now
%
%% TODO: find a better name for Determ instead of 'polyhedra'?
%%       (e.g., linear arithmetic)
determinable(polyhedra,polyhedra).

determinable(Dom,[X|Xs]):-
	determinable(Dom,X),
	determinable(Dom,Xs).

 %% determinable(typeshfr,Prop):-
 %% 	determinable(shfr,Prop).
