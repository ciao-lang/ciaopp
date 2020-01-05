:- module(abs_exec_ops, 
    [ unify_if_it_is_instance/2,
      unify_if_it_is_variant/2,
      adapt_info_to_assrt_head/6,
      abs_exec_regtype/3,
      abs_exec_regtype_in_clause/8
    ],[assertions, isomodes]).

:- doc(title,"Auxiliary Operations for Abstract Execution").

:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This module contains the implementation of a
     series of operations which are instrumental for abstractly
     executing properties. A particular aim is to be able to handle
     both non-normalized (i.e., possibly containing non-variable
     terms) literals and assertions.").  

:- use_module(spec(abs_exec_cond), [cond/4]).
 
:- use_module(ciaopp(plai/domains), [call_to_entry/10, project/6]).

:- use_module(library(terms_check), [instance/2, variant/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(library(assertions/assrt_lib), [denorm_goal_prop/3]).

unify_if_it_is_instance(Goal,NGoal):-
    copy_term(Goal,Copy),
    Copy = NGoal,
    instance(Goal,Copy),
    Goal = NGoal.

unify_if_it_is_variant(Goal,NGoal):-
    variant(Goal,NGoal),
    Goal = NGoal.

:- pred adapt_info_to_assrt_head(+Abs,+Goal,Vars,+Info,+Head,-NewInfo) 
   # "This predicate allows adapting the analysis info available at a
     given program point to the head of an assertion which is
     applicable to such program point. The @var{Head} of the assertion
     must be a variant of @var{Goal} or be less instantiated than
     @var{Goal}. Otherwise the information is not safe to adapt and
     the predicate fails. @var{NewInfo} can be used to check
     assertions in program points which are not necessarily
     normalized.".

adapt_info_to_assrt_head(_Abs,Goal,_Vars,Info,Head,NewInfo):-
    unify_if_it_is_variant(Goal,Head),!,
    NewInfo = Info.
adapt_info_to_assrt_head(Abs,Goal,Vars,Info,Head,NewInfo):-
    instance(Goal,Head),!,
    varset(Goal,Sv),
    varset(Head,Hv),
    project(Abs,Goal,Sv,Vars,Info,InfoProj),   
    call_to_entry(Abs,Sv,Goal,Hv,Head,not_provided,[],InfoProj,NewInfo,_Info). % TODO: add some ClauseKey? (JF)

:- pred abs_exec_regtype(TypeSymbol,Sense,Cond) # "Calls to regular
   types can be abstractly executed to true or false assuming type
   analysis information is available.".

abs_exec_regtype(TypeSymbol, true , type_incl(1,TypeSymbol)).
abs_exec_regtype(TypeSymbol, fail , incomp_type(1,TypeSymbol)).
abs_exec_regtype(TypeSymbol, fail, free(1)):-
    TypeSymbol \== term.

:- pred abs_exec_regtype_in_clause/8 # "This predicate tries to
   abstractly execute a call to a regtype appearing in a clause to
   either true or false.  Note that this differs from regular types in
   assertions in that the default in assertions is instantiation,
   whereas in program code the default is compatibility!".

abs_exec_regtype_in_clause(Abs,SPred,F,A,Goal,Vars,Info,Sense):-
    denorm_goal_prop(SPred,TypeSymbol,_),
    functor(NHead,F,A),
    adapt_info_to_assrt_head(Abs,Goal,Vars,Info,NHead,NewInfo),
    regtype_exec_in_clause(TypeSymbol,NHead,NewInfo,Abs,Sense).

regtype_exec_in_clause(SPred,NHead,NewInfo,Abs,Sense):-
    cond(type_incl(1,SPred),Abs,NHead,NewInfo),!,
    Sense = true.
regtype_exec_in_clause(SPred,NHead,NewInfo,Abs,Sense):-
    cond(incomp_type(1,SPred),Abs,NHead,NewInfo),!,
    Sense = fail.

