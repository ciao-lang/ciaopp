:- module(modular_spec,
	[
	    generate_abs_execs_from_equivs/0,
	    reset_equivs/0,
	    equiv/3,
	    dyn_abs_spec/5
	],
	[assertions, datafacts]).

:- doc(title,"Specialization of Modular Programs").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains the dynamic abstract
      executability table for predicates defined in imported
      modules. This table contains both specialized versions
      introduced by hand and automatically generated.").

:- doc(bug, "predicate basiccontrol:true/0 is handled ad-hoc").

:- use_module(library(lists), [member/2]).
:- use_module(ciaopp(p_unit/assrt_db), 
	[assertion_read/9,
	 assertion_body/7]).

generate_abs_execs_from_equivs:-
	assertion_read(Goal,_M,Status,comp,Body,_VarNames,_S,_LB,_LE),
	member(Status,[trust,true]),
	assertion_body(Goal,_Compat,Call,_Succ,Comp,_Comm,Body),
	member('basic_props:equiv'(_Goal,NewGoal),Comp),
	asserta_fact(equiv(Goal,Call,NewGoal)),
	fail.

generate_abs_execs_from_equivs:-
	asserta_fact(equiv(true,[],true)).


reset_equivs:-
	retractall_fact(equiv(_,_,_)).

%-------------------------------------------------------------%

:- pred dyn_abs_spec(Module,Sg,AbsInt,Proj,SpecName)

# "Data predicate which contains the dynamic part of the abstract
  executability table.".

:- data dyn_abs_spec/5.

%-------------------------------------------------------------%

%-------------------------------------------------------------%

:- pred equiv(Goal,Cond,NewGoal)

# "Data predicate which contains the predicates from other modules
  which can be replaced by specialized versions.".

:- data equiv/3.
