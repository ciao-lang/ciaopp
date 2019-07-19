:- module(transform,
	[ determine_r_flag/3,
	  transform_clauses/5,
	  body_info0/4,
	  % trans clause db operations
	  trans_clause/3,
	  remove_trans_clause/2,
	  cleanup_trans_clauses_pred/1,
	  cleanup_trans_clauses/0,
	  reorder_trans_clauses/1,
	  update_trans_clause_rflag/3,
	  update_trans_clause/6
	],
	[assertions, datafacts]).

:- use_module(library(sets), [ord_member/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).
:- use_module(ciaopp(plai/domains), [combined_special_builtin/3, special_builtin/6]).

%------------------------------------------------------------------------%
%                    Meaning of the Module Variables                     %
%                                                                        %
%  AbsInt  : identifier of the abstract domain being used                %
%  SgKey   : Predicate Key, represented by 'F/A'                         %
%  Head    : Head of one of the clauses which define the predicate       %
%  RFlag   : Recursivity flag (r or nr)                                  %
%  Body    : Body of the clause                                          %
%  Clid    : Clause identifier, represented by 'F/A/C' where C is the    %
%            position of the clause with respect to the other clauses of %
%            the predicate                                               %
%  Vars_u  : All the variables present in a clause (head and body)       %
%------------------------------------------------------------------------%

:- data trans_clause_/6.
% NOTE: clauses are transformed for a domain (and recomputed for each domain).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Database operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
trans_clause(SgKey,RFlag,X) :-
	current_fact(trans_clause_(SgKey,RFlag,Head,Vars_u,Clid,Body)),
	X = clause(Head,Vars_u,Clid,Body).

remove_trans_clause(SgKey, Clid) :-
	retract_fact(trans_clause_(SgKey, _, _, _, Clid, _)).

cleanup_trans_clauses_pred(SgKey) :-
	retractall_fact(trans_clause_(SgKey, _, _, _, _, _)).

cleanup_trans_clauses :-
	retractall_fact(trans_clause_(_, _, _, _, _, _)).

update_trans_clause_rflag(Key, Clid, RFlag) :-
	retract_fact(trans_clause_(Key,_,Head,Vars,Clid,Body)), !, % IG: Clid is unique
	asserta_fact(trans_clause_(Key,RFlag,Head,Vars,Clid,Body)).

update_trans_clause(Key, Clid, RFlag, Head, Vars, Body) :-
	retract_fact(trans_clause_(Key,_,_,_,Clid,_)), !, % IG: Clid is unique
	asserta_fact(trans_clause_(Key,RFlag,Head,Vars,Clid,Body)).

:- pred reorder_trans_clauses(Clids) : list # "Reorders the transformed
clauses so they are enumerated stored in the same order in which they are written
in the original source code.".
reorder_trans_clauses(Clids) :- % With list of clids and move to transform.pl
	get_ordered_trans_clauses(Clids, NCls),
	cleanup_trans_clauses,
	assert_all(NCls).

get_ordered_trans_clauses([], []).
get_ordered_trans_clauses([Clid|Clids], [clause(K, A, B, C, Clid, E)|NCls]) :-
	trans_clause_(K, A, B, C, Clid, E), !,
	get_ordered_trans_clauses(Clids, NCls).

assert_all([]).
assert_all([clause(K, A, B, C, D, E)|Cls]) :-
	assertz_fact(trans_clause_(K, A, B, C, D, E)),
	assert_all(Cls).


% End of database operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------
% transform_clauses(+,+,+,+)
% transform_clauses(Clauses,Dicts,RecursCl,RecursPs)
% It transforms the program into a suitable format and recorda all clauses
% in the database. 
% If Clause is a directive, the new format is (Clause,DK) and nothing 
% is recordered in the data base
% Otherwise, the new format is (clause(Head,NewBody),Clid) were Clid is the
% atom 'F/A/N', F is the predicate symbol of the head, A is its arity and N is 
% the clause number, and NewBody is the result of substituting each Atom for
% Atom:Key were key is an atom 'F/A/N/M', and M indicates the position of the 
% atom in the clause). 
% Special cases are:
%    - if the clause is a fact, NewBody is 'true'
%    - no :Key is added to cuts 
% The register kept in the database is:
%         asserta_fact(trans_clause_(Key,Rflag,Head,Vars,Clid,B))
% were Key is the atom 'F/A', Rflag is the recursiveness flag for the clause
% (r if it is recursive, nr if it is not), and Clid is used as key to identify
% the exit point of the clause.
% B is a list of lists of elements g(Key,Sv,Rflag,SgKey,Sg), one
% for each literal in the body.
%-----------------------------------------------------------------------------
transform_clauses([Clause:ClId|Clauses],[D|Ds],[R|Rs],Ps,AbsInt):-
	clause_info(Clause,ClId,D,R,Ps,AbsInt),
	transform_clauses(Clauses,Ds,Rs,Ps,AbsInt).
transform_clauses([],[],[],_Ps,_AbsInt).

clause_info(directive(_),_,_,_,_,_). %% do nothing...
clause_info(clause(Head,Body),Clid,_D,Rflag,_,_AbsInt):-
%	(Body = true ; Body = (!)), !,  %%%%% Warning
	Body = true, !,
	predkey_from_sg(Head,Key),
	varset(Head,Vars),
%	vars_names_dict(D,Vars,_),
	assertz_fact(trans_clause_(Key,Rflag,Head,Vars,Clid,true)).
clause_info(clause(Head,Body),Clid,_D,Rflag,Ps,AbsInt):-
	body_info0(Body,Ps,AbsInt,B),
	predkey_from_sg(Head,Key),
	varset((Head,Body),Vars),
%	vars_names_dict(D,Vars,_),
	assertz_fact(trans_clause_(Key,Rflag,Head,Vars,Clid,B)).

body_info0((Atom,Atoms),Ps,AbsInt,Ats):- !,
	Ats = (At,Ats0),
	body_info0(Atom,Ps,AbsInt,At),
	body_info0(Atoms,Ps,AbsInt,Ats0).
body_info0(Atom:Key,Ps,AbsInt,At):- !,
	atom_info(Atom,Key,Ps,AbsInt,At).
body_info0((!),Ps,AbsInt,At):-
	atom_info((!),(!),Ps,AbsInt,At).  % TODO: strange key for !/0

atom_info(Subgoal,Id,_Ps,_AbsInt,Goal) :-
	var(Subgoal), !,
	Goal=g(Id,Subgoal,'$var',no,Subgoal).
atom_info(Subgoal,Id,Ps,AbsInt,g(Id,Svars,Info,SgKey,Goal)) :-
	varset(Subgoal,Svars),
	predkey_from_sg(Subgoal,SgKey),
	atom_meta_builtin_info(SgKey,Subgoal,Ps,AbsInt,Info,Goal).

atom_meta_builtin_info(_SgKey,Subgoal,Ps,AbsInt,Info,Goal):-
  ( type_of_goal(metapred(Type,_Meta),Subgoal),
	  type_of_goal(imported,Subgoal) -> true
  ; fail
  ),
	functor(Subgoal,F,A),
	functor(Goal,F,A),
	meta_info(Subgoal,A,Ps,AbsInt,Bodies,Data,Goal),
  \+ Bodies = [],
  !,
	Info = '$meta'(Type,Bodies,Data).
atom_meta_builtin_info(SgKey,Subgoal,Ps,AbsInt,Info,Goal):-
	combined_special_builtin(AbsInt,Subgoal,SgKey,Domains), !,
	Goal = Subgoal,
	map_atom_builtin_info(Domains,SgKey,Subgoal,Ps,Info).
atom_meta_builtin_info(SgKey,Subgoal,Ps,AbsInt,Info,Subgoal):-
	atom_builtin_info(SgKey,Subgoal,Ps,AbsInt,Info).

map_atom_builtin_info([],_SgKey,_Subgoal,_Ps,[]).
map_atom_builtin_info([AbsInt|Domains],SgKey,Subgoal,Ps,[I|Info]):-
	atom_builtin_info(SgKey,Subgoal,Ps,AbsInt,I),
	map_atom_builtin_info(Domains,SgKey,Subgoal,Ps,Info).

atom_builtin_info(SgKey,Subgoal,_Ps,AbsInt,Info):-
	builtin_info(Subgoal,SgKey,AbsInt,Type,TypeGoal,Condvars), !,
%	type_of_goal(imported,Subgoal), !,
	Info = '$built'(Type,TypeGoal,Condvars).
atom_builtin_info(_SgKey,Subgoal,Ps,_AbsInt,Rflag):-
	functor(Subgoal,F,A),
	determine_r_flag(Ps,F/A,Rflag).

builtin_info(Subgoal,_SgKey,AbsInt,Type,TypeGoal,Condvars):-
	type_of_goal(builtin(TypeGoal),Subgoal),
	predkey_from_sg(TypeGoal,SgKey),
	special_builtin(AbsInt,SgKey,TypeGoal,Subgoal,Type,Condvars), !.
builtin_info(Subgoal,SgKey,AbsInt,Type,Subgoal,Condvars):-
	special_builtin(AbsInt,SgKey,Subgoal,Subgoal,Type,Condvars).

combined_special_builtin(AbsInt,Subgoal,_SgKey,Domains):-
	type_of_goal(builtin(TypeGoal),Subgoal),
	predkey_from_sg(TypeGoal,SgKey),
	domains:combined_special_builtin(AbsInt,SgKey,Domains).
combined_special_builtin(AbsInt,_Subgoal,SgKey,Domains):-
	domains:combined_special_builtin(AbsInt,SgKey,Domains).

meta_info(_,0,_Ps,_,[],_,_) :- !.
meta_info(G,A,Ps,AbsInt,Bodies,Data,NewG):-
	A > 0,
	arg(A,G,GA),
	arg(A,NewG,Term),
	( nonvar(GA),
	  GA='$'(Term,Goal,Type)
	-> ( Type=goal
	   -> body_info0(Goal,Ps,AbsInt,Body),
	      Bodies=[Body|Bodies0],
	      Data=Data0
	    ; % Type=data,
	      Data=[Goal|Data0],
	      Bodies=Bodies0 )
	 ; Term=GA,
	   Bodies=Bodies0 ),
	A1 is A-1,
	meta_info(G,A1,Ps,AbsInt,Bodies0,Data0,NewG).

determine_r_flag(notarjan,_P,Rflag):-!,
	Rflag = r. % if no tarjan done we have to assume recursive...
determine_r_flag(Ps,P,Rflag):-
	ord_member(P,Ps), !, % TODO: this is potentially slow, Ps has
			     % element of the form P/A
	Rflag=r.
determine_r_flag(_Ps,_P,nr).
