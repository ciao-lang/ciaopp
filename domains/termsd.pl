:- module(termsd,[
%	replace/6,  % delete
%	get_typedefinition/2, % delete
	terms_init_abstract_domain/1,
	%
	terms_call_to_entry/9,
	terms_exit_to_prime/7,
	terms_project/3,
	terms_compute_lub/2,
	terms_compute_lub_el/3,
	terms_abs_sort/2,
	terms_extend/4,
	terms_less_or_equal/2,
	terms_glb/3,
	terms_unknown_call/4,
	terms_unknown_entry/3,
	terms_empty_entry/3,
	terms_call_to_success_fact/9,
	terms_special_builtin/5,
	terms_success_builtin/5,
	terms_call_to_success_builtin/6,
	terms_input_interface/4,
	terms_asub_to_native/5,
	terms_output_interface/2,
	terms_input_user_interface/5,
	terms_collect_abstypes_abs/3,
	terms_rename_abstypes_abs/4,
	terms_identical_abstract/2,
	terms_widen/3,
	terms_widencall/3,
	terms_concrete/3,
	%
	concrete/4,
	normalize_type_asub/2,
	revert_types/4,
	shortening_el/2,
	precondition_builtin/2,
	postcondition_builtin/4
	     ],
	     [assertions,regtypes,basicmodes
	     ]).


:- doc(title,"Types Abstract Domain").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").

:- doc(module,"

This module implements the abstract operations of the type domains with
widening based on shortening.
An abstrat sustitution is list of Var:Type elements, where Var is a 
variable and Type is a pure type term @cite{Dart-Zobel}. 

").

:- use_module(ciaopp(p_unit), [new_internal_predicate/3]).
% type operations from Pedro's library
:- use_module(typeslib(typeslib), 
	[
	    assert_param_type_instance/2,
	    compound_pure_type_term/4,
	    construct_compound_pure_type_term/2,
	    dz_equivalent_types/2,
	    dz_type_included/2,
	    em_defined_type_symbol/2,
	    equiv_type/2,
	    equiv_types/2,
	    generate_a_type_assigment/3,
	    get_type_definition/2,
	    insert_rule/2,
	    internally_defined_type_symbol/2,
	    new_type_symbol/1,
	    param_type_symbol_renaming/2,
	    pure_type_term/1,
	    recorda_required_types/1,
	    rule_type_symbol/1,
	    set_atom_type/1,
	    set_float_type/1,
	    set_int_type/1,
	    set_numeric_type/1,
	    set_numexp_type/1,
	    set_top_type/1,
	    type_escape_term_list/2,
	    type_intersection_2/3,
	    type_symbol/1,
	    unfold_type_union_1/4,
    	    get_module_types/1,
	    contain_this_type/3,
	    minimaltype/2
	]).

%:- reexport(typeslib(typeslib),[insert_rule/2]). % delete

:- use_module(library(messages), [warning_message/2]).

:- use_module(library(terms_vars), 
	[
	  varset/2
	]).
:- use_module(library(terms_check), 
	[
	  variant/2
	]).
:- use_module(library(lists), 
	[
	    member/2, append/3,
	    reverse/2
	]).
:- use_module(library(sets), 
	[ 
	    merge/3,
	    ord_subtract/3,
	    ord_member/2,
	    insert/3
	]).
:- use_module(library(sort), 
	[
	    sort/2
	]).

:- use_module(ciaopp(preprocess_flags), 
	[
	    current_pp_flag/2
	]).

:- use_module(library(assoc), [get_assoc/3]).

:- regtype absu(A) # "@var{A} is an abstract substitution".

absu('$bottom').
absu([]).
absu([Elem|Absu]):- 
	absu_elem(Elem),
	absu(Absu).

:- regtype absu_elem(E) # "@var{E} is a single substitution".

absu_elem(Var:Type):-
	var(Var),
	pure_type_term(Type).

terms_input_interface(ground(X),perfect,Acc,[gnd(X)|Acc]).
terms_input_interface(regtype(T),perfect,Acc,[T|Acc]):-
        functor(T,_,1),!,
        may_be_var(Acc).
terms_input_interface(regtype(T),perfect,Acc,[NonPT|Acc]):-
        functor(T,_,2),!,
        arg(1,T,V),
        assert_param_type_instance(T,NonPType),
        functor(NonPT,NonPType,1),
        arg(1,NonPT,V),
        may_be_var(Acc).
terms_input_interface(member(X,L),perfect,Acc,[P|Acc]):-
	type_escape_term_list(L,Def),
        new_type_symbol(T),
	insert_rule(T,Def),
	P =.. [T,X].


may_be_var([]):- !.
may_be_var(_Acc).

get_type(Var,[NVar:T|_],T):- Var == NVar.
get_type(Var,[_|ASub],T):- 
	get_type(Var,ASub,T).

concret_def([],L,L,_).
concret_def([T1|Def],List1,List2,Seen):-
	concrete(T1,List1,List0,Seen),
	concret_def(Def,List0,List2,Seen).

addarg([],_,_,L,L).
addarg([C|ListArg],F,A,[Term|L1],L2):-
	copy_term(F,Term),
	arg(A,Term,C),
	addarg(ListArg,F,A,L1,L2).
	
buildarg(L,M,M,_,_):- var(L),!.
buildarg([],M,M,_,_):- !.
buildarg([F|Prev],L,T,A,ListArg):-
	addarg(ListArg,F,A,L,L2),
	buildarg(Prev,L2,T,A,ListArg).

concret_arg(0,_,P,P,_,_).
concret_arg(A,Term,Prev,List,List2,Seen):-
	arg(A,Term,Arg1),
	concrete(Arg1,ListArg1,[],Seen),
%	concrete(Arg1,ListArg1,List2,Seen),
        buildarg(Prev,NewPrev,List2,A,ListArg1),
	A1 is A -1,
	concret_arg(A1,Term,NewPrev,List,List2,Seen).
	

defined_type_symbol(Type,Def):-
	em_defined_type_symbol(Type,Def).
defined_type_symbol(Type,Def):-
	equiv_type(Type,Type1),
	em_defined_type_symbol(Type1,Def).


concrete(Type,List1,List2,Seen):-
	defined_type_symbol(Type,Def),!,
	( 
	    member(Type,Seen) ->
	    fail
	;
	    concret_def(Def,List1,List2,[Type|Seen])
	).
concrete(Type,List1,List2,Seen):-
	compound_pure_type_term(Type,Term,F,A),!,
	functor(Seed,F,A),
	concret_arg(A,Term,[Seed|List2],List1,List2,Seen).
%	append(List,List2,List1).
concrete(^(Term),[Term|List],List,_).
concrete(Term,[Term|List],List,_):- number(Term).
concrete(Term,[Term|List],List,_):- Term = [_|_].
concrete(Term,[Term|List],List,_):- Term = [].
	

terms_concrete(Var,ASub,List):-
	get_type(Var,ASub,Type),
	concrete(Type,List,[],[]).
	

%------------------------------------------------------------------%
:- pred terms_compute_lub(+ListASub,-Lub): list(absu) * absu # 
" It computes the least upper bound of a set of abstract
substitutions.  For each two abstract substitutions @var{ASub1} and
@var{ASub2} in @var{ListASub}, obtaining the lub is foreach X:Type1 in
@var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion is in Lub, and
TypeUnion is the deterministic union of Type1 an Type2.  ".

terms_compute_lub([ASub1,ASub2|Rest],Lub):-
	terms_compute_lub_el(ASub1,ASub2,ASub3_tmp),
	( current_pp_flag(type_precision,defined) ->
	  terms_naive_widen(ASub3_tmp,ASub3)
	; ASub3 = ASub3_tmp
	),
	terms_compute_lub([ASub3|Rest],Lub).
terms_compute_lub([ASub],ASub).

%------------------------------------------------------------------%

terms_compute_lub_el('$bottom',ASub,ASub):- !.
terms_compute_lub_el(ASub,'$bottom',ASub):- !.
terms_compute_lub_el(ASub1,ASub2,ASub3):-
	ASub1 == ASub2, !,
	ASub3 = ASub2.
terms_compute_lub_el(ASub1,ASub2,ASub3):-
	terms_lub0(ASub1,ASub2,ASub3).

terms_lub0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
	X==Y,
	type_union(T1,T2,T3,[]),
	terms_lub0(ASub1,ASub2,ASub3).
terms_lub0([],[],[]).


%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%-----------------------Deterministic Union --------------------------%	 
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
:- pred type_union(+Type1,+Type2,-Type3,Seen) :
	pure_type_term * pure_type_term * pure_type_term * list #
"
@var{Type3} is the union of @var{Type1} and @var{Type2} and is defined
by a deterministic type rule.
 This is done as follows: 
@begin{itemize} 
@item if @var{Type1} is included in @var{Type2} the union is @var{Type2}.
@item if @var{Type2} is included in @var{Type1} the union is @var{Type1}.
@item Otherwise, if (Type1,Type2,Type3) in @var{Seen} (i.e. the union
of Type1 and Type2 was previously evaluated) the union is
@var{Type3}. Otherwise, it will create a new type simbol Type3, merge
the definitions of Type1 and Type2 in a deterministic way, unfold the
new definition, and insert the new rule.
@end{itemize}
".

type_union(Type1,Type2,Type3,_Seen):-
	dz_type_included(Type1,Type2),!,
	Type3=Type2.
type_union(Type1,Type2,Type3,_Seen):-
	dz_type_included(Type2,Type1),!,
	Type3=Type1.
type_union(Type1,Type2,Type3,Seen):-
	(
	    member((Type1,Type2,Type3),Seen) -> true
	;
	    new_type_symbol(Type3),
	    get_typedefinition(Type1,Def1),
	    get_typedefinition(Type2,Def2),
	    sort(Def1,Def1_s),sort(Def2,Def2_s),
	    deterministic_union(Def1_s,Def2_s,Def,[(Type1,Type2,Type3)|Seen]),
	    unfold(Type3,Def,UDef),	    % change unfold test test
	    sort(UDef,UDef_s),
	    insert_rule(Type3,UDef_s)
	).

:- pred get_typedefinition(+Type,-Def): pure_type_term * list(pure_type_term) #
"
Return the definition of @var{Type} if Type is a type simbol. Otherwise return [Type].
".

get_typedefinition(Type,Def):-
       ( 
	   rule_type_symbol(Type) ->
%	   em_defined_type_symbol(Type, Defin) -> 
	   get_type_definition(Type,Def)
%	   Def = Defin
       ;
	   Def = [Type]
       ).

:- pred unfold(+TS,+Def,-UDef)
	: term * list(pure_type_term) * list(pure_type_term) #
"
Each type term in Def is unfolded in the following way:
@begin{itemize} 
@item if it is a type symbol and its definition consists of only one
type term, replace the type symbol by the type term.
@item if it is a compound pure type term return the same compound term
with its arguments unfolded.
@item otherwise the type term is unchanged.
@end{itemize}
".

unfold(TypSymbol,Defin,OuDefin):-
	unfold_type_union_1(Defin, [TypSymbol], [], TmpDefin),
	reverse(TmpDefin, OuDefin).

% unfold([],[]).
% unfold([Type|Def],[UnfType|Def1]):-
% 	unfold0(Type,UnfType,[]),
%  	unfold(Def,Def1).

% unfold0(Type,UnfType,Seen):-
%  	em_defined_type_symbol(Type, Defin),!,
%  	( 
%  	    member(Type,Seen) -> UnfType = Type
%  	;
%  	    ( 
%  		Defin = [OneTerm] -> unfold0(OneTerm,UnfType,[Type|Seen])
%  	    ;
%  		UnfType = Type
%  	    )
%  	).
% unfold0(Type,UnfType,Seen):-
%  	compound_pure_type_term(Type,Term,Name,Arity),!,
%  	functor(NewTerm,Name,Arity),
%  	unfoldargs(Arity,Term,NewTerm,Seen),
%  	construct_compound_pure_type_term(NewTerm,UnfType).
% unfold0(Type,Type,_Seen).	    

% unfoldargs(0,_,_,_).
% unfoldargs(N,Term,NewTerm,Seen):-
% 	arg(N,Term,Arg),
% 	unfold0(Arg,NArg,Seen),
% 	arg(N,NewTerm,NArg),
%  	N1 is N - 1,
%  	unfoldargs(N1,Term,NewTerm,Seen).


:- pred deterministic_union(+Def1,+Def2,-Def,+Seen):
list(pure_type_term) * list(pure_type_term) * list(pure_type_term) *
list #
"
@var{Def1} and @var{Def2} are two sorted lists of type terms with
compound type terms of different functor/arity. @var{Def1} is the
merge of both definitions, if two compound type terms have the same
functor/arity, both are replaced by a new compound type terms whose
arguments are the deterministic union of the formers.
".

deterministic_union([],D,D,_Seen):- !.
deterministic_union(D,[],D,_Seen):- !.
deterministic_union([TermType1|Def1],[TermType2|Def2],[TermType|Def],Seen):-
	compare(Order,TermType1,TermType2),
	deterministic_union0([TermType1|Def1],[TermType2|Def2],Order,TermType,Def,Seen).


deterministic_union0([TermType1|Def1],[_TermType2|Def2],=,TermType1,Def,Seen):-
	!,
	deterministic_union(Def1,Def2,Def,Seen).
deterministic_union0([TermType1|Def1],[TermType2|Def2],_Order,TermType,Def,Seen):-
	compound_pure_type_term(TermType1,Term1,Name,Arity),
	compound_pure_type_term(TermType2,Term2,Name,Arity),!,
	functor(Term,Name,Arity),
	obtain_new_term(Arity,Term1,Term2,Term,Seen),
	construct_compound_pure_type_term(Term,TermType),
	deterministic_union(Def1,Def2,Def,Seen).
deterministic_union0([TermType1|Def1],[TermType2|Def2],<,TermType1,Def,Seen):-
	deterministic_union(Def1,[TermType2|Def2],Def,Seen).
deterministic_union0([TermType1|Def1],[TermType2|Def2],>,TermType2,Def,Seen):-
	deterministic_union([TermType1|Def1],Def2,Def,Seen).


obtain_new_term(0,_,_,_,_).
obtain_new_term(N,Term1,Term2,Term,Seen):-
	arg(N,Term1,Arg1),
	arg(N,Term2,Arg2),
	type_union(Arg1,Arg2,Arg,Seen),
	arg(N,Term,Arg),
	N1 is N - 1,
	obtain_new_term(N1,Term1,Term2,Term,Seen).
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%----------------------END-Deterministic-Union------------------------%	 
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 




%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%--------------------------WIDENING----------------------------------%
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
normalize_type_asub(Prime,Prime). % needed for plai framework

terms_widencall(Prime0,Prime1,NewPrime):-
	terms_widen(Prime0,Prime1,NewPrime).
%	display(terms_widencall),nl,
%	terms_compute_lub_el(Prime0,Prime1,Prime),
%	shortening(Prime,NewPrime).


:- pred terms_widen(+Prime0,+Prime1,-NewPrime):
absu * absu * absu #
"
Induction step on the abstract substitution of a fixpoint.
@var{Prime0} corresponds to non-recursive and @var{Prime1} to
recursive clauses.  @var{NewPrime} is the result of apply one widening
operation to the least upper bound of the formers.  Widening
operations implemented are ``shortening'' and ``restricted shortening''
@cite{gallagher-types-iclp94,Saglam-Gallagher-95} .  ".

terms_widen(Prime0,Prime1,NewPrime):-
	terms_compute_lub_el(Prime0,Prime1,Prime),
%	terms_naive_widen(Prime,NewPrime)
%       henten(Prime0,Prime,NewPrime).
	shortening(Prime,NewPrime).
%	jungle(Prime,NewPrime).
%       widen(Prime0,Prime,NewPrime)


terms_naive_widen('$bottom','$bottom').
terms_naive_widen([],[]).
terms_naive_widen([X:T1|Prime],[X:T|NewPrime]):-
	terms_naive_ewiden_el(T1,T),
	terms_naive_widen(Prime,NewPrime).

terms_naive_ewiden_el(T,T2):-
	get_module_types(List),
	contain_this_type(List,T,Ret),
	minimaltype(Ret,T2),!.

%% henten('$bottom','$bottom','$bottom').
%% henten('$bottom',Prime,Prime).
%% henten([],[],[]).
%% henten([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
%% 	hentenwid(T1,T2,T,[],[],no),
%% 	henten(Prime0,Prime,NewPrime).
%% 
%% samepf([],[]).
%% samepf([T|Def],[T2|Def2]):-
%% 	samefunctor(T,T2),!,
%% 	samepf(Def,Def2).
%% 
%% samefunctor(T,T).
%% samefunctor(T,T2):-
%% 	compound_pure_type_term(T,_Term,F,A),!,
%% 	compound_pure_type_term(T2,_Term2,F,A).
%% 	
%% hentenancestor(T2,Seen,NT):-
%% 	member((T,NT),Seen),
%% 	dz_type_included(T2,T).
%% 	
%% hentendef([],[],[],_,_,_).
%% hentendef([T1|Def1],[T2|Def],[T|NewDef],Seen,Prev,Flag):-
%% 	hentenwid(T1,T2,T,Seen,Prev,Flag),
%% 	hentendef(Def1,Def,NewDef,Seen,Prev,Flag).
%% 
%% hentenwid_arg(0,_Term1,_Term2,_NewTerm,_Seen,_Prev,_Flag).
%% hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag):-
%% 	arg(A,Term2,Arg2),
%% 	arg(A,Term1,Arg1),
%% 	hentenwid(Arg1,Arg2,NewArg,Seen,Prev,Flag),	
%% 	arg(A,NewTerm,NewArg),
%% 	A1 is A - 1,
%% 	hentenwid_arg(A1,Term1,Term2,NewTerm,Seen,Prev,Flag).
%% 
%% hentenwid(T1,T2,T,Seen,Prev,Flag):-
%% 	em_defined_type_symbol(T2,Def),!,
%% 	(
%% 	    member((T2,T),Seen) -> true
%% 	;
%% 	    (
%% 		(
%% 		    em_defined_type_symbol(T1,Def1) ->
%% 		    NewPrev = [T1|Prev],
%% 		    (
%% 			(Flag == yes;member(T1,Prev)) ->
%% 			 NewFlag = yes
%% 		    ;
%% 			NewFlag = Flag
%% 		    )
%% 		;
%% 		    NewPrev = Prev,
%% 		    Def1 = [T1],
%% 		    NewFlag = Flag
%% 		),
%% 		(
%% 		    (samepf(Def,Def1),NewFlag = no) ->
%% 		     new_type_symbol(NT),
%% 		     hentendef(Def1,Def,NewDef,[(T2,NT)|Seen],NewPrev,NewFlag),
%% 		     (
%% 			 Def == NewDef ->
%% 			 T = T2
%% 		     ;
%% 			 T = NT,
%% 			 unfold(T,NewDef,NewDef_u),
%% 			 sort(NewDef_u,NewDef_u_s),
%% 			 insert_rule(T,NewDef_u_s)
%% 		     )
%% 		;
%% 		    (
%% 			hentenancestor(T2,Seen,T) ->
%% 			true
%% 		    ;
%% 			T = T2
%% 		    )
%% 		)
%% 	    )
%% 	).
%% 
%% hentenwid(T1,T2,T,Seen,Prev,Flag):-
%% 	compound_pure_type_term(T2,Term2,F,A),!,
%% 	compound_pure_type_term(T1,Term1,F,A),
%% 	functor(NewTerm,F,A),
%% 	hentenwid_arg(A,Term1,Term2,NewTerm,Seen,Prev,Flag),
%% 	construct_compound_pure_type_term(NewTerm,T).
%% 
%% hentenwid(_T1,T2,T2,_Seen,_Prev,_Flag).	
%% 	
%% 
%% widen('$bottom','$bottom','$bottom').
%% widen('$bottom',Prime,Prime).
%% widen([],[],[]).
%% widen([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
%% 	widen_el(T1,T2,T),
%% 	widen(Prime0,Prime,NewPrime).
%% 
%% widen_el(T1,T2,T):-
%% 	em_defined_type_symbol(T1,Def),!,
%% 	sort(Def,Def_s),
%% 	new_replace(T2,T1,Def_s,T2,T,[]).
%% 
%% %widen_el(_,T,T).
%% widen_el(T1,T2,T):-
%% 	new_replace(T2,_,[T1],T2,T,[]).
%% 
%% new_replace(T,TPrime,_,NewNode,NewNode,_):- T==TPrime,!.
%% new_replace(T,TPrime,DefPrime,NewNode,NT,Seen):-
%% 	em_defined_type_symbol(T,Def),!,
%% 	sort(Def,Def_s),
%% 	( 
%% 	    ord_subset_diff(DefPrime,Def_s,DiffDef) -> 
%% 	    insert(DiffDef,NewNode,NewDef),
%% 	    new_type_symbol(NewT), 
%% 	    unfold(NewT,NewDef,NewDef_u),	    
%% 	    sort(NewDef_u,NewDef_u_s),
%% % do we also have to replace in NewDef?
%% % 	    ( 
%% % 		member(T,Seen) -> NT = T
%% % 	    ;
%% %		new_replace_def(NewDef_u_s1,NewDef_u_s,TPrime,DefPrime,NewNode,[T|Seen]),
%% % do we also have to replace in NewDef?		    
%% 		
%%             (
%% 		NewDef_u_s == Def_s -> 
%% 		( 
%% 		    member(T,Seen) -> NT = T
%% 		;
%% 		new_replace_def(DiffDef,DiffDef2,TPrime,DefPrime,NewNode,[T|Seen]),
%% 		append(DefPrime,DiffDef2,Ddef),
%% 		NT = NewT,
%% 		replace_def(Ddef,Ddef2,T,TPrime,NT,Seen), %Seen
%% 		unfold(NT,Ddef2,Ddef_u),
%% 		sort(Ddef_u,Ddef_u_s),
%% 		insert_rule(NT,Ddef_u_s)
%% 		)
%% 		
%% 	    ;
%% 		NT = NewT,
%% 		replace_def(NewDef_u_s,NDef,T,T,NT,Seen), % Seen
%% 	        unfold(NT,NDef,NDef_u),	
%% 		sort(NDef_u,NDef_u_s),    
%% 		insert_rule(NT,NDef_u_s) % do we also have to replace in NewDef?
%% 	    )
%% % ) % do we also have to replace in NewDef?		    
%% 	;
%% 	    ( 
%% 		member(T,Seen) -> NT = T
%% 	    ;
%% 		new_replace_def(Def_s,NewDef,TPrime,DefPrime,NewNode,[T|Seen]),
%% 		(
%% 		    Def_s == NewDef -> 
%% 		    NT = T
%% 		;
%% 		    new_type_symbol(NT),
%% 		    replace_def(NewDef,NewDef2,T,T,NT,Seen), % Seen
%% 		    unfold(NT,NewDef2,NewDef2_u),
%% 		    sort(NewDef2_u,NewDef2_u_s),
%% 		    insert_rule(NT,NewDef2_u_s)
%% 		)
%% 	    )
%% 	).
%% new_replace(T,TPrime,DefPrime,NewNode,NT,Seen):-
%% 		compound_pure_type_term(T,Term,F,A),!,
%% 	functor(NewTerm,F,A),
%% 	new_replace_arg(A,Term,NewTerm,TPrime,DefPrime,NewNode,Seen),
%% 	construct_compound_pure_type_term(NewTerm,NT).
%% new_replace(T,_,[T],New,New,_):- !.	  
%% new_replace(T,_,_,_,T,_).	  
%% 
%% new_replace_def([],[],_,_,_,_).
%% new_replace_def([T|Def],[NT|NewDef],TPrime,DefPrime,NewNode,Seen):-
%% 	new_replace(T,TPrime,DefPrime,NewNode,NT,Seen),
%% 	new_replace_def(Def,NewDef,TPrime,DefPrime,NewNode,Seen).
%% 
%% new_replace_arg(0,_,_,_,_,_,_).
%% new_replace_arg(A,Term,NewTerm,TPrime,DefPrime,NewNode,Seen):-
%% 	arg(A,Term,Arg),
%% 	new_replace(Arg,TPrime,DefPrime,NewNode,NewArg,Seen),
%% 	arg(A,NewTerm,NewArg),
%% 	A1 is A - 1,
%% 	new_replace_arg(A1,Term,NewTerm,TPrime,DefPrime,NewNode,Seen).

shortening('$bottom','$bottom').
shortening([],[]).
shortening([X:T1|Asub1],[X:T2|Asub2]):-
	shortening_el(T1,T2),
	shortening(Asub1,Asub2).

shortening_el(T,ST):- 
	find_path(T,Anc,N,[],1,Flag),!,
	(
	    Flag == included ->
	    Node = Anc
	;
	    type_union(Anc,N,Node,[])
	),
	em_defined_type_symbol(Node, Defin),
	new_type_symbol(NewNode),
	replace_def(Defin,NewDefin,N,Anc,NewNode,[]),
        unfold(NewNode,NewDefin,NewDefin_u),	
	sort(NewDefin_u,NewDefin_u_s),
	insert_rule(NewNode,NewDefin_u_s),
	replace(T,Anc,Anc,NewNode,NT,[]),
	shortening_el(NT,ST).
shortening_el(T,T).

replace(T,T1,_,NewNode,NewNode,_):- T == T1,!.
replace(T,_,T1,NewNode,NewNode,_):- T == T1,!.
replace(T,T1,T2,NewNode,NT,Seen):-
	em_defined_type_symbol(T,Def),!,
	(
	    member(T,Seen) -> NT = T
	;
	    replace_def(Def,NewDef,T1,T2,NewNode,[T|Seen]),
	    ( 
		Def == NewDef ->
		NT = T
	    ;
		new_type_symbol(NT),		
		replace_def(NewDef,NewDef2,T,T,NT,Seen),  %  Seen
		unfold(NT,NewDef2,NewDef2_u), 
		sort(NewDef2_u,NewDef2_u_s),
		insert_rule(NT,NewDef2_u_s)
	    )
	).
% replace(T,T1,T2,NewNode,NT,Seen):-
% 	em_defined_type_symbol(T,Def),!,
% 	(
% 	    member((T,NT),Seen) -> true
% 	;
% 	    new_type_symbol(NT),
% 	    replace_def(Def,NewDef,T1,T2,NewNode,[(T,NT)|Seen]),
% 	    unfold(NT,NewDef,NewDef_u), % test test test test
% 	    insert_rule(NT,NewDef_u)
% 	).
replace(T,T1,T2,NewNode,NT,Seen):-
	compound_pure_type_term(T,Term,F,A),!,
	functor(NewTerm,F,A),
	replace_arg(A,Term,NewTerm,T1,T2,NewNode,Seen),
	construct_compound_pure_type_term(NewTerm,NT).
replace(T,_,_,_,T,_).

replace_def([],[],_,_,_,_).
replace_def([T|Def],[NT|NewDef],T1,T2,NewNode,Seen):-
	replace(T,T1,T2,NewNode,NT,Seen),
	replace_def(Def,NewDef,T1,T2,NewNode,Seen).

replace_arg(0,_,_,_,_,_,_).
replace_arg(A,Term,NewTerm,T1,T2,NewNode,Seen):-
	arg(A,Term,Arg),
	replace(Arg,T1,T2,NewNode,NewArg,Seen),
	arg(A,NewTerm,NewArg),
	A1 is A - 1,
	replace_arg(A1,Term,NewTerm,T1,T2,NewNode,Seen).

find_path(T,Anc,N,Seen,Depth,Flag):-
	em_defined_type_symbol(T,Def),!,
	prlb(T,Lab),
	current_pp_flag(depth,Depthk),
	(
	    (member((Lab,Anc),Seen),((Depthk =\= 0,Depth >= Depthk);dz_type_included(T,Anc))) ->
	    (
		T == Anc -> fail
	    ;
		N = T,
		(
		    (Depthk =\= 0,Depth >= Depthk) -> Flag = notincluded
		;
		    Flag = included
		)
	    )
	;
	    NewDepth is Depth + 1,
	    find_path_def(Def,Anc,N,[(Lab,T)|Seen],NewDepth,Flag)
	).
find_path(T,Anc,N,Seen,Depth,Flag):-
	compound_pure_type_term(T,Term,_F,A),!,
	NewDepth is Depth + 1,	
	find_path_arg(A,Term,Anc,N,Seen,NewDepth,Flag).

find_path_def([T|_Def],Anc,N,Seen,Depth,Flag):-
	find_path(T,Anc,N,Seen,Depth,Flag),!.
find_path_def([_T|Def],Anc,N,Seen,Depth,Flag):-
	find_path_def(Def,Anc,N,Seen,Depth,Flag).

find_path_arg(0,_,_,_,_,_,_):- !,fail.
find_path_arg(A,Term,Anc,N,Seen,Depth,Flag):-
	arg(A,Term,Arg),
	find_path(Arg,Anc,N,Seen,Depth,Flag),!.
find_path_arg(A,Term,Anc,N,Seen,Depth,Flag):-
	A1 is A - 1,
	find_path_arg(A1,Term,Anc,N,Seen,Depth,Flag).

%% :- pred jungle(+Prime,-NewPrime): absu * absu #
%% "
%% A @em{Type Jungle} is a type graph with at most one node for each
%% function symbol. It can be used as a finite subdomain of type
%% graphs. This predicate converts a type graph into the finite domain of
%% type jungles.
%% The main component is the predicate @tt{build_type_jungle}. 
%% ".
%% 
%% jungle('$bottom','$bottom').
%% jungle([],[]).
%% jungle([X:T1|Asub1],[X:T2|Asub2]):-
%% 	jungle_el(T1,T2),
%% 	jungle(Asub1,Asub2).
%% 
%% jungle_el(T,T):-
%% 	top_type(T),!.
%% jungle_el(T,T):-
%% 	base_type_symbol(T),!.
%% jungle_el(T,JT):-
%% 	prlb(T,Lab),
%% 	build_type_jungle(Lab,JT,[],T,Rules,[]),
%% 	insert_rules(Rules).
%% 
%% insert_rules([]).
%% insert_rules([(S,Def)|Rules]):-
%% 	unfold(S,Def,Def_u), % test test test test	
%% 	sort(Def_u,Def_u_s),
%% 	insert_rule(S,Def_u_s),
%% 	insert_rules(Rules).
%% 
%% :- pred build_type_jungle(+Lab,-JT,+Nodes,+Type,+Rules,+TailRules): list * pure_type_term * list * pure_type_term * list * list #
%% "
%% It takes a set @var{Lab} of funtion symbols and will return a node
%% (type term @var{JT}) that is an upper bound of all funtor nodes in the type
%% graph labeled with one of the function symbols in @var{Lab}. If there
%% is already a node for this set of functors then it is looked up in
%% @var{Nodes} and returned directly. Otherwise there are three cases:
%% @begin{itemize}
%% @item if @var{Lab} is a singleton @{JT@} and JT is not a functor/arity element, return Jt.
%% @item if @var{Lab} is a singleton @{F/A@} return a new compound pure
%% type term that should be an upper bound of all nodes in the type graph
%% with label F. It is done by the predicate @tt{build_args} by calling
%% recursively @tt{build_type_jungle} for each argument.
%% @item if on the other hand @var{Lab} is not a singleton, it return a
%% new type symbol and create a new type rule which definition is built
%% by the predicate @tt{build_def} by calling recursively
%% @tt{build_type_jungle} for each element in @var{Lab}.
%% @end{itemize}
%% ".
%% 
%% 
%% build_type_jungle(Lab,JT,Nodes,_Type,Rules,Rules):-
%% 	member((Lab,JT),Nodes),!.
%% build_type_jungle([F/A],JT,Nodes,Type,Rules,TailRules):-
%% 	functor(NewTerm,F,A),
%% 	construct_compound_pure_type_term(NewTerm,JT),
%% 	build_args(A,NewTerm,F,A,Type,[([F/A],JT)|Nodes],Rules,TailRules).
%% build_type_jungle([JT],JT,_Nodes,_Type,Rules,Rules).
%% build_type_jungle(Lab,JT,Nodes,Type,[(JT,Def)|Rules],TailRules):-
%% 	new_type_symbol(JT),
%%         build_def(Lab,Def,[(Lab,JT)|Nodes],Type,Rules,TailRules).
%% %	insert_rule(JT,Def).
%% 
%% build_args(0,_,_,_,_,_,R,R).
%% build_args(N,Term,F,A,Type,Nodes,Rules,TailRules):-
%% 	labels_of_functor(Type,F,A,N,Lab),
%% 	arg(N,Term,JT),
%% 	build_type_jungle(Lab,JT,Nodes,Type,Rules,Rules1),
%% 	N1 is N - 1,
%% 	build_args(N1,Term,F,A,Type,Nodes,Rules1,TailRules).
%% 
%% build_def([],[],_,_,R,R).
%% build_def([L|Lab],[D|Def],Nodes,Type,Rules,TailRules):-
%% 	build_type_jungle([L],D,Nodes,Type,Rules,Rules1),
%% 	build_def(Lab,Def,Nodes,Type,Rules1,TailRules).
%% 
%% 
%% :- pred labels_of_functor(+Type,+Functor,+Arity,+I,-Lab): pure_type_term * atom * int * 
%% int * list #
%% "
%% It obtains a list of functor/arity terms or basic type terms which are
%% the principal function symbols or basic type terms of the @var{I}th
%% argument of any compound type term with @var{Functor}/@var{Arity}
%% function symbol in the type graph @var{Type}. 
%% There are three cases:
%% @begin{itemize}
%% @item if @var{Type} is a type symbol and it is alredy in the set @var{Seen} it returns the empty set. Otherwise it returns the set of labels of each type term in the definition.
%% @item if @var{Type} is a compound type term with @var{Functor}/@var{Arity}
%% function symbol it obtains the @var{I}th argument and returns the principal labels of it.
%% @item Otherwise it returns the empty set.
%% @end{itemize}
%% ".
%% 
%% labels_of_functor(Type,Functor,Arity,I,Lab):-
%% 	labels_of_functor0(Type,Functor,Arity,I,L,[],[]),
%% 	sort(L,Lab).
%% 
%% labels_of_functor0(T,F,A,I,Lab,L,Seen):-
%% 	em_defined_type_symbol(T,Def),!,
%% 	( 
%% 	    member(T,Seen) ->
%% 	    Lab = L
%% 	;
%% 	    labels_of_functorlist(Def,F,A,I,Lab,L,[T|Seen])
%% 	).	
%% 
%% labels_of_functor0(T,F,A,I,Lab,L,_Seen):-
%% 	compound_pure_type_term(T,Term,F,A),!,
%% 	arg(I,Term,Arg),
%% 	prlb0(Arg,Lab,L1,[]),
%% 	labels_of_functor0(Arg,F,A,I,L1,L,_Seen).
%% 
%% labels_of_functor0(_T,_F,_A,_I,L,L,_Seen).
%% 
%% labels_of_functorlist([],_F,_A,_I,L,L,_Seen).
%% labels_of_functorlist([T|Rest],F,A,I,Lab,L,Seen):-
%% 	labels_of_functor0(T,F,A,I,Lab,L1,Seen),
%% 	labels_of_functorlist(Rest,F,A,I,L1,L,Seen).

:- pred prlb(+Type,-Lab): pure_type_term * list #
"
It obtains the principal labels of the type graph @var{Type}, i.e. the
sorted set of functor/arity terms or basic type terms which are the principal
function symbols or basic type terms of the type term @var{Type}.
".

prlb(T,Lab):-
	prlb0(T,L,[],[]),
	sort(L,Lab).
prlb0(T,Lab,L,Seen):-
	em_defined_type_symbol(T,Def),!,
	( 
	    member(T,Seen) ->
	    Lab = L
	;
	    prlblist(Def,Lab,L,[T|Seen])
	).
prlb0(T,[Name/Arity |L],L,_Seen):-
	compound_pure_type_term(T,_Term,Name,Arity),!.
prlb0(T,[T|L],L,_Seen).


prlblist([],L,L,_Seen).
prlblist([T|RestT],Lab,L,Seen):-
	prlb0(T,Lab,L1,Seen),
	prlblist(RestT,L1,L,Seen).
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%--------------------------END-WIDENING-------------------------------%
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

terms_init_abstract_domain([widen]) :-
	push_pp_flag(widen,on).

%------------------------------------------------------------------%
:- pred terms_call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo): term * callable * list * 
callable * term * list * absu * absu * extrainfo # 
"
It obtains the abstract substitution @var{Entry} which results from
adding the abstraction of the @var{Sg} = @var{Head} to @var{Proj},
later projecting the resulting substitution onto @var{Hv}.
 This is done as follows: 
@begin{itemize} 
@item If @var{Sg} and @var{Head} are identical up to renaming it is just  
 renaming @var{Proj} and adding the @var{Fv} 
@item Otherwise, it will 
 @begin{itemize} 
 @item obtain the abstract substitution from unifying @var{Sg} and @var{Head} calling ``unify_term_and_type_term'' 
 @item add to this abstract substituion the variables in Fv as term type. 
 @end{itemize} 
@end{itemize} 

The meaning of the variables is
@begin{itemize}
@item @var{Sg} is the subgoal being analysed. 
@item @var{Head} is the Head of the clause being analysed. 
@item @var{Fv} is a list of free variables in the body of the clause being considered. 
@item @var{Proj} is the abstract substitution @var{Call} projected onto @var{Sv}. 
@item @var{Entry} is the Abstract entry substitution (i.e. the abstract subtitution obtained after the abstract unification of @var{Sg} and @var{Head} projected onto @var{Hv} + @var{Fv}). 
@item @var{ExtraInfo}is a flag ``yes'' when no unification is required, i.e.,  
Entry=Proj upto names of vars. and ignoring Fv. It is ``no''
 if unification fails. 
@end{itemize}
".

terms_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
	variant(Sg,Head), !,
	Flag = yes,
	copy_term((Sg,Proj),(NewTerm,NewProj_u)),
	Head = NewTerm,
	terms_abs_sort(NewProj_u,NewProj),
	variables_are_variable_type(Fv,Free),
	merge(Free,NewProj,Entry).
terms_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,dummy):-
	unify_term_and_type_term(Head,Hv,Sg,Proj,TmpEntry), !,
	variables_are_variable_type(Fv,Tmp),
	merge(Tmp,TmpEntry,Entry).
terms_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- regtype extrainfo/1.

extrainfo(yes).
extrainfo(no).

:- pred variables_are_variable_type(+Fv,-ASub): list * absu # 
"at the moment it assigns the value top_type to the variables in @var{Fv}
 but in the future it must assign the value ``var''".


variables_are_variable_type(Fv,ASub):-
	variables_are_top_type(Fv,ASub).


%------------------------------------------------------------------%
:- pred terms_exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime): list
* list * callable * callable * absu * extrainfo * absu # 
"
It computes the prime abstract substitution @var{Prime}, i.e.  the result of 
 going from the abstract substitution over the head variables @var{Exit}, to
 the abstract substitution over the variables in the subgoal. It will:
 @begin{itemize}
@item If @var{Exit} is '$bottom', @var{Prime} will be also '$bottom'.               
@item If @var{ExtraInfo} = yes (@var{Head} and @var{Sg} identical up to renaming) it is just 
renaming Exit                                            %
@item  Otherwise: it will 
 @begin{itemize}                                                        
  @item projects @var{Exit} onto @var{Hv} obtaining @var{BPrime}. 
  @item obtain the abstract substitution from unifying @var{Sg} and @var{Head} calling 
         ``unify_term_and_type_term'' 
 @end{itemize}
@end{itemize}
".

terms_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
	Prime = '$bottom'.
terms_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
	terms_project(Hv,Exit,BPrime),
	copy_term((Head,BPrime),(NewTerm,NewPrime)),
	Sg = NewTerm,
	terms_abs_sort(NewPrime,Prime).	
terms_exit_to_prime(Sg,Hv,Head,Sv,Exit,_ExtraInfo,Prime):- 
	terms_project(Hv,Exit,BPrime),
	unify_term_and_type_term(Sg,Sv,Head,BPrime,Prime).
terms_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').


:- pred unify_term_and_type_term(+Term1,+Tv,+Term2,+ASub,-NewASub): callable * list * 
callable * absu * absu # 
"it unifies the term @var{Term1} to the type term @var{Term2}
obtaining the the abstract substitution TypeAss which is sorted and
projeted on @var{Tv}".



unify_term_and_type_term(Term1,Tv,Term2,ASub,NewASub):-
	copy_term((Term2,ASub),(TypeTerm,ASub0)),
	TypeTerm =.. [_|Types],
	Term1 =.. [_|Args],
	type_escape_term_list(Types,EscTypes),
	apply(ASub0),
	generate_a_type_assigment(EscTypes,Args,TypeAss),
	( 
	    member(_:bot,TypeAss) -> fail
	;
	    terms_abs_sort(TypeAss,ASub1),
	    terms_project(Tv,ASub1,NASub),
	    normal_asub(NASub,NewASub)
	).

normal_asub([],[]).
normal_asub([X:Type|ASub],[X:NType|NASub]):-
	normalize(Type,NType),
	normal_asub(ASub,NASub).

normalize(Type,NType):-
	nonvar(Type),
	(
	    number(Type);
	    Type = [] ;
	    Type = [_|_];
	    Type = ^(_) 
	),!,
        new_type_symbol(NType),
	insert_rule(NType,[Type]).
normalize(Type,Type).


:- pred apply(+ASub): absu # 
"it unifies the variables in the abstract
substitution @var{ASub} to his respective values".

apply([X:Term|ASub]):-
	X=Term,
	apply(ASub).
apply([]).



%------------------------------------------------------------------%
:- pred terms_project(+Vars,+Asub,-Proj): list * absu * absu # 
"@var{Proj} is the result of eliminating from @var{Asub} all
@var{X}:@var{Value} such that @var{X} is not in @var{Vars}".

terms_project(_,'$bottom',Proj):- 
	Proj = '$bottom'.
terms_project(Vars,ASub,Proj) :- 
	terms_project_aux(Vars,ASub,Proj).
%	displayq(proj(Proj)),nl.

terms_project_aux([],_,Proj):- !,
	Proj = [].
terms_project_aux(_,[],Proj):- !,
	Proj = [].
terms_project_aux([Head1|Tail1],[Head2:Type|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	terms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

terms_project_aux_(=,_,Tail1,HeadType,Tail2,[HeadType|Proj]) :-
	terms_project_aux(Tail1,Tail2,Proj).
terms_project_aux_(>,Head1,Tail1,_,[Head2:Type|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	terms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).



%------------------------------------------------------------------%
:- pred terms_abs_sort(+Asub,-Asub_s): absu * absu
# 
"It sorts the set of @var{X}:@var{Type} in @var{Asub} ontaining @var{Asub_s}".

terms_abs_sort('$bottom','$bottom'):- !.
terms_abs_sort(ASub,ASub_s):- sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- pred terms_extend(+Prime,+Sv,+Call,-Succ): absu * list * absu * absu # 
"
If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
 @var{Succ} is computed updating the values of @var{Call} with those
 in @var{Prime}".

terms_extend('$bottom',_Sv,_Call,'$bottom'):- !.
terms_extend(Prime,Sv,Call,Succ):-
	subtract_keys(Call,Sv,RestCall),
	merge(RestCall,Prime,Succ).

subtract_keys([K:_|Xs],Ks,Dict):-
	ord_member(K,Ks), !,
	subtract_keys(Xs,Ks,Dict).
subtract_keys([X|Xs],Ks,[X|Dict]):-
	subtract_keys(Xs,Ks,Dict).
subtract_keys([],_Ks,[]).


%------------------------------------------------------------------%
:- pred terms_less_or_equal(+ASub0,+ASub1): absu * absu # 
"Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
it's assumed the two abstract substitutions are defined on the same variables".


terms_less_or_equal('$bottom',_ASub):- !.
terms_less_or_equal(ASub1,ASub2):-
	ASub1 == ASub2, !.
terms_less_or_equal(ASub1,ASub2):-
	terms_less_or_equal0(ASub1,ASub2).

terms_less_or_equal0([X:T1|ASub1],[Y:T2|ASub2]):-
	X==Y,
	dz_type_included(T1,T2),
	terms_less_or_equal0(ASub1,ASub2).
terms_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- pred terms_glb(+ASub0,+ASub1,-Glb): absu * absu * absu # 
"@var{Glb} is the great lower bound of @var{ASub0} and @var{ASub1}".

terms_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
terms_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
terms_glb(ASub1,ASub2,ASub3):-
	ASub1 == ASub2, !,
	ASub3 = ASub2.
terms_glb(ASub1,ASub2,ASub3):-
	terms_glb0(ASub1,ASub2,ASub3), !.
terms_glb(_ASub1,_ASub2,'$bottom').

terms_glb0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
	X==Y,
	type_intersection_2(T1,T2,T3),!,
	( 
	    T3==bot -> fail 
	;
	    terms_glb0(ASub1,ASub2,ASub3)
	).
terms_glb0([],[],[]).

%------------------------------------------------------------------%
:- pred terms_unknown_entry(+Sg,+Qv,-Call): callable * list * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to   
 Call. In this domain the top value is X:term forall X in the set of variables".

terms_unknown_entry(_Sg,Vars,ASub):-
	variables_are_top_type(Vars,ASub).

:- pred terms_empty_entry(+Sg,+Vars,-Entry): callable * list * absu # "Gives the
""empty"" value in this domain for a given set of variables
@var{Vars}, resulting in the abstract substitution @var{Entry}. I.e.,
obtains the abstraction of a substitution in which all variables
@var{Vars} are unbound: free and unaliased. In this domain the empty
value is giving the variable type to each variable".

terms_empty_entry(_Sg,Vars,ASub):-
	variables_are_variable_type(Vars,ASub).


%------------------------------------------------------------------%
:- pred terms_unknown_call(+Sg,+Vars,+Call,-Succ): callable * list * absu * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to
 @var{Call}".

terms_unknown_call(_Sg,Vars,Call,Succ):-
	substitution(Call,CallVars,_),
	ord_subtract(Vars,CallVars,TopVars),
	variables_are_top_type(TopVars,ASub),
	merge(Call,ASub,Succ).

:- export(substitution/3).
substitution([],[],[]).
substitution([X:T|TypeAss],[X|Vars],[T|ListTypes]):-
	substitution(TypeAss,Vars,ListTypes).

:- export(variables_are_top_type/2).
:- pred variables_are_top_type(+Fv,-ASub): list * absu # 
"it assigns the value top_type to the variables in @var{Fv}
and return the abstract substitution @var{ASub} ".

variables_are_top_type([V|Fv],[V:Type|ASub]):-
	set_top_type(Type),
	variables_are_top_type(Fv,ASub).
variables_are_top_type([],[]).

%------------------------------------------------------------------%
:- pred terms_call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ): callable * 
list * callable * term * list * absu * absu * absu * absu # 
"Specialized version of call_to_entry + exit_to_prime + extend for facts".

terms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
	terms_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
	terms_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
	terms_extend(Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%
%			       BUILTINS
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% terms_special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)             %
% Type is a flag indicating what is the abstraction of builtin SgKey     %
% and to which variables Condvars of the goal Sg it affects.             %
%------------------------------------------------------------------------%

terms_special_builtin('!/0',_Sg,_Subgoal,id,[]).
terms_special_builtin('@=</2',_Sg,_Subgoal,id,[]).
terms_special_builtin('@>/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('@>=/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('@</2',_Sg,_Subgoal,id,[]).
terms_special_builtin('\\==/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('==/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('display/1',_Sg,_Subgoal,id,[]).
terms_special_builtin('get_code/1',Sg,_Subgoal,type(T),Condvars):-
        set_int_type(T),
	varset(Sg,Condvars).
% terms_special_builtin('integer/1',Sg,_Subgoal,type(T),Condvars):-
%         set_int_type(T),
% 	varset(Sg,Condvars).
terms_special_builtin('atom/1',Sg,_Subgoal,type(T),Condvars):-
        set_atom_type(T), % no, it is atom or num type
	varset(Sg,Condvars).
terms_special_builtin('atomic/1',Sg,_Subgoal,type(T),Condvars):-
        set_atom_type(T), % no, it is atom or num type
	varset(Sg,Condvars).
terms_special_builtin('var/1',_Sg,_Subgoal,id,[]).
	% set_top_type(T),
	% varset(Sg,Condvars).
terms_special_builtin('nonvar/1',_Sg,_Subgoal,id,[]).
	% set_top_type(T),
	% varset(Sg,Condvars).
terms_special_builtin('ground/1',_Sg,_Subgoal,id,[]).
	% set_top_type(T),
	% varset(Sg,Condvars).
% terms_special_builtin('float/1',Sg,_Subgoal,type(T),Condvars):-
% 	set_float_type(T),
% 	varset(Sg,Condvars).
% terms_special_builtin('number/1',Sg,_Subgoal,type(T),Condvars):-
% 	set_numeric_type(T),
% 	varset(Sg,Condvars).
terms_special_builtin('fail/0',_Sg,_Subgoal,bot,[]).
terms_special_builtin('true/0',_Sg,_Subgoal,id,[]).
terms_special_builtin('nl/0',_Sg,_Subgoal,id,[]).
terms_special_builtin('repeat/0',_Sg,_Subgoal,id,[]).
%
terms_special_builtin('erase/1',Sg,_Subgoal,type(T),Condvars):-
	set_top_type(T),
	varset(Sg,Condvars).
%
terms_special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
	terms_very_special_builtin(Key).

terms_very_special_builtin('=/2').

%------------------------------------------------------------------------%
% terms_success_builtin(+Type,+Sv_uns,+Condvars,+Call,-Succ)             %
% Depending on Type it computes the abstraction of a builtin affecting   %
% variables Condvars and having variables Sv_uns with call subs. Call.   %
%------------------------------------------------------------------------%

terms_success_builtin(id,_Sv_uns,_Condvars,Call,Call).
terms_success_builtin(bot,_Sv_uns,_Condvars,_Call,'$bottom').
terms_success_builtin(type(T),_Sv_uns,Condvars,Call,Succ):-
	keys_same_value(Condvars,T,Prime),
	terms_extend(Prime,Condvars,Call,Succ).
terms_success_builtin(Key,_Sv_uns,_Condvars,Call,Call):-
	warning_message("the builtin key ~q is not defined",[Key]).

keys_same_value([K|Ks],V,[K:V|ASub]):-
	keys_same_value(Ks,V,ASub).
keys_same_value([],_V,[]).

%------------------------------------------------------------------------%
% terms_call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)        %
% Same as above but for each particular builtin.                         %
%------------------------------------------------------------------------%



precondition_builtin('is/2',(X is _Y)):-
	(var(X);number(X)).
precondition_builtin(_Key,_).

postcondition_builtin('list/1',list(X1),Bv,Exit):-
         TX = list,
	 Exit_u = [X1:TX],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).

postcondition_builtin('num/1',num(X1),Bv,Exit):-
         set_numeric_type(TX),
	 Exit_u = [X1:TX],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).


postcondition_builtin('number/1',number(X1),Bv,Exit):-
         set_numeric_type(TX),
	 Exit_u = [X1:TX],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).

postcondition_builtin('float/1',float(X1),Bv,Exit):-
         set_float_type(TX),
	 Exit_u = [X1:TX],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).


postcondition_builtin('integer/1',integer(X1),Bv,Exit):-
         set_int_type(TX),
	 Exit_u = [X1:TX],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).

postcondition_builtin('int/1',int(X1),Bv,Exit):-
         set_int_type(TX),
	 Exit_u = [X1:TX],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).


postcondition_builtin('is/2',(X1 is Y1),Bv,Exit):-
	set_numexp_type(TY),
	set_numeric_type(TX),
	Exit_u = [X1:TX,Y1:TY],
	Bv_u = [X1,Y1],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).

postcondition_builtin('>/2',(X > Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	Exit_u = [X:TX,Y:TY],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).

postcondition_builtin('>=/2',(X >= Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	Exit_u = [X:TX,Y:TY],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).

postcondition_builtin('</2',(X < Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	Exit_u = [X:TX,Y:TY],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).

postcondition_builtin('=</2',(X =< Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	Exit_u = [X:TX,Y:TY],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).

postcondition_builtin('=\\=/2',(X =\= Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	Exit_u = [X:TX,Y:TY],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).

postcondition_builtin('=:=/2',(X =:= Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	Exit_u = [X:TX,Y:TY],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).


postcondition_builtin('functor/3',functor(X1,Y1,Z1),Vars,Exit):-
         set_int_type(TZ),
	 set_atom_type(TY),
	 set_top_type(TX),
	 Exit_u = [X1:TX,Y1:TY,Z1:TZ],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).

postcondition_builtin('arg/3',arg(X1,Y1,Z1),Vars,Exit):-
         set_int_type(TX),
	 set_top_type(TY),
	 set_top_type(TZ),
	 Exit_u = [X1:TX,Y1:TY,Z1:TZ],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).


postcondition_builtin('current_op/3',current_op(X1,Y1,Z1),Vars,Exit):-
	 set_top_type(TX),
	 set_atom_type(TY),
	 set_atom_type(TZ),
	 Exit_u = [X1:TX,Y1:TY,Z1:TZ],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).

postcondition_builtin('member/2',member(X1,Y1),Vars,Exit):-
	 set_top_type(TX),
	 set_top_type(TY), % TY = pt1,
	 Exit_u = [X1:TX,Y1:TY],
	 Vars_u = [X1,Y1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).


postcondition_builtin('=../2',X1=..Y1,Vars,Exit):-
	 set_top_type(TX),
	 set_top_type(TY), %TY = pt1,
	 Exit_u = [X1:TX,Y1:TY],
	 Vars_u = [X1,Y1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).

postcondition_builtin('numbervars/3',numbervars(X1,Y1,Z1),Vars,Exit):-
         set_int_type(TZ),
	 set_int_type(TY),
	 set_top_type(TX),
	 Exit_u = [X1:TX,Y1:TY,Z1:TZ],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).


postcondition_builtin('name/2',name(X1,Y1),Vars,Exit):-
	 set_atom_type(TX),
	 set_top_type(TY), % TY = pt1,
	 Exit_u = [X1:TX,Y1:TY],
	 Vars_u = [X1,Y1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).


terms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
	terms_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?

terms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
	(
	    precondition_builtin(Key,Sg) ->
	    postcondition_builtin(Key,Bg,Bv,Exit),
	    terms_exit_to_prime(Sg,Bv,Bg,Sv,Exit,no,Prime1),
	    terms_glb(Proj,Prime1,Prime),
	    terms_extend(Prime,Sv,Call,Succ)
	;
	    Succ = '$bottom'
	).
	    




%------------------------------------------------------------------------%
%			    USER INTERFACE
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% terms_input_user_interface(+InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)    %
% Obtains the abstract substitution ASub from user supplied information. %
%------------------------------------------------------------------------%

terms_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
        obtain_Asub_user(InputUser,ASub0),
	sort(ASub0,ASub_s),
	reduce_same_var(ASub_s,ASub1),
	substitution(ASub1,Vars,_),
	ord_subtract(Qv,Vars,TopV),
	variables_are_top_type(TopV,ASub2),
	sort(ASub2,ASub3),
	merge(ASub1,ASub3,ASub).

obtain_Asub_user([],[]):- !.
obtain_Asub_user([User|InputUser],[X:T|ASub]):-
	functor(User,T,_),
	arg(1,User,X),
	obtain_Asub_user(InputUser,ASub).

reduce_same_var([X:T|ASub],NewASub):-
	reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var([],[]).

reduce_same_var_([Y:TY|ASub],X,TX,NewASub):-
	reduce_same_var__(Y,TY,X,TX,ASub,NewASub).
reduce_same_var_([],X,T,[X:T]).

reduce_same_var__(Y,TY,X,TX,ASub,NewASub):-
	X == Y, !,
	type_intersection_2(TY,TX,T),
	reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var__(Y,TY,X,TX,ASub,[X:TX|NewASub]):-
	reduce_same_var_(ASub,Y,TY,NewASub).


% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
% 	Type=..[T,X],
% 	inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).


%------------------------------------------------------------------------%
% terms_asub_to_native(+ASub,+Qv,+Flag,-OutputUser,-Comps)               %
% Transforms abstract substitution ASub to user friendly format.         %
%------------------------------------------------------------------------%

terms_asub_to_native(ASub,_Qv,Flag,OutputUser,[]):-
	terms_asub_to_native0(ASub,OutputUser1),
	equiv_types(OutputUser1,OutputUser2),
	revert_types(OutputUser2,OutputUser,Symbols,[]),
	recorda_required_types_(Flag,Symbols).

terms_asub_to_native0([X:T|ASub],[Type|OutputUser]):-
	revert_type(T,X,Type),
	terms_asub_to_native0(ASub,OutputUser).
terms_asub_to_native0([],[]).

revert_type(T,X,Type):-
	type_symbol(T), !,
	functor(Type,T,1),
	arg(1,Type,X).

%	Type=..[T,X].
revert_type(T,X,(X=T)).      

revert_types([Type|OutputUser],[NType|NOutputUser],Symbols,Rest):-
	( 
	    Type = (_X = T) ->
	    symbols_of(T,Symbols,Rest1),
	    NType = Type
	;
	    functor(Type,S,AS),
	    arg(1,Type,X),
	    ( 
		param_type_symbol_renaming(PT,S) ->
		PT=..[N|Args],
		% parametric are not created: so not required
		% Symbols = [PT|Rest1],
		%pp% Symbols = Rest1,
		append(Args,Rest1,Symbols),
		NType=..[N,X|Args]
	    ;
		( 
		    internally_defined_type_symbol(S,AS) ->
		    Symbols = [S|Rest1],
		    new_internal_predicate(S,AS,NewS),
		    Type=..[S|Args],
		    NType=..[NewS|Args]
		;
		    Symbols = Rest1,
		    NType=Type
		)
	    )
	),
	revert_types(OutputUser,NOutputUser,Rest1,Rest).
revert_types([],[],S,S).

symbols_of(T,Symbols,Rest):-
	compound_pure_type_term(T,Term,_Name,Arity),!,
	symbols_of0(Arity,Term,Symbols,Rest).
symbols_of(T,[T|Rest],Rest).

symbols_of0(0,_Term,S,S).
symbols_of0(N,Term,Symbols,Rest):-
	arg(N,Term,T),
	symbols_of(T,Symbols,Rest1),
	N1 is N - 1,
	symbols_of0(N1,Term,Rest1,Rest).

recorda_required_types_(no,_Symbols).
recorda_required_types_(yes,Symbols):-
	recorda_required_types(Symbols).

%------------------------------------------------------------------------%
% terms_output_interface(+ASub,-Output)                                  %
% Transforms abstract substitution ASub to a more readible but still     %
% close to internal format.                                              %
%------------------------------------------------------------------------%

terms_output_interface(ASub,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

terms_collect_abstypes_abs([],Types,Types).
terms_collect_abstypes_abs([_:Type|Abs],Types0,Types):-
	insert(Types0,Type,Types1),
	terms_collect_abstypes_abs(Abs,Types1,Types).

terms_rename_abstypes_abs([],_,_,[]).
terms_rename_abstypes_abs([C|Call],Types,Names,[RenC|RenCall]):-
	C = Var:Type,
	RenC = Var:RenType,
	get_value_(Types,Type,RenType),
%	new_type_name(RenName),
%	insert_type_name(RenName,[],0),
	terms_rename_abstypes_abs(Call,Types,Names,RenCall).

get_value_(Rens,Type,RenType):-
	assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%

terms_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
terms_identical_abstract(ASub1,ASub2):-
	terms_identical_abstract0(ASub1,ASub2).

terms_identical_abstract0([X:Type0|ASub0],[Y:Type1|ASub1]):-
	X==Y,
        dz_equivalent_types(Type0,Type1),
	terms_identical_abstract0(ASub0,ASub1).
terms_identical_abstract0([],[]).
