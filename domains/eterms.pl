:- module(eterms,[                          
	eterms_call_to_entry/9,
	eterms_exit_to_prime/7,
	eterms_project/3,
	eterms_compute_lub/2,
	eterms_compute_lub_el/3,
	eterms_sort/2,
	eterms_extend/4,
	eterms_less_or_equal/2,
	eterms_glb/3,
	eterms_unknown_call/4,
	eterms_unknown_entry/2,
	eterms_empty_entry/2,
	eterms_call_to_success_fact/9,
	eterms_special_builtin/5,
	eterms_success_builtin/5,
	eterms_call_to_success_builtin/6,
	eterms_input_interface/4,
	eterms_input_user_interface/3,
	eterms_output_interface/2,
	eterms_asub_to_native/5,
	eterms_asub_to_native1/3,
	eterms_collect_abstypes/3,
	eterms_rename_abs/4,
	eterms_identical_abstract/2,
	eterms_widen/3,
	eterms_widencall/3,
	eterms_concret/3,
	eterms_part_conc/4,
	eterms_multi_part_conc/3,
	get_type/3,
	resetunion/0,
	type_union/3,
	make_deterministic/2, 
	make_determ_wide_rules/1,
	precondition_builtin/2,
	postcondition_builtin/4,
	keys_same_value/3,
	replaceintype/5,
	determinate_sel/3,
	getargtypes/6,
	eterms_arg_call_to_success/9
	     ],
	     [assertions,regtypes,basicmodes
	     ]).
:- use_package(dynamic). % TODO: datafacts should be enough

:- doc(title,"Types Abstract Domain").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").

:- doc(module,"

This module implements the abstract operations of a types domain
within the PLAI abstract interpretation framework.  An abstract
substitution is list of Var:Type elements, where Var is a variable and
Type is a pure type term @cite{Dart-Zobel}.

").

:- doc(bug,"A (imported?) goal which is a regtype should probably be treated
	as a builtin: its success is itself! Maybe do it in trust.pl?
        Otherwise, assertions trust list(X) => list(X) should be added.").

:- doc(bug, "2 commented out last clause of eterms_very_special_builtin. 
          This may lose precision, but otherwise type_eval produces wrong
          results").

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
	    get_type_name/2,
	    get_equiv_name/2,
	    insert_equiv_name/2,
	    retract_equiv_name/2,
	    insert_rule/2,
	    insert_type_name/3,
	    native_type_symbol/1,
	    new_type_name/1,
	    new_type_symbol/1,
	    pure_type_term/1,
	    recorda_required_types/1,
	    retract_rule/1,
	    retract_type_name/3,
	    rule_type_symbol/1,
	    set_atom_type/1,
	    set_float_type/1,
	    set_int_type/1,
	    set_numeric_type/1,
	    set_numexp_type/1,
	    set_top_type/1,
	    top_type/1,
	    type_escape_term_list/2,
	    type_intersection_2/3,
	    type_symbol/1,
	    unfold_type_union_1/4
	]).

% CiaoPP library
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(spec(unfold_builtins), 
	[can_be_evaluated/1]).

:- use_module(engine(io_basic)).
:- use_module(engine(hiord_rt), [call/1]).
:- use_module(engine(hiord_rt), ['$meta_call'/1]).

:- use_module(ciaopp(plai/apply_assertions_old), [apply_trusted0/7]).

% DTM: types for assertions
:- use_module(domain(gr), [extrainfo/1]).
:- use_module(domain(termsd), [concret/4,	revert_types/4]).

:- use_module(library(hiordlib), [maplist/2, maplist/3]).
:- use_module(library(messages)).
:- use_module(library(aggregates), [(^)/2, findall/4, setof/3]).
:- use_module(library(terms_vars), [varset/2, varsbag/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(lists), [
	    member/2,
	    append/3,
	    reverse/2,
	    dlist/3,
	    nth/3,
	    cross_product/2
	]).
:- use_module(library(sets), 
	[ 
	    merge/3,
	    ord_subtract/3,
	    insert/3,
	    ord_union/3,
	    ord_delete/3
	]).
:- use_module(library(assoc), [get_assoc/3]).
:- use_module(library(sort), [sort/2]).

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


get_type(Var,[NVar:(_,T0)|_],T):- Var == NVar, !, T = T0.
get_type(Var,[_|ASub],T):- 
	get_type(Var,ASub,T).


eterms_concret(Var,ASub,List):-
	get_type(Var,ASub,Type),
	concret(Type,List,[],[]).


%------------------------------------------------------------------%
:- pred eterms_compute_lub(+ListASub,-Lub): list(absu) * absu # 
" It computes the least upper bound of a set of abstract
substitutions.  For each two abstract substitutions @var{ASub1} and
@var{ASub2} in @var{ListASub}, obtaining the lub is foreach X:Type1 in
@var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion is in Lub, and
TypeUnion is the deterministic union of Type1 an Type2.  ".

eterms_compute_lub([ASub1,ASub2|Rest],Lub):-
	eterms_compute_lub_el(ASub1,ASub2,ASub3),
	!,
	eterms_compute_lub([ASub3|Rest],Lub).
eterms_compute_lub([ASub],ASub).

%------------------------------------------------------------------%

resetunion:-
	retractall(uniontriple(_,_,_)).


eterms_compute_lub_el('$bottom',ASub,ASub):- !.
eterms_compute_lub_el(ASub,'$bottom',ASub):- !.
eterms_compute_lub_el(ASub1,ASub2,ASub3):-
	ASub1 == ASub2, !,
	ASub3 = ASub2.
eterms_compute_lub_el(ASub1,ASub2,ASub3):-
	eterms_lub0(ASub1,ASub2,ASub3).


eterms_lub0([X:(N1_e,T1)|ASub1],[Y:(N2_e,T2)|ASub2],[X:(N2,T3)|ASub3]):-
	X==Y,
	get_canonical_name(N1_e,N1),
	get_canonical_name(N2_e,N2),
	( 
	    ( top_type(T2) ; top_type(T1) ) -> set_top_type(T3) 
	;
	    resetunion,
	    type_union(T1,T2,T3)
	),
%	lab_intersect(N1,N2),
	lab_intersect(N2,N1),
	eterms_lub0(ASub1,ASub2,ASub3).
eterms_lub0([],[],[]).


%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%-----------------------Deterministic Union --------------------------%	 
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 

:- dynamic(uniontriple/3).


:- pred type_union(+Type1,+Type2,-Type3): pure_type_term * pure_type_term * pure_type_term #
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



type_union(Type1,Type2,Type3):-
	    uniontriple(Type1,Type2,Type3),!.
type_union(Type1,Type2,Type3):-
	dz_type_included(Type1,Type2),!,
	Type3=Type2.
type_union(Type1,Type2,Type3):-
	dz_type_included(Type2,Type1),!,
	Type3=Type1.
type_union(Type1,Type2,Type3):-
	    new_type_symbol(Type3),
	    get_typedefinition(Type1,Def1),
	    get_typedefinition(Type2,Def2),
	    merge(Def1,Def2,Def_s),
	    insert_rule(Type3,Def_s),
	    get_native_type_symbols(Def_s,Def_n,Def_nnat),
	    union_of_native_types(Def_n,[],Def_natun),
	    asserta(uniontriple(Type1,Type2,Type3)),
	    make_deterministic(Def_nnat,Defnew), 
	    merge(Def_natun,Defnew,Def),
	    unfold(Type3,Def,UDef),	%  unfold test test
	    SDef = UDef,  %    simplify_def(UDef,SDef,Type3),
	    sort(SDef,SDef_s),
	    retract_rule(Type3),
	    insert_rule(Type3,SDef_s).




% simplify_def([],[],_Root).
% simplify_def([Type|UDef],[NType|SDef],Root):-
% 	compound_pure_type_term(Type,Term,F,A),!,
% 	functor(NewTerm,F,A),
%         simplify_arg(A,Term,NewTerm,Root),
% 	construct_compound_pure_type_term(NewTerm,NType),
%         simplify_def(UDef,SDef,Root).
% simplify_def([Type|UDef],[Type|SDef],Root):-
%         simplify_def(UDef,SDef,Root).

% simplify_arg(0,_Term,_NewTerm,_Root).
% simplify_arg(A,Term,NewTerm,Root):-
% 	arg(A,Term,Type),
% 	( 
% 	    dz_equivalent_types(Type,Root) ->
% 	    arg(A,NewTerm,Root)
% 	;
% 	    arg(A,NewTerm,Type)
% 	),
% 	A1 is A - 1,
%         simplify_arg(A1,Term,NewTerm,Root).



get_native_type_symbols([],[],[]).
get_native_type_symbols([T|Def_s],[T|Def_n],Def_nnat):-
	native_type_symbol(T),!,
	get_native_type_symbols(Def_s,Def_n,Def_nnat).
get_native_type_symbols([T|Def_s],Def_n,[T|Def_nnat]):-
	get_native_type_symbols(Def_s,Def_n,Def_nnat).


union_of_native_types([],L,L).
union_of_native_types([T|L],A,R):-
	union_elem_native_type(T,A,A1),
	union_of_native_types(L,A1,R).

union_elem_native_type(T,[],[T]) :- !.
union_elem_native_type(T,[T1|R],[T1|R]):-
	dz_type_included(T,T1),!.
union_elem_native_type(T,[T1|R],[T|R]):-
	dz_type_included(T1,T),!.
union_elem_native_type(T,[T1|R],[T1|R1]):-
	union_elem_native_type(T,R,R1).



:- pred get_typedefinition(+Type,-Def): pure_type_term * list(pure_type_term) #
"
Return the definition of @var{Type} if Type is a type simbol. Otherwise return [Type].
".

get_typedefinition(Type,Def):-
       ( 
	   rule_type_symbol(Type) ->
	   get_type_definition(Type,Def)
       ;
	   Def = [Type]
       ).

:- pred unfold(+TS, +Def,-UDef): list * list(pure_type_term) * list(pure_type_term) #
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

:- pred make_deterministic(+Def1,+Def2):  
 list(pure_type_term) * list(pure_type_term)#  
"
@var{Def1} and @var{Def2} are two sorted lists of type terms with
compound type terms of different functor/arity. @var{Def1} is the
merge of both definitions, if two compound type terms have the same
functor/arity, both are replaced by a new compound type terms whose
arguments are the deterministic union of the formers.
".


make_deterministic([],[]):- !. 
make_deterministic([X],[X]):- !. 
make_deterministic([TermType1,TermType2|Def1],Def):- 
	compare(Order,TermType1,TermType2),
	make_deterministic0(Order,TermType1,TermType2,Def1,Def). 

make_deterministic0(=,_TermType1,TermType2,Def1,Def):- 
	make_deterministic([TermType2|Def1],Def),!. 
make_deterministic0(_,TermType1,TermType2,Def1,Def):- 
	compound_pure_type_term(TermType1,Term1,Name,Arity),
	compound_pure_type_term(TermType2,Term2,Name,Arity),!,
	functor(Term,Name,Arity),
	obtain_new_term(Arity,Term1,Term2,Term),
	construct_compound_pure_type_term(Term,TermType),
	make_deterministic([TermType|Def1],Def). 
make_deterministic0(_,TermType1,TermType2,Def1,[TermType1|Def]):- 
	make_deterministic([TermType2|Def1],Def).


obtain_new_term(0,_,_,_) :- !.
obtain_new_term(N,Term1,Term2,Term):-
	arg(N,Term1,Arg1),
	arg(N,Term2,Arg2),
	type_union(Arg1,Arg2,Arg),
	arg(N,Term,Arg),
	N1 is N - 1,
        asserta(uniontriple(Arg1,Arg2,Arg)),
	obtain_new_term(N1,Term1,Term2,Term).



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


eterms_widencall(Prime0,Prime1,Result):-
%	display(user,'widencall'),
	eterms_widen(Prime0,Prime1,Result).	


:- pred eterms_widen(+Prime0,+Prime1,-NewPrime):
absu * absu * absu #
"
Induction step on the abstract substitution of a fixpoint.
@var{Prime0} corresponds to non-recursive and @var{Prime1} to
recursive clauses.  @var{NewPrime} is the result of apply one widening
operation to the least upper bound of the formers.
".

eterms_widen(Prime0,Prime1,NewPrime):-
%	display(user,'widen'),nl(user),
  eterms_compute_lub_el(Prime0,Prime1,Prime),
	ewiden(Prime0,Prime,NewPrime).


ewiden('$bottom','$bottom','$bottom') :- !.
ewiden('$bottom',Prime,Prime).
ewiden([],[],[]).
ewiden([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
	lnewiden_el(T1,T2,T),
	ewiden(Prime0,Prime,NewPrime).

laddcycles([],[]).
laddcycles([(S,N)|LWs],[(S,N,[(S,N)])|LWss]):-
	laddcycles(LWs,LWss).


lnewiden_el(T1,T2,T1):- T1 == T2,!.
lnewiden_el(_,(N,T),(N,T)):- top_type(T),!.
lnewiden_el((_N1,T1),(N2_e,T2),(N2,W)):-
	get_canonical_name(N2_e,N2),
	retract_type_name(N2,LWs,Count),        % equival_names
	laddcycles(LWs,LWss),
	lfilternames(LWss,N2,LWSS),
	( LWSS == [] ->
	    W=T2,
	    insert_type_name(N2,LWs,Count)
	;
	    insert_type_name(N2,LWs,Count),
	    (
		current_pp_flag(type_eval,on), member((['$is'],_N),LWs) -> %% OJO REVISAR
		get_less_numeric_type(T2,W)
	    ;
		new_type_symbol(W),
		get_typedefinition(T2,Def),
%		display(user,'start'),nl(user),
		lnewiden_def(Def,NewDef,T1,T2,W,[(N2,W)],[],LWSS,[],I,[],ListofnewW,[W]), 
		sort(NewDef,NewDef_s),
		insert_rule(W,NewDef_s),
%		display(user,'end'),nl(user),
		sort(ListofnewW,ListofnewW_s),
		normalize_wide_rules_listOfnew(ListofnewW_s,I),
		resetunion,
		make_determ_wide_rules(I)
%		display(user,'endnor'),nl(user)
	    )
	).



lnewiden_def([],[],_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN):- !.
lnewiden_def([T|Def],[NT|NewDef],T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LNt):-
	lnewiden_elem(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,I1,LN,LN1),
	lnewiden_def(Def,NewDef,T1,T2,W,N2,Sel,LW,Seen,I1,Tail,LN1,LNt).


lnewiden_args(0,_F,_Term,_NewTerm,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN):- !.
lnewiden_args(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LNt):-
	arg(A,Term,Arg),
	lnsimplify_LW([F/A|Sel],LW,LW1),
	sort(LW1,LW1_s),
	lnewiden_elem_arg(Arg,NewArg,T1,T2,W,N2,[F/A|Sel],LW1_s,Seen,I,I1,LN,LN1),
	arg(A,NewTerm,NewArg),
	A1 is A - 1,
	lnewiden_args(A1,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I1,Tail,LN1,LNt).



lnsimplify_LW(_,[],[]) :- !.
lnsimplify_LW(Sel,[(PS,S,N,C)|LW],[(PS,S,N,C)|LW1]):-
        dlist(_,S,Sel),!,
	lnsimplify_LW(Sel,LW,LW1).
lnsimplify_LW(Sel,[_|LW],LW1):-
	lnsimplify_LW(Sel,LW,LW1).


lfilternames([],_N2,[]) :- !.
lfilternames([(S,Nw,C)|LWs],Nw,[([],S,Nw,C)|LWW]):- !,
	lfilternames(LWs,Nw,LWW).
lfilternames([(S,N,C)|LWs],Nw,LWW1):-
	get_type_name(N,L),
	insert(C,(S,N),NC),
	lexpandandfilternames(L,S,NC,Nw,LWW1,LWW),
	lfilternames(LWs,Nw,LWW).


lexpandandfilternames([],_S,_C,_Nw,L,L) :- !.
lexpandandfilternames([(NS,NL)|L],S,C,Nw,[(PS,TS,NL,C)|LWP],LW1):-
	member((PS,NL),C),!,
	dlist(NS,TS,S),
	lexpandandfilternames(L,S,C,Nw,LWP,LW1).
lexpandandfilternames([(SL,Nw)|L],S,C,Nw,[([],NSL,Nw,C)|LWP],LW1):- !,
        dlist(SL,NSL,S),	
	lexpandandfilternames(L,S,C,Nw,LWP,LW1).
lexpandandfilternames([(SL,NL)|L],S,C,Nw,LWP,LW1):-
        dlist(SL,NSL,S),	
	get_type_name(NL,LL),	
	insert(C,(NSL,NL),NC),
	lexpandandfilternames(LL,NSL,NC,Nw,LWP,LWP1),
	lexpandandfilternames(L,S,C,Nw,LWP1,LW1).



lnewiden_elem(T,T,_T1,_T2,_W,_N2,_Sel,[],_Seen,I,I,LN,LN) :- !. 
lnewiden_elem(T,T,_T1,_T2,_W,_N2,Sel,LW,_Seen,I,I,LN,LN):-
	compound_pure_type_term(T,_Term,F,_A),
	\+ lselismember([F/_|Sel],LW), !. % TODO: factorize
lnewiden_elem(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
	compound_pure_type_term(T,Term,F,A),!,
	functor(NewTerm,F,A),
	lnewiden_args(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1),
	construct_compound_pure_type_term(NewTerm,NT).
lnewiden_elem(T,T,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN).



lnewiden_elem_arg(T,NT,_T1,T2,W,_N2,_Sel,_LW,Seen,I,I,LN,LN):- 
 	em_defined_type_symbol(T,_Def),
	( 
	    T== T2 -> NT = W 
	;
	    member((T,NT),Seen)
	),!.
lnewiden_elem_arg(T,T,_T1,_T2,_W,_N2,_Sel,[],_Seen,I,I,LN,LN) :- !.
lnewiden_elem_arg(T,NT,T1,T2,RW,N,Sel,LW,Seen,I,Tail,LN,LNt):-
       ( member((_,Sel,_,_),LW) ; member((Sel,_,_,_),LW) ),
	new_type_symbol(NT),
        findall((ONO,NT),member((Sel,_,ONO,_),LW),NewN,N),
	( member((_,Sel,ON,_),LW) ->  
	  findall(W,(member((_,Sel,ON,_),LW),member((ON,W),N)),WWW,[]), I1 = [NT|Tail], 
	  dlist(WWW,LN1,LNt), % LN1 = [W|LNt], 
	  Add = true ; I1 = Tail, LN1 = LNt, Add = false),
	get_typedefinition(T,DefT),
	    ( 
	    	em_defined_type_symbol(T, Defin) -> 
	    	DefT = Defin,
	    	NewSeen = [(T,NT)|Seen]
	    ;
	    	DefT = [T],
	    	NewSeen = Seen
	    ),
	    lnewiden_def(DefT,DefU,T1,T2,RW,NewN,Sel,LW,NewSeen,I,I1,LN,LN1),
%	    display(user,'WWWWWWWWWWWWWW'),nl(user),
      %
	    sort(DefU,Def_s),	
	    ( Add == true ->  
	      sort(WWW,WWWs),
	      merge(WWWs,Def_s,Def)
%	      merge([W],Def_s,Def) 
	    ; Def = Def_s),
 	    insert_rule(NT,Def), !. % TODO: move this cut
%
lnewiden_elem_arg(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
	em_defined_type_symbol(T,Def),!,
	(
	    member((T,NT),Seen) -> I = Tail,LN = LN1
	;
	    new_type_symbol(NT),
	    lnewiden_def(Def,NewDef,T1,T2,W,N2,Sel,LW,[(T,NT)|Seen],I,Tail,LN,LN1),
	    sort(NewDef,NewDef_s),
	    insert_rule(NT,NewDef_s)
	).
lnewiden_elem_arg(T,T,_T1,_T2,_W,_N2,Sel,LW,_Seen,I,I,LN,LN):-
	compound_pure_type_term(T,_Term,F,_A),
	\+ lselismember([F/_|Sel],LW), !. % TODO: factorize
lnewiden_elem_arg(T,NT,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1):-
	compound_pure_type_term(T,Term,F,A),!,
	functor(NewTerm,F,A),
	lnewiden_args(A,F,Term,NewTerm,T1,T2,W,N2,Sel,LW,Seen,I,Tail,LN,LN1),
	construct_compound_pure_type_term(NewTerm,NT).
lnewiden_elem_arg(T,T,_T1,_T2,_W,_N2,_Sel,_LW,_Seen,I,I,LN,LN).


lselismember(Sel,[(_,S,_N,_C)|_LW]):-
	dlist(_,S,Sel), !. % TODO: move cut?
lselismember(Sel,[_|LW]):-
	lselismember(Sel,LW).



make_determ_wide_rules([]).
make_determ_wide_rules([T|Rules]):-
	em_defined_type_symbol(T, Def),
%	resetunion,
	make_deterministic(Def,NewDef), 
	SDef = NewDef,	%	simplify_def(NewDef,SDef,T),
        sort(SDef,SDef_s),
	retract_rule(T),
	insert_rule(T,SDef_s),
	make_determ_wide_rules(Rules).


normalize_wide_rules_listOfnew([],_).
normalize_wide_rules_listOfnew([W|ListofnewW],I):-
	normalize_wide_rules_ow(I,W),	
	normalize_wide_rules_listOfnew(ListofnewW,I).


normalize_wide_rules_ow([],_).
normalize_wide_rules_ow([T|Rules],W):-
	em_defined_type_symbol(T, Def),
	member(W,Def),!,
	ord_delete(Def,W,U),
	em_defined_type_symbol(W,DefW),
	merge(DefW,U,NewDef),
	retract_rule(T),
	insert_rule(T,NewDef), 
	normalize_wide_rules_ow(Rules,W).
normalize_wide_rules_ow([_|Rules],W):-
	normalize_wide_rules_ow(Rules,W).

	
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%--------------------------END-WIDENING-------------------------------%
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 




%------------------------------------------------------------------%
:- pred eterms_call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo): term * callable * list * 
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
 @item add to this abstract substitution the variables in Fv as term type. 
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

eterms_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,(yes,Proj)):- 
	variant(Sg,Head), !,
	copy_term((Sg,Proj),(NewTerm,NewProj_u)),
	Head = NewTerm,
	eterms_sort(NewProj_u,NewProj),
	eterms_project(Hv,NewProj,NewProj1),
	variables_are_variable_type(Fv,Free),
	merge(Free,NewProj1,Entry).
eterms_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,(no,Proj)):-
	unify_term_and_type_term(Head,Hv,Sg,Proj,TmpEntry), !,
	variables_are_variable_type(Fv,Tmp),
	merge(Tmp,TmpEntry,Entry).
eterms_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- pred variables_are_variable_type(+Fv,-ASub): list * absu # 
"at the moment it assigns the value top_type to the variables in @var{Fv}
 but in the future it must assign the value ``var''".


% create_names([],[]).
% create_names([X:(N,T)|Proj],[X:(Name,T)|Proj1]):-
% 	new_type_name(Name),
% 	insert_type_name(Name,T,[]),
% 	create_names(Proj,Proj1).

variables_are_variable_type(Fv,ASub):-
	variables_are_top_type(Fv,ASub).


%------------------------------------------------------------------%
:- pred eterms_exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime): list
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

eterms_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
	Prime = '$bottom'.
eterms_exit_to_prime(Sg,Hv,Head,_Sv,Exit,(yes,Proj),Prime):- !,
	eterms_project(Hv,Exit,BPrime),
	copy_term((Head,BPrime),(NewTerm,NewPrime)),
	Sg = NewTerm,
	eterms_sort(NewPrime,Prime1),
	replace_names(Proj,Prime1,Prime).	
eterms_exit_to_prime(Sg,Hv,Head,Sv,Exit,(no,ExtraInfo),Prime):- 
	eterms_project(Hv,Exit,BPrime),
	unify_term_and_type_term_exit(Sg,Sv,Head,BPrime,ExtraInfo,Prime), !. %,!, %change
  % TODO: cut was disabled here
%
% probar agregar sinonimos de ExtraInfo a Prime
%%	replace_names(ExtraInfo,Prime1,Prime).
eterms_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').

% replace_names1([],[],[]).
% replace_names1([X:(N,_T)|ExtraInfo],[X:(_N1,T1)|Prime1],[X:(N,T1)|Prime]):-
% 	replace_names1(ExtraInfo,Prime1,Prime).


replace_names([],[],[]).
replace_names([X:(N_e,_T)|ExtraInfo],[X:(N1_e,T1)|Prime1],[X:(N,T1)|Prime]):-
	get_canonical_name(N_e,N),
	get_canonical_name(N1_e,N1),
	lab_intersect(N,N1),
%	get_type_name(N1,LN1),
% %	retract_type_name(N1,LN1,C1),
%	retract_type_name(N,LN,C),
%	merge(LN,LN1,L),
% %	insert_type_name(N1,LN1,C1),
%	insert_type_name(N,L,C),
	replace_names(ExtraInfo,Prime1,Prime).

% % replace_names([],[],[]).
% % replace_names([X:(N,_T)|ExtraInfo],[X:(N1,T1)|Prime1],[X:(N1,T1)|Prime]):-
% % 	retract_type_name(N1,L,C1),
% % 	insert(L,([],N),L1),
% % 	insert_type_name(N1,L1,C1),
% % 	replace_names(ExtraInfo,Prime1,Prime).

:- pred unify_term_and_type_term(+Term1,+Tv,+Term2,+ASub,-NewASub): callable * list * 
callable * absu * absu # 
"it unifies the term @var{Term1} to the type term @var{Term2}
obtaining the the abstract substitution TypeAss which is sorted and
projeted on @var{Tv}".

get_canonical_name(N,Canonical):-
	get_equiv_name(N,Canonical),!.
get_canonical_name(N,N):- !.

obtains_names(Types,Args,ASub0,TypeNameAss):-
	gen_list(Types,Args,ASub0,Out),
	join_assign(Out,TypeNameAss1),
	get_all_canonical(TypeNameAss1,TypeNameAss).


get_all_canonical([],[]).
get_all_canonical([X:Lab1|TypeNameAss1],[X:Lab|TypeNameAss]):-
	get_all_canonical2(Lab1,Lab),
	get_all_canonical(TypeNameAss1,TypeNameAss).

get_all_canonical2([],[]).
get_all_canonical2([(S,N)|Lab1],[(S,N1)|Lab]):-
	get_canonical_name(N,N1),	
	get_all_canonical2(Lab1,Lab).

lab_intersection([],[]).
lab_intersection([X],[X]) :- !.
lab_intersection([(S1,N1_e),(S2,N2_e)|Lab],LabO):-
	S1 == S2,!,
	get_canonical_name(N1_e,N1),
	get_canonical_name(N2_e,N2),
	lab_intersect(N1,N2),
	lab_intersection([(S1,N1)|Lab],LabO).
lab_intersection([(S1,N1),(S2,N2)|Lab],[(S1,N1)|LabO]):-
	lab_intersection([(S2,N2)|Lab],LabO).

lab_intersect(N,N):- !.
lab_intersect(N1,N2):-
	retract_type_name(N1,L1,C),
	retract_type_name(N2,L2,_C2),
	ord_union(L1,L2,L),
	insert_type_name(N1,L,C),
	insert_equiv_name(N2,N1),
%	insert_type_name(N2,L,C2),
	replace_all_type_names(N2,N1),
	replace_all_equiv_names(N2,N1),!.

replace_all_equiv_names(N2,N1):-
	retract_equiv_name(N,N2),
	insert_equiv_name(N,N1),
	fail.
replace_all_equiv_names(_,_).

replace_all_type_names(N2,N1):-
	setof(N,L^S^(get_type_name(N,L),member((S,N2),L)),List),!,
%	ord_delete(List,N2,List_s),
	replace_all_type_name0(List,N2,N1).
replace_all_type_names(_,_).

replace_all_type_name0([],_,_).
replace_all_type_name0([N|List],N2,N1):-
	retract_type_name(N,L,C),
	replace_type_names(L,N2,N1,NL),
	sort(NL,NL_s),
	insert_type_name(N,NL_s,C),	
	replace_all_type_name0(List,N2,N1).

replace_type_names([],_N2,_N1,[]).
replace_type_names([(S,N2)|L],N2,N1,[(S,N1)|NL]):- 
	!,
	replace_type_names(L,N2,N1,NL).
replace_type_names([(S,N)|L],N2,N1,[(S,N)|NL]):- 
	replace_type_names(L,N2,N1,NL).

join_one([],A,A) :- !.
join_one(A,[],A) :- !.
join_one([X:Lab1|A1],[Y:Lab2|A2],[Z:Lab|A]):-
	compare(Order,X,Y),
	join_one0([X:Lab1|A1],[Y:Lab2|A2],Order,Z,Lab,A).

join_one0([X:Lab1|A1],[_Y:Lab2|A2],=,X,Lab,A):- !,
%	ord_intersection(Lab1,Lab2,Lab),		
	ord_union(Lab1,Lab2,Lab_s),
 	lab_intersection(Lab_s,Lab),
	join_one(A1,A2,A).
join_one0([X:Lab1|A1],[Y:Lab2|A2],<,X,Lab1,A):- !,
	join_one(A1,[Y:Lab2|A2],A).
join_one0([X:Lab1|A1],[Y:Lab2|A2],>,Y,Lab2,A):-
	join_one([X:Lab1|A1],A2,A).


join_assign([],[]).
join_assign([AssArg],AssArg2):- !,
	join_one(AssArg,AssArg,AssArg2).
join_assign([AssArg1,AssArg2|Out],TypeNameAss):-
	join_one(AssArg1,AssArg2,Assign),
	join_assign([Assign|Out],TypeNameAss).

get_positions_of_vars([],_,[]).
get_positions_of_vars([X|Vars],Arg,[X:P|Pos]):-
	get_pos_var(X,Arg,P,[],[]),
	get_positions_of_vars(Vars,Arg,Pos).

get_pos_var(X,Term,[Sel|Tail],Tail,Sel):- X == Term,!.
get_pos_var(X,Term,P,Tail,Sel):-
	nonvar(Term),
	functor(Term,F,A),!,
	get_pos_var_arg(A,X,Term,F,Sel,P,Tail).
get_pos_var(_X,_Term,P,P,_).

get_pos_var_arg(0,_X,_Term,_F,_Sel,P,P) :- !.
get_pos_var_arg(A,X,Term,F,Sel,P,Tail):-
	arg(A,Term,Arg),
	get_pos_var(X,Arg,P,P1,[F/A|Sel]),
	A1 is A - 1,
	get_pos_var_arg(A1,X,Term,F,Sel,P1,Tail).

get_names_of_positions([],_,_,[]).
get_names_of_positions([X:P|Pos],TypeArg,ASub0,[X:Lab|Assign1]):-
	get_names_of_positions1(P,TypeArg,ASub0,Lab),
	get_names_of_positions(Pos,TypeArg,ASub0,Assign1).

get_names_of_positions1([],_,_,[]).
get_names_of_positions1([Pos],TypeArg,ASub0,Lab):- !,
	get_names_of_one_pos(Pos,TypeArg,ASub0,Lab1),
	sort(Lab1,Lab).
get_names_of_positions1([Pos|P],TypeArg,ASub0,Lab):-
	get_names_of_one_pos(Pos,TypeArg,ASub0,Lab1),
	sort(Lab1,Lab1_s),
	get_names_of_positions1(P,TypeArg,ASub0,Lab2),
%	ord_intersection(Lab1_s,Lab2,Lab).	
	ord_union(Lab1_s,Lab2,Lab).		

get_names_of_one_pos([],TypeArg,ASub0,Lab):-
	!,
	get_names_of_subterm(TypeArg,[],ASub0,Lab,[]).
get_names_of_one_pos(P,TypeArg,ASub0,Lab):- 
	var(TypeArg),!,
	member(Y:(Name_e,_),ASub0),
	get_canonical_name(Name_e,Name),
	Y == TypeArg, % TODO: cut if TypeArg is unique in Asub0
	get_type_name(Name,L),                    % equival_names
	% findall(([A|B],N),( 
	% 		      member((S,N),L),
	% 		      dlist([A|B],S,P)
	% 		  ),Lab,[]).
	findall((A,N),( 
			      member((S,N),L),
			      dlist(A,S,P)
			  ),Lab,[]).
get_names_of_one_pos(P,TypeArg,ASub0,Lab):-
	dlist(NP,P,[F/A]),
 	functor(TypeArg,F,_),	
	arg(A,TypeArg,Arg),
	get_names_of_one_pos(NP,Arg,ASub0,Lab).

get_names_of_subterm(TypeArg,Sel,ASub0,Lab,Tail):-
	var(TypeArg),!,
	member(Y:(Name_e,_),ASub0),         % equival_names
	get_canonical_name(Name_e,Name),
	TypeArg == Y, % TODO: cut if TypeArg is unique in Asub0
	(
	    Sel == [] ->
%	    get_type_name(Name,L),
%	    dlist(L,Lab1,Tail),     % changed
	    Lab = [([],Name)|Tail]  % changed
	;
	    Lab = [(Sel,Name)|Tail]
	).
% get_names_of_subterm(TypeArg,Sel,_ASub0,Lab,Tail):-
% 	atom(TypeArg),!,
% 	( 
% 	    exist_name(TypeArg) ->
% 	    get_canonical_name(TypeArg,NewName)
% 	;
% 	    insert_type_name(TypeArg,[],0),
% 	    NewName = TypeArg
% 	),
% 	Lab = [(Sel,NewName)|Tail].
get_names_of_subterm(TypeArg,Sel,ASub0,Lab,Tail):-
	functor(TypeArg,F,A),
	get_names_of_subterm_arg(A,TypeArg,F,Sel,ASub0,Lab,Tail).

% exist_name(TypeArg):-
% 	get_type_name(TypeArg,_).
% exist_name(TypeArg):-
% 	get_equiv_name(TypeArg,_).
	    
get_names_of_subterm_arg(0,_,_,_,_,L,L) :- !.
get_names_of_subterm_arg(N,Term,F,Sel,ASub0,Lab,Tail):-
	arg(N,Term,Arg),
	get_names_of_subterm(Arg,[F/N|Sel],ASub0,Lab,Tail1),
	N1 is N - 1,
	get_names_of_subterm_arg(N1,Term,F,Sel,ASub0,Tail1,Tail).




gen_list([],[],_,[]).
gen_list([TypeArg|Types],[Arg|Args],ASub0,[Assign|Out]):-
	varset(Arg,Vars),
	get_positions_of_vars(Vars,Arg,Pos),
	get_names_of_positions(Pos,TypeArg,ASub0,Assign1),
	sort(Assign1,Assign),
	gen_list(Types,Args,ASub0,Out).
	


unify_term_and_type_term_exit(Term1,Tv,Term2,ASub,Proj,NewASub):-
	copy_term((Term2,ASub),(TypeTerm,ASub0)),
        Term2 =.. [_|HeadArg], 
	TypeTerm =.. [_|Types],
	Term1 =.. [_|Args],
	type_escape_term_list(Types,EscTypes),
	apply(ASub0),
	generate_a_type_assigment(EscTypes,Args,TypeAss),
	( 
	    member(_:bot,TypeAss) -> fail
	;
	    sort(Proj,Proj_s),
	    eterms_sort(TypeAss,ASub1),
	    obtains_names(HeadArg,Args,ASub,TypeNameAss),

	    % generate_subs_exit(ASub1,Proj,Subs),
	    % update_names(TypeNameAss,Subs),

	    sort(TypeNameAss,TypeNameAss_s),
	    generate_subs_exit(ASub1,Proj_s,TypeNameAss_s,Subs),

	    eterms_project(Tv,Subs,NASub),
	    normal_asub(NASub,NewASub)
	).


unify_term_and_type_term(Term1,Tv,Term2,ASub,NewASub):-
	copy_term((Term2,ASub),(TypeTerm,ASub0)),
        Term2 =.. [_|HeadArg], 
	TypeTerm =.. [_|Types],
	Term1 =.. [_|Args],
	type_escape_term_list(Types,EscTypes),
	apply(ASub0),
	generate_a_type_assigment(EscTypes,Args,TypeAss),
	( 
	    member(_:bot,TypeAss) -> fail
	;
	    sort(ASub,ASub_s),
	    eterms_sort(TypeAss,ASub1),
	    obtains_names(HeadArg,Args,ASub_s,TypeNameAss),
	    sort(TypeNameAss,ASub2),
	    generate_subs(ASub1,ASub2,Subs),
	    obtains_names(Args,HeadArg,Subs,TypeNameAss2),
	    sort(TypeNameAss2,TypeNameAss2_s),
	    update_names(TypeNameAss2_s,ASub_s),
	    eterms_project(Tv,Subs,NASub),
	    normal_asub(NASub,NewASub)
	).

normal_asub([],[]).
normal_asub([X:(Name,Type)|ASub],[X:(Name,NType)|NASub]):-
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

update_names([],_):-!.
update_names([Y:Lab|Labels],[Z:(Name_e,_)|ASub]):-
%	member(Z:(Name,_),ASub),
	Y == Z,!,
	get_canonical_name(Name_e,Name),
	retract_type_name(Name,L,C),
	(
	    member(([],Name0_e),Lab) ->     
	    ord_delete(Lab,([],Name0_e),Lab0),
	    get_canonical_name(Name0_e,Name0),
	    ord_union(L,Lab0,NLab),		
	    insert_type_name(Name,NLab,C),
	    (
		Name0 == Name -> true
	    ;
		lab_intersect(Name,Name0)
	    )
	;
	    ord_union(L,Lab,NLab),		
	    insert_type_name(Name,NLab,C)
	),
	update_names(Labels,ASub).
update_names(_,_):-
	error_message("SOMETHING HAS FAILED! See eterms domain.", []).

generate_subs_exit([],_Proj,_TypeNameAss,[]):-!.
generate_subs_exit([X:Type|Types],[Z:(NameP_e,_)|Proj],[Y:Lab|Labels],[X:(Name,Type)|Subs]):-
	X == Y,
	X == Z,!,
	get_canonical_name(NameP_e,Name),	
	retract_type_name(Name,L,C),	
	(
	    member(([],Name0_e),Lab) ->
	    ord_delete(Lab,([],Name0_e),Lab0),
	    get_canonical_name(Name0_e,Name0),	
	    ord_union(L,Lab0,NLab),		
	    insert_type_name(Name,NLab,C),  
	    (
		Name0 == Name -> true
	    ;
		lab_intersect(Name,Name0)
	    )
	;
	    ord_union(L,Lab,NLab),		
	    insert_type_name(Name,NLab,C)
	),
	generate_subs_exit(Types,Proj,Labels,Subs).
generate_subs_exit(_,_,_,_):-
	error_message("SOMETHING HAS FAILED! See eterms domain.").


generate_subs([],[],[]):-!.
generate_subs([X:Type|Types],[Y:Lab|Labels],[X:(Name,Type)|Subs]):-
	X == Y,!,
	sort(Lab,Lab1),
	 (
	     member(([],Name),Lab1) -> 
	     ord_delete(Lab1,([],Name),Lab0),
	     retract_type_name(Name,L,C),     
	     ord_union(Lab0,L,NL),  
	     insert_type_name(Name,NL,C)	     
	 ;
	    new_type_name(Name),
	    insert_type_name(Name,Lab1,0)
	),
	generate_subs(Types,Labels,Subs).
generate_subs(_,_,_):-
	display(user,'SOMETHING HAS FAILED! See eterms domain.'), nl(user).

:- pred apply(+ASub): absu # 
"it unifies the variables in the abstract
substitution @var{ASub} to his respective values".

apply([X:(_N,Term)|ASub]):-
	X=Term,
	apply(ASub).
apply([]).



%------------------------------------------------------------------%
:- pred eterms_project(+Vars,+Asub,-Proj): list * absu * absu # 
"@var{Proj} is the result of eliminating from @var{Asub} all
@var{X}:@var{Value} such that @var{X} is not in @var{Vars}".



eterms_project(_,'$bottom',Proj):-  !,
	Proj = '$bottom'.
eterms_project(Vars,ASub,Proj) :- 
	eterms_project_aux(Vars,ASub,Proj).

eterms_project_aux([],_,Proj):- !,
	Proj = [].
eterms_project_aux(_,[],Proj):- !,
	Proj = [].
eterms_project_aux([Head1|Tail1],[Head2:Type|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	eterms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

eterms_project_aux_(=,_,Tail1,HeadType,Tail2,[HeadType|Proj]) :-
	eterms_project_aux(Tail1,Tail2,Proj).
eterms_project_aux_(>,Head1,Tail1,_,[Head2:Type|Tail2],Proj) :-
	compare(Order,Head1,Head2),
	eterms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

%------------------------------------------------------------------%
:- pred eterms_sort(+Asub,-Asub_s): absu * absu
# 
"It sorts the set of @var{X}:@var{Type} in @var{Asub} ontaining @var{Asub_s}".

eterms_sort('$bottom','$bottom'):- !.
eterms_sort(ASub,ASub_s):- sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- pred eterms_extend(+Prime,+Sv,+Call,-Succ): absu * list * absu * absu # 
"
If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
 @var{Succ} is computed updating the values of @var{Call} with those
 in @var{Prime}".

eterms_extend('$bottom',_Sv,_Call,'$bottom'):- !.
eterms_extend([],_Sv,Call,Call):- !.
eterms_extend(Prime,_Sv,[],Prime):- !.
eterms_extend([X:(N_e,T)|Prime],Sv,[Y:(N1_e,_T1)|Call],[X:(N,T)|Succ]):-
	X == Y,!,
	get_canonical_name(N_e,N),
	get_canonical_name(N1_e,N1),
	lab_intersect(N,N1), % equival_names
	eterms_extend(Prime,Sv,Call,Succ).
eterms_extend([X:(N_e,T)|Prime],Sv,[Y:(N1,T1)|Call],[X:(N,T)|Succ]):-
	X @< Y,!,
	get_canonical_name(N_e,N),
	eterms_extend(Prime,Sv,[Y:(N1,T1)|Call],Succ).
eterms_extend([X:(N,T)|Prime],Sv,[Y:(N1,T1)|Call],[Y:(N1,T1)|Succ]):-
        X @> Y,!,
	eterms_extend([X:(N,T)|Prime],Sv,Call,Succ).


%------------------------------------------------------------------%
:- pred eterms_less_or_equal(+ASub0,+ASub1): absu * absu # 
"Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
it's assumed the two abstract substitutions are defined on the same variables".


eterms_less_or_equal('$bottom',_ASub):- !.
eterms_less_or_equal(ASub1,ASub2):-
	ASub1 == ASub2, !.
eterms_less_or_equal(ASub1,ASub2):-
	eterms_less_or_equal0(ASub1,ASub2).

eterms_less_or_equal0([X:(_N1,T1)|ASub1],[Y:(_N2,T2)|ASub2]):-
	X==Y,
	dz_type_included(T1,T2),
	eterms_less_or_equal0(ASub1,ASub2).
eterms_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- pred eterms_glb(+ASub0,+ASub1,-Glb): absu * absu * absu # 
"@var{Glb} is the great lower bound of @var{ASub0} and @var{ASub1}".

eterms_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
eterms_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
eterms_glb(ASub1,ASub2,ASub3):-
	ASub1 == ASub2, !,
	ASub3 = ASub2.
eterms_glb(ASub1,ASub2,ASub3):-
	eterms_glb0(ASub1,ASub2,ASub33), !,
        eterms_glbnames(ASub1,ASub33,ASub3).
eterms_glb(_ASub1,_ASub2,'$bottom').

eterms_glb0([X:(_N1,T1)|ASub1],[Y:(N2,T2)|ASub2],[X:(N2,T3)|ASub3]):-
	X==Y,
	type_intersection_2(T1,T2,T3),
	( 
	    T3==bot -> fail 
	;
  	    eterms_glb0(ASub1,ASub2,ASub3)
	).
eterms_glb0([],[],[]).

eterms_glbnames([X:(N1_e,_)|ASub1],[X:(N3_e,T3)|ASub33],[X:(N3,T3)|ASub3]):-
	get_canonical_name(N1_e,N1),
	get_canonical_name(N3_e,N3),
	lab_intersect(N3,N1),
	eterms_glbnames(ASub1,ASub33,ASub3),!. % TODO: move cut
eterms_glbnames([],[],[]):- !.


% eterms_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
% eterms_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
% eterms_glb(ASub1,ASub2,ASub3):-
% 	ASub1 == ASub2, !,
% 	ASub3 = ASub2.
% eterms_glb(ASub1,ASub2,ASub3):-
% 	eterms_glb0(ASub1,ASub2,ASub3), !.
% eterms_glb(_ASub1,_ASub2,'$bottom').

% eterms_glb0([X:(N1,T1)|ASub1],[Y:(N2,T2)|ASub2],[X:(N3,T3)|ASub3]):-
% 	X==Y,
% 	type_intersection_2(T1,T2,T3),!,
% 	( 
% 	    T3==bot -> fail 
% 	;
% 	    get_type_name(N1,L1),
% 	    get_type_name(N2,L2),                   % equival_names
% 	    merge(L1,L2,L3),
% %	    ord_intersection(L1,L2,L3),
% 	    new_type_name(N3),
% 	    insert_type_name(N3,L3,0),
% 	%   add_labels_intersection(T3,N1,N2,N3),
%   	    eterms_glb0(ASub1,ASub2,ASub3)
% 	).
% eterms_glb0([],[],[]).


%------------------------------------------------------------------%
:- pred eterms_unknown_entry(+Qv,-Call): list * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to   
 Call. In this domain the top value is X:term forall X in the set of variables".

eterms_unknown_entry(Vars,ASub):-
	variables_are_top_type(Vars,ASub).


:- pred eterms_empty_entry(+Vars,-Entry): list * absu # "Gives the
""empty"" value in this domain for a given set of variables
@var{Vars}, resulting in the abstract substitution @var{Entry}. I.e.,
obtains the abstraction of a substitution in which all variables
@var{Vars} are unbound: free and unaliased. In this domain the empty
value is giving the variable type to each variable".

eterms_empty_entry(Vars,ASub):-
	variables_are_variable_type(Vars,ASub).



%------------------------------------------------------------------%
:- pred eterms_unknown_call(+Sg,+Vars,+Call,-Succ): callable * list * absu * absu # 
"Gives the ``top'' value for the variables involved in a 
 literal whose definition is not present, and adds this top value to
 @var{Call}".

eterms_unknown_call(_Sg,Vars,Call,Succ):-
	substitution(Call,CallVars,_),
	ord_subtract(Vars,CallVars,TopVars),
	variables_are_top_type(TopVars,ASub),
	merge(Call,ASub,Succ).
	
substitution([],[],[]).
substitution([X:T|TypeAss],[X|Vars],[T|ListTypes]):-
	substitution(TypeAss,Vars,ListTypes).

:- pred variables_are_top_type(+Fv,-ASub) :: list * absu # 
"it assigns the value top_type to the variables in @var{Fv}
and return the abstract substitution @var{ASub} ".

variables_are_top_type([V|Fv],[V:(Name,Type)|ASub]):-
	set_top_type(Type),
	new_type_name(Name),
	insert_type_name(Name,[],0),
	variables_are_top_type(Fv,ASub).
variables_are_top_type([],[]).

%------------------------------------------------------------------%
:- pred eterms_call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ): callable * 
list * callable * term * list * absu * absu * absu * absu # 
"Specialized version of call_to_entry + exit_to_prime + extend for facts".

eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
	eterms_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
	eterms_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
	eterms_extend(Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%
%			       BUILTINS
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% eterms_special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)                      %
% Type is a flag indicating what is the abstraction of builtin SgKey     %
% and to which variables Condvars of the goal Sg it affects.             %
%------------------------------------------------------------------------%


eterms_special_builtin('!/0',_Sg,_,id,[]) :- !.
eterms_special_builtin('@=</2',_Sg,_,id,[]) :- !.
eterms_special_builtin('@>/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('@>=/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('@</2',_Sg,_,id,[]) :- !.
eterms_special_builtin('\\==/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('==/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('display/1',_Sg,_,id,[]) :- !.
%eterms_special_builtin('var/1',_Sg,_,id,[]) :- !.
	% set_top_type(T),
        % varset(Sg,Condvars).
eterms_special_builtin('free/1',_Sg,_,id,[]) :- !.
%eterms_special_builtin('nonvar/1',_Sg,_,id,[]) :- !.
	% set_top_type(T),
	% varset(Sg,Condvars).
eterms_special_builtin('not_free/1',_Sg,_,id,[]) :- !.
eterms_special_builtin('ground/1',_Sg,_,id,[]) :- !.
	% set_top_type(T),
	% varset(Sg,Condvars).
% eterms_special_builtin('float/1',Sg,type(T),Condvars):-
% 	set_float_type(T),
% 	varset(Sg,Condvars).
% eterms_special_builtin('number/1',Sg,type(T),Condvars):-
% 	set_numeric_type(T),
% 	varset(Sg,Condvars).
eterms_special_builtin('fail/0',_Sg,_,bot,[]) :- !.
eterms_special_builtin('true/0',_Sg,_,id,[]) :- !.
eterms_special_builtin('nl/0',_Sg,_,id,[]) :- !.
eterms_special_builtin('repeat/0',_Sg,_,id,[]) :- !.

eterms_special_builtin('erase/1',Sg,_,type(T),Condvars):- !,
	set_top_type(T),
	varset(Sg,Condvars).

eterms_special_builtin(Key,_Sg,Subgoal,special(KKey),[]):-
	eterms_very_special_builtin(Key,KKey,Subgoal).

eterms_very_special_builtin('=/2','=/2',_).
eterms_very_special_builtin('is/2','is/2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('functor/3','functor/3',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('arg/3','arg/3',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('>/2','>/2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('>=/2','>=/2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('=</2','=</2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('</2','</2',_):- current_pp_flag(type_eval,on).
%% GP: WARNING I have commented this clause because
%%     it was producing wrong results for the stream interpreter
%%     case study
%% eterms_very_special_builtin(_,key(KKey,Goal),Goal):-
%% 	current_pp_flag(type_eval,on),
%% 	predkey_from_sg(Goal,KKey),
%% 	assertion_read(Goal,_M,_Status,comp,Body,_VarNames,_S,_LB,_LE),
%% 	assertion_body(Goal,_Compat,_Call,_Succ,Comp,_Comm,Body),
%% 	member('basic_props:sideff'(Goal,free),Comp),
%% 	assertion_read(Goal,_M2,_Status2,comp,Body2,_VarNames2,_S2,_LB2,_LE2),
%% 	assertion_body(Goal,_Compat2,_Call2,_Succ2,Comp2,_Comm2,Body2),
%% 	member('basic_props:eval'(_),Comp2).


%------------------------------------------------------------------------%
% eterms_success_builtin(+Type,+Sv_uns,+Condvars,+Call,-Succ)             %
% Depending on Type it computes the abstraction of a builtin affecting   %
% variables Condvars and having variables Sv_uns with call subs. Call.   %
%------------------------------------------------------------------------%

eterms_success_builtin(id,_Sv_uns,_Condvars,Call,Call).
eterms_success_builtin(bot,_Sv_uns,_Condvars,_Call,'$bottom').
eterms_success_builtin(type(T),_Sv_uns,Condvars,Call,Succ):-
	keys_same_value(Condvars,T,Prime),
	eterms_extend(Prime,Condvars,Call,Succ).


keys_same_value([K|Ks],V,[K:(Name,V)|ASub]):-
	new_type_name(Name),
	insert_type_name(Name,[],0),
	keys_same_value(Ks,V,ASub).
keys_same_value([],_V,[]).

%------------------------------------------------------------------------%
% eterms_call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)        %
% Same as above but for each particular builtin.                         %
%------------------------------------------------------------------------%

precondition_builtin('is/2',(X is _Y)):- !,
	(var(X);number(X)).
precondition_builtin(_Key,_).

postcondition_builtin('list/1',list(X1),Bv,Exit):-
         TX = list,
	 new_type_name(NX),
	 insert_type_name(NX,[],0),
	 Exit_u = [X1:(NX,TX)],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).
%
postcondition_builtin('number/1',number(X1),Bv,Exit):-
         set_numeric_type(TX),
	 new_type_name(NX),
	 insert_type_name(NX,[],0),
	 Exit_u = [X1:(NX,TX)],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).
%
postcondition_builtin('num/1',num(X1),Bv,Exit):-
         set_numeric_type(TX),
	 new_type_name(NX),
	 insert_type_name(NX,[],0),
	 Exit_u = [X1:(NX,TX)],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).
%
postcondition_builtin('float/1',float(X1),Bv,Exit):-
         set_float_type(TX),
	 new_type_name(NX),
	 insert_type_name(NX,[],0),
	 Exit_u = [X1:(NX,TX)],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).
%
postcondition_builtin('integer/1',integer(X1),Bv,Exit):-
         set_int_type(TX),
	 new_type_name(NX),
	 insert_type_name(NX,[],0),
	 Exit_u = [X1:(NX,TX)],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).
%
postcondition_builtin('int/1',int(X1),Bv,Exit):-
         set_int_type(TX),
	 new_type_name(NX),
	 insert_type_name(NX,[],0),
	 Exit_u = [X1:(NX,TX)],
	 Bv_u = [X1],
	 sort(Exit_u,Exit),
	 sort(Bv_u,Bv).
%
postcondition_builtin('is/2',(X1 is Y1),Bv,Exit):-
	set_numexp_type(TY),
	set_numeric_type(TX),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
	Bv_u = [X1,Y1],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('>/2',(X > Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X:(NX,TX),Y:(NY,TY)],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('>=/2',(X >= Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X:(NX,TX),Y:(NY,TY)],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('</2',(X < Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X:(NX,TX),Y:(NY,TY)],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('=</2',(X =< Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X:(NX,TX),Y:(NY,TY)],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('=\\=/2',(X =\= Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X:(NX,TX),Y:(NY,TY)],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('=:=/2',(X =:= Y),Bv,Exit):-
	set_numexp_type(TX),
	set_numexp_type(TY),
	new_type_name(NX),
	new_type_name(NY),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	Exit_u = [X:(NX,TX),Y:(NY,TY)],
	Bv_u = [X,Y],
	sort(Exit_u,Exit),
	sort(Bv_u,Bv).
%
postcondition_builtin('functor/3',functor(X1,Y1,Z1),Vars,Exit):-
         set_int_type(TZ),
	 set_atom_type(TY),
	 set_top_type(TX),
	 new_type_name(NX),
	 new_type_name(NY),
	 new_type_name(NZ),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 insert_type_name(NZ,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).
%
postcondition_builtin('arg/3',arg(X1,Y1,Z1),Vars,Exit):-
         set_int_type(TX),
	 set_top_type(TY),
	 set_top_type(TZ),
	 new_type_name(NX),
	 new_type_name(NY),
	 new_type_name(NZ),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 insert_type_name(NZ,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).
%
postcondition_builtin('current_op/3',current_op(X1,Y1,Z1),Vars,Exit):-
	 set_top_type(TX),
	 set_atom_type(TY),
	 set_atom_type(TZ),
	 new_type_name(NX),
	 new_type_name(NY),
	 new_type_name(NZ),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 insert_type_name(NZ,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).
%
postcondition_builtin('member/2',member(X1,Y1),Vars,Exit):-
	 set_top_type(TX),
	 set_top_type(TY), % TY = pt1,
	 new_type_name(NX),
	 new_type_name(NY),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
	 Vars_u = [X1,Y1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).
%
postcondition_builtin('=../2',X1=..Y1,Vars,Exit):-
	 set_top_type(TX),
	 set_top_type(TY), %TY = pt1,
	 new_type_name(NX),
	 new_type_name(NY),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
	 Vars_u = [X1,Y1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).
%
postcondition_builtin('numbervars/3',numbervars(X1,Y1,Z1),Vars,Exit):-
         set_int_type(TZ),
	 set_int_type(TY),
	 set_top_type(TX),
	 new_type_name(NX),
	 new_type_name(NY),
	 new_type_name(NZ),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 insert_type_name(NZ,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
	 Vars_u = [X1,Y1,Z1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).
%
postcondition_builtin('name/2',name(X1,Y1),Vars,Exit):-
	 set_atom_type(TX),
	 set_top_type(TY), % TY = pt1,
	 new_type_name(NX),
	 new_type_name(NY),
	 insert_type_name(NX,[],0),
	 insert_type_name(NY,[],0),
	 Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
	 Vars_u = [X1,Y1],
	 sort(Exit_u,Exit),
	 sort(Vars_u,Vars).



eterms_arg_call_to_success(Sg,Hv,arg(X,Y,Z),Sv,Call,Proj,Succ,TypeX,TypeY):-
	eterms_call_to_entry(Sv,Sg,Hv,arg(X,Y,Z),not_provided,[],Proj,Entry,ExtraInfo), % TODO: add some ClauseKey?
       	get_type(X,Entry,TypeX),
	get_type(Y,Entry,TypeY),
	new_type_name(NX),
	new_type_name(NY),
	new_type_name(NZ),
	insert_type_name(NX,[],0),
	insert_type_name(NY,[],0),
	insert_type_name(NZ,[],0),
	sort([X:(NX,int),Y:(NY,term),Z:(NZ,term)],Prime1), % postcondition builtin
	( 
	    concret(TypeX,ValuesX,[],[]) -> 
	    (
		getargtypes(TypeY,ValuesX,ValuesY,[],_,_) ->
		resetunion,
		set_union(ValuesY,TZ),
		replacetype(Z,Entry,TZ,Prime0),
		eterms_glb(Prime0,Prime1,Prime2)
	    ;
		Prime2 = Prime1
	    )
	; 
	    Prime2 = Prime1
	),
	eterms_glb(Prime2,Entry,Prime3),
	eterms_exit_to_prime(Sg,Hv,arg(X,Y,Z),Sv,Prime3,ExtraInfo,Prime),
	eterms_extend(Prime,Sv,Call,Succ).

eterms_call_to_success_builtin('arg/3',Sg,Sv,Call,Proj,Succ):- !,
	sort([X,Y,Z],Hv),
	eterms_arg_call_to_success(Sg,Hv,arg(X,Y,Z),Sv,Call,Proj,Succ,_,_).
%
eterms_call_to_success_builtin('functor/3',Sg,Sv,Call,Proj,Succ):- !,
	sort([X,Y,Z],Hv),
	Head = functor(X,Y,Z),
	eterms_call_to_entry(Sv,Sg,Hv,Head,not_provided,[],Proj,Entry,ExtraInfo), % TODO: add some ClauseKey?
	get_type(X,Entry,TypeX),
	get_type(Y,Entry,TypeY),
	get_type(Z,Entry,TypeZ),
	( getfunctors(TypeX,ValuesX) -> true ; true),
	( concret(TypeY,ValuesY,[],[]) -> true ; true),
	( concret(TypeZ,ValuesZ,[],[]) -> true ; true),
	  new_type_name(NX),
	  new_type_name(NY),
	  new_type_name(NZ),
	  insert_type_name(NX,[],0),
	  insert_type_name(NY,[],0),
	  insert_type_name(NZ,[],0),
	  sort([X:(NX,term),Y:(NY,atm),Z:(NZ,int)],Prime1),
	( 
	    setof(f(X,Y,Z),(getvalue(X,ValuesX),getvalue(Y,ValuesY),getvalue(Z,ValuesZ),functor(X,Y,Z)),ListF) -> 
	    split(ListF,ListX,ListY,ListZ),
	    new_type_symbol(TX),
	    new_type_symbol(TY),
	    new_type_symbol(TZ),
	    sort(ListX,DefX1),
	    sort(ListY,DefY1),
	    sort(ListZ,DefZ1),
	    varset(DefX1,VarsX),
	    type_escape_term_list(DefX1,DefX),
	    type_escape_term_list(DefY1,DefY),
	    type_escape_term_list(DefZ1,DefZ),
	    unifytoterm(VarsX),
	    insert_rule(TX,DefX),
	    insert_rule(TY,DefY),
	    insert_rule(TZ,DefZ),
	    sort([X:(NX,TX),Y:(NY,TY),Z:(NZ,TZ)],Prime0),
	    eterms_glb(Prime0,Prime1,Prime2)
	;
	    Prime2 = Prime1
	),
	eterms_glb(Prime2,Entry,Prime3),
	eterms_exit_to_prime(Sg,Hv,Head,Sv,Prime3,ExtraInfo,Prime),
	eterms_extend(Prime,Sv,Call,Succ).
%
eterms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):- !,
	eterms_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
%
eterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
	    ( Key = '>/2' ; Key = '>=/2' ; Key = '=</2' ; Key = '</2' ), !,
	    TY = 'arithmetic:arithexpression',
	    TX = 'arithmetic:arithexpression',
	    new_type_name(NX),
	    new_type_name(NY),
	    insert_type_name(NX,[],0),
	    insert_type_name(NY,[],0),
	    Exit_u = [X:(NX,TX),Y:(NY,TY)],
	    Bv_u = [X,Y],
	    sort(Exit_u,Exit),
	    sort(Bv_u,Bv),
	    functor(Sg,F,2),
	    functor(G,F,2),
	    arg(1,G,X),
	    arg(2,G,Y),
	    eterms_exit_to_prime(Sg,Bv,G,Sv,Exit,(no,Proj),Prime1),
	    eterms_glb(Proj,Prime1,Prime2),
	    (
		Prime2 \== '$bottom' ->
		abs_eval_arithcomp(Sg,Sv,Prime2,Prime)
	    ;
		Prime = '$bottom'
	    ),
	    eterms_extend(Prime,Sv,Call,Succ).
%
eterms_call_to_success_builtin('is/2',(X is Y),Sv,Call,Proj,Succ):- !,
	(
 	    precondition_builtin('is/2',(X is Y)) ->
	    TY = 'arithmetic:arithexpression',
	    new_type_name(NY),
	    insert_type_name(NY,[],0),
	    varset(Y,Svy),
	    eterms_project(Svy,Proj,Projy),
	    eterms_exit_to_prime(p(Y),[Y1],p(Y1),Svy,[Y1:(NY,TY)],(no,Projy),Primey),
	    eterms_glb(Projy,Primey,Primey2),
	    (
		Primey2 \== '$bottom' ->
		abs_eval_arith(Y,Primey2,Type),		
		TX = Type,
		new_type_name(NX),
		get_list_names_is(Projy,NameSelec),
		insert_type_name(NX,NameSelec,0),
		varset(X,Svx),
		eterms_project(Svx,Proj,Projx),
		eterms_exit_to_prime(p(X),[X1],p(X1),Svx,[X1:(NX,TX)],(no,Projx),Primex),
		eterms_glb(Projx,Primex,Primex2),
		(
		    Primex2 \== '$bottom' ->
		    append(Primex2,Primey2,Prime_u),
		    sort(Prime_u,Prime),
		    eterms_extend(Prime,Sv,Call,Succ)
		;
		    Succ = '$bottom'
		)
	    ;
		Succ = '$bottom'
	    )
	;
	    Succ = '$bottom'
	).
%
eterms_call_to_success_builtin(key(Key,SubGoal),_Sg,Sv,Call,Proj,Succ):- !,
	(
	    getvalues_comp_cond(Sv,Proj,Vals)->
	    (
		generateSucc0_cond(Vals,SubGoal,Vals,Proj,Prime)-> true
	    ;
		Prime = '$bottom'
	    )
	;
	    apply_trusted0(Proj,Key,SubGoal,Sv,eterms,_,Prime)
	),
	eterms_extend(Prime,Sv,Call,Succ).



% eterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
% 	(
% 	    precondition_builtin(Key,Sg) ->
% 	    postcondition_builtin(Key,Bg,Bv,Exit),
% 	    eterms_exit_to_prime(Sg,Bv,Bg,Sv,Exit,(no,Proj),Prime1),
% 	    eterms_glb(Proj,Prime1,Prime),
% 	    eterms_extend(Prime,Sv,Call,Succ)
% 	;
% 	    Succ = '$bottom'
% 	).



%------------------------------------------------------------------------%
%			    USER INTERFACE
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% eterms_input_user_interface(+InputUser,+Qv,-ASub)                       %
% Obtains the abstract substitution ASub from user supplied information. %
%------------------------------------------------------------------------%

eterms_input_user_interface(InputUser,Qv,ASub):-
        obtain_Asub_user(InputUser,ASub0),
	sort(ASub0,ASub_s),
	reduce_same_var(ASub_s,ASub1),
	substitution(ASub1,Vars,_),
	ord_subtract(Qv,Vars,TopV),
	variables_are_top_type(TopV,ASub2),
	sort(ASub2,ASub3),
	merge(ASub1,ASub3,ASub).

obtain_Asub_user([],[]):- !.
obtain_Asub_user([User|InputUser],[X:(Name,T)|ASub]):-
	functor(User,T,_),
	arg(1,User,X),
	new_type_name(Name),
	insert_type_name(Name,[],0),
	obtain_Asub_user(InputUser,ASub).

reduce_same_var([X:(Name,T)|ASub],NewASub):-
	reduce_same_var_(ASub,X,Name,T,NewASub).
reduce_same_var([],[]).

reduce_same_var_([Y:(NameY,TY)|ASub],X,NameX,TX,NewASub):-
	reduce_same_var__(Y,NameY,TY,X,NameX,TX,ASub,NewASub).
reduce_same_var_([],X,Name,T,[X:(Name,T)]).

reduce_same_var__(Y,_NameY,TY,X,NameX,TX,ASub,NewASub):-
	X == Y, !,
	type_intersection_2(TY,TX,T),
	reduce_same_var_(ASub,X,NameX,T,NewASub).
reduce_same_var__(Y,NameY,TY,X,NameX,TX,ASub,[X:(NameX,TX)|NewASub]):-
	reduce_same_var_(ASub,Y,NameY,TY,NewASub).

% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
% 	Type=..[T,X],
% 	inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).

eterms_input_interface(ground(X),perfect,Acc,[gnd(X)|Acc]).
eterms_input_interface(regtype(T),perfect,Acc,[T|Acc]):-
        functor(T,_,1),!,
        may_be_var(Acc).
eterms_input_interface(regtype(T),perfect,Acc,[NonPT|Acc]):-
        functor(T,_,2),!,
        arg(1,T,V),
        assert_param_type_instance(T,NonPType),
        functor(NonPT,NonPType,1),
        arg(1,NonPT,V),
        may_be_var(Acc).
eterms_input_interface(member(X,L),perfect,Acc,[P|Acc]):-
	type_escape_term_list(L,Def),
        new_type_symbol(T),
	insert_rule(T,Def),
	P =.. [T,X].

may_be_var([]):- !.
may_be_var(_Acc).

%------------------------------------------------------------------------%
% eterms_asub_to_native(+ASub,+Qv,+Flag,-OutputUser,-Comps)              %
% Transforms abstract substitution ASub to user friendly format.         %
%------------------------------------------------------------------------%

eterms_asub_to_native(ASub,_Qv,Flag,OutputUser,[]):-
	eterms_asub_to_native0(ASub,OutputUser1),
	eterms_asub_to_native1(OutputUser1,Flag,OutputUser).

eterms_asub_to_native1(OutputUser1,Flag,OutputUser):-
	equiv_types(OutputUser1,OutputUser2),
	revert_types(OutputUser2,OutputUser,Symbols,[]),
	recorda_required_types_(Flag,Symbols).

eterms_asub_to_native0([X:(_N,T)|ASub],[Type|OutputUser]):-
	revert_type(T,X,Type),
	eterms_asub_to_native0(ASub,OutputUser).
eterms_asub_to_native0([],[]).

revert_type(T,X,Type):-
	type_symbol(T), !,
	functor(Type,T,1),
	arg(1,Type,X).
%	Type=..[T,X].
revert_type(T,X,(X=T)).      

recorda_required_types_(no,_Symbols).
recorda_required_types_(yes,Symbols):-
	recorda_required_types(Symbols).

%------------------------------------------------------------------------%
% eterms_output_interface(+ASub,-Output)                                  %
% Transforms abstract substitution ASub to a more readible but still     %
% close to internal format.                                              %
%------------------------------------------------------------------------%

eterms_output_interface(ASub,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

eterms_collect_abstypes([],Types,Types).
eterms_collect_abstypes([_:(_,Type)|Abs],Types0,Types):-
	insert(Types0,Type,Types1),
	eterms_collect_abstypes(Abs,Types1,Types).

eterms_rename_abs([],_,_,[]).
eterms_rename_abs([C|Call],Types,Names,[RenC|RenCall]):-
	C = Var:(_Name,Type),
	RenC = Var:(RenName,RenType),
	get_value_(Types,Type,RenType),
%jcf-begin
%	get_value_(Names,Name,RenName),
	new_type_name(RenName),         % taken from obtain_Asub_user/2.
	insert_type_name(RenName,[],0), % taken from obtain_Asub_user/2.
%jcf-end
	eterms_rename_abs(Call,Types,Names,RenCall).

get_value_(Rens,Type,RenType):-
	assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%

eterms_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
eterms_identical_abstract(ASub1,ASub2):-
	eterms_identical_abstract0(ASub1,ASub2).

eterms_identical_abstract0([X:(_Name0,Type0)|ASub0],[Y:(_Name1,Type1)|ASub1]):-
	X==Y,
        dz_equivalent_types(Type0,Type1),
	eterms_identical_abstract0(ASub0,ASub1).
eterms_identical_abstract0([],[]).


%-------------------- evalterms

get_less_numeric_type(T,int):-
        dz_type_included(T,int), !.
get_less_numeric_type(T,flt):- 
	    dz_type_included(T,flt), !.
get_less_numeric_type(_T,num).

getargtypes(Type,Args,ValuesX,Rest,Selectors,RestSel):-
	get_typedefinition(Type,Def),
        getargtypes_(Def,Args,ValuesX,Rest,Selectors,RestSel).

getargtypes_([],_,Rest,Rest,RestSel,RestSel).
getargtypes_([Type|Def],Args,ValuesX,Rest,Selectors,RestSel):-
	compound_pure_type_term(Type, Term, Name, Arity),
	!,
	getargtypes1(Args,Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel1),
        getargtypes_(Def,Args,Rest1,Rest,RestSel1,RestSel).

getargtypes1([],_Arity,_Term,Rest,Rest,_Name,RestSel,RestSel).
getargtypes1([Arg|Args],Arity,Term,[Val|ValuesX],Rest1,Name,[[Name/Arg]|Selectors],RestSel):-
	Arg =< Arity,
        Arg > 0,
	!,
	arg(Arg,Term,Val),
	getargtypes1(Args,Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel).
getargtypes1([_|Args],Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel):-
	getargtypes1(Args,Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel).
	
	
set_union([T],T).
set_union([T1,T2|L],T):-
    type_union(T1,T2,T3),
    set_union([T3|L],T).

replacetype(Z,[X:(N,_T)|Entry],TZ,[X:(N,TZ)|Entry]):-
	Z == X,!.
replacetype(Z,[X:(N,T)|Entry],TZ,[X:(N,T)|Prime]):-
	replacetype(Z,Entry,TZ,Prime).

getfunctors(Type,ValuesX):-
	get_typedefinition(Type,Def),
        getfunctors_(Def,ValuesX).

getfunctors_([],[]).
getfunctors_([Type|Def],[Val|ValuesX]):-
	compound_pure_type_term(Type, _Term, Name, Arity),
	!,
	functor(Val,Name,Arity),
        getfunctors_(Def,ValuesX).


split([],[],[],[]).
split([f(X,Y,Z)|ListF],[X|ListX],[Y|ListY],[Z|ListZ]):-
	split(ListF,ListX,ListY,ListZ).

getvalue(_X,Vals):- var(Vals),!.
getvalue(X,Vals):- member(X,Vals).

unifytoterm([]).
unifytoterm([V|VarsX]):-
	V = term,
	unifytoterm(VarsX).



abs_eval_arithcomp(X,Vars,Prime,Succ):-
	(
	    getvalues_comp(Vars,Prime,Vals)->
	    ( 
		generateSucc0(Vals,X,Vals,Prime,Succ)-> true
	    ;
		Succ = '$bottom'
	    )
	;
	    Succ = Prime
	).


generateSucc0([],Goal,_VALS,Prime,Succ):- 
	(
	    call(Goal) -> Succ = Prime
	;
	    Succ = '$bottom'
	).
generateSucc0(Vals,X,Vals,Prime,Succ):-
	generateSucc(Vals,X,Vals,Prime,Succ).


generateSucc0_cond([],Sg,_Vals,Proj,Prime):-
	(
	    can_be_evaluated(Sg),call(Sg) -> Prime = Proj
	;
	    Prime = '$bottom'
	).
generateSucc0_cond(Vals,Sg,Vals,Proj,Prime):-
	generateSucc_cond(Vals,Sg,Vals,Proj,Prime).


generateSucc([],_Goal,_VALS,_Prime,[]). 
generateSucc([X/Val|Vals],Goal,VALS,Prime,[X:(N,T)|Succ]):-
	setof(Z,Goal^(member(Z,Val),satisfy(Goal,X,Z,VALS)),Tconc),!,
	member(Y:(Name,_),Prime),
	X == Y, % TODO: cut if X is unique in Prime
	N_e = Name,
	get_canonical_name(N_e,N),
	new_type_symbol(T),	
	insert_rule(T,Tconc),
	generateSucc(Vals,Goal,VALS,Prime,Succ).


generateSucc_cond([],_Goal,_VALS,_Prime,[]). 
generateSucc_cond([X/Val|Vals],Goal,VALS,Prime,[X:(N,T)|Succ]):-
	setof(Z,Goal^(member(Z,Val),satisfy_cond(Goal,X,Z,VALS)),Tconc),!,
	member(Y:(Name,_),Prime),
	X == Y, % TODO: cut if X is unique in Prime
	N_e = Name,
	get_canonical_name(N_e,N),
	new_type_symbol(T),	
	type_escape_term_list(Tconc,TDef),
	insert_rule(T,TDef),
	generateSucc_cond(Vals,Goal,VALS,Prime,Succ).



satisfy(G,X,Z,VALS):-
	X = Z,
	maplist(apply_,VALS),
	call(G).


satisfy_cond(G,X,Z,VALS):-
	X = Z,
	maplist(apply_,VALS),
	can_be_evaluated(G),	
	'$meta_call'(G).
%	call(G).


abs_eval_arith(X,Proj,ResultType):-
	varset(X,Vars),
	getvalues_(Vars,Proj,Vals,Concr),
	setof(Z,X^calc(X,Z,Vals),T3),
	new_type_symbol(Type),
	insert_rule(Type,T3),
	( 
	    var(Concr) ->
            ResultType = Type 
	;
	    get_less_numeric_type(Type,ResultType)
	).


getvalues_comp([],_Prime,[]):- !.
getvalues_comp([V|Vars],Prime,[Val|Vals]):-
	getvaluescomp(V,Prime,Val),
	getvalues_comp(Vars,Prime,Vals).


getvalues_comp_cond([],_Prime,[]):- !.
getvalues_comp_cond([V|Vars],Prime,[Val|Vals]):-
	getvaluescomp_cond(V,Prime,Val),
	getvalues_comp_cond(Vars,Prime,Vals).


getvaluescomp(X,Prime,X/Vals):-
	member(Y:(_,Type),Prime),
	X == Y, % TODO: cut if X is unique in Prime
	concret(Type,Vals,[],[]).


getvaluescomp_cond(X,Prime,X/Vals):-
	member(Y:(_,Type),Prime),
	X == Y, % TODO: cut if X is unique in Prime
	( 
	    Type = term -> Vals = [X]
	;
	    concret(Type,Vals,[],[])
	).


getvalues_([],_,[],_):- !.
getvalues_([V|Vars],Proj,[Val|Vals],Concr):- 
	getvalues(V,Proj,Val,Concr),
	getvalues_(Vars,Proj,Vals,Concr).

getvalues(X,Proj,X/Vals,Concr):-
	member(Y:(_,Type),Proj),
	X == Y, % TODO: cut if X is unique in Proj
	(
%	    member(Type,[int,flt,num,arithexpression]) ->
	    concret(Type,Values,[],[]) -> 
%	    get_type_definition(Type,Vals)
	    Vals = Values
	;
    	    Concr = no,
	    choose_one(Type,Vals)
	).



choose_one('basic_props:int',[3]) :- !.
choose_one('basic_props:flt',[3.0]) :- !.
choose_one('basic_props:num',[3.0,3]) :- !.
choose_one('arithmetic:arithexpression',[3.0,3]) :- !.
choose_one(int,[3]) :- !.
choose_one(flt,[3.0]) :- !.
choose_one(num,[3.0,3]) :- !.
choose_one(arithexpression,[3.0,3]) :- !.
choose_one(_,[3.0,3]).


calc(X,Z,Vals):-
	maplist(apply_,Vals),
	Z is X.

apply_(X/Y):- member(X,Y). % TODO: cuts needed?

get_list_names_is([],[]).
get_list_names_is([_:(Name,_)|Proj],[(['$is'],Name)|List]):-
	get_list_names_is(Proj,List).



%-------------------- svterms

determinate_sel(Var,Sel,Types):-
	get_type(Var,Types,Type),
	existpos(Type,Sel,[]),
	!.
	

replaceintype((NameX,Tx),Sx,(NameY,Ty),Sy,(NameX,Txn)):-
	reverse(Sx,RSx),
	reverse(Sy,RSy),
	gettypeinpos(Tx,RSx,TTx),
	gettypeinpos(Ty,RSy,TTy),
	(
	    dz_equivalent_types(TTx,TTy) ->
	    Txn = Tx
	;
	    replacetypeinpos(Tx,RSx,TTy,Txn),
	    addnamesinpos(NameX,Sx,NameY,Sy)
	), !.
replaceintype(_,_,_,_,_):-
	display(user,'SOMETHING WAS WRONG With same value selectors'), nl(user).
	

existpos(_Type,[],_Seen):-!.
existpos(T,_,Seen):-
	member(T,Seen),!,
	fail.
existpos(T,[F/A|S],Seen):-
%	get_type_definition(T,Def),
	get_typedefinition(T,Def),
	gettpos(Def,F,A,NT),
	!,
	existpos(NT,S,[T|Seen]).

gettypeinpos(T,[],T) :- !.
gettypeinpos(T,[F/A|S],ST):-
%	get_type_definition(T,Def),
	get_typedefinition(T,Def),
	gettpos(Def,F,A,NT),
	!,
	gettypeinpos(NT,S,ST).

gettpos([],_F,_A,_NT):- !,fail.
gettpos([C|_Def],F,A,NT):-
	compound_pure_type_term(C,Term,F,Arity),
	A =< Arity,!,
	arg(A,Term,NT).
gettpos([_|Def],F,A,NT):-
	gettpos(Def,F,A,NT).
	

replacetypeinpos(_Tx,[],TTy,TTy) :- !.
replacetypeinpos(Tx,[F/A|S],TTy,Txn):-
	get_type_definition(Tx,Def),
	replacetypeinposdef(Def,F,A,S,TTy,NDef),
        new_type_symbol(Txn),
	insert_rule(Txn,NDef), !.
replacetypeinpos(_,_,_,_):-
	display(user,'SOMETHING WAS WRONG With same value selectors'), nl(user).

replacetypeinposdef([],_F,_A,_S,_TTy,_NDef):- !,fail.
replacetypeinposdef([C|Def],F,A,S,TTy,[NC|Def]):- 
	compound_pure_type_term(C,Term,F,Arity),
	A =< Arity,!,
	arg(A,Term,T),
	replacetypeinpos(T,S,TTy,NT),
	functor(NTerm,F,Arity),
	arg(A,NTerm,NT),
	copyargsbutA(Arity,A,Term,NTerm),
	construct_compound_pure_type_term(NTerm,NC).
replacetypeinposdef([C|Def],F,A,S,TTy,[C|NDef]):- 
	replacetypeinposdef(Def,F,A,S,TTy,NDef).

copyargsbutA(0,_A,_Term,_NTerm) :- !.
copyargsbutA(Arity,A,Term,NTerm):-
	( 
	    Arity \== A ->
	    arg(Arity,Term,Arg),
	    arg(Arity,NTerm,Arg)
	; 
	    true
	),
	NArity is Arity - 1,
	copyargsbutA(NArity,A,Term,NTerm).
	
addnamesinpos(NameX,Sx,NameY,Sy):-
	retract_type_name_(NameX,EQNameX,Lx,C),
	( EQNameX \== NameY ->
	  get_type_name(NameY,Ly)
	; Ly = Lx
	),
	deleteposdeeperSx(Lx,Sx,Lx2),
	addposfromY(Ly,Lx2,Sy,Sx,Lx3),
	insert_type_name(EQNameX,Lx3,C),!.	

% PP: Take a canonical name if NameX has been already retracted
retract_type_name_(NameX,NameX,Lx,C) :-
	retract_type_name(NameX,Lx,C),!.
retract_type_name_(NameX,EQName,Lx,C) :-
	get_equiv_name(NameX,EQName),
	retract_type_name(EQName,Lx,C).


deleteposdeeperSx([],_Sx,[]).
deleteposdeeperSx([(S,_N)|Lx],Sx,Lx2):-
	dlist([_|_],S,Sx),!,
	deleteposdeeperSx(Lx,Sx,Lx2).
deleteposdeeperSx([(S,N)|Lx],Sx,[(S,N)|Lx2]):-
	deleteposdeeperSx(Lx,Sx,Lx2).
	
addposfromY([],Lx2,_Sy,_Sx,Lx2).
addposfromY([(S,N)|Ly],Lx2,Sy,Sx,[(NS,N)|Lx3]):-
	dlist(NNS,S,Sy),!,
	dlist(NNS,NS,Sx),
	addposfromY(Ly,Lx2,Sy,Sx,Lx3).
addposfromY([_|Ly],Lx2,Sy,Sx,Lx3):-
	addposfromY(Ly,Lx2,Sy,Sx,Lx3).


%-------------------- types operations



eterms_multi_part_conc(A,ASub,List):- 
	varset(A,Vars_s),
	varsbag(A,AVars,[]),
	get_all_paths(Vars_s,ASub,Paths),
        cross_product(Paths,Llist),
	maplist(splitlist,Llist,R),
	maplist(build_concr(A,Vars_s,AVars),R,List).


build_concr((LT,S),A,Vars_s,AVars,(NA,S)):-
	copy_term(A,NA),
	varsbag(NA,NAVars,[]),
	assign_terms(Vars_s,LT,AVars,NAVars).

assign_terms([],[],_,_).
assign_terms([V|Vars_s],[T|LT],AVars,NAVars):-
	nth(N,AVars,X),
	X==V,
	nth(N,NAVars,NX),
	NX = T,
	assign_terms(Vars_s,LT,AVars,NAVars).


	


splitlist(Llist,(T,S)):-
	splitlist_(Llist,T,S).

splitlist_([],[],[]).
splitlist_([(T,S)|List],[T|Terms],Subs):-
	append(S,TailS,Subs),
	splitlist_(List,Terms,TailS).


get_all_paths([],_,[]).
get_all_paths([V|Vars_s],ASub,[VPaths|AllPaths]):-
	get_type(V,ASub,Type),
	partial_concret(Type,VPaths,[],[]),
	get_all_paths(Vars_s,ASub,AllPaths).



partial_concret_def([],L,L,_).
partial_concret_def([T1|Def],List1,List2,Seen):-
	partial_concret(T1,List1,List0,Seen),
	partial_concret_def(Def,List0,List2,Seen).

addarg([],_,_,_,L,L).
addarg([(C,CS)|ListArg],F,A,S,[(Term,TermS)|L1],L2):-
	copy_term((F,S),(Term,Term1S)),
	arg(A,Term,C),
	append(CS,Term1S,TermS),
	addarg(ListArg,F,A,S,L1,L2).
	

buildarg(L,M,M,_,_):- var(L),M=L, !. % TODO: move cut?
buildarg([(F,S)|Prev],L,T,A,ListArg):-
	addarg(ListArg,F,A,S,L,L2),
	buildarg(Prev,L2,T,A,ListArg).

partial_concret_arg(0,_,P,P,_,_) :- !.
partial_concret_arg(A,Term,Prev,List,List2,Seen):-
	arg(A,Term,Arg1),
	partial_concret(Arg1,ListArg1,[],Seen),
        buildarg(Prev,NewPrev,List2,A,ListArg1),
	A1 is A -1,
	partial_concret_arg(A1,Term,NewPrev,List,List2,Seen).
	

defined_type_symbol(Type,Def):-
        em_defined_type_symbol(Type,Def).
% TODO: add cut somewhere if Def is unique for Type
defined_type_symbol(Type,Def):-
	equiv_type(Type,Type1),
	em_defined_type_symbol(Type1,Def).


partial_concret(Type,List1,List2,Seen):-
	defined_type_symbol(Type,Def),!,
	( 
	    member(Type,Seen) ->
	    new_type_name(N),
	    insert_type_name(N,[],0),
	    List1 = [(A,[A:(N,Type)])|List2]
	;
	    partial_concret_def(Def,List1,List2,[Type|Seen])
	).
partial_concret(Type,List1,List2,Seen):-
	compound_pure_type_term(Type,Term,F,A),!,
	functor(Seed,F,A),
	partial_concret_arg(A,Term,[(Seed,[])|List2],List1,List2,Seen).
partial_concret(^(Term),[(Term,[])|List],List,_) :- !.
partial_concret(Term,[(Term,[])|List],List,_):- number(Term),!.
partial_concret(Term,[(Term,[])|List],List,_):- Term = [_|_],!.
partial_concret(Term,[(Term,[])|List],List,_):- Term = [],!.
partial_concret(Type,[(A,[A:(N,Type)])|List],List,_):-
	    new_type_name(N),
	    insert_type_name(N,[],0).


%-----------------------------------------------------------








get_det_conc_args(0,_Term,_NA,ASub,ASub) :- !.
get_det_conc_args(Arity,Term,NA,NASub,ASub):-
	arg(Arity,Term,Arg1),
	get_det_conc(Arg1,_,A,NASub,NASub2),
	arg(Arity,NA,A),
	Arity1 is Arity - 1,
	get_det_conc_args(Arity1,Term,NA,NASub2,ASub).


get_det_conc(Type,A,A,[A:(N,Type)|ASub],ASub):-
	native_type_symbol(Type),!,
	new_type_name(N),
	insert_type_name(N,[],0).
get_det_conc(Type,A,NA,NASub,ASub):-
	get_typedefinition(Type,[SingletonDef]),!,
	get_det_conc_(SingletonDef,A,NA,NASub,ASub).	
get_det_conc(Type,A,A,[A:(N,Type)|ASub],ASub):-
	new_type_name(N),
	insert_type_name(N,[],0).

	
 
get_det_conc_(SingletonDef,_A,NA,NASub,ASub):-
	compound_pure_type_term(SingletonDef,Term,F,Arity),!,
	functor(NA,F,Arity),
	get_det_conc_args(Arity,Term,NA,NASub,ASub).
get_det_conc_(^(Term),_,Term,ASub,ASub) :- !.
get_det_conc_(Term,_,Term,ASub,ASub):- number(Term),!.
get_det_conc_(Term,_,Term,ASub,ASub):- Term = [_|_],!.
get_det_conc_(Term,_,Term,ASub,ASub):- Term = [],!.
get_det_conc_(SingletonDef,A,NA,NASub,ASub):- !,
	get_det_conc(SingletonDef,A,NA,NASub,ASub).	

eterms_part_conc(A,ASub,NA,NASub):- 
	eterms_parc_conc_(A,ASub,NA,NASub,ASub).
 
eterms_parc_conc_(A,ASub,NA,NASub,NASubT):- 
	var(A),!,
	get_type(A,ASub,Type),
	get_det_conc(Type,A,NA,NASub,NASubT).
eterms_parc_conc_(A,ASub,NA,NASub,NASubT):- 	
	functor(A,F,Arity),
	functor(NA,F,Arity),
	eterms_parc_conc_arg(Arity,A,NA,ASub,NASub,NASubT).

eterms_parc_conc_arg(0,_A,_NA,_,ASub,ASub) :- !.
eterms_parc_conc_arg(Arity,A,NA,ASub,NASub,NASubT):-
	arg(Arity,A,Arg1),
	Arity1 is Arity - 1,
	eterms_parc_conc_(Arg1,ASub,NAArg,NASub,NASub2), 	
	arg(Arity,NA,NAArg),	
	eterms_parc_conc_arg(Arity1,A,NA,ASub,NASub2,NASubT).
