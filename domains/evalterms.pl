:- module(evalterms,[                             
	evalterms_call_to_success_builtin/6,
	evalterms_widen/3,
	evalterms_widencall/3,
	evalterms_special_builtin/5
   ], [assertions,regtypes,basicmodes,datafacts]).

:- use_module(domain(eterms), 
	[
	    eterms_less_or_equal/2,
	    eterms_compute_lub_el/3,
	    eterms_identical_abstract/2,
	    eterms_call_to_success_fact/9,
	    eterms_project/5,
	    eterms_exit_to_prime/7,
	    eterms_call_to_entry/9,
	    eterms_glb/3,
	    eterms_extend/4,
	    resetunion/0,
	    type_union/3,
	    make_determ_wide_rules/1,
	    precondition_builtin/2,
	    postcondition_builtin/4,
	    get_type/3
 	]).


:- use_module(spec(unfold_builtins), 
	[can_be_evaluated/1]).


:- use_module(domain(termsd), 
	[ 
	concrete/4,
	shortening_el/2 
	]).


:- use_module(library(lists), 
	[
	    member/2,
	    append/3,
	    dlist/3
	]).

:- use_module(library(aggregates), 
	[
	    (^)/2,
	    findall/4,
	    setof/3
	]).

:- use_module(library(terms_vars), 
	[
	  varset/2
	]).

:- use_module(library(sets), 
	[ 
	    merge/3,
	    ord_delete/3
	]).
:- use_module(library(sort), 
	[
	    sort/2
	]).

:- use_module(library(hiordlib), [maplist/2]).

:- use_module(typeslib(typeslib), 
	[
	    compound_pure_type_term/4,
	    construct_compound_pure_type_term/2,
	    dz_type_included/2,
	    em_defined_type_symbol/2,
	    get_type_definition/2,
	    get_type_name/2,
	    insert_rule/2,
	    insert_type_name/3,
	    new_type_name/1,
	    new_type_symbol/1,
	    pure_type_term/1,
	    retract_rule/1,
	    retract_type_name/3,
	    rule_type_symbol/1,
	    set_atom_type/1,
	    set_int_type/1,
	    set_top_type/1,
	    top_type/1,
	    type_escape_term_list/2
	]).

:- use_module(domain(deftypes), [absu/1]).


evalterms_special_builtin('!/0',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@=</2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@>/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@>=/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@</2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('\\==/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('==/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('display/1',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('get_code/1',Sg,_Subgoal,type(T),Condvars):-
        set_int_type(T),
	varset(Sg,Condvars).
% eterms_special_builtin('integer/1',Sg,_Subgoal,type(T),Condvars):-
%         set_int_type(T),
% 	varset(Sg,Condvars).
evalterms_special_builtin('atom/1',Sg,_Subgoal,type(T),Condvars):-
        set_atom_type(T), % no, it is atom or num type
	varset(Sg,Condvars).
evalterms_special_builtin('atomic/1',Sg,_Subgoal,type(T),Condvars):-
        set_atom_type(T), % no, it is atom or num type
	varset(Sg,Condvars).
evalterms_special_builtin('var/1',_Sg,_Subgoal,id,[]).
	% set_top_type(T),
	% varset(Sg,Condvars).
evalterms_special_builtin('nonvar/1',_Sg,_Subgoal,id,[]).
	% set_top_type(T),
	% varset(Sg,Condvars).
evalterms_special_builtin('ground/1',_Sg,_Subgoal,id,[]).
	% set_top_type(T),
	% varset(Sg,Condvars).
% eterms_special_builtin('float/1',Sg,_Subgoal,type(T),Condvars):-
% 	set_float_type(T),
% 	varset(Sg,Condvars).
% eterms_special_builtin('number/1',Sg,_Subgoal,type(T),Condvars):-
% 	set_numeric_type(T),
% 	varset(Sg,Condvars).
evalterms_special_builtin('fail/0',_Sg,_Subgoal,bot,[]).
evalterms_special_builtin('true/0',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('nl/0',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('repeat/0',_Sg,_Subgoal,id,[]).
%
evalterms_special_builtin('erase/1',Sg,_Subgoal,type(T),Condvars):-
	set_top_type(T),
	varset(Sg,Condvars).
%
evalterms_special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
	evalterms_very_special_builtin(Key).

evalterms_very_special_builtin('=/2').
evalterms_very_special_builtin('is/2').
evalterms_very_special_builtin('functor/3').
evalterms_very_special_builtin('arg/3').
evalterms_very_special_builtin(Key):-
	can_be_evaluated(Key).


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


do_not_lub([X:(N1,_T1)|ASub1],[Y:(N2,T2)|ASub2],[X:(N1,T2)|ASub3]):-
	X==Y,
	( 
	    ( top_type(T2) ) -> true 
	;
	    get_type_name(N2,L2),
	    retract_type_name(N1,L1,C1),
	    merge(L1,L2,L3),
	    insert_type_name(N1,L3,C1)
	),
	do_not_lub(ASub1,ASub2,ASub3).
do_not_lub([],[],[]).


evalterms_widencall(Prime0,Prime1,Result):-
	(
	    eterms_less_or_equal(Prime1,Prime0) ->
	    Result = Prime0
	;
	    get_synonymous(Prime0,Synon),
	    do_not_lub(Prime0,Prime1,PrimePrime),
	    eterms_compute_lub_el(Prime0,Prime1,Prime),
	    ewiden(Prime0,Prime,Prime2,Synon),
	    ( 
		eterms_identical_abstract(Prime2,Prime) ->
		Result = PrimePrime
	    ;
		Result = Prime2
	    )
	).


:- pred evalterms_widen(+Prime0,+Prime1,-NewPrime):
absu * absu * absu #
" 
Induction step on the abstract substitution of a fixpoint.
@var{Prime0} corresponds to non-recursive and @var{Prime1} to
recursive clauses.  @var{NewPrime} is the result of apply one widening
operation to the least upper bound of the formers.  At the moment the
widening operation implemented is ``Type Graph Jungle Widening''.  ".

evalterms_widen(Prime0,Prime1,NewPrime):-
	get_synonymous(Prime0,Synon),
	eterms_compute_lub_el(Prime0,Prime1,Prime),
%	NewPrime = Prime.
	ewiden(Prime0,Prime,NewPrime,Synon).


get_synonymous('$bottom',[]).
get_synonymous([],[]).
get_synonymous([X:(N,_)|Prime],[X:L|Synon]):-
	get_type_name(N,LWs),
	findall(N1,member(([],N1),LWs),L,[]),
	get_synonymous(Prime,Synon).

ewiden('$bottom','$bottom','$bottom',_).
ewiden('$bottom',Prime,Prime,_).
ewiden([],[],[],[]).
ewiden([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime],[X:Syn|Synon]):-
	ewiden_el(T1,T2,T,Syn),
	ewiden(Prime0,Prime,NewPrime,Synon).

obtain_all_names_selectors([],_N2,_,_,L,L,_).
obtain_all_names_selectors([(S,N)|LWs],N2,Sel,Seen,NL,Tail,Syn):-

% in order to manage the case when there is not relation between the new approximation and the older
	member(N,Syn) ,!,
% in order to manage the case when there is not relation between the new approximation and the older

%	N == N2,!,
	append(S,Sel,S1),
	( S1 = [] -> NL = LW ;	NL = [(S1,N2)|LW]),
	obtain_all_names_selectors(LWs,N2,Sel,Seen,LW,Tail,Syn).
obtain_all_names_selectors([(_S,N)|LWs],N2,Sel,Seen,LW,Tail,Syn):-
	member(N,Seen),!,
	obtain_all_names_selectors(LWs,N2,Sel,Seen,LW,Tail,Syn).
obtain_all_names_selectors([(S,N)|LWs],N2,Sel,Seen,LW,Tail,Syn):-
	get_type_name(N,L),
	append(S,Sel,S1),
	obtain_all_names_selectors(L,N2,S1,[N|Seen],LW,LW1,Syn),
	obtain_all_names_selectors(LWs,N2,Sel,Seen,LW1,Tail,Syn).
	

ewiden_el(T1,T2,T1,_):- T1 == T2,!.
ewiden_el(_,(N,T),(N,T),_):- top_type(T),!.
ewiden_el((_N1,T1),(N2,T2),(N2,W),_L):-
	retract_type_name(N2,LWs,Count),
%	obtain_all_names_selectors(LWs,N2,[],[],LW1,[]),

% in order to manage the case when there is not relation between the new approximation and the older

% % %   obtain_all_names_selectors(LWs,N2,[],[],LW1,[],[N2|L]),
	obtain_all_names_selectors(LWs,N2,[],[],LW1,[],[N2]),

% in order to manage the case when there is not relation between the new approximation and the older

	sort(LW1,LW),
%	findall((S,N2),member((S,N2),LWs),LW,[]), % here, the clausure
	(
	    LW == [] ->
	    ( 
		Count < 5 ->
		W = T2,
		Count1 is Count + 1,
		insert_type_name(N2,LWs,Count1)
	    ;
		shortening_el(T2,W),
	        insert_type_name(N2,LWs,0)	     
	    )
	;
	    insert_type_name(N2,LWs,0),
	    (
		member((['$is'],_N),LW) ->
		get_less_numeric_type(T2,W)
	    ;
		new_type_symbol(W),
		get_typedefinition(T2,Def),
		ewiden_def(Def,NewDef,T1,T2,W,[],LW,[],I,[]), 
		sort(NewDef,NewDef_s),
		insert_rule(W,NewDef_s),
		normalize_wide_rules(I,W),
		make_determ_wide_rules(I)
	    )
	).
% 	    restrict_labels(LWs,W,NLW),   % here, is  not necesary
% 	    update_labels(NLW,NewLW,N2),   
% 	    sort(NewLW,NewLW_s),
% 	    insert_type_name(N2,NewLW_s).
	

% restrict_labels([],_W,[]).
% restrict_labels([(S,N)|LW],W,[(S,N)|NLW]):-
% 	get_sub_term(S,W,_Subterm),!,
% 	restrict_labels(LW,W,NLW).
% restrict_labels([_|LW],W,NLW):-
% 	restrict_labels(LW,W,NLW).

% update_labels(LW,NewLW,N2):-
% 	findall((S,N2),member((S,N2),LW),List,[]),
% 	update_labels0(LW,NewLW,N2,List).


% ancestor(_S,[]):- !,fail.
% ancestor(S,[(WS,_)|_List]):-
% 	dlist([_|_],WS,S),!.
% ancestor(S,[_|List]):-
% 	ancestor(S,List).

% update_labels0([],[],_N2,_List).
% update_labels0([(S,T)|LW],New,N2,List):-
% %	(
% %	    T == N2 -> New = [(S,T)|NewLW]     % cambio
% %	    T == N2 -> New = NewLW
% %	;
% 	    (
% 		ancestor(S,List) -> 
%  			New = NewLW 
% 	    ;
% 		New = [(S,T)|NewLW]
% 	    ),
% %	),
% 	update_labels0(LW,NewLW,N2,List).


ewiden_def([],[],_T1,_T2,_W,_Sel,_LW,_Seen,I,I).
ewiden_def([T|Def],[NT|NewDef],T1,T2,W,Sel,LW,Seen,I,Tail):-
	ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,I1),
	ewiden_def(Def,NewDef,T1,T2,W,Sel,LW,Seen,I1,Tail).

ewiden_args(0,_F,_Term,_NewTerm,_T1,_T2,_W,_Sel,_LW,_Seen,I,I).
ewiden_args(A,F,Term,NewTerm,T1,T2,W,Sel,LW,Seen,I,Tail):-
	arg(A,Term,Arg),
	simplify_LW([F/A|Sel],LW,LW1),
	ewiden_elem(Arg,NewArg,T1,T2,W,[F/A|Sel],LW1,Seen,I,I1),
	arg(A,NewTerm,NewArg),
	A1 is A - 1,
	ewiden_args(A1,F,Term,NewTerm,T1,T2,W,Sel,LW,Seen,I1,Tail).

simplify_LW(_,[],[]).
simplify_LW(Sel,[(S,N)|LW],[(S,N)|LW1]):-
        dlist(_,S,Sel),!,
	simplify_LW(Sel,LW,LW1).
simplify_LW(Sel,[_|LW],LW1):-
	simplify_LW(Sel,LW,LW1).



replace(T,NT,P,Seen):-
	em_defined_type_symbol(T,Def),!,
	(
	    member((T,NT),P) -> true
	;
	    (
		member(T,Seen) -> NT = T
	    ;
		replace_def(Def,NewDef,P,[T|Seen]),
		( 
		    Def == NewDef ->
		    NT = T
		;
		    new_type_symbol(NT),		
		    sort(NewDef,NewDef_s),
		    insert_rule(NT,NewDef_s)
		)
	    )
	).
replace(T,NT,P,Seen):-
	compound_pure_type_term(T,Term,F,A),!,
	functor(NewTerm,F,A),
	replace_arg(A,Term,NewTerm,P,Seen),
	construct_compound_pure_type_term(NewTerm,NT).
replace(T,T,_,_).
		
replace_def([],[],_P,_Seen).
replace_def([T|Def],[NT|NewDef],P,Seen):-
	replace(T,NT,P,Seen),
	replace_def(Def,NewDef,P,Seen).	

replace_arg(0,_,_,_,_).
replace_arg(A,Term,NewTerm,P,Seen):-
	arg(A,Term,Arg),
        replace(Arg,NArg,P,Seen),
	arg(A,NewTerm,NArg),
	A1 is A - 1,
	replace_arg(A1,Term,NewTerm,P,Seen).


ewiden_elem(T,W,_T1,T2,W,_Sel,_LW,_Seen,I,I):- 
 	em_defined_type_symbol(T,_Def),T== T2,!.
ewiden_elem(T,NT,_T1,_T2,_W,_Sel,[],Seen,I,I):-
	replace(T,NT,Seen,[]).
ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,Tail):-
	member((Sel,N),LW),!,
	(
	    (  T == T1;	dz_type_included(T,T2))  -> NT = W,I=Tail
	;
	    new_type_symbol(NT),
%  	    ( 
%  		em_defined_type_symbol(T1,_Def) ->
%  		replace(T,T1,T1,W,U,[])  % acaaaa
%  	    ;
%  		U = T
%  	    ),
%  	    get_typedefinition(U,DefU),
	    ord_delete(LW,(Sel,N),LW1),

            get_typedefinition(T,DefT),
	    ( 
		em_defined_type_symbol(T, Defin) -> 
		DefT = Defin,
		NewSeen = [(T,NT)|Seen]
	    ;
		DefT = [T],
		NewSeen = Seen
	    ),
	    ewiden_def(DefT,DefU,T1,T2,W,Sel,LW1,NewSeen,I,I1),
	    
 	    merge([W],DefU,Def),
 	    insert_rule(NT,Def),
	    I1 = [NT|Tail]
	).
ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,Tail):-
	em_defined_type_symbol(T,Def),!,
	(
	    member((T,NT),Seen) -> I = Tail
	;
	    new_type_symbol(NT),
	    ewiden_def(Def,NewDef,T1,T2,W,Sel,LW,[(T,NT)|Seen],I,Tail),
	    sort(NewDef,NewDef_s),
	    insert_rule(NT,NewDef_s)
	).
ewiden_elem(T,NT,T1,T2,W,Sel,LW,Seen,I,Tail):-
	compound_pure_type_term(T,Term,F,A),!,
	functor(NewTerm,F,A),
	ewiden_args(A,F,Term,NewTerm,T1,T2,W,Sel,LW,Seen,I,Tail),
	construct_compound_pure_type_term(NewTerm,NT).
ewiden_elem(T,T,_T1,_T2,_W,_Sel,_LW,_Seen,I,I).



normalize_wide_rules([],_).
normalize_wide_rules([T|Rules],W):-
	em_defined_type_symbol(T, Def),
	ord_delete(Def,W,U),
	em_defined_type_symbol(W,DefW),
	merge(DefW,U,NewDef),
	retract_rule(T),
	insert_rule(T,NewDef), 
	normalize_wide_rules(Rules,W).
	
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 
%--------------------------END-WIDENING-------------------------------%
%---------------------------------------------------------------------%	 
%---------------------------------------------------------------------%	 

split([],[],[],[]).
split([f(X,Y,Z)|ListF],[X|ListX],[Y|ListY],[Z|ListZ]):-
	split(ListF,ListX,ListY,ListZ).

getvalue(_X,Vals):- var(Vals),!.
getvalue(X,Vals):- member(X,Vals).

unifytoterm([]).
unifytoterm([V|VarsX]):-
	V = term,
	unifytoterm(VarsX).

getargtypes(Type,Args,ValuesX,Rest):-
	get_typedefinition(Type,Def),
        getargtypes_(Def,Args,ValuesX,Rest).

getargtypes_([],_,Rest,Rest).
getargtypes_([Type|Def],Args,ValuesX,Rest):-
	compound_pure_type_term(Type, Term, _Name, Arity),
	!,
	getargtypes1(Args,Arity,Term,ValuesX,Rest1),
        getargtypes_(Def,Args,Rest1,Rest).

getargtypes1([],_Arity,_Term,Rest,Rest).
getargtypes1([Arg|Args],Arity,Term,[Val|ValuesX],Rest1):-
	Arg =< Arity,
        Arg > 0,
	!,
	arg(Arg,Term,Val),
	getargtypes1(Args,Arity,Term,ValuesX,Rest1).
getargtypes1([_|Args],Arity,Term,ValuesX,Rest1):-
	getargtypes1(Args,Arity,Term,ValuesX,Rest1).
	
	
set_union([T],T).
set_union([T1,T2|L],T):-
    type_union(T1,T2,T3),
    set_union([T3|L],T).



getfunctors(Type,ValuesX):-
	get_typedefinition(Type,Def),
        getfunctors_(Def,ValuesX).

getfunctors_([],[]).
getfunctors_([Type|Def],[Val|ValuesX]):-
	compound_pure_type_term(Type, _Term, Name, Arity),
	!,
	functor(Val,Name,Arity),
        getfunctors_(Def,ValuesX).

replacetype(Z,[X:(N,_T)|Entry],TZ,[X:(N,TZ)|Entry]):-
	Z == X,!.
replacetype(Z,[X:(N,T)|Entry],TZ,[X:(N,T)|Prime]):-
	replacetype(Z,Entry,TZ,Prime).
	
evalterms_call_to_success_builtin('arg/3',Sg,Sv,Call,Proj,Succ):-
	sort([X,Y,Z],Hv),
	Head = arg(X,Y,Z),
	eterms_call_to_entry(Sv,Sg,Hv,Head,not_provided,[],Proj,Entry,ExtraInfo), % TODO: add some ClauseKey? (JF)
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
	    concrete(TypeX,ValuesX,[],[]) -> 
	    (
		getargtypes(TypeY,ValuesX,ValuesY,[]) ->
		resetunion,
		set_union(ValuesY,TZ),
%		make_deterministic(ValuesY,Defnew,[]),
%		new_type_symbol(TZ),
%		insert_rule(TZ,Defnew),
		replacetype(Z,Entry,TZ,Prime0),
		eterms_glb(Prime0,Prime1,Prime2)
	    ;
		Prime2 = Prime1
	    )
	; 
	    Prime2 = Prime1
	),
	eterms_glb(Prime2,Entry,Prime3),
	eterms_exit_to_prime(Sg,Hv,Head,Sv,Prime3,ExtraInfo,Prime),
	eterms_extend(Prime,Sv,Call,Succ).

evalterms_call_to_success_builtin('functor/3',Sg,Sv,Call,Proj,Succ):-
	sort([X,Y,Z],Hv),
	Head = functor(X,Y,Z),
	eterms_call_to_entry(Sv,Sg,Hv,Head,not_provided,[],Proj,Entry,ExtraInfo), % TODO: add some ClauseKey?
	get_type(X,Entry,TypeX),
	get_type(Y,Entry,TypeY),
	get_type(Z,Entry,TypeZ),
	( getfunctors(TypeX,ValuesX) -> true ; true),
	( concrete(TypeY,ValuesY,[],[]) -> true ; true),
	( concrete(TypeZ,ValuesZ,[],[]) -> true ; true),
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

	    
evalterms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
	eterms_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?

evalterms_call_to_success_builtin('is/2',(X is Y),Sv,Call,Proj,Succ):-
	(
 	    precondition_builtin('is/2',(X is Y)) ->
	    TY = 'arithmetic:arithexpression',
	    new_type_name(NY),
	    insert_type_name(NY,[],0),
	    varset(Y,Svy),
	    eterms_project(not_provided_Sg,Svy,not_provided_HvFv_u,Proj,Projy),
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
		eterms_project(not_provided_Sg,Svx,not_provided_HvFv_u,Proj,Projx),
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
	    


evalterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
	(
	    precondition_builtin(Key,Sg) ->
	    postcondition_builtin(Key,Bg,Bv,Exit),
	    eterms_exit_to_prime(Sg,Bv,Bg,Sv,Exit,(no,Proj),Prime1),
	    eterms_glb(Proj,Prime1,Prime),
	    eterms_extend(Prime,Sv,Call,Succ)
	;
	    Succ = '$bottom'
	).




%------------------------------------------------------------------%

get_list_names_is([],[]).
get_list_names_is([_:(Name,_)|Proj],[(['$is'],Name)|List]):-
	get_list_names_is(Proj,List).


%--------------------------------------------

% myfunctor(X,Z,Y):- functor(X,Y,Z).

% abs_eval_functor(X,Y,Z,Proj,NProj):-	
% 	get_type(X,Proj,TypeX),
% 	get_typedefinition(TypeX,DefX),
% 	maplist(functor(_Y),DefX,DefZ),
% 	maplist(myfunctor(_Z),DefX,DefY),
% 	new_type_symbol(TY),
% 	new_type_symbol(TZ),
% 	sort(DefZ,DefZ_s),
% 	sort(DefY,DefY_s),
% 	insert_rule(TY,DefY_s),
% 	insert_rule(TZ,DefZ_s).
	


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



getvalues_([],_,[],_):- !.
getvalues_([V|Vars],Proj,[Val|Vals],Concr):- 
	getvalues(V,Proj,Val,Concr),
	getvalues_(Vars,Proj,Vals,Concr).

getvalues(X,Proj,X/Vals,Concr):-
	member(Y:(_,Type),Proj),
	X == Y,
	(
%	    member(Type,[int,flt,num,arithexpression]) ->
	    concrete(Type,Values,[],[]) -> 
%	    get_type_definition(Type,Vals)
	    Vals = Values
	;
    	    Concr = no,
	    choose_one(Type,Vals)
	).



choose_one('basic_props:int',[3]).
choose_one('basic_props:flt',[3.0]).
choose_one('basic_props:num',[3.0,3]).
choose_one('arithmetic:arithexpression',[3.0,3]).
choose_one(int,[3]).
choose_one(flt,[3.0]).
choose_one(num,[3.0,3]).
choose_one(arithexpression,[3.0,3]).
choose_one(_,[3.0,3]).


calc(X,Z,Vals):-
	maplist(apply,Vals),
	Z is X.

apply(X/Y):- member(X,Y).


%--------------------------------------------

get_less_numeric_type(T,int):-
	    dz_type_included(T,int).
get_less_numeric_type(T,flt):-
	    dz_type_included(T,flt).
get_less_numeric_type(_T,num).
