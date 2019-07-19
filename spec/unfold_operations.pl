:- module(unfold_operations, 
	[decide_orig_goal/2,
	 body2list/2,
	 list2body/2,
	 replicate_atoms/4,
	 filter_pops/2,
	 is_embedded/3,
	 is_embedded/4,
	 is_embedded_tree/4
	 ],
	 []).

:- use_package(assertions).

:- doc(author, "Germ@'{a}n Puebla").
:- doc(author, "Elvira Albert").

:- doc(module," This module contains auxiliary predicates for
    unfolding").

:- use_package(.(no_debug)).

:- use_module(library(lists), [member/2]).

:- use_module(spec(homeo_emb), 
	[homeomorphic_embedded/2,
	 homeomorphic_embedded_num/2,
	 homeomorphic_embedded_type/2]).

:- use_module(spec(arith_simplify), [arith_simp/2]).
:- use_module(spec(generalize_emb_atoms), [decide_lc_filter/2, add_gen_emb_hint/2, 
	                                  get_petype_mask/2]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(library(term_filtering/fr_notation), [fr_to_term/3]).
:- use_module(engine(hiord_rt), ['$meta_call'/1]).

:- use_module(ciaopp(p_unit/prednames)).
:- reexport(ciaopp(p_unit/prednames), [orig_pred_name/2, orig_goal/2]).

:- pred decide_orig_goal(+Goal,-Orig_Goal) # "If we are not performing
     local control, then @var{Orig_Goal} is identical to
     @var{Goal}. Otherwise we compute @var{Orig_Goal} using
     @pred{orig_goal/2}.".

decide_orig_goal(Goal,Orig_Goal):-
	current_pp_flag(local_control,off),!,
	Orig_Goal = Goal.
decide_orig_goal(Goal,Orig_Goal):-
	orig_goal(Goal,Orig_Goal).

:- pred body2list(+Body,-List) # "Transforms the body of clause
      (conjunction) into a list.".

body2list(Body,[First|More]):-
	nonvar(Body),
	Body = (First,Rest),
        !,
        body2list(Rest,More).
body2list(Body,LBody):-
	nonvar(Body),
	Body = true,!,
	LBody = [].
body2list(Last,[Last]).


:- pred list2body(+List,-Body) # "Transforms a list into the body of
      clause (conjunction).".

list2body([],true).
list2body([Last],Last):-!.
list2body([First|Rest],(First,More)):-
        list2body(Rest,More).


:- pred replicate_atoms(+Clauses,+Atom,+TmpAtoms,-RepAtoms) # "The
	list @var{RepAtoms} on output contains as many replicates of
	@var{Atoms} as elements there are in the list @var{Clauses}".

replicate_atoms([],_A1,NA1s,NA1s).
replicate_atoms([_|Cls],A1,NA1s,[A1|NAs]):-
	replicate_atoms(Cls,A1,NA1s,NAs).

filter_pops(Body,NBody):-
	current_pp_flag(sim_ari_exp,SIMP),
	(member(SIMP,[post,both]) ->
	    (iterate_filter_pops_arith(Body,NBody) ->
	        true
	    ;
		NBody = ['basiccontrol:fail']
	    )
	;
	    filter_pops_no_arith(Body,NBody)
	).

:- pred filter_pops_no_arith(+,-) # "Removes the pseudo literals '$pop'
	and '$susp' from residual clauses.".

filter_pops_no_arith([],[]).
filter_pops_no_arith(['$pop$'|Body],NBody):-!,
	filter_pops_no_arith(Body,NBody).
filter_pops_no_arith(['$susp'(L)|Body],[L|NBody]):-!,
	filter_pops_no_arith(Body,NBody).
filter_pops_no_arith([L|Body],[L|NBody]):-!,
	filter_pops_no_arith(Body,NBody).

iterate_filter_pops_arith(Body,NBody):-
	filter_pops_arith(Body,TmpBody,Flag),
	(Flag == yes -> 
	    iterate_filter_pops_arith(TmpBody,NBody)
	;
	    NBody = TmpBody
	).

:- pred filter_pops_arith(+,-,?) # "Removes the pseudo literals '$pop'
	and '$susp' from residual clauses. Also, simplifies and evaluates 
	calls to is/2 and unification.".

filter_pops_arith([],[],_).
filter_pops_arith(['$pop$'|Body],NBody,Flag):-!,
	filter_pops_arith(Body,NBody,Flag).
filter_pops_arith(['$susp'(L)|Body],NBody,Flag):-!,
	filter_pops_arith([L|Body],NBody,Flag).
filter_pops_arith(['myprofiler_rt:is'(Res,Form)|Body],NBody,Flag):-!,
	(ground(Form) ->
	    debug(arith_simp),
	    '$meta_call'('myprofiler_rt:is'(Res,Form)),
	    NBody = MoreBody,
	    Flag = yes
	;
	    (var(Form) ->
	        debug(arith_simp_var),
		'$meta_call'('term_basic:='(Res,Form)),
		NBody = MoreBody
	    ;
		arith_simp(Form,Form1),
		(Form == Form1 ->
		    true
		;
		    Flag = yes
		),
		L = 'myprofiler_rt:is'(Res,Form1),
		NBody = [L|MoreBody]
	    )
	),
	filter_pops_arith(Body,MoreBody,Flag).
filter_pops_arith(['arithmetic:is'(Res,Form)|Body],NBody,Flag):-!,
	(ground(Form) ->
	    '$meta_call'('arithmetic:is'(Res,Form)),
	    NBody = MoreBody,
	    Flag = yes
	;
	    arith_simp(Form,Form1),
	    (Form == Form1 ->
	        true
	    ;
		Flag = yes),
	    L = 'arithmetic:is'(Res,Form1),
	    NBody = [L|MoreBody]
	),
	filter_pops_arith(Body,MoreBody,Flag).
filter_pops_arith(['term_basic:='(Res,Form)|Body],NBody,Flag):-!,
	debug(arith_simp_unif),
	Flag = yes,
	'$meta_call'('term_basic:='(Res,Form)),
	NBody = MoreBody,
	filter_pops_arith(Body,MoreBody,yes).
filter_pops_arith([L|Body],[L|NBody],Flag):-!,
	filter_pops_arith(Body,NBody,Flag).

is_embedded(true,L,A):- 
	decide_lc_filter(L,Lfr),
	(functor(Lfr,',',2) -> % Lfr is a FR notation atom
	   (Lfr = (Lf,_Lr),
	    functor(Lf,F,Arity),
	    functor(Atomf,F,Arity),Atom = (Atomf,_),
	    member(Atom,A),
	    homeomorphic_embedded(Atomf,Lf),
	    get_petype_mask(F,Mask),
	    fr_to_term(Atom,Mask,OrigAtom))
	;                     % Lfr is a normal atom
	   (functor(Lfr,F,Arity),
	    functor(Atom,F,Arity),
	    member(Atom,A),
	    homeomorphic_embedded(Atom,Lfr),
	    OrigAtom = Atom)),
	add_gen_emb_hint(L,OrigAtom).

is_embedded(true,FNums,L,A):- 
	decide_lc_filter(L,Lfr),
	(functor(Lfr,',',2) -> % Lfr is a FR notation atom
	   (Lfr = (Lf,_Lr),
	    functor(Lf,F,Arity),
	    functor(Atomf,F,Arity),Atom = (Atomf,_),
	    member(Atom,A),
	    (FNums == types -> homeomorphic_embedded_type(Atomf,Lf) 
	    ; (FNums == on  -> homeomorphic_embedded_num(Atomf,Lf)
	                     ; homeomorphic_embedded(Atomf,Lf))),
	    get_petype_mask(F,Mask),
	    fr_to_term(Atom,Mask,OrigAtom))
	;                      % Lfr is a normal atom
	   (functor(Lfr,F,Arity),
	    functor(Atom,F,Arity),
	    member(Atom,A),
	    (FNums == types -> homeomorphic_embedded_type(Atom,Lfr)
	    ; (FNums == on  -> homeomorphic_embedded_num(Atom,Lfr)
	                     ; homeomorphic_embedded(Atom,Lfr))),
	    OrigAtom = Atom)),
	add_gen_emb_hint(L,OrigAtom).

is_embedded_tree(true,L,Parent,A):- 
	functor(L,F,Arity),
	ancestor(Parent,A,Ancestor),
	functor(Ancestor,F,Arity),
	homeomorphic_embedded(Ancestor,L).

ancestor(Parent,A,Ancestor):-
	member((Parent,Ancestor,_),A).
ancestor(Parent,A,Ancestor):-
	member((Parent,_Ancestor0,Grand_Parent),A),
	ancestor(Grand_Parent,A,Ancestor).
