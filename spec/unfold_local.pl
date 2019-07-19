:- module(_,[select_atom/9],[]).

:- use_package(assertions).
:- use_package(spec(no_debug)).

:- doc(title,"Implementation of Different Computation Rules").

:- doc(author, "Elvira Albert").
:- doc(author, "Germ@'{a}n Puebla").

:- doc(module," This file contains the implementation of local
unfolding with ancestor stacks including the efficient treatment of
builtins").

:- use_module(spec(homeo_emb), [homeomorphic_embedded/2]).

:- use_module(spec(unfold_builtins), 
	[can_be_evaluated/1,
	 pure/3,
	 bind_ins/3,
	 no_side_effects/1]).

:- use_module(spec(unfold_df_operations), 
	[can_continue/3,
	 decide_arith_simp/2]).

:- use_module(ciaopp(p_unit), [type_of_goal/2]).

:- use_module(library(lists), [member/2, reverse/2, append/3]).

:- doc(select_atom(+Strategy,+Sg,+Info,-Susp,+Body,-NewBody,+AS,-Emb,+Lit),
  "@var{Strategy} can be @tt{leftmost}, either leftmost or any
  external predicate which is evaluable @tt{eval_builtin}, local
  unfolding with builtins taking into account the embedding ordering
  (i.e., @tt{local_emb}), or @tt{jump_builtin}. The last strategy
  @tt{jump_builtin}, does not perform reordering of goals and can only
  be non-leftmost if all atoms to the left are builtins. @var{Body}
  corresponds to a given goal (i.e., a list of atoms) with three
  different kind of atoms: the mark @tt{top}, a builtin predicate or a
  user-defined predicate. @var{Info} is the abstract substitution at
  that program point and which we have to adapt to @var{Sg}.").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%     LEFTMOST COMPUTATION RULE    %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

select_atom(leftmost,_Sg,_Info,[],Body,Body,_AS,_Done,1).

select_atom(eval_builtin,_Sg,_Info,Susp,Body,NewBody,_AS,_Done,Lit):-
	select_builtin(Body,[],NewBody,Susp,1,Lit).

select_atom(local_emb,_Sg,_Info,Susp,Body,NewBody,AS,Emb,Lit):-
	select_builtin_emb(Body,[],NewBody,Susp,AS,Emb,_Pop,1,Lit).

select_atom(jump_builtin,_Sg,_Info,Susp,Body,NewBody,AS,Emb,Lit):-
	jump_over_builtin(Body,NewBody,[],Susp,AS,Emb,_Pop,1,Lit).

select_atom(safe_jb,Sg,Info,Susp,Body,NewBody,AS,Emb,Lit):-
	safe_jump_builtin(Body,Sg,Info,NewBody,[],Susp,AS,Emb,_Pop,1,Lit).

select_atom(bind_ins_jb,Sg,Info,Susp,Body,NewBody,AS,Emb,Lit):-
	bind_ins_jump_builtin(Body,Sg,Info,NewBody,[],Susp,AS,Emb,_Pop,1,Lit).

select_atom(no_sideff_jb,Sg,Info,Susp,Body,NewBody,AS,Emb,Lit):-
	no_side_effects_jump_builtin(Body,Sg,Info,NewBody,[],Susp,AS,Emb,_Pop,1,Lit).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    SELECTION OF EVALUABLE BUILTINS  %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


select_builtin([],Visited,Res,[],_,1):-
	reverse(Visited,Res).
 
select_builtin([L|R],Visited,Res,Susp,Sel,Lit):-
        ( can_be_evaluated(L) -> 
             reverse(Visited,Susp),
	     Res = [L|R],
	     Lit = Sel
	   ;
	     New_Sel is Sel + 1,
	     decide_arith_simp(L,L1),
	     select_builtin(R,[L1|Visited],Res,Susp,New_Sel,Lit)
        ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    SELECTION OF EVALUABLE BUILTINS OR NON EMBEDDED TERMS    %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- doc(select_builtin_emb(Body,Visited,NewBody,Susp,AS,Emb,Pop),"Predicate
  @pred{select_builtin_emb/6} traverses the @var{Body} looking for an
  atom to the left of the mark @tt{top} which can be evaluated, i.e.,
  it is a builtin which can be evaluated or it a user defined
  predicate which does not subsume any ancestor atom.  If there exists
  such an evaluable atom, then it is placed to the leftmost
  position. Otherwise, the same @var{Body} will be returned in
  @var{NewBody}. Finally, @var{Emb} is used to indicate whether the
  embedding ordering does not have to be checked later during
  unfolding. @var{AS} is the ancestor stack which contains the set of
  atoms that should be used to check the embedding
  subsumption. @var{Pop} is a logical variable which indicates that
  the topmost atom can be popped off the stack because all atoms to
  the left of the selected atom are builtins (if @var{Pop} is bound to
  @tt{false} this cannot be done)").


select_builtin_emb([],Visited,Res,[],_AS,true,_,_,1):-
	reverse(Visited,Res).

select_builtin_emb(['$pop$'|R],Visited,Res,Susp,_AS,Emb,Pop,Sel,Lit):-!,
 	reverse(Visited,Head),
	Emb = true,
	Lit = Sel,
	Susp = [],
 	(Pop==false ->
	 append(Head,['$pop$'|R],Res)
	;
 	    append(['$pop$'|Head],R,Res)
	).
%% 	New_Sel is Sel + 1, 
%% 	select_builtin_emb(R,['$pop$'|Visited],Res,Susp,AS,true,Pop,New_Sel,Lit).

select_builtin_emb([L|R],Visited,Res,Susp,AS,Emb,Pop,Sel,Lit):-
	type_of_goal(imported,L),!,
        ( can_be_evaluated(L) -> 
             reverse(Visited,Susp),
	     Res = [L|R],
	     Emb=false,
	     Lit = Sel
	   ;
	     New_Sel is Sel + 1, 
	     decide_arith_simp(L,L1),
             select_builtin_emb(R,[L1|Visited],Res,Susp,AS,Emb,Pop,New_Sel,Lit)
        ).

select_builtin_emb([L|R],Visited,Res,Susp,AS,Emb,_Pop,Sel,Lit):-
        functor(L,F,Arity),
	functor(Atom,F,Arity),
 	( member(Atom,AS),
          homeomorphic_embedded(Atom,L) -> 
	     New_Sel is Sel + 1, 
	     select_builtin_emb(R,[L|Visited],Res,Susp,AS,Emb,false,New_Sel,Lit)
         ;
	    (can_continue(L,_,_) ->
                reverse(Visited,Susp),
	        Res = [L|R],
	        Emb=false,
	        Lit = Sel
	    ;
		New_Sel is Sel + 1, 
		select_builtin_emb(R,[L|Visited],Res,Susp,AS,Emb,false,New_Sel,Lit)
	    )
        ).
  


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    JUMPING ONLY OVER NON-EVALUABLE BUILTINS (NO EMBEDDING)  %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- doc(jump_over_builtin(Body,NewBody,Susp,RevSusp,AS,Emb,_Pop),"Predicate
  @pred{jump_over_builtin/7} tries to select the leftmost atom in
  @var{Body}, but if it is a builtin which is not evaluable, it jumps
  over it. Suspended builtins are moved out of @var{Body} and
  introduced in the list @var{Susp}. The resulting body without
  suspended builtins is returned in @var{NewBody}. @var{RevSusp} is
  the list of suspended atoms in the same order they appear in
  @var{Body}. Finally, @var{AS,Emb,Pop} are used as in
  @pred{select_builtin_emb})").


jump_over_builtin([],[],Susp,RevSusp,_AS,true,_,Lit,Lit):-
	reverse(Susp,RevSusp).
jump_over_builtin(['$pop$'|R],['$pop$'|R],Susp,RevSusp,_AS,true,_Pop,Lit,Lit):-!,
	reverse(Susp,RevSusp).
jump_over_builtin([L|R],NewBody,Susp,RevSusp,AS,Emb,Pop,Sel,Lit):-
	type_of_goal(imported,L),!,
        ( can_be_evaluated(L) -> 
	     reverse(Susp,RevSusp),
	     Emb=false,
	     NewBody=[L|R],
	     Lit = Sel
	   ;
	     New_Sel is Sel + 1, 
	     decide_arith_simp(L,L1),
             jump_over_builtin(R,NewBody,[L1|Susp],RevSusp,AS,Emb,Pop,New_Sel,Lit)
        ).
jump_over_builtin([L|R],[L|R],Susp,RevSusp,_AS,_Emb,_Pop,Lit,Lit):-
	reverse(Susp,RevSusp).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    JUMPING ONLY OVER NON-EVALUABLE BUILTINS (NO EMBEDDING)  %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- doc(safe_jump_builtin(Body,Sg,Info,NewBody,Susp,RevSusp,AS,Emb,_Pop),"Predicate
  @pred{safe_jump_builtin/8} tries to select the leftmost atom in
  @var{Body}, but if it is a builtin which is not evaluable, it jumps
  over it. Suspended builtins are moved out of @var{Body} and
  introduced in the list @var{Susp}. The resulting body without
  suspended builtins is returned in @var{NewBody}. @var{RevSusp} is
  the list of suspended atoms in the same order they appear in
  @var{Body}. @var{Info} is the abstract substitution at that program
  point and which needs to be adapted to @var{Sg}. Finally,
  @var{AS,Emb,Pop} are used as in @pred{select_builtin_emb})").


safe_jump_builtin([],_Sg,_Info,[],Susp,RevSusp,_AS,true,_,Lit,Lit):-
	reverse(Susp,RevSusp).

safe_jump_builtin(['$pop$'|R],_Sg,_Info,['$pop$'|R],Susp,RevSusp,_AS,true,_Pop,Lit,Lit):-!,
	reverse(Susp,RevSusp).

safe_jump_builtin([L|R],Sg,Info,NewBody,Susp,RevSusp,AS,Emb,Pop,Sel,Lit):-
	type_of_goal(imported,L),!,
        ( can_be_evaluated(L) -> 
	     reverse(Susp,RevSusp),
	     Emb=false,
	     NewBody=[L|R],
	     Lit = Sel
	   ;
	    decide_arith_simp(L,L1),
	    (pure(L1,Sg,Info) ->
	        New_Sel is Sel + 1,
	        safe_jump_builtin(R,Sg,Info,NewBody,[L1|Susp],RevSusp,AS,Emb,Pop,New_Sel,Lit)
	    ;
		reverse(Susp,RevSusp),
		Emb=false,
		NewBody=[L1|R],
		Lit = Sel
	    )	    
        ).
safe_jump_builtin([L|R],_Sg,_Info,[L|R],Susp,RevSusp,_AS,_Emb,_Pop,Lit,Lit):-
	reverse(Susp,RevSusp).
  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    JUMPING ONLY OVER NON-EVALUABLE BUILTINS (NO EMBEDDING)  %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- doc(bind_ins_jump_builtin(Body,Sg,Info,NewBody,Susp,RevSusp,AS,Emb,_Pop),"Predicate
  @pred{bind_ins_jump_builtin/8} tries to select the leftmost atom in
  @var{Body}, but if it is a builtin which is not evaluable, it jumps
  over it. Suspended builtins are moved out of @var{Body} and
  introduced in the list @var{Susp}. The resulting body without
  suspended builtins is returned in @var{NewBody}. @var{RevSusp} is
  the list of suspended atoms in the same order they appear in
  @var{Body}. @var{Info} is the abstract substitution at that program
  point and which needs to be adapted to @var{Sg}. Finally,
  @var{AS,Emb,Pop} are used as in @pred{select_builtin_emb})").


bind_ins_jump_builtin([],_Sg,_Info,[],Susp,RevSusp,_AS,true,_,Lit,Lit):-
	reverse(Susp,RevSusp).

bind_ins_jump_builtin(['$pop$'|R],_Sg,_Info,['$pop$'|R],Susp,RevSusp,_AS,true,_Pop,Lit,Lit):-!,
	reverse(Susp,RevSusp).

bind_ins_jump_builtin(['$susp'(L)|R],Sg,Info,NewBody,Susp,RevSusp,AS,Emb,Pop,Sel,Lit):-
	New_Sel is Sel + 1,	
	bind_ins_jump_builtin(R,Sg,Info,NewBody,[L|Susp],RevSusp,AS,Emb,Pop,New_Sel,Lit).

bind_ins_jump_builtin([L|R],Sg,Info,NewBody,Susp,RevSusp,AS,Emb,Pop,Sel,Lit):-
	type_of_goal(imported,L),!,
        ( can_be_evaluated(L) -> 
	     reverse(Susp,RevSusp),
	     Emb=false,
	     NewBody=[L|R],
	     Lit = Sel
	   ;
	    decide_arith_simp(L,L1),
	    (bind_ins(L1,Sg,Info) ->
	        debug('IS bindind insensitive'),
		debug(L1),
	        New_Sel is Sel + 1,
	        bind_ins_jump_builtin(R,Sg,Info,NewBody,[L1|Susp],RevSusp,AS,Emb,Pop,New_Sel,Lit)
	    ;
	        debug('NOT binding insensitive'),
		debug(L1),
		reverse(Susp,RevSusp),
		Emb=false,
		NewBody=[L1|R],
		Lit = Sel
	    )	    
        ).
bind_ins_jump_builtin([L|R],_Sg,_Info,[L|R],Susp,RevSusp,_AS,_Emb,_Pop,Lit,Lit):-
	reverse(Susp,RevSusp).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    JUMPING ONLY OVER NON-EVALUABLE BUILTINS (NO EMBEDDING)  %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- doc(no_side_effects_jump_builtin(Body,Sg,Info,NewBody,Susp,RevSusp,AS,Emb,_Pop),"Predicate
  @pred{no_side_effects_jump_builtin/8} tries to select the leftmost
  atom in @var{Body}, but if it is a builtin which is not evaluable,
  it jumps over it. Suspended builtins are moved out of @var{Body} and
  introduced in the list @var{Susp}. The resulting body without
  suspended builtins is returned in @var{NewBody}. @var{RevSusp} is
  the list of suspended atoms in the same order they appear in
  @var{Body}. @var{Info} is the abstract substitution at that program
  point and which needs to be adapted to @var{Sg}. Finally,
  @var{AS,Emb,Pop} are used as in @pred{select_builtin_emb}). This
  rule differs from bind_ins_jump_builtin in that it allows jumping
  builtins as long as they have no side effects.").


no_side_effects_jump_builtin([],_Sg,_Info,[],Susp,RevSusp,_AS,true,_,Lit,Lit):-
	reverse(Susp,RevSusp).

no_side_effects_jump_builtin(['$pop$'|R],_Sg,_Info,['$pop$'|R],Susp,RevSusp,_AS,true,_Pop,Lit,Lit):-!,
	reverse(Susp,RevSusp).

no_side_effects_jump_builtin([L|R],Sg,Info,NewBody,Susp,RevSusp,AS,Emb,Pop,Sel,Lit):-
	type_of_goal(imported,L),!,
        ( can_be_evaluated(L) -> 
	     reverse(Susp,RevSusp),
	     Emb=false,
	     NewBody=[L|R],
	     Lit = Sel
	   ;
	    decide_arith_simp(L,L1),
	    (no_side_effects(L1) ->
	        debug('NO side effect'),
		debug(L1),
	        New_Sel is Sel + 1,
	        no_side_effects_jump_builtin(R,Sg,Info,NewBody,[L1|Susp],RevSusp,AS,Emb,Pop,New_Sel,Lit)
	    ;
	        debug('HAS side effect'),
		debug(L1),
		reverse(Susp,RevSusp),
		Emb=false,
		NewBody=[L1|R],
		Lit = Sel
	    )	    
        ).
no_side_effects_jump_builtin([L|R],_Sg,_Info,[L|R],Susp,RevSusp,_AS,_Emb,_Pop,Lit,Lit):-
	reverse(Susp,RevSusp).
