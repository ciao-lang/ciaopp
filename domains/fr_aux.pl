%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : Minimal Freeness Domain Fm
% Copyright (C) 1993 Wim Simoens, Veroniek Dumortier
%		and Katholieke Universiteit Leuven.
% Based on the code of the non-Minimal Freeness Domain by G. Janssens
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxiliary predicates for coupling the Fm abstraction with PLAI
% uses set_* predicates from fros.pl
% uses ss_* predicates from fross23.pl
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abstract state <as> ::= as(<ac>o , <ac>n) | "'$bottom'"
% <ac> ::= ordered set of <sets_of_variables>
% <set_of_variables> ::= ordered set of variables 	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VD	2nd approach old-new
%	2 versions for lub
%	space-optimised (o = t \ n)
%	identical test separately on o- and n-components
%	idea of split:
%		extra parameter needed in fr_join, namely (ordered) set of
%		variables occurring in the AlfaC part
%		Split of ss-info in Call w.r.t. AlfaC
%
% added builtins and improved some existing builtins	25/01/95
% replaced fr_nonfree_arg in builtins by fr_ground_arg
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% fr_call_head_unif(Sargs, Hargs, Asub, AsubSH)
% AsubSH = Asub \Aconj (Sargs = Hargs)
%
% :- mode fr_call_head_unif(?,?,?,o).
fr_call_head_unif([], [], Asub, Asub).
fr_call_head_unif([Sarg | SargRest], [Harg | Hargrest], Asub, AsubSH):-
	fr_success_builtin_eq_noteq(Sarg, Harg, Asub, Asub1),
	fr_call_head_unif(SargRest, Hargrest, Asub1, AsubSH).

%--------------------------------------------------------------------------

% fr_restriction(Hv, Asub, Asub_restr) 	(S)
% Asub, Asub_restr: <as>; Hv : sorted list of variable identifiers
% Asub_restr is the restriction of Asub wrt the variables in Hv
%
% :- mode fr_restriction(?,?,o).
fr_restriction(_Hv, Asub, Asub_restr):-                                
	bottomelement(Asub), !, Asub_restr = Asub.
fr_restriction(Hv, as(ACo,ACn), as(ACor,ACnr)) :-
	ss_restriction(ACo, Hv, ACor),
	ss_restriction(ACn, Hv, ACnr).
		% note: Acnr is not empty as required by procedure-entry !

%--------------------------------------------------------------------------

% fr_restriction_entry(Vars, Call, Proj) 	(S)
% REQ: not(bottomelement(Call))
% Call, Proj: <as>; Vars : sorted list of variable identifiers
% Proj is the restriction of Call wrt the variables in Vars
% Used at procedure entry -> the new component of Proj is empty
%
% :- mode fr_restriction_entry(?,?,o).
fr_restriction_entry(Vars, as(ACo,ACn), as(ACop,ACnp)) :-
	ss_restriction(ACo, Vars, ACor),
	ss_restriction(ACn, Vars, ACnr),
	ss_union(ACor, ACnr, ACop_nonmin),
	ss_minimise(ACop_nonmin, ACop),
	ss_empty(ACnp).
		% note: Acnp is empty as required by procedure-entry

%--------------------------------------------------------------------------

% SPECIFIC VERSION OF LUB USED AT PROCEDURE EXIT (computes only n-comp)
% uses approach 2 (wrt determining ACo-ACn)

% fr_lub_uas(UsefulASlist, Lub)
% REQ : UsefulASlist =/= []
%
% :- mode fr_lub_uas(?,o).
fr_lub_uas([as(_ACo, ACn) | UsefulASlist], as(dummy, ACnlub)):-
	% dummy has to be filled in, do not leave uninstantiated var because
	% subsequent fr_identical_abstract test would check identity of =/= vars
	fr_lub_uas2(UsefulASlist, ACn, ACnlub).
                        
% fr_lub_uas2(UsefulASlist, ACn, ACnlub)
% ACnlub = lub({ACn,new_comps_of_UsefulASlist})
%
% :- mode fr_lub_uas2(?,?,o).
fr_lub_uas2([], ACnlub, ACnlub).
fr_lub_uas2([as(_ACo1,ACn1) | UsefulASlist], ACn2, ACnlub):-
	ss_lubm(ACn1, ACn2, ACnlubAcc),
	fr_lub_uas2(UsefulASlist, ACnlubAcc, ACnlub).


% GENERAL VERSION OF LUB TO BE USED FOR ANNOTATION (support3.pl)
% uses approach 2 (wrt determining ACo-ACn)

%% % fr_lub_uas_general(UsefulASlist, Lub)
%% % REQ : UsefulASlist =/= []
%% %
%% % :- mode fr_lub_uas_general(?,o).
%% fr_lub_uas_general([as(ACo, ACn) | UsefulASlist], as(AColub, ACnlub)):-
%% 	fr_lub_uas_general2(UsefulASlist, ACo, ACn, AColub, ACnlub).
%% 
%% % fr_lub_uas_general2(UsefulASlist, ACo, ACn, AColub, ACnlub)
%% % <AColub,ACnlub> = lub of <ACo,ACn> and the <as> in UsefulASlist
%% %
%% % :- mode fr_lub_uas_general2(?,?,?,o,o).
%% fr_lub_uas_general2([], AColub, ACnlub, AColub, ACnlub).
%% fr_lub_uas_general2([as(ACo1,ACn1) | UsefulASlist], ACo2, ACn2,
%% 					AColub, ACnlub):-
%% 	ss_lubm(ACn1, ACn2, ACnlubAcc),
%% 	ss_union_list([ACo1, ACn1, ACo2, ACn2], ACt12),
%% 	ss_minimise(ACt12, ACtlubAcc),
%% 	ss_diff(ACtlubAcc, ACnlubAcc, AColubAcc),
%% 	fr_lub_uas_general2(UsefulASlist, AColubAcc, ACnlubAcc, AColub, ACnlub).

%--------------------------------------------------------------------------

% fr_success_builtin_eq_noteq(L,R,Call,Succ)
% Abstract interpretation of L (=|#) R
% note: recursive calls may have bottomelement(Call) !
%
% :- mode fr_success_builtin_eq_noteq(?,?,?,o).
fr_success_builtin_eq_noteq(_L,_R,Call,Succ):-
	bottomelement(Call), !, Succ = Call.
fr_success_builtin_eq_noteq(L,R,Call,Succ):-
        get_type(L, TypeL),
        get_type(R, TypeR),
        ( TypeL == var ->
        	( TypeR == var ->
                      ( L == R -> Succ = Call ; fr_abstract_simple([L,R], Call, Succ))
                ;
                      fr_prim_eq_noteq_split(TypeR, L, R, Call, Succ)
                )
        ;
                ( TypeR == var ->
                      fr_prim_eq_noteq_split(TypeL, R, L, Call, Succ)
                ;
                      ( TypeL == TypeR ->
                              fr_full_eq_noteq_split(TypeL, L, R, Call, Succ)
                      ;
                              bottomelement(Succ)
                      )
                )
        ).
 
fr_prim_eq_noteq_split(herb, L, R, Call, Succ):-
        fr_abstract_prim_herbcs(L, R, Call, Succ).
fr_prim_eq_noteq_split(num, L, R, Call, Succ):-
        fr_abstract_prim_numcs('=', L, R, Call, Succ).
fr_prim_eq_noteq_split(piii, L, piii(R), Call, Succ):-
        fr_abstract_prim_piiics(L, R, Call, Succ).

fr_full_eq_noteq_split(herb, L, R, Call, Succ):-
        fr_abstract_full_herbcs(L, R, Call, Succ).
fr_full_eq_noteq_split(num, L, R, Call, Succ):-
        fr_abstract_full_numcs('=', L, R, Call, Succ).
fr_full_eq_noteq_split(piii, piii(L), piii(R), Call, Succ):-
        fr_abstract_full_piiics(L, R, Call, Succ).

%--------------------------------------------------------------------------

% fr_abstract_prim_herbcs(Var, Term, Call, Succ)
% Abstract interpretation of Var (=|#) Term (Term is a nonvar Herbrand term)
% REQ: not bottomelement(Call)
%
fr_abstract_prim_herbcs(Var, Term, Call, Succ):-
        get_var_groups(Term, TermVars, VarGroups),
        ss_make_AlfaFunctor_groups(VarGroups, Var, AlfaC),
        set_add_el(Var, TermVars, VarsAlfaC),
        fr_join(Call, AlfaC, VarsAlfaC, Succ).
        
%--------------------------------------------------------------------------

% fr_abstract_full_herbcs(Term1, Term2, Call, Succ)
% Abstract interpretation of Term1 (=|#) Term2
% (both Term1 and Term2 are nonvar Herbrand terms)
% REQ: not bottomelement(Call)
%
fr_abstract_full_herbcs(Term1, Term2, Call, Succ):-
        functor(Term1, F1, A1),
        functor(Term2, F2, A2),
        ( F1 == F2, A1 == A2 ->		% also works for A1=A2=0
                Term1 =.. [_|Args1], Term2 =.. [_|Args2],
                fr_abstract_herbcs_args(Args1, Args2, Call, Succ)
        ;
                bottomelement(Succ)
        ).

% fr_abstract_herbcs_args(Args1, Args2, Call, Succ)
% Abstract interpretation of Args1 = Args2 by recursively equating the
% corresponding arguments
% note : bottomelement(Call) is possible now !
%
fr_abstract_herbcs_args([], [], Succ, Succ).
fr_abstract_herbcs_args([Arg1 | Rest1], [Arg2 | Rest2], Call, Succ):-
	fr_success_builtin_eq_noteq(Arg1, Arg2, Call, Lambda_mid),
	% one could already test for bottomelement(Lambda_mid) here
	fr_abstract_herbcs_args(Rest1, Rest2, Lambda_mid, Succ).

%--------------------------------------------------------------------------

% fr_abstract_prim_numcs(Comp, Var, Term, Call, Succ)
% Abstract interpretation of the numerical constraint  "Var Comp Term"
% (Term is a nonvar numerical term)
% REQ: not(bottomelement(Call))
%
% :- mode fr_abstract_prim_numcs(?,?,?,?,o).
fr_abstract_prim_numcs(_Comp, Var, Term, Call, Succ):-
        ( linear(Term) ->
		get_vars_repvars([Var,Term], Vars, Doubles),
		ss_oplusm([Vars], [Doubles], SS),
		ss_add_el(Vars, SS, SS2),
		ss_minimise(SS2, AlfaC)
        ;
        	get_vars([Var,Term], Vars),
                ss_make_singl(Vars, AlfaC)
        ),
        fr_join(Call, AlfaC, Vars, Succ).

%--------------------------------------------------------------------------

% fr_abstract_full_numcs(Comp, Term1, Term2, Call, Succ)
% Abstract interpretation of the numerical constraint  "Term1 Comp Term2"
% (both Term1 and Term2 are nonvar numerical terms)
% REQ: not bottomelement(Call)
%
fr_abstract_full_numcs(Comp, Term1, Term2, Call, Succ):-
	( number(Term1), number(Term2) ->
		( compare(Comp,Term1,Term2) ->
			Succ = Call
		;
			bottomelement(Succ)
		)
	;
          	( linear(Term1), linear(Term2) ->
			get_vars_repvars([Term1,Term2], Vars, Doubles),
			( Vars \== [] ->
				ss_oplusm([Vars], [Doubles], SS),
				ss_add_el(Vars, SS, SS2),
				ss_minimise(SS2, AlfaC),
				fr_join(Call, AlfaC, Vars, Succ)
			;
				Succ = Call
			)
        	;
			get_vars([Term1,Term2], Vars),
			( Vars \== [] ->
                		ss_make_singl(Vars, AlfaC),
				fr_join(Call, AlfaC, Vars, Succ)
			;
				Succ = Call
			)
          	)
	).

%--------------------------------------------------------------------------

% fr_success_builtin_compare(Comp,L,R,Call,Succ)
% REQ: not(bottomelement(Call))
% Abstract interpretation of "L Comp R" with Comp::= (> | >= | < | <= )
%
% :- mode fr_success_builtin_compare(?,?,?,?,o).
fr_success_builtin_compare(Comp,L,R,Call,Succ) :-
	numerical(L), numerical(R) ->
		fr_abstract_full_numcs(Comp,L,R,Call,Succ)
	;
		bottomelement(Succ)
	.

%--------------------------------------------------------------------------

% fr_abstract_prim_piiics(Var, Term, Call, Succ)
% abstract interpretation of Var (=|#) Term where Term is a list of
% concatenated piii-tuple parts
%	e.g. Term = [X, [f(Y),Z+U], T] -> X.<f(Y),Z+U)>.T
%
fr_abstract_prim_piiics(Var, Term, Call, Succ):-
	get_var_groups(Term, TermVars, VarGroups),
        ss_addpairs_groups(VarGroups, Var, [], SS),
	( piii_restricted_length(Term) ->
		ss_add_el([Var], SS, AlfaC) ; AlfaC = SS ),
        set_add_el(Var, TermVars, VarsAlfaC),
        fr_join(Call, AlfaC, VarsAlfaC, Succ).

%--------------------------------------------------------------------------

% fr_abstract_full_piiics(Term1, Term2, Call, Succ)
% abstract interpretation of Term1 (=|#) Term2 where
% Term1 and Term2 are lists of concatenated piii-tuple parts
%
fr_abstract_full_piiics([], [], Call, Call):- !.
fr_abstract_full_piiics([], Term2, Call, Succ):-
	!,
	fr_piii_empty(Term2, Call, Succ).
fr_abstract_full_piiics(Term1, [], Call, Succ):-
	!,
	fr_piii_empty(Term1, Call, Succ).
fr_abstract_full_piiics([X], Term2, Call, Succ):-
	var(X), !, fr_abstract_prim_piiics(X, Term2, Call, Succ).
fr_abstract_full_piiics(Term1, [X], Call, Succ):-
	var(X), !, fr_abstract_prim_piiics(X, Term1, Call, Succ).
fr_abstract_full_piiics([X|Rest1], [Y|Rest2], Call, Succ):-
        (var(X) ; var(Y)), !,
        get_vars([X|Rest1], Vars1),
        get_vars([Y|Rest2], Vars2),
        set_union(Vars1, Vars2, VarsAlfaC),
	( ( piii_restricted_length([X|Rest1]) ;
	    piii_restricted_length([Y|Rest2]) ) ->
		ss_make_singl(VarsAlfaC, AlfaC)
	;
		ss_make_pairs(Vars1, Vars2, AlfaC)
	),
        fr_join(Call, AlfaC, VarsAlfaC, Succ).
fr_abstract_full_piiics([X|Rest1], [Y|Rest2], Call, Succ):-
	!,
        fr_peel_piiics(X, Y, Rest1, Rest2, NR1, NR2, Call, NCall),
	( bottomelement(NCall) ->
		Succ = NCall
	;
	        fr_abstract_full_piiics(NR1, NR2, NCall, Succ)
	).
fr_abstract_full_piiics(_Term1, _Term2, _Call, Succ):-
	% Term1 and/or Term2 not a list
	compiler_error(piii_lists),
	bottomelement(Succ).

fr_peel_piiics([], [], R1, R2, R1, R2, Call, Call):- !.
fr_peel_piiics([], Term, R1, R2, R1, [Term|R2], Call, Call):- !.
fr_peel_piiics(Term, [], R1, R2, [Term|R1], R2, Call, Call):- !.
fr_peel_piiics([X|Rest1], [Y|Rest2], R1, R2, NR1, NR2, Call, Succ):-
        fr_success_builtin_eq_noteq(X, Y, Call, NCall),
	( bottomelement(NCall) ->
		Succ = NCall
	;
		fr_peel_piiics(Rest1, Rest2, R1, R2, NR1, NR2, NCall, Succ)
	).


fr_piii_empty([], Call, Call).
fr_piii_empty([ V | Rest], Call, Succ):-
	var(V), !,
	fr_join(Call, [[V]], [V], NCall),
	fr_piii_empty(Rest, NCall, Succ).
fr_piii_empty([ [] | Rest ], Call, Succ):-
	!, fr_piii_empty(Rest, Call, Succ).
fr_piii_empty(_T, _Call, Succ):-
	bottomelement(Succ).

%--------------------------------------------------------------------------

% fr_success_builtin_ground(Pred, Args, Sv_uns, Call, Succ)
% REQ: not(bottomelement(Call))
% note : the default is given by the last clause
%	 the other clauses may detect '$bottom' based on conditions on the
%	 call pattern or type of the arguments of the builtin;
%	 this leads to more precise output, but is also more time-consuming !
%	 (one could use the default in all cases if time performance is
%	  important)
%
% :- mode fr_success_builtin_ground(?,?,?,?,o).
fr_success_builtin_ground(assign,Args,_Sv_uns,Call,Succ):-
	!, Args = [I, T],
	( fr_ground_arg(I, Call),
	  fr_ground_arg(T, Call) ->
		%%% VD  25/01/95
		% fr_abs_int_ground(Call, Sv_uns, Succ) not needed since
		% the args are already checked to be ground (non-free)
		Succ = Call
		% adjust when pos fail is represented : then Succ = Call U [[]]
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(cpu_time,Args,Sv_uns,Call,Succ):-
	!, Args = [A],
	( numerical(A) ->
		fr_abs_int_ground(Call, Sv_uns, Succ)
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(enum,Args,Sv_uns,Call,Succ):-
	!, Args = [A],
	( numerical(A) ->
		fr_abs_int_ground(Call, Sv_uns, Succ)
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(erase,Args,_Sv_uns,Call,Succ):-
	!, Args = [A],
	( fr_ground_arg(A, Call) ->
		%%% VD 25/01/95
		% fr_abs_int_ground(Call, Sv_uns, Succ) not needed since
                % the arg is already checked to be ground (non-free)
                Succ = Call
                % adjust when pos fail is represented : then Succ = Call U [[]]
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(min_value,Args,_Sv_uns,Call,Succ):-
	%%% VD 25/01/95 min_value/2 is now minimum/2 in PrologIII v1.4
	!, Args = [A1, A2],
	( numerical(A1), numerical(A2) ->
		get_vars(A2, Vars),
		fr_abs_int_ground(Call, Vars, Succ)
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(outm,Args,_Sv_uns,Call,Succ):-
	!, Args = [A],
	( fr_ground_arg(A, Call) ->
                %%% VD 25/01/95
		% fr_abs_int_ground(Call, Sv_uns, Succ) not needed since
                % the arg is already checked to be ground (non-free)
		Succ = Call
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(outml,Args,_Sv_uns,Call,Succ):-
	!, Args = [A],
	( fr_ground_arg(A, Call) ->
                %%% VD 25/01/95
		% fr_abs_int_ground(Call, Sv_uns, Succ) not needed since
                % the arg is already checked to be ground (non-free)
		Succ = Call
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(recorda,Args,_Sv_uns,Call,Succ):-
	!, Args = [Key, _Term, Ref],
	( fr_ground_arg(Key, Call) ->
                %%% VD 25/01/95
		% get_vars([Key,Ref], Vars),  Key already checked to be
		% ground (non-free), so do not add it again
		% adjust when pos fail : [] should be in Succ since the key
		% may not exist
		get_vars(Ref, Vars),
		fr_abs_int_ground(Call, Vars, Succ)
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(val,Args,_Sv_uns,Call,Succ):-
	!, Args = [A1, A2],
	( fr_ground_arg(A1, Call) ->
                %%% VD 25/01/95
		% fr_abs_int_ground(Call, Sv_uns, Succ)
		% not needed to add A1-vars again since
                % the arg is already checked to be ground (non-free)
		% adjust when pos fail is represented : [] should be in Succ
		get_vars(A2, Vars),
		fr_abs_int_ground(Call, Vars, Succ)
	;
		bottomelement(Succ)
	).
%%% VD added 25/01/95
fr_success_builtin_ground(sys_command,Args,_Sv_uns,Call,Succ):-
	!, Args = [A],
	( fr_ground_arg(A, Call) ->
		Succ = Call
		% adjust when pos fail is represented : [] should be in Succ
        ;
                bottomelement(Succ)
        ).
fr_success_builtin_ground((=\=),Args,_Sv_uns,Call,Succ):-
	!, Args = [A1,A2],
	( fr_ground_arg(A1, Call),
	  fr_ground_arg(A2, Call) ->
		Succ = Call
                % adjust when pos fail is represented : [] should be in Succ
	;
		bottomelement(Succ)
	).
fr_success_builtin_ground(is,Args,_Sv_uns,Call,Succ):-
	!, Args = [A1,A2],
	( fr_ground_arg(A2, Call) ->
		get_vars(A1, Vars),
		fr_abs_int_ground(Call, Vars, Succ)
        ;
                bottomelement(Succ)
        ).
%%%
fr_success_builtin_ground(_Pred,_Args,Sv_uns,Call,Succ):-
	% default: ground without conditions
	fr_abs_int_ground(Call, Sv_uns, Succ).


% fr_abs_int_ground(Call, Sv_uns, Succ)
%
% :- mode fr_abs_int_ground(?,?,o).
fr_abs_int_ground(Call, Sv_uns, Succ):-
	( Sv_uns = [] ->
		Succ = Call
	;
		set_create(Sv_uns, Sv_s),
		ss_make_singl(Sv_s, AlfaC),
		fr_join(Call, AlfaC, Sv_s, Succ)
	).

% fr_nonfree_arg(A, AS)
%
% :- mode fr_nonfree_arg(?,?).
fr_nonfree_arg(A, _):-
	nonvar(A), !.
fr_nonfree_arg(A, as(ACo,ACn)):-
	ss_is_in([A], ACo) -> true; ss_is_in([A], ACn).

% fr_ground_arg(A, AS)
% A must be completely ground (all variables in it must be non-free)
%
% :- mode fr_ground_arg(?,?).
fr_ground_arg(A, _AS):-
	ground(A), !.
fr_ground_arg(A, AS):-
	var(A), !,
	AS = as(ACo,ACn), ( ss_is_in([A], ACo) -> true; ss_is_in([A], ACn) ).
fr_ground_arg(A, AS):-
	A =.. [_|Args], fr_all_ground_args(Args, AS).

fr_all_ground_args([], _AS).
fr_all_ground_args([Arg|Restargs], AS):-
	fr_ground_arg(Arg, AS),
	fr_all_ground_args(Restargs, AS).
	

%--------------------------------------------------------------------------

% fr_abstract_simple(Sv_uns,Call,Succ)
% REQ: not(bottomelement(Call))
% Abstract interpretation of  X (=|#|>) Y
% Sv_uns: unordered list of variables
% Succ = Call ^ AlfaC
% with AlfaC = { Sv_s } where Sv_s is the ordered set of
% Sv_uns variables
%
fr_abstract_simple(Sv_uns,Call,Succ):-
        set_create(Sv_uns,Sv_s),
        AlfaC = [Sv_s],
        fr_join(Call,AlfaC,Sv_s,Succ).

%--------------------------------------------------------------------------

% fr_join(Call, AlfaC, VarsAlfaC, Succ)
% REQ: not(bottomelement(Call))
% computes abstract interpretation of Call by adding AlfaC yielding Succ
% Succ_n = Call_n \AconjM AlfaC
%	= minimise(Call_n1 U (Call_n2 \AconjM AlfaC))
%	(Call_n1 is disjoint with AlfaC, Call_n2 is non-disjoint with AlfaC)
% Succ_t = Call_t \AconjM AlfaC = ... (split Call_t similarly as above)
% Succ_o = Succ_t \ Succ_n
%
fr_join(Call, AlfaC, VarsAlfaC, Succ) :-
	Call = as(ACco, ACcn), 
	Succ = as(ACso, ACsn),
	% new part
	ss_split(ACcn, VarsAlfaC, ACcn1, ACcn2),
		% ACcn1 contains no VarsAlfaC, ACcn2 contains VarsAlfaC
	ss_aconjm(ACcn2, AlfaC, ACsn2),
	ss_union(ACcn1, ACsn2, ACsn_nonmin),
	ss_minimise(ACsn_nonmin, ACsn),
	% old part
	ss_union(ACco, ACcn, ACct_nonmin),
	ss_minimise(ACct_nonmin, ACct),
%% % if no split for ACst
%% 	ss_aconjm(ACct, AlfaC, ACst),
%% 	ss_diff(ACst, ACsn, ACso).
%%
	ss_split(ACct, VarsAlfaC, ACct1, ACct2),
		% ACct1 contains no VarsAlfaC, ACct2 contains VarsAlfaC
	ss_aconjm(ACct2, AlfaC, ACst2),
	ss_union(ACct1, ACst2, ACst_nonmin),
	ss_minimise(ACst_nonmin, ACst),
	ss_diff(ACst, ACsn, ACso).
