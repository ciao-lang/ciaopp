%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : combined Definiteness-Freeness Domain DFm
%                                      Madrid      Leuven
% Copyright (C) 1993 Wim Simoens. Veroniek Dumortier
%	 and Katholieke Universiteit Leuven.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% auxiliary predicates for coupling the DFm abstraction with PLAI
% uses set_* predicates from fr_os.pl
% uses ss_* predicates from fr_oss23.pl
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abstract state <as> ::= as(<def>o, <free>o, <def>n, <free>n) | "'$bottom'"
%			(o = old, n = new)
% <def> ::= ordered set of variables
% <free> ::= ordered set of <sets_of_variables>
% <set_of_variables> ::= ordered set of variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VD	2nd approach old-new
%	2 versions for lub
%	space-optimised (o = t \ n)
%	identical test separately on o- and n-components
%	idea of split:
%		extra parameter needed in vero_join, namely (ordered) set of
%		variables occurring in the AlfaC part
%		Split of ss-info in F_call w.r.t. AlfaC
%
% added builtins and improved some existing builtins    25/01/95
% replaced vero_nonfree_arg in builtins by vero_ground_arg
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% vero_call_head_unif(Sargs, Hargs, Asub, G, AsubSH)
% AsubSH = Asub \Aconj_G alpha(Sargs = Hargs)
%
% :- mode vero_call_head_unif(?,?,?,?,o).
vero_call_head_unif([], [], Asub, _G, Asub).
vero_call_head_unif([Sarg | SargRest], [Harg | Hargrest], Asub, G, AsubSH):-
	vero_success_builtin_eq_noteq(Sarg, Harg, Asub, G, Asub1),
	vero_call_head_unif(SargRest, Hargrest, Asub1, G, AsubSH).

%----------------------------------------------------------------------------

% vero_restriction(Hv, Asub, Asub_restr) 	(S)
% REQ: not(bottomelement(Asub))
% Asub, Asub_restr: <as>; Hv : sorted list of variable identifiers
% Asub_restr is the restriction of Asub wrt the variables in Hv
%
% :- mode vero_restriction(?,?,o).
vero_restriction(_Hv, Asub, Asub_restr):-
	bottomelement(Asub), !, Asub_restr = Asub.
vero_restriction(Hv, as(Do1, Po1, Dn1, Pn1), as(Do2, Po2, Dn2, Pn2)) :- 
	def_restriction(Do1,Hv,Do2),	% assumes that Do1 and Dn1 are sorted
	def_restriction(Dn1,Hv,Dn2),
	ss_restriction(Po1,Hv,Po2),
	ss_restriction(Pn1,Hv,Pn2).

%----------------------------------------------------------------------------

% vero_restriction_entry(Vars, Call, Proj) 	(S)
% REQ: not(bottomelement(Call))
% Call, Proj: <as>; Vars : sorted list of variable identifiers
% Proj is the restriction of Call wrt the variables in Vars
% Used at procedure entry -> the new component of Proj is empty
%
% :- mode vero_restriction_entry(?,?,o).
vero_restriction_entry(Vars, as(Do1, Po1, Dn1, Pn1), as(Do2, Po2, Dn2, Pn2)) :-
	def_restriction(Do1, Vars, Do1r), % assumes that Do1 is sorted
	def_restriction(Dn1, Vars, Dn1r), % assumes that Do1 is sorted
	set_union(Do1r, Dn1r, Do2),
	ss_restriction(Po1, Vars, Po1r),
	ss_restriction(Pn1, Vars, Pn1r),
	ss_union(Po1r, Pn1r, Po2_nonmin),
	ss_minimise(Po2_nonmin, Po2),
        def_empty(Dn2), % Dn2 is empty as required by procedure-entry
	ss_empty(Pn2).	% Pn2 is empty as required by procedure-entry

%----------------------------------------------------------------------------

% SPECIFIC VERSION OF LUB USED AT PROCEDURE EXIT (computes only n-comp)
% uses approach 2 (wrt determining old-new)

% vero_lub_uas(UsefulASlist, G_lub, F_lub)
% REQ : UsefulASlist =/= []
%
% :- mode vero_lub_uas(?,?,o).
vero_lub_uas([as(_Do,_Po,Dn,Pn) | UsefulASlist], G_lub,
			as(dummy,dummy,Dnlub,Pnlub)):-
	% dummy has to be filled in, do not leave uninstantiated vars because
	% subsequent vero_identical_abstract test would check identity of
	% =/= vars
	vero_lub_uas2(UsefulASlist, G_lub, Dn, Pn, Dnlub, Pnlub).

% vero_lub_uas2(UsefulASlist, G_lub, Dn, Pn, Dnlub, Pnlub)
% Dnlub = lub({Dn,Dn_comps_of_UsefulASlist})
% Pnlub = lub({Pn,Pn_comps_of_UsefulASlist})
%
% :- mode vero_lub_uas2(?,?,?,?,o,o).
vero_lub_uas2([], _G_lub, Dnlub, Pnlub, Dnlub, Pnlub).
vero_lub_uas2([as(_Do1,_Po1,Dn1,Pn1) | UsefulASlist], G_lub, Dn2, Pn2,
			Dnlub, Pnlub):-
	vero_lub(Dn1, Pn1, Dn2, Pn2, G_lub, DnlubAcc, PnlubAcc),
	vero_lub_uas2(UsefulASlist, G_lub, DnlubAcc, PnlubAcc, Dnlub, Pnlub).

% vero_lub(Dn1, Pn1, Dn2, Pn2, G_lub, Dn_lub, Pn_lub)
% Dn_lub = lub(Dn1, Dn2) = Dn1 intersect Dn2
% Pn_lub = minimise( Pn1 U Pn2 U {{X} | X in (Dn1 U Dn2) \ G_lub } )
%
% :- mode vero_lub(?,?,?,?,?,o,o).
vero_lub(Dn1, Pn1, Dn2, Pn2, G_lub, Dn_lub, Pn_lub) :-
	% computation of Dn_lub
	set_intersect(Dn1, Dn2, Dn_lub),
	% computation of Pn_lub
	set_union(Dn1, Dn2, Dn12),
	set_diff(Dn12, G_lub, Sings),
	ss_make_singl(Sings, Sing1n),
	ss_union_list([Pn1,Pn2,Sing1n], Pn_lub_nonmin),
	ss_minimise(Pn_lub_nonmin, Pn_lub).


% GENERAL VERSION OF LUB TO BE USED FOR ANNOTATION (support3.pl)
% uses approach 2 (wrt determining old-new)

% vero_lub_uas_general(UsefulASlist,G_lub,F_lub)
% REQ : UsefulASlist =/= []
%
% :- mode vero_lub_uas_general(?,?,o).
%%
%% vero_lub_uas_general([AS1 | UsefulASlist], G_lub, F_lub):-
%% 	vero_lub_uas_general2(UsefulASlist, AS1, G_lub, F_lub).
%% 
%% % vero_lub_uas_general2(UsefulASlist, F_lub_Acc, G_lub, F_lub)
%% % F_lub = lub({F_lub_Acc, States_of_UsefulASlist})
%% %
%% % :- mode vero_lub_uas_general2(?,?,?,o).
%% vero_lub_uas_general2([], F_lub, _G_lub, F_lub).
%% vero_lub_uas_general2([AS1 | ASrest], AS2, G_lub, F_lub):-
%% 	vero_lub_general(AS1, AS2, G_lub, Lub12),
%% 	vero_lub_uas_general2(ASrest, Lub12, G_lub, F_lub).
%% 
%% % vero_lub_general(AS1, AS2, G_lub, AS_lub)
%% % AS_lub = lub(AS1, AS2) given G_lub
%% %
%% % :- mode vero_lub_general(?,?,?,o).
%% vero_lub_general(as(D1o,P1o,D1n,P1n), as(D2o,P2o,D2n,P2n), G_lub, Lub) :-
%% 	Lub = as(Dlo,Plo,Dln,Pln),
%% 	% def part	
%% 	set_intersect(D1n, D2n, Dln), 	% D1n \intersect D2n = Dln
%% 	set_diff(G_lub, Dln, Dlo), 	% Dlo = G_lub \ Dln (cfr footnote 12)
%% 
%% 	% free part, Pnew
%% 	set_union(D1n, D2n, D12n),
%% 	set_diff(D12n, G_lub, Sings),
%% 	ss_make_singl(Sings, Sing1n),
%% 	ss_union_list([P1n,P2n,Sing1n], Pln_nonmin),
%% 	ss_minimise(Pln_nonmin, Pln),
%% 
%% 	% free part, Ptot
%% 	set_union_list([D1o, D2o, D12n], D12t),
%% 	set_diff(D12t, G_lub, DefXst),
%% 	ss_make_singl(DefXst, Singt),
%% 	ss_union_list([P1o, P1n, P2o, P2n, Singt], Plt_nonmin),
%% 	ss_minimise(Plt_nonmin,Plt),
%% 
%% 	% free part, Pold
%% 	ss_diff(Plt, Pln, Plo).

%--------------------------------------------------------------------------

% vero_success_builtin_eq_noteq(L, R, Call,G_succ,Succ)
% Abstract interpretation of L (=|#) R
% note: recursive calls may have bottomelement(Call) !
%
% :- mode vero_success_builtin_eq_noteq(?,?,?,?,o).
vero_success_builtin_eq_noteq(_L, _R, Call, _G_succ, Succ):-
	bottomelement(Call), !, Succ = Call.
vero_success_builtin_eq_noteq(L, R, Call, G_succ, Succ):-
        get_type(L, TypeL),
        get_type(R, TypeR),
        ( TypeL == var ->
        	( TypeR == var ->
                      (L == R -> Succ = Call ; vero_abstract_simple([L,R], Call, G_succ, Succ))
                ;
                      vero_prim_eq_noteq_split(TypeR,L,R,Call,G_succ,Succ)
                )
        ;
                ( TypeR == var ->
                      vero_prim_eq_noteq_split(TypeL,R,L,Call,G_succ,Succ)
                ;
                      ( TypeL == TypeR ->
                              vero_full_eq_noteq_split(TypeL,L,R,Call,
					G_succ,Succ)
                      ;
                              bottomelement(Succ)
                      )
                )
        ).

vero_prim_eq_noteq_split(herb, L, R, Call, G_succ, Succ):-
        vero_abstract_prim_herbcs(L, R, Call, G_succ, Succ).
vero_prim_eq_noteq_split(num, L, R, Call, G_succ, Succ):-
        vero_abstract_prim_numcs('=', L, R, Call, G_succ, Succ).
vero_prim_eq_noteq_split(piii, L, piii(R), Call, G_succ, Succ):-
        vero_abstract_prim_piiics(L, R, Call, G_succ, Succ).

vero_full_eq_noteq_split(herb, L, R, Call, G_succ, Succ):-
        vero_abstract_full_herbcs(L, R, Call, G_succ, Succ).
vero_full_eq_noteq_split(num, L, R, Call, G_succ, Succ):-
        vero_abstract_full_numcs('=', L, R, Call, G_succ, Succ).
vero_full_eq_noteq_split(piii, piii(L), piii(R), Call, G_succ, Succ):-
        vero_abstract_full_piiics(L, R, Call, G_succ, Succ).

%--------------------------------------------------------------------------

% vero_abstract_prim_herbcs(Var, Term, Call, G_succ, Succ)
% Abstract interpretation of Var (=|#) Term (Term is a nonvar Herbrand term)
% REQ: not bottomelement(Call)
%
vero_abstract_prim_herbcs(Var, Term, Call, G_succ, Succ):-
        get_var_groups(Term, TermVars, VarGroups),
        ss_make_AlfaFunctor_groups(VarGroups, Var, AlfaC),
        set_add_el(Var, TermVars, VarsAlfaC),
        vero_join(Call, AlfaC, VarsAlfaC, G_succ, Succ).
        
%--------------------------------------------------------------------------

% vero_abstract_full_herbcs(Term1, Term2, Call, G_succ, Succ)
% Abstract interpretation of Term1 (=|#) Term2
% (both Term1 and Term2 are nonvar Herbrand terms)
% REQ: not bottomelement(Call)
%
vero_abstract_full_herbcs(Term1, Term2, Call, G_succ, Succ):-
        functor(Term1, F1, A1),
        functor(Term2, F2, A2),
        ( F1 == F2, A1 == A2 ->	   	% also works for A1=A2=0
                Term1 =.. [_|Args1], Term2 =.. [_|Args2],
                vero_abstract_herbcs_args(Args1, Args2, Call, G_succ, Succ)
        ;
                bottomelement(Succ)
        ).

% vero_abstract_herbcs_args(Args1, Args2, Call, G_succ, Succ)
% Abstract interpretation of Args1 = Args2 by recursively equating the
% corresponding arguments
% note : bottomelement(Call) is possible now !
%
vero_abstract_herbcs_args([], [], Succ, _G_succ, Succ).
vero_abstract_herbcs_args([Arg1 | Rest1], [Arg2 | Rest2],Call,G_succ,Succ):-
	vero_success_builtin_eq_noteq(Arg1, Arg2, Call, G_succ, Lambda_mid),
	% one could already test for bottomelement(Lambda_mid) here
	vero_abstract_herbcs_args(Rest1, Rest2, Lambda_mid, G_succ, Succ).

%--------------------------------------------------------------------------

% vero_abstract_prim_numcs(Comp, Var, Term, Call, G_succ, Succ)
% Abstract interpretation of the numerical constraint  "Var Comp Term"
% (Term is a nonvar numerical term)
% REQ: not(bottomelement(Call))
%
% :- mode vero_abstract_prim_numcs(?,?,?,?,o).
vero_abstract_prim_numcs(_Comp, Var, Term, Call, G_succ, Succ):-
        ( linear(Term) ->
		get_vars_repvars([Var,Term], Vars, Doubles),
		ss_oplusm([Vars], [Doubles], SS),
		ss_add_el(Vars, SS, SS2),
		ss_minimise(SS2, AlfaC)
        ;
        	get_vars([Var,Term], Vars),
                ss_make_singl(Vars, AlfaC)
        ),
        vero_join(Call, AlfaC, Vars, G_succ, Succ).

%--------------------------------------------------------------------------

% vero_abstract_full_numcs(Comp, Term1, Term2, Call, G_succ, Succ)
% Abstract interpretation of the numerical constraint  "Term1 Comp Term2"
% (both Term1 and Term2 are nonvar numerical terms)
% REQ: not bottomelement(Call)
%
vero_abstract_full_numcs(Comp, Term1, Term2, Call, G_succ, Succ):-
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
				vero_join(Call, AlfaC, Vars, G_succ, Succ)
			;
				Succ = Call
			)
        	;
			get_vars([Term1,Term2], Vars),
			( Vars \== [] ->
                		ss_make_singl(Vars, AlfaC),
				vero_join(Call, AlfaC, Vars, G_succ, Succ)
			;
				Succ = Call
			)
          	)
	).

%--------------------------------------------------------------------------

% vero_success_builtin_compare(Comp,L,R,Call,G_succ,Succ)
% REQ: not(bottomelement(Call))
% Abstract interpretation of "L Comp R" with Comp::= (> | >= | < | <= )
%
% :- mode vero_success_builtin_compare(?,?,?,?,o).
vero_success_builtin_compare(Comp,L,R,Call,G_succ,Succ) :-
	numerical(L), numerical(R) ->
		vero_abstract_full_numcs(Comp,L,R,Call,G_succ,Succ)
	;
		bottomelement(Succ)
	.

%--------------------------------------------------------------------------

% vero_abstract_prim_piiics(Var, Term, Call, G_succ, Succ)
% abstract interpretation of Var (=|#) Term where Term is a list of
% concatenated piii-tuple parts
%	e.g. Term = [X, [f(Y),Z+U], T] -> X.<f(Y),Z+U)>.T
%
vero_abstract_prim_piiics(Var, Term, Call, G_succ, Succ):-
	get_var_groups(Term, TermVars, VarGroups),
        ss_addpairs_groups(VarGroups, Var, [], SS),
	( piii_restricted_length(Term) ->
		ss_add_el([Var], SS, AlfaC) ; AlfaC = SS ),
        set_add_el(Var, TermVars, VarsAlfaC),
        vero_join(Call, AlfaC, VarsAlfaC, G_succ, Succ).

%--------------------------------------------------------------------------

% vero_abstract_full_piiics(Term1, Term2, Call, G_succ, Succ)
% abstract interpretation of Term1 (=|#) Term2 where
% Term1 and Term2 are lists of concatenated piii-tuple parts
%
vero_abstract_full_piiics([], [], Call, _G_succ, Call):- !.
vero_abstract_full_piiics([], Term2, Call, G_succ, Succ):-
	!,
	vero_piii_empty(Term2, Call, G_succ, Succ).
vero_abstract_full_piiics(Term1, [], Call, G_succ, Succ):-
	!,
	vero_piii_empty(Term1, Call, G_succ, Succ).
vero_abstract_full_piiics([X], Term2, Call, G_succ, Succ):-
	var(X), !, vero_abstract_prim_piiics(X, Term2, Call, G_succ, Succ).
vero_abstract_full_piiics(Term1, [X], Call, G_succ, Succ):-
	var(X), !, vero_abstract_prim_piiics(X, Term1, Call, G_succ, Succ).
vero_abstract_full_piiics([X|Rest1], [Y|Rest2], Call, G_succ, Succ):-
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
        vero_join(Call, AlfaC, VarsAlfaC, G_succ, Succ).
vero_abstract_full_piiics([X|Rest1], [Y|Rest2], Call, G_succ, Succ):-
	!,
        vero_peel_piiics(X, Y, Rest1, Rest2, NR1, NR2, Call, G_succ, NCall),
	( bottomelement(NCall) ->
		Succ = NCall
	;
	        vero_abstract_full_piiics(NR1, NR2, NCall, G_succ, Succ)
	).
vero_abstract_full_piiics(_Term1, _Term2, _Call, _G_succ, Succ):-
	% Term1 and/or Term2 not a list
	compiler_error(piii_lists),
	bottomelement(Succ).

vero_peel_piiics([], [], R1, R2, R1, R2, Call, _G_succ, Call):- !.
vero_peel_piiics([], Term, R1, R2, R1, [Term|R2], Call, _G_succ, Call):- !.
vero_peel_piiics(Term, [], R1, R2, [Term|R1], R2, Call, _G_succ, Call):- !.
vero_peel_piiics([X|Rest1], [Y|Rest2], R1, R2, NR1, NR2, Call, G_succ, Succ):-
        vero_success_builtin_eq_noteq(X, Y, Call, G_succ, NCall),
	( bottomelement(NCall) ->
		Succ = NCall
	;
		vero_peel_piiics(Rest1, Rest2, R1, R2, NR1, NR2, NCall, G_succ, Succ)
	).


vero_piii_empty([], Call, _G_succ, Call).
vero_piii_empty([ V | Rest], Call, G_succ, Succ):-
	var(V), !,
	vero_join(Call, [[V]], [V], G_succ, NCall),
	vero_piii_empty(Rest, NCall, G_succ, Succ).
vero_piii_empty([ [] | Rest ], Call, G_succ, Succ):-
	!, vero_piii_empty(Rest, Call, G_succ, Succ).
vero_piii_empty(_T, _Call, _G_succ, Succ):-
	bottomelement(Succ).

%--------------------------------------------------------------------------

% vero_success_builtin_ground(Pred, Args, Sv_uns, Call, G_succ, Succ)
% REQ: not(bottomelement(Call))
% note : the default is given by the last clause
%	 the other clauses may detect '$bottom' based on conditions on the
%	 call pattern or type of the arguments of the builtin;
%	 this leads to more precise output, but is also more time-consuming !
%	 (one could use the default in all cases if time performance is
%	  important)
%
% :- mode vero_success_builtin_ground(?,?,?,?,?,o).
vero_success_builtin_ground(assign,Args,Sv_uns,Call,G_succ,Succ):-
	!, Args = [I, T],
	( vero_ground_arg(I, Call),
	  vero_ground_arg(T, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(cpu_time,Args,Sv_uns,Call,G_succ,Succ):-
	!, Args = [A],
	( numerical(A) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(enum,Args,Sv_uns,Call,G_succ, Succ):-
	!, Args = [A],
	( numerical(A) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(erase,Args,Sv_uns,Call,G_succ, Succ):-
	!, Args = [A],
	( vero_ground_arg(A, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(min_value,Args,_Sv_uns,Call,G_succ, Succ):-
	!, Args = [A1, A2],
	( numerical(A1), numerical(A2) ->
		get_vars(A2, Vars),
		vero_abs_int_ground(Call, Vars, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(outm,Args,Sv_uns,Call,G_succ, Succ):-
	!, Args = [A],
	( vero_ground_arg(A, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(outml,Args,Sv_uns,Call,G_succ, Succ):-
	!, Args = [A],
	( vero_ground_arg(A, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(recorda,Args,_Sv_uns,Call,G_succ, Succ):-
	!, Args = [Key, _Term, Ref],
	( vero_ground_arg(Key, Call) ->
		get_vars([Key,Ref], Vars),
		vero_abs_int_ground(Call, Vars, G_succ, Succ)
	;
		bottomelement(Succ)
	).
vero_success_builtin_ground(val,Args,Sv_uns,Call,G_succ, Succ):-
	!, Args = [A1, _A2],
	( vero_ground_arg(A1, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
	).
%%% VD added 25/01/95
vero_success_builtin_ground(sys_command,Args,Sv_uns,Call,G_succ, Succ):-
        !, Args = [A],
        ( vero_ground_arg(A, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
	;
		bottomelement(Succ)
        ).
vero_success_builtin_ground((=\=),Args,Sv_uns,Call,G_succ, Succ):-
        !, Args = [A1, A2],
        ( vero_ground_arg(A1, Call),
          vero_ground_arg(A2, Call) ->
                vero_abs_int_ground(Call, Sv_uns, G_succ, Succ) 
        ; 
                bottomelement(Succ) 
        ). 
vero_success_builtin_ground(is,Args,Sv_uns,Call,G_succ, Succ):- 
        !, Args = [_A1, A2],
        ( vero_ground_arg(A2, Call) ->
		vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
        ;  
                bottomelement(Succ)  
        ).
%%%
vero_success_builtin_ground(_Pred,_Args,Sv_uns,Call,G_succ, Succ):-
	% default: ground without conditions
	vero_abs_int_ground(Call, Sv_uns, G_succ, Succ).

% vero_abs_int_ground(Call, Sv_uns, G_succ, Succ)
%
% :- mode vero_abs_int_ground(?,?,o).
vero_abs_int_ground(Call, Sv_uns, G_succc, Succ):-
	set_create(Sv_uns, Sv_s),
	ss_make_singl(Sv_s, AlfaC),
	vero_join(Call, AlfaC, Sv_s, G_succc, Succ).

% vero_nonfree_arg(A, AS)
%
% :- mode vero_nonfree_arg(?,?).
vero_nonfree_arg(A,_):-
	nonvar(A), !.
vero_nonfree_arg(A, as(Do,Po,Dn,Pn)):-
	set_is_in(A, Do), ! ;
	set_is_in(A, Dn), ! ;
	ss_is_in([A], Po), !;
	ss_is_in([A], Pn).

% vero_ground_arg(A, AS)
% A must be completely ground (so all variables in it must certainly be non-free)
%
% :- mode vero_ground_arg(?,?).
vero_ground_arg(A, _AS):-
	ground(A), !.
vero_ground_arg(A, AS):-
        var(A), !,
	AS = as(Do,Po,Dn,Pn),
        ( set_is_in(A, Do), ! ;
          set_is_in(A, Dn), ! ;
          ss_is_in([A], Po), !;
          ss_is_in([A], Pn) ).
vero_ground_arg(A, AS):-
	A =.. [_|Args], vero_all_ground_args(Args, AS).
 
vero_all_ground_args([], _AS).
vero_all_ground_args([Arg|Restargs], AS):-
        vero_ground_arg(Arg, AS),
        vero_all_ground_args(Restargs, AS).

%--------------------------------------------------------------------------

% vero_abstract_simple(Sv_uns, F_call, G_succ, F_succ)
% REQ: not(bottomelement(F_call))
% Abstract interpretation of  X (=|#|>) Y
% Sv_uns: unordered list of variables
% F_succ = F_call ^ AlfaC
% with AlfaC = { Sv_s } where Sv_s is the ordered set of
% Sv_uns variables
%
vero_abstract_simple(Sv_uns, F_call, G_succ, F_succ):-
	set_create(Sv_uns, Sv_s),
	AlfaC = [Sv_s],
	vero_join(F_call, AlfaC, Sv_s, G_succ, F_succ).

%--------------------------------------------------------------------------

% vero_join(F_call, AlfaC, VarsAlfaC, F_succ)
% REQ: not(bottomelement(F_call))
% computes abstract interpretation of F_call by adding AlfaC yielding F_succ
%
vero_join(F_call, AlfaC, VarsAlfaC, G_succ, F_succ) :-
	F_call = as(Dco, Pco, _Dcn, Pcn), 
	F_succ = as(Dso, Pso, Dsn, Psn),
	% definiteness part
	Dso = Dco,
	set_diff(G_succ,Dco,Dsn),

	% freeness part Psn
	ss_reduce_min(Pcn,G_succ,Rcn),
	ss_reduce_min(AlfaC,G_succ,Ra),
	ss_split(Rcn, VarsAlfaC, Rcn1, Rcn2),
	ss_aconjm(Rcn2,Ra,Psn2),
	ss_union(Rcn1,Psn2,Psn_nonmin),
	ss_minimise(Psn_nonmin,Psn),

	% freeness part Pst
	ss_union(Pco, Pcn, Pct),
	ss_reduce_min(Pct,G_succ,Rct),
	ss_split(Rct, VarsAlfaC, Rct1, Rct2),
	ss_aconjm(Rct2,Ra,Pst2),
	ss_union(Rct1,Pst2,Pst_nonmin),
	ss_minimise(Pst_nonmin,Pst),

	% freeness part Pso
	ss_diff(Pst, Psn, Pso).

%--------------------------------------------------------------------------


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%                                def_* part
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%--------------------------------------------------------------------------

def_empty([]).

%--------------------------------------------------------------------------
%% 
%% % def_renaming(Varlist1, Varlist2, D, Dren)	(S)
%% % Varlist1, Varlist2 : congruent lists of var. identifiers (unordered!)
%% % D in terms of vars of Varlist1 is renamed to Dren in terms of vars of
%% % Varlist2
%% %
%% % :- mode def_renaming(i,i,?,o).
%% def_renaming(Varlist1, Varlist2, D, Dren) :-
%% 	def_ren(Varlist1, Varlist2, D, [], Dren).	% [] is empty set
%% 
%% def_ren(_Varlist1, _Varlist2, [], Dren, Dren).
%% def_ren(Varlist1, Varlist2, [Var | D], DrenAcc, Dren) :-
%% 	newname(Varlist1, Varlist2, Var, Varren),
%% 	set_add_el(Varren, DrenAcc, NewDrenAcc),
%% 	def_ren(Varlist1, Varlist2, D, NewDrenAcc, Dren).
%% 
%% % newname(Varlist1, Varlist2, Var, Varren)
%% % the mapping Varlist1 -> Varlist2 maps Var to Varren
%% %
%% % :- mode newname(i,i,i,o).
%% newname([Iold | _L1], [Inew |_L2], I, Inew) :- 
%% 	Iold == I, !.
%% newname([_I1 | L1], [_I2 | L2], I, Inew) :- 
%% 	newname(L1, L2, I, Inew).

%--------------------------------------------------------------------------

% def_restriction(D, Vars, Dr).
% Vars : ordered set of variables
% Dr = { X in D | X in Vars }
%
% :- mode def_restriction(?,?,o).
def_restriction([], _Vars, []).
def_restriction([Dvar | Dvars], Vars, Dr):-
	( set_is_in(Dvar, Vars) ->
		( Dr = [Dvar | DrRest],	% uses that [Dvar | Dvars] is ordered
		def_restriction(Dvars, Vars, DrRest))
	;
		def_restriction(Dvars, Vars, Dr)
	).
