%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : combined Definiteness - Minimal Freeness Domain DFm
%                                   U.P.M.(Madrid)  K.U.Leuven
% Copyright (C) 1993 Wim Simoens, Veroniek Dumortier
%	 and Katholieke Universiteit Leuven.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% top predicates for coupling the DFm abstraction with PLAI
% other predicates are defined in
%	min_df_aux.pl : auxiliary predicates for DFm	(fr_*)
%	shared.pl : predicates shared between Fm and DFm
%	fr_os.pl : ordered sets of variables		(set_*)
%	fr_oss23.pl: ordered set of sets			(ss_*)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abstract state <as> ::= as(<def>o,<free>o,<def>n,<free>n) | "'$bottom'"
%			(o = old, n = new)
% <def> ::= ordered set of variables
% <free> ::= ordered set of <sets_of_variables>
% <set_of_variables> ::= ordered set of variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VD	2nd approach old-new
%	2 versions for lub
%	space-optimised (ACo = ACt \ ACn)
%	identical test separately on o- and n-components
%	split local in AconjM (AC1 AconjM AC2: split of AC1 wrt AC2)
%	use of 23-trees locally within AconjM
%
% adjusted abstraction of L::N 16/5/94
% adjusted vero_unknown_call/3    16/5/94
% added vero_unknown_entry/2      16/5/94
% added vero_less_or_equal/2      16/5/94
%
% adjusted vero_call_to_entry	31/05/94
% adjusted vero_exit_to_prime	31/05/94
% note: still adjust vero_call_to_success_fact if entry constraint for fact
%	is needed !!
% corrected vero_anymodes	31/05/94
%
% corrected vero_less_or_equal	16/01/95
% adjusted vero_unknown_entry (changed role old/new)	16/01/95
% adjusted vero_qmode_info (changed role old/new)	16/01/95
% added vero_reverse/2					16/01/95
%
% added builtins and replaced vero_nonfree_arg by vero_ground_arg  25/01/95
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% vero_call_to_entry(Sv, Sg, Hv, Head, K, G_proj, F_proj, G_entry, F_entry)	(S)
% renames F_proj in terms of the call variables of Sg into F_entry
% in terms of the variables of Head and initialises the local clause vars.
% Hv: ordered set of variables in Head
% Sargs, Hargs: list of arguments of Sg (resp. Head)
% F_projSH = F_proj \Aconj alpha(Sargs = Hargs)
%
% :- mode vero_call_to_entry(?,?,?,?,?,?,?,?,o).
vero_call_to_entry(_Sv, _Sg, _Hv, _Head, _K, _G_proj, F_proj, _G_entry, F_proj):-
	bottomelement(F_proj), !.
vero_call_to_entry(_Sv, Sg, Hv, Head, _K, G_proj, F_proj, G_entry, F_entry) :- 
	Sg =.. [_|Sargs], Head =.. [_|Hargs],
	set_union(G_proj, G_entry, G_callhead),
	vero_call_head_unif(Sargs, Hargs, F_proj, G_callhead, F_projSH),
	vero_project(F_projSH, Hv, F_entry).
	/* no initialisation necessary for the local variables */

%----------------------------------------------------------------------------

% vero_exit_to_prime(F_exit,G_exit,Sg,Hv,Head,Sv,G_prime,F_prime)
% maps F_exit (in terms of vars of clause with head H) into
% F_prime (in terms of vars of Sg)
% Note : - no lub is taken (computed separately!!!)
%	 - also the extension wrt variables in the clause of the call S
%	   is not yet done (no call of
%	   vero_extend(F_prime,_,_Sv,Call,Succ)).
% Hv, Sv: ordered set of variables in Head (resp. Sg)
% Hargs, Sargs: list of arguments of Head (resp. Sg)
%
% :- mode vero_exit_to_prime(?,?,?,?,?,?,?,o).
vero_exit_to_prime(F_exit, _G_exit, _Sg, _Hv, _Head, _Sv, _G_prime,
						F_exit):-
	bottomelement(F_exit), !.
vero_exit_to_prime(F_exit,G_exit,Sg,Hv,Head,Sv,G_prime,F_prime) :-
	vero_restriction(Hv, F_exit, Beta_prime),
		% above line not needed ?! BUT will be more efficient:
		% subsequent computation with smaller state Beta_prime
	Head =.. [_|Hargs], Sg =.. [_|Sargs],
	set_union(G_exit, G_prime, G_callhead),
	vero_call_head_unif(Hargs, Sargs, Beta_prime, G_callhead, Beta_primeSH),
	vero_restriction(Sv, Beta_primeSH, F_prime).

%----------------------------------------------------------------------------

% vero_project(Call, Sv, Proj)
% projects Call in terms of all variables of the call environment into
% Proj in terms of just the call variables Sv
% Sv : ordered set of variables
%
% :- mode vero_project(?,?,o).
vero_project(Call, _Sv, Call):-
	bottomelement(Call), !.
vero_project(Call, Sv, Proj):-
	vero_restriction_entry(Sv, Call, Proj).

%----------------------------------------------------------------------------

% SPECIFIC VERSION OF LUB USED AT PROCEDURE EXIT (computes only n-comp)
% vero_compute_lub(LAsub, G_lub, F_lub)
% F_Lub = as(dummy,dummy,dummy,ACnlub) with ACnlub = lub(new_accomps_of_LAsub)
%
% :- mode vero_compute_lub(?,?,o).
vero_compute_lub(LAsub, G_lub, F_lub):-
	get_useful_AS(LAsub, UsefulAsub),
	( UsefulAsub = [] ->                   
		bottomelement(F_lub)
	;
		vero_lub_uas(UsefulAsub, G_lub, F_lub)
	).

% GENERAL VERSION OF LUB TO BE USED FOR ANNOTATION (support3.pl)
% vero_compute_lub_general(LAsub, G_lub, F_lub)
% F_Lub = lub(LAsub)
%
% :- mode vero_compute_lub_general(?,?,o).
%%
%% :- export(vero_compute_lub_general/3).
%% vero_compute_lub_general(LAsub, G_lub, F_lub):-
%% 	get_useful_AS(LAsub, UsefulAsub),
%% 	( UsefulAsub = [] ->
%% 		bottomelement(F_lub)
%% 	;
%% 		vero_lub_uas_general(UsefulAsub, G_lub, F_lub)
%% 	).

%----------------------------------------------------------------------------

% vero_identical_abstract(Asub1, Asub2)
% succeeds if Asub1 and Asub2 are identical abstract states
%
% :- mode vero_identical_abstract(?,?).
vero_identical_abstract(Bottom, Bottom) :- 
	bottomelement(Bottom), !.
vero_identical_abstract(as(D1o,P1o,D1n,P1n), as(D2o,P2o,D2n,P2n)) :- 
	D1o == D2o,
	D1n == D2n,
	ss_identical(P1o,P2o),
	ss_identical(P1n,P2n).

%----------------------------------------------------------------------------

% vero_sort(Asub1, Asub2)
% Asub1 is sorted into Asub2
%
% :- mode vero_sort(?,o).
vero_sort(Bottom,Bottom) :-
	bottomelement(Bottom), !.
vero_sort(as(dummy,dummy,Dn,Pn),as(dummy,dummy,D1n,P1n)) :-
	!,	% can occur due to specific lub
	sort(Dn, D1n),
	ss_sort(Pn, P1n).
vero_sort(as(Do,Po,Dn,Pn),as(D1o,P1o,D1n,P1n)) :-
	sort(Do,D1o),
	sort(Dn,D1n),
	ss_sort(Po,P1o),
	ss_sort(Pn,P1n).

%----------------------------------------------------------------------------

% vero_extend(F_prime,G_succ,Sv,F_call,F_succ)
% F_prime, F_call,F_succ : <as>;
% Sv : sorted list of var. iden. occurring in the call of the predicate
% Let F_prime be the abstract success state of the call
%	(in terms of the call variables Sv)
% and let F_call be the abstract call state of the call
%	(in terms of all the variables in the call environment)
% Then F_succ is the abstract success state of the call
%	(in terms of all the variables in the call environment)
%
% :- mode vero_extend(?,?,?,?,o).
vero_extend(F_prime, _, _, _F_call, F_prime) :-
	% bottomelement(F_call) will not occur, is checked previously
	bottomelement(F_prime), !.
vero_extend(as(_Do,_Po,_Dn,Pn),G_succ,Sv,F_call,F_succ) :-
	vero_join(F_call, Pn, Sv, G_succ, F_succ).

%----------------------------------------------------------------------------

% vero_call_to_success_fact(F_Proj,G_proj,G_succ,Hv,Head,K,Sv,Sg,F_Call,
%		F_Prime,F_Succ)
% F_Proj,F_Call,F_Prime,F_Succ : <as>;
% F_Prime = (F_Proj \Aconj (Sg=Head)) projected onto Sv
% F_Succ = F_Call \Aconj F_Primen
%
vero_call_to_success_fact(F_Proj,_G_proj,_G_succ,_Hv,_Head,_K,_Sv,_Sg,_F_Call,F_Prime,F_Succ) :-
	bottomelement(F_Proj), !, F_Prime = F_Proj, F_Succ = F_Proj.
vero_call_to_success_fact(F_Proj,G_proj,G_succ,_Hv,Head,_K,Sv,Sg,F_Call,F_Prime,F_Succ):-
	Sg =.. [_|Sargs], Head =.. [_|Hargs],
	vero_call_head_unif(Sargs, Hargs, F_Proj, G_proj, F_PrimeSvHv),
	( bottomelement(F_PrimeSvHv) ->
		F_Prime = F_PrimeSvHv, F_Succ = F_Prime
	;
		vero_restriction(Sv, F_PrimeSvHv, F_Prime),
		F_Prime = as(_Do,_Po,_Dn,Pn),
		vero_join(F_Call, Pn, Sv, G_succ, F_Succ)
	).                           


%----------------------------------------------------------------------------

% vero_success_builtin(Type,Sv_uns,InfoF,F_call,G_succ,F_succ)
% Abstract interpretation of builtins
% (note: direct computation, not via projection and extension)
% Type : indicates which kind of special builtin has to be treated
%	currently : '$fd_unchanged', '$fd_fail', '$fd_=', 
%		'$fd_#', '$fd_comp', '$fd_ground', '$fd_$::', '$fd_bound_mult'
% Sv_uns : vars in call of builtin
% F_call,F_succ :<as>
%
% :- mode vero_success_builtin(i,?,?,?,?,o).

vero_success_builtin(_Type,_Sv_uns,_InfoF,F_call,_G_succ,
					F_call) :-
	bottomelement(F_call),!.

vero_success_builtin('$fd_unchanged',_Sv_uns,_InfoF,F_call,_G_succ,
					F_call).

vero_success_builtin('$fd_fail',_Sv_uns,_InfoF,_F_call,_G_succ,
					Bottom):-
	bottomelement(Bottom).

vero_success_builtin('$fd_=',_Sv_uns,InfoF,F_call,G_succ,F_succ):-
	InfoF = '='(L,R),
	vero_success_builtin_eq_noteq(L, R, F_call, G_succ, F_succ).

vero_success_builtin('$fd_#',_Sv_uns,InfoF,F_call,G_succ,F_succ):-
	InfoF = '#'(L,R),
	vero_success_builtin_eq_noteq(L, R, F_call, G_succ, F_succ).

vero_success_builtin('$fd_comp',_Sv_uns,InfoF,F_call,G_succ,
					F_succ):-
	InfoF =.. [Comp,L,R],
	vero_success_builtin_compare(Comp, L, R, F_call, G_succ, F_succ).

vero_success_builtin('$fd_$::',_Sv_uns,InfoF,F_call,G_succ,F_succ):-
	InfoF = '$::'(L,N),
	( var(L), var(N) ->
		ss_empty(SS1),
		set_create([L,N], S), ss_add_el(S, SS1, SS2),
		ss_add_el([N], SS2, AlfaC),
		vero_join(F_call, AlfaC, S, G_succ,F_succ)
	;
	        compiler_error(cons_lists),
		bottomelement(F_succ)                                    
	).

vero_success_builtin('$fd_ground',Sv_uns,InfoF,F_call,G_succ,
					F_succ):-
	InfoF  =.. [P | Args],
	vero_success_builtin_ground(P,Args,Sv_uns,F_call,G_succ,
						F_succ).

vero_success_builtin('$fd_bound_mult',_Sv_uns,InfoF,F_call,G_succ,
					F_Succ):-
	InfoF  =.. [_ | Args],
	Args = [A1, A2, A3],
	( numerical(A1), numerical(A2), numerical(A3),
	  ( vero_ground_arg(A1, F_call) ; vero_ground_arg(A2, F_call) ) ->
		vero_abstract_full_numcs('=', A1*A2, A3, F_call, G_succ, F_Succ)
	;
		bottomelement(F_Succ)
	).


vero_success_builtin('$fd_nonvar',_Sv_uns,nonvar(X),F_call,_,F_succ):-
	vero_nonfree_arg(X,F_call),!,
	F_succ =F_call.
vero_success_builtin('$fd_nonvar',_Sv_uns,_S,_Call,_,Succ):-
	bottomelement(Succ).

vero_success_builtin('$fd_arg',_Sv_uns,InfoF,F_call,G_succ,F_succ):-
        InfoF  =.. [_,A1,A2,A3],
        ( numerical(A1), vero_ground_arg(A1, F_call), vero_nonfree_arg(A2,F_call) ->
                ( var(A2) ->
                        get_vars(A3, Sh),
                        set_add_el(A2, Sh, S),
                        ss_make_singl(S, AlfaC),
                        % [] should be added to AlfaC if pos fail is represented
                        % because the value of A1 may cause failure
                        vero_join(F_call, AlfaC, S, G_succ, F_succ)
                ;
		        compiler_error(arg_not_normal),
			bottomelement(F_succ)
                )
        ;
                bottomelement(F_succ)
        ).

%----------------------------------------------------------------------------

% vero_lambda_to_success_builtin(Sg_key,_Sg,_Sv,_F_call,_F_proj,
% 	                    _F_prime,_F_succ) :-
% 	compiler_error(not_implemented(fd,Sg_key)).

%----------------------------------------------------------------------------

% vero_input_interface(Asub,Asub).

%----------------------------------------------------------------------------

vero_output_interface(as(_Do,Po,_Dn,Pn), External) :-
	!,
%% to see old and new separately
%	External= [Po,Pn].
%% joined old and new
	ss_union(Po,Pn,Pt),
	ss_minimise(Pt,Pt_min),
	External= [closeU(Pt_min)].
vero_output_interface(Asub,Asub).

%----------------------------------------------------------------------------

% vero_unknown_call(Sg,Vars,Call,Succ)
% Gives the "top" value (mode any) for the variables Vars involved in
% a literal whose definition is not present, and joins this top abstraction
% with Call yielding Succ
% Is used for metacalls
% req: Vars is ordered
%
vero_unknown_call(_Sg,_Vars,Call,Call):-
        bottomelement(Call), !.
vero_unknown_call(_Sg,Vars,Call,Succ) :-
        ss_make_singl(Vars, AlfaC),
        vero_join(Call, AlfaC, Vars, [], Succ).

%----------------------------------------------------------------------------

% vero_unknown_entry(Vars,Call)
% Gives the "top" value (mode any) for the variables Vars,
% resulting in the abstract constraint Call
% req: Vars is ordered
%
vero_unknown_entry(Vars, as([],ACo,[],ACn)) :-
%        ss_make_singl(Vars, ACo), ss_empty(ACn). replaced by  16/01/95
%	(reason : what is used for query is Call info, not projected info)
        ss_empty(ACo), ss_make_singl(Vars, ACn).

%----------------------------------------------------------------------------

% vero_less_or_equal(Asub1,Asub2) (SF)
% succeeds if Asub1 =< Asub2
%
% :- mode vero_less_or_equal(?,?).
vero_less_or_equal(Bottom, Bottom):-
        bottomelement(Bottom), !.
vero_less_or_equal(as(Do1,Po1,Dn1,Pn1), as(Do2,Po2,Dn2,Pn2)) :-
	set_is_subset(Do2,Do1),
	set_is_subset(Dn2,Dn1),
	%
	set_diff(Do1, Do2, Do1MinDo2),
	ss_make_singl(Do1MinDo2, Singo),
	ss_union(Singo, Po1, Union1o),
        ss_close(Po2, Po2Cl),
        ss_is_subset(Union1o, Po2Cl),
	%
	set_diff(Dn1, Dn2, Dn1MinDn2),
	ss_make_singl(Dn1MinDn2, Singn),
	ss_union(Singn, Pn1, Union1n),
        ss_close(Pn2, Pn2Cl),
        ss_is_subset(Union1n, Pn2Cl).
 
%% %----------------------------------------------------------------------------
%%                    
%% % vero_qmode_info(Info,G,F)
%% % Given the query pattern Info, computes the call state F
%% %
%% % :- mode vero_qmode_info(i,?,o).
%% vero_qmode_info(Info,G,F) :-
%% 	vero_anymodes(Info,[],Lavars),
%%         set_diff(Lavars, G, Avars),
%% %	ss_make_singl(Avars,ACo), ss_empty(ACn),
%% %	F = as(G,ACo,[],ACn).
%% %  replaced by  16/01/95 :
%% %  (reason : what is used for query is Call info, not projected info)
%% 	ss_empty(ACo), ss_make_singl(Avars,ACn),
%% 	F = as([],ACo,G,ACn).
%% 

%% 
%% vero_anymodes([],Lavars,Lavars).
%% vero_anymodes([mode(_Varident,f)|Info],LavarsAcc,Lavars) :-
%%         !, vero_anymodes(Info,LavarsAcc,Lavars).
%% vero_anymodes([mode(Varident,_)|Info],LavarsAcc,Lavars) :-
%%         set_add_el(Varident,LavarsAcc,LavarsNewAcc),
%%         vero_anymodes(Info,LavarsNewAcc,Lavars).
%% 

%----------------------------------------------------------------------------
% Maria Garcia de la Banda May-1995
% Similar to the one above but with Info with the form free(ListFreeVars)
% instead of [mode(X,f),mode(Y,g),..] etc

vero_input_user_interface((Gv,Fv),Vars,Call):-
	may_be_var(Gv),
	may_be_var(Fv),
	merge(Gv,Fv,FreeAndGroundVars),
	ord_subtract(Vars,FreeAndGroundVars,TopVars),
	ss_empty(ACo), 
	ss_make_singl(TopVars,ACn),
	Call = as([],ACo,Gv,ACn).

paco_input_interface(free(V),approx,(Gv,Fv0),(Gv,Fv)):-
	var(V),
	myinsert(Fv0,V,Fv).
paco_input_interface(ground(V),perfect,(Gv0,Fv),(Gv,Fv)):-
	varset(V,Vs),
	myappend(Gv0,Vs,Gv).

myinsert(Fr0,X,Fr):-
	var(Fr0), !,
	Fr = [X].
myinsert(Fr0,X,Fr):-
	insert(Fr0,X,Fr).

myappend(Vs,V0,V):-
	var(Vs), !,
	V=V0.
myappend(Vs,V0,V):-
	merge(Vs,V0,V).

may_be_var(X):- ( X=[] ; true ), !.

%----------------------------------------------------------------------------                                                                         
% vero_reverse(AS, ASrev)
% interchanges the old and new components in the abstraction
% note : not(bottomelement(AS))
%
% :- mode vero_reverse(i,o).
%% vero_reverse(as(Do,Po,Dn,Pn), as(Dn,Pn,Do,Po)).
