:- module(fr_top,
	[ fr_call_to_entry/9, 
	  fr_call_to_success_fact/9,
	  fr_compute_lub/2,   
	  fr_exit_to_prime/7,
	  fr_extend/5,        
	  fr_identical_abstract/2, 
	  fr_input_user_interface/5,  
	  fr_input_interface/4,  
	  fr_less_or_equal/2,
	  fr_glb/3,
	  fr_output_interface/3,
	  fr_project/5,       
	  fr_sort/2,          
	  fr_special_builtin/5,
	  fr_success_builtin/6,
	  fr_asub_to_native/5,
	  fr_unknown_call/4,
	  fr_unknown_entry/3,
	  fr_empty_entry/3,
	% humm...
	  get_free_vars/3
	], [datafacts]).

:- use_module(ciaopp(p_unit), [language/1]).
:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

:- use_module(domain(fr_sets)).
:- use_module(domain(fr_shared)).

:- use_module(library(sets), [insert/3, ord_subtract/3]).
:- use_module(library(sort), [sort/2]).

:- include(domain(fr_aux)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% file min_fr_top.pl
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : Minimal Freeness Domain Fm
% Copyright (C) 1993 Wim Simoens, Veroniek Dumortier and
%		Katholieke Universiteit Leuven.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% top predicates for coupling the minimal freeness abstraction Fm with PLAI
% other predicates are defined in         
%	min_fr_aux.pl : auxiliary predicates for Fm	(fr_*)
%	shared.pl : predicates shared between Fm and DFm
%	fr_os.pl : ordered sets of variables		(set_*)
%	fr_oss23.pl: ordered set of sets			(ss_*)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abstract state <as> ::= as(<ac>o , <ac>n) | "'$bottom'"
%			(o = old, n = new)
% <ac> ::= ordered set of <sets_of_variables>
% <set_of_variables> ::= ordered set of variables
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VD	2nd approach old-new
%	2 versions for lub
%	space-optimised (o = t \ n)
%	identical test separately on o- and n-components
%	split local in AconjM (AC1 AconjM AC2: split of AC1 wrt AC2)
%		AC1 \AconjM AC2 = minimise( (AC1_disjoint_with_AC2)
%				U (AC1_nondisjoint_with_AC2 \AconjM AC2) )
%	use of 23-trees locally within AconjM
%
% adjusted abstraction of L::N	16/5/94
% adjusted fr_unknown_call/3	16/5/94
% added fr_unknown_entry/2	16/5/94
% added fr_less_or_equal/2	16/5/94
%
% adjusted fr_unknown_entry/2 (change role ACo,ACn)	16/01/95
% adjusted fr_qmode_info/2 (change role ACo,ACn)	16/01/95
% added fr_reverse/2					16/01/95
% 
% added builtins and replaced fr_nonfree_arg by fr_ground_arg  25/01/95
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% fr_call_to_entry(_Sv,Sg,Hv,Head,_K,_Fv,Proj,Entry,_ExtraInfo) (S)
% renames Proj in terms of the call variables of Sg into Entry
% in terms of the variables of Head and initialises the local clause vars.
% Hv: ordered set of variables in Head
% Sargs, Hargs: list of arguments of Sg (resp. Head)
% ProjSH = Proj \Aconj alpha(Sargs = Hargs)
%
% :- mode fr_call_to_entry(?,?,?,o).
fr_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,Entry,Entry,_ExtraInfo):-
	bottomelement(Entry), !.
fr_call_to_entry(_Sv,Sg,Hv,Head,_K,_Fv,Proj,Entry,_ExtraInfo):-
	Sg =.. [_ | Sargs], Head =.. [_ | Hargs],
	fr_call_head_unif(Sargs, Hargs, Proj, ProjSH),
	fr_project_(ProjSH, Hv, Entry).
        %% no initialisation necessary for the local variables
                                                                             
%----------------------------------------------------------------------------

% fr_exit_to_prime(Sg, Hv, Head, Sv, Exit, _ExtraInfo, Prime)  (S)                     
% maps Exit (in terms of vars of clause with head H) into           
% Prime (in terms of vars of Sg)
% Note : - no lub is taken (computed separately!!!)
%	 - also the extension wrt variables in the clause of the call S
%	   is not yet done (no call of
%	   fr_extend(Sg, Prime,_Sv,Call,Succ)).
% Hv, Sv: ordered set of variables in Head (resp. Sg)
% Hargs, Sargs: list of arguments of Head (resp. Sg)
%
% :- mode fr_exit_to_prime(?,?,?,o).
fr_exit_to_prime(_Sg, _Hv, _Head, _Sv, Exit, _ExtraInfo, Exit) :-
	bottomelement(Exit), !.
fr_exit_to_prime(Sg, Hv, Head, Sv, Exit, _ExtraInfo, Prime) :-
	fr_restriction(Hv, Exit, Beta_prime),
		% above line not needed ?! BUT will be more efficient:
		% subsequent computation with smaller state Beta_prime
	Head =.. [_|Hargs], Sg =.. [_|Sargs],
	fr_call_head_unif(Hargs, Sargs, Beta_prime, Beta_primeSH),
	fr_restriction(Sv, Beta_primeSH, Prime).

%----------------------------------------------------------------------------


% fr_project(_Sg, Vars, _HvFv, Call, Proj) (S)
% projects Call in terms of all variables of the call environment into
% Lamda_p in terms of just the call variables Vars
% Vars : ordered set of variables
%
% :- mode fr_project_(?,?,?,?,o).
fr_project(_Sg,Vars,_HvFv,ASub,Proj) :-
	fr_project_(ASub,Vars,Proj).

fr_project_(Proj, _Vars, Proj):-
	bottomelement(Proj), !.
fr_project_(Call, Vars, Proj):-
	fr_restriction_entry(Vars, Call, Proj).

%----------------------------------------------------------------------------

% SPECIFIC VERSION OF LUB USED AT PROCEDURE EXIT (computes only n-comp)
% fr_compute_lub(LAsub, Lub)
% Lub = as(dummy,ACnlub) with ACnlub = lub(new_comps_of_LAsub)
%
% :- mode fr_compute_lub(?,o).
fr_compute_lub(LAsub, Lub) :-
	get_useful_AS(LAsub, UsefulAS),
	( UsefulAS = [] ->
		bottomelement(Lub)
	;
		fr_lub_uas(UsefulAS, Lub)
	).

% GENERAL VERSION OF LUB TO BE USED FOR ANNOTATION (support3.pl)
% fr_compute_lub_general(LAsub, Lub)
% Lub = lub(LAsub)
%
% :- mode fr_compute_lub_general(?,o).

%% :- export(fr_compute_lub_general/2).
%% fr_compute_lub_general(LAsub, Lub) :-
%% 	get_useful_AS(LAsub, UsefulAS),
%% 	( UsefulAS = [] ->
%% 		bottomelement(Lub)
%% 	;
%% 		fr_lub_uas_general(UsefulAS, Lub)
%% 	).                                                                

%----------------------------------------------------------------------------

% fr_identical_abstract(Asub1,Asub2)	(SF)
% succeeds if Asub1 and Asub2 are identical abstract states
%
% :- mode fr_identical_abstract(?,?).
fr_identical_abstract(Bottom, Bottom):-
	bottomelement(Bottom), !.
fr_identical_abstract(as(ACo1,ACn1), as(ACo2,ACn2)) :-
	ss_identical(ACo1, ACo2),                                        
	ss_identical(ACn1, ACn2).                                          

%----------------------------------------------------------------------------

% fr_sort(Asub1, Asub2).
% Asub1 is sorted into Asub2
%
% :- mode fr_sort(?,o).
fr_sort(Bottom, Bottom):-
	bottomelement(Bottom), !.
fr_sort(as(dummy,ACn), as(dummy, ACn_sort)):-
	% as(ACo,ACn) may be produced by the specific lub -> ACo may be dummy
	!, ss_sort(ACn, ACn_sort).
fr_sort(as(ACo,ACn), as(ACo_sort, ACn_sort)):-
	ss_sort(ACo, ACo_sort),
	ss_sort(ACn, ACn_sort).

%----------------------------------------------------------------------------

% fr_extend(_Sg, Prime, Sv, Call, Succ)
% Prime, Call,Succ : <as>;
% Sv : sorted list of var. iden. occurring in the call of the predicate
% Let Prime be the abstract success state of the call
%	(in terms of the call variables Sv)
% and let Call be the abstract call state of the call
%	(in terms of all the variables in the call environment)
% Then Succ is the abstract success state of the call
%	(in terms of all the variables in the call environment)
%
% :- mode fr_extend(?,?,?,?,o).
fr_extend(_Sg, Prime, _Sv, _Call, Prime):-
	% bottomelement(Call) will not occur, is checked previously
	bottomelement(Prime), !.
fr_extend(_Sg, as(_ACoprime,ACnprime), Sv, Call, Succ) :- 
	fr_join(Call, ACnprime, Sv, Succ).

%----------------------------------------------------------------------------

fr_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

%----------------------------------------------------------------------------

% fr_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ)         
% Proj,Call,Prime,Succ : <as>;
% Prime = (Proj \Aconj (Sg=Head)) projected onto Sv
% Succ = Call \Aconj Primen
%
fr_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,Proj,Prime,Succ) :-
	bottomelement(Proj), !, Prime = Proj, Succ = Proj.
fr_call_to_success_fact(Sg,_Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
	Sg =.. [_|Sargs], Head =.. [_|Hargs],
	fr_call_head_unif(Sargs, Hargs, Proj, PrimeSvHv),
	( bottomelement(PrimeSvHv) ->
		Prime = PrimeSvHv, Succ = Prime
	;
		fr_restriction(Sv, PrimeSvHv, Prime),
		Prime = as(_Primeo,Primen),
		fr_join(Call, Primen, Sv, Succ)
	).

%----------------------------------------------------------------------------

% fr_special_builtin(Sg_key, Sg, _Subgoal, Type, Condvars)
% Determines Type and Condvars based on BuiltinFunctor and Sg
% note: Condvars : if this is a set of variables, then it is ordered
%
% :- mode fr_special_builtin(i,?,?,o,o).
fr_special_builtin('=/2',Sg,_Subgoal,Type,Condvars):-
	Type= '$fd_=', Condvars = Sg .
fr_special_builtin('</2',Sg,_Subgoal,Type,Condvars):- 
	language(clp),!,
	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('</2',Sg,_Subgoal,Type,Condvars):- 
	language(lp),!,
	Type = '$fd_ground', Condvars = Sg . 
%% fr_special_builtin('<=/2',Sg,_Subgoal,Type,Condvars):- 
%% 	language(clp),!,
%% 	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('=</2',Sg,_Subgoal,Type,Condvars):- 
	language(clp),!,
	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('=</2',Sg,_Subgoal,Type,Condvars):- 
	language(lp),!,
	Type = '$fd_ground', Condvars = Sg . 
fr_special_builtin('>/2',Sg,_Subgoal,Type,Condvars):- 
	language(clp),!,
	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('>/2',Sg,_Subgoal,Type,Condvars):- 
	language(lp),!,
	Type = '$fd_ground', Condvars = Sg . 
fr_special_builtin('>=/2',Sg,_Subgoal,Type,Condvars):-  
	language(clp),!,
	Type = '$fd_comp', Condvars = Sg .
fr_special_builtin('>=/2',Sg,_Subgoal,Type,Condvars):-  
	language(lp),!,
	Type = '$fd_ground', Condvars = Sg .
fr_special_builtin('.<./2',Sg,_Subgoal,Type,Condvars):- 
	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('.=<./2',Sg,_Subgoal,Type,Condvars):- 
	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('.>./2',Sg,_Subgoal,Type,Condvars):- 
	Type = '$fd_comp', Condvars = Sg . 
fr_special_builtin('.>=./2',Sg,_Subgoal,Type,Condvars):-  
	Type = '$fd_comp', Condvars = Sg .
fr_special_builtin('#/2',Sg,_Subgoal,Type,Condvars):-
	Type= '$fd_#', Condvars = Sg .	
fr_special_builtin('fail/0',_Sg,_Subgoal,Type,_Condvars):-   
	Type = '$fd_fail' .
fr_special_builtin('true/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).   
fr_special_builtin('!/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).   
fr_special_builtin('nl/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).   
fr_special_builtin('write/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).   
fr_special_builtin('display/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
%%% PrologIII
fr_special_builtin('assign/2',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('bound_mult/3',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_bound_mult', Condvars = Sg.
fr_special_builtin('cpu_time/1',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('enum/1',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('erase/1',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('line/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('min_value/2',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('out/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('outc/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('outl/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('outm/1',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('outml/1',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('recorda/3',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
	% VD : recorda can be improved :
	% error (-> bottom) if X is free in call AC
fr_special_builtin('recorded/3',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('reset_cpu_time/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('val/2',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('$::/2',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_$::', Condvars = Sg.
%%% CLP(R)
fr_special_builtin('ctime/1',Sg,_Subgoal,Type,Condvars):-
	Type = '$fd_ground', Condvars = Sg.
fr_special_builtin('dump/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('inf/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('floor/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('printf/2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('ztime/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
%%% VD added 25/01/95
% general
fr_special_builtin('listing/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('listing/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('repeat/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('seen/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('told/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('read/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('write/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
% in SICStus and PrologIII
fr_special_builtin('atom/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('atomic/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('assert/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('asserta/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('assertz/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('false/0',_Sg,_Subgoal,'$fd_fail',_Condvars).
fr_special_builtin('ground/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('current_op/3',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('integer/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('length/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('=../2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('functor/3',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('debug/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('$metachoice/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('$metacut/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('var/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('nonvar/1',Sg,_Subgoal,'$fd_nonvar',Sg).
fr_special_builtin('writeq/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('name/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('numbervars/3',Sg,_Subgoal,'$fd_ground',Sg).
% SICStus3 (ISO)
fr_special_builtin('=\\=/2',Sg,_Subgoal,'$fd_ground',Sg).
% SICStus2.x
% fr_special_builtin('=\=/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('is/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('statistics/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('tab/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('tab/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('ttynl/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('ttyput/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('get_code/1',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('sort/2',sort(X,Y),_Subgoal,'$fd_=','='(X,Y)).
fr_special_builtin('keysort/2',keysort(X,Y),_Subgoal,'$fd_=','='(X,Y)).
fr_special_builtin('@</2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('@>/2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('@=</2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('@>=/2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
% SICStus3 (ISO)
fr_special_builtin('\\==/2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
% SICStus2.x
% fr_special_builtin('\==/2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('==/2',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('=:=/2',Sg,_Subgoal,'$fd_ground',Sg).
fr_special_builtin('arg/3',Sg,_Subgoal,'$fd_arg',Sg).	% in SICStus and PrologIII
						% but different functionality
% in SICStus and CLP(R)
fr_special_builtin('abort/0',_Sg,_Subgoal,'$fd_fail',_Condvars).
fr_special_builtin('halt/0',_Sg,_Subgoal,'$fd_fail',_Condvars).
fr_special_builtin('assert/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('asserta/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('assertz/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('print/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
% in PrologIII
fr_special_builtin('sys_command/1',Sg,_Subgoal,'$fd_ground',Sg).
% in SICStus
fr_special_builtin('debugging/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('garbage_collect/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('gc/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('nonzero/1',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('$metacut/1',Sg,_Subgoal,'$fd_ground',Sg).   
fr_special_builtin('format/2',format(X,_),_Subgoal,'$fd_ground',f(X)).   
fr_special_builtin('nogc/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('otherwise/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('start_event_trace/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('stop_event_trace/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('ttyflush/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).
fr_special_builtin('ttynl/0',_Sg,_Subgoal,'$fd_unchanged',_Condvars).

%----------------------------------------------------------------------------

% fr_success_builtin(Type, Sv_uns,Condvars,_HvFv_u,Call,Succ).
% Abstract interpretation of builtins
% (note: direct computation, not via projection and extension)
% Type : indicates which kind of special builtin has to be treated
%	currently : '$fd_unchanged', '$fd_fail', '$fd_=', 
%		'$fd_#', '$fd_comp', '$fd_$::', '$fd_ground',
%		'$fd_bound_mult'
% Sv_uns : vars in call of builtin
% Call,Succ :<as>
%
% :- mode fr_success_builtin(i,?,?,?,?,o).

fr_success_builtin(_Type,_Sv_uns,_Condvars,_HvFv_u,Call,Succ) :-
	bottomelement(Call), !, Succ=Call.

fr_success_builtin('$fd_unchanged',_Sv_uns,_Condvars,_HvFv_u,Call,Call).

fr_success_builtin('$fd_fail',_Sv_uns,_Condvars,_HvFv_u,_Call,Bottom):-
	bottomelement(Bottom).

fr_success_builtin('$fd_=',_Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg = '='(L,R),
	fr_success_builtin_eq_noteq(L, R, Call, Succ).

fr_success_builtin('$fd_#',_Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg = '#'(L,R),
	fr_success_builtin_eq_noteq(L, R, Call, Succ).

fr_success_builtin('$fd_comp',_Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg =.. [Comp,L,R],
	fr_success_builtin_compare(Comp, L, R, Call, Succ).

fr_success_builtin('$fd_$::',_Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg = '$::'(L,N),
	( var(L), var(N) ->
		ss_empty(SS1),
		set_create([L,N], S), ss_add_el(S, SS1, SS2),
		ss_add_el([N], SS2, AlfaC),
		fr_join(Call, AlfaC, S, Succ)
	;
	        compiler_error(cons_lists),
		bottomelement(Succ) 
	).

fr_success_builtin('$fd_ground',Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg =.. [P | Args],
	fr_success_builtin_ground(P,Args,Sv_uns,Call,
					Succ).
                                                                      
fr_success_builtin('$fd_bound_mult',_Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg =.. [_ | Args],
	Args = [A1, A2, A3],
	( numerical(A1), numerical(A2), numerical(A3),
	  ( fr_ground_arg(A1, Call) ; fr_ground_arg(A2, Call) ) ->
		fr_abstract_full_numcs('=', A1*A2, A3, Call, Succ)
	;
		bottomelement(Succ)
	).                   

fr_success_builtin('$fd_nonvar',_Sv_uns,nonvar(X),_HvFv_u,Call,Succ):-
	fr_nonfree_arg(X,Call),!,
	Succ = Call.
fr_success_builtin('$fd_nonvar',_Sv_uns,_Sg,_HvFv_u,_Call,Succ):-
	bottomelement(Succ).


fr_success_builtin('$fd_arg',_Sv_uns,Sg,_HvFv_u,Call,Succ):-
	Sg =.. [_,A1,A2,A3],
	( numerical(A1), fr_ground_arg(A1, Call) ->
	  ( language(lp) -> % In SICStus A2 must be a compound ter
	    ( fr_nonfree_arg(A2,Call) ->
		( var(A2) ->
			get_vars(A3, Sh),
			set_add_el(A2, Sh, S),
			ss_make_singl(S, AlfaC),
			% [] should be added to AlfaC if pos fail is represented
			% because the value of A1 may cause failure
			fr_join(Call, AlfaC, S, Succ)
		;
		        compiler_error(arg_not_normal),
			bottomelement(F_succ)
		)
	    ; bottomelement(Succ)
	    )
	  ;   ( var(A2) ->
                        get_vars(A3, Sh),
                        set_add_el(A2, Sh, S),
                        ss_make_singl(S, AlfaC),
                        % [] should be added to AlfaC if pos fail is represented
                        % because the value of A1 may cause failure
                        fr_join(Call, AlfaC, S, Succ)
                ;
		        compiler_error(arg_not_normal),
			bottomelement(F_succ)
                )
	  )  
	;
		bottomelement(Succ)
	).

%----------------------------------------------------------------------------

% fr_lambda_to_success_builtin(Sg_key,_Sg,_Sv,_Call,_Proj,_Prime,_Succ) :-
% 	compiler_error(not_implemented(fr,Sg_key)).
	
%----------------------------------------------------------------------------

%fail: fr_output_interface('$bottom',_Qv,'$bottom').
fr_output_interface(as(ACo,ACn), Qv, Succ) :-
	!,
%% to see old and new separately
%	Asub_external = [ACo,ACn].
%% joined old and new
	ss_union(ACo, ACn, ACt),
	ss_minimise(ACt,Free_dep),
	sort(Qv,Qv_s),
	get_free_vars(Qv_s,Free_dep,Fv),
	if_not_nil(Fv,free(Fv),Succ,Succ0),
	if_not_nil(Free_dep,posdeps(Free_dep),Succ0,[]).

get_free_vars([],_,[]).
get_free_vars([X|Xs],ACtmin,F):-
	ss_is_in([X],ACtmin), !,
	get_free_vars(Xs,ACtmin,F).
get_free_vars([X|Xs],ACtmin,[X|F]):-
	get_free_vars(Xs,ACtmin,F).

if_not_nil([],_,Xs,Xs):- !.
if_not_nil(_,X,[X|Xs],Xs).

%----------------------------------------------------------------------------

fr_asub_to_native(ASub,Qv,_OutFlag,OutputUser,[]) :- fr_output_interface(ASub,Qv,OutputUser).

%----------------------------------------------------------------------------

% fr_unknown_call(_Sg,Vars,Call,Succ)
% Gives the "top" value (mode any) for the variables Vars involved in
% a literal whose definition is not present, and joins this top abstraction
% with Call yielding Succ
% Is used for metacalls
% req: Vars is ordered 
%
fr_unknown_call(_Sg,_Vars,Call,Call):-
	bottomelement(Call), !.
fr_unknown_call(_Sg,Vars,Call,Succ) :-
	ss_make_singl(Vars, AlfaC),
	fr_join(Call, AlfaC, Vars, Succ).

%----------------------------------------------------------------------------

% fr_unknown_entry(_Sg,Vars,Call)
% Gives the "top" value (mode any) for the variables Vars,
% resulting in the abstract constraint Call
% req: Vars is ordered 
%
fr_unknown_entry(_Sg, Vars, as(ACo,ACn)) :-
%	ss_make_singl(Vars, ACo), ss_empty(ACn). replaced by  16/01/95
%	what is used for query is Call-info, not projected info !
	ss_empty(ACo), ss_make_singl(Vars, ACn).

fr_empty_entry(_,_,_):-
	throw(not_implemented(fr_empty_entry)).

%----------------------------------------------------------------------------

% fr_less_or_equal(Asub1,Asub2)	(SF)
% succeeds if Asub1 =< Asub2
%
% :- mode fr_less_or_equal(?,?).
fr_less_or_equal(Bottom, Bottom):-
	bottomelement(Bottom), !.
fr_less_or_equal(as(ACo1,ACn1), as(ACo2,ACn2)) :-
	ss_close(ACo2, ACo2Cl),
	ss_is_subset(ACo1, ACo2Cl),
	ss_close(ACn2, ACn2Cl),
	ss_is_subset(ACn1, ACn2Cl).

%% %----------------------------------------------------------------------------
%% 
%% % fr_qmode_info(Info,Call)
%% % Given the query pattern Info, computes the Call
%% %
%% % :- mode fr_qmode_info(i,o).
%% fr_qmode_info(Info,Call) :-
%% 	fr_nfmodes(Info,[],Lnfvars),
%% %	ss_make_singl(Lnfvars,ACo), ss_empty(ACn), replaced by  16/01/95
%% %	what is used for query is Call-info, not projected info !
%% 	ss_empty(ACo), ss_make_singl(Lnfvars,ACn),
%% 	Call = as(ACo,ACn).
%%

%% fr_nfmodes([],Lnfvars,Lnfvars).
%% fr_nfmodes([mode(_Varident,f)|Info],LnfvarsAcc,Lnfvars) :-!,
%% 	fr_nfmodes(Info,LnfvarsAcc, Lnfvars).
%% fr_nfmodes([mode(Varident,_)|Info],LnfvarsAcc,Lnfvars) :-
%% 	set_add_el(Varident,LnfvarsAcc,LnfvarsNewAcc),
%% 	fr_nfmodes(Info,LnfvarsNewAcc,Lnfvars).

%----------------------------------------------------------------------------
% Maria Garcia de la Banda May-1995
% Similar to the one above but with Info with the form free(ListFreeVars)
% instead of [mode(X,f),mode(Y,g),..] etc

fr_input_user_interface(FreeVars,Vars,Call,_Sg,_MaybeCallASub):-
	may_be_var(FreeVars),
	ord_subtract(Vars,FreeVars,NonFreeVars),
	ss_empty(ACo), 
	ss_make_singl(NonFreeVars,ACn),
	Call = as(ACo,ACn).

fr_input_interface(free(V),perfect,Fv0,Fv):-
	var(V),
	myinsert(Fv0,V,Fv).

myinsert(Fr0,X,Fr):-
	var(Fr0), !,
	Fr = [X].
myinsert(Fr0,X,Fr):-
	insert(Fr0,X,Fr).

may_be_var(X):- ( X=[] ; true ), !.

%----------------------------------------------------------------------------

% fr_reverse(AS,ASrev)
% interchanges the old and new components in the abstraction
% note : not(bottomelement(AS))
%
% :- mode fr_reverse(i,o).
%% fr_reverse(as(ACo,ACn),as(ACn,ACo)).
