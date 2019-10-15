:- module(depthk,
	[ depthk_call_to_entry/9, 
	  depthk_call_to_success_builtin/6, 
	  depthk_call_to_success_fact/9,
	  depthk_compute_lub/2,
	  depthk_glb/3,
	  depthk_eliminate_equivalent/2,
	  depthk_abs_subset/2,
	  depthk_exit_to_prime/7,
	  depthk_extend/4,    
	  depthk_identical_abstract/2, 
	  depthk_input_user_interface/5,
	  depthk_input_interface/4,
	  depthk_less_or_equal/2,  
	  depthk_asub_to_native/5, 
	  depthk_project/3,   
	  depthk_abs_sort/2,      
	  depthk_special_builtin/5,  
	  depthk_success_builtin/5,
	  depthk_unknown_call/4, 
	  depthk_unknown_entry/3,  
	  depthk_empty_entry/3
        ],
	[ assertions ] ).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(domain(s_eqs), 
	[ apply/1, eqs_ranges/6, keys_and_values/3, peel/4, subtract_keys/3 ]).
:- use_module(library(lists), [member/2]).
:- use_module(library(sets), 
	[ insert/3, merge/3, ord_member/2, ord_subset/2, ord_subtract/3 ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), 
	[ instance/2, 
	  most_specific_generalization/3, 
	  most_general_instance/3,
	  variant/2
	]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(io_basic)).
:- use_module(library(write), [numbervars/3]).

depth_k(K):- current_pp_flag(depth,K).

% -------------------------------------------------------------------------
%
% Programmer: Francisco Bueno
% Date:       February 1, 1995
%
% -------------------------------------------------------------------------
% MODULE: "depthk": the depth-k domain 
% -----------------------------------------------------------------------
% substitutions are (sorted) lists of unification equations - X=term
% memo lists of substitutions not singletons (lub as disjunction)
% lub as disjunction selected with a flag - real lub not yet implemented!
% -----------------------------------------------------------------------+

:- doc(bug,"tried to keep ""project"" reasonable but it seems wrong!").

% -----------------------------------------------------------------------

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% depthk_call_to_entry(+,+,+,+,+,+,+,-,-)                                %
% depthk_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)          %
%------------------------------------------------------------------------%

depthk_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
	variant(Sg,Head),!,
	Flag = yes,
	copy_term((Sg,Proj),(NewTerm,NewProj_u)),
	Head = NewTerm,
	depthk_abs_sort(NewProj_u,NewProj),
	variables_are_variables(Fv,Free),
	merge(Free,NewProj,Entry).
depthk_call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
	variables_are_variables(Fv,Entry).
depthk_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,Unifiers):-
	peel(Head,Sg,Unifiers,[]),
	depthk_unify(Unifiers,Proj,Entry0), !,
	depthk_bu_project(Entry0,Hv,Entry1),
	depthk_abs_sort(Entry1,Entry2),
	variables_are_variables(Fv,Tmp),
	merge(Tmp,Entry2,Entry).
depthk_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

variables_are_variables([V|Fv],[V=_|ASub]):-
	variables_are_variables(Fv,ASub).
variables_are_variables([],[]).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% depthk_exit_to_prime(+,+,+,+,+,-,-)                                    %
% depthk_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)               %
% It computes the prime abstract substitution Prime, i.e.  the result of %
% going from the abstract substitution over the head variables (Exit), to%
% the abstract substitution over the variables in the subgoal. It will:  %
% * If Exit is '$bottom', Prime will be also '$bottom'.                  %
% * If Flag = yes (Head and Sg identical up to renaming) it is just a    %
%   question of renaming Exit                                            %
% * If Hv = [], Prime = []                                               %
% * Otherwise:                                                           %
%      * apply abstract unification with the original equations from     % 
%        the head unification                                            %
%      * then project (closing) over Sv obtaining Prime                  %
%------------------------------------------------------------------------%

depthk_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
	Prime = '$bottom'.
depthk_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
	depthk_project(Hv,Exit,BPrime),
	copy_term((Head,BPrime),(NewTerm,NewPrime)),
	Sg = NewTerm,
	depthk_abs_sort(NewPrime,Prime).	
depthk_exit_to_prime(_Sg,[],_Head,_Sv,_Exit,_ExtraInfo,Prime):- !,
	Prime = [].
depthk_exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,Unifiers,Prime):-
	depthk_unify(Unifiers,Exit,Prime0),
	depthk_bu_project(Prime0,Sv,Prime1),
	depthk_abs_sort(Prime1,Prime).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT Extend
%-------------------------------------------------------------------------
%------------------------------------------------------------------------%
% depthk_extend(+,+,+,-)                                                 %
% depthk_extend(Prime,Sv,Call,Succ)                                      %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ. Otherwise,  %
% just add to Prime equs. for variables in Call and not in Prime.        %
%------------------------------------------------------------------------%

depthk_extend('$bottom',_Sv,_Call,Succ):- !,
	Succ = '$bottom'.
depthk_extend(_Prime,[],Call,Succ):- !,
	Call = Succ.
depthk_extend(Prime,Sv,Call,Succ):-
	variables_are_variables(Cv,Call),
	ord_subtract(Cv,Sv,Nv),
	depthk_project(Nv,Call,Succ0),
	merge(Succ0,Prime,Succ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% depthk_project(+,+,-)                                                  %
% depthk_project(Vars,ASub,Proj)                                         %
% Leave in Proj only equs. related to Vars                               %
%------------------------------------------------------------------------%

depthk_project(_,'$bottom',Proj):- !,
	Proj = '$bottom'.
depthk_project([],_ASub,[]):- !.
depthk_project(Vars,ASub,Proj):-
	discriminate_equs(ASub,Vars,Proj,_,_).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                      ABSTRACT SORT
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% depthk_abs_sort(+,-)                                                       %
% depthk_abs_sort(Asub_u,Asub)                                               %
% Sorts the list of equs.                                                %
%-------------------------------------------------------------------------

depthk_abs_sort('$bottom','$bottom'):- !.
depthk_abs_sort(ASub_u,ASub):-
	sort(ASub_u,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT LUB                                      %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%-------------------------------------------------------------------------
% depthk_compute_lub(+,-)                                                %
% depthk_compute_lub(ListASub,Lub)                                       %
%-------------------------------------------------------------------------

depthk_compute_lub([ASub],Lub):- !,
	Lub = ASub.
depthk_compute_lub([ASub1,ASub2|ListASub],Lub):-
	compute_lub(ASub1,ASub2,Lub0),
	depthk_compute_lub([Lub0|ListASub],Lub).

compute_lub('$bottom',ASub,Lub):- !, Lub = ASub.
compute_lub(ASub,'$bottom',Lub):- !, Lub = ASub.
compute_lub(ASub1,ASub2,Lub):-
	lub_each_eq(ASub1,ASub2,Lub).

lub_each_eq([],[],[]).
lub_each_eq([X=T1|ASub1],[X=T2|ASub2],[X=T|Lub]):-
	most_specific_generalization(T1,T2,T),
	lub_each_eq(ASub1,ASub2,Lub).

%-------------------------------------------------------------------------
% depthk_glb(+,-)                                                        %
% depthk_glb(ASub1,ASub2)                                                %
%-------------------------------------------------------------------------

depthk_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
depthk_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
depthk_glb(ASub1,ASub2,Glb):-
	glb_each_eq(ASub1,ASub2,Glb).

glb_each_eq([],[],[]).
glb_each_eq([X=T1|ASub1],[X=T2|ASub2],[X=T|Lub]):-
	most_general_instance(T1,T2,T),
	glb_each_eq(ASub1,ASub2,Lub).

%------------------------------------------------------------------------%

:- use_module(ciaopp(plai/domains), [absub_eliminate_equivalent/3]).

depthk_eliminate_equivalent(TmpLSucc,LSucc) :- absub_eliminate_equivalent(TmpLSucc,depthk,LSucc).

%------------------------------------------------------------------------%

depthk_abs_subset(LASub1,LASub2) :- absub_is_subset(LASub1,LASub2), !. % TODO: added cut (absub_is_subset/2 leaves choicepoints)

% TODO: leaves choicepoints!
absub_is_subset([],_LASub2).
absub_is_subset([Sub1|Subs1],LASub2) :-
	member(ASub2,LASub2),
	depthk_identical_abstract(Sub1,ASub2),
% OR:
%	absub_fixpoint_covered(depthk,Sub1,ASub2),
	absub_is_subset(Subs1,LASub2).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%-------------------------------------------------------------------------

depthk_call_to_success_fact(Sg,_Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
	peel(Head,Sg,Unifiers,[]),
	depthk_unify(Unifiers,Proj,Entry0), !,
	depthk_bu_project(Entry0,Sv,Prime1),
	depthk_abs_sort(Prime1,Prime),
	depthk_extend(Prime,Sv,Call,Succ).
depthk_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%------------------------------------------------------------------------%
% depthk_identical_abstract(+,+)                                         %
% depthk_identical_abstract(ASub1,ASub2)                                 %
% Succeeds if abstract substitutions ASub1 and ASub2 are defined on the  %
% same variables and are equivalent                                      %
%------------------------------------------------------------------------%

%% care with top variables, which can be shared between the two substs.!!

depthk_identical_abstract(ASub1,ASub2):-
	variables_are_variables(V1,ASub1),
	\+ \+ (
	numbervars(V1,0,M),
	copy_term(ASub1,T1),
	copy_term(ASub2,T2),
	numbervars(T1,M,N),
	numbervars(T2,M,N),
	T1==T2 ).

%------------------------------------------------------------------------%
% depthk_less_or_equal(+,+)                                              %
% depthk_less_or_equal(ASub0,ASub1)                                      %
%------------------------------------------------------------------------%

depthk_less_or_equal('$bottom',_).
depthk_less_or_equal(ASub0,ASub1):-
	less_or_equal(ASub0,ASub1).

less_or_equal([],[]).
less_or_equal([X=T1|ASub1],[X=T2|ASub2]):-
	instance(T1,T2),
	less_or_equal(ASub1,ASub2).

%-------------------------------------------------------------------------
% depthk_unknown_call(+,+,+,-)                                           |
% depthk_unknown_call(Sg,Qv,Call,Succ)                                   |
%-------------------------------------------------------------------------

depthk_unknown_call(_Sg,Qv,Call,Succ):-
	subtract_keys(Call,Qv,Succ0),
	variables_are_variables(Qv,Succ1),
	merge(Succ0,Succ1,Succ).

%-------------------------------------------------------------------------
% depthk_unknown_entry(+,+,-)                                            |
% depthk_unknown_entry(Sg,Qv,Call)                                       |
%-------------------------------------------------------------------------

depthk_unknown_entry(_Sg,Qv,Call):-
	variables_are_variables(Qv,Call).

depthk_empty_entry(Sg,Qv,Call):-
	depthk_unknown_entry(Sg,Qv,Call).

%-------------------------------------------------------------------------
%                      USER INTERFACE
%-------------------------------------------------------------------------

%------------------------------------------------------------------------%
% depthk_input_user_interface(+,+,-,+,+)                                 %
% depthk_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)        %
% Obtaining the abstract substitution for Depthk from the user supplied  %
% information                                                            %
%------------------------------------------------------------------------%

depthk_input_user_interface(Info,Qv,Call,_Sg,_MaybeCallASub):-
	may_be_var(Info),
	sort(Info,Eqs),
	eqs_ranges(Qv,Eqs,Terms,_Vars,[],_AVarSet),
	keys_and_values(Qv,Terms,AEqs),
	depth_k(K),
	check_equs(AEqs,K,[],Call).

depthk_input_interface(instance(X,T),perfect,Eqs0,Eqs):-
	var(X),
	myappend(Eqs0,X=T,Eqs).

myappend(Vs0,V,Vs):-
	var(Vs0), !,
	Vs=[V].
myappend(Vs,V,[V|Vs]).

may_be_var(X):- ( X=[] ; true ), !.

%-------------------------------------------------------------------------
% depthk_asub_to_native(+,+,+,-,-)
% depthk_asub_to_native(ASub,Qv,OutFlag,Info,Comps)
%-------------------------------------------------------------------------

depthk_asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :-
	depthk_asub_to_native_(ASub,OutputUser).

depthk_asub_to_native_([],[]).
depthk_asub_to_native_([X=T|ASub],Info):-
	accumulate(X,T,Info0,Info),
	depthk_asub_to_native_(ASub,Info0).

accumulate(_,T,Info0,Info):-
	var(T), !,
	Info=Info0.
accumulate(X,T,Info,[instance(X,T)|Info]).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

depthk_special_builtin('!/0',(!),_,nochange,[]).
% SICStus3 (ISO)
depthk_special_builtin('=\\=/2',(_ =\= _),_,nochange,[]).
% SICStus2.x
% depthk_special_builtin('=\=/2',(_ =\= _),_,nochange,[]).
depthk_special_builtin('=<'/2,'=<'(_,_),_,nochange,[]).
depthk_special_builtin('@=<'/2,'@=<'(_,_),_,nochange,[]).
depthk_special_builtin('@>'/2,'@>'(_,_),_,nochange,[]).
depthk_special_builtin('@>='/2,'@>='(_,_),_,nochange,[]).
depthk_special_builtin('@<'/2,'@<'(_,_),_,nochange,[]).
depthk_special_builtin('>'/2,'>'(_,_),_,nochange,[]).
depthk_special_builtin('>='/2,'>='(_,_),_,nochange,[]).
% SICStus3 (ISO)
depthk_special_builtin('\\==/2',(_ \== _),_,nochange,[]).
% SICStus2.x
% depthk_special_builtin('\==/2',(_ \== _),_,nochange,[]).
depthk_special_builtin('<'/2,'<'(_,_),_,nochange,[]).
depthk_special_builtin('$metachoice'/1,'$metachoice'(_),_,nochange,[]).
depthk_special_builtin('$metacut'/1,'$metacut'(_),_,nochange,[]).
%depthk_special_builtin('arg/3',arg(_,_,_),_,nochange,[]).
depthk_special_builtin('atom/2',atom(_),_,nochange,[]).
depthk_special_builtin('atomic/2',atomic(_),_,nochange,[]).
depthk_special_builtin('format/2',format(_,_),_,nochange,[]).
depthk_special_builtin('format/3',format(_,_,_),_,nochange,[]).
%depthk_special_builtin('functor/3',functor(_,_,_),_,nochange,[]).
depthk_special_builtin('ground/1',ground(_),_,nochange,[]).
depthk_special_builtin('integer/1',integer(_),_,nochange,[]).
depthk_special_builtin('instance/2',instance(X,Y),_,instance,(X,Y)).
depthk_special_builtin('is/2',is(_,_),_,nochange,[]).
depthk_special_builtin('length/2',length(_,_),_,nochange,[]).
depthk_special_builtin('nl/1',nl(_),_,nochange,[]).
depthk_special_builtin('nonvar/1',nonvar(_),_,nochange,[]).
depthk_special_builtin('number/1',number(_),_,nochange,[]).
depthk_special_builtin('statistics/2',statistics(_,_),_,nochange,[]).
depthk_special_builtin('var/1',var(_),_,nochange,[]).
depthk_special_builtin('write/1',write(_),_,nochange,[]).      
depthk_special_builtin('write/2',write(_,_),_,nochange,[]).
depthk_special_builtin('write_canonical/1',write_canonical(_),_,nochange,[]).
depthk_special_builtin('write_canonical/2',write_canonical(_,_),_,nochange,[]).
depthk_special_builtin('writeq/1',writeq(_),_,nochange,[]).
depthk_special_builtin('writeq/2',writeq(_,_),_,nochange,[]).
depthk_special_builtin(_Key,Builtin,_,nochange,[]):- functor(Builtin,_,0).
depthk_special_builtin(Key,_Builtin,_,special(Key),[]):- 
	very_special_builtin(Key).

very_special_builtin('=../2').
very_special_builtin('arg/3').
very_special_builtin('functor/3').
very_special_builtin('is/2').
very_special_builtin('name/2').

depthk_success_builtin(nochange,_Sv_uns,[],Call,Call).
depthk_success_builtin(instance,_Sv_uns,(X,Y),Call,Succ):-
	var(X), !,
	discriminate_equs(Call,[X],[X=T],NonRelated,_Renamings),
	( most_general_instance(T,Y,NewT)
	-> merge_eqs([X=NewT],NonRelated,Succ)
	 ; Succ='$bottom'
	).
depthk_success_builtin(instance,_Sv_uns,_Args,Call,Call).

depthk_call_to_success_builtin(_SgKey,Sg,Sv,Call,_Proj,Succ):-
	depthk_call_to_prime_builtin(Sg,Sv,Call,Prime0),
	varset(Prime0,Vars),
	ord_subtract(Sv,Vars,Vars0),
	depthk_project(Vars0,Call,Prime1),
	merge_eqs(Prime0,Prime1,Prime),
	depthk_extend(Prime,Sv,Call,Succ), !.
depthk_call_to_success_builtin(_SgKey,_Sg,_Sv,_Call,_Proj,'$bottom').

depthk_call_to_prime_builtin(Sg,Sv,Call,Prime):-
	execute_builtin(Sg,Call,Eqs), !,
	depthk_bu_unify(Eqs,Sv,[],Prime).
depthk_call_to_prime_builtin(Sg,Sv,_Call,Prime):-
	depthk_abstract_builtin(Sg,Sv,Prime).

execute_builtin(Sg,Call,Eqs):-
	build_call(Sg,Call,Goal,Eqs),

% RH:   replace catch by intercept because intercept does 
%       not handle anymore exceptions 
%	intercept(Goal,_Any,fail).
	catch(Goal,_Any,fail).

%	on_exception(_,call(Goal),fail).

build_call('=..'(X,Y),Call,'=..'(A,Y0),[X=A]):-
	build_a_copy(Y,Call,Y0).
build_call(is(X,Y),Call,'=..'(A,Y0),[X=A]):-
	build_a_copy(Y,Call,Y0).
build_call(name(X,Y),Call,name(X0,A),[Y=A]):-
	build_a_copy(X,Call,X0).
build_call(name(X,Y),Call,name(A,Y0),[X=A]):-
	build_a_copy(Y,Call,Y0).
build_call(functor(X,Y,Z),Call,functor(A,Y0,Z0),[X=A]):-
	build_a_copy(t(Y,Z),Call,t(Y0,Z0)).
build_call(functor(X,Y,Z),Call,functor(X0,A,B),[Y=A,Z=B]):-
	build_a_copy(X,Call,X0).
build_call(arg(X,Y,Z),Call,arg(A,Y0,B),[X=A,Z=B]):-
	build_a_copy(Y,Call,Y0).
build_call(arg(X,Y,Z),Call,arg(X0,A,Z0),[Y=A]):-
	build_a_copy(t(X,Z),Call,t(X0,Z0)).
build_call(arg(X,Y,Z),Call,arg(X0,Y0,Z0),[]):-
	build_a_copy(t(X,Y,Z),Call,t(X0,Y0,Z0)).

% copy the call but respect the variables in Y
build_a_copy(Y,Call,Y0):-
	copy_term(Y,Y0),
	varset(Y,YVars),
	varset(Y0,YVars0),
	depthk_project(YVars,Call,ProjY),
	rename_domain(YVars,YVars0,ProjY,ProjY0),
	apply(ProjY0).

rename_domain([Y|Ys],[Y0|Y0s],[Y=A|ProjY],[Y0=A|ProjY0]):-
	rename_domain(Ys,Y0s,ProjY,ProjY0).
rename_domain([],[],[],[]).

%------------------------------------------------------------------------%
%		          BOTTOM-UP FUNCTIONS                            %
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------

%% having an entry per literal makes the abstraction of a literal void 
%%  (i.e. top! - nothing is known for the variables in the literal)

% depthk_abstract(_Literal,[]).

%-------------------------------------------------------------------------

depthk_bu_unify(Eqs,Vars,Proj,ASub):-
	unify_eqs(Eqs,Unifiers),
	depthk_unify(Unifiers,Proj,ASub0),
	depthk_project(Vars,ASub0,ASub).

unify_eqs([X=Y|Eqs],Unifiers):-
	peel(X,Y,Unifiers,Tail),
	unify_eqs(Eqs,Tail).
unify_eqs([],[]).

%% to unify, merge all unification equations and leave only one for each var

depthk_unify(Unifiers,I,NewI):-
	sort(Unifiers,SUnifiers),
	merge(SUnifiers,I,MUnifiers),
	simplify_equalities(MUnifiers,NewI).

:- push_prolog_flag(multi_arity_warnings,off).

simplify_equalities([],[]).
simplify_equalities([U],[U]):- !.
simplify_equalities([X=Y|Unifiers],SUnifiers):-
	simplify_equalities(Unifiers,X,Y,SiUnifiers,NewUnifiers,no,F),
	simplify_rares(NewUnifiers,[X=Y|Unifiers],[],GoodUnifiers),
	merge(SiUnifiers,GoodUnifiers,AllUnifiers),
	simplify_equalities(F,AllUnifiers,SUnifiers).

simplify_equalities(no,Unifiers,Unifiers).
simplify_equalities(yes,Unifiers,SUnifiers):-
	simplify_equalities(Unifiers,SUnifiers).

simplify_equalities([],X,Y,[X=Y],[],F,F).
simplify_equalities([U|Unifiers],V,R,SUnifiers,EUnifiers,_,yes):-
	U=(X=Y), X==V, !,
	peel(R,Y,EUnifiers,MoreUnifiers),
	simplify_equalities(Unifiers,V,R,SUnifiers,MoreUnifiers,_,_).
simplify_equalities([V=R|Unifiers],X,Y,[X=Y|SUnifiers],EUnifiers,F0,F):-
	simplify_equalities(Unifiers,V,R,SUnifiers,EUnifiers,F0,F).

:- pop_prolog_flag(multi_arity_warnings).

simplify_rares([],_,GoodUnifiers,GoodUnifiers).
simplify_rares([X=Y|Unifiers],Check,TmpUnifiers,GoodUnifiers):-
	X==Y, !,
	simplify_rares(Unifiers,Check,TmpUnifiers,GoodUnifiers).
simplify_rares([U|Unifiers],Check,TmpUnifiers,GoodUnifiers):-
	ord_member(U,Check), !,
	simplify_rares(Unifiers,Check,TmpUnifiers,GoodUnifiers).
simplify_rares([U|Unifiers],Check,TmpUnifiers,GoodUnifiers):-
	insert(TmpUnifiers,U,MoreUnifiers),
	simplify_rares(Unifiers,Check,MoreUnifiers,GoodUnifiers).

%=========================

%% simetric_renamings([],[]).
%% simetric_renamings([X=Y|AUnifiers],[X=Y,Y=X|SUnifiers]):- var(Y), !,
%% 	simetric_renamings(AUnifiers,SUnifiers).
%% simetric_renamings([X=Y|AUnifiers],[X=Y|SUnifiers]):-
%% 	simetric_renamings(AUnifiers,SUnifiers).

:- push_prolog_flag(multi_arity_warnings,off).

merge_eqs([], Set2, Set2):- !.
merge_eqs(Set1, [], Set1).
merge_eqs([Head1|Tail1], [Head2|Tail2], Union):-
	Head1=(X=_), Head2=(Y=_),
	compare(Order,X,Y),
	merge_eqs(Order,Head1,Tail1,Head2,Tail2,Union).

%% if they are for the same variable, they must unify:

merge_eqs(<,Head0,[],Head2,Tail2,[Head0,Head2|Tail2]).
merge_eqs(<,Head0,[Head1|Tail1],Head2,Tail2,[Head0|Union]):-
	Head1=(X=_), Head2=(Y=_),
	compare(Order,X,Y),
	merge_eqs(Order,Head1,Tail1,Head2,Tail2,Union).
merge_eqs(=,Head,Tail1,X=Y,Tail2,[Head|Union]):- 
	Head=(X=Y),                                 %% NO SE PUEDE UNIFICAR!
	merge_eqs(Tail1,Tail2,Union).
merge_eqs(>,Head1,Tail1,Head0,[],[Head0,Head1|Tail1]).
merge_eqs(>,Head1,Tail1,Head0,[Head2|Tail2],[Head0|Union]):-
	Head1=(X=_), Head2=(Y=_),
	compare(Order,X,Y),
	merge_eqs(Order,Head1,Tail1,Head2,Tail2,Union).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------

%% %% merge the lists (taking care of special case "bottom") and check they
%% %%  are consistent
%% %% we don't take care of related variables (in "unifiers") until 
%% %%  after unify/3 and in project/3
%% 
%% depthk_conjunction('$bottom','$bottom','$bottom'):- !.
%% depthk_conjunction('$bottom',I,I):- !.
%% depthk_conjunction(I,'$bottom',I):- !.
%% depthk_conjunction(I1,I2,I):-
%% %%	merge_eqs(I1,I2,I).
%% %%	depthk_unify(I1,I2,I).
%% 	append(I1,I2,I).
%% 
%% %% have to unify here because it is not done in "tp" after "retrieve"
%% %% ojo que en "dep" no hace falta porque el "unify" no hace nada
%% %% que tenga que ver con cierres transitivos...
%% 
%% %-------------------------------------------------------------------------
%% 
%% %% depthk_lub(yes,Is,I1,I):-
%% %% 	depthk_lub(Is,I1,I).     %% NOT IMPLEMENTED YET
%% depthk_lub(yes,Is,I1,I):-
%% 	depthk_lub_disjunctive(Is,I1,I).
%% depthk_lub(no,Is,I1,I):-
%% 	depthk_lub_disjunctive(Is,I1,I).
%% 
%% %% lub a list of substs. and a single subst 
%% %%   check if subst. belongs to the list, if not add it:
%% %%   each subst. refers to each and all of the variables involved (sorted)
%% %%   but it may have "free" variables (the end of the K-depth)
%% 
%% depthk_lub_disjunctive(Is,I,Is):-
%%  	\+ \+ (
%%  	numbervars(I,0,N),
%% 	member(I0,Is),
%%  	numbervars(I0,0,N),
%%  	I == I0
%%  	), !.
%% depthk_lub_disjunctive(Is,I,[I|Is]).

%-------------------------------------------------------------------------

%% project to variables in Literal (Vars)
%%  close equations w.r.t. variables not in Literal, then
%%  keep the equations for variables in Literal and forget the rest
%%  also check depth of equations to K

depthk_bu_project(I,Vars,Projected):-
	depth_k(K),
	project_loop(I,Vars,NewI),
	equs_for_all_vars(Vars,NewI,Closed),
	check_equs(Closed,K,Vars,Projected).

%% having simplified in "unify" we have here that \forall X \exists! X=Y \in I
%%  we add things to Related so we have to simplify again (one pass only)
%%  we don't add to Renamings, so we have only one eq per var
%%  NonRelated can be executed! -> Not in top-down!!

project_loop(Eqs,Vars,Projected):-
	discriminate_equs(Eqs,Vars,Related,NonRelated,Renamings),
%	get_rid_of_void_equs(NonRelated),
	substitute_equs(NonRelated,Related,Related0),
	substitute_equs(Renamings,Related0,NewRelated),
	sort(NewRelated,SoRelated),
	simplify_equalities(SoRelated,SRelated),
	project_loop0(NewRelated,SRelated,Vars,Projected).

project_loop0(NewRelated,SRelated,_Vars,Projected):-
	compatible(NewRelated,SRelated,CRelated), !,
	Projected=CRelated.
project_loop0(_NewRelated,SRelated,Vars,Projected):-
	project_loop(SRelated,Vars,Projected).

compatible(X,Y,X):- X==Y.

%% having simplified in "unify" we have here that \forall X=Y \in I either:
%% (R)   X \in Vars and vars(Y) \in Vars
%% (R)   X \in Vars and \forall Z \in vars(Y), Z \notin Vars
%% (S'o) X \notin Vars and vars(Y) \in Vars
%% (RN)   (special case vars(Y)={Y})
%% (NSo) X \notin Vars and \forall Z \in vars(Y), Z \notin Vars

discriminate_equs([],_,[],[],[]).
discriminate_equs([E|Eqs],Vars,Related,NonRelated,Renamings):-
	E=(X=_),
	ord_member(X,Vars), !,
	Related=[E|More],
	discriminate_equs(Eqs,Vars,More,NonRelated,Renamings).
discriminate_equs([X=Y|Eqs],Vars,Related,NonRelated,Renamings):-
	discriminate_equs0(X,Y,Eqs,Vars,Related,NonRelated,Renamings).

discriminate_equs0(X,Y,Eqs,Vars,Related,NonRelated,Renamings):-
	var(Y),
	ord_member(Y,Vars), !,
	Related=[Y=X|More],
	discriminate_equs(Eqs,Vars,More,NonRelated,Renamings).
discriminate_equs0(X,Y,Eqs,Vars,Related,NonRelated,Renamings):-
	varset(Y,YVars),
	ord_subset(YVars,Vars), !,
	Renamings=[X=Y|More],
	discriminate_equs(Eqs,Vars,Related,NonRelated,More).
discriminate_equs0(X,Y,Eqs,Vars,Related,[X=Y|NonRelated],Renamings):-
	discriminate_equs(Eqs,Vars,Related,NonRelated,Renamings).

%% get_rid_of_void_equs([]).
%% get_rid_of_void_equs([X=Y|Eqs]):-
%% 	X=Y,
%% 	get_rid_of_void_equs(Eqs).

%% get_rid_of_void_equs([],_,[]).
%% get_rid_of_void_equs([X=Y|Eqs],Vars,NEqs):-
%% 	\+ ( ord_member(X,Vars) ),
%% 	varset(Y,YVars),
%% 	ord_intersection(YVars,Vars,[]), !,
%% 	X=Y,
%% 	get_rid_of_void_equs(Eqs,Vars,NEqs).
%% get_rid_of_void_equs([E|Eqs],Vars,[E|NEqs]):-
%% 	get_rid_of_void_equs(Eqs,Vars,NEqs).

equs_for_all_vars([],[],[]).
equs_for_all_vars([V|Vs],[E|Es],Related):-
	E=(X=_), V==X, !,
	Related=[E|More],
	equs_for_all_vars(Vs,Es,More).
equs_for_all_vars([V|Vs],Es,Related):-
	( Es=[X=_|_], V@<X ; Es=[] ), !,
	Related=[V=_|More],
	equs_for_all_vars(Vs,Es,More).

%% equs_for_all_vars([],[],_Renamings,[]).
%% equs_for_all_vars([V|Vs],[E|Es],Renamings,Related):-
%% 	E=(X=_), V==X, !,
%% 	Related=[E|More],
%% 	equs_for_all_vars(Vs,Es,Renamings,More).
%% equs_for_all_vars([V|Vs],Es,Renamings,Related):-
%% 	( Es=[X=_|_], V@<X ; Es=[] ), !,
%% 	get_a_renaming(Renamings,V,ThisOne,NewRenamings),
%% 	put_a_renaming(ThisOne,V,E0),
%% 	Related=[E0|More],
%% 	equs_for_all_vars(Vs,Es,NewRenamings,More).
%% 
%% get_a_renaming([],_,[],[]).
%% get_a_renaming([Y=X|Rs],V,ThisOne,NewRs):-
%% 	V==X, !,
%% 	ThisOne=[Y],
%% 	NewRs=Rs.
%% get_a_renaming([R|Rs],V,ThisOne,[R|NewRs]):-
%% 	get_a_renaming(Rs,V,ThisOne,NewRs).
%% 
%% put_a_renaming([],X,X=_).
%% put_a_renaming([Y],X,X=Y).

substitute_equs([],Closed,Closed).
substitute_equs(WReplace,InReplace,Closed):- WReplace=[_|_],
	perform(WReplace,Vars,Replaces),
	replace_all(InReplace,Vars,Replaces,Closed).

perform([],[],[]).
perform([X=Y|Es],[X|Xs],[Y|Ys]):-
	perform(Es,Xs,Ys).

replace_all([],_,_,[]).
replace_all([X=Y|Es],Vars,Replaces,[E|Closed]):-
	replace_equs(Vars,Replaces,Y,X,E),
	replace_all(Es,Vars,Replaces,Closed).

replace_equs(Vars,Replaces,Y,X,X=NewY):-
	varset(Y,YVars),
	ord_subtract(YVars,Vars,VarsToKeep),
	copy_term(term(Y,Vars),term(NewY,NewVars)),
	varset(NewY,NewYVars),
	sort(NewVars,NewVarsSorted),
	ord_subtract(NewYVars,NewVarsSorted,VarsToKeep),
	replace_each_var(NewVars,Replaces).

replace_each_var([],[]).
replace_each_var([V|Vs],[V|Replaces]):-
	replace_each_var(Vs,Replaces).

check_equs([],_,_,[]).
%% check_equs([_=Y|Eqs],K,Vars,Projected):-
%% 	var(Y),
%% 	\+ ( ord_member(Y,Vars) ), !,
%% 	check_equs(Eqs,K,Vars,Projected).
check_equs([X=Y|Eqs],K,Vars,[X=NewY|More]):-
	check_depth(K,Y,NewY),
	check_equs(Eqs,K,Vars,More).

check_depth(_,Term,NewTerm):- var(Term), !, NewTerm=Term.
check_depth(K,Term,NewTerm):-
	K1 is K-1,
	functor(Term,F,A),
	functor(NewTerm,F,A),
	check_depth_args(A,K1,Term,NewTerm).

check_depth_args(0,_,_,_):- !.
check_depth_args(_,0,_,_):- !.
check_depth_args(N,K,Term,NewTerm):-
	arg(N,Term,Arg),
	arg(N,NewTerm,NewArg),
	check_depth(K,Arg,NewArg),
	N1 is N-1,
	check_depth_args(N1,K,Term,NewTerm).

%-------------------------------------------------------------------------

%% two lists of substs. identical - same trick as in "sem"

%% depthk_identical_interpretations('$bottom','$bottom'):- !.
%% depthk_identical_interpretations('$bottom',_I):- !, fail.
%% depthk_identical_interpretations(_I,'$bottom'):- !, fail.
%% depthk_identical_interpretations(I0,I1):-
%% 	length(I0,L),
%% 	length(I1,L).

%-------------------------------------------------------------------------

%% table of builtins

depthk_abstract_builtin(Builtin,Sv,I):-
	builtin_depthk(Builtin,Sv,D),
	sort(D,I).

%% very raw this! There is a lot on info for refining the subst. which
%%  can not be expressed here!!!!!!!!!!

builtin_depthk((!),_Sv,[]).
builtin_depthk('='(X,Y),Sv,I):-          depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk('=..'(_,Y),Sv,I):-        depthk_bu_unify([Y=[_|_]],Sv,[],I).
builtin_depthk('=:='(X,Y),Sv,I):-        depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk('=='(X,Y),Sv,I):-         depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk((_ =\= _),_Sv,[]).
builtin_depthk('=<'(_,_),_Sv,[]).
builtin_depthk('@=<'(_,_),_Sv,[]).
builtin_depthk('@>'(_,_),_Sv,[]).
builtin_depthk('@>='(_,_),_Sv,[]).
builtin_depthk('@<'(_,_),_Sv,[]).
builtin_depthk('>'(_,_),_Sv,[]).
builtin_depthk('>='(_,_),_Sv,[]).
builtin_depthk((_ \== _),_Sv,[]).
builtin_depthk('<'(_,_),_Sv,[]).
builtin_depthk('$metachoice'(_),_Sv,[]).
builtin_depthk('$metacut'(_),_Sv,[]).
builtin_depthk('C'(X,Y,Z),Sv,I):-        depthk_bu_unify([X=[Y|Z]],Sv,[],I).
builtin_depthk(arg(_,_,_),_Sv,[]).
builtin_depthk(atom(_),_Sv,[]).
builtin_depthk(atomic(_),_Sv,[]).
builtin_depthk(fail,_Sv,[]).
builtin_depthk(false,_Sv,[]).
builtin_depthk(format(_,_),_Sv,[]).
builtin_depthk(format(_,_,_),_Sv,[]).
builtin_depthk(functor(_,_,_),_Sv,[]).
builtin_depthk(ground(_),_Sv,[]).
builtin_depthk(integer(_),_Sv,[]).
builtin_depthk(is(_,_),_Sv,[]).
builtin_depthk(length(_,_),_Sv,[]).
builtin_depthk(name(_,_),_Sv,[]).
builtin_depthk(nl(_),_Sv,[]).
builtin_depthk(nonvar(_),_Sv,[]).
builtin_depthk(number(_),_Sv,[]).
builtin_depthk(numbervars(X,Y,_),Sv,I):- depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk(statistics(_,_),_Sv,[]).
builtin_depthk(true,_Sv,[]).
builtin_depthk(var(_),_Sv,[]).
builtin_depthk(write(_),_Sv,[]).      
builtin_depthk(write(_,_),_Sv,[]).
builtin_depthk(write_canonical(_),_Sv,[]).
builtin_depthk(write_canonical(_,_),_Sv,[]).
builtin_depthk(writeq(_),_Sv,[]).
builtin_depthk(writeq(_,_),_Sv,[]).
builtin_depthk(Builtin,_Sv,[]):-          functor(Builtin,_,0).
