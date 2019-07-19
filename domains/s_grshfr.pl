:- module(s_grshfr,
	[ asubs_to_indep/2,
	  asubs_to_dep/3,
	  dep_to_indep/3,
	  ground_conds/3,
	  impossible/3,
	  indep_conds_one_var/4,
	  indep_cond_one_var_ordered/5,
	  indep_conds/4,
	  not_ground_conds/3,
	  not_indep/4,
	  not_indep_conds_one_var/4,
	%
	  ground_imply_ground/4,
	  ground_imply_indep/5,
	  ground_imply_not_indep/4,
	  indep_imply_ground/4,
	  indep_imply_indep/5,
	  indep_imply_not_indep/4,
	% hummm: too low level!
	  change_values_insert/4,
	  collect_vars_freeness/2,
	  create_values/3,
	  member_value_freeness/3,
	  merge_no_supersets/3,
	  new1_gvars/4,
	  projected_gvars/3,
	  var_value/3, % GPS needed by spec/abs_exec.pl
	  change_values_if_differ/5,
	  combinations_no_supersets/2, % JN needed by sharedef.pl
	  ord_split_supersets/4        % JN needed by sharedef.pl
	],
	[]).

:- use_package(assertions).

:- use_module(library(lists), [list_to_list_of_lists/2]).
:- use_module(library(lsets), 
        [ merge_list_of_lists/2, ord_intersect_all/2, ord_split_lists/4,
          ord_split_lists_from_list/4, setproduct_lists/4]).
:- use_module(library(sets), 
        [ merge/3, ord_intersect/2, ord_member/2, ord_subset/2, ord_subset_diff/3,
          ord_subtract/3]).
:- use_module(library(sort)).
:- use_module(library(terms_vars), [varset/2]).

asubs_to_indep(ASub,Indeps):-
	asubs_to_dep(ASub,Dep,NGVars),
	dep_to_indep(NGVars,Dep,Indeps).

%------------------------------------------------------------------------------
% asubs_to_dep(+,-,-)
% asubs_to_dep(Xss,Dep,Ngvars) 
% Ngvars is the oredered set of variables which appear in some Xs of Xss
% Dep is the ordered set of dep(X,Y) foreach X,Y appearing in some Xs 
% of Xss (X < Y, if Xs is sorted)
%------------------------------------------------------------------------------
asubs_to_dep(Xss,Dep,Ngvars) :-
	asubs_to_dep_(Xss,[],Dep,[],Ngvars).

asubs_to_dep_([Xs|Xss],Temp1Dep,Dep,Temp1Ngvars,Ngvars) :-
	merge(Xs,Temp1Ngvars,Temp2Ngvars),
	sharing_to_depend(Xs,Newdep),
	merge(Temp1Dep,Newdep,Temp2Dep),
	asubs_to_dep_(Xss,Temp2Dep,Dep,Temp2Ngvars,Ngvars).
asubs_to_dep_([],Dep,Dep,Ngvars,Ngvars).

%------------------------------------------------------------------------------
% sharing_to_depend(+,-)
% sharing_to_depend(Xs,Dep)
% Xs is an ordered list
% Dep = { dep(X,Y) | forall X,Y in Xs,  X < Y}
%------------------------------------------------------------------------------
sharing_to_depend([X|Xs],Dep) :-
	create_dep(Xs,X,Tail,Dep),
	sharing_to_depend(Xs,Tail).
sharing_to_depend([],[]).

create_dep([Y|Ys],X,Tail,[dep(X,Y)|NewDep]) :-
	create_dep(Ys,X,Tail,NewDep).
create_dep([],_,Tail,Tail).

%------------------------------------------------------------------------------
% dep_to_indep(+,+,-)
% dep_to_indep(Xs,Dep,Indep) 
% Indep = { indep(X,Y) | forall X,Y in Xs s.t. dep(X,Y) not in Dep}
%------------------------------------------------------------------------------
dep_to_indep([X|Xs],Dep,Indep) :-
	add_indep(Xs,X,Dep,Indep,Tail),
	dep_to_indep(Xs,Dep,Tail).
dep_to_indep([],_,[]).

add_indep([Y|Ys],X,Dep,Indep,Tail) :-
	ord_member(dep(X,Y),Dep), !,
	add_indep(Ys,X,Dep,Indep,Tail).
add_indep([Y|Ys],X,Dep,Indep,Tail) :-
	compare(D,X,Y),
	indep_cond_one_var_ordered(D,X,Y,Indep,Tail1),
	add_indep(Ys,X,Dep,Tail1,Tail).
add_indep([],_,_,Tail,Tail).

%------------------------------------------------------------------------------
% make conds
%------------------------------------------------------------------------------

% make ground conds for each variable in a list of variables

ground_conds([],T,T).
ground_conds([X|Xs],[ground(X)|More],Tail):-
	ground_conds(Xs,More,Tail).

% make not-ground conds for each variable in a list of variables

not_ground_conds([],T,T).
not_ground_conds([X|Xs],[not(ground(X))|More],Tail):-
	not_ground_conds(Xs,More,Tail).

% make indep conds for each couple of variables in two lists of variables

indep_conds([],_,T,T).
indep_conds([X|Xs],Ys,List,Tail):-
	indep_conds_one_var(Ys,X,List,List1),
	indep_conds(Xs,Ys,List1,Tail).

indep_conds_one_var([],_,T,T).
indep_conds_one_var([Y|Ys],X,List,Tail):-
	compare(D,X,Y),
	indep_cond_one_var_ordered(D,X,Y,List,List1),
	indep_conds_one_var(Ys,X,List1,Tail).

indep_cond_one_var_ordered(<,X,V,[indep(X,V)|Tail],Tail).
indep_cond_one_var_ordered(>,X,V,[indep(V,X)|Tail],Tail).
indep_cond_one_var_ordered(=,_X,_V,Tail,Tail).

% make indep conds for a variable and each variable in a list of variables

not_indep_conds_one_var([],_,T,T).
not_indep_conds_one_var([Y|Ys],X,List,Tail):-
	compare(D,X,Y),
	not_indep_cond_one_var_ordered(D,X,Y,List,List1),
	not_indep_conds_one_var(Ys,X,List1,Tail).

not_indep_cond_one_var_ordered(<,X,V,[not(indep(X,V))|Tail],Tail).
not_indep_cond_one_var_ordered(>,X,V,[not(indep(V,X))|Tail],Tail).
not_indep_cond_one_var_ordered(=,_X,_V,Tail,Tail).

impossible([Element|Sh],Sh1,Vars):-
	possible(Element,Sh1,Vars,Temp), !,
	sort([Element|Temp],Elements),
	ord_subtract(Sh,Elements,NewSh),
	impossible(NewSh,Sh1,Vars).
impossible(X,_,_):-
	X = [_|_].
	
possible(Vars,_Sh1,OldVars,Elements):- 
	Vars == OldVars,!,
	Elements = [].
possible(Vars,Sh1,OldVars,[S|NewElements]):-
	take_element_free(Sh1,Vars,NewSh1,S),
	merge(S,Vars,NewVars),
	possible(NewVars,NewSh1,OldVars,NewElements).
	
take_element_free([S|Sh],OldVars,NewSh,NewS):-
	\+ (ord_intersect(S,OldVars)),!,
	NewSh = Sh,
	NewS = S.
take_element_free([S|Sh],OldVars,[S|NewSh],NewS):-
	take_element_free(Sh,OldVars,NewSh,NewS).

%------------------------------------------------------------------------
% not_indep(+,+,-,?)
% not_indep(Freevars,Sh,Neg,NegTail)
% not(indep(X,Y)) holds for any free variable X and any other variable Y
% which appears in all sharing sets in which X appears
%------------------------------------------------------------------------
not_indep([],_Sh,Neg,Neg).
not_indep([X|Xs],Sh,Neg,NegTail):-
	ord_split_supersets([X],Sh,[],Supersets),
	ord_intersect_all(Supersets,CommonVars),
	not_indep_conds_one_var(CommonVars,X,Neg,Neg0),
	not_indep(Xs,Sh,Neg0,NegTail).

%------------------------------------------------------------------------
% ground_imply_ground(+,+,-,?)
% ground_imply_ground(Ngvars,Sh,Imp,ImpTail)
% indep_imply_ground(+,+,-,?)
% indep_imply_ground(Ngvars,Sh,Imp,ImpTail)
% implications of ground(X) exist if the sharing set [X] does not exist
% and for all sharing sets containing X the antecedent can eliminate them
%------------------------------------------------------------------------
ground_imply_ground([],_Sh,Imp,Imp).
ground_imply_ground([X|Xs],Sh,Imp,ImpT):-
	ord_split_supersets([X],Sh,[],Supersets),
	ground_imply(Supersets,ground(X),Imp,Imp0),
	ground_imply_ground(Xs,Sh,Imp0,ImpT).

indep_imply_ground([],_Sh,Imp,Imp).
indep_imply_ground([X|Xs],Sh,Imp,ImpT):-
	ord_split_supersets_with([X],Sh,[],Supersets),
	indep_imply(Supersets,ground(X),Imp,Imp0),
	indep_imply_ground(Xs,Sh,Imp0,ImpT).

%------------------------------------------------------------------------
% ground_imply_indep(+,+,+,-,?)
% ground_imply_indep(Ngvars1,Ngvars2,Sh,Imp,ImpTail)
% indep_imply_indep(+,+,+,-,?)
% indep_imply_indep(Ngvars1,Ngvars2,Sh,Imp,ImpTail)
% for any two non-ground variables X,Y s.t. X\==Y implications of 
% indep(X,Y) exist if the sharing set [X,Y] does not exist and for all 
% sharing sets containing X and Y the antecedent can eliminate them
%------------------------------------------------------------------------
ground_imply_indep([],_Vars,_Sh,Imp,Imp).
ground_imply_indep([X|Xs],Vars,Sh,Imp,ImpT):-
	ground_imply_indep_var(Vars,X,Sh,Imp,Imp0),
	ground_imply_indep(Xs,Vars,Sh,Imp0,ImpT).

ground_imply_indep_var([],_X,_Sh,Imp,Imp).
ground_imply_indep_var([Y|Ys],X,Sh,Imp,Imp0):-
	X == Y, !,
	ground_imply_indep_var(Ys,X,Sh,Imp,Imp0).
ground_imply_indep_var([Y|Ys],X,Sh,Imp,ImpT):-
	sort([X,Y],Vars),
	ord_split_supersets(Vars,Sh,[],Supersets),
	compare(D,X,Y),
	indep_cond_one_var_ordered(D,X,Y,[Consecuent],[]),
	ground_imply(Supersets,Consecuent,Imp,Imp0),
	ground_imply_indep_var(Ys,X,Sh,Imp0,ImpT).

indep_imply_indep([],_Vars,_Sh,Imp,Imp).
indep_imply_indep([X|Xs],Vars,Sh,Imp,ImpT):-
	indep_imply_indep_var(Vars,X,Sh,Imp,Imp0),
	indep_imply_indep(Xs,Vars,Sh,Imp0,ImpT).

indep_imply_indep_var([],_X,_Sh,Imp,Imp).
indep_imply_indep_var([Y|Ys],X,Sh,Imp,ImpT):-
	X == Y, !,
	indep_imply_indep_var(Ys,X,Sh,Imp,ImpT).
indep_imply_indep_var([Y|Ys],X,Sh,Imp,ImpT):-
	sort([X,Y],SubVars),
	ord_split_supersets_with(SubVars,Sh,[],Supersets),
	compare(D,X,Y),
	indep_cond_one_var_ordered(D,X,Y,[Consecuent],[]),
	indep_imply(Supersets,Consecuent,Imp,Imp0),
	indep_imply_indep_var(Ys,X,Sh,Imp0,ImpT).

%------------------------------------------------------------------------
% ground_imply_not_indep(+,+,-,?)
% ground_imply_not_indep(Freevars,Sh,Imp,ImpTail)
% indep_imply_not_indep(+,+,-,?)
% indep_imply_not_indep(Freevars,Sh,Imp,ImpTail)
% for a free variable X implications of not(indep(X,Y)) exist if the
% sharing set [X] does not exist and X\==Y and Y appears in some sharing 
% set in which X appears and for all sharing sets in which X appears but 
% Y does not the antecedent can eliminate them
%------------------------------------------------------------------------
ground_imply_not_indep([],_Sh,Imp,Imp).
ground_imply_not_indep([X|Xs],Sh,Imp,ImpT):-
	ord_split_supersets([X],Sh,[],Supersets),
	varset(Supersets,Vars),
	ground_imply_not_indep_var(Vars,X,Supersets,Imp,Imp0),
	ground_imply_not_indep(Xs,Sh,Imp0,ImpT).

ground_imply_not_indep_var([],_X,_ShX,Imp,Imp).
ground_imply_not_indep_var([Y|Ys],X,ShX,Imp,ImpT):-
	X == Y, !,
	ground_imply_not_indep_var(Ys,X,ShX,Imp,ImpT).
ground_imply_not_indep_var([Y|Ys],X,ShX,Imp,ImpT):-
	ord_split_lists(ShX,Y,_,Disjunct),
	compare(D,X,Y),
	indep_cond_one_var_ordered(D,X,Y,[Consecuent],[]),
	ground_imply(Disjunct,not(Consecuent),Imp,Imp0),
	ground_imply_not_indep_var(Ys,X,ShX,Imp0,ImpT).

indep_imply_not_indep([],_Sh,Imp,Imp).
indep_imply_not_indep([X|Xs],Sh,Imp,ImpT):-
	ord_split_supersets_with([X],Sh,[],Supersets),
	varset(Supersets,Vars),
	indep_imply_not_indep_var(Vars,X,Supersets,Imp,Imp0),
	indep_imply_not_indep(Xs,Sh,Imp0,ImpT).

indep_imply_not_indep_var([],_X,_ShX,Imp,Imp).
indep_imply_not_indep_var([Y|Ys],X,ShX,Imp,ImpT):-
	X == Y, !,
	indep_imply_not_indep_var(Ys,X,ShX,Imp,ImpT).
indep_imply_not_indep_var([Y|Ys],X,ShX,Imp,ImpT):-
	ord_split_lists(ShX,Y,_,Disjunct),
	compare(D,X,Y),
	indep_cond_one_var_ordered(D,X,Y,[Consecuent],[]),
	indep_imply(Disjunct,Consecuent,Imp,Imp0),
	indep_imply_not_indep_var(Ys,X,ShX,Imp0,ImpT).

%------------------------------------------------------------------------
% ground_imply(+,+,-,?)
% ground_imply(Sh,Consecuent,Imp,ImpTail)
% a sharing can be eliminated with conditions ground(X) for each sharing
% set, where X can be any variable in the sharing set - except those which
% already appear in the consecuent, i.e. we don't want things such as
% ground(X) -> ground(X) or ground(X) -> indep(X,Y)
%------------------------------------------------------------------------
ground_imply([],_Consecuent,Imp,Imp).
ground_imply(Sh,Consecuent,Imp,ImpT):-
	all_possible_grounds(Sh,As),
	combinations_no_supersets(As,Antecedents),
	imply_all(Antecedents,Consecuent,Imp,ImpT).

all_possible_grounds([],[]).
all_possible_grounds([S|Sh],[Gs|More]):-
	ground_conds(S,Gs,[]),
	all_possible_grounds(Sh,More).

imply_all([],_Consecuent,Imp,Imp).
imply_all([Antecedent|More],Consecuent,Imp,ImpT):-
	implies(Antecedent,Consecuent,Imp,Imp0),
	imply_all(More,Consecuent,Imp0,ImpT).

implies([],_Consecuent,Imp,Imp):- !.
implies(Antecedent,Consecuent,[(Antecedent->Consecuent)|Imp0],Imp0).

%------------------------------------------------------------------------
% indep_imply(+,+,-,?)
% indep_imply(Sh,Consecuent,Imp,ImpTail)
% a sharing can be eliminated with conditions indep(X,Y) for each sharing
% set, where X,Y can be any variables in the sharing set - except when
% indep(X,Y) is the consecuent, i.e. we don't want indep(X,Y) -> indep(X,Y)
% but we do want indep(X,Y) -> ground(X)
%------------------------------------------------------------------------
indep_imply([],_Consecuent,Imp,Imp). % TODO: Missing cut?
indep_imply(Sh,Consecuent,Imp,ImpT):-
	all_possible_indeps(Sh,[Consecuent],As),
	combinations_no_supersets(As,Antecedents),
	imply_all(Antecedents,Consecuent,Imp,ImpT).

all_possible_indeps([],_Consecuent,[]).
all_possible_indeps([S|Sh],Consecuent,[Is|More]):-
	indep_conds(S,S,IConds,[]),
	ord_subtract(IConds,Consecuent,Is),
	all_possible_indeps(Sh,Consecuent,More).

%------------------------------------------------------------------------
% combinations_no_supersets(+,-)
% combinations_no_supersets(Lss,Css)
% Css = { Cs | for each Ls in Lss, exists X in Ls, X in Cs and there is
%         no Cs0 s.t. Cs subset Cs0 }
%------------------------------------------------------------------------
combinations_no_supersets([],[]).
combinations_no_supersets([Ls|Lss],Css):-
	list_to_list_of_lists(Ls,Init),
	combinations_no_supersets_(Lss,Init,Css).

combinations_no_supersets_([],Css,Css).
combinations_no_supersets_([Ls|Lss],Css0,Css):-
	ord_split_lists_from_list(Ls,Css0,Intersect,Disjunct),
	list_to_list_of_lists(Ls,Zss),
	setproduct_lists(Disjunct,Zss,Product,[]),
	sort(Product,Product_s),
	merge_no_supersets(Product_s,Intersect,Css1),
	combinations_no_supersets_(Lss,Css1,Css).
      
%-------------------------------------------------------------------------
% merge_no_supersets(+,+,-)                                              |
% merge_no_supersets(Xss,Yss,Zss)                                        |
% Xss and Yss are ordered set of ordered sets with a particular          |
% characteristic: there is no Xs1,Xs2 in Xss s.t. Xs1 susbseteq Xs2 (the |
% same with Yss.                                                         |
% Zss is the result of merging Xss and Yss in the same way, i.e. there is|
% no Zs1,Zs2 in Zss s.t. Zs1 subseteq Zs2                                |
%-------------------------------------------------------------------------
merge_no_supersets(Xss,Yss,Minimized):-
        merge_no_supersets0(Xss,Yss,Temp),
        sort(Temp,Minimized).

merge_no_supersets0(Xss,[],Temp):- !, Temp = Xss.
merge_no_supersets0([],Yss,Temp):-    Temp = Yss.
merge_no_supersets0([Xs|Xss],Yss,Temp):-
        ord_superset(Yss,Xs,RestYss,Temp,Tail1,Flag),
        decide_no_supersets(Flag,Xs,Tail1,Tail2),
        merge_no_supersets0(Xss,RestYss,Tail2).

ord_superset([],_Xs,[],Tail,Tail,nosuperset).
ord_superset([Ys|Yss],Xs,RestYss,Temp,Tail,Flag):-
	Ys = [Y|RestYs],
	Xs = [X|RestXs],
        compare(Order,Y,X),
        myord_superset(Order,Y,RestYs,X,RestXs,Flag1),
	decide_ord_superset(Flag1,Xs,Ys,Yss,RestYss,Temp,Tail,Flag).

decide_ord_superset(nosuperset,Xs,Ys,Yss,[Ys|NewYss],TempYss,Tail,Flag):-
        ord_superset(Yss,Xs,NewYss,TempYss,Tail,Flag).
decide_ord_superset(lessxs,_Xs,Ys,Yss,[Ys|Yss],Tail,Tail,nosuperset).
decide_ord_superset(superset2,_Xs,Ys,Yss,[Ys|Yss],Tail,Tail,superset).
decide_ord_superset(lessys,Xs,Ys,Yss,NewYss,[Ys|TempYss],Tail,Flag):-
        ord_superset(Yss,Xs,NewYss,TempYss,Tail,Flag).
decide_ord_superset(superset1,Xs,_Ys,Yss,NewYss,TempYss,Tail,Flag):-
        ord_superset(Yss,Xs,NewYss,TempYss,Tail,Flag).

decide_no_supersets(superset,_Xs,Tail,Tail).
decide_no_supersets(nosuperset,Xs,[Xs|Tail],Tail).

%-------------------------------------------------------------------------
% myord_superset(+,+,-),                                                  |
% myord_superset(Order,Y,Ys,X,Xs,Flag)                                    |
% Ty = [Y|Ys] and Tx = [X|Xs] are sets of variables. Flag = superset1 if  |
% Ty is a superset of Tx. Flag = superset2 if Tx is a superset or equal to|
% Ty. If  Y is greater than any X1 in Tx, Flag = lessxs.                  |
% If X is greater than any Y1 in Ty, Flag = lessys                        |
% Otherwise Flag = nosuperset                                             |
%-------------------------------------------------------------------------
myord_superset(=,_Y,Ys,_X,Xs,Flag):-
        myord_subset_equal(Ys,Xs,Flag).
myord_superset(<,_Y,Ys,X,Xs,Flag):-
        myord_lessys(Ys,[X|Xs],Flag).
myord_superset(>,Y,Ys,_X,Xs,Flag):-
        myord_lessxs(Xs,[Y|Ys],Flag).

myord_subset_equal([],_,superset2):- !.
myord_subset_equal(_,[],superset1):- !.
myord_subset_equal([Y|Ys],[X|Xs],Flag):-
        compare(Order,Y,X),
        myord_subset_equal_(Order,Y,Ys,X,Xs,Flag).

myord_subset_equal_(=,_Y,Ys,_X,Xs,Flag):-
        myord_subset_equal(Ys,Xs,Flag).
myord_subset_equal_(<,_Y,Ys,X,Xs,Flag):-
	myord_subset_1(Ys,[X|Xs],Flag).
myord_subset_equal_(>,Y,Ys,_X,Xs,Flag):-
        myord_subset_2([Y|Ys],Xs,Flag).

myord_subset_1(_,[],superset1):- !.
myord_subset_1([],_,nosuperset).
myord_subset_1([Y|Ys],[X|Xs],Flag):-
        compare(Order,Y,X),
        myord_subset_1_(Order,Y,Ys,X,Xs,Flag).

myord_subset_1_(=,_Y,Ys,_X,Xs,Flag):-
        myord_subset_1(Ys,Xs,Flag).
myord_subset_1_(<,_Y,Ys,X,Xs,Flag):-
        myord_subset_1(Ys,[X|Xs],Flag).
myord_subset_1_(>,_Y,_Ys,_X,_Xs,nosuperset).

myord_subset_2([],_,superset2):- !.
myord_subset_2(_,[],nosuperset):- !.
myord_subset_2([Y|Ty],[X|Tx],Flag):-
        compare(Order,Y,X),
        myord_subset_2_(Order,Y,Ty,X,Tx,Flag).

myord_subset_2_(=,_Y,Ys,_X,Xs,Flag):-
        myord_subset_2(Ys,Xs,Flag).
myord_subset_2_(<,_Y,_Ys,_X,_Xs,nosuperset).
myord_subset_2_(>,Y,Ys,_X,Xs,Flag):-
        myord_subset_2([Y|Ys],Xs,Flag).

myord_lessxs([],_,lessxs).
myord_lessxs([X|Xs],[Y|Ys],Flag):-
        compare(Order,Y,X),
        myord_lessxs_(Order,Y,Ys,X,Xs,Flag).

myord_lessxs_(=,_Y,Ys,_X,Xs,Flag):-
        myord_subset_2(Ys,Xs,Flag).
myord_lessxs_(>,Y,Ys,_X,Xs,Flag):-
        myord_lessxs(Xs,[Y|Ys],Flag).
myord_lessxs_(<,_Y,_Ys,_X,_Xs,nosuperset).

myord_lessys([],_,lessys).
myord_lessys([Y|Ys],[X|Xs],Flag):-
        compare(Order,Y,X),
        myord_lessys_(Order,Y,Ys,X,Xs,Flag).

myord_lessys_(=,_Y,Ys,_X,Xs,Flag):-
        myord_subset_1(Ys,Xs,Flag).
myord_lessys_(>,_Y,_Ys,_X,_Xs,nosuperset).
myord_lessys_(<,_Y,Ys,X,Xs,Flag):-
        myord_lessys(Ys,[X|Xs],Flag).

%-------------------------------------------------------------------------
% collect_vars_freeness(+,-)                                             |
% collect_vars_freeness(Fr,Vars)                                         |
% It returns in Vars the list of variables in Fr.                        |
%-------------------------------------------------------------------------
collect_vars_freeness([],[]).
collect_vars_freeness([X/_|Rest],[X|Vars]):-
	collect_vars_freeness(Rest,Vars).

%-------------------------------------------------------------------------
% var_value(+,+,-)                                                       |
% var_value(Fr,X,Value)                                                  |
% It obtains in the third argument the freeness value of X               |
%-------------------------------------------------------------------------
var_value([Y/V|More],X,Value):-
	compare(D,X,Y),
	var_value_(D,V,More,X,Value).

var_value_(=,Value,_More,_X,Value).
var_value_(>,_Elem,[Y/V|More],X,Value):-
	compare(D,X,Y),
	var_value_(D,V,More,X,Value).

%-------------------------------------------------------------------------
% change_values_if_differ(+,+,-,+,+)                                     |
% change_values_if_differ(Vars,Fr,NewFr,Value1,Value2)                   |
% Forall X in Vars there must exist X/V in Fr and V must be different    |
% from Value2. If so, X/V is changed to X/Value1. Otherwise it fails     |
%-------------------------------------------------------------------------
change_values_if_differ([],Fr,NewFr,_,_):- !,
	NewFr = Fr.
change_values_if_differ([Y|Ys],[X/Val|Fr],NewFr,Val1,Val2):- 
	compare(D,X,Y),
	change_values_if_differ_(D,X/Val,Fr,Y,Ys,NewFr,Val1,Val2).

change_values_if_differ_(=,_/Val,Fr,Y,Ys,NewFr,Val1,Val2):-
	Val \== Val2,
	NewFr = [Y/Val1|RestFr],
	change_values_if_differ(Ys,Fr,RestFr,Val1,Val2).
change_values_if_differ_(<,Elem,Fr,Y,Ys,[Elem|NewFr],Val1,Val2):-
	change_values_if_differ([Y|Ys],Fr,NewFr,Val1,Val2).

%-------------------------------------------------------------------------
% create_values(+,-,+)                                                   |
% create_values(Vars,Fr,Value)                                           |
% Forall X in Vars, X/Value is in Fr                                     |
%-------------------------------------------------------------------------
create_values([],[],_Value).
create_values([X|Xs],[X/Value|NewFr],Value):-
	create_values(Xs,NewFr,Value).

%-------------------------------------------------------------------------
% change_values_insert(+,+,-,+)                                          |
% change_values_insert(Vars,Fr,NewFr,Value)                              |
% Forall X in Vars, if exists X/V in Fr it is changed to X/Value,        |
% otherwise X/Value is added to Fr. Both Ordered                         |
%-------------------------------------------------------------------------
change_values_insert([],Fr,Fr,_):- !.
change_values_insert(Vars,[],NewFr,Value):- !,
	create_values(Vars,NewFr,Value).
change_values_insert([X|Xs],[Y/Val|Fr],NewFr,Value):- 
	compare(D,Y,X),
	change_values_insert_(D,Y/Val,Fr,X,Xs,NewFr,Value).

change_values_insert_(=,_,Fr,X,Xs,[X/Value|NewFr],Value):-
	change_values_insert(Xs,Fr,NewFr,Value).
change_values_insert_(>,Elem,Fr,X,[],NewFr,Value):- !,
	NewFr = [X/Value,Elem|Fr].
change_values_insert_(>,Elem,Fr,X,Xs,[X/Value|NewFr],Value):- 
	change_values_insert(Xs,[Elem|Fr],NewFr,Value).
change_values_insert_(<,Elem,[],X,Xs,NewFr,Value):- !,
	NewFr = [Elem,X/Value|RestFr],
	create_values(Xs,RestFr,Value).
change_values_insert_(<,Elem,Fr,X,Xs,[Elem|NewFr],Value):-
	change_values_insert([X|Xs],Fr,NewFr,Value).

%-------------------------------------------------------------------------
% member_value_freeness(+,-,+)                                           |
% member_value_freeness(PairList,List,Value)                             |
% It returns in Vars the list of variables with freeness value: Value    |
% I.e., returns in List the list of Xs with value V=Value where          |
% PairList=[X/V|...]                                                     |
%-------------------------------------------------------------------------
member_value_freeness([],[],_).
member_value_freeness([X/Value|Rest],ListValue,Value):- !,
	ListValue = [X|More],
	member_value_freeness(Rest,More,Value).
member_value_freeness([_|Rest],ListValue,Value):- 
	member_value_freeness(Rest,ListValue,Value).

%-------------------------------------------------------------------------
% projected_gvars(+,+,-)                                                 |
% projected_gvars(ASub,Vars,Gv)                                          |
% Obtains in Gv the set of variables in Vars which are ground w.r.t. ASub|
%-------------------------------------------------------------------------
projected_gvars([],Vars,Vars):- !.
projected_gvars(_ASub,[],[]):- !.
projected_gvars(ASub,Vars,Gv) :-
	merge_list_of_lists(ASub,NonGround),
	ord_subtract(Vars,NonGround,Gv).

:- push_prolog_flag(multi_arity_warnings,off).

new1_gvars([], _,[], []).
new1_gvars([(Y,Bind)|Rest],X,Int1_Binds,New1_gvars) :-
	compare(Order,X,Y),
	new1_gvars(Order,(Y,Bind),Rest,X,Int1_Binds,New1_gvars).

new1_gvars(>,(Y,Bind),[],_,Int1_Binds,New1_gvars) :- !,
	Int1_Binds = [(Y,Bind)],
	New1_gvars = [].
new1_gvars(>,(Y,Bindy),[(Z,Bindz)|Rest],X,Int1_Binds,New1_gvars) :-
	compare(Order,X,Z),
	Int1_Binds = [(Y,Bindy)|Rest_bind],
	new1_gvars(Order,(Z,Bindz),Rest,X,Rest_bind,New1_gvars).
new1_gvars(=, (_,Bind),Rest,_,Rest,New1_gvars) :-
	varset(Bind,New1_gvars).
new1_gvars(<, (Y,Bind),Rest,_,[(Y,Bind)|Rest],[]).

:- pop_prolog_flag(multi_arity_warnings).

%-------------------------------------------------------------------------
% ord_split_supersets_with(+,+,+,-)
% ord_split_supersets_with(Vars,Xss,[],Supersets)
% if there is no Xs in Xss s.t. Vars == Xs, then 
%              Supersets1 = {Xs in Xss| Vars subset Xs}
% Then Supersets = min(Supersets1) were
%   min(SS) = {S in SS| neg exists S' in SS, S' subset S}
% Otherwise Supersets = []
%-------------------------------------------------------------------------
ord_split_supersets_with([],Xss,[],Xss):- !.
ord_split_supersets_with(Xs,Xss,Temp,Supersets):-
	ord_split_supersets_with1(Xss,Xs,Temp,Supersets).
	
ord_split_supersets_with1([],_,Supersets,Supersets).
ord_split_supersets_with1([Ls|_Lss],Vars,_Temp,Supersets):-
	Vars == Ls,!,
	Supersets = [].
ord_split_supersets_with1([Ls|Lss],Vars,Temp,Supersets):-
	ord_subset(Vars,Ls),!,
	merge_no_supersets([Ls],Temp,Temp1),
	ord_split_supersets_with1(Lss,Vars,Temp1,Supersets).
ord_split_supersets_with1([_Ls|Lss],Vars,Temp,Supersets):-
	ord_split_supersets_with1(Lss,Vars,Temp,Supersets).

%-------------------------------------------------------------------------
% ord_split_supersets(+,+,+,-)
% ord_split_supersets(Vars,Xss,Temp,Supersets)
% if there is no Xs in Xss s.t. Vars == Xs, then 
%     Supersets1 = {Ys | exits Xs in Xss, Vars subset Xs, Ys = Xs \ Vars}
% Then Supersets = min(Supersets1) were
%   min(SS) = {S in SS| neg exists S' in SS, S' subset S}
% Otherwise Supersets = []
%-------------------------------------------------------------------------
ord_split_supersets([],Xss,[],Xss):- !.
ord_split_supersets(Xs,Xss,Temp,Supersets):-
	ord_split_supersets1(Xss,Xs,Temp,Supersets).
	
ord_split_supersets1([],_,Supersets,Supersets).
ord_split_supersets1([Ls|Lss],Vars,Temp,Supersets):-
	ord_subset_diff(Vars,Ls,Diff),!,
	decide_subset_diff(Diff,Lss,NewLss,Temp,Temp1,Supersets),
	ord_split_supersets1(NewLss,Vars,Temp1,Supersets).
ord_split_supersets1([_Ls|Lss],Vars,Temp,Supersets):-
	ord_split_supersets1(Lss,Vars,Temp,Supersets).

decide_subset_diff([],_Lss,NewLss,_Temp,_Temp1,Supersets):- 
	NewLss = [],
	Supersets = [].
decide_subset_diff([D|Diff],Lss,Lss,Temp,Temp1,_Supersets):- 
	merge_no_supersets([[D|Diff]],Temp,Temp1).
