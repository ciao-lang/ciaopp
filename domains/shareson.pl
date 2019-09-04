
:- module(shareson,
	[ shareson_call_to_entry/9,
	  shareson_call_to_success_fact/9, 
	  shareson_compute_lub/2,
	  shareson_exit_to_prime/7,  
	  shareson_extend/4,  
	  shareson_input_user_interface/3,
	  shareson_input_interface/4,
	  shareson_less_or_equal/2, 
	  shareson_asub_to_native/5,
	  shareson_project/3, 
	  shareson_sort/2,    
	  shareson_unknown_call/4,  
	  shareson_unknown_entry/3, 
	  shareson_empty_entry/2,
	%
	  shareson_compose/4
	],
	[ ]).

:- use_module(domain(share)).
:- use_module(domain(sondergaard)).
:- use_module(domain(s_grshfr), [projected_gvars/3]).

:- use_module(library(llists), [collect_singletons/2]).
:- use_module(library(lsets), [merge_list_of_lists/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(terms_vars), [varset/2]).

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 22/10/92                             %
%                       programmer: M.J. Garcia de la Banda              %
%                                                                        %
% Function: combined analysis using the Sondergaard and the Sharing      %
%           domain                                                       %
%------------------------------------------------------------------------%
%                    Meanning of the Program Variables                   %
%                                                                        %
%  _son    : Suffix added to abstract subsitutions (Prime,Exit,Proj,...) %
%            for the part corresponding to Sondergaard domain            %
%  _sh     : Suffix added to abstract subsitutions (Prime,Exit,Proj,...) %
%            for the part corresponding to Sharing domain                %
%  GSon    : First argument in substitutions of Sondergaard domain (set  %
%            of ground variables)                                        %
%  SSon    : Second argument in substitutions of Sondergaard domain (set %
%            for singletons and couples of variables)                    %
%  Sh      : Sharing domain (second component of the combination)        %
%  Rest are as in domain_dependent.pl                                    %
%-------------------------------------------------------------------------
% All abstract functions for the combined domain "shareson" first compute%
% the results for the corresponding to the "share" and "son" functions   %
% and then compose the information of both, eliminating redundancies.    %
% See compose function.                                                  %
%-------------------------------------------------------------------------

shareson_call_to_entry(Sv,Sg,Hv,Head,K,Fv,(Proj_son,Proj_sh),Entry,ExtraInfo):-
	son_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_son,Entry_son,ExtraInfo_son),
	share_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj_sh,Entry_sh,ExtraInfo_sh),
	compose(Entry_son,Entry_sh,Hv,Entry),
	ExtraInfo = (ExtraInfo_son,ExtraInfo_sh).

%-------------------------------------------------------------------------

shareson_exit_to_prime(_,_,_,_,'$bottom',_,Prime):- !,
	Prime = '$bottom'.
shareson_exit_to_prime(Sg,Hv,Head,Sv,(Exit_son,Exit_sh),ExtraInfo,Prime):- 
	ExtraInfo = (ExtraInfo_son,ExtraInfo_sh),
	share_exit_to_prime(Sg,Hv,Head,Sv,Exit_sh,ExtraInfo_sh,Prime_sh),
	son_exit_to_prime(Sg,Hv,Head,Sv,Exit_son,ExtraInfo_son,Prime_son),
	compose(Prime_son,Prime_sh,Sv,Prime).
	
%-------------------------------------------------------------------------

shareson_extend('$bottom',_,_,Succ):- !,Succ = '$bottom'.
shareson_extend(_Prime,[],Call,Succ):- !, Call = Succ.
shareson_extend((Prime_son,Prime_sh),Sv,(Call_son,Call_sh),Succ):-
	share_extend(Prime_sh,Sv,Call_sh,Succ_sh),
	son_extend(Prime_son,Sv,Call_son,Succ_son),
	merge_list_of_lists(Call_sh,Vars),
	compose(Succ_son,Succ_sh,Vars,Succ).

%-------------------------------------------------------------------------

shareson_call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
	Proj = (Proj_son,Proj_sh),
	son_call_to_prime_fact(Sg,Hv,Head,Sv,Proj_son,Prime_son),
	share_call_to_prime_fact(Sg,Hv,Head,Sv,Proj_sh,Prime_sh),
	compose(Prime_son,Prime_sh,Sv,Prime),
	shareson_extend(Prime,Sv,Call,Succ).

%-------------------------------------------------------------------------

shareson_compose((_,Call_sh),Succ_sh,Succ_son,Succ):-
	merge_list_of_lists(Call_sh,Vars),
	compose(Succ_son,Succ_sh,Vars,Succ).

%-------------------------------------------------------------------------

shareson_unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
shareson_unknown_call(Sg,Vars,(Call_son,Call_sh),Succ):-
	share_unknown_call(Sg,Vars,Call_sh,Succ_sh),
	son_unknown_call(Sg,Vars,Call_son,Succ_son),
	merge_list_of_lists(Call_sh,AllVars),
	compose(Succ_son,Succ_sh,AllVars,Succ).

%-------------------------------------------------------------------------

shareson_unknown_entry(Sg,Qv,Call):-
	share_unknown_entry(Sg,Qv,Call_sh),
	son_unknown_entry(Sg,Qv,Call_son),
	compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

shareson_empty_entry(Qv,Call):-
	share_empty_entry(Qv,Call_sh),
	son_empty_entry(Qv,Call_son),
	compose(Call_son,Call_sh,Qv,Call).

%-------------------------------------------------------------------------

shareson_project(_,'$bottom',Proj):- !,
	Proj = '$bottom'.
shareson_project([],_,Proj):- !,
	Proj = (([],[]),[]).
shareson_project(Vars,(Call_son,Call_sh),(Proj_son,Proj_sh)):-
	son_project(Vars,Call_son,Proj_son),
	share_project(Vars,Call_sh,Proj_sh).

%-------------------------------------------------------------------------

shareson_compute_lub([ASub1,ASub2|Rest],Lub) :-
	ASub1 == ASub2,!,
	shareson_compute_lub([ASub1|Rest],Lub).
shareson_compute_lub(['$bottom',ASub|Rest],Lub) :- !,
	shareson_compute_lub([ASub|Rest],Lub).
shareson_compute_lub([ASub,'$bottom'|Rest],Lub) :- !,
	shareson_compute_lub([ASub|Rest],Lub).
shareson_compute_lub([(ASub_son1,ASub_sh1),(ASub_son2,ASub_sh2)|Rest],Lub) :-
	son_lub(ASub_son1,ASub_son2,ASub_son3),
	share_lub(ASub_sh1,ASub_sh2,ASub_sh3),
	shareson_compute_lub([(ASub_son3,ASub_sh3)|Rest],Lub).
shareson_compute_lub([ASub],ASub).

%---------------------------------------------------------------------------

shareson_sort('$bottom','$bottom').
shareson_sort((ASub_son,ASub_sh),(ASub_son_s,ASub_sh_s)):-
	son_sort(ASub_son,ASub_son_s),
	share_sort(ASub_sh,ASub_sh_s).

%--------------------------------------------------------------------------

shareson_input_user_interface(Struct,Qv,(Son,Sh)):-
	Struct = (Sharing,_Lin),
	son_input_user_interface(Struct,Qv,Son),
	share_input_user_interface(Sharing,Qv,Sh).

shareson_input_interface(Info,Kind,Struct0,Struct):-
	% already calls share_input_...
	son_input_interface(Info,Kind,Struct0,Struct).

%--------------------------------------------------------------------------

shareson_asub_to_native(((Gr,SSon),Sh),Qv,_OutFlag,ASub_user,[]):-
	collect_singletons(SSon,Singletons),
	varset(Singletons,NonLinearVars),
	ord_subtract(Qv,NonLinearVars,LinearVars),
	if_not_nil(Gr,ground(Gr),ASub_user,ASub_user0),
	if_not_nil(LinearVars,linear(LinearVars),ASub_user0,ASub_user1),
	if_not_nil(Sh,sharing(Sh),ASub_user1,[]).

if_not_nil([],_,Xs,Xs):- !.
if_not_nil(_,X,[X|Xs],Xs).

%------------------------------------------------------------------------%
% shareson_less_or_equal(+,+)                                            %
% shareson_less_or_equal(ASub0,ASub1)                                    %
% Succeeds if ASub1 is more general or equal to ASub0                    %
%------------------------------------------------------------------------%

shareson_less_or_equal(ASub0,ASub1):-
	ASub0 == ASub1.
shareson_less_or_equal((Son0,Sh0),(Son1,Sh1)):-
	share_less_or_equal(Sh0,Sh1),
	son_less_or_equal(Son0,Son1).

%-------------------------------------------------------------------------
% compose(+,+,+,-)                                                       |
% compose(ASub_son,ASub_sh,Sv,(NewASub_son,NewASub_sh))                  |
% It composes the two abstract substitutions in order to eliminate       |
% redundancies. In doing this, it performs the folowing steps:           |
% (1) propagates the sharing info from SSon to ASub_sh (NewASub_sh)      |
% (2) collects in  Gv the ground variables w.r.t. NewASub_sh             |
% (3) NewGSon  is the result of merging Gv and GSon                      |
% (4) NewSSon is the result of eliminating the pairs not allowed by      |
%     NewASub_sh                                                         |
%-------------------------------------------------------------------------


compose((GSon,SSon),ASub_sh,Sv,((NewGSon,NewSSon),NewASub_sh)):-
	propagate_to_sh(ASub_sh,SSon,NewASub_sh,Allowed_sh),
	projected_gvars(NewASub_sh,Sv,Gv),
	merge(GSon,Gv,NewGSon),
	propagate_to_son(SSon,Allowed_sh,NewGSon,NewSSon),!.
compose(_,_,_,'$bottom').
