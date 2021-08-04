:- module(sharing_amgu, [], [assertions, isomodes]).

:- doc(title, "amgu-based sharing domain").
:- doc(author, "Jorge Navas").
% Copyright (C) 2004-2019 The Ciao Development Team

:- include(ciaopp(plai/plai_domain)).
:- dom_def(share_amgu, [default]).

:- use_module(domain(sharing), [
    abs_sort/2,
    extend/5,
    project/5,
    special_builtin/5,
    success_builtin/6,
    compute_lub/2,
    less_or_equal/2,
    glb/3,
    input_interface/4,
    input_user_interface/5,
    asub_to_native/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3
]).
:- dom_impl(_, project/5, [from(sharing:share), noq]).
:- dom_impl(_, compute_lub/2, [from(sharing:share), noq]).
:- dom_impl(_, abs_sort/2, [from(sharing:share), noq]).
:- dom_impl(_, extend/5, [from(sharing:share), noq]).
:- dom_impl(_, less_or_equal/2, [from(sharing:share), noq]).
:- dom_impl(_, glb/3, [from(sharing:share), noq]).
:- dom_impl(_, input_interface/4, [from(sharing:share), noq]).
:- dom_impl(_, input_user_interface/5, [from(sharing:share), noq]).
:- dom_impl(_, asub_to_native/5, [from(sharing:share), noq]).
:- dom_impl(_, unknown_call/4, [from(sharing:share), noq]).
:- dom_impl(_, unknown_entry/3, [from(sharing:share), noq]).
:- dom_impl(_, empty_entry/3, [from(sharing:share), noq]).
% :- dom_impl(_, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub), [from(sharing:share), noq]).

%------------------------------------------------------------------------%
% This file implements the same functions than sharing.pl but the        |
% functions call_to_entry and exit_to_prime are developed based on the   |
% amgu.                                                                  |
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Non-Redundant: the non-redundant version is not working because the    |
% semantics of the builtins must be redefined.                           |
%------------------------------------------------------------------------
% The meaning of the variables are defined in sharing.pl                 |
%------------------------------------------------------------------------%

:- doc(bug,"1. The builtin ==/2 is defined but it is not used. For 
       its use, comment it out in special_builtin.").
:- doc(bug,"2. The builtins read/2 and length/2 are used in a simple
       way. In order to use more complex definitions, comment it in 
       special_builtin.").
:- doc(bug,"3. The non-redundant version is not working because the 
       semantics of the builtins has not been defined yet.").

:- use_module(library(terms_vars),     [varset/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(library(sets)).
:- use_module(library(lsets)).
:- use_module(domain(s_grshfr),        [projected_gvars/3]).
:- use_module(domain(share_amgu_sets), [delete_vars_from_list_of_lists/3]).

:- use_module(library(lists), [list_to_list_of_lists/2, append/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(domain(share_amgu_aux)).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,?)
%-------------------------------------------------------------------------
:- export(call_to_entry/9).
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
     variant(Sg,Head),!,
     ExtraInfo = yes,
     copy_term((Sg,Proj),(NewSg,NewProj)),
     Head = NewSg,
     sharing:abs_sort(NewProj,Temp),
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp,Entry).
call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,ExtraInfo):- !,
     ExtraInfo = no,
     list_to_list_of_lists(Fv,Entry).
call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
     projected_gvars(Proj,Sv,Gv_Call),
     augment_asub(Proj,Hv,ASub),     
     peel_equations(Sg,Head,Eqs),
     amgu_iterate(Eqs,star,ASub,Result),
     sharing:project(Sg,Hv,not_provided_HvFv_u,Result,Entry0),
     augment_asub(Entry0,Fv,Entry),
     ExtraInfo = (Eqs,Gv_Call),!.
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).

%------------------------------------------------------------------------%
% amgu_iterate(+,+,+,-)
% amgu_iterate(Eqs,Flag,ASub0,ASub)
% For each equation in Eqs, it performs the amgu.                        %
%------------------------------------------------------------------------%

amgu_iterate([],_,ASub, ASub).
amgu_iterate([(X,Ts)|Eqs],Flag,ASub, ASub2):-
     amgu(X,Ts,Flag,ASub,ASub1),
     amgu_iterate(Eqs,Flag,ASub1, ASub2).

%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% amgu(+,+,+,-)
% amgu(Sg,Head,ASub,AMGU)
% @var{AMGU} is the abstract unification between @var{Sg} and @var{Head}.%
%------------------------------------------------------------------------%
:- export(amgu/4).
:- dom_impl(_, amgu/4, [noq]).
amgu(Sg,Head,ASub,AMGU):-
    peel_equations(Sg,Head,Eqs),
    amgu_iterate(Eqs,star,ASub,AMGU),!.

%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% augment_asub(+,+,-)
%-------------------------------------------------------------------------

:- export(augment_asub/3).
:- dom_impl(_, augment_asub/3, [noq]).
augment_asub(ASub,[],ASub).
augment_asub(ASub,Vars,ASub1):-
    sharing:abs_sort(ASub,SASub),
    sort(Vars,SVars),
    augment_asub_(SASub,SVars,ASub0),
    sharing:abs_sort(ASub0,ASub1).

augment_asub_(ASub,[],ASub).
augment_asub_(ASub,[H|T],[[H]|ASub0]):-
    augment_asub_(ASub,T,ASub0).

%------------------------------------------------------------------------%
%                      ABSTRACT Extend_two_asub                          %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% augment_two_asub(+,+,-)
%-------------------------------------------------------------------------
:- export(augment_two_asub/3).
:- dom_impl(_, augment_two_asub/3, [noq]).
augment_two_asub([],ASub1,ASub1):-!.
augment_two_asub(ASub0,[],ASub0):-!.
augment_two_asub(ASub0,ASub1,ASub):-
    append(ASub0,ASub1,ASub_u),
    sharing:abs_sort(ASub_u,ASub),!. % TODO: cut in the wrong place
       
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,-)                                                 %
%-------------------------------------------------------------------------

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,Flag,Prime):-  
    Flag == yes, !,
    sharing:project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewHead,NewPrime)),
    Sg = NewHead,
    sharing:abs_sort(NewPrime,Prime).
exit_to_prime(_,[],_,_,_,_,[]):- !.
exit_to_prime(Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo= (Equations,Gv_Call),
    augment_asub(Exit,Sv,ASub),     
    amgu_iterate(Equations,star, ASub, Prime0),
    sharing:project(Sg,Sv,not_provided_HvFv_u,Prime0,Prime1),
    % groundness propagation from call_to_entry
    ord_split_lists_from_list(Gv_Call,Prime1,_,Prime).

%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ) :-
% exit_to_prime
    augment_asub(Call,Hv,ASub),
    peel_equations(Sg, Head,Equations),
    amgu_iterate(Equations,star,ASub,ASub1),
    sharing:project(Sg,Sv,not_provided_HvFv_u,ASub1,Prime),
% extend
    delete_vars_from_list_of_lists(Hv,ASub1,Succ0),
    sort_list_of_lists(Succ0,Succ),!.       
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom'). 

%-------------------------------------------------------------------------
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%-------------------------------------------------------------------------

call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime
    augment_asub(Call,Hv,ASub),
    peel_equations(Sg, Head,Equations),
    amgu_iterate(Equations,star,ASub,ASub1),
    sharing:project(Sg,Sv,not_provided_HvFv_u,ASub1,Prime).   

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%
% special_builtin(+,+,+,-,-)                                             |
% special_builtin(SgKey,Sg,Subgoal,Type,Condvars)                        |
% Satisfied if the builtin does not need a very complex action. It       |
% divides builtins into groups determined by the flag returned in the    |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) ground : if the builtin makes all variables ground whithout        |
%     imposing any condition on the previous freeness values of the      |
%     variables                                                          |
% (2) bottom : if the abstract execution of the builtin returns bottom   |
% (3) unchanged : if we cannot infer anything from the builtin, the      |
%     substitution remains unchanged and there are no conditions imposed |
%     on the previous freeness values of the variables.                  |
% (4) some: if it makes some variables ground without imposing conditions|
% (5) Sgkey: special handling of some particular builtins                |
%-------------------------------------------------------------------------
:- dom_impl(_, special_builtin/5, [noq]).
special_builtin('read/2',read(X,Y),_,'recorded/3',p(Y,X)).
special_builtin('length/2',length(_X,Y),_,some,[Y]).
special_builtin('==/2',_,_,_,_):- !, fail.
special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
    sharing:special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

%-------------------------------------------------------------------------
% success_builtin(+,+,+,+,+,-)
% success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ)
% Obtains the success for some particular builtins:                      |
%  * If Type = ground, it updates Call making all vars in Sv_u ground    |
%  * If Type = bottom, Succ = '$bottom'                                  |
%  * If Type = unchanged, Succ = Call                                    |
%  * If Type = some, it updates Call making all vars in Condv ground     |
%  * Otherwise Type is the SgKey of a particular builtin for each the    |
%    Succ is computed                                                    |
%-------------------------------------------------------------------------
:- dom_impl(_, success_builtin/6, [noq]).
success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
    varset(X,Varsx),
    projected_gvars(Call,Varsx,Vars),Vars == Varsx,!,
    varset(Y,Varsy),
    ord_split_lists_from_list(Varsy,Call,_Intersect,Succ).
success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
    nonvar(Y),
    Y = [Z|W],
    varset(W,Varsy),
    projected_gvars(Call,Varsy,Vars),Vars == Varsy,!,
    varset((X,Z),Varsx),
    ord_split_lists_from_list(Varsx,Call,_Intersect,Succ).
success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
    var(X), var(Y),!,
    sort(Sv_u,Sv),
    sharing:extend(not_provided_Sg,[Sv],Sv,Call,Succ).
success_builtin('=../2',Sv_u,p(X,Y),_,Call,Succ):-
%%      ( var(Y) ; Y = [_|_] ), !,
%%      ( var(X) -> Term=[g|X] ; X=..Term ),
    ( var(Y) -> G=g ; Y = [G|_] ), !,
    ( var(X) -> Term=[G|X] ; X=..Term ),
    sort(Sv_u,Sv),
    sharing:project(not_provided_Sg,Sv,not_provided_HvFv_u,Call,Proj),
    call_to_success_builtin('=/2','='(Term,Y),Sv,Call,Proj,Succ).
success_builtin('=../2',_Sv_u,_,_,_Call,'$bottom'):- !.
success_builtin(copy_term,_Sv_u,p(X,Y),_,Call,Succ):-
    varset(X,VarsX),
    sharing:project(not_provided_Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    sort_list_of_lists(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    sharing:project(not_provided_Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    merge(ProjectedY,ProjectedNewX,TempProjected),
    merge(ProjectedNewX,Call,TempCall),
    call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                            TempCall,TempProjected,Temp_success),
    merge_list_of_lists(Call,VarsCall),
    sharing:project(not_provided_Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ),
    !. % TODO: move cut somewhere else? (JF)
success_builtin(findall,_Sv_u,p(X,Z),HvFv_u,Call,Succ):-
    varset(X,Varsx),
    projected_gvars(Call,Varsx,Vars),Vars == Varsx,!,
    varset(Z,Varsz),
    sharing_amgu:success_builtin(ground,Varsz,_any,HvFv_u,Call,Succ).
success_builtin(findall,_Sv_u,_,_HvFv_u,Call,Call):- !.
%
success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ):-
    sharing:success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ).

%-------------------------------------------------------------------------
% call_to_success_builtin(+,+,+,+,+,-)
% call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ)
% Handles those builtins for which computing Prime is easier than Succ   %
%-------------------------------------------------------------------------
:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom').
call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
    call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
call_to_success_builtin('expand_term/2',expand_term(X,Y),Sv,Call,Proj,Succ):- 
    call_to_success_builtin('arg/3',arg(1,Y,X),Sv,Call,Proj,Succ).
call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
    call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ).
call_to_success_builtin('arg/3',arg(X,Y,Z),_,Call,Proj,Succ):- 
    varset(X,OldG),
    ord_split_lists_from_list(OldG,Call,_Intersect,TempCall),
    Sg = p(Y,Z),
    Head = p(f(A,_B),A),
    varset(Sg,Sv),
    varset(Head,Hv),
    sharing:project(not_provided_Sg,Sv,not_provided_HvFv_u,TempCall,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempCall,Proj,_Prime,Succ). % TODO: add some ClauseKey?

%------------------------------------------------------------------------%
%            Intermediate Functions                                      |
%------------------------------------------------------------------------%

%% obtain_groundness_call(Proj,Sv,Gv):-
%%      merge_list_of_lists(Proj,Vars_Proj),
%%      ord_subtract(Sv,Vars_Proj,Gv).

