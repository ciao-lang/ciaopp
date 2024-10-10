:- module(sharefree_amgu, [], [assertions, modes_extra]).

:- doc(title, "amgu-based sharing+freeness (abstract domain)").
:- doc(author, "Jorge Navas").
:- doc(copyright,"Copyright @copyright{} 2004-2019 The Ciao Development Team").
:- doc(stability, prod).

:- use_module(domain(sharefree), [
    compute_lub/2,
    less_or_equal/2,
    glb/3,
    obtain_info/4,
    input_interface/4,
    input_user_interface/5,
    asub_to_native/5,
    unknown_call/4,
    unknown_entry/3,
    empty_entry/3,
    call_to_success_builtin/6,
    extend/5,
    project/5,
    abs_sort/2,
    special_builtin/5,
    success_builtin/6
]).
:- include(ciaopp(plai/plai_domain)).
:- dom_def(sharefree_amgu, [default]).
:- dom_impl(_, project/5, [from(sharefree:shfr), noq]).
:- dom_impl(_, compute_lub/2, [from(sharefree:shfr), noq]).
:- dom_impl(_, abs_sort/2, [from(sharefree:shfr), noq]).
:- dom_impl(_, extend/5, [from(sharefree:shfr), noq]).
:- dom_impl(_, less_or_equal/2, [from(sharefree:shfr), noq]).
:- dom_impl(_, glb/3, [from(sharefree:shfr), noq]).
:- dom_impl(_, obtain_info/4, [from(sharefree:shfr), noq]).
:- dom_impl(_, input_interface/4, [from(sharefree:shfr), noq]).
:- dom_impl(_, input_user_interface/5, [from(sharefree:shfr), noq]).
:- dom_impl(_, asub_to_native/5, [from(sharefree:shfr), noq]).
:- dom_impl(_, unknown_call/4, [from(sharefree:shfr), noq]).
:- dom_impl(_, unknown_entry/3, [from(sharefree:shfr), noq]).
:- dom_impl(_, empty_entry/3, [from(sharefree:shfr), noq]).

% infers(ground/1, rtcheck).
% infers(mshare/1, rtcheck).
% infers(var/1, rtcheck).

:- doc(module,"
This file implements the same domain-dependent abstract functions than      
`sharefree.pl` but the functions `call_to_entry` and `exit_to_prime` are 
defined based on `amgu`.

@begin{note}
The meaning of the variables is defined in `sharefree.pl`.       
@end{note}
").

:- doc(bug,"1. The builtin ==/2 is defined but it is not used because
       of benchmarks. For its use, comment it out in special_builtin.").
:- doc(bug,"2. The builtins read/2 and length/2 are used in a simple
       way. In order to use more complex definitions, comment it in 
       special_builtin.").
:- doc(bug,"3. The non-redundant version is not working because the 
       semantics of the builtins has not been defined yet.").

:- use_module(library(terms_vars),     [varset/2, varset0/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(library(sets)).
:- use_module(library(lists), [
    list_to_list_of_lists/2
   ]).
:- use_module(library(lsets), [
    closure_under_union/2,
    sort_list_of_lists/2,
    merge_each/3
   ]).
:- use_module(library(terms_check), [variant/2]).

:- use_module(domain(share_amgu_sets), [delete_vars_from_list_of_lists/3]).
:- use_module(domain(s_grshfr),
    [ change_values_if_differ/5,
      collect_vars_freeness/2,
      var_value/3,
      change_values_insert/4]).
:- use_module(domain(share_aux), [list_ground/2]).

:- use_module(domain(sharing), [project/5]).
:- use_module(domain(sharing_amgu), [augment_asub/3]).
:- use_module(domain(sharefree_amgu_aux)).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,?ExtraInfo).

:- export(call_to_entry/9).
:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
     variant(Sg,Head),!,
     Flag = yes,
     copy_term((Sg,Proj),(NewTerm,NewProj)),
     Head = NewTerm,
     sharefree:abs_sort(NewProj,(Temp_sh,Temp_fr)),
     change_values_insert(Fv,Temp_fr,Entry_fr,f),       
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp_sh,Entry_sh),
     Entry = (Entry_sh,Entry_fr).
call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
     list_to_list_of_lists(Fv,Entry_sh),
     change_values_insert(Fv,[],Entry_fr,f),
     Entry = (Entry_sh,Entry_fr).
call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Project,Entry,ExtraInfo):-
     Project = (_,F2),
     peel_equations_frl(Sg, Head,Equations),
     augment_asub(Project,Hv,ASub),     
     sharefree_amgu_iterate(Equations,ASub,(Sh,F)),
     shfr_update_freeness(Sh,F,Hv,F1),
     sharefree:project(Sg,Hv,not_provided_HvFv_u,(Sh,F1),Entry0),
     augment_asub(Entry0,Fv,Entry),
     ExtraInfo = (Equations,F2),!.
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,+ExtraInfo,-Prime).

:- export(exit_to_prime/7).
:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
     sharefree:project(Sg,Hv,not_provided_HvFv_u,Exit,(BPrime_sh,BPrime_fr)),
     copy_term((Head,(BPrime_sh,BPrime_fr)),(NewTerm,NewPrime)),
     Sg = NewTerm,
     sharefree:abs_sort(NewPrime,Prime).     
exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
     list_ground(Sv,Prime_fr),
     Prime = ([],Prime_fr).
exit_to_prime(Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Freeness_Call),     
     filter_freeness_with_call(Sv,Freeness_Call,New_Sv),
     augment_asub(Exit,New_Sv,ASub),     
     sharefree_amgu_iterate(Equations,ASub,(Sh,F)),
     shfr_update_freeness(Sh,F,Sv,F1),
     sharefree:project(Sg,Sv,not_provided_HvFv_u,(Sh,F1),Prime).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred amgu(+Sg,+Head,+ASub,-AMGU)
   # "`AMGU` is the abstract unification between `Sg` and `Head`.".

:- export(amgu/4).
:- dom_impl(_, amgu/4, [noq]).
amgu(Sg,Head,ASub,AMGU):-
    peel_equations_frl(Sg, Head,Eqs),
    sharefree_amgu_iterate(Eqs,ASub,AMGU),!.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred augment_asub(+,+,-).

:- export(augment_asub/3).
:- redefining(augment_asub/3).
:- dom_impl(_, augment_asub/3, [noq]).
augment_asub(SHF,[],SHF) :- !.
augment_asub((Sh,F),Vars,(Sh0,F0)):-
    sharing_amgu:augment_asub(Sh,Vars,Sh0),
    augment_asub0(F,Vars,F0).

:- export(augment_asub0/3).
augment_asub0(F,[],F) :- !.
augment_asub0(F,Vars,F1):-
    sort(F,SF),
    sort(Vars,SVars),
    augment_asub1(SF,SVars,F1).

augment_asub1(F,[],F) :- !.
augment_asub1(F,[H|T],F1):-
    augment_asub1(F,T,F0),
    ord_union(F0,[H/f],F1).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call to Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred call_to_success_fact/9
   # "Specialized version of `call_to_entry` + `exit_to_prime` + `extend` for facts".

:- export(call_to_success_fact/9).
:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ) :-
% exit_to_prime    -------------------------------------------------------
    augment_asub(Call,Hv,ASub),  
    peel_equations_frl(Sg, Head,Equations),
    sharefree_amgu_iterate(Equations,ASub,(Sh,F)),
    ASub = (_,Vars),
    unmap_freeness_list(Vars,Vars0),
    shfr_update_freeness(Sh,F,Vars0,F1),
    ASub1= (Sh,F1),
    sharefree:project(Sg,Sv,not_provided_HvFv_u,ASub1,Prime),
% extend   ---------------------------------------------------------------
    sharefree_delete_variables(Hv,ASub1,Succ),!.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom').

:- export(sharefree_delete_variables/3).
sharefree_delete_variables(Vars,(Sh,Fr),(New_Sh,New_Fr)):-
    delete_vars_from_list_of_lists(Vars,Sh,Sh0),
    sort_list_of_lists(Sh0,New_Sh),
    delete_variables_freeness(Fr,Vars,New_Fr).

delete_variables_freeness([],_,[]).
delete_variables_freeness([X/_|Xs],Vars,Res):-
    ord_member(X,Vars),!,
    delete_variables_freeness(Xs,Vars,Res).
delete_variables_freeness([X/V|Xs],Vars,[X/V|Res]):-
    delete_variables_freeness(Xs,Vars,Res).

%------------------------------------------------------------------------%
% Specialised version of share_call_to_success_fact in order to allow    |
% the computation of the prime, the composition and then the extension   |
% Note that if the success is computed (instead of the prime) and then   |
% we compose the information and project it, we can loose information    |
% since the extension is the step in which more information is lost      |
%------------------------------------------------------------------------%
:- export(call_to_prime_fact/6).
call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime   --------------------------------------------------------
    augment_asub(Call,Hv,Exit),
    Call = (_Sh,Extra_Info),
    exit_to_prime(Sg,Hv,Head,Sv,Exit,Extra_Info,Prime).

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

:- pred special_builtin(+SgKey,+Sg,+Subgoal,-Type,---Condvars).

:- export(special_builtin/5).
:- dom_impl(_, special_builtin/5, [noq]).
special_builtin('read/2',read(X,Y),_,'recorded/3',p(Y,X)).
special_builtin('length/2',length(_X,Y),_,some,[Y]).
special_builtin('==/2',_,_,_,_):- !, fail.
special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
    sharefree:special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
    
:- pred success_builtin(+Type,+Sv_u,?Condv,+HvFv_u,+Call,-Succ).

:- export(success_builtin/6).
:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(arg,_,Sg0,_,Call,Succ):- Sg0=p(X,Y,Z),
    Call = (Call_sh,Call_fr),
    varset(X,OldG),
    update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
    var_value(Temp_fr,Y,Value),
    Value \== f,
    !,
    Sg = p(Y,Z),
    Head = p(f(A,_B),A),
    varset(Sg,Sv),
    varset(Head,Hv),
    TempASub = (Temp_sh,Temp_fr),
    sharefree:project(Sg,Sv,not_provided_HvFv_u,TempASub,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
success_builtin(arg,_,_,_,_,'$bottom') :- !.
success_builtin(exp,_,Sg,_,Call,Succ):-
    Head = p(A,f(A,_B)),
    varset(Sg,Sv),
    varset(Head,Hv),
    sharefree:project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ), % TODO: add some ClauseKey?
    !. % TODO: move cut somewhere else? (JF)
success_builtin(exp,_,_,_,_,'$bottom') :- !.
% there is a new case (general case) in '../2' that should be implemented 
% in this module because it calls call_to_success_builtin 
success_builtin(copy_term,_,Sg,_,Call,Succ):- Sg=p(X,Y),
    varset(X,VarsX),
    sharefree:project(Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    sharefree:abs_sort(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    sharefree:project(Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    ProjectedY = (ShY,FrY),
    ProjectedNewX = (ShNewX,FrNewX),
    merge(ShY,ShNewX,TempSh),
    merge(FrY,FrNewX,TempFr),
    Call = (ShCall,FrCall),
    merge(ShNewX,ShCall,TempCallSh),
    merge(FrNewX,FrCall,TempCallFr),
    call_to_success_builtin('=/2','='(NewX,Y),TempSv,
                (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
    collect_vars_freeness(FrCall,VarsCall),
    sharefree:project(Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ),
    !. % TODO: move cut somewhere else? (JF)
success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ):-
    sharefree:success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ).

:- pred call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)
   # "Handles those builtins for which computing `Prime` is easier than `Succ`".

:- export(call_to_success_builtin/6).
:- redefining(call_to_success_builtin/6).
:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr),Succ):-
    varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
    Call = (Call_sh,Call_fr),
    ord_subtract(Sv,VarsX,VarsY),
    update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr),Succ):-
    varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
    Call = (Call_sh,Call_fr),
    ord_subtract(Sv,VarsY,VarsX),
    update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
    Succ = (Succ_sh,Succ_fr).
call_to_success_builtin('=/2','='(X,Y),_Sv,Call,Proj,Succ):-
    var(X),var(Y), !,
    (
        X==Y -> Call=Succ
    ;
        Proj = (_,Proj_fr),
        obtain_prime_var_var(Proj_fr,Call,Succ)
    ).
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
    var(X), !,
    Proj = (Proj_sh,Proj_fr),       
    ord_subtract(Sv,[X],VarsY),
    var_value(Proj_fr,X,ValueX),
    product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
    Prime= (Prime_sh,Prime_fr),
    sharefree:extend(not_provided_Sg,Prime,Sv,Call,Succ).
call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('=/2',_Sg,_Sv,_Call,_Proj,'$bottom') :- !.
call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):-
    call_to_success_fact('='(X,[Y|Z]),[W],'='(W,W),not_provided,Sv,Call,Proj,_Prime,Succ), % TODO: add some ClauseKey?
    !. % TODO: move cut? (JF)
call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):- 
    call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ),
    !. % TODO: move cut? (JF)
call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    var(X), !,
    Proj = (_Sh,Fr),
    var_value(Fr,X,Val),
    ( Val = f ->
      Succ = '$bottom'
    ; varset([X,Y],Sv),
      copy_term(Y,Yterm),
      varset(Yterm,Vars),
      call_to_success_fact('='(X,Y),Vars,'='(Yterm,Yterm),not_provided,Sv,Call,Proj,_Prime,Succ) % TODO: add some ClauseKey?
    ).
call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ):- 
    functor(X,'.',_), !,
    varset0(X,[Z|_]),
    Call = (Call_Sh,Call_fr),
    change_values_if_f([Z],Call_fr,Temp_fr,nf),
    varset([X,Y],Sv),
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,
    varset(Xterm,Vars),
    Proj = (Sh,Fr),
    change_values_if_f([Z],Fr,TFr,nf),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_Sh,Temp_fr),(Sh,TFr),_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ):- 
    sharefree:call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,Succ).

%------------------------------------------------------------------------%
%                     Intermediate Functions                             %
%------------------------------------------------------------------------%

:- use_module(domain(sharefree), [
    update_lambda_non_free/5,
    values_equal/3,
    change_values/4,
    change_values_if_f/4,
    update_lambda_sf/5,
    insert_each/3,
    take_coupled/3,
    obtain_prime_var_var/3
    ]).

%-------------------------------------------------------------------------

product(f,X,VarsY,_,Sh,Lda_fr,Prime_sh,Prime_fr):-
    sharing:project(not_provided_Sg,VarsY,not_provided_HvFv_u,Sh,Temp), % TODO: why not project_share/3 like in sharefree.pl?
    insert_each(Temp,X,Temp1),
    sort_list_of_lists(Temp1,Prime_sh),
    take_coupled(Sh,[X],Coupled),
    change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
product(nf,X,VarsY,Sv,Sh,Lda_fr,Prime_sh,Prime_fr):-
    sharing:project(not_provided_Sg,VarsY,not_provided_HvFv_u,Sh,Temp), % TODO: why not project_share/3 like in sharefree.pl?
    closure_under_union(Temp,Temp1),
    merge_each([X],Temp1,Temp2),
    sort(Temp2,Prime_sh),
    take_coupled(Sh,Sv,Coupled),
    change_values_if_f(Coupled,Lda_fr,Prime_fr,nf).
