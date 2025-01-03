:- module(shfrlin_amgu, [], [assertions, modes_extra]).

:- doc(title, "amgu-based sharing+freeness+linearity (abstract domain)").
:- doc(author, "Jorge Navas").
:- doc(copyright,"Copyright @copyright{} 2006-2019 The Ciao Development Team").
:- doc(stability, prod).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(shfrlin_amgu, [default]).

% infers(ground/1, rtcheck).
% infers(mshare/1, rtcheck).
% infers(var/1, rtcheck).
% infers(linear/1, rtcheck).

:- doc(module,"
This file implements the domain dependent abstract functions           
`sharing`+`freeness`+`linearity`. The functions `call2entry` and `exit2prime` are
defined based on `amgu`.

@begin{note}
The meaning of the variables are partially defined in `sharefree.pl`.     
@end{note}
").

:- doc(bug,"1. The builtins do not use the linearity info."). 
:- doc(bug,"2. The extend function does not use linearity info."). 
     
:- use_module(library(terms_vars),     [varset/2, varset0/2]).
:- use_module(library(sort),           [sort/2]).
:- use_module(library(sets)).
:- use_module(library(lists), [list_to_list_of_lists/2]).
:- use_module(library(terms_check), [variant/2]).

:- use_module(domain(sharefree), [
    compute_lub_el/3,
    empty_entry/3,
    extend/5,
    glb/3,
    obtain_info/4,
    input_interface/4,
    input_user_interface/5,
    less_or_equal/2,
    project/5,
    abs_sort/2,
    unknown_call/4,
    unknown_entry/3]).
:- use_module(domain(sharefree), [
    update_lambda_sf/5,
    values_equal/3,
    change_values_if_f/4,
    obtain_prime_var_var/3,
    product/8]).
:- use_module(domain(sharefree_amgu), [
    call_to_success_builtin/6,
    augment_asub/3,
    special_builtin/5,
    success_builtin/6,
    sharefree_delete_variables/3]).
:- use_module(domain(share_aux), [if_not_nil/4,list_ground/2]).
:- use_module(domain(sharefree_amgu_aux), [
    filter_freeness_with_call/3,
    peel_equations_frl/3,
    unmap_freeness_list/2]).

:- use_module(domain(s_grshfr), [
    member_value_freeness/3,
    change_values_insert/4,
    var_value/3]).
:- use_module(domain(shfrlin_amgu_aux),
    [shfrlin_amgu_iterate/3, shfrlin_amgu_update_fr_lin/3]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred call_to_entry(+,+,+,+,+,+,+,-,?).

:- dom_impl(_, call_to_entry/9, [noq]).
call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
     variant(Sg,Head),!,
     Flag = yes,
     copy_term((Sg,Proj),(NewTerm,NewProj)),
     Head = NewTerm,
     abs_sort(NewProj,(Temp_sh,Temp_fr,Temp_lin)),
     change_values_insert(Fv,Temp_fr,Entry_fr,f),       
     list_to_list_of_lists(Fv,Temp1),
     merge(Temp1,Temp_sh,Entry_sh),
     merge(Temp_lin,Fv,Entry_lin),
     Entry = (Entry_sh,Entry_fr,Entry_lin).
call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
     list_to_list_of_lists(Fv,Entry_sh),
     change_values_insert(Fv,[],Entry_fr,f),
     member_value_freeness(Entry_fr,Entry_lin,f),
     Entry = (Entry_sh,Entry_fr,Entry_lin).
call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Project,Entry,ExtraInfo):-
     Project = (_,F2,_),
     peel_equations_frl(Sg, Head,Equations),
     augment_asub(Project,Hv,ASub),     
     shfrlin_amgu_iterate(Equations,ASub,ASub0),
     shfrlin_amgu_update_fr_lin(ASub0,Hv,ASub1),
     project(Sg,Hv,not_provided_HvFv_u,ASub1,Entry0),
     augment_asub(Entry0,Fv,Entry),
     ExtraInfo = (Equations,F2),!.
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',_).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Exit to Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred exit_to_prime(+,+,+,+,+,?,-).

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_,_,_,_,'$bottom',_,'$bottom'):-!.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
     project(Sg,Hv,not_provided_HvFv_u,Exit,(BPrime_sh,BPrime_fr,BPrime_lin)),
     copy_term((Head,(BPrime_sh,BPrime_fr,BPrime_lin)),(NewTerm,NewPrime)),
     Sg = NewTerm,
     abs_sort(NewPrime,Prime).     
exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
     list_ground(Sv,Prime_fr),
     member_value_freeness(Prime_fr,Prime_lin,f),
     Prime = ([],Prime_fr,Prime_lin).
exit_to_prime(Sg,_Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
     ExtraInfo = (Equations,Freeness_Call),     
     filter_freeness_with_call(Sv,Freeness_Call,New_Sv),
     augment_asub(Exit,New_Sv,ASub),     
     shfrlin_amgu_iterate(Equations,ASub,ASub0),
     shfrlin_amgu_update_fr_lin(ASub0,Sv,ASub1),
     project(Sg,Sv,not_provided_HvFv_u,ASub1,Prime).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred extend(+Sg,+Prime,+Sv,+Call,-Succ).

:- redefining(extend/5).
:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
extend(Sg,Prime,Sv,Call,(Succ_sh,Succ_fr,Succ_lin)):-
    Call = (Call_sh,Call_fr,Call_lin),
    Prime = (Prime_sh,Prime_fr,Prime_lin),
    %% sharing + freeeness
    sharefree:extend(Sg,(Prime_sh,Prime_fr),Sv,(Call_sh,Call_fr),(Succ_sh,Succ_fr)),
    %% linearity
    ord_subtract(Call_lin,Sv,Call_lin_not_rel),
    member_value_freeness(Succ_fr,Succ_gr,g),
    ord_subtract(Call_lin_not_rel,Succ_gr,Call_lin_not_rel0),
    ord_union(Prime_lin,Call_lin_not_rel0,Succ_lin).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                            ABSTRACT AMGU                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred amgu(+Sg,+Head,+ASub,-AMGU)
   # "`AMGU` is the abstract unification between `Sg` and `Head`.".

:- dom_impl(_, amgu/4, [noq]).
amgu(Sg,Head,ASub,AMGU):-
    peel_equations_frl(Sg, Head,Eqs),
    shfrlin_amgu_iterate(Eqs,ASub,AMGU),!.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend_Asub                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred augment_asub(+,+,-).

:- redefining(augment_asub/3).
:- dom_impl(_, augment_asub/3, [noq]).
augment_asub('$bottom',_,'$bottom'):-!.
augment_asub(SHFL,[],SHFL):-!.
augment_asub((Sh,F,L),Vars,(NewSh,NewF,NewL)):-
    ord_union(L,Vars,NewL),
    sharefree_amgu:augment_asub((Sh,F),Vars,(NewSh,NewF)).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                         ABSTRACT Project                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred project(+,+,+,+,-).

:- redefining(project/5).
:- dom_impl(_, project/5, [noq]).
project(_Sg,_Vars,_HvFv_u,'$bottom','$bottom') :- !.
project(Sg,Vars,HvFv_u,(Sh,F,L),(Sh_proj,F_proj,L_proj)):-
    sharefree:project(Sg,Vars,HvFv_u,(Sh,F),(Sh_proj,F_proj)),
    ord_intersection(L,Vars,L_proj).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                         ABSTRACT Sort                                  %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred abs_sort(+,-).

:- redefining(abs_sort/2).
:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom').
abs_sort((Sh,F,L),(Sh_s,F_s,L_s)):-
    sharefree:abs_sort((Sh,F),(Sh_s,F_s)),
    sort(L,L_s).

:- pred glb(+ASub0,+ASub1,-Glb).

:- dom_impl(_, glb/3, [noq]).
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb((Sh1,Fr1,Lin1),(Sh2,Fr2,Lin2),Glb):-
    sharefree:glb((Sh1,Fr1),(Sh2,Fr2),Glb0),
    ( Glb0 == '$bottom' 
    -> 
      Glb = '$bottom'
    ;
      ord_union(Lin1,Lin2,Lin),
      Glb0= (Sh,Fr),
      Glb = (Sh,Fr,Lin)
    ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- dom_impl(_, call_to_success_fact/9, [noq]).
:- pred call_to_success_fact/9
   #"Specialized version of call_to_entry + exit_to_prime + extend for facts.".

call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,_Proj,Prime,Succ) :-
% exit_to_prime   -------------------------------------------------------
    augment_asub(Call,Hv,ASub),  
    peel_equations_frl(Sg, Head,Equations),
    shfrlin_amgu_iterate(Equations,ASub,ASub0),
    ASub = (_,Vars,_),        
    unmap_freeness_list(Vars,Vars0),
    shfrlin_amgu_update_fr_lin(ASub0,Vars0,ASub1),
    project(Sg,Sv,not_provided_HvFv_u,ASub1,Prime),
% extend    --------------------------------------------------------------
    delete_variables(Hv,ASub1,Succ),!.
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj, '$bottom','$bottom').

delete_variables(Vars,(Sh,Fr,L),(New_Sh,New_Fr,NewL)):-
    sharefree_delete_variables(Vars,(Sh,Fr),(New_Sh,New_Fr)),
    delete_variables_lin(L,Vars,NewL).

delete_variables_lin([],_,[]).
delete_variables_lin([X|Xs],Vars,Res):-
    ord_member(X,Vars),!,
    delete_variables_lin(Xs,Vars,Res).
delete_variables_lin([X|Xs],Vars,[X|Res]):-
    delete_variables_lin(Xs,Vars,Res).

:- pred call_to_prime_fact/6
   #
"Specialised version of `call_to_success_fact/7` in order to allow          
the computation of the prime, the composition and then the extension   
Note that if the success is computed (instead of the prime) and then   
we compose the information and project it, we can loose information    
since the extension is the step in which more information is lost      
".

call_to_prime_fact(Sg,Hv,Head,Sv,Call,Prime) :-
% exit_to_prime    -------------------------------------------------------
    augment_asub(Call,Hv,Exit),
    Call = (_Sh,Extra_Info,_),
    exit_to_prime(Sg,Hv,Head,Sv,Exit,Extra_Info,Prime), !.
call_to_prime_fact(_Sg,_Hv,_Head,_Sv,'$bottom','$bottom').

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

:- dom_impl(_, special_builtin/5, [noq]).
:- pred special_builtin(+SgKey,+Sg,+Subgoal,-Type,---Condvars).

special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
    sharefree_amgu:special_builtin(SgKey,Sg,Subgoal,Type,Condvars).
    
:- dom_impl(_, success_builtin/6, [noq]).
:- pred success_builtin(+Type,+Sv_u,?Condv,+HvFv_u,+Call,-Succ).

% success_builtin(arg,_,p(X,Y,Z),_,Call,Succ):-
%       Call = (Call_sh,Call_fr,Call_lin),
%       varset(X,OldG),
%       update_lambda_non_free(OldG,Call_fr,Call_sh,Temp_fr,Temp_sh),
%       var_value(Temp_fr,Y,Value),
%       Value \== f,!,
%       Sg = p(Y,Z),
%       Head = p(f(A,_B),A),
%       varset(Sg,Sv),
%       varset(Head,Hv),
%       TempASub = (Temp_sh,Temp_fr),
%       sharefree:project(not_provided_Sg,Sv,not_provided_HvFv_u,TempASub,Proj),
%       call_to_success_fact(Sg,Hv,Head,not_provided,Sv,TempASub,Proj,_,Succ). % TODO: add some ClauseKey?
% success_builtin(arg,_,_,_,'$bottom').
success_builtin(exp,_,Sg,_,Call,Succ):- !,
    Head = p(A,f(A,_B)),
    varset(Sg,Sv),
    varset(Head,Hv),
    project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
success_builtin(exp,_,_,_,_,'$bottom'):- !.
% success_builtin(copy_term,_,p(X,Y),_,Call,Succ):-
%       varset(X,VarsX),
%       sharefree:project(not_provided_Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
%       copy_term((X,ProjectedX),(NewX,NewProjectedX)),
%       sharefree:abs_sort(NewProjectedX,ProjectedNewX),
%       varset(NewX,VarsNewX),
%       varset(Y,VarsY),
%       merge(VarsNewX,VarsY,TempSv),
%       sharefree:project(not_provided_Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
%       ProjectedY = (ShY,FrY),
%       ProjectedNewX = (ShNewX,FrNewX),
%       merge(ShY,ShNewX,TempSh),
%       merge(FrY,FrNewX,TempFr),
%       Call = (ShCall,FrCall),
%       merge(ShNewX,ShCall,TempCallSh),
%       merge(FrNewX,FrCall,TempCallFr),
%       call_to_success_builtin('=/2','='(NewX,Y),TempSv,
%                     (TempCallSh,TempCallFr),(TempSh,TempFr),Temp_success),
%       collect_vars_freeness(FrCall,VarsCall),
%       sharefree:project(not_provided_Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ):-
    Call = (Sh,Fr,Lin),
    ord_subtract(Lin,Sv_u,Lin_not_rel),     
    sharefree_amgu:success_builtin(Type,Sv_u,Condv,HvFv_u,(Sh,Fr),Succ0),
    ( Succ0 == '$bottom' 
    ->
      Succ = '$bottom'
    ;
      Succ0 = (Sh_succ,Fr_succ),
      member_value_freeness(Fr_succ,L_succ0,f),
      ord_union(L_succ0,Lin_not_rel,L_succ),
      Succ= (Sh_succ,Fr_succ,L_succ)
    ).

:- pred call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)
   # "Handles those builtins for which computing `Prime` is easier than `Succ`.".

:- redefining(call_to_success_builtin/6).
:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,(_,Proj_fr,_),Succ):-
    varset(X,VarsX), values_equal(VarsX,Proj_fr,g), !,
    Call = (Call_sh,Call_fr,Call_lin),
    ord_subtract(Call_lin,Sv,Call_lin_not_rel),
    ord_subtract(Sv,VarsX,VarsY),
    update_lambda_sf(VarsY,Call_fr,Call_sh,Succ_fr,Succ_sh),
    member_value_freeness(Succ_fr,Succ_lin0,f),
    ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin),
    Succ = (Succ_sh,Succ_fr,Succ_lin).
call_to_success_builtin('=/2','='(_X,Y),Sv,Call,(_,Proj_fr,_),Succ):-
    varset(Y,VarsY), values_equal(VarsY,Proj_fr,g), !,
    Call = (Call_sh,Call_fr,Call_lin),
    ord_subtract(Call_lin,Sv,Call_lin_not_rel),
    ord_subtract(Sv,VarsY,VarsX),
    update_lambda_sf(VarsX,Call_fr,Call_sh,Succ_fr,Succ_sh),
    member_value_freeness(Succ_fr,Succ_lin0,f),
    ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin),
    Succ = (Succ_sh,Succ_fr,Succ_lin).
call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    var(X),var(Y), !,
    (
        X==Y -> Call=Succ
    ;
        Proj = (_,Proj_fr,_),
        Call = (Sh_call,Fr_call,Call_lin),
        ord_subtract(Call_lin,Sv,Call_lin_not_rel),
        obtain_prime_var_var(Proj_fr,(Sh_call,Fr_call),(Succ_sh,Succ_fr)),
        member_value_freeness(Succ_fr,Succ_lin0,f),
        ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin),
        Succ = (Succ_sh,Succ_fr,Succ_lin)
    ).
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
    var(X), !,
    Proj = (Proj_sh,Proj_fr,_),     
    ord_subtract(Sv,[X],VarsY),
    var_value(Proj_fr,X,ValueX),
    product(ValueX,X,VarsY,Sv,Proj_sh,Proj_fr,Prime_sh,Prime_fr),
    member_value_freeness(Prime_fr,Prime_lin,f),
    extend(not_provided_Sg,(Prime_sh,Prime_fr,Prime_lin),Sv,Call,Succ).
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
    Proj = (_Sh,Fr,_),
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
    Call = (Call_Sh,Call_fr,_),
    change_values_if_f([Z],Call_fr,Temp_fr,nf),
    varset([X,Y],Sv),
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,
    varset(Xterm,Vars),
    Proj = (Sh,Fr,_),
    change_values_if_f([Z],Fr,TFr,nf),
    member_value_freeness(Temp_fr,Temp_lin,f),
    member_value_freeness(TFr,Lin,f),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,(Call_Sh,Temp_fr,Temp_lin),(Sh,TFr,Lin),_Prime,Succ). % TODO: add some ClauseKey? 
call_to_success_builtin(SgKey,Sg,Sv,Call,Proj,(Succ_sh,Succ_fr,Succ_lin)):- 
    Call = (Call_sh,Call_fr,Call_lin),
    ord_subtract(Call_lin,Sv,Call_lin_not_rel),
    Proj = (Proj_sh,Proj_fr,_),
    sharefree_amgu:call_to_success_builtin(SgKey,Sg,Sv,(Call_sh,Call_fr),
                                           (Proj_sh,Proj_fr),(Succ_sh,Succ_fr)),
    member_value_freeness(Succ_fr,Succ_lin0,f),
    ord_union(Succ_lin0,Call_lin_not_rel,Succ_lin).

:- pred compute_lub(+,-).

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([X],X):- !.
compute_lub([ASub1,ASub2|Xs],Lub):-
    compute_lub_el(ASub1,ASub2,ASubLub),
    compute_lub([ASubLub|Xs],Lub).

:- pred compute_lub_el(+,+,-).

:- redefining(compute_lub_el/3).
compute_lub_el('$bottom',ASub,ASub):-!.
compute_lub_el(ASub,'$bottom',ASub):-!.
compute_lub_el((Sh1,Fr1,Lin1),(Sh2,Fr2,Lin2),ASub):-
    sharefree:compute_lub_el((Sh1,Fr1),(Sh2,Fr2),(Sh_ASub,Fr_ASub)),
    ord_intersection(Lin1,Lin2,Lin_ASub),
    ASub = (Sh_ASub,Fr_ASub,Lin_ASub).

:- dom_impl(_, less_or_equal/2, [noq]).
:- pred less_or_equal(+,+)
   # "Succeeds if ASub1 is more general or equal to ASub0.".

less_or_equal('$bottom',_ASub):- !.
less_or_equal((Sh0,Fr0,Lin0),(Sh1,Fr1,Lin1)):-
    sharefree:less_or_equal((Sh0,Fr0),(Sh1,Fr1)),!,
    ord_subset(Lin0,Lin1).

:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(?InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   #
"Obtaining the abstract substitution for `Sh`+`Fr`+`lin` from the user        
supplied information just consists in taking the `Sharing` first and the 
`var(Fv)` element of `InputUser`, and construct from them the `Freeness` and 
the `Linearity`.                                                         
".

input_user_interface((Sh,Vars,_),Qv,(Call_sh,Call_fr,Call_lin),Sg,MaybeCallASub):-
    sharefree:input_user_interface((Sh,Vars),Qv,(Call_sh,Call_fr),Sg,MaybeCallASub),
    member_value_freeness(Call_fr,Call_lin,f).

%------------------------------------------------------------------------%

:- dom_impl(_, obtain_info/4, [noq]).
obtain_info(Prop,Vars,(Sh,Fr,_Lin),Info) :- sharefree:obtain_info(Prop,Vars,(Sh,Fr),Info).

:- pred input_interface(+InputUser,?Kind,?ASub0,?ASub).

:- dom_impl(_, input_interface/4, [noq]).
input_interface(linear(X),perfect,(Sh,Fr,Lin0),(Sh,Fr,Lin)):-
    myunion(Lin0,X,Lin).
input_interface(free(X),perfect,(Sh,Fr0,Lin0),(Sh,Fr,Lin)):-
    var(X),
    myinsert(Fr0,X,Fr),
    myinsert(Lin0,X,Lin).
input_interface(Info,Kind,(Sh0,Fr0,Lin),(Sh,Fr,Lin)):-
    sharefree:input_interface(Info,Kind,(Sh0,Fr0),(Sh,Fr)).

myunion(Lin0,X,Lin):-
    var(Lin0),!,
    sort(X,Lin).
myunion(Lin0,X,Lin):-
    sort(X,Xs),
    ord_union(Lin0,Xs,Lin).
myinsert(Fr0,X,Fr):-
    var(Fr0), !,
    Fr = [X].
myinsert(Fr0,X,Fr):-
    insert(Fr0,X,Fr).

:- pred asub_to_native(+ASub,+Qv,+OutFlag,-ASub_user,-Comps)
   #
"The user friendly format consists in extracting the ground variables, 
free variables, and linear variables.
".

:- dom_impl(_, asub_to_native/5, [noq]).
asub_to_native((Sh,Fr,L),_Qv,_OutFlag,Info,[]):-
    if_not_nil(Sh,sharing(Sh),Info,Info0),
    member_value_freeness(Fr,Fv,f),
    if_not_nil(Fv,free(Fv),Info0,Info1),
    member_value_freeness(Fr,Gv,g),
    if_not_nil(Gv,ground(Gv),Info1,Info2),
    if_not_nil(L,linear(L),Info2,[]).

% asub_to_native((Sh,Fr,_L),_Qv,Info):-
%       if_not_nil(Sh,sharing(Sh),Info,Info0),
%       member_value_freeness(Fr,Fv,f),
%       if_not_nil(Fv,free(Fv),Info0,Info1),
%       member_value_freeness(Fr,Gv,g),
%       if_not_nil(Gv,ground(Gv),Info1,[]).

:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg,+Vars,+Call,-Succ)
   #
"Obtained by selecting those sets in `Call` for which at least a variable 
in `Vars` appears, making the star of those sets, and adding the sets    
with empty intersection with `Vars`. In freeness, all variables related
to `Vars` are `nf`, and in `linearity`, subtract from `Call_lin` all variables 
not related to `Vars` and make the union between the related `Call_lin`    
with free variables returned by freeness.                              
".

unknown_call(_Sg,_Vars,'$bottom','$bottom') :- !.
unknown_call(Sg,Vars,(Call_sh,Call_fr,Call_lin),Succ):-
    sharefree:unknown_call(Sg,Vars,(Call_sh,Call_fr),(Succ_sh,Succ_fr)),
    ord_subtract(Call_lin,Vars,Call_lin_not_rel),
    member_value_freeness(Succ_fr,Succ_lin0,f),
    ord_intersection(Succ_lin0,Vars,Succ_lin1),
    ord_union(Call_lin_not_rel,Succ_lin1,Succ_lin),
    Succ = (Succ_sh,Succ_fr,Succ_lin).

:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg,+Qv,-Call)
   #
"The top value in `Sh` for a set of variables is the powerset, in `Fr` is  
`X`/`nf` forall `X` in the set of variables, and in no variable is linear.   
".

unknown_entry(Sg,Qv,(Call_sh,Call_fr,[])):-
    sharefree:unknown_entry(Sg,Qv,(Call_sh,Call_fr)).

:- dom_impl(_, empty_entry/3, [noq]).
:- pred empty_entry(+Sg,+Qv,-Entry)
   #
"The empty value in `Sh` for a set of variables is the list of singletons,
in `Fr` is `X`/`f` forall `X` in the set of variables, and these variables are 
all linear.                                                            
".

empty_entry(Sg,Qv,(Call_sh,Call_fr,Qv)):-
    sharefree:empty_entry(Sg,Qv,(Call_sh,Call_fr)).

