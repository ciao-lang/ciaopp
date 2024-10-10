:- module(gr, [], [assertions,regtypes,modes_extra,datafacts,nativeprops]).

:- doc(title,"gr: simple groundness (abstract domain)").
:- doc(author, "Claudio Vaucheret").
:- doc(stability, beta).

% infers(ground/1, rtcheck).

:- doc(module,"

This module implements the abstract operations of a simple groundness
domain for the PLAI framework of abstract interpretation.  An abstract
substitution is a list of `Var`/`Mode` elements, where
`Var` is a variable and `Mode` is `any`, `g` or `ng`. 

The abstract domain lattice is:

@begin{verbatim}
             any
            /  \\
           /    \\
  (ground) g     ng (not ground)
           \\    /
            \\  /
          $bottom
@end{verbatim}

").

% NOTE: The abstract value 'ng' WILL NOT be used
%
% In practice, the abstract value 'ng' will not be used and we will
% use 'any' instead, so the lattice would be like this:
%             any
%              |
%              |
%   (ground)   g
%              |
%              |
%           $bottom
%
% The reason for this is that this domain does not keep track of
% sharing, and then we need to assume that any potential sharing
% between variables is possible. If we do that, any time there is an
% unification between two variables, any unrelated 'ng' variable could
% share with either of them and become ground as a result of that
% unification, and therefore its value needs to be updated to
% 'any'. And even if that was not the case and some sharing
% information was kept, variables would not last much longer with
% value 'ng' since that value needs to be updated as soon as they are
% unified with something (to 'g' when unified with 'g' variables and
% to 'any' when unified to 'ng' or 'any' variables).
%
% As a result, even if the things above were considered in the
% implementation of the domain (which were not), the cases were having
% the value 'ng' would result in a gain of precision with respect to
% removing that value altogether are scarce. Therefore it has been
% preferred to remove that value rather than fixing the domain
% implementation to reflect the problem above, and use the domain shfr
% when a more precise analysis is needed. Now the value 'ng' is never
% introduced for a variable, but unnecessary code for handling 'ng'
% varibles might remain.

:- use_module(engine(io_basic)).
:- use_module(library(messages), [warning_message/2]).
:- use_module(library(sort)).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).

:- include(ciaopp(plai/plai_domain)).
:- dom_def(gr, [default]).

:- doc(doinclude,asub/1).
:- doc(doinclude,asub_elem/1).
:- doc(doinclude,gr_mode/1).
:- doc(doinclude,extrainfo/1).
:- doc(doinclude,binds/1).
:- doc(doinclude,binding/1).

% :- compilation_fact(check_wellformed_asub).
:- if(defined(check_wellformed_asub)).
:- prop asub(A)
   # "`A` is a well-formed abstract substitution of the gr domain.".
asub('$bottom').
asub([]).
asub([A/M|Asub]):- 
    asub_elem(A/M),
    not_unified(Asub,A),
    asub(Asub).

:- prop not_unified/2
   #"This property may be violated if the domain operations are called with
   abstract substitutions that are not properly sorted (e.g. lub unifies
   variables).".
% TODO: quadratic check! use rtc_impl with a low-level linear check 
% (bind seen vars, fail if seen marked, all under a double negation
not_unified([],_). 
not_unified([V/_|R],A) :-
    V \== A,
    not_unified(R,A).

:- else.
:- prop asub(A)
   # "`A` is a well-formed abstract substitution of the `gr` domain.".
asub('$bottom').
asub([]).
asub([E|Asub]):- % cheaper check
    asub_elem(E),
    asub(Asub).
:- endif.

:- prop asub_elem(E) # "`E` is a single substitution.".
asub_elem(Var/Mode):-
    var(Var),
    gr_mode(Mode).

:- regtype gr_mode(M) # "`M` is `g` (ground), `ng` (nonground), or `any`.".
gr_mode(g).
gr_mode(ng).
gr_mode(any).

:- prop extrainfo(E) # "`E` is a par (`asub/1`,`binds/1`).".
extrainfo(yes).
extrainfo(no).
extrainfo((A,B)):-
    asub(A),
    binds(B).

:- prop binds(B) # "`B` is a list of bindings.".
binds(B) :- list(binding,B).

:- prop binding(B) # "`B` is a triple (`X`,`Term`,`Vars`), where `X` is
a variable, `Term` is a term and `Vars` is the set of variables in `Term`.".
binding((X,Term,Vars)):-
    var(X),
    term(Term),
    list(Vars).


:- export(unknown_entry/3).
:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(Sg, Qv, Call)
   : cgoal * list * term => asub(Call) + (not_fails, is_det)
   #
"Gives the *top* value for the variables involved in a literal whose
definition is not present, and adds this top value to `Call`. In this domain
the *top* value is `X`/`any` forall `X` in the set of variables.
".
   
unknown_entry(_Sg,Qv,Call):-
    create_values(Qv,Call,any).

%-----------------------------------------------------------------------

:- pred create_values(+Vars,-Asub,+Value)
   : list * term * gr_mode => asub(Asub) + (not_fails, is_det)
   # "Forall `X` in `Vars`, `X`/`Value` is in `Asub`.".

create_values([],[],_Value).
create_values([X|Xs],[X/Value|New],Value):-
    create_values(Xs,New,Value).

:- export(empty_entry/3).
:- dom_impl(_, empty_entry/3, [noq]).
:- pred empty_entry(+Sg,+Vars,-Entry)
   : cgoal * list * term => asub(Entry) + (not_fails, is_det)
   #
"Gives the *empty* value in this domain for a given set of variables
`Vars`, resulting in the abstract substitution `Entry`. I.e., obtains
the abstraction of a substitution in which all variables `Vars` are
unbound: free and unaliased. In this domain the *empty* value is equivalent to
the *unknown* value.
".

empty_entry(Sg,Vars,Entry):- 
    unknown_entry(Sg,Vars,Entry).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                             ABSTRACT SORT                              %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(abs_sort/2).       
:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+Asub,-Asub_s)
   : asub(Asub) => asub(Asub_s) + (not_fails, is_det)
   # "It sorts the set of `X`/`Value` in `Asub` obtaining `Asub_s`.".

abs_sort('$bottom','$bottom'):- !.
abs_sort(Asub,Asub_s):-
    sort(Asub,Asub_s).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                        ABSTRACT PROJECTION                             %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(project/5).
:- dom_impl(_, project/5, [noq]).
:- pred  project(+Sg,+Vars,+HvFv_u,+Asub,?Proj)
   : term * list * term * asub * term => asub(Proj) + (not_fails, is_det)
   # 
"`Proj` is the result of eliminating from `Asub` all `X`/`Value`
such that `X` is not in `Vars`. `HvFv_u` may be a list or
'`not_provided_HvFv_u`'.
This predicate may be used with `Proj` instantiated, see
`call_to_success_builtin/6`.
".

project(_Sg,_Vars,_HvFv_u,'$bottom',Proj) :- !,
    Proj = '$bottom'.
project(_Sg,Vars,_HvFv_u,ASub,Proj) :- 
    project_aux(Vars,ASub,Proj).

:- pred  project_aux(+Vars,+ListValues,?Proj)
   : list * list * term => asub(Proj)
   #
"Eliminates from each list in the second argument any variable/value such
that the variable is not an element of `Vars`.
".

project_aux([],_,Proj):- !,
    Proj = [].
project_aux(_,[],Proj):- !,
    Proj = [].
project_aux([Head1|Tail1],[Head2/Val|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    project_aux_(Order,Head1,Tail1,Head2/Val,Tail2,Proj).

project_aux_(=,_,Tail1,HeadVal,Tail2,[HeadVal|Proj]) :-
    project_aux(Tail1,Tail2,Proj).
project_aux_(>,Head1,Tail1,_,[Head2/Val|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    project_aux_(Order,Head1,Tail1,Head2/Val,Tail2,Proj).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                        ABSTRACT Call To Entry                          %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(call_to_entry/9).
:- dom_impl(_, call_to_entry/9, [noq]).
:- pred call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo)
   : ( list(Sv), cgoal(Sg), list(Hv), cgoal(Head), term(K), list(Fv), asub(Proj)) % cheaper properties
   => (asub(Entry), extrainfo(ExtraInfo)) + (not_fails, is_det)
   #
"It obtains the abstract substitution `Entry` which results from
adding the abstraction of the `Sg` = `Head` to `Proj`,
later projecting the resulting substitution onto `Hv` + `Fv`. This is
done as follows:  
- If `Sg` and `Head` are identical up to renaming it is just  
 renaming `Proj` and adding the `Fv`. 
- If `Hv` = [], `Entry` is just adding the `Fv`. 
- Otherwise, it will 
 - obtain in `Binds` the primitive equations corresponding to `Sg` = `Head`. 
 - add to `Proj` the variables in `Hv` as not ground in `Temp1`. 
 - update `Temp1`, grounding some variables obtaining `Temp2`. 
 - insert `Fv` in `Temp2` as `any` obtaining `Temp3`.
 - projects `Temp3` onto `Hv` + `Fv` obtaining `Entry`.  

The meaning of the variables is
- `Sv` is a list of subgoal variables. 
- `Sg` is the subgoal being analysed. 
- `Head` is the Head of the clause being analysed. 
- `Fv` is a list of free variables in the body of the clause being considered. 
- `Proj` is the abstract substitution `Call` projected onto `Sv`. 
- `Entry` is the Abstract entry substitution (i.e. the abstract subtitution
   obtained after the abstract unification of `Sg` and `Head` projected
   onto `Hv` + `Fv`). 
- `ExtraInfo` Info computed during the `call_to_entry/9` that can
   be reused during the `exit_to_prime/7` step.  
".

call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):-
    variant(Sg,Head),!,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj)),
    Head = NewTerm,
    abs_sort(NewProj,Projsorted),
    gr_change_values_insert(Fv,Projsorted,Entry,any).       
call_to_entry(_,_,[],_Head,_K,Fv,_Proj,Entry,no):- !,
    gr_change_values_insert(Fv,[],Entry,any). % (*)
call_to_entry(Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
    gr_simplify_equations(Sg,Head,Binds),
    gr_change_values_insert(Hv,Proj,Temp1,any),
    abs_gunify(Temp1,Binds,Temp2,NewBinds),
    gr_change_values_insert(Fv,Temp2,Temp3,any),
    merge(Hv,Fv,HvFv),
    project(Sg,HvFv,not_provided_HvFv_u,Temp3,Entry),
    project(Sg,Sv,not_provided_HvFv_u,Temp3,NewProj),
    ExtraInfo= (NewProj,NewBinds),!.
% (*) See why it is not ng in comment below the lattice sketch

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Exit To Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(exit_to_prime/7).
:- dom_impl(_, exit_to_prime/7, [noq]).
:- pred  exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,?ExtraInfo,-Prime)
   : term * list * cgoal * cgoal * asub * term * term
   => ( extrainfo(ExtraInfo), asub(Prime))
   #
"It computes the prime abstract substitution `Prime`, i.e.  the result of 
going from the abstract substitution over the head variables `Exit`, to
the abstract substitution over the variables in the subgoal. It will:
- If `Exit` is `$bottom`, `Prime` will be also `$bottom`.               
- If `Flag` = yes (`Head` and `Sg` identical up to renaming) it is just 
  renaming `Exit`.
-  If `Hv` = [], `Prime` = `\\{` `X`/`g`| forall `X` in `Sv` `\\}`                
-  Otherwise: it will 
  - obtain the primitive equations corresponding to `Sg`=`Head`
    from `Extrainfo`.
  - projects `Exit` onto `Hv` obtaining `BPrime`. 
  - merge `Proj` from `Extrainfo` and `BPrime` obtaining `TempPrime`.
  - update  `TempPrime`, grounding some variables obtaining  `NewTempPrime`.
  - projects  `NewTempPrime` onto `Sv` obtaining `Prime`.
".

exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    abs_sort(NewPrime,Prime).    
exit_to_prime(_Sg,[],_Head,Sv,_Exit,_ExtraInfo,Prime):- !,
    create_values(Sv,Prime,g).
exit_to_prime(Sg,Hv,_Head,Sv,Exit,ExtraInfo,Prime):-
    ExtraInfo = (Proj,Binds),
    project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    merge(Proj,BPrime,TempPrime),
    abs_gunify(TempPrime,Binds,NewTempPrime,_),
    project(Sg,Sv,not_provided_HvFv_u,NewTempPrime,Prime),!.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                           ABSTRACT LUB                                 %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(compute_lub/2).
:- dom_impl(_, compute_lub/2, [noq]).
:- pred compute_lub(+ListASub,-Lub)
   : list(asub, ListASub) => asub(Lub) + (not_fails, is_det)
   #
"It computes the least upper bound of a set of abstract substitutions. 
For each two abstract substitutions `ASub1` and `ASub2` in `ListASub`, 
obtaining the *lub* is just:
 
foreach `X`/`Value1` in `ASub1` and `X`/`Value2` in `ASub2`:   
- if `Value1` == `Value2`, `X`/`Value1` in `Lub`.
- otherwise, `X`/`any` in `Lub`.
".

compute_lub([X],X):- !.
compute_lub([ASub1,ASub2|Xs],Lub):-
    compute_lub_el(ASub1,ASub2,ASubLub),
    compute_lub([ASubLub|Xs],Lub).

% :- dom_impl(_, compute_lub_el(ASub1,ASub2,ASub), compute_lub_el(ASub1,ASub2,ASub)).
:- pred compute_lub_el(+ASub1,+ASub2,-Lub)
   : asub * asub * term => asub(Lub) + (not_fails, is_det)
   #
"For each two abstract substitutions `ASub1` and `ASub2` 
obtaining the least upper bound is just:    
foreach `X`/`Value1` in `ASub1` and `X`/`Value2` in `ASub2`:  
- if `Value1` == `Value2`, `X`/`Value1` in `Lub`.                              
- otherwise, `X`/`any` in `Lub`.                                           
".

compute_lub_el('$bottom',ASub,ASub):- !.
compute_lub_el(ASub,'$bottom',ASub):- !.
compute_lub_el(ASub1,ASub2,Lub):- 
    compute_lub_gr(ASub1,ASub2,Lub).

compute_lub_gr(ASub1,ASub2,Lub):- 
    ASub1 == ASub2, !,
    Lub = ASub1.
compute_lub_gr([Xv|ASub1],[Yv|ASub2],Lub):- 
    Xv == Yv, !,
    Lub = [Xv|Lub_Cont],
    compute_lub_gr(ASub1,ASub2,Lub_Cont).
compute_lub_gr([X/_|ASub1],[X/_|ASub2],[X/any|Lub_Cont]):-
    compute_lub_gr(ASub1,ASub2,Lub_Cont).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                            ABSTRACT Extend                             %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(extend/5).
:- dom_impl(_, extend/5, [noq]).
:- pred  extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : term * asub * list * asub * term => asub(Succ) + (not_fails, is_det)
   #
"If `Prime` = `$bottom`, `Succ` = `$bottom`. If `Sv` = [],
`Call` = `Succ`. Otherwise, `Succ` is computed updating the
values of `Call` with those in `Prime`.
".

extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
extend(_Sg,Prime,_Sv,Call,Succ):-
    update_Call(Call,Prime,Succ).

update_Call([],_,[]) :- !.
update_Call(Call,[],Call) :- !.
update_Call([X/ValueX|Call],[Y/ValueY|Prime],Succ):-
    compare(Order,X,Y),
    update_Call_(Order,X/ValueX,Call,Y/ValueY,Prime,Succ).

update_Call_(=,_,Call,ElemP,Prime,[ElemP|Succ]):-
    update_Call(Call,Prime,Succ).
update_Call_(<,ElemC,Call,ElemP,Prime,[ElemC|Succ]):-
    update_Call(Call,[ElemP|Prime],Succ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- export(call_to_success_fact/9).
:- dom_impl(_, call_to_success_fact/9, [noq]).
:- pred call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : cgoal * list * cgoal * term * list * asub * asub * term * term
   => ( asub(Prime), asub(Succ) ) + (not_fails, is_det)
   # "Specialized version of `call_to_entry/9` + `exit_to_prime/7` + `extend/5` for facts.".

call_to_success_fact(Sg,[],_Head,_K,Sv,Call,_Proj,Prime,Succ) :- !,
    create_values(Sv,Prime,g),
    extend(Sg,Prime,Sv,Call,Succ).       
call_to_success_fact(Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    gr_simplify_equations(Sg,Head,Binds),!,
    gr_change_values_insert(Hv,Proj,Temp1,any),
    abs_gunify(Temp1,Binds,Temp2,_NewBinds),
    project(Sg,Sv,not_provided_HvFv_u,Temp2,Prime),
    extend(Sg,Prime,Sv,Call,Succ).
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

:- export(special_builtin/5).
:- dom_impl(_, special_builtin/5, [noq]).
:- pred special_builtin(+Pred,+Sg,+Subgoal,?Type,---Condvars)
   : term * cgoal * term * term * term
   #
"Satisfied if the builtin does not need a very complex action. It       
divides builtins into groups determined by the flag returned in the    
second argument + some special handling for some builtins:             
- *new_ground* if the builtin makes all variables ground whithout      
  imposing any condition on the previous freeness values of the      
  variables.                                                          
- *old_ground* if the builtin requires the variables to be ground.      
- *old_new_ground* if the builtin requires some variables to be       
  ground and grounds the rest.                                        
- unchanged if we cannot infer anything from the builtin, the        
  substitution remains unchanged and there are no conditions imposed 
  on the previous freeness values of the variables.                  
- *some* if it makes some variables ground without imposing conditions. 
- `Sgkey`, special handling of some particular builtins.                
".

special_builtin('CHOICE IDIOM/1',_,_,new_ground,_).
special_builtin('$metachoice/1',_,_,new_ground,_).
special_builtin('current_atom/1',_,_,new_ground,_).
special_builtin('current_input/1',_,_,new_ground,_).
special_builtin('current_module/1',_,_,new_ground,_).
special_builtin('current_output/1',_,_,new_ground,_).
special_builtin('current_op/3',_,_,new_ground,_).
special_builtin('depth/1',_,_,new_ground,_).
special_builtin('get_code/1',_,_,new_ground,_).
special_builtin('get1_code/1',_,_,new_ground,_).
special_builtin('seeing/1',_,_,new_ground,_).
special_builtin('telling/1',_,_,new_ground,_).
special_builtin('statistics/2',_,_,new_ground,_).
special_builtin(':/2',(prolog:'$metachoice'(_)),_,new_ground,_).

special_builtin('CUT IDIOM/1',_,_,old_ground,_).
special_builtin('$metacut/1',_,_,old_ground,_).
special_builtin(':/2',(prolog:'$metacut'(_)),_,old_ground,_).
special_builtin('op/3',_,_,old_ground,_).
special_builtin('save_event_trace/1',_,_,old_ground,_).
special_builtin('close/1',_,_,old_ground,_).

special_builtin('abort/0',_,_,bottom,_).
special_builtin('fail/0',_,_,bottom,_).
special_builtin('false/0',_,_,bottom,_).
special_builtin('halt/0',_,_,bottom,_).

special_builtin('!/0',_,_,unchanged,_).
special_builtin('assert/1',_,_,unchanged,_).
special_builtin('asserta/1',_,_,unchanged,_).
special_builtin('assertz/1',_,_,unchanged,_).
special_builtin('debug/0',_,_,unchanged,_).
special_builtin('debugging/0',_,_,unchanged,_).
special_builtin('dif/2',_,_,unchanged,_).
special_builtin('display/1',_,_,unchanged,_).
special_builtin('flush_output/0',_,_,unchanged,_).
special_builtin('garbage_collect/0',_,_,unchanged,_).
special_builtin('gc/0',_,_,unchanged,_).
special_builtin('listing/0',_,_,unchanged,_).
special_builtin('listing/1',_,_,unchanged,_).
special_builtin('nl/0',_,_,unchanged,_).
special_builtin('nogc/0',_,_,unchanged,_).
special_builtin('not/1',_,_,unchanged,_).
special_builtin('print/1',_,_,unchanged,_).
special_builtin('repeat/0',_,_,unchanged,_).
special_builtin('start_event_trace/0',_,_,unchanged,_).
special_builtin('stop_event_trace/0',_,_,unchanged,_).
special_builtin('seen/0',_,_,unchanged,_).
special_builtin('told/0',_,_,unchanged,_).
special_builtin('true/0',_,_,unchanged,_).
special_builtin('ttyflush/0',_,_,unchanged,_).
special_builtin('otherwise/0',_,_,unchanged,_).
special_builtin('ttynl/0',_,_,unchanged,_).
special_builtin('write/1',_,_,unchanged,_).
special_builtin('writeq/1',_,_,unchanged,_).


% SICStus3 (ISO)
special_builtin('\\+/1',_,_,unchanged,_).
special_builtin('\\==/2',_,_,unchanged,_).
% SICStus2.x
% special_builtin('\+/1',_,_,unchanged,_).
% special_builtin('\==/2',_,_,unchanged,_).
special_builtin('@>=/2',_,_,unchanged,_).
special_builtin('@=</2',_,_,unchanged,_).
special_builtin('@>/2',_,_,unchanged,_).
special_builtin('@</2',_,_,unchanged,_).
%-------------------------------------------------------------------------
% special_builtin('read/1',_,_,all_nonfree,_).     ask to Paco
% special_builtin('read/2',read(X,Y),_,read2,p(X,Y)).  ask to Paco
%-------------------------------------------------------------------------
special_builtin('atom/1',_,_,old_ground,_).
special_builtin('atomic/1',_,_,old_ground,_).
special_builtin('ensure_loaded/1',_,_,old_ground,_).
special_builtin('erase/1',_,_,old_ground,_).
special_builtin('float/1',_,_,old_ground,_).
special_builtin('flush_output/1',_,_,old_ground,_).
special_builtin('integer/1',_,_,old_ground,_).
special_builtin('number/1',_,_,old_ground,_).
special_builtin('nl/1',_,_,old_ground,_).
special_builtin('put_code/1',_,_,old_ground,_).
special_builtin('put_code/2',_,_,old_ground,_).
special_builtin('see/1',_,_,old_ground,_).
special_builtin('tell/1',_,_,old_ground,_).
special_builtin('tab/1',_,_,old_ground,_).
special_builtin('tab/2',_,_,old_ground,_).
special_builtin('ttyput/1',_,_,old_ground,_).
special_builtin('=:=/2',_,_,old_ground,_).
special_builtin('>=/2',_,_,old_ground,_).
special_builtin('>/2',_,_,old_ground,_).
special_builtin('</2',_,_,old_ground,_).
special_builtin('=</2',_,_,old_ground,_).
% SICStus3 (ISO)
special_builtin('=\\=/2',_,_,old_ground,_).
% SICStus2.x
% gr_special_builtin('=\=/2',_,_,old_ground,_).
special_builtin('ground/1',_,_,old_ground,_).
%-------------------------------------------------------------------------
special_builtin('absolute_file_name/2',absolute_file_name(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('get_code/2',get_code(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('get1_code/2',get1_code(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('is/2',is(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,NewG),
    varset(Y,OldG).
special_builtin('open/3',open(X,Y,Z),_,old_new_ground,(OldG,NewG)):-
    varset(p(X,Y),OldG),
    varset(Z,NewG).
special_builtin('format/2',format(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
special_builtin('format/3',format(X,Y,_Z),_,old_new_ground,(OldG,[])):-
    varset(p(X,Y),OldG).
special_builtin('predicate_property/2',predicate_property(_X,Y),_,old_new_ground,
                                                                    ([],NewG)):-
    varset(Y,NewG).
special_builtin('print/2',print(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
special_builtin('prolog_flag/2',prolog_flag(X,Y),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(Y,NewG).
special_builtin('prolog_flag/3',prolog_flag(X,Y,Z),_,old_new_ground,(OldG,NewG)):-
    varset(X,OldG),
    varset(f(Y,Z),NewG).
special_builtin('write/2',write(X,_Y),_,old_new_ground,(OldG,[])):-
    varset(X,OldG).
%-------------------------------------------------------------------------
special_builtin('assert/2',assert(_X,Y),_,some,Vars):-
    varset(Y,Vars).
special_builtin('assertz/2',assertz(_X,Y),_,some,Vars):-
    varset(Y,Vars).
special_builtin('asserta/2',asserta(_X,Y),_,some,Vars):-
    varset(Y,Vars).
special_builtin('recorda/3',recorda(_X,_Y,Z),_,some,Vars):-
    varset(Z,Vars).
special_builtin('recordz/3',recordz(_X,_Y,Z),_,some,Vars):-
    varset(Z,Vars).
%%%%%%%%%% arg/3
special_builtin('arg/3',arg(X,Y,Z),_,arg,p(X,Y,Z)).
%%%%%%%%%% expand_term/2
special_builtin('expand_term/2',expand_term(X,Y),_,exp,p(X,Y)).
%%%%%%%%%% =../2
special_builtin('=../2','=..'(X,Y),_,'=../2',p(X,Y)).
%%%%%%%%%% recorded/3
special_builtin('recorded/3',recorded(_X,Y,Z),_,recorded,p(Y,Z)).
special_builtin('retract/1',retract(X),_,recorded,p(X,a)).
special_builtin('retractall/1',retractall(X),_,recorded,p(X,a)).
%%%%%%%%%% copy_term
special_builtin('copy_term/2',copy_term(X,Y),_,copy_term,p(X,Y)).
%%%%%%%%%% current_key/2
special_builtin('current_key/2',current_key(X,_Y),_,'current_key/2',p(X)).
%%%%%%%%%% current_predicate/2
special_builtin('current_predicate/2',current_predicate(X,Y),_,
                                           'current_predicate/2',p(X,Y)).
%%%%%%%%%% functor/3
special_builtin('functor/3',functor(X,Y,Z),_,'functor/3',p(X,Y,Z)).
%%%%%%%%%% name/2
special_builtin('name/2',name(X,Y),_,'name/2',p(X,Y)).
%%%%%%%%%% nonvar/1
special_builtin('nonvar/1',_,_,unchanged,_).  % needed?
special_builtin('not_free/1',_,_,unchanged,_).  % ask to Paco
%%%%%%%%%% numbervars/3
special_builtin('numbervars/3',numbervars(X,Y,Z),_,'numbervars/3',p(X,Y,Z)).
%%%%%%%%%% compare/3
special_builtin('compare/3',compare(X,_Y,_Z),_,'compare/3',p(X)).
%%%%%%%%%% indep/2
special_builtin('indep/2',_,_,unchanged,_).  % ask to Paco
%%%%%%%%%% length/2
special_builtin('length/2',_,_,unchanged,_).  % ask to Paco
%%%%%%%%%% var/1
special_builtin('var/1',_,_,unchanged,_).  % needed?
special_builtin('free/1',_,_,unchanged,_).  % ask to Paco
%%%%%%%%%% indep/1
special_builtin('indep/1',_,_,unchanged,_).  % ask to Paco
%%%%%%%%%% others
special_builtin(Key,_Goal,_,special(Key),[]):-
    very_special_builtin(Key).

very_special_builtin('==/2').
very_special_builtin('=/2').
very_special_builtin('C/3').
%very_special_builtin('keysort/2').
%very_special_builtin('sort/2').

:- export(success_builtin/6).
:- dom_impl(_, success_builtin/6, [noq]).
:- pred  success_builtin(+Type,+Sv_u,?Condv,+HvFv_u,+Call,-Succ)
   : atm * list * term * list * asub * term => asub(Succ)
   #
"Obtains the success for some particular builtins:
- If `Type` = *new_ground*, it updates `Call` making all vars in `Sv_u` ground.
- If `Type` = *bottom*, `Succ` = `$bottom`.                              
- If `Type` = *unchanged*, `Succ` = `Call`.       
- If `Type` = *some*, it updates `Call` making all vars in `Condv` ground.
- If `Type` = *old_ground*, if grounds all variables in `Sv` and checks that 
  no free variables has becomed ground.                      
- If `Type` = *old_ground*, if grounds all variables in `OldG` and checks   
  that no free variables has becomed ground. If so, it grounds all
  variables in `NewG`.                             
- Otherwise `Type` is the `SgKey` of a particular builtin for each the    
  `Succ` is computed.      
".
% TODO: Missing cuts in all the following clauses
success_builtin(new_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    gr_change_values_insert(Sv,Call,Succ,g).
%
success_builtin(bottom,_,_,_,_,'$bottom').
%
success_builtin(unchanged,_,_,_,Succ,Succ).
%
success_builtin(some,_Sv,NewGr_u,_,Call,Succ):-
    sort(NewGr_u,NewGr),
    gr_change_values_insert(NewGr,Call,Succ,g).
%
success_builtin(old_ground,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    gr_values_notequal(Sv,Call,ng),!,
    gr_change_values_insert(Sv,Call,Succ,g).
success_builtin(old_ground,_,_,_,_,'$bottom').
%
success_builtin(old_new_ground,_,(OldG_u,NewG_u),_,Call,Succ):-
    sort(OldG_u,OldG),
    gr_values_notequal(OldG,Call,ng),!,
    gr_change_values_insert(OldG,Call,TempSucc,g),  
    sort(NewG_u,NewG),
    gr_change_values_insert(NewG,TempSucc,Succ,g).
success_builtin(old_new_ground,_,_,_,_,'$bottom').
%
success_builtin(arg,_,Sg0,_,Call,Succ):- Sg0=p(X,Y,Z),
    varset(X,OldG),
    gr_values_notequal(OldG,Call,ng),!,  
    gr_change_values_insert(OldG,Call,NCall,g),
    Sg = p(Y,Z),
    Head = p(f(A,_B),A),
    varset(Sg,Sv),
    varset(Head,Hv),
    project(Sg,Sv,not_provided_HvFv_u,NCall,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,NCall,Proj,_,Succ). % TODO: add some ClauseKey?
success_builtin(arg,_,_,_,_,'$bottom').
%
success_builtin(exp,_,Sg,_,Call,Succ):-
    Head = p(A,f(A,_B)),
    varset(Sg,Sv),
    varset(Head,Hv),
    project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    call_to_success_fact(Sg,Hv,Head,not_provided,Sv,Call,Proj,_,Succ). % TODO: add some ClauseKey?
success_builtin(exp,_,_,_,_,'$bottom').
%
success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
    varset(X,Varsx),
    gr_values_equal(Varsx,Call,g),!,
    varset(Y,VarsY),
    gr_change_values_insert(VarsY,Call,Succ,g).
success_builtin('=../2',_,p(X,Y),_,Call,Succ):-
    varset(Y,VarsY),
    gr_values_equal(VarsY,Call,g),!,
    varset(X,VarsX),
    gr_change_values_insert(VarsX,Call,Succ,g).
success_builtin('=../2',_,_,_,Succ,Succ). 
%
success_builtin(recorded,_,p(_Y,Z),_,Call,Succ):-
    varset(Z,NewGr),
    gr_change_values_insert(NewGr,Call,Succ,g).
%
success_builtin(copy_term,_,Sg,_,Call,Succ):- Sg=p(X,Y),
    varset(X,VarsX),
    project(Sg,VarsX,not_provided_HvFv_u,Call,ProjectedX),
    copy_term((X,ProjectedX),(NewX,NewProjectedX)),
    abs_sort(NewProjectedX,ProjectedNewX),
    varset(NewX,VarsNewX),
    varset(Y,VarsY),
    merge(VarsNewX,VarsY,TempSv),
    project(Sg,VarsY,not_provided_HvFv_u,Call,ProjectedY),
    merge(ProjectedY,ProjectedNewX,TempAbs),
    merge(ProjectedNewX,Call,TempCall),
    call_to_success_builtin('=/2','='(NewX,Y),TempSv, TempCall,TempAbs,Temp_success),
    collect_vars_gr(Call,VarsCall),
    project(Sg,VarsCall,not_provided_HvFv_u,Temp_success,Succ).
%
success_builtin('current_key/2',_,p(X),_,Call,Succ):-
    varset(X,NewG),
    gr_change_values_insert(NewG,Call,Succ,g).
%
success_builtin('current_predicate/2',_,p(X,_Y),_,Call,Succ):- !,
    varset(X,NewG),
    gr_change_values_insert(NewG,Call,Succ,g).
%
success_builtin('functor/3',_,p(X,Y,Z),_,Call,Succ):-
    varset(X,OldG),
    gr_values_equal(OldG,Call,g),!,
    varset([Y,Z],NewGr),    
    gr_change_values_insert(NewGr,Call,Succ,g).
success_builtin('functor/3',_,_,_,Succ,Succ).
%
success_builtin('name/2',_,p(X,Y),_,Call,Succ):-
    varset(X,OldG),
    gr_values_notequal(OldG,Call,ng),!,
    varset(Y,NewG),
    gr_change_values_insert(NewG,Call,Succ,g).
success_builtin('name/2',_,p(X,Y),_,Call,Succ):-
    varset(Y,OldG),
    gr_values_notequal(OldG,Call,ng),!,
    varset(X,NewG),
    gr_change_values_insert(NewG,Call,Succ,g).
success_builtin('name/2',_,_,_,_,'$bottom').
%
success_builtin('numbervars/3',_,p(X,Y,Z),_,Call,Succ):-
    varset(Y,OldG),
    gr_values_notequal(OldG,Call,ng),!,
    varset(p(X,Z),NewG),
    gr_change_values_insert(NewG,Call,Succ,g).
success_builtin('numbervars/3',_,_,_,_,'$bottom').
%
success_builtin('compare/3',_,p(X),_,Call,Succ):- 
    atom(X),!,
    Succ = Call.
success_builtin('compare/3',_,p(X),_,Call,Succ):- 
    var(X),!,
    gr_change_values_insert([X],Call,Succ,g).
success_builtin('compare/3',_,_,_,_,'$bottom').
%
%success_builtin(bag,_,(_From,_On,nofail),_,'$bottom',Succ):-
%
success_builtin(Key,_,_,_,Succ,Succ):-
    warning_message("the builtin key ~q is not defined",[Key]).

:- export(call_to_success_builtin/6).
:- dom_impl(_, call_to_success_builtin/6, [noq]).
:- pred  call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)
   : atm * cgoal * list * asub * asub * term
   # "Handles those builtins for which computing `Proj` is easier than `Succ`.".

call_to_success_builtin('==/2',Sg,Sv,Call,Proj,Succ):- Sg='=='(X,Y),
    gr_simplify_equations(X,Y,Binds),
    project(Sg,Sv,not_provided_HvFv_u,Call,Proj),
    gr_comp(Binds,Proj,Exit),!,
    extend(Sg,Exit,Sv,Call,Succ).
call_to_success_builtin('==/2',_,_,_call,_,'$bottom').
%
call_to_success_builtin('=/2','='(X,_Y),Sv,Call,Proj,Succ):-
    varset(X,VarsX), 
    gr_values_equal(VarsX,Proj,g), !,
    ord_subtract(Sv,VarsX,VarsY),
    gr_change_values_insert(VarsY,Call,Succ,g).
%
call_to_success_builtin('=/2','='(_X,Y),Sv,Call,Proj,Succ):-
    varset(Y,VarsY), 
    gr_values_equal(VarsY,Proj,g), !,
    ord_subtract(Sv,VarsY,VarsX),
    gr_change_values_insert(VarsX,Call,Succ,g).
call_to_success_builtin('=/2','='(X,Y),Sv,Call,Proj,Succ):-
    copy_term(X,Xterm),
    copy_term(Y,Yterm),
    Xterm = Yterm,!,
    varset(Xterm,Vars),
    call_to_success_fact('='(X,Y),Vars,'='(Xterm,Xterm),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin('=/2',_,_,_call,_,'$bottom').
%
call_to_success_builtin('C/3','C'(X,Y,Z),Sv,Call,Proj,Succ):- !,
    call_to_success_builtin('=/2','='(X,[Y|Z]),Sv,Call,Proj,Succ).
%
call_to_success_builtin('keysort/2',keysort(X,Y),Sv,Call,Proj,Succ):-
    call_to_success_builtin('sort/2',sort(X,Y),Sv,Call,Proj,Succ).

gr_comp([],Proj,Proj).
gr_comp([(X,Term,_Tv)|Binds],Proj,Exit):-
    var(Term),!,
    gr_var_value(Proj,X,Val),
    gr_var_value(Proj,Term,Val),
    gr_comp(Binds,Proj,Exit).
gr_comp([(X,_,Tv)|Binds],Proj,Exit):-
    ( gr_var_value(Proj,X,g) ->
        gr_change_values_insert(Tv,Proj,Proj1,g)
    ;
        Proj1 = Proj
    ),
    gr_comp(Binds,Proj1,Exit).

:- export(input_user_interface/5). 
:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(?InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   : term * list * term * term * term => asub(ASub) + (not_fails, is_det)
   #
"Obtains the abstract substitution for `gr` from the native properties found
in the user supplied info.
".

input_user_interface((Gv_u,Ng_u),Qv,ASub,_Sg,_MaybeCallASub):-
    may_be_var(Gv_u,Gv),
    may_be_var(Ng_u,Ng),
    merge(Gv,Ng,Infv),
    ord_subtract(Qv,Infv,AnyV),
    create_values(Gv,Temp1,g),
    gr_change_values_insert(Ng,Temp1,Temp2,any), % (*)
    gr_change_values_insert(AnyV,Temp2,ASub,any).
% (*) See why it is not ng in comment below the lattice sketch

:- dom_impl(_, input_interface/4, [noq]).
:- pred input_interface(+Prop,?Kind,?Struc0,?Struc1)
   #
"Adds native property `Prop` to the structure accumulating the
properties relevant to this domain, namely: `ground/1`, `free/1`, and
`not_ground/1`.
".
   
%input_interface(regtype(gnd(X)),K,S0,S1) :-
%    input_interface(ground(X),K,S0,S1).
input_interface(ground(X),perfect,(Gv0,NGv),(Gv,NGv)):-
    varset(X,Vs),
    myappend(Gv0,Vs,Gv).
input_interface(free(X),approx,Struct0,Struct):-
    input_interface(not_ground(X),_Any,Struct0,Struct).
input_interface(not_ground(X),approx,(Gv,NGv0),(Gv,NGv)):- % (*)
    varset(X,Vs),
    myappend(Vs,NGv0,NGv).
% (*) See why it is 'approx' and not 'perfect' in the comment below
% the lattice sketch

myappend(Vs,V0,V):-
    var(Vs), !,
    V=V0.
myappend(Vs,V0,V):-
    merge(Vs,V0,V).

may_be_var(X,X):- ( X=[] ; true ), !.

:- export(asub_to_native/5). 
:- dom_impl(_, asub_to_native/5, [noq]).
:- pred  asub_to_native(+ASub,+Qv,+OutFlag,-ASub_user,-Comps)
   : asub * list * term * term * term
   #
"The user friendly format consists in extracting the ground variables
and the nonground variables.
".

asub_to_native(Abs,_Qv,_OutFlag,ASub_user,[]):-
    member_value_gr(Abs,Gv,g),
    member_value_gr(Abs,NGv,ng),
    ( Gv=[] -> ASub_user=ASub_user0 ; ASub_user=[ground(Gv)|ASub_user0] ),
    ( NGv=[] -> ASub_user0=[] ; ASub_user0=[not_ground(Gv)] ).

:- pred member_value_gr(+Abs,-Vars,+Value).

member_value_gr([],[],_).
member_value_gr([X/V|Rest],[X|RestV],Value):-
    V==Value,!,
    member_value_gr(Rest,RestV,Value).
member_value_gr([_|Rest],RestV,Value):-
    member_value_gr(Rest,RestV,Value).

%% %------------------------------------------------------------------------%
%% % output_interface(+,-)                                                  %
%% % output_interface(ASub,Output)                                          %
%% % The readible format still close to the internal formal is identical    %
%% %-------------------------------------------------------------------------
%% 
%% %!  output_interface(+ASub,-Output): asub * asub # 
%% "The readible format still close to the internal formal is identical".
%%  
%% output_interface(Output,Output).

:- export(unknown_call/4).
:- dom_impl(_, unknown_call/4, [noq]).
:- pred unknown_call(+Sg,+Vars,+Call,-Succ)
   : cgoal * list * asub * term => asub(Succ) + (not_fails, is_det)
   #
"Gives the *top* value for the variables involved in a literal whose
definition is not present, and adds this *top* value to `Call`.
".

unknown_call(_Sg,Vars,Call,Succ):-
    gr_change_values_insert(Vars,Call,Succ,any).

:- export(less_or_equal/2).
:- dom_impl(_, less_or_equal/2, [noq]).
:- pred less_or_equal(+ASub0,+ASub1)
   : asub * asub + is_det
   #
"Succeeds if `ASub1` is more general or equal to `ASub0`. It's
assumed the two abstract substitutions are defined on the same variables.
".

% it's assumed the two abstract        
% substitutions are defined on the same variables 
less_or_equal('$bottom',_) :- !.
less_or_equal(ASub0,ASub1):-
    less_or_equal_(ASub0,ASub1).

less_or_equal_([],[]).
less_or_equal_([X/Value0|Rest0],[X/Value1|Rest1]):-

    less_or_equal_el(Value0,Value1),
    less_or_equal_(Rest0,Rest1).

less_or_equal_el(g,g) :- !.
less_or_equal_el(g,any).
less_or_equal_el(ng,ng) :- !.
less_or_equal_el(ng,any).
less_or_equal_el(any,any).

:- export(glb/3).  
:- dom_impl(_, glb/3, [noq]).
:- pred  glb(+ASub0,+ASub1,-Glb): asub * asub * term
   => asub(Glb) + (not_fails, is_det)
   # "`Glb` is the great lower bound of `ASub0` and `ASub1`.".
   
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb(ASub0,ASub1,Glb):-
    ASub0 == ASub1,!,
    Glb = ASub1.
glb(ASub0,ASub1,Glb):-
    glb_(ASub0,ASub1,Glb),!.
glb(_,_,'$bottom').

glb_([],[],[]).
glb_([Xv|ASub0],[Yv|ASub1],[Xv|Glb]):-
    Xv == Yv,!,
    glb_(ASub0,ASub1,Glb).
glb_([X/any|ASub0],[X/Value|ASub1],[X/Value|Glb]):-
    !,
    glb_(ASub0,ASub1,Glb).
glb_([X/Value|ASub0],[X/any|ASub1],[X/Value|Glb]):-
    !,
    glb_(ASub0,ASub1,Glb).

%% %-------------------------------------------------------------------------
%% % extend_free(+,+,-)
%% % extend_free(ASub,Vars,NewASub)
%% %-------------------------------------------------------------------------
%% 
% :- dom_impl(_, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
%% :- pred extend_free(+ASub,+Vars,-NewASub): asub * list * asub.
%% 
%% extend_free(ASub,Vars,NewASub):-
%%      gr_change_values_insert(Vars,ASub,NewASub,ng).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      Intermediate Functions                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- pred gr_simplify_equations(+Term1,+Term2,-Binds)
   #
"It returns in `Binds` the simplified set of primitive equations obtained 
from the unification of `Term1` and `Term2` with the following format:     
(`X`,`Term`,`Tv`) where `X` is a variable, `Term` is a term and `Tv` is
the set of variables in `Term`.
".

%  COMMENT!!!!!!! is sort(Temp,E) needed??????????                        

gr_simplify_equations(Term1,Term2,Binds):-
    gr_free_peel(Term1,Term2,Temp,[]),
    sort(Temp,Binds).

gr_free_peel(Term1,Term2,Binds,Rest) :-
    var(Term1), !,
    varset(Term2,List),
    Binds = [(Term1,Term2,List)|Rest].
gr_free_peel(Term1,Term2,Binds,Rest) :-
    var(Term2), !,
    varset(Term1,List),
    Binds = [(Term2,Term1,List)|Rest].
gr_free_peel(Term1,Term2,Binds,Rest) :-
    Term1 == Term2, !,
    Binds = Rest.
gr_free_peel(Term1,Term2,Binds,Rest) :- 
    functor(Term1,F,N),
    functor(Term2,F,N),
    gr_free_peel_args(0,N,Term1,Term2,Binds,Rest).
    
gr_free_peel_args(N,N,_,_,Binds,Rest) :- !,
    Binds = Rest.
gr_free_peel_args(N1,N,Term1,Term2,Binds,Rest) :-
    N2 is N1 + 1,
    arg(N2,Term1,A1),
    arg(N2,Term2,A2),
    gr_free_peel(A1,A2,Binds,Rest1),
    gr_free_peel_args(N2,N,Term1,Term2,Rest1,Rest).

:- pred gr_change_values_insert(+Vars,+Fr,-NewFr,+Value)
   #
"Forall `X` in `Vars`, if exists `X`/`V` in `Fr` it is changed
to `X`/`Value`, otherwise `X`/`Value` is added to `Fr`. Both ordered.
".

gr_change_values_insert([],Fr,Fr,_):- !.
gr_change_values_insert(Vars,[],NewFr,Value):- !,
    create_values(Vars,NewFr,Value).
gr_change_values_insert([X|Xs],[Y/Val|Fr],NewFr,Value):- 
    compare(D,Y,X),
    gr_change_values_insert_(D,Y/Val,Fr,X,Xs,NewFr,Value).

gr_change_values_insert_(=,_,Fr,X,Xs,[X/Value|NewFr],Value):-
    gr_change_values_insert(Xs,Fr,NewFr,Value).
gr_change_values_insert_(>,Elem,Fr,X,[],NewFr,Value):- !,
    NewFr = [X/Value,Elem|Fr].
gr_change_values_insert_(>,Elem,Fr,X,Xs,[X/Value|NewFr],Value):- 
    gr_change_values_insert(Xs,[Elem|Fr],NewFr,Value).
gr_change_values_insert_(<,Elem,[],X,Xs,NewFr,Value):- !,
    NewFr = [Elem,X/Value|RestFr],
    create_values(Xs,RestFr,Value).
gr_change_values_insert_(<,Elem,Fr,X,Xs,[Elem|NewFr],Value):-
    gr_change_values_insert([X|Xs],Fr,NewFr,Value).

:- pred gr_var_value(+Fr,in_var(X),-Value)
   # "It obtains in the third argument the value of `X` (`g`, `ng` or `any`).".

gr_var_value([Y/V|More],X,Value):-
    compare(D,X,Y),
    gr_var_value_(D,V,More,X,Value).

gr_var_value_(=,Value,_More,_X,Value).
gr_var_value_(>,_Elem,[Y/V|More],X,Value):-
    compare(D,X,Y),
    gr_var_value_(D,V,More,X,Value).

:- pred gr_values_equal(+Vars,+Fr,+Value)
   # "Satisfied if the values of all variables in `Vars` is not equal to `Value`.".

gr_values_notequal([],_,_).
gr_values_notequal([X|Xs],[Y/V|Ys],Value):-
    compare(D,X,Y),
    gr_values_notequal_(D,X,Xs,V,Ys,Value).

gr_values_notequal_(=,_X,Xs,V,Ys,Value):-
    V \== Value,
    gr_values_notequal(Xs,Ys,Value).
gr_values_notequal_(>,X,Xs,_,[Y/V|Ys],Value):-
    compare(D,X,Y),
    gr_values_notequal_(D,X,Xs,V,Ys,Value).


:- pred gr_values_equal(+Vars,+Fr,+Value)
   # "Satisfied if the values of all variables in `Vars` is equal to `Value`.".

gr_values_equal([],_,_).
gr_values_equal([X|Xs],[Y/V|Ys],Value):-
    compare(D,X,Y),
    gr_values_equal_(D,X,Xs,V,Ys,Value).

gr_values_equal_(=,_X,Xs,Value,Ys,Value):-
    gr_values_equal(Xs,Ys,Value).
gr_values_equal_(>,X,Xs,_,[Y/V|Ys],Value):-
    compare(D,X,Y),
    gr_values_equal_(D,X,Xs,V,Ys,Value).

:- pred abs_gunify(Proj,Binds,NewProj,NewBinds)
   #
"It will traverse Binds updating `Proj` (grounding some variables due     
to the bindings in `Binds`), updating and eliminating from `Binds`         
all primitive equations (`X`,`Term`,`Tv`) s.t. `X` or `Term` are ground  
The fixpoint will be reached when both `Proj` and `Binds` remain          
unchanged through one iteration.                                       
".

abs_gunify(Proj,Binds,NewProj,NewBinds):-
    ab_unify(Binds,Proj,Proj1,Binds1),
    fixpoint_gunify(Proj,Binds,Proj1,Binds1,NewProj,NewBinds).

fixpoint_gunify(Proj,Binds,Proj1,Binds1,NewProj,NewBinds):-
    Proj == Proj1,Binds == Binds1,!,
    NewProj = Proj1,
    NewBinds = Binds1.
fixpoint_gunify(_,_,Proj1,Binds1,NewProj,NewBinds):-
    abs_gunify(Proj1,Binds1,NewProj,NewBinds).

ab_unify([],Proj,Proj,[]).

ab_unify([(X,_,Tv)|Binds],Proj,Proj1,NewBinds):-
    gr_var_value(Proj,X,Val),
    Val = g,!,
    gr_change_values_insert(Tv,Proj,NewProj,g),
    ab_unify(Binds,NewProj,Proj1,NewBinds).
ab_unify([(X,_,Tv)|Binds],Proj,Proj1,NewBinds):-
    gr_values_equal(Tv,Proj,g),!,
    gr_change_values_insert([X],Proj,NewProj,g),
    ab_unify(Binds,NewProj,Proj1,NewBinds).

% ab_unify([(X,Term,Tv)|Binds],Proj,Proj1,NewBinds):-
%       nonvar(Term),!,
%       gr_change_values_insert([X],Proj,NewProj,ng),
%       NewBinds = [(X,Term,Tv)|RestBinds],
%       ab_unify(Binds,NewProj,Proj1,RestBinds).

ab_unify([(X,Term,Tv)|Binds],Proj,Proj1,NewBinds):-
    NewBinds = [(X,Term,Tv)|RestBinds],
    ab_unify(Binds,Proj,Proj1,RestBinds).

:- pred collect_vars_gr(+Abs,-Vars)
   # "It returns in `Vars` the list of variables in `Abs`.".

collect_vars_gr([],[]).
collect_vars_gr([X/_|Rest],[X|Vars]):-
    collect_vars_gr(Rest,Vars).

%%%%%%%%%%%%%%%%% to do %%%%%
% propagate_downwards_closed(gr,ASub1,ASub2,ASub):-
%       gr_downwards_closed(ASub1,ASub2,ASub).

% del_real_conjoin(gr,ASub1,ASub2,ASub):-
%       gr_real_conjoin(ASub1,ASub2,ASub).

% del_hash(gr,ASub,Vars,N):- 
%       gr_hash(ASub,Vars,N).

% more_instantiate(gr,ASub1,ASub2):-
%       gr_more_instantiate(ASub1,ASub2).

% convex_hull(gr,Old,New,Hull):-
%       gr_convex_hull(Old,New,Hull).

% del_check_cond(gr,Cond,ASub,Sv,Flag,WConds):-
%       gr_check_cond(Cond,ASub,Sv,Flag,WConds).

% del_impose_cond(gr,LCond,Sv,ASub,LASub):-
%       gr_impose_cond(LCond,Sv,ASub,LASub).
%%%%%%%%%%%%%%%%% to do %%%%%
