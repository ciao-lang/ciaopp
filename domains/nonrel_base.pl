% (included file)

% :- doc(title, "Base for Non Relational Domains").
% :- doc(author, "Isabel Garcia-Contreras").
% (see nonrel_base_doc.pl for documentation)

:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(sets), [merge/3]).

%-----------------------------------------------------------------------
% (Predicates to be implemented by the domain extending this base)

% TODO: use a dedicated 'interval' trait?

% TODO: discontiguous is not needed unless we do traits
:- discontiguous(nonrel_top/2).
:- discontiguous(nonrel_bot/2).
:- discontiguous(nonrel_var/2).
:- discontiguous(nonrel_amgu/5). % TODO: make nonrel_base call the domain operation instead?
:- discontiguous(nonrel_less_or_equal_elem/3).
:- discontiguous(nonrel_compute_glb_elem/4).
:- discontiguous(nonrel_compute_lub_elem/4).
:- discontiguous(nonrel_widen_elem/4).
%:- discontiguous(nonrel_input_interface/5).
:- discontiguous(nonrel_special_builtin0/5).
:- discontiguous(nonrel_call_to_success_builtin0/7).

:- doc(doinclude, nonrel_top/2).
:- pred nonrel_top(AbsInt, X) # "@var{X} is the representation of
   ``top'' in the abstract domain.
   @begin{alert}(implement in derived domain)@end{alert}".

:- doc(doinclude, nonrel_bot/2).
:- pred nonrel_bot(AbsInt, X) # "@var{X} is the representation of
   ``bot'' in the abstract domain.
   @begin{alert}(implement in derived domain)@end{alert}".

:- doc(doinclude, nonrel_var/2).
:- pred nonrel_var(AbsInt, X) # "@var{X} is the abstraction of a free
   variable in the abstract domain.
   @begin{alert}(implement in derived domain)@end{alert}".

%:- export(nonrel_amgu/5).
:- doc(doinclude, nonrel_amgu/5).
:- pred nonrel_amgu(+AbsInt, +Term1,+Term2,+ASub0,-NASub) #
   "@var{NASub} is the abstract unification of @var{Term1} and
   @var{Term2}, with @var{ASub0} an abstract substitution that
   represents the state of both terms.
   @begin{alert}(implement in derived domain)@end{alert}".
% TODO: The abstract unification could be simplified even more if domains are
% non relational

:- doc(doinclude, nonrel_less_or_equal_elem/3).
:- pred nonrel_less_or_equal_elem(+AbsInt,+E1,+E2) #"
   Succeeds if @var{E1} is smaller than @var{E2}.
   @begin{alert}(implement in derived domain)@end{alert}".

:- doc(doinclude, nonrel_compute_glb_elem/4).
:- pred nonrel_compute_glb_elem(+AbsInt,+E1,+E2,EG) #"
   @var{EG} is the @em{greatest lower bound} of @var{E1} and @var{E2}.
   @begin{alert}(implement in derived domain)@end{alert}".

:- doc(doinclude, nonrel_compute_lub_elem/4).
:- pred nonrel_compute_lub_elem(+AbsInt,+E1,+E2,EL) #"
   @var{EL} is the @em{least upper bound} of @var{E1} and @var{E2}.
   @begin{alert}(implement in derived domain)@end{alert}".

:- doc(doinclude, nonrel_widen_elem/4).
:- pred nonrel_widen_elem(+AbsInt,+E1,+E2,EW) #"
   @var{EW} is the @em{widening} of @var{E1} and @var{E2}.
   @begin{alert}(implement in derived domain)@end{alert}".

%-----------------------------------------------------------------------
% :- doc(section, "Generic functionality for non-relational domains").

%:- export(nonrel_unknown_entry/4).
:- doc(doinclude, nonrel_unknown_entry/4).
:- pred nonrel_unknown_entry(+AbsInt,+Sg,+Vars,-Call) : atm * cgoal * list * term
    #"Gives the ``top'' value for a given set of variables @var{Vars},
    resulting in abstract constraint @var{Call}.".
nonrel_unknown_entry(AbsInt,_Sg,Qv,Call):-
    nonrel_top(AbsInt,Top),
    nonrel_create_asub(Qv,Top,Call).

% ---------------------------------------------------------------------------
% Operations on abstract substitutions
:- pred nonrel_create_asub(+Vars,+Value,-Asub) : list * term * term # 
    "Forall @var{X} in @var{Vars}, @var{X}/@var{Value} is in @var{Asub}".
nonrel_create_asub([],_Value,[]).
nonrel_create_asub([X|Xs],Value,[X/Value|New]):-
    nonrel_create_asub(Xs,Value,New).

nonrel_replace_value_asub([],_,_,[]).
nonrel_replace_value_asub([V/_|Vs],Var,Value,[V/Value|Vs]):-
    Var == V, !.
nonrel_replace_value_asub([V|Vs],Var,Value,[V|New]):-
    nonrel_replace_value_asub(Vs,Var,Value,New).

:- pred nonrel_get_value_asub(+ASub,+Var,-Value)
    #"This predicate fails if @var{Var} is not in @var{Asub}".
nonrel_get_value_asub([Var/Val|ASub],V1,Value) :-
    ( Var == V1 ->
        Value = Val
    ;
        nonrel_get_value_asub(ASub,V1,Value)
    ).

% ---------------------------------------------------------------------------
:- pred nonrel_empty_entry(+AbsInt,+Vars,-Entry) : atm * list * term
    #"Obtains the abstraction of a substitution in which all variables
      @var{Vars} are unbound: free and unaliased.".
nonrel_empty_entry(AbsInt,Vars,Entry) :-
    nonrel_var(AbsInt,VarValue),
    nonrel_create_asub(Vars,VarValue,Entry).

%:- export(nonrel_abs_sort/2).
:- doc(doinclude, nonrel_abs_sort/2).
:- pred nonrel_abs_sort(+Asub,-Asub_s): term * term
    # "It sorts the set of @var{X}/@var{Values} in @var{Asub} obtaining
      @var{Asub_s}".
nonrel_abs_sort('$bottom','$bottom'):- !. % TODO: this clause should be generic
                                      % for all abstract domains
nonrel_abs_sort(Asub,Asub_s):-
    sort(Asub,Asub_s).

%:- export(nonrel_project/3).
:- doc(doinclude, nonrel_project/3).
:- pred nonrel_project(+Asub,+Vars,-Proj): term * list * term # 
    "@var{Proj} is the result of eliminating from @var{Asub} all
      @var{X}/@var{Value} such that @var{X} is not in @var{Vars}".
nonrel_project('$bottom',_,Proj) :- !, 
    Proj = '$bottom'.
nonrel_project(ASub,Vars,Proj) :- 
    project_aux(Vars,ASub,Proj).

:- pred project_aux(+Vars,+ASub,-Proj): list * list * term # 
    "Eliminates from each list in the second argument any variable/value
    such that the variable is not an element of @var{Vars}".
project_aux([],_,Proj):- !,
    Proj = [].
project_aux(_,[],Proj):- !,
    Proj = [].
project_aux([Var|Vs],[V2/Val|ASub],[V2/Val|Proj]) :-
    Var == V2, !,
    project_aux(Vs, ASub, Proj).
project_aux([Var|Vs], [_|ASub], NASub0) :-
    project_aux([Var|Vs], ASub, NASub0).

%:- export(nonrel_call_to_entry/10).
:- doc(doinclude, nonrel_call_to_entry/10).
:- pred nonrel_call_to_entry(+AbsInt,+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo)
    : atm * list * cgoal * list * cgoal * term * list * term * term * term

    #"It obtains the abstract substitution @var{Entry} which results from
    adding the abstraction of @var{Sg} = @var{Head} to @var{Proj}, later
    projecting the resulting substitution onto @var{Hv}.

    In the general case, the steps are:
    @begin{itemize}
    @item Add to @var{Proj} the variables of @var{Hv} with a ``top'' value.
    @item Perform the abstract unification of @var{Sg} and @var{Head}.
    @item Add to the unification the variables of @var{Fv} with a ``top'' value.
    @item Project to the variables in @var{Hv} and @var{Fv}.
 @end{itemize} ".

nonrel_call_to_entry(_,_Sv,_Sg,_Hv,_Head,_K,_Fv,'$bottom','$bottom',no) :- !.
nonrel_call_to_entry(AbsInt,_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo) :-
    variant(Sg,Head), !,
    copy_term((Sg,Proj),(NewTerm,NewProj)),
    Head = NewTerm,
    nonrel_abs_sort(NewProj,Entry0),
    nonrel_top(AbsInt,Top),
    insert_values_asub(Fv,Entry0,Top,Entry),
    ExtraInfo = yes.
nonrel_call_to_entry(AbsInt,_,_,[],_Head,_K,Fv,Proj,Entry,Proj) :- !, % head has no variables
    nonrel_top(AbsInt,Top),
    nonrel_create_asub(Fv,Top,Entry).
nonrel_call_to_entry(AbsInt,_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,Proj) :- 
    nonrel_top(AbsInt,Top),
    insert_values_asub(Hv,Proj,Top,Call0), % Add variables of the clause head
    nonrel_amgu(AbsInt,Sg,Head,Call0,Call),       % Unify clauses
    merge(Hv,Fv,HvFv),
    nonrel_project(Call,HvFv,Entry0),      % Project to the variables in the clause
    nonrel_bot(AbsInt,Bot),
    ( member(_/Bot, Entry0) ->
        Entry = Bot
    ;
        insert_values_asub(Fv, Entry0, Top, Entry)
    ).

:- pred insert_values_asub(+NewVars, +ASub, +AbsElem, -NewASub)
    #"Inserts values in an abstract substitution @var{ASub}, asigning each
    variable in @var{NewVars} @var{AbsElem} producing @var{NewASub}.
    @var{NewVars} has to be sorted.".
insert_values_asub([], [], _, []) :- !.
insert_values_asub([], ASub, _, ASub) :- !.
insert_values_asub([V|Vs], [], AbsElem, [V/AbsElem|NASub0]) :- !,
    insert_values_asub(Vs, [], AbsElem, NASub0).
insert_values_asub([V|Vs], [X/Val|ASub], AbsElem, [V/AbsElem|NASub0]) :-
    V @< X, !,
    insert_values_asub(Vs, [X/Val|ASub], AbsElem, NASub0).
insert_values_asub(Vs, [X/Val|ASub], AbsElem, [X/Val|NASub0]) :-
    insert_values_asub(Vs, ASub, AbsElem, NASub0).

%:- export(nonrel_exit_to_prime/8).
:- doc(doinclude, nonrel_exit_to_prime/8).
:- pred nonrel_exit_to_prime(+AbsInt,+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime)
    : atm * list * list * cgoal * cgoal * term * term * term # 
 "".
nonrel_exit_to_prime(_,_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !, % generic
    Prime = '$bottom'.
nonrel_exit_to_prime(_,Sg,Hv,Head,_Sv,Exit,yes,Prime):- !, % generic
    nonrel_project(Exit,Hv,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    nonrel_abs_sort(NewPrime,Prime).        
nonrel_exit_to_prime(AbsInt,Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime):-
    ( ExtraInfo = no ->
        nonrel_top(AbsInt,Top),
        nonrel_create_asub(Sv,Top,Proj)
    ;
        Proj = ExtraInfo
    ),
    nonrel_project(Exit,Hv,BPrime),
    merge(BPrime,Proj,TPrime),
    % need to add variables here, merge substitutions?
    nonrel_amgu(AbsInt,Head,Sg,TPrime,NewTempPrime),
    nonrel_project(NewTempPrime,Sv,Prime0),
    nonrel_bot(AbsInt,Bot),
    ( member(_/Bot, Prime0) ->
        Prime = Bot
    ;
        Prime = Prime0
    ).

%:- export(nonrel_compute_lub/3).
:- doc(doinclude, nonrel_compute_lub/3).
:- pred nonrel_compute_lub(+AbsInt,+ListASub,-Lub) : atm * list * term
    #"@var{Lub} is the @em{least upper bound} of the list of abstract
     substitutions @var{ListASub}.".
nonrel_compute_lub(AbsInt,ListASub, Lub) :-
    nonrel_compute_lub_list(ListASub, AbsInt, Lub).

:- pred nonrel_compute_lub_list(+ListASub,+AbsInt,-Lub) : list * atm * term.
nonrel_compute_lub_list([X],_,X) :- !.
nonrel_compute_lub_list([ASub1,ASub2|Xs],AbsInt,Lub):-
    nonrel_compute_lub_pair(ASub1,ASub2,AbsInt,ASubLub),
    nonrel_compute_lub_list([ASubLub|Xs],AbsInt,Lub).

:- pred nonrel_compute_lub_pair(+ASub1,+ASub2,+AbsInt,-Lub)
    : list * list * atm * term.
nonrel_compute_lub_pair('$bottom',ASub,_,ASub):- !.
nonrel_compute_lub_pair(ASub,'$bottom',_, ASub):- !.
nonrel_compute_lub_pair(ASub1,ASub2,AbsInt,Lub):- 
    compute_lub_pair(ASub1,ASub2,AbsInt,Lub).

% TODO: assuming that they have the same variables and that both Abstract
% substitutions are sorted
compute_lub_pair([],[],_,[]).
compute_lub_pair([X/Vx|ASub1],[Y/Vy|ASub2],AbsInt,[X/Lub|ASubLub]):-
    X == Y, !,
    nonrel_compute_lub_elem(AbsInt,Vx,Vy,Lub),
    compute_lub_pair(ASub1,ASub2,AbsInt,ASubLub).
compute_lub_pair(_,_,_,_):-
    throw(error(variable_mismatch, nonrel_compute_lub/3)).

%:- export(nonrel_extend/5).
:- doc(doinclude, nonrel_extend/5).
:- pred nonrel_extend(+AbsInt,+Prime,Sv,+Call,-Succ)
    : atm * term * list * term * term.
nonrel_extend(_,'$bottom',_Sv,_Call,Succ):- !, % generic
    Succ = '$bottom'.
nonrel_extend(_,_Prime,[],Call,Succ):- !,      % generic
    Call = Succ.
nonrel_extend(AbsInt,Prime_u,_Sv,Call_u,Succ) :-
    % TODO: unnecessary sort?
    nonrel_abs_sort(Prime_u, Prime),
    nonrel_abs_sort(Call_u, Call),
    nonrel_extend_(Prime,Call,AbsInt,Succ).

nonrel_extend_([], X, _, X) :- !.              % generic
nonrel_extend_(_, [], _, []) :- !.             % generic
nonrel_extend_([X1/V1|ASub1], [X2/V2|ASub2], AbsInt, Succ) :-
    X1 == X2, !,
    nonrel_compute_glb_elem(AbsInt,V1,V2,NV),
    Succ = [X1/NV|RSucc],
    nonrel_extend_(ASub1, ASub2, AbsInt, RSucc).
nonrel_extend_([X1/V1|ASub1], [X2/V2|ASub2], AbsInt, Succ) :-  % generic
    ( X1 @< X2 ->
        nonrel_extend_(ASub1, [X2/V2|ASub2], AbsInt, Succ)
    ;
        nonrel_extend_([X1/V1|ASub1], ASub2, AbsInt, RSucc),
        Succ = [X2/V2|RSucc]
    ).

%:- export(nonrel_call_to_success_fact/10).
:- doc(doinclude, nonrel_call_to_success_fact/10).
:- pred nonrel_call_to_success_fact(+AbsInt,+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
    : atm * cgoal * list * cgoal * list * term * term * term * term * term 
    #"Specialized version of @pred{call_to_entry/9} + @pred{exit_to_prime/7}
    + @pred{extend/4} for facts".
nonrel_call_to_success_fact(AbsInt,_,_,_,_,_,Call,Proj,Bot,Bot) :-
    nonrel_bot(AbsInt,Bot),
    ( Proj = Bot ; Call = Bot ), !.
nonrel_call_to_success_fact(AbsInt,Sg,Hv,Head,_K,Sv,Call,Proj,Prime,Succ) :-
    nonrel_top(AbsInt,Top),
    insert_values_asub(Hv,Proj,Top,Call0),
    nonrel_amgu(AbsInt,Sg,Head,Call0,Tmp),
    nonrel_project(Tmp,Sv,Prime),
    nonrel_extend(AbsInt,Prime,Sv,Call,Succ).

%:- export(nonrel_special_builtin/5).
:- doc(doinclude, nonrel_special_builtin/5).
:- pred nonrel_special_builtin(+AbsInt,+SgKey,+Sg,-Type,-Condvars)
    : atm * predname * cgoal * atm * term
    #"@begin{alert}This predicate needs to be implemented by the
    user.@end{alert}".
nonrel_special_builtin(_,'=/2',_,_,_) :- !.
nonrel_special_builtin(_,'==/2',_,_,_) :- !.
nonrel_special_builtin(_,'true/0',_,_,_) :- !.
% true/0 is necessary but it does not need a specific implementation in
% "call_to_success_builtin", it is included in the fixpoints
nonrel_special_builtin(AbsInt,SgKey,Sg,Type,Condvars) :-
    nonrel_special_builtin0(AbsInt,SgKey,Sg,Type,Condvars).

%:- export(nonrel_success_builtin/5).
:- doc(doinclude, nonrel_success_builtin/5).
:- pred nonrel_success_builtin(+AbsInt,+Type,+Condv,+Call,-Succ)
    : atm * atm * term * term * term
    #"Obtains the success for some particular builtins.".
nonrel_success_builtin(_,_,_,_,_). % TODO: not finished, Succ is unbound (JF)

%:- export(nonrel_call_to_success_builtin/7).
:- doc(doinclude, nonrel_call_to_success_builtin/7).
:- pred nonrel_call_to_success_builtin(+AbsInt,+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)
    : atm * predname * cgoal * list * term * term * term
    #"Handles those builtins for which computing @var{Proj} is easier than
    @var{Succ}. Currently only builtins @pred{=/2} and @pred{==/2} are
    implemented. More builtins can be added by the user.".
nonrel_call_to_success_builtin(AbsInt,SgKey,Sg,Sv,Call,Proj,Succ) :-
    nonrel_call_to_success_builtin_(SgKey,AbsInt,Sg,Sv,Call,Proj,Succ0),
    nonrel_bot(AbsInt,Bot),
    ( member(_/Bot, Succ0) ->
        Succ = Bot
    ;
        Succ = Succ0
    ).

nonrel_call_to_success_builtin_('=/2',AbsInt,'='(X,Y),_Sv,Call,_Proj,Succ) :- !, % generic
    nonrel_amgu(AbsInt,X,Y,Call,Succ).
% More builtins may be added by the user.
nonrel_call_to_success_builtin_('==/2',AbsInt,'=='(X,Y),_Sv,Call,_Proj,Succ) :- !, % generic
    nonrel_amgu(AbsInt,X,Y,Call,Succ).
% X and Y have asociated a value of type interval asub. asuming runtime
% semantics of the operator (i.e. X and Y are instantiated, otherwise an error
% is raised and the execution is stops)
nonrel_call_to_success_builtin_(SgKey,AbsInt,Sg,Sv,Call,Proj,Succ) :-
    nonrel_call_to_success_builtin0(AbsInt,SgKey,Sg,Sv,Call,Proj,Succ).

%:- export(nonrel_input_user_interface/4).
:- doc(doinclude, nonrel_input_user_interface/4).
:- pred nonrel_input_user_interface(+AbsInt,+InputUser,+Qv,+ASub)
    #"Obtains the abstract substitution from the native properties
 found in the user supplied info.".
nonrel_input_user_interface(AbsInt,_,Qv,ASub) :-
    nonrel_top(AbsInt,T),
    nonrel_create_asub(Qv,T,ASub).
% TODO: Currently it is implemented as by "abstracting" the user input as top

%:- export(nonrel_input_interface/5).
:- doc(doinclude, nonrel_input_interface/5).
:- pred nonrel_input_interface(+AbsInt,+Prop,?Kind,+Struc0,+Struc1)
# "Adds native property @var{Prop} to the structure accumulating the
    properties relevant to this domain.".
% To simplify the operations, a body is created and will be processed as such in
% the input_user_interface predicate
% TODO: No properties processed because as default operation we abstract the
% entry as top (more precise understanding of the properties should be
% implemented by the user).
nonrel_input_interface(_AbsInt,_Prop,_Kind,_Struct0,_Struct1). % TODO: not finished

%:- export(nonrel_asub_to_native/6).
:- doc(doinclude, nonrel_asub_to_native/6).
:- pred nonrel_asub_to_native(+AbsInt,+ASub,+Qv,+OutFlag,-ASub_user,-Comps) : 
   atm * term * term * term * term * term
   #"It translates an internal abstract constraint into something
     friendly for the user.".

nonrel_asub_to_native(_AbsInt,_Qv,_,ASub,ASub,[]).
% [IG] for now we output the raw internal representation. This predicate could
% be "overwritten by the developer of the domain."

%:- export(nonrel_unknown_call/5).
:- doc(doinclude, nonrel_unknown_call/5).
:- pred nonrel_unknown_call(+AbsInt,+Sg,+Vars,+Call,-Succ)
    : atm * cgoal * list * term * term
    #"Gives the ``top'' value for the variables involved in a literal whose
    definition is not present, and adds this top value to @var{Call}".
nonrel_unknown_call(AbsInt,_Sg,Vars,Call,Succ):-
    nonrel_top(AbsInt,Top),
    insert_values_asub(Vars,Call,Top,Succ).

%:- export(nonrel_less_or_equal/3).
:- doc(doinclude, nonrel_less_or_equal/3).
:- pred nonrel_less_or_equal(+AbsInt,+ASub0,+ASub1): atm * term * term # 
"Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
it is assumed the two abstract substitutions are defined on the same variables".
nonrel_less_or_equal(_, '$bottom',_) :- !.
nonrel_less_or_equal(AbsInt,ASub0,ASub1):-
    nonrel_less_or_equal_(ASub0,AbsInt,ASub1).

nonrel_less_or_equal_([],_, []) :- !.
nonrel_less_or_equal_([X/Value0|Rest0],AbsInt,[Y/Value1|Rest1]):-
    X == Y, !,
    nonrel_less_or_equal_elem(AbsInt,Value0,Value1),
    nonrel_less_or_equal_(Rest0,AbsInt,Rest1).
nonrel_less_or_equal_(_,_,_):-
    throw(error(variable_mismatch, nonrel_less_or_equal/2)).

%:- export(nonrel_glb/4).
:- doc(doinclude, nonrel_glb/4).
:- pred nonrel_glb(+AbsInt,+ASub0,+ASub1,-Glb): atm * list * list * var 
    #"@var{Glb} is the great lower bound of @var{ASub0} and @var{ASub1}, two
    substitutions that describe the same set of variables.".
nonrel_glb(_, '$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
nonrel_glb(_, _ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
nonrel_glb(_,ASub0,ASub1,Glb):-  % TODO: unnecessary case?
    ASub0 == ASub1,!,
    Glb = ASub1.
nonrel_glb(AbsInt,ASub0,ASub1,Glb):-
    nonrel_glb_(ASub0,ASub1,AbsInt,Glb), !.
nonrel_glb(_,_,_,'$bottom').

nonrel_glb_([],[],_,[]) :- !.
nonrel_glb_([X/Value1|ASub0],[Y/Value2|ASub1], AbsInt,[X/NValue|Glb]) :-
    X == Y, !,
    nonrel_compute_glb_elem(AbsInt,Value1, Value2, NValue),
    nonrel_glb_(ASub0,ASub1,AbsInt,Glb).
nonrel_glb_(_,_,_,_) :-
    throw(error(variable_mismatch, nonrel_glb/3)).

%:- export(nonrel_identical_abstract/2).
:- doc(doinclude, nonrel_identical_abstract/2).
% Note: [IG] When checking identical projs (i.e. Sg+Proj) the heads are already
% unified in domains.pl
:- pred nonrel_identical_abstract(+ASub1, +ASub2).
nonrel_identical_abstract(ASub1, ASub2) :-
    ASub1 == ASub2.

%:- export(nonrel_widen/4).
:- doc(doinclude, nonrel_widen/4).
% Assuming that both abstract substitutions are sorted.
:- pred nonrel_widen(+AbsInt,+Asub1,+ASub2,-WAsub).
% reasoning with bottom same as in eterms (this could be dealt with in the
% fixpoint algorithm)
nonrel_widen(AbsInt,Asub1,ASub2,WAsub) :- 
    nonrel_widen_(Asub1,AbsInt,ASub2,WAsub).

nonrel_widen_('$bottom',_,'$bottom','$bottom') :- !. % generic
nonrel_widen_('$bottom',_,Prime,Prime) :- !.         % generic
nonrel_widen_(Prime,_,'$bottom',Prime) :- !.         % generic
nonrel_widen_([],_,[],[]) :- !.                      % generic
nonrel_widen_([X/V1|ASub1],AbsInt,[Y/V2|ASub2],[X/VW|WAsub]) :-
    X == Y, !,
    nonrel_widen_elem(AbsInt,V1, V2, VW),
    nonrel_widen_(ASub1,AbsInt,ASub2,WAsub).
nonrel_widen_(_,_,_,_):-
    throw(error(variable_mismatch, nonrel_widen/3)).

%:- export(nonrel_widencall/4).
:- doc(doinclude, nonrel_widencall/4).
:- pred nonrel_widencall(+AbsInt,+Asub1,+ASub2,-WAsub).
nonrel_widencall(AbsInt,Asub1,ASub2,WAsub) :-
    nonrel_widen_(Asub1,AbsInt,ASub2,WAsub).
