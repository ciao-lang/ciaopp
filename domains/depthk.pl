:- module(depthk, [], [assertions]).

% ------------------------------------------------------------------------%
%                                                                         %
% Programmer: Francisco Bueno                                             %
% Date:       February 1, 1995                                            %
%                                                                         %
% ------------------------------------------------------------------------%
% MODULE: "depthk": the depth-k domain                                    %
% ------------------------------------------------------------------------%
% substitutions are (sorted) lists of unification equations - X=term      %
% memo lists of substitutions not singletons (lub as disjunction)         %
% lub as disjunction selected with a flag - real lub not yet implemented! %
% ------------------------------------------------------------------------%
:- doc(bug,"tried to keep ""project"" reasonable but it seems wrong!").
:- doc(title, "depthk  abstract domain").

:- doc(author, "Francisco Bueno").
:- doc(author, "Daniel Jurjo Rivas (improvements and bug fixes)").
:- doc(module, "

This tutorials aims to explain how depthk analysis works.


@section{The abstract substitution}

The abstract substitution of this domains consists in a sorted list of
idempotent unification equations (or bottom).  For example:

@begin{verbatim} 
[X=_, Y=g(X)]
@end{verbatim} 
is not a proper abstract substitution since X appears both in the left
and the right side. The correct abstract substitution would be:

@begin{verbatim} 
[X = A, Y = g(A)]
@end{verbatim} 

Notice that X = A does not means that X is a variable. It means that
we do not know anything about X (i.e. is top)

@section{How to run the analysis}
We can run this analysis as we do with others. In that case the depth
is set to one. If we want to change the depth of the analysis we have
to type in the CiaoPP top-level:

@begin{verbatim}
?- set_pp_flag(depthk_k, N). 
@end{verbatim}

with N a natural number (and this excludes the 0).

@section{Some examples}

@subsection{Example 1}

Consider this dummy predicate:

ex1(X) :- 
    X = f(a, Y), 
    Y = g(h(k(a, b, c))).
 
the results of the analysis with K = 1 is:
@begin{verbatim}
:- true pred ex1(X)
   => instance(X,f(_A,_B)).
@end{verbatim}

Let us check the results with another values of K:

@begin{enumerate}
@item K = 2 we obtain: instance(X,f(a,g(_A))).
@item K = 3 we obtain: instance(X,f(a,g(h(_A)))).
@item K = 4 we obtain: instance(X,f(a,g(h(k(_A,_B,_C))))).
@item K = 5 we obtain: instance(X,f(a,g(h(k(a,b,c))))).

@end{enumerate}

This analysis is quite more useful when recursion arises:

@subsection{Example 2}
Consider the following example:

@begin{verbatim}
ex(X) :-
    li(Y),
    X = g(s(a, Y), Z).

li(f(a, a, f(b,b, f(c,c, nil)))).
li(f(a, a, f(b,b,T))) :-
    li(T).
@end{verbatim}

in this case with the default depth we obtain:

@begin{verbatim}
:- true pred ex(X)
   => instance(X,g(_A,_B)).

@end{verbatim}

Let us check the results with another values of K:

@begin{enumerate}
@item K = 2 we obtain: instance(X,g(s(_B,_C),_A)).
@item K = 3 we obtain: instance(X,g(s(a,f(_B,_C,_D)),_A)).
@item K = 4 we obtain: instance(X,g(s(a,f(a,a,f(_B,_C,_D))),_A)).
@item K = 5 we obtain: instance(X,g(s(a,f(a,a,f(b,b,f(_B,_C,_D)))),_A)).
@end{enumerate}


@section{More in depth}

Consider the following example:
@begin{verbatim}
r(Y, Z) :-
    Y = g(L),
    M = f(K), 
    Z = f(Y).
@end{verbatim}


If we execute the analysis with a raw output (that can be activated
typing set_pp_flag(output_lang, raw). in the toplevel) we get:

@begin{verbatim}
r(Y,Z) :-
    true(2,[[Y=_,Z=_,L=_,M=_,K=_]]),
    'term_basic:='(Y,g(L)),
    true(2,[[Y=g(F),Z=_,L=F,M=_,K=_]]),
    'term_basic:='(M,f(K)),
    true(2,[[Y=g(G),Z=_,L=G,M=f(H),K=H]]),
    'term_basic:='(Z,f(Y)),
    true(2,[[Y=g(I),Z=f(g(I)),L=I,M=f(J),K=J]]).

@end{verbatim}

In this case we can see that all the program variables are represented
in the abstract substitution. Moreover each variables in the left side
of a unification is a program variable. Notice that we do not know if
they are free or not with the given information.

").
% -----------------------------------------------------------------------

:- include(ciaopp(plai/plai_domain)).
:- dom_def(depthk, [default]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(domain(s_eqs), 
    [ apply/1, eqs_ranges/6, keys_and_values/3, peel/4, subtract_keys/3 ]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(sets), 
    [ insert/3, merge/3, ord_member/2, ord_subset/2, ord_subtract/3, ord_intersection/3, ord_subset_diff/3, ord_union/3 ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), 
    [ instance/2, 
      most_specific_generalization/3, 
      most_general_instance/3,
      variant/2
    ]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(write), [numbervars/3]).

depth_k(K):- current_pp_flag(depthk_k,K).

%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% call_to_entry(+,+,+,+,+,+,+,-,-)                                       %
% call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo)                 %
%------------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).

call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,Flag):- 
    variant(Sg,Head),!,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    depthk_bu_project(NewProj_u, Hv, NewProj), % This projection is needed to capture the depth. It is also coherent with how call to entry is done usually (see eterms).
    abs_sort(NewProj, NewProj1),
    variables_are_variables(Fv,Free),
    merge(Free,NewProj1,Entry).
call_to_entry(Sv, Sg,[], Head, _K, [], Proj, Entry, Unifiers) :-  %% [DJ] this case is only needed to ensure combination. In a "normal" execution call_to_success_fact will be called instead
    peel(Head, Sg, Unifiers, []),
    depthk_unify(Unifiers, Proj, Entry0), !,
    depthk_bu_project(Entry0, Sv, Entry1),
    abs_sort(Entry1, Entry).
call_to_entry(_Sv,_Sg,[],_Head,_K,Fv,_Proj,Entry,no):- !,
    variables_are_variables(Fv,Entry).
call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,Unifiers):-
    peel(Head, Sg, Unifiers,[]), 
    depthk_unify(Unifiers,Proj,Entry0), !,
    depthk_bu_project(Entry0,Hv,Entry1),
    abs_sort(Entry1,Entry2),
    variables_are_variables(Fv,Tmp),
    merge(Tmp,Entry2,Entry).
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- export(variables_are_variables/2). %% 
variables_are_variables([V|Fv],[V=_|ASub]):-
    variables_are_variables(Fv,ASub).
variables_are_variables([],[]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Exit To Prime                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% exit_to_prime(+,+,+,+,+,-,-)                                           %
% exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime)                      %
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

:- dom_impl(_, exit_to_prime/7, [noq]).
exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_Flag,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    abs_sort(NewPrime,Prime).        
exit_to_prime(_Sg,[],_Head,_Sv,_Exit,_ExtraInfo,Prime):- !,
    Prime = [].
exit_to_prime(Sg,_Hv,Head,Sv,Exit,_Unifiers,Prime):-
    peel(Sg, Head, Unifiers, []),  !, % Sometimes it is not getting the Proper unifiers so it is more easy to create our own. This happens when combinating it since call_to_success_fact is not executed
    depthk_unify(Unifiers,Exit,Prime0),
    depthk_bu_project(Prime0,Sv,Prime1),
    abs_sort(Prime1,Prime).
exit_to_prime(_Sg,_Hv,_Head,Sv,Exit,Unifiers,Prime):-
    depthk_unify(Unifiers,Exit,Prime0),
    depthk_bu_project(Prime0,Sv,Prime1),
    abs_sort(Prime1,Prime).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend                                   %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% extend(+,+,+,+,-)                                                      %
% extend(Sg,Prime,Sv,Call,Succ)                                          %
% If Prime = bottom, Succ = bottom. If Sv = [], Call = Succ. Otherwise,  %
% just add to Prime equs. for variables in Call and not in Prime.        %
%------------------------------------------------------------------------%

:- dom_impl(_, extend/5, [noq]).
extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
extend(_Sg,_Prime,[],Call,Succ):- !,
    Call = Succ.
extend(Sg,Prime,Sv,Call,Succ):-
    sub2prime_and_replace(Prime, Call, TCall), !, %% [DJ] 9-jul-23 added the cut
    %% This call should capture all the variables
    % that are not being replaced in Prime
    variables_are_variables(Cv,TCall),
    ord_subtract(Cv,Sv,Nv),
    project(Sg,Nv,not_provided_HvFv_u,TCall,Succ0),
    merge(Succ0,Prime,Succ).
extend(_, _, _, _, '$bottom'). %% [DJ] 9-jul-23 added this case
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION                               %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% project(+,+,+,+,-)                                                     %
% project(Sg,Vars,HvFv_u,ASub,Proj)                                      %
% Leave in Proj only equs. related to Vars                               %
%------------------------------------------------------------------------%

:- dom_impl(_, project/5, [noq]).
project(_,_,_,'$bottom',Proj):- !,
    Proj = '$bottom'.
project(_Sg,[],_HvFv_u,_ASub,[]):- !.
project(_Sg,Vars,_HvFv_u,ASub,Proj):-
    discriminate_equs(ASub,Vars,Proj,_,_).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT SORT                                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% abs_sort(+,-)                                                          %
% abs_sort(Asub_u,Asub)                                                  %
% Sorts the list of equs.                                                %
%------------------------------------------------------------------------%

:- dom_impl(_, abs_sort/2, [noq]).
abs_sort('$bottom','$bottom'):- !.
abs_sort(ASub_u,ASub):-
    sort(ASub_u,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT LUB                                      %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% compute_lub(+,-)                                                       %
% compute_lub(ListASub,Lub)                                              %
%------------------------------------------------------------------------%

:- dom_impl(_, compute_lub/2, [noq]).
compute_lub([ASub],Lub):- !,
    Lub = ASub.
compute_lub([ASub1,ASub2|ListASub],Lub):-
    compute_lub_(ASub1,ASub2,Lub0),
    compute_lub([Lub0|ListASub],Lub).

compute_lub_('$bottom',ASub,Lub):- !, Lub = ASub.
compute_lub_(ASub,'$bottom',Lub):- !, Lub = ASub.
compute_lub_(ASub1,ASub2,Lub):-
    lub_each_eq(ASub1,ASub2,Lub).

lub_each_eq([],ASub, ASub).  
lub_each_eq([X=T1|ASub1],[X=T2|ASub2],[X=T|Lub]):-
    most_specific_generalization(T1,T2,T),
    lub_each_eq(ASub1,ASub2,Lub).

%------------------------------------------------------------------------%
% glb(+,-)                                                               %
% glb(ASub1,ASub2)                                                       %
%------------------------------------------------------------------------%

:- dom_impl(_, glb/3, [noq]).
glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb(ASub1,ASub2,Glb):-
    glb_each_eq(ASub1,ASub2,Glb), !.
glb(_, _, '$bottom').

glb_each_eq([],[],[]).
glb_each_eq([X=T1|ASub1],[X=T2|ASub2],[X=T|Lub]):-
    most_general_instance(T1,T2,T),
    glb_each_eq(ASub1,ASub2,Lub).

%------------------------------------------------------------------------%

:- use_module(ciaopp(plai/domains), [absub_eliminate_equivalent/3]).

:- dom_impl(_, eliminate_equivalent/2, [noq]).
eliminate_equivalent(TmpLSucc,LSucc) :- absub_eliminate_equivalent(TmpLSucc,depthk,LSucc).

%------------------------------------------------------------------------%

:- dom_impl(_, abs_subset/2, [noq]).
abs_subset(LASub1,LASub2) :- absub_is_subset(LASub1,LASub2), !. % TODO: added cut (absub_is_subset/2 leaves choicepoints)

% TODO: leaves choicepoints!
absub_is_subset([],_LASub2).
absub_is_subset([Sub1|Subs1],LASub2) :-
    member(ASub2,LASub2),
    identical_abstract(Sub1,ASub2),
% OR:
%       absub_fixpoint_covered(depthk,Sub1,ASub2),
    absub_is_subset(Subs1,LASub2).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                   ABSTRACT Call to Success Fact                        %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% Specialized version of call_to_entry + exit_to_prime + extend for facts%
%------------------------------------------------------------------------%

:- dom_impl(_, call_to_success_fact/9, [noq]).
call_to_success_fact(Sg,_Hv,Head,_K,Sv,Call,Proj,Prime,Succ):-
    peel(Sg, Head, Unifiers, []), % previously peel(Head, Sg, Unifiers, []) messed with variables in some corner cases.
    sort(Unifiers, Unifiers_s), 
    depthk_unify(Proj,Unifiers_s,Entry0), !,
    %% Sometimes Entry0 was not a proper ASub, these predicates are
    %% intended to keep the correct structure
    variables_are_variables(LeftVars, Entry0), 
    fix_asub(Entry0, LeftVars, Entry0_fixed), 
    depthk_bu_project(Entry0_fixed,Sv,Prime1),
    abs_sort(Prime1,Prime),
    extend(Sg,Prime,Sv,Call,Succ).
call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,_Proj,'$bottom','$bottom').

%% Given a collection of Equations and the set of program variables
%% over which these equations are defined, fix_asub/3 succeeds if 
%% PropASub is the Depth-k asbtraction capturing (perfectly) that equations.
%% For example, if Eqs = [X=Y, Z=f(X,C)] and the program variables are X, Y, and Z
%% then PropASub = [X = A, Y=A, Z =f(A, C)] where A is a free fresh variable
fix_asub(Eqs, Vars, PropASub) :-
    fix_asub_(Eqs, Vars, FixASub),
    depthk_bu_project(FixASub, Vars, PropASub).

fix_asub_([], _, []).
fix_asub_([X=Y|Xs], LeftVars, FASub) :-
    (ord_member(X, LeftVars) -> XIn = yes ; XIn = no), 
    (ord_member(Y, LeftVars) -> YIn = yes ; YIn = no),
    ( XIn = yes, YIn = yes ->  FASub = [Y=A,X=A|TFASub]
    ;
        (XIn = yes, YIn = no -> FASub = [X=Y|TFASub]
        ;
            (XIn = no, YIn = yes -> FASub = [Y=X|TFASub]
            ;
                XIn = no, YIn =no -> FASub = TFASub)
        )
    ),
    fix_asub_(Xs, LeftVars, TFASub).
    
%------------------------------------------------------------------------%
% identical_abstract(+,+)                                                %
% identical_abstract(ASub1,ASub2)                                        %
% Succeeds if abstract substitutions ASub1 and ASub2 are defined on the  %
% same variables and are equivalent                                      %
%------------------------------------------------------------------------%

%% care with top variables, which can be shared between the two substs.!!

:- dom_impl(_, identical_abstract/2, [noq]).
identical_abstract('$bottom', '$bottom') :- !.
identical_abstract(ASub1,ASub2):-
    variables_are_variables(V1,ASub1),
    \+ \+ (
    numbervars(V1,0,M),
    copy_term(ASub1,T1),
    copy_term(ASub2,T2),
    numbervars(T1,M,N),
    numbervars(T2,M,N),
    T1==T2 ).

%------------------------------------------------------------------------%
% less_or_equal(+,+)                                                     %
% less_or_equal(ASub0,ASub1)                                             %
%------------------------------------------------------------------------%

:- dom_impl(_, less_or_equal/2, [noq]).
less_or_equal('$bottom',_).
less_or_equal(ASub0,ASub1):-
    less_or_equal_(ASub0,ASub1).

less_or_equal_([],[]).
less_or_equal_([X=T1|ASub1],[X=T2|ASub2]):-
    instance(T1,T2),
    less_or_equal_(ASub1,ASub2).

%-------------------------------------------------------------------------
% unknown_call(+,+,+,-)                                                  |
% unknown_call(Sg,Qv,Call,Succ)                                          |
%-------------------------------------------------------------------------

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(_Sg,Qv,Call,Succ):-
    subtract_keys(Call,Qv,Succ0),
    variables_are_variables(Qv,Succ1),
    merge(Succ0,Succ1,Succ).

%------------------------------------------------------------------------%
% unknown_entry(+,+,-)                                                   %
% unknown_entry(Sg,Qv,Call)                                              %
%------------------------------------------------------------------------%

:- dom_impl(_, unknown_entry/3, [noq]).
unknown_entry(_Sg,Qv,Call):-
    variables_are_variables(Qv,Call).

:- dom_impl(_, empty_entry/3, [noq]).
empty_entry(Sg,Qv,Call):-
    unknown_entry(Sg,Qv,Call).

%------------------------------------------------------------------------%
%                      USER INTERFACE                                    %
%------------------------------------------------------------------------%
                     
%------------------------------------------------------------------------%
% input_user_interface(+,+,-,+,+)                                        %
% input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub)               %
% Obtaining the abstract substitution for Depthk from the user supplied  %
% information                                                            %
%------------------------------------------------------------------------%

:- dom_impl(_, input_user_interface/5, [noq]).
input_user_interface(Info,Qv,Call,_Sg,_MaybeCallASub):-
    may_be_var(Info),
    sort(Info,Eqs),
    eqs_ranges(Qv,Eqs,Terms,_Vars,[],_AVarSet),
    keys_and_values(Qv,Terms,AEqs),
    make_idempotent(Terms, Qv, AEqs, Terms_idm),
    keys_and_values(Qv, Terms_idm, AEqs_idm),
    depth_k(K),
    check_equs(AEqs_idm,K,[],Call).

%%% input_user_interface was not keeping an idempotent representation;
%%% this predicate recovers the appropiate representation for the ASub

%%% We use this concept of idempotent representation/abstraction which
%%% I am not sure where comes from. We say that a depth-k abstraction
%%% is idempotent iff it is a list of equations such that for each
%%% program variable X there exists only one equation X = F (where F
%%% is whatever) , if Y = S is in the abstraction then Y is a program
%%% variable and the set of variables "in the left" is disjoint with
%%% the set of variables "in the right".
%% For example [X=A, Y = Y , Z=f(Y, C)] is not idempotent but [X = A,
%% Y = B, Z = f(B, B)] it is (it X, Y, and Z are the only variables in
%% the program).

% TODO: check efficiency
%%% make_imdepotent/3 has O(LT*LAEqs) (LT the length of Terms and LAEqs
%%% the lenght of AEqs). Maybe can be reduced exploiting the sorted
%%% representation of AEqs
make_idempotent([], _, _, []).
make_idempotent([Ts|Terms], Qv, AEqs, NTerms) :-
    make_idempotent_(Ts, Qv, AEqs, NTs),
    make_idempotent(Terms, Qv, AEqs, NTerms_t),
    NTerms = [NTs|NTerms_t].

make_idempotent_(Term, Qv, AEqs, NTerm) :-
    varset(Term,TVars_us), 
    sort(TVars_us, TVars),
    ord_intersection(TVars, Qv, ToReplace),
    ord_subset_diff(ToReplace, TVars, NotChange), 
    get_replacements(AEqs, ToReplace, Replacements),
    replace_vars(Term, ToReplace, NotChange, Replacements, NTerm).

get_replacements(_, [], []).
get_replacements([V=T|Eqs], [X|Xs], Repl) :-
    V == X, !, Repl = [X = T|Repl_t],
    get_replacements(Eqs, Xs, Repl_t).
get_replacements([_|Eqs], Xs, Repl) :-
    get_replacements(Eqs, Xs, Repl).

replace_vars(Term, ToReplace, NotChange, Replacements, NTerm) :-
    varset(Replacements, RepVars),
    ord_intersection(RepVars, ToReplace, Intr),
    ord_subset_diff(Intr, RepVars, NotChange2),
    ord_union(NotChange, NotChange2, NotCh),
    copy_term(Term-NotCh-Replacements, Term_cp-NotCh-Replacements_cp),
    s_eqs:apply(Replacements_cp),
    NTerm = Term_cp.
    

:- dom_impl(_, input_interface/4, [noq]).
input_interface(instance(X,T),perfect,Eqs0,Eqs):-
    var(X),
    myappend(Eqs0,X=T,Eqs).

myappend(Vs0,V,Vs):-
    var(Vs0), !,
    Vs=[V].
myappend(Vs,V,[V|Vs]).

may_be_var(X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------%
% asub_to_native(+,+,+,-,-)                                              %
% asub_to_native(ASub,Qv,OutFlag,Info,Comps)                             %
%------------------------------------------------------------------------%

:- dom_impl(_, asub_to_native/5, [noq]).
%% ASub to native was showing a bad output in which some program
%% variables where unified when something like [X=A, Y=A] was
%% abstracter. This fixes it.
asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :-
    unifying_vars(ASub, Unifs_us), sort(Unifs_us, Unifs), %% To avoid unify program variables
    variables_are_variables(LeftUnifs, Unifs),
    variables_are_variables(DkVars, ASub),
    ord_subset_diff(LeftUnifs, DkVars, DkVarswounifs),
    depthk:project(not_provided_Sg, DkVarswounifs, not_provided_HvFv, ASub, DepthkASub_red),
    partial_apply(DepthkASub_red),
    asub_to_native_(ASub,OutputUser).

asub_to_native_([],[]).
asub_to_native_([X=T|ASub],Info):-
    accumulate(X,T,Info0,Info),
    asub_to_native_(ASub,Info0).

accumulate(_,T,Info0,Info):-
    var(T), !,
    Info=Info0.
accumulate(X,T,Info,[instance(X,T)|Info]).

%% This predicate obtains the set of variables that are unifying in
%% the abstraction.  Two variables X and Y are unifying if there
%% exists a variable A s.t. X = A and Y =A are equations in the
%% abstraction.

%This predicate is quadratic, probably can be reduced
%% generating a "reversed abstraction" and sorting it (for example if
%% [X=A, Y=B, Z=f(_)], generate the auxiliar set of equation [A=X,
%% B=Y] and do not consider the functors/atoms since we are only
%% looking for variables)
% TODO: check efficiency
unifying_vars([], []).
unifying_vars([X=Term|Eqs], UVars) :-
    var(Term), !,
    unifying_vars_aux(Eqs, X, Term, RedEqs, Unifs),
    unifying_vars(RedEqs, TempUnifs),
    ord_union(TempUnifs, Unifs, UVars).
unifying_vars([_|Eqs], UVars) :-
    !, unifying_vars(Eqs, UVars).

unifying_vars_aux([], _, _,[], []).
unifying_vars_aux([Y=Term|Eqs], X, T, Eqs_red, Unifs) :-
    var(Term), Y\== X, Term == T, !,
    Unifs = [Y=X|UnifsTemp],
    unifying_vars_aux(Eqs, X, T, Eqs_red, UnifsTemp).
unifying_vars_aux([Eq|Eqs], X, T, Eqs_red, Unifs) :-
    !,
    Eqs_red = [Eq|EqsTemp],
    unifying_vars_aux(Eqs, X, T, EqsTemp, Unifs).

partial_apply([]).
partial_apply([V1=T1|ASub]) :-
    (
        var(T1) -> T1 = V1,
            partial_apply(ASub)
        ;
        partial_apply(ASub)).
    
%------------------------------------------------------------------------%
%                         HANDLING BUILTINS                              %
%------------------------------------------------------------------------%

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin('get_code/1',_, _,nochange,[]).
special_builtin('fail/0',_, _, bottom,_).
special_builtin('!/0',(!),_,nochange,[]).
% SICStus3 (ISO)
special_builtin('=\\=/2',(_ =\= _),_,nochange,[]).
% SICStus2.x
% special_builtin('=\=/2',(_ =\= _),_,nochange,[]).
special_builtin('=<'/2,'=<'(_,_),_,nochange,[]).
special_builtin('@=<'/2,'@=<'(_,_),_,nochange,[]).
special_builtin('@>'/2,'@>'(_,_),_,nochange,[]).
special_builtin('@>='/2,'@>='(_,_),_,nochange,[]).
special_builtin('@<'/2,'@<'(_,_),_,nochange,[]).
special_builtin('>'/2,'>'(_,_),_,nochange,[]).
special_builtin('>='/2,'>='(_,_),_,nochange,[]).
% SICStus3 (ISO)
special_builtin('\\==/2',(_ \== _),_,nochange,[]).
% SICStus2.x
% special_builtin('\==/2',(_ \== _),_,nochange,[]).
special_builtin('<'/2,'<'(_,_),_,nochange,[]).
special_builtin('$metachoice'/1,'$metachoice'(_),_,nochange,[]).
special_builtin('$metacut'/1,'$metacut'(_),_,nochange,[]).
%special_builtin('arg/3',arg(_,_,_),_,nochange,[]).
special_builtin('atom/2',atom(_),_,nochange,[]).
special_builtin('atomic/2',atomic(_),_,nochange,[]).
special_builtin('format/2',format(_,_),_,nochange,[]).
special_builtin('format/3',format(_,_,_),_,nochange,[]).
%special_builtin('functor/3',functor(_,_,_),_,nochange,[]).
special_builtin('ground/1',ground(_),_,nochange,[]).
special_builtin('integer/1',integer(_),_,nochange,[]).
special_builtin('instance/2',instance(X,Y),_,instance,(X,Y)).
special_builtin('is/2',is(_,_),_,nochange,[]).
special_builtin('length/2',length(_,_),_,nochange,[]).
special_builtin('nl/1',nl(_),_,nochange,[]).
special_builtin('nl/0',nl,_,nochange,[]).
special_builtin('display/1',display(_),_,nochange,[]).
special_builtin('ttynl/0',_,_,nochange,[]).
special_builtin('ttyput/1',_,_,nochange,[]).
special_builtin('nonvar/1',nonvar(_),_,nochange,[]). % needed?
special_builtin('not_free/1',nonvar(_),_,nochange,[]).
special_builtin('number/1',number(_),_,nochange,[]).
special_builtin('statistics/2',statistics(_,_),_,nochange,[]).
special_builtin('var/1',var(_),_,nochange,[]). % needed?
special_builtin('free/1',var(_),_,nochange,[]).
special_builtin('write/1',write(_),_,nochange,[]).      
special_builtin('write/2',write(_,_),_,nochange,[]).
special_builtin('write_canonical/1',write_canonical(_),_,nochange,[]).
special_builtin('write_canonical/2',write_canonical(_,_),_,nochange,[]).
special_builtin('writeq/1',writeq(_),_,nochange,[]).
special_builtin('writeq/2',writeq(_,_),_,nochange,[]).
special_builtin('true/0', _, _, nochange, []). % otherwise it is not captured by combined_special_builtin0
%special_builtin('=/2','='(X,Y), _, instance, (X, Y)).
special_builtin(_Key,Builtin,_,nochange,[]):- functor(Builtin,_,0).
special_builtin(Key,_Builtin,_,special(Key),[]):- 
    very_special_builtin(Key).

very_special_builtin('=../2').
very_special_builtin('arg/3').
very_special_builtin('functor/3').
very_special_builtin('is/2').
very_special_builtin('name/2').
very_special_builtin('=/2').

:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(nochange,_Sv_uns,[],_,Call,Call).
success_builtin(instance,_Sv_uns,(X,Y),_,Call,Succ):-
    var(X), !,
    discriminate_equs(Call,[X],[X=T],NonRelated,_Renamings),
    ( most_general_instance(T,Y,NewT)
    -> merge_eqs([X=NewT],NonRelated,Succ)
     ; Succ='$bottom'
    ).
success_builtin(instance,_Sv_uns,_Args,_,Call,Call).

:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin(_SgKey,Sg,Sv,Call,_Proj,Succ):-
    call_to_prime_builtin(Sg,Sv,Call,Prime0), 
    varset(Prime0,Vars),
    ord_subtract(Sv,Vars,Vars0),
    project(Sg,Vars0,not_provided_HvFv_u,Call,Prime1),
    merge_eqs(Prime0,Prime1,Prime),
    extend(Sg,Prime,Sv,Call,Succ), !. %% mod Call -> TCall
call_to_success_builtin(_SgKey,_Sg,_Sv,_Call,_Proj,'$bottom').

call_to_prime_builtin(Sg,Sv,Call,Prime):-
    execute_builtin(Sg,Call,Eqs), !,
    depthk_bu_unify(Eqs,Sv,[],Prime).
call_to_prime_builtin(Sg,Sv,_Call,Prime):-
    depthk_abstract_builtin(Sg,Sv,Prime).

execute_builtin(Sg,Call,Eqs):-
    build_call(Sg,Call,Goal,Eqs),
    %
% RH:   replace catch by intercept because intercept does 
%       not handle anymore exceptions 
%       intercept(Goal,_Any,fail).  
    catch(Goal,error(_,_),fail). % TODO: not for all errors?!
%       on_exception(_,call(Goal),fail).

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
build_call('='(X,Y),Call,'='(A,Y0),[X=A]):-
    build_a_copy(Y,Call,Y0).

% copy the call but respect the variables in Y
build_a_copy(Y,Call,Y0):-
    varset(Y, YVars),
    copy_term(Y-YVars, Y0-YVars0),
    project(not_provided_Sg,YVars,not_provided_HvFv_u,Call,ProjY),
    rename_domain(YVars,YVars0,ProjY,ProjY0),
    apply(ProjY0).

rename_domain([Y|Ys],[Y0|Y0s],[Y=A|ProjY],[Y0=A|ProjY0]):-
    rename_domain(Ys,Y0s,ProjY,ProjY0).
rename_domain([],[],[],[]).

%------------------------------------------------------------------------%
%                         BOTTOM-UP FUNCTIONS                            %
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%

%% having an entry per literal makes the abstraction of a literal void 
%%  (i.e. top! - nothing is known for the variables in the literal)

% depthk_abstract(_Literal,[]).

%------------------------------------------------------------------------%

depthk_bu_unify(Eqs,Vars,Proj,ASub):-
    unify_eqs(Eqs,Unifiers),
    depthk_unify(Unifiers,Proj,ASub0),
    project(not_provided_Sg,Vars,not_provided_HvFv_u,ASub0,ASub).

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
%%      simetric_renamings(AUnifiers,SUnifiers).
%% simetric_renamings([X=Y|AUnifiers],[X=Y|SUnifiers]):-
%%      simetric_renamings(AUnifiers,SUnifiers).

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
%% %%   merge_eqs(I1,I2,I).
%% %%   depthk_unify(I1,I2,I).
%%      append(I1,I2,I).
%% 
%% %% have to unify here because it is not done in "tp" after "retrieve"
%% %% ojo que en "dep" no hace falta porque el "unify" no hace nada
%% %% que tenga que ver con cierres transitivos...
%% 
%% %-------------------------------------------------------------------------
%% 
%% %% depthk_lub(yes,Is,I1,I):-
%% %%   depthk_lub(Is,I1,I).     %% NOT IMPLEMENTED YET
%% depthk_lub(yes,Is,I1,I):-
%%      depthk_lub_disjunctive(Is,I1,I).
%% depthk_lub(no,Is,I1,I):-
%%      depthk_lub_disjunctive(Is,I1,I).
%% 
%% %% lub a list of substs. and a single subst 
%% %%   check if subst. belongs to the list, if not add it:
%% %%   each subst. refers to each and all of the variables involved (sorted)
%% %%   but it may have "free" variables (the end of the K-depth)
%% 
%% depthk_lub_disjunctive(Is,I,Is):-
%%      \+ \+ (
%%      numbervars(I,0,N),
%%      member(I0,Is),
%%      numbervars(I0,0,N),
%%      I == I0
%%      ), !.
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
%       get_rid_of_void_equs(NonRelated),
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
%%      X=Y,
%%      get_rid_of_void_equs(Eqs).

%% get_rid_of_void_equs([],_,[]).
%% get_rid_of_void_equs([X=Y|Eqs],Vars,NEqs):-
%%      \+ ( ord_member(X,Vars) ),
%%      varset(Y,YVars),
%%      ord_intersection(YVars,Vars,[]), !,
%%      X=Y,
%%      get_rid_of_void_equs(Eqs,Vars,NEqs).
%% get_rid_of_void_equs([E|Eqs],Vars,[E|NEqs]):-
%%      get_rid_of_void_equs(Eqs,Vars,NEqs).

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
%%      E=(X=_), V==X, !,
%%      Related=[E|More],
%%      equs_for_all_vars(Vs,Es,Renamings,More).
%% equs_for_all_vars([V|Vs],Es,Renamings,Related):-
%%      ( Es=[X=_|_], V@<X ; Es=[] ), !,
%%      get_a_renaming(Renamings,V,ThisOne,NewRenamings),
%%      put_a_renaming(ThisOne,V,E0),
%%      Related=[E0|More],
%%      equs_for_all_vars(Vs,Es,NewRenamings,More).
%% 
%% get_a_renaming([],_,[],[]).
%% get_a_renaming([Y=X|Rs],V,ThisOne,NewRs):-
%%      V==X, !,
%%      ThisOne=[Y],
%%      NewRs=Rs.
%% get_a_renaming([R|Rs],V,ThisOne,[R|NewRs]):-
%%      get_a_renaming(Rs,V,ThisOne,NewRs).
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
%%      var(Y),
%%      \+ ( ord_member(Y,Vars) ), !,
%%      check_equs(Eqs,K,Vars,Projected).
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

%% identical_interpretations('$bottom','$bottom'):- !.
%% identical_interpretations('$bottom',_I):- !, fail.
%% identical_interpretations(_I,'$bottom'):- !, fail.
%% identical_interpretations(I0,I1):-
%%      length(I0,L),
%%      length(I1,L).

%-------------------------------------------------------------------------

%% table of builtins

depthk_abstract_builtin(Builtin,Sv,I):-
    builtin_depthk(Builtin,Sv,D),
    sort(D,I).

%% very raw this! There is a lot on info for refining the subst. which
%%  can not be expressed here!!!!!!!!!!

builtin_depthk((!),_Sv,[]).
builtin_depthk('='(X,Y),Sv,I) :- depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk('=..'(_,Y),Sv,I) :- depthk_bu_unify([Y=[_|_]],Sv,[],I).
builtin_depthk('=:='(X,Y),Sv,I) :- depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk('=='(X,Y),Sv,I) :- depthk_bu_unify([X=Y],Sv,[],I).
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
builtin_depthk('C'(X,Y,Z),Sv,I) :- depthk_bu_unify([X=[Y|Z]],Sv,[],I).
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
builtin_depthk(numbervars(X,Y,_),Sv,I) :- depthk_bu_unify([X=Y],Sv,[],I).
builtin_depthk(statistics(_,_),_Sv,[]).
builtin_depthk(true,_Sv,[]).
builtin_depthk(var(_),_Sv,[]).
builtin_depthk(write(_),_Sv,[]).      
builtin_depthk(write(_,_),_Sv,[]).
builtin_depthk(write_canonical(_),_Sv,[]).
builtin_depthk(write_canonical(_,_),_Sv,[]).
builtin_depthk(writeq(_),_Sv,[]).
builtin_depthk(writeq(_,_),_Sv,[]).
builtin_depthk(Builtin,_Sv,[]) :- functor(Builtin,_,0).

%% Auxiliary predicates:

% (exported)

% This predicate performs a first step in the extend
% operation. Is defined as follows:
% The equation V=F in Typically
% iff
% - V in domain(Call)
% - If V in domain(Prime) => V=F in Call
% - If V not in domain(Prime) => F is the result of applying the
%   substitution defined by Prime over the variables in F that belong
%   to domain(Prime)

% Notice that after the computation of TCAll it is going to be
% projected over the variables not in Prime, because of that we do not
% need to update that variables in TCall (actually we need to keep
% them unchanged to maintain the relations between variables in Call
% during the computation of TCall)

% E.g., Prime=[X=a], Call=[X=_A,Y=f(_A)] => TCall=[X=_A,Y=f(a)]
% TODO: quadratic complexity? (exploit sorted representation better?
% TODO: check efficiency
sub2prime_and_replace(Prime, Call, TCall) :-
    sub2prime(Prime, Call, Call, PrimeT),
    replace_eqs(PrimeT, Call, TCall).

% E.g., Ps=[X=a], Call=[X=_A,Y=f(_A)] => Prime=[X=_, Y=f(a)]
sub2prime([], _Call, Prime, Prime).
sub2prime([V=T|Eqs], Call, Prime0, Prime) :-
    % remove bindings for V from Calls and replace in terms
    member(V0=BV, Call),
    %select(V0=BV, Call, PartCall),
    V0 == V, !, %change to select
    ( var(BV) ->
        sub_replace(Prime0, V, BV, T, Prime1)
    ;
        peel(BV, T, Unifs, []),
        sub_replace_list(Unifs, V, Prime0, Prime1)
        ),
    sub2prime(Eqs, Call, Prime1, Prime).

sub_replace_list([], _, Eqs, Eqs).
sub_replace_list([V=T|Unifs], BVar, Eqs, EqsSub) :-
    sub_replace(Eqs, BVar, V, T, EqsSubT),
    sub_replace_list(Unifs, BVar, EqsSubT, EqsSub).

sub_replace([], _, _, _, []).
sub_replace([Eq|Xs], BVar, V, T, [Y|Ys]) :-
    % only replace eqs V0=T0 where V appears in T0 and T0 is not V
    ( Eq=(V0=T0),
      V0\==BVar,
      has_var(T0, V) ->
        replace_var_in_term(T0, V, T, T2),
        Y=(V0=T2)
    ; Eq=Y
    ),
    sub_replace(Xs, BVar, V, T, Ys).

% E.g., Prime=[Y=f(a)], Call=[X=_A,Y=f(_A)] => NCall=[X=_A,Y=f(a)]
replace_eqs([], Call, Call).
replace_eqs([V1=T1|Ts], Call, Call2) :-
    replace_eq(Call, V1, T1, Call1),
    replace_eqs(Ts, Call1, Call2).

replace_eq([], _, _, []).
replace_eq([V2=T2|Eqs], V1, T1, NCall) :-
    ( V1 == V2 ->
        NCall = [V1=T1|Eqs]
    ; NCall = [V2=T2|NEqs],
      replace_eq(Eqs, V1, T1, NEqs)
    ).


% Var appears in term X
has_var(X, Var) :- varset(X, Vars), member(Var0, Vars), Var == Var0, !.

% replace_var_in_term(X, V, T, Y): Y is the result of replacing
%   occurences of V by T in term X.
replace_var_in_term(X, V, T, Y) :-
    ( var(X) ->
        ( X == V -> Y = T ; Y = X )
    ; X =.. [F|As],
      replace_var_in_terms(As, V, T, Bs),
      Y =.. [F|Bs]
    ).

replace_var_in_terms([], _, _, []).
replace_var_in_terms([X|Xs], V, T, [Y|Ys]) :-
    replace_var_in_term(X, V, T, Y),
    replace_var_in_terms(Xs, V, T, Ys).


%%% Include a widen predicate
:- dom_impl(_, widencall/3, [noq]).

widencall('$bottom', '$bottom','$bottom') :-!. 
widencall('$bottom',ASub2,ASub2):-!.
widencall(ASub1,'$bottom',ASub1):-!.
widencall([], [], []) :- !.
widencall(ASub1, ASub2, ASubW) :-
    compute_lub([ASub1, ASub2], ASubW).

:- dom_impl(_, widen/3, [noq]).
widen(Prime0,Prime1,New_Prime):-
    widencall(Prime0,Prime1,New_Prime).
