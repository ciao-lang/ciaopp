:- module(deftypes, [], [assertions,regtypes,basicmodes]).

:- doc(title,"deftypes: defined types (based on termsd) (abstract domain)").
:- doc(author, "Pawel Pietrzak (original)").
:- doc(author, "Ciao Development Team").

:- doc(module, "This module implements types abstract domain (based on
   @lib{termsd}) that only includes library types, user-defined types
   and instances of parametric rules.  Like in @lib{termsd}, an
   abstract sustitution is list of Var:Type elements, where Var is a
   variable and Type is a pure type term @cite{Dart-Zobel}.").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(deftypes, [default]).

% ---------------------------------------------------------------------------

:- use_module(domain(termsd), [
    substitution/3,
    variables_are_variable_type/2,
    variables_are_top_type/2,
    unify_term_and_type_term/5,
    terms_abs_sort/2,
    terms_project/5,
    terms_extend/5,
    terms_asub_to_native/5,
    terms_input_interface/4,
    terms_special_builtin/5,
    terms_success_builtin/6,
    terms_concrete/3,
    terms_unknown_entry/3,
    terms_empty_entry/3,
    terms_unknown_call/4,
    terms_collect_auxinfo_asub/3,
    terms_rename_auxinfo_asub/3]).

:- use_module(typeslib(typeslib), [
    def_type_approx_as_defined/2,
    def_subtype/2,
    def_type_lub/3,
    def_type_glb/3,
    def_equivalent_types/2,
    % type_intersection_2/3,
    contains_type_param/1,
    pure_type_term/1]).

:- use_module(library(terms_check), [variant/2]).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(sort), [sort/2]).

% ---------------------------------------------------------------------------

:- prop asub(A) # "@var{A} is an abstract substitution".

asub('$bottom').
asub([]).
asub([Elem|Absu]):-
    asub_elem(Elem),
    asub(Absu).

:- prop asub_elem(E) # "@var{E} is a single substitution".

asub_elem(Var:Type):-
    var(Var),
    pure_type_term(Type).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(_, init_abstract_domain/1, [noq]).
init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

%% ---------------------------------------------------------------------------

:- use_module(domain(termsd), [
    precondition_builtin/2,
    postcondition_builtin/4]).

:- dom_impl(_, call_to_success_builtin/6, [noq]).
call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
    call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    % TODO: use new code?
    ( precondition_builtin(Key,Sg) ->
        postcondition_builtin(Key,Bg,Bv,Exit),
        exit_to_prime(Sg,Bv,Bg,Sv,Exit,no,Prime1),
        glb(Proj,Prime1,Prime),
        terms_extend(Sg,Prime,Sv,Call,Succ)
    ; Succ = '$bottom'
    ).

% TODO: "PP: TO BE FIXED:" in case for member(X,L)
:- dom_impl(_, input_interface/4, [noq]).
input_interface(X,Mode,Acc,R) :-
    terms_input_interface(X,Mode,Acc,R).

%------------------------------------------------------------------%

:- dom_impl(_, special_builtin/5, [noq]).
special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :-
    terms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

:- dom_impl(_, success_builtin/6, [noq]).
success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ):-
    terms_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).

:- dom_impl(_, concrete/3, [noq]).
concrete(Var,ASub,List) :-
    terms_concrete(Var,ASub,List).

:- dom_impl(_, unknown_call/4, [noq]).
unknown_call(Sg,Vars,Call,Succ) :-
    terms_unknown_call(Sg,Vars,Call,Succ).

%------------------------------------------------------------------%
:- dom_impl(_, compute_lub/2, [noq]).
:- pred compute_lub(+ListASub,-Lub)
   : list(asub, ListASub) => asub(Lub)
   # "It computes the least upper bound of a set of abstract
   substitutions.  For each two abstract substitutions @var{ASub1} and
   @var{ASub2} in @var{ListASub}, obtaining the lub is foreach X:Type1
   in @var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion is in Lub,
   and TypeUnion is the deterministic union of Type1 an Type2.".

compute_lub([ASub1,ASub2|Rest],Lub):-
    compute_lub_el(ASub1,ASub2,ASub3),
    compute_lub([ASub3|Rest],Lub).
compute_lub([ASub],ASub).

compute_lub_el('$bottom',ASub,ASub):- !.
compute_lub_el(ASub,'$bottom',ASub):- !.
compute_lub_el(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
compute_lub_el(ASub1,ASub2,ASub3):-
    lub0(ASub1,ASub2,ASub3),!.

lub0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
    X==Y,
%       type_union(T1,T2,T3,[]),
    def_type_lub(T1,T2,T3),
    lub0(ASub1,ASub2,ASub3).
lub0([],[],[]).

% ---------------------------------------------------------------------------
% Widening

:- dom_impl(_, widencall/3, [noq]).
widencall(_Prime0,Prime1,Prime1).
% widencall(Prime0,Prime1,NewPrime):-
%     widen(Prime0,Prime1,NewPrime).
%     display(terms_widencall),nl,
%     terms_compute_lub_el(Prime0,Prime1,Prime),
%     shortening(Prime,NewPrime).

:- dom_impl(_, needs/1, [noq]).
%% needs(widen). % not needed because only working with defined types
needs(auxinfo).

:- dom_impl(_, widen/3, [noq]).
:- pred widen(+Prime0,+Prime1,-NewPrime)
   : asub * asub * term => asub(NewPrime)
   # "Induction step on the abstract substitution of a fixpoint.
   @var{Prime0} corresponds to non-recursive and @var{Prime1} to
   recursive clauses.  @var{NewPrime} is the result of apply one
   widening operation to the least upper bound of the formers.
   Widening operations implemented are ``shortening'' and ``restricted
   shortening'' @cite{gallagher-types-iclp94,Saglam-Gallagher-94}.".

widen(Prime0,Prime1,NewPrime):-
    compute_lub_el(Prime0,Prime1,NewPrime).

%------------------------------------------------------------------%
:- dom_impl(_, call_to_entry/9, [noq]).
:- pred call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo)
   : term * cgoal * list * cgoal * term * list * asub * term * term
   => (asub(Entry), extrainfo(ExtraInfo))
   # "It obtains the abstract substitution @var{Entry} which results
   from adding the abstraction of the @var{Sg} = @var{Head} to
   @var{Proj}, later projecting the resulting substitution onto
   @var{Hv}.

   This is done as follows: 
   @begin{itemize} 
   @item If @var{Sg} and @var{Head} are identical up to renaming it is
     just renaming @var{Proj} and adding the @var{Fv}
   @item Otherwise, it will 
     @begin{itemize} 
     @item obtain the abstract substitution from unifying @var{Sg} and
       @var{Head} calling ``unify_term_and_type_term''
     @item add to this abstract substituion the variables in Fv as
       term type.
     @end{itemize} 
   @end{itemize} 
   
   The meaning of the variables is
   @begin{itemize}
   @item @var{Sg} is the subgoal being analysed. 
   @item @var{Head} is the Head of the clause being analysed.
   @item @var{Fv} is a list of free variables in the body of the
     clause being considered.
   @item @var{Proj} is the abstract substitution @var{Call} projected
     onto @var{Sv}.
   @item @var{Entry} is the Abstract entry substitution (i.e. the
     abstract subtitution obtained after the abstract unification of
     @var{Sg} and @var{Head} projected onto @var{Hv} + @var{Fv}).
   @item @var{ExtraInfo} is a flag ``yes'' when no unification is
     required, i.e., Entry=Proj upto names of vars. and ignoring
     Fv. It is ``no'' if unification fails.
   @end{itemize}".

call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
    variant(Sg,Head), !,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    terms_abs_sort(NewProj_u,NewProj),
    variables_are_variable_type(Fv,Free),
    merge(Free,NewProj,Entry).
call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,dummy):-
    unify_term_and_type_term_approx(Head,Hv,Sg,Proj,TmpEntry), !,
    variables_are_variable_type(Fv,Tmp),
    merge(Tmp,TmpEntry,Entry).
call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- regtype extrainfo/1.
extrainfo(yes).
extrainfo(no).
extrainfo(dummy).

%------------------------------------------------------------------%
:- dom_impl(_, exit_to_prime/7, [noq]).
:- pred exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,?ExtraInfo,-Prime)
   : cgoal * list * cgoal * list * asub * term * term
   => (extrainfo(ExtraInfo), asub(Prime))
   # "It computes the prime abstract substitution @var{Prime}, i.e.
   the result of going from the abstract substitution over the head
   variables @var{Exit}, to the abstract substitution over the
   variables in the subgoal. It will:

   @begin{itemize}
   @item If @var{Exit} is '$bottom', @var{Prime} will be also
     '$bottom'.
   @item If @var{ExtraInfo} = yes (@var{Head} and @var{Sg} identical
     up to renaming) it is just renaming Exit %
   @item  Otherwise: it will 
     @begin{itemize}                                                        
     @item projects @var{Exit} onto @var{Hv} obtaining @var{BPrime}.
     @item obtain the abstract substitution from unifying @var{Sg} and
        @var{Head} calling ``unify_term_and_type_term''
     @end{itemize}
   @end{itemize}".

exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
    Prime = '$bottom'.
exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    terms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    terms_abs_sort(NewPrime,Prime). 
exit_to_prime(Sg,Hv,Head,Sv,Exit,_ExtraInfo,Prime):- 
    terms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    unify_term_and_type_term_approx(Sg,Sv,Head,BPrime,Prime).
exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').

:- pred unify_term_and_type_term_approx(+Term1,+Tv,+Term2,+ASub,-NewASub)
   : cgoal * list * cgoal * asub * term
   => asub(NewASub)
   # "it unifies the term @var{Term1} to the type term @var{Term2}
   obtaining the the abstract substitution TypeAss which is sorted and
   projeted on @var{Tv}".

unify_term_and_type_term_approx(Term1,Tv,Term2,ASub,NewASub):-
    unify_term_and_type_term(Term1,Tv,Term2,ASub,NewASub0),
    approx_asub(NewASub0,NewASub).

approx_asub([],[]).
approx_asub([X:Type|ASub],[X:NType|NASub]):-
    def_type_approx_as_defined(Type,NType),
%   remove_rule(NType0). % TODO: only if new % TODO: it was commented out
    approx_asub(ASub,NASub).

%------------------------------------------------------------------%
:- dom_impl(_, project/5, [noq]).
:- pred project(+Sg,+Vars,+HvFv_u,+Asub,-Proj)
   : term * list * list * asub * term => asub(Proj)
   # "@var{Proj} is the result of eliminating from @var{Asub} all
   @var{X}:@var{Value} such that @var{X} is not in @var{Vars}".

project(Sg,Vars,HvFv_u,ASub,Proj) :-
    terms_project(Sg,Vars,HvFv_u,ASub,Proj).

%------------------------------------------------------------------%
:- dom_impl(_, abs_sort/2, [noq]).
:- pred abs_sort(+Asub,-Asub_s) : asub(Asub)
   => asub(Asub_s)
   # "It sorts the set of @var{X}:@var{Type} in @var{Asub} containing
   @var{Asub_s}".

abs_sort(ASub,ASub_s):- terms_abs_sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- dom_impl(_, extend/5, [noq]).
:- pred extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : term * asub * list * asub * term
   => asub(Succ)
   # "If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
   @var{Succ} is computed updating the values of @var{Call} with those
   in @var{Prime}".

extend(Sg,Prime,Sv,Call,Succ):-
    terms_extend(Sg,Prime,Sv,Call,Succ).

%------------------------------------------------------------------%
:- dom_impl(_, less_or_equal/2, [noq]).
:- pred less_or_equal(+ASub0,+ASub1) : asub * asub
   # "Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
   it's assumed the two abstract substitutions are defined on the same
   variables".

less_or_equal('$bottom',_ASub):- !.
less_or_equal(ASub1,ASub2):-
    ASub1 == ASub2, !.
less_or_equal(ASub1,ASub2):-
    less_or_equal0(ASub1,ASub2).

less_or_equal0([X:T1|ASub1],[Y:T2|ASub2]):-
    X==Y,
    def_subtype(T1,T2), % dz_type_included(T1,T2),
    less_or_equal0(ASub1,ASub2).
less_or_equal0([],[]).

%------------------------------------------------------------------%
:- dom_impl(_, glb/3, [noq]).
:- pred glb(+ASub0,+ASub1,-Glb)
   : asub * asub * term
   => asub(Glb)
   # "@var{Glb} is the great lower bound of @var{ASub0} and
   @var{ASub1}".

glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
glb(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
glb(ASub1,ASub2,ASub3):-
    glb0(ASub1,ASub2,ASub3), !.
glb(_ASub1,_ASub2,'$bottom').

glb0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
    X==Y,
    def_type_glb(T1,T2,T3),!,
    T3 \== bot,
    glb0(ASub1,ASub2,ASub3).
glb0([],[],[]).

%------------------------------------------------------------------%
:- dom_impl(_, unknown_entry/3, [noq]).
:- pred unknown_entry(+Sg,+Qv,-Call)
   : cgoal * list * term => asub(Call)
   # "Gives the ``top'' value for the variables involved in a literal
   whose definition is not present, and adds this top value to
   Call. In this domain the top value is X:term forall X in the set of
   variables".

unknown_entry(Sg,Qv,Call) :- terms_unknown_entry(Sg,Qv,Call).

:- dom_impl(_, empty_entry/3, [noq]).
:- pred empty_entry(+Sg,+Vars,-Entry)
   : cgoal * list * term => asub(Entry)
   # "Gives the \"empty\" value in this domain for a given set of
   variables @var{Vars}, resulting in the abstract substitution
   @var{Entry}. I.e., obtains the abstraction of a substitution in
   which all variables @var{Vars} are unbound: free and unaliased. In
   this domain the empty value is giving the variable type to each
   variable".

empty_entry(Sg,Qv,Call) :- terms_empty_entry(Sg,Qv,Call).

%------------------------------------------------------------------%
:- dom_impl(_, call_to_success_fact/9, [noq]).
:- pred call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : cgoal * list * cgoal * term * list * asub * asub * term * term
   => (asub(Prime), asub(Succ))
   # "Specialized version of call_to_entry + exit_to_prime + extend for facts".

call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
    exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
    terms_extend(Sg,Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%

:- dom_impl(_, input_user_interface/5, [noq]).
:- pred input_user_interface(?InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   # "Obtains the abstract substitution ASub from user supplied
   information.".

input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
    obtain_Asub_user(InputUser,ASub0),
    sort(ASub0,ASub_s),
    reduce_same_var(ASub_s,ASub1),
    substitution(ASub1,Vars,_),
    ord_subtract(Qv,Vars,TopV),
    variables_are_top_type(TopV,ASub2),
    sort(ASub2,ASub3),
    merge(ASub1,ASub3,ASub).

obtain_Asub_user([],[]):- !.
obtain_Asub_user([User|InputUser],[X:T|ASub]):-
    functor(User,T,_),
    arg(1,User,X), % note: expected arity 1, parametric types already renamed
    obtain_Asub_user(InputUser,ASub).

reduce_same_var([X:T|ASub],NewASub):-
    reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var([],[]).

reduce_same_var_([Y:TY|ASub],X,TX,NewASub):-
    reduce_same_var__(Y,TY,X,TX,ASub,NewASub).
reduce_same_var_([],X,T,[X:T]).

reduce_same_var__(Y,TY,X,TX,ASub,NewASub):-
    X == Y, !,
%       type_intersection_2(TY,TX,T),
    def_type_glb(TY,TX,T),
    reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var__(Y,TY,X,TX,ASub,[X:TX|NewASub]):-
    reduce_same_var_(ASub,Y,TY,NewASub).

% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
%       Type=..[T,X],
%       inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).

%------------------------------------------------------------------------%
% TODO: OK? terms_asub_to_native depends internally on equiv_type/2
%   instead of def_equiv_type/2 (JFMC)

:- dom_impl(_, asub_to_native/5, [noq]).
:- pred asub_to_native(+ASub,+Qv,+OutFlag,-OutputUser,-Comps)
   # "Transforms abstract substitution @var{ASub} to user friendly format.
      Record relevant symbols for output if @var{OutFlag} is @tt{yes}.".

asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps):-
    terms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).

%------------------------------------------------------------------------%

:- dom_impl(_, collect_auxinfo_asub/3, [noq]).
collect_auxinfo_asub(Abs,Types1,Types) :-
    terms_collect_auxinfo_asub(Abs,Types1,Types).

:- dom_impl(_, rename_auxinfo_asub/3, [noq]).
rename_auxinfo_asub(ASub,Dict,RenASub) :-
    terms_rename_auxinfo_asub(ASub,Dict,RenASub).

%------------------------------------------------------------------%

:- dom_impl(_, identical_abstract/2, [noq]).
identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
identical_abstract(ASub1,ASub2):-
    identical_abstract0(ASub1,ASub2).

identical_abstract0([X:Type0|ASub0],[Y:Type1|ASub1]):-
    X==Y,
    def_equivalent_types(Type0,Type1),
    identical_abstract0(ASub0,ASub1).
identical_abstract0([],[]).

% ---------------------------------------------------------------------------

% TODO: not in termsd.pl, why?
:- dom_impl(_, contains_parameters/1, [noq]).
contains_parameters([_:T|Subs]) :-
    ( contains_type_param(T),!
    ; contains_parameters(Subs)
    ).
