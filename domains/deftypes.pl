:- module(deftypes, [], [assertions,regtypes,basicmodes,datafacts]).

:- doc(title,"deftypes: defined types (based on termsd) (abstract domain)").
:- doc(author, "Pawel Pietrzak (original)").
:- doc(author, "Ciao Development Team").

:- doc(module, "This module implements types abstract domain (based on
   @lib{termsd}) that only includes library types, user-defined types
   and instances of parametric rules.  Like in @lib{termsd}, an
   abstract sustitution is list of Var:Type elements, where Var is a
   variable and Type is a pure type term @cite{Dart-Zobel}.").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(deftypes).

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
    terms_collect_abstypes_abs/3,
    terms_rename_abstypes_abs/3]).

:- use_module(ciaopp(p_unit), [new_internal_predicate/3]).

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

:- regtype absu(A) # "@var{A} is an abstract substitution".

absu('$bottom').
absu([]).
absu([Elem|Absu]):- 
    absu_elem(Elem),
    absu(Absu).

:- regtype absu_elem(E) # "@var{E} is a single substitution".

absu_elem(Var:Type):-
    var(Var),
    pure_type_term(Type).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(deftypes, init_abstract_domain/1).
% :- export(deftypes_init_abstract_domain/1). % TODO: why not imported?
deftypes_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

%% ---------------------------------------------------------------------------

:- use_module(domain(termsd), [
    precondition_builtin/2,
    postcondition_builtin/4]).

:- dom_impl(deftypes, call_to_success_builtin/6).
:- export(deftypes_call_to_success_builtin/6).
deftypes_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
    deftypes_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
deftypes_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    % TODO: use new code?
    ( precondition_builtin(Key,Sg) ->
        postcondition_builtin(Key,Bg,Bv,Exit),
        deftypes_exit_to_prime(Sg,Bv,Bg,Sv,Exit,no,Prime1),
        deftypes_glb(Proj,Prime1,Prime),
        terms_extend(Sg,Prime,Sv,Call,Succ)
    ; Succ = '$bottom'
    ).

% TODO: "PP: TO BE FIXED:" in case for member(X,L)
:- dom_impl(deftypes, input_interface/4).
:- export(deftypes_input_interface/4).
deftypes_input_interface(X,Mode,Acc,R) :-
    terms_input_interface(X,Mode,Acc,R).

%------------------------------------------------------------------%

:- dom_impl(deftypes, special_builtin/5).
:- export(deftypes_special_builtin/5).
deftypes_special_builtin(SgKey,Sg,Subgoal,Type,Condvars) :-
    terms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

:- dom_impl(deftypes, success_builtin/6).
:- export(deftypes_success_builtin/6).
deftypes_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ):-
    terms_success_builtin(Type,Sv_uns,Condvars,HvFv_u,Call,Succ).

:- dom_impl(deftypes, concrete/3).
:- export(deftypes_concrete/3).
deftypes_concrete(Var,ASub,List) :-
    terms_concrete(Var,ASub,List).

:- dom_impl(deftypes, unknown_call/4).
:- export(deftypes_unknown_call/4).
deftypes_unknown_call(Sg,Vars,Call,Succ) :-
    terms_unknown_call(Sg,Vars,Call,Succ).

%------------------------------------------------------------------%
:- dom_impl(deftypes, compute_lub/2).
:- export(deftypes_compute_lub/2).
:- pred deftypes_compute_lub(+ListASub,-Lub) : list(absu) * absu
   # "It computes the least upper bound of a set of abstract
   substitutions.  For each two abstract substitutions @var{ASub1} and
   @var{ASub2} in @var{ListASub}, obtaining the lub is foreach X:Type1
   in @var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion is in Lub,
   and TypeUnion is the deterministic union of Type1 an Type2.".

deftypes_compute_lub([ASub1,ASub2|Rest],Lub):-
    deftypes_compute_lub_el(ASub1,ASub2,ASub3),
    deftypes_compute_lub([ASub3|Rest],Lub).
deftypes_compute_lub([ASub],ASub).

%------------------------------------------------------------------%

deftypes_compute_lub_el('$bottom',ASub,ASub):- !.
deftypes_compute_lub_el(ASub,'$bottom',ASub):- !.
deftypes_compute_lub_el(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
deftypes_compute_lub_el(ASub1,ASub2,ASub3):-
    deftypes_lub0(ASub1,ASub2,ASub3),!.

deftypes_lub0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
    X==Y,
%       type_union(T1,T2,T3,[]),
    def_type_lub(T1,T2,T3),
    deftypes_lub0(ASub1,ASub2,ASub3).
deftypes_lub0([],[],[]).

% ---------------------------------------------------------------------------
% Widening

:- dom_impl(deftypes, widencall/3).
:- export(deftypes_widencall/3).
deftypes_widencall(_Prime0,Prime1,Prime1).
%deftypes_widencall(Prime0,Prime1,NewPrime):-
%       deftypes_widen(Prime0,Prime1,NewPrime).
%       display(terms_widencall),nl,
%       terms_compute_lub_el(Prime0,Prime1,Prime),
%       shortening(Prime,NewPrime).

:- dom_impl(deftypes, widen/3).
:- export(deftypes_widen/3).
:- pred deftypes_widen(+Prime0,+Prime1,-NewPrime)
   : absu * absu * absu
   # "Induction step on the abstract substitution of a fixpoint.
   @var{Prime0} corresponds to non-recursive and @var{Prime1} to
   recursive clauses.  @var{NewPrime} is the result of apply one
   widening operation to the least upper bound of the formers.
   Widening operations implemented are ``shortening'' and ``restricted
   shortening'' @cite{gallagher-types-iclp94,Saglam-Gallagher-95}.".

deftypes_widen(Prime0,Prime1,NewPrime):-
    deftypes_compute_lub_el(Prime0,Prime1,NewPrime).

%------------------------------------------------------------------%
:- dom_impl(deftypes, call_to_entry/9).
:- export(deftypes_call_to_entry/9).
:- pred deftypes_call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo)
   : term * callable * list * callable * term * list * absu * absu * extrainfo

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

deftypes_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
    variant(Sg,Head), !,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    terms_abs_sort(NewProj_u,NewProj),
    variables_are_variable_type(Fv,Free),
    merge(Free,NewProj,Entry).
deftypes_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,dummy):-
    unify_term_and_type_term_approx(Head,Hv,Sg,Proj,TmpEntry), !,
    variables_are_variable_type(Fv,Tmp),
    merge(Tmp,TmpEntry,Entry).
deftypes_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- regtype extrainfo/1.

extrainfo(yes).
extrainfo(no).

%------------------------------------------------------------------%
:- dom_impl(deftypes, exit_to_prime/7).
:- export(deftypes_exit_to_prime/7).
:- pred deftypes_exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime)
   : list * list * callable * callable * absu * extrainfo * absu
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

deftypes_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
    Prime = '$bottom'.
deftypes_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    terms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    terms_abs_sort(NewPrime,Prime). 
deftypes_exit_to_prime(Sg,Hv,Head,Sv,Exit,_ExtraInfo,Prime):- 
    terms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    unify_term_and_type_term_approx(Sg,Sv,Head,BPrime,Prime).
deftypes_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').

:- pred unify_term_and_type_term_approx(+Term1,+Tv,+Term2,+ASub,-NewASub)
   : callable * list * callable * absu * absu
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
:- dom_impl(deftypes, project/5).
:- export(deftypes_project/5).
:- pred deftypes_project(+Sg,+Vars,+HvFv_u,+Asub,-Proj)
   : term * list * list * absu * absu
   # "@var{Proj} is the result of eliminating from @var{Asub} all
   @var{X}:@var{Value} such that @var{X} is not in @var{Vars}".

deftypes_project(Sg,Vars,HvFv_u,ASub,Proj) :-
    terms_project(Sg,Vars,HvFv_u,ASub,Proj).

%------------------------------------------------------------------%
:- dom_impl(deftypes, abs_sort/2).
:- export(deftypes_abs_sort/2).
:- pred deftypes_abs_sort(+Asub,-Asub_s) : absu * absu
   # "It sorts the set of @var{X}:@var{Type} in @var{Asub} containing
   @var{Asub_s}".

deftypes_abs_sort(ASub,ASub_s):- terms_abs_sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- dom_impl(deftypes, extend/5).
:- export(deftypes_extend/5).
:- pred deftypes_extend(+Sg,+Prime,+Sv,+Call,-Succ) : term * absu * list * absu * absu
   # "If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
   @var{Succ} is computed updating the values of @var{Call} with those
   in @var{Prime}".

deftypes_extend(Sg,Prime,Sv,Call,Succ):-
    terms_extend(Sg,Prime,Sv,Call,Succ).

%------------------------------------------------------------------%
:- dom_impl(deftypes, less_or_equal/2).
:- export(deftypes_less_or_equal/2).
:- pred deftypes_less_or_equal(+ASub0,+ASub1) : absu * absu
   # "Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
   it's assumed the two abstract substitutions are defined on the same
   variables".

deftypes_less_or_equal('$bottom',_ASub):- !.
deftypes_less_or_equal(ASub1,ASub2):-
    ASub1 == ASub2, !.
deftypes_less_or_equal(ASub1,ASub2):-
    deftypes_less_or_equal0(ASub1,ASub2).

deftypes_less_or_equal0([X:T1|ASub1],[Y:T2|ASub2]):-
    X==Y,
%       dz_type_included(T1,T2),
    def_subtype(T1,T2),
    deftypes_less_or_equal0(ASub1,ASub2).
deftypes_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- dom_impl(deftypes, glb/3).
:- export(deftypes_glb/3).
:- pred deftypes_glb(+ASub0,+ASub1,-Glb) : absu * absu * absu
   # "@var{Glb} is the great lower bound of @var{ASub0} and
   @var{ASub1}".

deftypes_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
deftypes_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
deftypes_glb(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
deftypes_glb(ASub1,ASub2,ASub3):-
    deftypes_glb0(ASub1,ASub2,ASub3), !.
deftypes_glb(_ASub1,_ASub2,'$bottom').

deftypes_glb0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
    X==Y,
    def_type_glb(T1,T2,T3),!,
    T3 \== bot,
    deftypes_glb0(ASub1,ASub2,ASub3).
deftypes_glb0([],[],[]).

%------------------------------------------------------------------%
:- dom_impl(deftypes, unknown_entry/3).
:- export(deftypes_unknown_entry/3).
:- pred deftypes_unknown_entry(+Sg,+Qv,-Call) : callable * list * absu
   # "Gives the ``top'' value for the variables involved in a literal
   whose definition is not present, and adds this top value to
   Call. In this domain the top value is X:term forall X in the set of
   variables".

deftypes_unknown_entry(Sg,Qv,Call) :- terms_unknown_entry(Sg,Qv,Call).

:- dom_impl(deftypes, empty_entry/3).
:- export(deftypes_empty_entry/3).
:- pred deftypes_empty_entry(+Sg,+Vars,-Entry) : callable * list * absu
   # "Gives the \"empty\" value in this domain for a given set of
   variables @var{Vars}, resulting in the abstract substitution
   @var{Entry}. I.e., obtains the abstraction of a substitution in
   which all variables @var{Vars} are unbound: free and unaliased. In
   this domain the empty value is giving the variable type to each
   variable".

deftypes_empty_entry(Sg,Qv,Call) :- terms_empty_entry(Sg,Qv,Call).

%------------------------------------------------------------------%
:- dom_impl(deftypes, call_to_success_fact/9).
:- export(deftypes_call_to_success_fact/9).
:- pred deftypes_call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : callable * list * callable * term * list * absu * absu * absu * absu
   # "Specialized version of call_to_entry + exit_to_prime + extend for facts".

deftypes_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    deftypes_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
    deftypes_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
    terms_extend(Sg,Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%

:- dom_impl(deftypes, input_user_interface/5).
:- export(deftypes_input_user_interface/5).
:- pred deftypes_input_user_interface(+InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   # "Obtains the abstract substitution ASub from user supplied
   information.".

deftypes_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
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

:- dom_impl(deftypes, asub_to_native/5).
:- export(deftypes_asub_to_native/5).
:- pred deftypes_asub_to_native(+ASub,+Qv,+OutFlag,-OutputUser,-Comps)
   # "Transforms abstract substitution @var{ASub} to user friendly format.
      Record relevant symbols for output if @var{OutFlag} is @tt{yes}.".

deftypes_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps):-
    terms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps).

%------------------------------------------------------------------------%

:- dom_impl(deftypes, collect_abstypes_abs/3).
:- export(deftypes_collect_abstypes_abs/3).
deftypes_collect_abstypes_abs(Abs,Types1,Types) :-
    terms_collect_abstypes_abs(Abs,Types1,Types).

:- dom_impl(deftypes, rename_abstypes_abs/3).
:- export(deftypes_rename_abstypes_abs/3).
deftypes_rename_abstypes_abs(ASub,Dict,RenASub) :-
    terms_rename_abstypes_abs(ASub,Dict,RenASub).

%------------------------------------------------------------------%

:- dom_impl(deftypes, identical_abstract/2).
:- export(deftypes_identical_abstract/2).
deftypes_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
deftypes_identical_abstract(ASub1,ASub2):-
    deftypes_identical_abstract0(ASub1,ASub2).

deftypes_identical_abstract0([X:Type0|ASub0],[Y:Type1|ASub1]):-
    X==Y,
    def_equivalent_types(Type0,Type1),
    deftypes_identical_abstract0(ASub0,ASub1).
deftypes_identical_abstract0([],[]).

% ---------------------------------------------------------------------------

% TODO: not in termsd.pl, why?
:- dom_impl(deftypes, contains_parameters/1).
:- export(deftypes_contains_parameters/1).
deftypes_contains_parameters([_:T|Subs]) :-
    ( contains_type_param(T),!
    ; deftypes_contains_parameters(Subs)
    ).

