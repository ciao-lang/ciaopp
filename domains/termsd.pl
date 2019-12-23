:- module(termsd,[], [assertions,regtypes,basicmodes]).

:- doc(title,"termsd: types with shortening (abstract domain)").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").
:- doc(author, "Ciao Development Team").

:- doc(module,"This module implements the abstract operations of the
   type domains with widening based on shortening
   (@pred{shortening_el/3}).  An abstract sustitution is a list of
   @tt{Var:Type} elements, where @var{Var} is a variable and
   @var{Type} is a pure type term @cite{Dart-Zobel}.").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(terms).

:- use_module(library(messages), [warning_message/2]).

:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(lists), [member/2]).
:- use_module(library(sets), [ 
    merge/3,
    ord_subtract/3,
    ord_member/2,
    insert/3]).
:- use_module(library(sort), [sort/2]).

:- use_module(ciaopp(p_unit), [new_internal_predicate/3]).
:- use_module(typeslib(typeslib), [
    assert_param_type_instance/2,
    dz_equivalent_types/2,
    dz_type_included/2,
    equiv_types/2,
    generate_a_type_assigment/3,
    insert_rule/2,
    normalize_type/2,
    new_type_symbol/1,
    pure_type_term/1,
    assert_required_type/1,
    set_atom_type/1,
    set_float_type/1,
    set_int_type/1,
    set_numeric_type/1,
    set_numexp_type/1,
    set_top_type/1,
    type_escape_term_list/2,
    type_intersection_2/3,
    type_union_NoDB/4,
    terms_naive_ewiden_el/2,
    shortening_el/3,
    revert_type/3, revert_types/5,
    concrete/4]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

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

:- dom_impl(terms, input_interface/4).
:- export(terms_input_interface/4).
terms_input_interface(ground(X),perfect,Acc,[gnd(X)|Acc]).
terms_input_interface(regtype(T),perfect,Acc,[T|Acc]):-
    functor(T,_,1),!,
    may_be_var(Acc).
terms_input_interface(regtype(T),perfect,Acc,[NonPT|Acc]):-
    functor(T,_,2),!,
    arg(1,T,V),
    assert_param_type_instance(T,NonPType),
    functor(NonPT,NonPType,1),
    arg(1,NonPT,V),
    may_be_var(Acc).
terms_input_interface(member(X,L),perfect,Acc,[P|Acc]):-
    type_escape_term_list(L,Def),
    new_type_symbol(T),
    insert_rule(T,Def),
    P =.. [T,X].

may_be_var([]):- !.
may_be_var(_Acc).

% ---------------------------------------------------------------------------

:- dom_impl(terms, concrete/3).
:- export(terms_concrete/3).
terms_concrete(Var,ASub,List):-
    get_type(Var,ASub,Type),
    concrete(Type,List,[],[]).

get_type(Var,[NVar:T|_],T):- Var == NVar.
get_type(Var,[_|ASub],T):- 
    get_type(Var,ASub,T).

%------------------------------------------------------------------%
:- dom_impl(terms, compute_lub/2).
:- export(terms_compute_lub/2).
:- pred terms_compute_lub(+ListASub,-Lub) : list(absu) * absu
   # "It computes the least upper bound of a set of abstract
   substitutions.  For each two abstract substitutions @var{ASub1}
   and @var{ASub2} in @var{ListASub}, obtaining the lub is foreach
   X:Type1 in @var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion
   is in Lub, and TypeUnion is the deterministic union of Type1 an
   Type2.".

terms_compute_lub([ASub1,ASub2|Rest],Lub):-
    terms_compute_lub_el(ASub1,ASub2,ASub3_tmp),
    ( current_pp_flag(type_precision,defined) ->
        terms_naive_widen(ASub3_tmp,ASub3)
    ; ASub3 = ASub3_tmp
    ),
    terms_compute_lub([ASub3|Rest],Lub).
terms_compute_lub([ASub],ASub).

%------------------------------------------------------------------%

:- export(terms_compute_lub_el/3).
terms_compute_lub_el('$bottom',ASub,ASub):- !.
terms_compute_lub_el(ASub,'$bottom',ASub):- !.
terms_compute_lub_el(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
terms_compute_lub_el(ASub1,ASub2,ASub3):-
    terms_lub0(ASub1,ASub2,ASub3).

terms_lub0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
    X==Y,
    type_union_NoDB(T1,T2,T3,[]),
    terms_lub0(ASub1,ASub2,ASub3).
terms_lub0([],[],[]).

%---------------------------------------------------------------------%  
% Widening

:- dom_impl(terms, widencall/3).
:- export(terms_widencall/3).
terms_widencall(Prime0,Prime1,NewPrime):-
    terms_widen(Prime0,Prime1,NewPrime).
%       display(terms_widencall),nl,
%       terms_compute_lub_el(Prime0,Prime1,Prime),
%       shortening(Prime,NewPrime).

:- dom_impl(terms, widen/3).
:- export(terms_widen/3).
:- pred terms_widen(+Prime0,+Prime1,-NewPrime)
   : absu * absu * absu
   # "Induction step on the abstract substitution of a fixpoint.
   @var{Prime0} corresponds to non-recursive and @var{Prime1} to
   recursive clauses.  @var{NewPrime} is the result of apply one
   widening operation to the least upper bound of the formers.
   Widening operations implemented are ``shortening'' and ``restricted
   shortening'' @cite{gallagher-types-iclp94,Saglam-Gallagher-95}.".

terms_widen(Prime0,Prime1,NewPrime):-
    terms_compute_lub_el(Prime0,Prime1,Prime),
%       terms_naive_widen(Prime,NewPrime)
%       henten(Prime0,Prime,NewPrime).
    shortening(Prime,NewPrime).
%       jungle(Prime,NewPrime).
%       widen(Prime0,Prime,NewPrime)

terms_naive_widen('$bottom','$bottom').
terms_naive_widen([],[]).
terms_naive_widen([X:T1|Prime],[X:T|NewPrime]):-
    terms_naive_ewiden_el(T1,T),
    terms_naive_widen(Prime,NewPrime).

shortening('$bottom','$bottom').
shortening([],[]).
shortening([X:T1|Asub1],[X:T2|Asub2]):-
    current_pp_flag(depth,Depthk),
    shortening_el(T1,T2,Depthk),
    shortening(Asub1,Asub2).

%% :- pred jungle(+Prime,-NewPrime) : absu * absu
%%    # "A @em{Type Jungle} is a type graph with at most one node for
%%    each function symbol. It can be used as a finite subdomain of
%%    type graphs. This predicate converts a type graph into the
%%    finite domain of type jungles. The main component is the
%%    predicate @tt{build_type_jungle}.".
%% 
%% jungle('$bottom','$bottom').
%% jungle([],[]).
%% jungle([X:T1|Asub1],[X:T2|Asub2]):-
%%      jungle_el(T1,T2),
%%      jungle(Asub1,Asub2).

%---------------------------------------------------------------------%  

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(terms, init_abstract_domain/1).
:- export(terms_init_abstract_domain/1).
terms_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

%------------------------------------------------------------------%
:- dom_impl(terms, call_to_entry/9).
:- export(terms_call_to_entry/9).
:- pred terms_call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo)
   : term * callable * list * callable * term * list * absu * absu * extrainfo
   # "It obtains the abstract substitution @var{Entry} which results
   from adding the abstraction of the @var{Sg} = @var{Head} to
   @var{Proj}, later projecting the resulting substitution onto
   @var{Hv}.

   This is done as follows: 
   @begin{itemize} 
   @item If @var{Sg} and @var{Head} are identical up to renaming it
     is just renaming @var{Proj} and adding the @var{Fv}
   @item Otherwise, it will:
     @begin{itemize} 
     @item obtain the abstract substitution from unifying @var{Sg}
       and @var{Head} calling ``unify_term_and_type_term''
     @item add to this abstract substituion the variables in
       @var{Fv} as term type.
     @end{itemize} 
   @end{itemize} 

   The meaning of the variables is:
   @begin{itemize}
   @item @var{Sg} is the subgoal being analysed. 
   @item @var{Head} is the Head of the clause being analysed. 
   @item @var{Fv} is a list of free variables in the body of the
     clause being considered.
   @item @var{Proj} is the abstract substitution @var{Call}
     projected onto @var{Sv}.
   @item @var{Entry} is the Abstract entry substitution (i.e. the
     abstract subtitution obtained after the abstract unification
     of @var{Sg} and @var{Head} projected onto @var{Hv} +
     @var{Fv}).
   @item @var{ExtraInfo} is a flag @tt{yes} when no unification is
     required, i.e., @tt{Entry=Proj} upto names of vars. and
     ignoring @var{Fv}. It is @tt{no} if unification fails.
   @end{itemize}".

terms_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag):- 
    variant(Sg,Head), !,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    terms_abs_sort(NewProj_u,NewProj),
    variables_are_variable_type(Fv,Free),
    merge(Free,NewProj,Entry).
terms_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,dummy):-
    unify_term_and_type_term(Head,Hv,Sg,Proj,TmpEntry), !,
    variables_are_variable_type(Fv,Tmp),
    merge(Tmp,TmpEntry,Entry).
terms_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- regtype extrainfo/1.

extrainfo(yes).
extrainfo(no).

:- export(variables_are_variable_type/2). % (shared with deftypes.pl)
:- pred variables_are_variable_type(+Fv,-ASub) : list * absu
   # "(at the moment) assigns the value top_type to the variables in
   @var{Fv} but in the future it must assign the value @tt{var}".

variables_are_variable_type(Fv,ASub):-
    variables_are_top_type(Fv,ASub).

%------------------------------------------------------------------%
:- dom_impl(terms, exit_to_prime/7).
:- export(terms_exit_to_prime/7).
:- pred terms_exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime)
   : list * list * callable * callable * absu * extrainfo * absu
   # "It computes the prime abstract substitution @var{Prime}, i.e.
   the result of going from the abstract substitution over the head
   variables @var{Exit}, to the abstract substitution over the
   variables in the subgoal. It will:

   @begin{itemize}
   @item If @var{Exit} is '$bottom', @var{Prime} will be also
     '$bottom'.
   @item If @var{ExtraInfo} = yes (@var{Head} and @var{Sg}
     identical up to renaming) it is just renaming Exit %
   @item Otherwise, it will:
     @begin{itemize}                                                        
     @item projects @var{Exit} onto @var{Hv} obtaining
       @var{BPrime}.
     @item obtain the abstract substitution from unifying @var{Sg}
       and @var{Head} calling ``unify_term_and_type_term''
     @end{itemize}
   @end{itemize}".

terms_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
    Prime = '$bottom'.
terms_exit_to_prime(Sg,Hv,Head,_Sv,Exit,yes,Prime):- !,
    terms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    terms_abs_sort(NewPrime,Prime). 
terms_exit_to_prime(Sg,Hv,Head,Sv,Exit,_ExtraInfo,Prime):- 
    terms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    unify_term_and_type_term(Sg,Sv,Head,BPrime,Prime).
terms_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').

:- export(unify_term_and_type_term/5). % (shared with deftypes.pl)
:- pred unify_term_and_type_term(+Term1,+Tv,+Term2,+ASub,-NewASub)
   : callable * list * callable * absu * absu
   # "It unifies the term @var{Term1} to the type term @var{Term2}
   obtaining the the abstract substitution TypeAss which is sorted
   and projeted on @var{Tv}".

unify_term_and_type_term(Term1,Tv,Term2,ASub,NewASub):-
    copy_term((Term2,ASub),(TypeTerm,ASub0)),
    TypeTerm =.. [_|Types],
    Term1 =.. [_|Args],
    type_escape_term_list(Types,EscTypes),
    apply(ASub0),
    generate_a_type_assigment(EscTypes,Args,TypeAss),
    ( member(_:bot,TypeAss) ->
        fail
    ; terms_abs_sort(TypeAss,ASub1),
      terms_project(not_provided_Sg,Tv,not_provided_HvFv_u,ASub1,NASub),
      normal_asub(NASub,NewASub)
    ).

% TODO: why? only after terms_project/5
normal_asub([],[]).
normal_asub([X:Type|ASub],[X:NType|NASub]):-
    normalize_type(Type,NType),
    normal_asub(ASub,NASub).

:- pred apply(+ASub) : absu 
   # "It unifies the variables in the abstract substitution @var{ASub}
   to his respective values".

apply([X:Term|ASub]):-
    X=Term,
    apply(ASub).
apply([]).

%------------------------------------------------------------------%
:- dom_impl(terms, project/5).
:- export(terms_project/5).
:- pred terms_project(+Sg,+Vars,+HvFv_u,+Asub,-Proj)
   : term * list * list * absu * absu
   # "@var{Proj} is the result of eliminating from @var{Asub} all
   @var{X}:@var{Value} such that @var{X} is not in @var{Vars}".

terms_project(_Sg,_Vars,_HvFv_u,'$bottom',Proj):- !,
    Proj = '$bottom'.
terms_project(_Sg,Vars,_HvFv_u,ASub,Proj) :- 
    terms_project_aux(Vars,ASub,Proj).

terms_project_aux([],_,Proj):- !,
    Proj = [].
terms_project_aux(_,[],Proj):- !,
    Proj = [].
terms_project_aux([Head1|Tail1],[Head2:Type|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    terms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

terms_project_aux_(=,_,Tail1,HeadType,Tail2,[HeadType|Proj]) :-
    terms_project_aux(Tail1,Tail2,Proj).
terms_project_aux_(>,Head1,Tail1,_,[Head2:Type|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    terms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

%------------------------------------------------------------------%
:- dom_impl(terms, abs_sort/2).
:- export(terms_abs_sort/2).
:- pred terms_abs_sort(+Asub,-Asub_s) : absu * absu
   # "It sorts the set of @var{X}:@var{Type} in @var{Asub} containing
   @var{Asub_s}".

terms_abs_sort('$bottom','$bottom'):- !.
terms_abs_sort(ASub,ASub_s):- sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- dom_impl(terms, extend/5).
:- export(terms_extend/5).
:- pred terms_extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : term * absu * list * absu * absu
   # "If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
   @var{Succ} is computed updating the values of @var{Call} with
   those in @var{Prime}".

terms_extend(_Sg,'$bottom',_Sv,_Call,'$bottom'):- !.
terms_extend(_Sg,Prime,Sv,Call,Succ):-
    subtract_keys(Call,Sv,RestCall),
    merge(RestCall,Prime,Succ).

subtract_keys([K:_|Xs],Ks,Dict):-
    ord_member(K,Ks), !,
    subtract_keys(Xs,Ks,Dict).
subtract_keys([X|Xs],Ks,[X|Dict]):-
    subtract_keys(Xs,Ks,Dict).
subtract_keys([],_Ks,[]).

%------------------------------------------------------------------%
:- dom_impl(terms, less_or_equal/2).
:- export(terms_less_or_equal/2).
:- pred terms_less_or_equal(+ASub0,+ASub1) : absu * absu
   # "Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
   it's assumed the two abstract substitutions are defined on the same
   variables".

terms_less_or_equal('$bottom',_ASub):- !.
terms_less_or_equal(ASub1,ASub2):-
    ASub1 == ASub2, !.
terms_less_or_equal(ASub1,ASub2):-
    terms_less_or_equal0(ASub1,ASub2).

terms_less_or_equal0([X:T1|ASub1],[Y:T2|ASub2]):-
    X==Y,
    dz_type_included(T1,T2),
    terms_less_or_equal0(ASub1,ASub2).
terms_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- dom_impl(terms, glb/3).
:- export(terms_glb/3).
:- pred terms_glb(+ASub0,+ASub1,-Glb) : absu * absu * absu 
   # "@var{Glb} is the great lower bound of @var{ASub0} and
   @var{ASub1}".

terms_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
terms_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
terms_glb(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
terms_glb(ASub1,ASub2,ASub3):-
    terms_glb0(ASub1,ASub2,ASub3), !.
terms_glb(_ASub1,_ASub2,'$bottom').

terms_glb0([X:T1|ASub1],[Y:T2|ASub2],[X:T3|ASub3]):-
    X==Y,
    type_intersection_2(T1,T2,T3),!,
    ( T3==bot ->
        fail 
    ; terms_glb0(ASub1,ASub2,ASub3)
    ).
terms_glb0([],[],[]).

%------------------------------------------------------------------%
:- dom_impl(terms, unknown_entry/3).
:- export(terms_unknown_entry/3).
:- pred terms_unknown_entry(+Sg,+Qv,-Call) : callable * list * absu
   # "Gives the ``top'' value for the variables involved in a literal
   whose definition is not present, and adds this top value to
   Call. In this domain the top value is X:term forall X in the set of
   variables".

terms_unknown_entry(_Sg,Vars,ASub):-
    variables_are_top_type(Vars,ASub).

:- dom_impl(terms, empty_entry/3).
:- export(terms_empty_entry/3).
:- pred terms_empty_entry(+Sg,+Vars,-Entry) : callable * list * absu
   # "Gives the ""empty"" value in this domain for a given set of
   variables @var{Vars}, resulting in the abstract substitution
   @var{Entry}. I.e., obtains the abstraction of a substitution in
   which all variables @var{Vars} are unbound: free and unaliased. In
   this domain the empty value is giving the variable type to each
   variable".

terms_empty_entry(_Sg,Vars,ASub):-
    variables_are_variable_type(Vars,ASub).

%------------------------------------------------------------------%
:- dom_impl(terms, unknown_call/4).
:- export(terms_unknown_call/4).
:- pred terms_unknown_call(+Sg,+Vars,+Call,-Succ) : callable * list * absu * absu
   # "Gives the ``top'' value for the variables involved in a literal
   whose definition is not present, and adds this top value to
   @var{Call}".

terms_unknown_call(_Sg,Vars,Call,Succ):-
    substitution(Call,CallVars,_),
    ord_subtract(Vars,CallVars,TopVars),
    variables_are_top_type(TopVars,ASub),
    merge(Call,ASub,Succ).

:- export(substitution/3).
substitution([],[],[]).
substitution([X:T|TypeAss],[X|Vars],[T|ListTypes]):-
    substitution(TypeAss,Vars,ListTypes).

:- export(variables_are_top_type/2).
:- pred variables_are_top_type(+Fv,-ASub) : list * absu
   # "It assigns the value top_type to the variables in @var{Fv} and
   return the abstract substitution @var{ASub}".

variables_are_top_type([V|Fv],[V:Type|ASub]):-
    set_top_type(Type),
    variables_are_top_type(Fv,ASub).
variables_are_top_type([],[]).

%------------------------------------------------------------------%
:- dom_impl(terms, call_to_success_fact/9).
:- export(terms_call_to_success_fact/9).
:- pred terms_call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : callable * list * callable * term * list * absu * absu * absu * absu
   # "Specialized version of call_to_entry + exit_to_prime + extend for facts".

terms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    terms_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
    terms_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
    terms_extend(Sg,Prime,Sv,Call,Succ).

% ---------------------------------------------------------------------------
% Builtins

:- dom_impl(terms, special_builtin/5).
:- export(terms_special_builtin/5).
:- pred terms_special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)
   # "@var{Type} is a flag indicating what is the abstraction of
   builtin @var{SgKey} and to which variables @var{Condvars} of the
   goal @var{Sg} it affects.".

terms_special_builtin('!/0',_Sg,_Subgoal,id,[]).
terms_special_builtin('@=</2',_Sg,_Subgoal,id,[]).
terms_special_builtin('@>/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('@>=/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('@</2',_Sg,_Subgoal,id,[]).
terms_special_builtin('\\==/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('==/2',_Sg,_Subgoal,id,[]).
terms_special_builtin('display/1',_Sg,_Subgoal,id,[]).
terms_special_builtin('get_code/1',Sg,_Subgoal,type(T),Condvars):-
    set_int_type(T),
    varset(Sg,Condvars).
% terms_special_builtin('integer/1',Sg,_Subgoal,type(T),Condvars):-
%         set_int_type(T),
%       varset(Sg,Condvars).
terms_special_builtin('atom/1',Sg,_Subgoal,type(T),Condvars):-
    set_atom_type(T), % no, it is atom or num type
    varset(Sg,Condvars).
terms_special_builtin('atomic/1',Sg,_Subgoal,type(T),Condvars):-
    set_atom_type(T), % no, it is atom or num type
    varset(Sg,Condvars).
terms_special_builtin('var/1',_Sg,_Subgoal,id,[]).
    % set_top_type(T),
    % varset(Sg,Condvars).
terms_special_builtin('nonvar/1',_Sg,_Subgoal,id,[]).
    % set_top_type(T),
    % varset(Sg,Condvars).
terms_special_builtin('ground/1',_Sg,_Subgoal,id,[]).
    % set_top_type(T),
    % varset(Sg,Condvars).
% terms_special_builtin('float/1',Sg,_Subgoal,type(T),Condvars):-
%       set_float_type(T),
%       varset(Sg,Condvars).
% terms_special_builtin('number/1',Sg,_Subgoal,type(T),Condvars):-
%       set_numeric_type(T),
%       varset(Sg,Condvars).
terms_special_builtin('fail/0',_Sg,_Subgoal,bot,[]).
terms_special_builtin('true/0',_Sg,_Subgoal,id,[]).
terms_special_builtin('nl/0',_Sg,_Subgoal,id,[]).
terms_special_builtin('repeat/0',_Sg,_Subgoal,id,[]).
%
terms_special_builtin('erase/1',Sg,_Subgoal,type(T),Condvars):-
    set_top_type(T),
    varset(Sg,Condvars).
%
terms_special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
    terms_very_special_builtin(Key).

terms_very_special_builtin('=/2').

%------------------------------------------------------------------------%
% terms_success_builtin(+Type,+Sv_uns,+Condvars,+HvFv_u,+Call,-Succ)             %
% Depending on Type it computes the abstraction of a builtin affecting   %
% variables Condvars and having variables Sv_uns with call subs. Call.   %
%------------------------------------------------------------------------%

:- dom_impl(terms, success_builtin/6).
:- export(terms_success_builtin/6).
terms_success_builtin(id,_Sv_uns,_Condvars,_HvFv_u,Call,Call).
terms_success_builtin(bot,_Sv_uns,_Condvars,_HvFv_u,_Call,'$bottom').
terms_success_builtin(type(T),_Sv_uns,Condvars,_HvFv_u,Call,Succ):-
    keys_same_value(Condvars,T,Prime),
    terms_extend(not_provided_Sg,Prime,Condvars,Call,Succ).
terms_success_builtin(Key,_Sv_uns,_Condvars,_HvFv_u,Call,Call):-
    warning_message("the builtin key ~q is not defined",[Key]).

keys_same_value([K|Ks],V,[K:V|ASub]):-
    keys_same_value(Ks,V,ASub).
keys_same_value([],_V,[]).

%------------------------------------------------------------------------%
% terms_call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)        %
% Same as above but for each particular builtin.                         %
%------------------------------------------------------------------------%

:- dom_impl(terms, call_to_success_builtin/6).
:- export(terms_call_to_success_builtin/6).
terms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):- !,
    terms_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
terms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    % TODO: use new code?
    ( precondition_builtin(Key,Sg) ->
        postcondition_builtin(Key,Bg,Bv,Exit),
        terms_exit_to_prime(Sg,Bv,Bg,Sv,Exit,no,Prime1),
        terms_glb(Proj,Prime1,Prime),
        terms_extend(Sg,Prime,Sv,Call,Succ)
    ; Succ = '$bottom'
    ).

% (shared with deftypes.pl)
:- export(precondition_builtin/2).
precondition_builtin('is/2',(X is _Y)):-
    (var(X);number(X)).
precondition_builtin(_Key,_).

% (shared with deftypes.pl)
:- export(postcondition_builtin/4).
postcondition_builtin('list/1',list(X1),Bv,Exit):-
    TX = list,
    Exit_u = [X1:TX],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('num/1',num(X1),Bv,Exit):-
    set_numeric_type(TX),
    Exit_u = [X1:TX],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('number/1',number(X1),Bv,Exit):-
    set_numeric_type(TX),
    Exit_u = [X1:TX],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('float/1',float(X1),Bv,Exit):-
    set_float_type(TX),
    Exit_u = [X1:TX],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('integer/1',integer(X1),Bv,Exit):-
    set_int_type(TX),
    Exit_u = [X1:TX],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('int/1',int(X1),Bv,Exit):-
    set_int_type(TX),
    Exit_u = [X1:TX],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('is/2',(X1 is Y1),Bv,Exit):-
    set_numexp_type(TY),
    set_numeric_type(TX),
    Exit_u = [X1:TX,Y1:TY],
    Bv_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('>/2',(X > Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    Exit_u = [X:TX,Y:TY],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('>=/2',(X >= Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    Exit_u = [X:TX,Y:TY],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('</2',(X < Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    Exit_u = [X:TX,Y:TY],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('=</2',(X =< Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    Exit_u = [X:TX,Y:TY],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('=\\=/2',(X =\= Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    Exit_u = [X:TX,Y:TY],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('=:=/2',(X =:= Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    Exit_u = [X:TX,Y:TY],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('functor/3',functor(X1,Y1,Z1),Vars,Exit):-
    set_int_type(TZ),
    set_atom_type(TY),
    set_top_type(TX),
    Exit_u = [X1:TX,Y1:TY,Z1:TZ],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('arg/3',arg(X1,Y1,Z1),Vars,Exit):-
    set_int_type(TX),
    set_top_type(TY),
    set_top_type(TZ),
    Exit_u = [X1:TX,Y1:TY,Z1:TZ],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('current_op/3',current_op(X1,Y1,Z1),Vars,Exit):-
    set_top_type(TX),
    set_atom_type(TY),
    set_atom_type(TZ),
    Exit_u = [X1:TX,Y1:TY,Z1:TZ],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('member/2',member(X1,Y1),Vars,Exit):-
    set_top_type(TX),
    set_top_type(TY), % TY = pt1,
    Exit_u = [X1:TX,Y1:TY],
    Vars_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('=../2',X1=..Y1,Vars,Exit):-
    set_top_type(TX),
    set_top_type(TY), %TY = pt1,
    Exit_u = [X1:TX,Y1:TY],
    Vars_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('numbervars/3',numbervars(X1,Y1,Z1),Vars,Exit):-
    set_int_type(TZ),
    set_int_type(TY),
    set_top_type(TX),
    Exit_u = [X1:TX,Y1:TY,Z1:TZ],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('name/2',name(X1,Y1),Vars,Exit):-
    set_atom_type(TX),
    set_top_type(TY), % TY = pt1,
    Exit_u = [X1:TX,Y1:TY],
    Vars_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).

%------------------------------------------------------------------------%

:- dom_impl(terms, input_user_interface/5).
:- export(terms_input_user_interface/5).
:- pred terms_input_user_interface(+InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   # "Obtains the abstract substitution ASub from user supplied
   information.".

terms_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
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
    arg(1,User,X),
    obtain_Asub_user(InputUser,ASub).

reduce_same_var([X:T|ASub],NewASub):-
    reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var([],[]).

reduce_same_var_([Y:TY|ASub],X,TX,NewASub):-
    reduce_same_var__(Y,TY,X,TX,ASub,NewASub).
reduce_same_var_([],X,T,[X:T]).

reduce_same_var__(Y,TY,X,TX,ASub,NewASub):-
    X == Y, !,
    type_intersection_2(TY,TX,T),
    reduce_same_var_(ASub,X,T,NewASub).
reduce_same_var__(Y,TY,X,TX,ASub,[X:TX|NewASub]):-
    reduce_same_var_(ASub,Y,TY,NewASub).

% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
%       Type=..[T,X],
%       inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).

%------------------------------------------------------------------------%

:- dom_impl(terms, asub_to_native/5).
:- export(terms_asub_to_native/5).
:- pred terms_asub_to_native(+ASub,+Qv,+Flag,-OutputUser,-Comps)
   # "Transforms abstract substitution ASub to user friendly format.".

terms_asub_to_native(ASub,_Qv,Flag,OutputUser,[]):-
    terms_asub_to_native0(ASub,OutputUser1),
    equiv_types(OutputUser1,OutputUser2),
    revert_types(OutputUser2,OutputUser,new_internal_predicate,Symbols,[]),
    recorda_required_types(Flag,Symbols).

terms_asub_to_native0([X:T|ASub],[Type|OutputUser]):-
    revert_type(T,X,Type),
    terms_asub_to_native0(ASub,OutputUser).
terms_asub_to_native0([],[]).

% ---------------------------------------------------------------------------

:- export(recorda_required_types/2).
recorda_required_types(no,_Symbols).
recorda_required_types(yes,Symbols):-
    recorda_required_types_(Symbols).

recorda_required_types_([T|Types]):-
    ( imported_type(T) -> true
    ; assert_required_type(T)
    ),
    recorda_required_types_(Types).
recorda_required_types_([]).

:- use_module(ciaopp(p_unit), [type_of_goal/2]).

imported_type(T) :-
    functor(T,F,A),
    A1 is A+1,
    functor(G,F,A1),
    type_of_goal(imported,G), !.

%------------------------------------------------------------------------%
% terms_output_interface(+ASub,-Output)                                  %
% Transforms abstract substitution ASub to a more readible but still     %
% close to internal format.                                              %
%------------------------------------------------------------------------%

:- export(terms_output_interface/2).
terms_output_interface(ASub,ASub).

%------------------------------------------------------------------------%

:- use_module(library(assoc), [get_assoc/3]).

:- dom_impl(terms, collect_abstypes_abs/3).
:- export(terms_collect_abstypes_abs/3).
terms_collect_abstypes_abs([],Types,Types).
terms_collect_abstypes_abs([_:Type|Abs],Types0,Types):-
    insert(Types0,Type,Types1),
    terms_collect_abstypes_abs(Abs,Types1,Types).

:- dom_impl(terms, rename_abstypes_abs/3).
:- export(terms_rename_abstypes_abs/3).
terms_rename_abstypes_abs([],_,[]).
terms_rename_abstypes_abs([C|Call],Dict,[RenC|RenCall]):-
    Dict = (Types,_),
    C = Var:Type,
    RenC = Var:RenType,
    get_value_(Types,Type,RenType),
%       new_type_name(RenName),
%       insert_type_name(RenName,[],0),
    terms_rename_abstypes_abs(Call,Dict,RenCall).

get_value_(Rens,Type,RenType):-
    assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%

:- dom_impl(terms, identical_abstract/2).
:- export(terms_identical_abstract/2).
terms_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
terms_identical_abstract(ASub1,ASub2):-
    terms_identical_abstract0(ASub1,ASub2).

terms_identical_abstract0([X:Type0|ASub0],[Y:Type1|ASub1]):-
    X==Y,
    dz_equivalent_types(Type0,Type1),
    terms_identical_abstract0(ASub0,ASub1).
terms_identical_abstract0([],[]).
