:- module(eterms, [], [assertions,regtypes,modes_extra,hiord]).

:- doc(title,"eterms: types with lnewiden_el/4 (abstract domain)").
:- doc(author, "Claudio Vaucheret").
:- doc(author, "Francisco Bueno").
:- doc(author, "Ciao Development Team").
:- doc(stability, prod).

% TODO: Document widening and abstract domain (Name) (see paper)

:- doc(module,"This module implements the abstract operations of the
   type domains with widening based on 
   (@pred{lnewiden_el/4}).  An abstract sustitution is a list of
   @tt{Var:(Name,Type)} elements, where @var{Var} is a variable and
   @var{Type} is a pure type term @cite{Dart-Zobel}.").

% TODO: document flags, e.g., type_eval

:- doc(bug,"An (imported?) goal which is a regtype should probably be treated
    as a builtin: its success is itself! Maybe do it in trust.pl?
    Otherwise, assertions trust list(X) => list(X) should be added.").

:- doc(bug, "2 commented out last clause of eterms_very_special_builtin. 
      This may lose precision, but otherwise type_eval produces wrong
      results").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(eterms).

:- use_module(typeslib(typeslib), [
    compound_pure_type_term/4,
    construct_compound_pure_type_term/2,
    dz_equivalent_types/2,
    dz_type_included/2,
    get_type_definition/2,
    maybe_get_type_definition/2,
    get_type_name/2,
    get_equiv_name/2,
    insert_equiv_name/2,
    retract_equiv_name/2,
    insert_rule/2,
    normalize_type/2,
    insert_type_name/3,
    native_type_symbol/1,
    new_type_name/1,
    new_type_symbol/1,
    pure_type_term/1,
    retract_type_name/3,
    lab_intersect/2,
    set_top_type/1,
    top_type/1,
    type_escape_term_list/2,
    type_intersection_2/3,
    resetunion/0,
    type_union/3,
    lnewiden_el/4,
    get_less_numeric_type/2,
    get_canonical_name/2,
    concrete/4,
    partial_concrete/4,
    revert_type_internal/3]).
:- use_module(domain(termsd), [
    terms_input_interface/4,
    terms_internal_to_native/3,
    generate_a_type_assignment/3]).

% CiaoPP library
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(spec(unfold_builtins), [can_be_evaluated/1]).

:- use_module(engine(hiord_rt), [call/1]).
:- use_module(engine(hiord_rt), ['$meta_call'/1]).

:- use_module(ciaopp(plai/apply_assertions_old), [apply_trusted0/7]).
% IG: trusts should not be applied in domain operations

:- use_module(library(hiordlib), [maplist/2, maplist/3]).
:- use_module(library(messages)).
:- use_module(library(aggregates), [(^)/2, findall/4, setof/3]).
:- use_module(library(terms_vars), [varset/2, varsbag/3]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(lists), [
    member/2,
    append/3,
    reverse/2,
    dlist/3,
    nth/3,
    cross_product/2]).
:- use_module(library(sets), [ 
    merge/3,
    ord_subtract/3,
    insert/3,
    ord_union/3,
    ord_delete/3]).
:- use_module(library(assoc), [get_assoc/3]).
:- use_module(library(sort), [sort/2]).

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
% init_abstract_domain sets widen to 'on'

:- prop eterms_asub(A) # "@var{A} is an abstract substitution".
eterms_asub('$bottom').
eterms_asub([]).
eterms_asub([Elem|Absu]):-
    eterms_asub_elem(Elem),
    eterms_asub(Absu).

:- prop eterms_asub_elem(E) # "@var{E} is a single substitution".
eterms_asub_elem(Var:Type):-
    var(Var),
    pure_type_term(Type). % TODO: incorrect? (we have pairs)
eterms_asub_elem(ListVar:Type):-
    list(var,ListVar),
    pure_type_term(Type).

% (shared with etermsvar.pl)
:- export(get_type/3). % TODO: get type from asub, rename
get_type(Var,[NVar:(_,T0)|_],T):- Var == NVar, !, T = T0.
get_type(Var,[_|ASub],T):- 
    get_type(Var,ASub,T).

:- prop hvfv_u(A) # "`A` is head variables and free variables possibly unsorted".
hvfv_u(not_provided_HvFv_u).
hvfv_u(X):- list(var,X).

%------------------------------------------------------------------%
:- dom_impl(eterms, init_abstract_domain/1).
:- export(eterms_init_abstract_domain/1).
eterms_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

%------------------------------------------------------------------%
:- dom_impl(eterms, compute_lub/2).
:- export(eterms_compute_lub/2).
:- pred eterms_compute_lub(+ListASub,-Lub)
   : list(eterms_asub, ListASub) => eterms_asub(Lub)
   # "It computes the least upper bound of a set of abstract
   substitutions.  For each two abstract substitutions @var{ASub1} and
   @var{ASub2} in @var{ListASub}, obtaining the lub is foreach X:Type1
   in @var{ASub1} and X:Type2 in @var{ASub2}, X:TypeUnion is in Lub,
   and TypeUnion is the deterministic union of Type1 an Type2.".

eterms_compute_lub([ASub1,ASub2|Rest],Lub):-
    eterms_compute_lub_el(ASub1,ASub2,ASub3),
    !,
    eterms_compute_lub([ASub3|Rest],Lub).
eterms_compute_lub([ASub],ASub).

%------------------------------------------------------------------%

:- export(eterms_compute_lub_el/3).
eterms_compute_lub_el('$bottom',ASub,ASub):- !.
eterms_compute_lub_el(ASub,'$bottom',ASub):- !.
eterms_compute_lub_el(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
eterms_compute_lub_el(ASub1,ASub2,ASub3):-
    eterms_lub0(ASub1,ASub2,ASub3).

eterms_lub0([X:(N1_e,T1)|ASub1],[Y:(N2_e,T2)|ASub2],[X:(N2,T3)|ASub3]):-
    X==Y,
    get_canonical_name(N1_e,N1),
    get_canonical_name(N2_e,N2),
    ( 
        ( top_type(T2) ; top_type(T1) ) -> set_top_type(T3) 
    ;
        resetunion,
        type_union(T1,T2,T3)
    ),
%       lab_intersect(N1,N2),
    lab_intersect(N2,N1),
    eterms_lub0(ASub1,ASub2,ASub3).
eterms_lub0([],[],[]).

%---------------------------------------------------------------------%  
% Widening

:- dom_impl(eterms, widencall/3).
:- export(eterms_widencall/3).
eterms_widencall(Prime0,Prime1,Result):-
%       display(user,'widencall'),
    eterms_widen(Prime0,Prime1,Result).     

:- dom_impl(eterms, needs/1).
:- export(eterms_needs/1).
eterms_needs(widen).
eterms_needs(auxinfo).

:- dom_impl(eterms, widen/3).
:- export(eterms_widen/3).
:- pred eterms_widen(+Prime0,+Prime1,-NewPrime)
   : eterms_asub * eterms_asub * term => eterms_asub(NewPrime)
   # "Induction step on the abstract substitution of a fixpoint.
   @var{Prime0} corresponds to non-recursive and @var{Prime1} to
   recursive clauses.  @var{NewPrime} is the result of apply one
   widening operation to the least upper bound of the formers.".

eterms_widen(Prime0,Prime1,NewPrime):-
    % display(user,'widen'),nl(user),
    eterms_compute_lub_el(Prime0,Prime1,Prime),
    ewiden(Prime0,Prime,NewPrime).

ewiden('$bottom','$bottom','$bottom') :- !.
ewiden('$bottom',Prime,Prime).
ewiden([],[],[]).
ewiden([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
    ( current_pp_flag(type_eval,on) -> TEval = yes ; TEval = no ),
    lnewiden_el(T1,T2,TEval,T),
    ewiden(Prime0,Prime,NewPrime).
    
%------------------------------------------------------------------%

:- regtype eterms_extrainfo(_).
eterms_extrainfo(_). % TODO: define

:- dom_impl(eterms, call_to_entry/9).
:- export(eterms_call_to_entry/9).
:- pred eterms_call_to_entry(+Sv,+Sg,+Hv,+Head,+K,+Fv,+Proj,-Entry,-ExtraInfo)
   : term * cgoal * list * cgoal * term * list * eterms_asub * term * term
   => (eterms_asub(Entry), eterms_extrainfo(ExtraInfo))
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
     @item add to this abstract substitution the variables in Fv as
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
   @item @var{ExtraInfo}is a flag ``yes'' when no unification is
     required, i.e., Entry=Proj upto names of vars. and ignoring
     Fv. It is ``no'' if unification fails.
   @end{itemize}".

eterms_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,(yes,Proj)):- 
    variant(Sg,Head), !,
    copy_term((Sg,Proj),(NewTerm,NewProj_u)),
    Head = NewTerm,
    eterms_abs_sort(NewProj_u,NewProj),
    eterms_project(Sg,Hv,not_provided_HvFv_u,NewProj,NewProj1),
    variables_are_variable_type(Fv,Free),
    merge(Free,NewProj1,Entry).
eterms_call_to_entry(_Sv,Sg,Hv,Head,_K,Fv,Proj,Entry,(no,Proj)):-
    unify_term_and_type_term(Head,Hv,Sg,Proj,TmpEntry), !,
    variables_are_variable_type(Fv,Tmp),
    merge(Tmp,TmpEntry,Entry).
eterms_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,_Proj,'$bottom',no).

:- pred variables_are_variable_type(+Fv,-ASub)
   : list(Fv) => eterms_asub(ASub)
   # "At the moment it assigns the value top_type to the variables in
   @var{Fv} but in the future it must assign the value ``var''".

% create_names([],[]).
% create_names([X:(N,T)|Proj],[X:(Name,T)|Proj1]):-
%       new_type_name(Name),
%       insert_type_name(Name,T,[]),
%       create_names(Proj,Proj1).

variables_are_variable_type(Fv,ASub):-
    variables_are_top_type(Fv,ASub).

%------------------------------------------------------------------%
:- dom_impl(eterms, exit_to_prime/7).
:- export(eterms_exit_to_prime/7).
:- pred eterms_exit_to_prime(+Sg,+Hv,+Head,+Sv,+Exit,-ExtraInfo,-Prime)
   : term * list * cgoal * cgoal * eterms_asub * term * term
   => (eterms_extrainfo(ExtraInfo), eterms_asub(Prime))
   # "It computes the prime abstract substitution @var{Prime}, i.e.
   the result of going from the abstract substitution over the head
   variables @var{Exit}, to the abstract substitution over the
   variables in the subgoal. It will:
   @begin{itemize}
   @item If @var{Exit} is '$bottom', @var{Prime} will be also
     '$bottom'.
   @item If @var{ExtraInfo} = yes (@var{Head} and @var{Sg} identical
     up to renaming) it is just renaming Exit %
   @item Otherwise, it will:
     @begin{itemize}                                                        
     @item projects @var{Exit} onto @var{Hv} obtaining @var{BPrime}.
     @item obtain the abstract substitution from unifying @var{Sg} and
       @var{Head} calling ``unify_term_and_type_term''
     @end{itemize}
   @end{itemize}".

eterms_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
    Prime = '$bottom'.
eterms_exit_to_prime(Sg,Hv,Head,_Sv,Exit,(yes,Proj),Prime):- !,
    eterms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    eterms_abs_sort(NewPrime,Prime1),
    replace_names(Proj,Prime1,Prime).       
eterms_exit_to_prime(Sg,Hv,Head,Sv,Exit,(no,ExtraInfo),Prime):- 
    eterms_project(Sg,Hv,not_provided_HvFv_u,Exit,BPrime),
    unify_term_and_type_term_exit(Sg,Sv,Head,BPrime,ExtraInfo,Prime), !. %,!, %change
  % TODO: cut was disabled here
%
% probar agregar sinonimos de ExtraInfo a Prime
%%      replace_names(ExtraInfo,Prime1,Prime).
eterms_exit_to_prime(_Sg,_Hv,_Head,_Sv,_Exit,_ExtraInfo,'$bottom').

% replace_names1([],[],[]).
% replace_names1([X:(N,_T)|ExtraInfo],[X:(_N1,T1)|Prime1],[X:(N,T1)|Prime]):-
%       replace_names1(ExtraInfo,Prime1,Prime).

:- export(replace_names/3). % (shared with etermsvar.pl)
replace_names([],[],[]).
replace_names([X:(N_e,_T)|ExtraInfo],[X:(N1_e,T1)|Prime1],[X:(N,T1)|Prime]):-
    get_canonical_name(N_e,N),
    get_canonical_name(N1_e,N1),
    lab_intersect(N,N1),
%       get_type_name(N1,LN1),
% %     retract_type_name(N1,LN1,C1),
%       retract_type_name(N,LN,C),
%       merge(LN,LN1,L),
% %     insert_type_name(N1,LN1,C1),
%       insert_type_name(N,L,C),
    replace_names(ExtraInfo,Prime1,Prime).

% % replace_names([],[],[]).
% % replace_names([X:(N,_T)|ExtraInfo],[X:(N1,T1)|Prime1],[X:(N1,T1)|Prime]):-
% %     retract_type_name(N1,L,C1),
% %     insert(L,([],N),L1),
% %     insert_type_name(N1,L1,C1),
% %     replace_names(ExtraInfo,Prime1,Prime).

:- pred unify_term_and_type_term(+Term1,+Tv,+Term2,+ASub,-NewASub)
   : cgoal * list * cgoal * eterms_asub * term => eterms_asub(NewASub)
   # "It unifies the term @var{Term1} to the type term @var{Term2}
   obtaining the the abstract substitution TypeAss which is sorted and
   projeted on @var{Tv}".

unify_term_and_type_term_exit(Term1,Tv,Term2,ASub,Proj,NewASub):-
    copy_term((Term2,ASub),(TypeTerm,ASub0)),
    Term2 =.. [_|HeadArg], 
    TypeTerm =.. [_|Types],
    Term1 =.. [_|Args],
    type_escape_term_list(Types,EscTypes),
    apply(ASub0),
    generate_a_type_assignment(EscTypes,Args,TypeAss),
    ( member(_:bot,TypeAss) ->
        fail
    ; 
        sort(Proj,Proj_s),
        eterms_abs_sort(TypeAss,ASub1),
        obtains_names(HeadArg,Args,ASub,TypeNameAss),

        % generate_subs_exit(ASub1,Proj,Subs),
        % update_names(TypeNameAss,Subs),

        sort(TypeNameAss,TypeNameAss_s),
        generate_subs_exit(ASub1,Proj_s,TypeNameAss_s,Subs),

        eterms_project(not_provided_Sg,Tv,not_provided_HvFv_u,Subs,NASub),
        normal_asub(NASub,NewASub)
    ).

unify_term_and_type_term(Term1,Tv,Term2,ASub,NewASub):-
    copy_term((Term2,ASub),(TypeTerm,ASub0)),
    Term2 =.. [_|HeadArg], 
    TypeTerm =.. [_|Types],
    Term1 =.. [_|Args],
    type_escape_term_list(Types,EscTypes),
    apply(ASub0),
    generate_a_type_assignment(EscTypes,Args,TypeAss),
    ( member(_:bot,TypeAss) ->
        fail
    ;
        sort(ASub,ASub_s),
        eterms_abs_sort(TypeAss,ASub1),
        obtains_names(HeadArg,Args,ASub_s,TypeNameAss),
        sort(TypeNameAss,ASub2),
        generate_subs(ASub1,ASub2,Subs),
        obtains_names(Args,HeadArg,Subs,TypeNameAss2),
        sort(TypeNameAss2,TypeNameAss2_s),
        update_names(TypeNameAss2_s,ASub_s),
        eterms_project(not_provided_Sg,Tv,not_provided_HvFv_u,Subs,NASub),
        normal_asub(NASub,NewASub)
    ).

:- export(normal_asub/2). % (shared with etermsvar.pl)
normal_asub([],[]).
normal_asub([X:(Name,Type)|ASub],[X:(Name,NType)|NASub]):-
    normalize_type(Type,NType),
    normal_asub(ASub,NASub).

:- export(update_names/2). % (shared with etermsvar.pl)
update_names([],_):- !.
update_names([Y:Lab|Labels],[Z:(Name_e,_)|ASub]):-
%       member(Z:(Name,_),ASub),
    Y == Z,!,
    get_canonical_name(Name_e,Name),
    retract_type_name(Name,L,C),
    ( member(([],Name0_e),Lab) ->     
        ord_delete(Lab,([],Name0_e),Lab0),
        get_canonical_name(Name0_e,Name0),
        ord_union(L,Lab0,NLab),             
        insert_type_name(Name,NLab,C),
        ( Name0 == Name ->
            true
        ; lab_intersect(Name,Name0)
        )
    ; ord_union(L,Lab,NLab),              
      insert_type_name(Name,NLab,C)
    ),
    update_names(Labels,ASub).
update_names(_,_):-
    error_message("SOMETHING HAS FAILED! See eterms domain.", []).

:- export(generate_subs_exit/4). % (shared with etermsvar.pl)
generate_subs_exit([],_Proj,_TypeNameAss,[]):- !.
generate_subs_exit([X:Type|Types],[Z:(NameP_e,_)|Proj],[Y:Lab|Labels],[X:(Name,Type)|Subs]):-
    X == Y,
    X == Z,!,
    get_canonical_name(NameP_e,Name),       
    retract_type_name(Name,L,C),    
    ( member(([],Name0_e),Lab) ->
        ord_delete(Lab,([],Name0_e),Lab0),
        get_canonical_name(Name0_e,Name0),  
        ord_union(L,Lab0,NLab),             
        insert_type_name(Name,NLab,C),  
        ( Name0 == Name ->
            true
        ; lab_intersect(Name,Name0)
        )
    ; ord_union(L,Lab,NLab),              
      insert_type_name(Name,NLab,C)
    ),
    generate_subs_exit(Types,Proj,Labels,Subs).
generate_subs_exit(_,_,_,_):-
    error_message("SOMETHING HAS FAILED! See eterms domain.").

:- export(generate_subs/3). % (shared with etermsvar.pl)
generate_subs([],[],[]):-!.
generate_subs([X:Type|Types],[Y:Lab|Labels],[X:(Name,Type)|Subs]):-
    X == Y,!,
    sort(Lab,Lab1),
    ( member(([],Name),Lab1) -> 
        ord_delete(Lab1,([],Name),Lab0),
        retract_type_name(Name,L,C),     
        ord_union(Lab0,L,NL),  
        insert_type_name(Name,NL,C)             
    ; new_type_name(Name),
      insert_type_name(Name,Lab1,0)
    ),
    generate_subs(Types,Labels,Subs).
generate_subs(_,_,_):-
    error_message("SOMETHING HAS FAILED! See eterms domain.", []).

:- pred apply(+ASub) : eterms_asub
   # "It unifies the variables in the abstract substitution @var{ASub}
   to his respective values".

apply([X:(_N,Term)|ASub]):-
    X=Term,
    apply(ASub).
apply([]).

%------------------------------------------------------------------%
:- dom_impl(eterms, project/5).
:- export(eterms_project/5).
:- pred eterms_project(+Sg,+Vars,+HvFv_u,+ASub,-Proj)
   : term * list * hvfv_u * eterms_asub * term => eterms_asub(Proj)
   # "@var{Proj} is the result of eliminating from @var{ASub} all
   @var{X}:@var{Value} such that @var{X} is not in @var{Vars}.".

eterms_project(_,_,_,'$bottom',Proj) :- !,
    Proj = '$bottom'.
eterms_project(_Sg,Vars,_HvFv_u,ASub,Proj) :- 
    eterms_project_aux(Vars,ASub,Proj).

eterms_project_aux([],_,Proj):- !,
    Proj = [].
eterms_project_aux(_,[],Proj):- !,
    Proj = [].
eterms_project_aux([Head1|Tail1],[Head2:Type|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    eterms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

eterms_project_aux_(=,_,Tail1,HeadType,Tail2,[HeadType|Proj]) :-
    eterms_project_aux(Tail1,Tail2,Proj).
eterms_project_aux_(>,Head1,Tail1,_,[Head2:Type|Tail2],Proj) :-
    compare(Order,Head1,Head2),
    eterms_project_aux_(Order,Head1,Tail1,Head2:Type,Tail2,Proj).

%------------------------------------------------------------------%
:- dom_impl(eterms, abs_sort/2).
:- export(eterms_abs_sort/2).
:- pred eterms_abs_sort(+ASub,-ASub_s) : eterms_asub(ASub) => eterms_asub(ASub_s)
   # "It sorts the set of @var{X}:@var{Type} in @var{ASub} ontaining
   @var{ASub_s}".

eterms_abs_sort('$bottom','$bottom'):- !.
eterms_abs_sort(ASub,ASub_s):- sort(ASub,ASub_s).

%------------------------------------------------------------------%
:- dom_impl(eterms, extend/5).
:- export(eterms_extend/5).
:- pred eterms_extend(+Sg,+Prime,+Sv,+Call,-Succ)
   : term * eterms_asub * list * eterms_asub * term => eterms_asub(Succ)
   # "If @var{Prime} = '$bottom', @var{Succ} = '$bottom' otherwise,
   @var{Succ} is computed updating the values of @var{Call} with those
   in @var{Prime}".

eterms_extend(_Sg,Prime,_Sv,Call,Succ) :-
    eterms_extend_(Prime,Call,Succ).

eterms_extend_('$bottom',_Call,'$bottom'):- !.
eterms_extend_([],Call,Call):- !.
eterms_extend_(Prime,[],Prime):- !.
eterms_extend_([X:(N_e,T)|Prime],[Y:(N1_e,_T1)|Call],[X:(N,T)|Succ]):-
    X == Y,!,
    get_canonical_name(N_e,N),
    get_canonical_name(N1_e,N1),
    lab_intersect(N,N1), % equival_names
    eterms_extend_(Prime,Call,Succ).
eterms_extend_([X:(N_e,T)|Prime],[Y:(N1,T1)|Call],[X:(N,T)|Succ]):-
    X @< Y,!,
    get_canonical_name(N_e,N),
    eterms_extend_(Prime,[Y:(N1,T1)|Call],Succ).
eterms_extend_([X:(N,T)|Prime],[Y:(N1,T1)|Call],[Y:(N1,T1)|Succ]):-
    X @> Y,!,
    eterms_extend_([X:(N,T)|Prime],Call,Succ).

%------------------------------------------------------------------%
:- dom_impl(eterms, less_or_equal/2).
:- export(eterms_less_or_equal/2).
:- pred eterms_less_or_equal(+ASub0,+ASub1) : eterms_asub * eterms_asub
   # "Succeeds if @var{ASub1} is more general or equal to @var{ASub0}.
   it's assumed the two abstract substitutions are defined on the same
   variables".

eterms_less_or_equal('$bottom',_ASub):- !.
eterms_less_or_equal(ASub1,ASub2):-
    ASub1 == ASub2, !.
eterms_less_or_equal(ASub1,ASub2):-
    eterms_less_or_equal0(ASub1,ASub2).

eterms_less_or_equal0([X:(_N1,T1)|ASub1],[Y:(_N2,T2)|ASub2]):-
    X==Y,
    dz_type_included(T1,T2),
    eterms_less_or_equal0(ASub1,ASub2).
eterms_less_or_equal0([],[]).

%------------------------------------------------------------------%
:- dom_impl(eterms, glb/3).
:- export(eterms_glb/3).
:- pred eterms_glb(+ASub0,+ASub1,-Glb)
   : eterms_asub * eterms_asub * term => eterms_asub(Glb)
   # "@var{Glb} is the great lower bound of @var{ASub0} and @var{ASub1}".

eterms_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
eterms_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
eterms_glb(ASub1,ASub2,ASub3):-
    ASub1 == ASub2, !,
    ASub3 = ASub2.
eterms_glb(ASub1,ASub2,ASub3):-
    eterms_glb0(ASub1,ASub2,ASub33), !,
    eterms_glbnames(ASub1,ASub33,ASub3).
eterms_glb(_ASub1,_ASub2,'$bottom').

eterms_glb0([X:(_N1,T1)|ASub1],[Y:(N2,T2)|ASub2],[X:(N2,T3)|ASub3]):-
    X==Y,
    type_intersection_2(T1,T2,T3),
    ( T3==bot ->
        fail 
    ; eterms_glb0(ASub1,ASub2,ASub3)
    ).
eterms_glb0([],[],[]).

:- export(eterms_glbnames/3). % (shared with etermsvar.pl)
eterms_glbnames([X:(N1_e,_)|ASub1],[X:(N3_e,T3)|ASub33],[X:(N3,T3)|ASub3]):-
    get_canonical_name(N1_e,N1),
    get_canonical_name(N3_e,N3),
    lab_intersect(N3,N1),
    eterms_glbnames(ASub1,ASub33,ASub3),!. % TODO: move cut
eterms_glbnames([],[],[]):- !.

% eterms_glb('$bottom',_ASub,ASub3) :- !, ASub3='$bottom'.
% eterms_glb(_ASub,'$bottom',ASub3) :- !, ASub3='$bottom'.
% eterms_glb(ASub1,ASub2,ASub3):-
%       ASub1 == ASub2, !,
%       ASub3 = ASub2.
% eterms_glb(ASub1,ASub2,ASub3):-
%       eterms_glb0(ASub1,ASub2,ASub3), !.
% eterms_glb(_ASub1,_ASub2,'$bottom').

% eterms_glb0([X:(N1,T1)|ASub1],[Y:(N2,T2)|ASub2],[X:(N3,T3)|ASub3]):-
%       X==Y,
%       type_intersection_2(T1,T2,T3),!,
%       ( 
%           T3==bot -> fail 
%       ;
%           get_type_name(N1,L1),
%           get_type_name(N2,L2),                   % equival_names
%           merge(L1,L2,L3),
% %         ord_intersection(L1,L2,L3),
%           new_type_name(N3),
%           insert_type_name(N3,L3,0),
%       %   add_labels_intersection(T3,N1,N2,N3),
%           eterms_glb0(ASub1,ASub2,ASub3)
%       ).
% eterms_glb0([],[],[]).

% ---------------------------------------------------------------------------

:- dom_impl(eterms, concrete/3).
:- export(eterms_concrete/3).
eterms_concrete(Var,ASub,List):-
    get_type(Var,ASub,Type),
    concrete(Type,List,[],[]).

%------------------------------------------------------------------%
:- dom_impl(eterms, unknown_entry/3).
:- export(eterms_unknown_entry/3).
:- pred eterms_unknown_entry(+Sg,+Qv,-Call)
   : cgoal * list * term => eterms_asub(Call)
   # "Gives the ``top'' value for the variables involved in a literal
   whose definition is not present, and adds this top value to
   Call. In this domain the top value is X:term forall X in the set of
   variables".

eterms_unknown_entry(_Sg,Vars,ASub):-
    variables_are_top_type(Vars,ASub).

:- dom_impl(eterms, empty_entry/3).
:- export(eterms_empty_entry/3).
:- pred eterms_empty_entry(+Sg,+Vars,-Entry)
   : cgoal * list * term => eterms_asub(Entry)
   # "Gives the ""empty"" value in this domain for a given set of
   variables @var{Vars}, resulting in the abstract substitution
   @var{Entry}. I.e., obtains the abstraction of a substitution in
   which all variables @var{Vars} are unbound: free and unaliased. In
   this domain the empty value is giving the variable type to each
   variable".

eterms_empty_entry(_Sg,Vars,ASub):-
    variables_are_variable_type(Vars,ASub).

%------------------------------------------------------------------%
:- dom_impl(eterms, unknown_call/4).
:- export(eterms_unknown_call/4).
:- pred eterms_unknown_call(+Sg,+Vars,+Call,-Succ)
   : cgoal * list * eterms_asub * term => eterms_asub(Succ)
   # "Gives the ``top'' value for the variables involved in a literal
   whose definition is not present, and adds this top value to
   @var{Call}".

eterms_unknown_call(_Sg,Vars,Call,Succ):-
    substitution(Call,CallVars,_),
    ord_subtract(Vars,CallVars,TopVars),
    variables_are_top_type(TopVars,ASub),
    merge(Call,ASub,Succ).
    
substitution([],[],[]).
substitution([X:T|TypeAss],[X|Vars],[T|ListTypes]):-
    substitution(TypeAss,Vars,ListTypes).

:- export(variables_are_top_type/2). % (shared with etermsvar.pl)
:- pred variables_are_top_type(+Fv,-ASub) : list(Fv) => eterms_asub(ASub)
   # "It assigns the value top_type to the variables in @var{Fv} and
   return the abstract substitution @var{ASub} ".

variables_are_top_type([V|Fv],[V:(Name,Type)|ASub]):-
    set_top_type(Type),
    new_type_name(Name),
    insert_type_name(Name,[],0),
    variables_are_top_type(Fv,ASub).
variables_are_top_type([],[]).

%------------------------------------------------------------------%
:- dom_impl(eterms, call_to_success_fact/9).
:- export(eterms_call_to_success_fact/9).
:- pred eterms_call_to_success_fact(+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
   : cgoal * list * cgoal * term * list * eterms_asub * eterms_asub * term * term
   => (eterms_asub(Prime), eterms_asub(Succ))
   # "Specialized version of call_to_entry + exit_to_prime + extend for facts".

eterms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    eterms_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
    eterms_extend(Sg,Prime,Sv,Call,Succ).

%------------------------------------------------------------------------%
% Builtins

:- dom_impl(eterms, special_builtin/5).
:- export(eterms_special_builtin/5).
:- pred eterms_special_builtin(+SgKey,+Sg,+Subgoal,-Type,-Condvars)
   : (atm(SgKey), cgoal(Sg), cgoal(Subgoal))
   # "@var{Type} is a flag indicating what is the abstraction of
   builtin @var{SgKey} and to which variables @var{Condvars} of the
   goal @var{Sg} it affects.".

eterms_special_builtin('!/0',_Sg,_,id,[]) :- !.
eterms_special_builtin('@=</2',_Sg,_,id,[]) :- !.
eterms_special_builtin('@>/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('@>=/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('@</2',_Sg,_,id,[]) :- !.
eterms_special_builtin('\\==/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('==/2',_Sg,_,id,[]) :- !.
eterms_special_builtin('display/1',_Sg,_,id,[]) :- !.
%eterms_special_builtin('var/1',_Sg,_,id,[]) :- !.
    % set_top_type(T),
    % varset(Sg,Condvars).
eterms_special_builtin('free/1',_Sg,_,id,[]) :- !.
%eterms_special_builtin('nonvar/1',_Sg,_,id,[]) :- !.
    % set_top_type(T),
    % varset(Sg,Condvars).
eterms_special_builtin('not_free/1',_Sg,_,id,[]) :- !.
eterms_special_builtin('ground/1',_Sg,_,id,[]) :- !.
    % set_top_type(T),
    % varset(Sg,Condvars).
% eterms_special_builtin('float/1',Sg,type(T),Condvars):-
%       set_float_type(T),
%       varset(Sg,Condvars).
% eterms_special_builtin('number/1',Sg,type(T),Condvars):-
%       set_numeric_type(T),
%       varset(Sg,Condvars).
eterms_special_builtin('fail/0',_Sg,_,bot,[]) :- !.
eterms_special_builtin('true/0',_Sg,_,id,[]) :- !.
eterms_special_builtin('nl/0',_Sg,_,id,[]) :- !.
eterms_special_builtin('repeat/0',_Sg,_,id,[]) :- !.
%
eterms_special_builtin('erase/1',Sg,_,type(T),Condvars):- !,
    set_top_type(T),
    varset(Sg,Condvars).
%
eterms_special_builtin(Key,_Sg,Subgoal,special(KKey),[]):-
    eterms_very_special_builtin(Key,KKey,Subgoal).

eterms_very_special_builtin('=/2','=/2',_).
eterms_very_special_builtin('is/2','is/2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('functor/3','functor/3',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('arg/3','arg/3',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('>/2','>/2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('>=/2','>=/2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('=</2','=</2',_):- current_pp_flag(type_eval,on).
eterms_very_special_builtin('</2','</2',_):- current_pp_flag(type_eval,on).
% TODO: debug, fix
%% GP: WARNING I have commented this clause because
%%     it was producing wrong results for the stream interpreter
%%     case study
%% eterms_very_special_builtin(_,key(KKey,Goal),Goal):-
%%      current_pp_flag(type_eval,on),
%%      predkey_from_sg(Goal,KKey),
%%      assertion_read(Goal,_M,_Status,comp,Body,_VarNames,_S,_LB,_LE),
%%      assertion_body(Goal,_Compat,_Call,_Succ,Comp,_Comm,Body),
%%      member('basic_props:sideff'(Goal,free),Comp),
%%      assertion_read(Goal,_M2,_Status2,comp,Body2,_VarNames2,_S2,_LB2,_LE2),
%%      assertion_body(Goal,_Compat2,_Call2,_Succ2,Comp2,_Comm2,Body2),
%%      member('basic_props:eval'(_),Comp2).

%------------------------------------------------------------------------%
:- dom_impl(eterms, success_builtin/6).
:- export(eterms_success_builtin/6).
:- pred eterms_success_builtin(+Type,+Sv_uns,+Condvars,+HvFv_u,+Call,-Succ)
   # "Depending on @var{Type} it computes the abstraction of a builtin
   affecting variables @var{Condvars} and having variables
   @var{Sv_uns} with call subs. @var{Call}.".

eterms_success_builtin(id,_Sv_uns,_Condvars,_,Call,Call).
eterms_success_builtin(bot,_Sv_uns,_Condvars,_,_Call,'$bottom').
eterms_success_builtin(type(T),_Sv_uns,Condvars,_,Call,Succ):-
    keys_same_value(Condvars,T,Prime),
    eterms_extend(not_provided_Sg,Prime,Condvars,Call,Succ).

:- export(keys_same_value/3).
keys_same_value([K|Ks],V,[K:(Name,V)|ASub]):-
    new_type_name(Name),
    insert_type_name(Name,[],0),
    keys_same_value(Ks,V,ASub).
keys_same_value([],_V,[]).

%------------------------------------------------------------------------%
:- export(eterms_arg_call_to_success/9).

eterms_arg_call_to_success(Sg,Hv,Head,Sv,Call,Proj,Succ,TypeX,TypeY):-
    Head = arg(X,Y,Z),
    eterms_call_to_entry(Sv,Sg,Hv,Head,not_provided,[],Proj,Entry,ExtraInfo), % TODO: add some ClauseKey? (JF)
    get_type(X,Entry,TypeX),
    get_type(Y,Entry,TypeY),
    new_type_name(NX),
    new_type_name(NY),
    new_type_name(NZ),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    insert_type_name(NZ,[],0),
    sort([X:(NX,int),Y:(NY,term),Z:(NZ,term)],Prime1), % postcondition builtin
    ( concrete(TypeX,ValuesX,[],[]) -> 
        ( getargtypes(TypeY,ValuesX,ValuesY,[],_,_) ->
            resetunion,
            set_union(ValuesY,TZ),
% (from evalterms.pl) % TODO: outdated?
%               make_deterministic(ValuesY,Defnew,[]),
%               new_type_symbol(TZ),
%               insert_rule(TZ,Defnew),
            replacetype(Z,Entry,TZ,Prime0),
            eterms_glb(Prime0,Prime1,Prime2)
        ;
            Prime2 = Prime1
        )
    ; 
        Prime2 = Prime1
    ),
    eterms_glb(Prime2,Entry,Prime3),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,Prime3,ExtraInfo,Prime),
    eterms_extend(Sg,Prime,Sv,Call,Succ).

set_union([T],T).
set_union([T1,T2|L],T):-
    type_union(T1,T2,T3),
    set_union([T3|L],T).

:- dom_impl(eterms, call_to_success_builtin/6).
:- export(eterms_call_to_success_builtin/6).
:- pred eterms_call_to_success_builtin(+SgKey,+Sg,+Sv,+Call,+Proj,-Succ)
   : atm * cgoal * list * eterms_asub * eterms_asub * term => eterms_asub(Succ)
   # "Same as above but for each particular builtin.".

eterms_call_to_success_builtin('arg/3',Sg,Sv,Call,Proj,Succ):- !,
    sort([X,Y,Z],Hv),
    eterms_arg_call_to_success(Sg,Hv,arg(X,Y,Z),Sv,Call,Proj,Succ,_,_).
%
eterms_call_to_success_builtin('functor/3',Sg,Sv,Call,Proj,Succ):- !,
    sort([X,Y,Z],Hv),
    Head = functor(X,Y,Z),
    eterms_call_to_entry(Sv,Sg,Hv,Head,not_provided,[],Proj,Entry,ExtraInfo), % TODO: add some ClauseKey?
    get_type(X,Entry,TypeX),
    get_type(Y,Entry,TypeY),
    get_type(Z,Entry,TypeZ),
    ( getfunctors(TypeX,ValuesX) -> true ; true), % (unbound on failure, see getvalue/2)
    ( concrete(TypeY,ValuesY,[],[]) -> true ; true), % (unbound on failure, see getvalue/2)
    ( concrete(TypeZ,ValuesZ,[],[]) -> true ; true), % (unbound on failure, see getvalue/2)
    new_type_name(NX),
    new_type_name(NY),
    new_type_name(NZ),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    insert_type_name(NZ,[],0),
    sort([X:(NX,term),Y:(NY,atm),Z:(NZ,int)],Prime1),
    ( setof(f(X,Y,Z),(getvalue(X,ValuesX),getvalue(Y,ValuesY),getvalue(Z,ValuesZ),functor(X,Y,Z)),ListF) -> 
        split_f(ListF,ListX,ListY,ListZ),
        new_type_symbol(TX),
        new_type_symbol(TY),
        new_type_symbol(TZ),
        sort(ListX,DefX1),
        sort(ListY,DefY1),
        sort(ListZ,DefZ1),
        varset(DefX1,VarsX),
        type_escape_term_list(DefX1,DefX),
        type_escape_term_list(DefY1,DefY),
        type_escape_term_list(DefZ1,DefZ),
        unifytoterm(VarsX),
        insert_rule(TX,DefX),
        insert_rule(TY,DefY),
        insert_rule(TZ,DefZ),
        sort([X:(NX,TX),Y:(NY,TY),Z:(NZ,TZ)],Prime0),
        eterms_glb(Prime0,Prime1,Prime2)
    ;
        Prime2 = Prime1
    ),
    eterms_glb(Prime2,Entry,Prime3),
    eterms_exit_to_prime(Sg,Hv,Head,Sv,Prime3,ExtraInfo,Prime),
    eterms_extend(Sg,Prime,Sv,Call,Succ).
%
eterms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):- !,
    eterms_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?
%
eterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    ( Key = '>/2' ; Key = '>=/2' ; Key = '=</2' ; Key = '</2' ), !,
    TY = 'arithmetic:arithexpression',
    TX = 'arithmetic:arithexpression',
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv),
    functor(Sg,F,2),
    functor(G,F,2),
    arg(1,G,X),
    arg(2,G,Y),
    eterms_exit_to_prime(Sg,Bv,G,Sv,Exit,(no,Proj),Prime1),
    eterms_glb(Proj,Prime1,Prime2),
    ( Prime2 \== '$bottom' ->
        abs_eval_arithcomp(Sg,Sv,Prime2,Prime)
    ;
        Prime = '$bottom'
    ),
    eterms_extend(Sg,Prime,Sv,Call,Succ).
%
eterms_call_to_success_builtin('is/2',(X is Y),Sv,Call,Proj,Succ):- !,
    ( % precondition_builtin('is/2',(X is Y)) ->
      ( var(X) ; number(X) ) -> % (it was precondition_builtin)
        TY = 'arithmetic:arithexpression',
        new_type_name(NY),
        insert_type_name(NY,[],0),
        varset(Y,Svy),
        eterms_project(not_provided_Sg,Svy,not_provided_HvFv_u,Proj,Projy),
        eterms_exit_to_prime(p(Y),[Y1],p(Y1),Svy,[Y1:(NY,TY)],(no,Projy),Primey),
        % TODO: etermsvar.pl use normalize_names/2 here, why not here?
        eterms_glb(Projy,Primey,Primey2),
        ( Primey2 \== '$bottom' ->
            abs_eval_arith(Y,Primey2,Type),         
            TX = Type,
            new_type_name(NX),
            get_list_names_is(Projy,NameSelec),
            insert_type_name(NX,NameSelec,0),
            varset(X,Svx),
            eterms_project(not_provided_Sg,Svx,not_provided_HvFv_u,Proj,Projx),
            eterms_exit_to_prime(p(X),[X1],p(X1),Svx,[X1:(NX,TX)],(no,Projx),Primex),
            eterms_glb(Projx,Primex,Primex2),
            ( Primex2 \== '$bottom' ->
                append(Primex2,Primey2,Prime_u),
                sort(Prime_u,Prime),
                eterms_extend(not_provided_Sg,Prime,Sv,Call,Succ)
            ;
                Succ = '$bottom'
            )
        ;
            Succ = '$bottom'
        )
    ;
        Succ = '$bottom'
    ).
%
eterms_call_to_success_builtin(key(Key,SubGoal),Sg,Sv,Call,Proj,Succ):- !,
    ( getvalues_comp_cond(Sv,Proj,Vals)->
        ( generateSucc0_cond(Vals,SubGoal,Vals,Proj,Prime)-> true
        ; Prime = '$bottom'
        )
    ; apply_trusted0(Proj,Key,SubGoal,Sv,eterms,_,Prime)
    ),
    eterms_extend(Sg,Prime,Sv,Call,Succ).

% NOTE: see evalterms.pl for previous code
%
% eterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
%       (
%           precondition_builtin(Key,Sg) ->
%           postcondition_builtin(Key,Bg,Bv,Exit),
%           eterms_exit_to_prime(Sg,Bv,Bg,Sv,Exit,(no,Proj),Prime1),
%           eterms_glb(Proj,Prime1,Prime),
%           eterms_extend(Sg,Prime,Sv,Call,Succ)
%       ;
%           Succ = '$bottom'
%       ).

%------------------------------------------------------------------------%

:- use_module(ciaopp(plai/domains), [asub_to_info/5]).

:- dom_impl(eterms, obtain_info/4).
:- export(eterms_obtain_info/4).
eterms_obtain_info(_Prop,Vars,ASub,Info) :- asub_to_info(eterms,ASub,Vars,Info,_CompProps).

%------------------------------------------------------------------------%
% User interface

:- dom_impl(eterms, input_user_interface/5).
:- export(eterms_input_user_interface/5).
:- pred eterms_input_user_interface(?InputUser,+Qv,-ASub,+Sg,+MaybeCallASub)
   # "Obtains the abstract substitution @var{ASub} from user supplied
   information.".

eterms_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
    obtain_ASub_user(InputUser,ASub0),
    sort(ASub0,ASub_s),
    reduce_same_var(ASub_s,ASub1),
    substitution(ASub1,Vars,_),
    ord_subtract(Qv,Vars,TopV),
    variables_are_top_type(TopV,ASub2),
    sort(ASub2,ASub3),
    merge(ASub1,ASub3,ASub).

obtain_ASub_user([],[]):- !.
obtain_ASub_user([User|InputUser],[X:(Name,T)|ASub]):-
    functor(User,T,_),
    arg(1,User,X), % note: expected arity 1, parametric types already renamed
    new_type_name(Name),
    insert_type_name(Name,[],0),
    obtain_ASub_user(InputUser,ASub).

reduce_same_var([X:(Name,T)|ASub],NewASub):-
    reduce_same_var_(ASub,X,Name,T,NewASub).
reduce_same_var([],[]).

reduce_same_var_([Y:(NameY,TY)|ASub],X,NameX,TX,NewASub):-
    reduce_same_var__(Y,NameY,TY,X,NameX,TX,ASub,NewASub).
reduce_same_var_([],X,Name,T,[X:(Name,T)]).

reduce_same_var__(Y,_NameY,TY,X,NameX,TX,ASub,NewASub):-
    X == Y, !,
    type_intersection_2(TY,TX,T),
    reduce_same_var_(ASub,X,NameX,T,NewASub).
reduce_same_var__(Y,NameY,TY,X,NameX,TX,ASub,[X:(NameX,TX)|NewASub]):-
    reduce_same_var_(ASub,Y,NameY,TY,NewASub).

% inverse_terms_asub_to_native([X:T|ASub],[Type|OutputUser]):-
%       Type=..[T,X],
%       inverse_terms_asub_to_native(ASub,OutputUser).
% inverse_terms_asub_to_native([],[]).

:- dom_impl(eterms, input_interface/4).
:- export(eterms_input_interface/4).
eterms_input_interface(P,Kind,Acc0,Acc1) :-
    terms_input_interface(P,Kind,Acc0,Acc1).

%------------------------------------------------------------------------%
:- dom_impl(eterms, asub_to_native/5).
:- export(eterms_asub_to_native/5).
:- pred eterms_asub_to_native(+ASub,+Qv,+OutFlag,-OutputUser,-Comps)
   : (eterms_asub(ASub), list(Qv))
   # "Transforms abstract substitution @var{ASub} to user friendly
   format.".

eterms_asub_to_native(ASub,_Qv,OutFlag,OutputUser,[]):-
    eterms_asub_to_internal(ASub,OutputUser1),
    terms_internal_to_native(OutputUser1,OutFlag,OutputUser).

eterms_asub_to_internal([X:(_N,T)|ASub],[Type|OutputUser]):-
    revert_type_internal(T,X,Type),
    eterms_asub_to_internal(ASub,OutputUser).
eterms_asub_to_internal([],[]).

%------------------------------------------------------------------------%
:- export(eterms_output_interface/2).
:- pred eterms_output_interface(+ASub,-Output)
   : eterms_asub(ASub)
   # "Transforms abstract substitution @var{ASub} to a more readable
   but still close to internal format.".

eterms_output_interface(ASub,ASub).

%------------------------------------------------------------------------%

:- dom_impl(eterms, collect_auxinfo_asub/3).
:- export(eterms_collect_auxinfo_asub/3).
eterms_collect_auxinfo_asub([],Types,Types).
eterms_collect_auxinfo_asub([_:(_,Type)|Abs],Types0,Types):-
    insert(Types0,Type,Types1),
    eterms_collect_auxinfo_asub(Abs,Types1,Types).

:- dom_impl(eterms, rename_auxinfo_asub/3).
:- export(eterms_rename_auxinfo_asub/3).
eterms_rename_auxinfo_asub([],_,[]).
eterms_rename_auxinfo_asub([C|Call],Dict,[RenC|RenCall]):-
    Dict = (Types,_Names),
    C = Var:(_Name,Type),
    RenC = Var:(RenName,RenType),
    get_value_(Types,Type,RenType),
%jcf-begin
%       get_value_(Names,Name,RenName),
    new_type_name(RenName),         % taken from obtain_ASub_user/2.
    insert_type_name(RenName,[],0), % taken from obtain_ASub_user/2.
%jcf-end
    eterms_rename_auxinfo_asub(Call,Dict,RenCall).

get_value_(Rens,Type,RenType):-
    assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%

:- dom_impl(eterms, identical_abstract/2).
:- export(eterms_identical_abstract/2).
eterms_identical_abstract(ASub1,ASub2):- ASub1==ASub2, !.
eterms_identical_abstract(ASub1,ASub2):-
    eterms_identical_abstract0(ASub1,ASub2).

eterms_identical_abstract0([X:(_Name0,Type0)|ASub0],[Y:(_Name1,Type1)|ASub1]):-
    X==Y,
    dz_equivalent_types(Type0,Type1),
    eterms_identical_abstract0(ASub0,ASub1).
eterms_identical_abstract0([],[]).

%-------------------- evalterms

:- export(getargtypes/6).
getargtypes(Type,Args,ValuesX,Rest,Selectors,RestSel):-
    maybe_get_type_definition(Type,Def),
    getargtypes_(Def,Args,ValuesX,Rest,Selectors,RestSel).

getargtypes_([],_,Rest,Rest,RestSel,RestSel).
getargtypes_([Type|Def],Args,ValuesX,Rest,Selectors,RestSel):-
    compound_pure_type_term(Type, Term, Name, Arity),
    !,
    getargtypes1(Args,Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel1),
    getargtypes_(Def,Args,Rest1,Rest,RestSel1,RestSel).

getargtypes1([],_Arity,_Term,Rest,Rest,_Name,RestSel,RestSel).
getargtypes1([Arg|Args],Arity,Term,[Val|ValuesX],Rest1,Name,[[Name/Arg]|Selectors],RestSel):-
    Arg =< Arity,
    Arg > 0,
    !,
    arg(Arg,Term,Val),
    getargtypes1(Args,Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel).
getargtypes1([_|Args],Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel):-
    getargtypes1(Args,Arity,Term,ValuesX,Rest1,Name,Selectors,RestSel).

:- export(replacetype/4). % (shared with etermsvar.pl)
replacetype(Z,[X:(N,_T)|Entry],TZ,[X:(N,TZ)|Entry]):-
    Z == X,!.
replacetype(Z,[X:(N,T)|Entry],TZ,[X:(N,T)|Prime]):-
    replacetype(Z,Entry,TZ,Prime).

:- export(getfunctors/2). % (shared with etermsvar.pl)
getfunctors(Type,ValuesX):-
    maybe_get_type_definition(Type,Def),
    getfunctors_(Def,ValuesX).

getfunctors_([],[]).
getfunctors_([Type|Def],[Val|ValuesX]):-
    compound_pure_type_term(Type, _Term, Name, Arity),
    !,
    functor(Val,Name,Arity),
    getfunctors_(Def,ValuesX).

:- export(split_f/4). % (shared with etermsvar.pl)
split_f([],[],[],[]).
split_f([f(X,Y,Z)|ListF],[X|ListX],[Y|ListY],[Z|ListZ]):-
    split_f(ListF,ListX,ListY,ListZ).

:- export(getvalue/2). % (shared with etermsvar.pl)
getvalue(_X,Vals):- var(Vals),!.
getvalue(X,Vals):- member(X,Vals).

:- export(unifytoterm/1). % (shared with etermsvar.pl)
unifytoterm([]).
unifytoterm([V|VarsX]):-
    V = term,
    unifytoterm(VarsX).

:- export(abs_eval_arithcomp/4). % (shared with etermsvar.pl)
abs_eval_arithcomp(X,Vars,Prime,Succ):-
    ( getvalues_comp(Vars,Prime,Vals) ->
        ( generateSucc0(Vals,X,Vals,Prime,Succ) ->
            true
        ; Succ = '$bottom'
        )
    ; Succ = Prime
    ).

getvalues_comp([],_Prime,[]):- !.
getvalues_comp([V|Vars],Prime,[Val|Vals]):-
    getvaluescomp(V,Prime,Val),
    getvalues_comp(Vars,Prime,Vals).

getvaluescomp(X,Prime,X/Vals):-
    member(Y:(_,Type),Prime),
    X == Y, % TODO: cut if X is unique in Prime
    concrete(Type,Vals,[],[]).

generateSucc0([],Goal,_VALS,Prime,Succ):- 
    ( call(Goal) ->
        Succ = Prime
    ; Succ = '$bottom'
    ).
generateSucc0(Vals,X,Vals,Prime,Succ):-
    generateSucc(Vals,X,Vals,Prime,Succ).

:- export(generateSucc0_cond/5). % (shared with etermsvar.pl)
generateSucc0_cond([],Sg,_Vals,Proj,Prime):-
    ( can_be_evaluated(Sg),call(Sg) ->
        Prime = Proj
    ; Prime = '$bottom'
    ).
generateSucc0_cond(Vals,Sg,Vals,Proj,Prime):-
    generateSucc_cond(Vals,Sg,Vals,Proj,Prime).

generateSucc([],_Goal,_VALS,_Prime,[]). 
generateSucc([X/Val|Vals],Goal,VALS,Prime,[X:(N,T)|Succ]):-
    setof(Z,Goal^(member(Z,Val),satisfy(Goal,X,Z,VALS)),Tconc),!,
    member(Y:(Name,_),Prime),
    X == Y, % TODO: cut if X is unique in Prime
    N_e = Name,
    get_canonical_name(N_e,N),
    new_type_symbol(T),     
    insert_rule(T,Tconc),
    generateSucc(Vals,Goal,VALS,Prime,Succ).

generateSucc_cond([],_Goal,_VALS,_Prime,[]). 
generateSucc_cond([X/Val|Vals],Goal,VALS,Prime,[X:(N,T)|Succ]):-
    setof(Z,Goal^(member(Z,Val),satisfy_cond(Goal,X,Z,VALS)),Tconc),!,
    member(Y:(Name,_),Prime),
    X == Y, % TODO: cut if X is unique in Prime
    N_e = Name,
    get_canonical_name(N_e,N),
    new_type_symbol(T),     
    type_escape_term_list(Tconc,TDef),
    insert_rule(T,TDef),
    generateSucc_cond(Vals,Goal,VALS,Prime,Succ).

satisfy(G,X,Z,VALS):-
    X = Z,
    maplist(apply_,VALS),
    call(G).

satisfy_cond(G,X,Z,VALS):-
    X = Z,
    maplist(apply_,VALS),
    can_be_evaluated(G),    
    '$meta_call'(G).
%       call(G).

:- export(abs_eval_arith/3). % (shared with etermsvar.pl)
abs_eval_arith(X,Proj,ResultType):-
    varset(X,Vars),
    getvalues_(Vars,Proj,Vals,Concr),
    setof(Z,X^calc(X,Z,Vals),T3),
    new_type_symbol(Type),
    insert_rule(Type,T3),
    ( var(Concr) ->
        ResultType = Type 
    ; get_less_numeric_type(Type,ResultType)
    ).

getvalues_([],_,[],_):- !.
getvalues_([V|Vars],Proj,[Val|Vals],Concr):- 
    getvalues(V,Proj,Val,Concr),
    getvalues_(Vars,Proj,Vals,Concr).

getvalues(X,Proj,X/Vals,Concr):-
    member(Y:(_,Type),Proj),
    X == Y, % TODO: cut if X is unique in Proj
    (
%           member(Type,[int,flt,num,arithexpression]) ->
        concrete(Type,Values,[],[]) -> 
%           get_type_definition(Type,Vals)
        Vals = Values
    ;
        Concr = no,
        choose_one(Type,Vals)
    ).

% TODO: why? document
choose_one('basic_props:int',[3]) :- !.
choose_one('basic_props:flt',[3.0]) :- !.
choose_one('basic_props:num',[3.0,3]) :- !.
choose_one('arithmetic:arithexpression',[3.0,3]) :- !.
choose_one(int,[3]) :- !.
choose_one(flt,[3.0]) :- !.
choose_one(num,[3.0,3]) :- !.
choose_one(arithexpression,[3.0,3]) :- !.
choose_one(_,[3.0,3]).

calc(X,Z,Vals):-
    maplist(apply_,Vals),
    Z is X.

apply_(X/Y):- member(X,Y). % TODO: cuts needed?

:- export(getvalues_comp_cond/3). % (shared with etermsvar.pl)
getvalues_comp_cond([],_Prime,[]):- !.
getvalues_comp_cond([V|Vars],Prime,[Val|Vals]):-
    getvalues_comp_cond1(V,Prime,Val),
    getvalues_comp_cond(Vars,Prime,Vals).

getvalues_comp_cond1(X,Prime,X/Vals):-
    member(Y:(_,Type),Prime),
    X == Y, % TODO: cut if X is unique in Prime
    ( Type = term ->
        Vals = [X]
    ; concrete(Type,Vals,[],[])
    ).

:- export(get_list_names_is/2). % (shared with etermsvar.pl)
get_list_names_is([],[]).
get_list_names_is([_:(Name,_)|Proj],[(['$is'],Name)|List]):-
    get_list_names_is(Proj,List).

%-------------------- svterms

:- export(determinate_sel/3).
determinate_sel(Var,Sel,Types):-
    get_type(Var,Types,Type),
    existpos(Type,Sel,[]),
    !.

:- export(replaceintype/5).
replaceintype((NameX,Tx),Sx,(NameY,Ty),Sy,(NameX,Txn)):-
    reverse(Sx,RSx),
    reverse(Sy,RSy),
    gettypeinpos(Tx,RSx,TTx),
    gettypeinpos(Ty,RSy,TTy),
    ( dz_equivalent_types(TTx,TTy) ->
        Txn = Tx
    ; replacetypeinpos(Tx,RSx,TTy,Txn),
      addnamesinpos(NameX,Sx,NameY,Sy)
    ), !.
replaceintype(_,_,_,_,_):-
    error_message("SOMETHING WAS WRONG With same value selectors", []).

existpos(_Type,[],_Seen):-!.
existpos(T,_,Seen):-
    member(T,Seen),!,
    fail.
existpos(T,[F/A|S],Seen):-
%       get_type_definition(T,Def),
    maybe_get_type_definition(T,Def),
    gettpos(Def,F,A,NT),
    !,
    existpos(NT,S,[T|Seen]).

gettypeinpos(T,[],T) :- !.
gettypeinpos(T,[F/A|S],ST):-
%       get_type_definition(T,Def),
    maybe_get_type_definition(T,Def),
    gettpos(Def,F,A,NT),
    !,
    gettypeinpos(NT,S,ST).

gettpos([],_F,_A,_NT):- !,fail.
gettpos([C|_Def],F,A,NT):-
    compound_pure_type_term(C,Term,F,Arity),
    A =< Arity,!,
    arg(A,Term,NT).
gettpos([_|Def],F,A,NT):-
    gettpos(Def,F,A,NT).

replacetypeinpos(_Tx,[],TTy,TTy) :- !.
replacetypeinpos(Tx,[F/A|S],TTy,Txn):-
    get_type_definition(Tx,Def), % TODO: why not maybe_get_type_definition/2? !!!
    replacetypeinposdef(Def,F,A,S,TTy,NDef),
    new_type_symbol(Txn),
    insert_rule(Txn,NDef), !.
replacetypeinpos(_,_,_,_):-
    error_message("SOMETHING WAS WRONG With same value selectors", []).

replacetypeinposdef([],_F,_A,_S,_TTy,_NDef):- !,fail.
replacetypeinposdef([C|Def],F,A,S,TTy,[NC|Def]):- 
    compound_pure_type_term(C,Term,F,Arity),
    A =< Arity,!,
    arg(A,Term,T),
    replacetypeinpos(T,S,TTy,NT),
    functor(NTerm,F,Arity),
    arg(A,NTerm,NT),
    copyargsbutA(Arity,A,Term,NTerm),
    construct_compound_pure_type_term(NTerm,NC).
replacetypeinposdef([C|Def],F,A,S,TTy,[C|NDef]):- 
    replacetypeinposdef(Def,F,A,S,TTy,NDef).

copyargsbutA(0,_A,_Term,_NTerm) :- !.
copyargsbutA(Arity,A,Term,NTerm):-
    ( Arity \== A ->
        arg(Arity,Term,Arg),
        arg(Arity,NTerm,Arg)
    ; true
    ),
    NArity is Arity - 1,
    copyargsbutA(NArity,A,Term,NTerm).
    
addnamesinpos(NameX,Sx,NameY,Sy):-
    retract_type_name_(NameX,EQNameX,Lx,C),
    ( EQNameX \== NameY ->
        get_type_name(NameY,Ly)
    ; Ly = Lx
    ),
    deleteposdeeperSx(Lx,Sx,Lx2),
    addposfromY(Ly,Lx2,Sy,Sx,Lx3),
    insert_type_name(EQNameX,Lx3,C),!.      

% PP: Take a canonical name if NameX has been already retracted
retract_type_name_(NameX,NameX,Lx,C) :-
    retract_type_name(NameX,Lx,C),!.
retract_type_name_(NameX,EQName,Lx,C) :-
    get_equiv_name(NameX,EQName),
    retract_type_name(EQName,Lx,C).

deleteposdeeperSx([],_Sx,[]).
deleteposdeeperSx([(S,_N)|Lx],Sx,Lx2):-
    dlist([_|_],S,Sx),!,
    deleteposdeeperSx(Lx,Sx,Lx2).
deleteposdeeperSx([(S,N)|Lx],Sx,[(S,N)|Lx2]):-
    deleteposdeeperSx(Lx,Sx,Lx2).
    
addposfromY([],Lx2,_Sy,_Sx,Lx2).
addposfromY([(S,N)|Ly],Lx2,Sy,Sx,[(NS,N)|Lx3]):-
    dlist(NNS,S,Sy),!,
    dlist(NNS,NS,Sx),
    addposfromY(Ly,Lx2,Sy,Sx,Lx3).
addposfromY([_|Ly],Lx2,Sy,Sx,Lx3):-
    addposfromY(Ly,Lx2,Sy,Sx,Lx3).

%-------------------- types operations

:- dom_impl(eterms, multi_part_conc/3).
:- export(eterms_multi_part_conc/3).
eterms_multi_part_conc(A,ASub,List):- 
    varset(A,Vars_s),
    varsbag(A,AVars,[]),
    get_all_paths(Vars_s,ASub,Paths),
    cross_product(Paths,Llist),
    maplist(splitlist,Llist,R),
    maplist(build_concr(A,Vars_s,AVars),R,List).

build_concr(A,Vars_s,AVars,(LT,S),(NA,S)):-
    copy_term(A,NA),
    varsbag(NA,NAVars,[]),
    assign_terms(Vars_s,LT,AVars,NAVars).

assign_terms([],[],_,_).
assign_terms([V|Vars_s],[T|LT],AVars,NAVars):-
    nth(N,AVars,X),
    X==V,
    nth(N,NAVars,NX),
    NX = T,
    assign_terms(Vars_s,LT,AVars,NAVars).

splitlist(Llist,(T,S)):-
    splitlist_(Llist,T,S).

splitlist_([],[],[]).
splitlist_([(T,S)|List],[T|Terms],Subs):-
    append(S,TailS,Subs),
    splitlist_(List,Terms,TailS).

get_all_paths([],_,[]).
get_all_paths([V|Vars_s],ASub,[VPaths|AllPaths]):-
    get_type(V,ASub,Type),
    partial_concrete(Type,VPaths,[],[]),
    get_all_paths(Vars_s,ASub,AllPaths).

%-----------------------------------------------------------

:- dom_impl(eterms, part_conc/4).
:- export(eterms_part_conc/4).
eterms_part_conc(A,ASub,NA,NASub):- 
    eterms_part_conc_(A,ASub,NA,NASub,ASub).
 
eterms_part_conc_(A,ASub,NA,NASub,NASubT):- 
    var(A),!,
    get_type(A,ASub,Type),
    get_det_conc(Type,A,NA,NASub,NASubT).
eterms_part_conc_(A,ASub,NA,NASub,NASubT):-     
    functor(A,F,Arity),
    functor(NA,F,Arity),
    eterms_part_conc_arg(Arity,A,NA,ASub,NASub,NASubT).

eterms_part_conc_arg(0,_A,_NA,_,ASub,ASub) :- !.
eterms_part_conc_arg(Arity,A,NA,ASub,NASub,NASubT):-
    arg(Arity,A,Arg1),
    Arity1 is Arity - 1,
    eterms_part_conc_(Arg1,ASub,NAArg,NASub,NASub2),        
    arg(Arity,NA,NAArg),    
    eterms_part_conc_arg(Arity1,A,NA,ASub,NASub2,NASubT).

get_det_conc_args(0,_Term,_NA,ASub,ASub) :- !.
get_det_conc_args(Arity,Term,NA,NASub,ASub):-
    arg(Arity,Term,Arg1),
    get_det_conc(Arg1,_,A,NASub,NASub2),
    arg(Arity,NA,A),
    Arity1 is Arity - 1,
    get_det_conc_args(Arity1,Term,NA,NASub2,ASub).

get_det_conc(Type,A,A,[A:(N,Type)|ASub],ASub):-
    native_type_symbol(Type),!,
    new_type_name(N),
    insert_type_name(N,[],0).
get_det_conc(Type,A,NA,NASub,ASub):-
    maybe_get_type_definition(Type,[SingletonDef]),!,
    get_det_conc_(SingletonDef,A,NA,NASub,ASub).    
get_det_conc(Type,A,A,[A:(N,Type)|ASub],ASub):-
    new_type_name(N),
    insert_type_name(N,[],0).
 
get_det_conc_(SingletonDef,_A,NA,NASub,ASub):-
    compound_pure_type_term(SingletonDef,Term,F,Arity),!,
    functor(NA,F,Arity),
    get_det_conc_args(Arity,Term,NA,NASub,ASub).
get_det_conc_(^(Term),_,Term,ASub,ASub) :- !.
get_det_conc_(Term,_,Term,ASub,ASub):- number(Term),!.
get_det_conc_(Term,_,Term,ASub,ASub):- Term = [_|_],!.
get_det_conc_(Term,_,Term,ASub,ASub):- Term = [],!.
get_det_conc_(SingletonDef,A,NA,NASub,ASub):- !,
    get_det_conc(SingletonDef,A,NA,NASub,ASub).     

% ---------------------------------------------------------------------------

:- export(obtains_names/4). % (internal?)
obtains_names(Types,Args,ASub0,TypeNameAss):-
    gen_list(Types,Args,ASub0,Out),
    join_assign(Out,TypeNameAss1),
    get_all_canonical(TypeNameAss1,TypeNameAss).

gen_list([],[],_,[]).
gen_list([TypeArg|Types],[Arg|Args],ASub0,[Assign|Out]):-
    varset(Arg,Vars),
    get_positions_of_vars(Vars,Arg,Pos),
    get_names_of_positions(Pos,TypeArg,ASub0,Assign1),
    sort(Assign1,Assign),
    gen_list(Types,Args,ASub0,Out).

get_positions_of_vars([],_,[]).
get_positions_of_vars([X|Vars],Arg,[X:P|Pos]):-
    get_pos_var(X,Arg,P,[],[]),
    get_positions_of_vars(Vars,Arg,Pos).

get_pos_var(X,Term,[Sel|Tail],Tail,Sel):- X == Term,!.
get_pos_var(X,Term,P,Tail,Sel):-
    nonvar(Term),
    functor(Term,F,A),!,
    get_pos_var_arg(A,X,Term,F,Sel,P,Tail).
get_pos_var(_X,_Term,P,P,_).

get_pos_var_arg(0,_X,_Term,_F,_Sel,P,P) :- !.
get_pos_var_arg(A,X,Term,F,Sel,P,Tail):-
    arg(A,Term,Arg),
    get_pos_var(X,Arg,P,P1,[F/A|Sel]),
    A1 is A - 1,
    get_pos_var_arg(A1,X,Term,F,Sel,P1,Tail).

get_names_of_positions([],_,_,[]).
get_names_of_positions([X:P|Pos],TypeArg,ASub0,[X:Lab|Assign1]):-
    get_names_of_positions1(P,TypeArg,ASub0,Lab),
    get_names_of_positions(Pos,TypeArg,ASub0,Assign1).

get_names_of_positions1([],_,_,[]).
get_names_of_positions1([Pos],TypeArg,ASub0,Lab):- !,
    get_names_of_one_pos(Pos,TypeArg,ASub0,Lab1),
    sort(Lab1,Lab).
get_names_of_positions1([Pos|P],TypeArg,ASub0,Lab):-
    get_names_of_one_pos(Pos,TypeArg,ASub0,Lab1),
    sort(Lab1,Lab1_s),
    get_names_of_positions1(P,TypeArg,ASub0,Lab2),
%       ord_intersection(Lab1_s,Lab2,Lab).      
    ord_union(Lab1_s,Lab2,Lab).             

get_names_of_one_pos([],TypeArg,ASub0,Lab):-
    !,
    get_names_of_subterm(TypeArg,[],ASub0,Lab,[]).
get_names_of_one_pos(P,TypeArg,ASub0,Lab):- 
    var(TypeArg),!,
    member(Y:(Name_e,_),ASub0),
    get_canonical_name(Name_e,Name),
    Y == TypeArg, % TODO: cut if TypeArg is unique in ASub0
    get_type_name(Name,L),                    % equival_names
    % findall(([A|B],N),( 
    %                     member((S,N),L),
    %                     dlist([A|B],S,P)
    %                 ),Lab,[]).
    findall((A,N),( 
        member((S,N),L),
        dlist(A,S,P)
    ),Lab,[]).
get_names_of_one_pos(P,TypeArg,ASub0,Lab):-
    dlist(NP,P,[F/A]),
    functor(TypeArg,F,_),   
    arg(A,TypeArg,Arg),
    get_names_of_one_pos(NP,Arg,ASub0,Lab).

get_names_of_subterm(TypeArg,Sel,ASub0,Lab,Tail):-
    var(TypeArg),!,
    member(Y:(Name_e,_),ASub0),         % equival_names
    get_canonical_name(Name_e,Name),
    TypeArg == Y, % TODO: cut if TypeArg is unique in ASub0
    ( Sel == [] ->
        %           get_type_name(Name,L),
        %           dlist(L,Lab1,Tail),     % changed
        Lab = [([],Name)|Tail]  % changed
    ; Lab = [(Sel,Name)|Tail]
    ).
% get_names_of_subterm(TypeArg,Sel,_ASub0,Lab,Tail):-
%       atom(TypeArg),!,
%       ( 
%           exist_name(TypeArg) ->
%           get_canonical_name(TypeArg,NewName)
%       ;
%           insert_type_name(TypeArg,[],0),
%           NewName = TypeArg
%       ),
%       Lab = [(Sel,NewName)|Tail].
get_names_of_subterm(TypeArg,Sel,ASub0,Lab,Tail):-
    functor(TypeArg,F,A),
    get_names_of_subterm_arg(A,TypeArg,F,Sel,ASub0,Lab,Tail).

% exist_name(TypeArg):-
%       get_type_name(TypeArg,_).
% exist_name(TypeArg):-
%       get_equiv_name(TypeArg,_).
        
get_names_of_subterm_arg(0,_,_,_,_,L,L) :- !.
get_names_of_subterm_arg(N,Term,F,Sel,ASub0,Lab,Tail):-
    arg(N,Term,Arg),
    get_names_of_subterm(Arg,[F/N|Sel],ASub0,Lab,Tail1),
    N1 is N - 1,
    get_names_of_subterm_arg(N1,Term,F,Sel,ASub0,Tail1,Tail).

get_all_canonical([],[]).
get_all_canonical([X:Lab1|TypeNameAss1],[X:Lab|TypeNameAss]):-
    get_all_canonical2(Lab1,Lab),
    get_all_canonical(TypeNameAss1,TypeNameAss).

get_all_canonical2([],[]).
get_all_canonical2([(S,N)|Lab1],[(S,N1)|Lab]):-
    get_canonical_name(N,N1),       
    get_all_canonical2(Lab1,Lab).

join_assign([],[]).
join_assign([AssArg],AssArg2):- !,
    join_one(AssArg,AssArg,AssArg2).
join_assign([AssArg1,AssArg2|Out],TypeNameAss):-
    join_one(AssArg1,AssArg2,Assign),
    join_assign([Assign|Out],TypeNameAss).

join_one([],A,A) :- !.
join_one(A,[],A) :- !.
join_one([X:Lab1|A1],[Y:Lab2|A2],[Z:Lab|A]):-
    compare(Order,X,Y),
    join_one0([X:Lab1|A1],[Y:Lab2|A2],Order,Z,Lab,A).

join_one0([X:Lab1|A1],[_Y:Lab2|A2],=,X,Lab,A):- !,
%       ord_intersection(Lab1,Lab2,Lab),                
    ord_union(Lab1,Lab2,Lab_s),
    lab_intersection(Lab_s,Lab),
    join_one(A1,A2,A).
join_one0([X:Lab1|A1],[Y:Lab2|A2],<,X,Lab1,A):- !,
    join_one(A1,[Y:Lab2|A2],A).
join_one0([X:Lab1|A1],[Y:Lab2|A2],>,Y,Lab2,A):-
    join_one([X:Lab1|A1],A2,A).

lab_intersection([],[]).
lab_intersection([X],[X]) :- !.
lab_intersection([(S1,N1_e),(S2,N2_e)|Lab],LabO):-
    S1 == S2,!,
    get_canonical_name(N1_e,N1),
    get_canonical_name(N2_e,N2),
    lab_intersect(N1,N2),
    lab_intersection([(S1,N1)|Lab],LabO).
lab_intersection([(S1,N1),(S2,N2)|Lab],[(S1,N1)|LabO]):-
    lab_intersection([(S2,N2)|Lab],LabO).

