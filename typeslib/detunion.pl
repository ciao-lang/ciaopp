%---------------------------------------------------------------------%  
%---------------------------------------------------------------------%  
%-----------------------Deterministic Union --------------------------%  
%---------------------------------------------------------------------%  
%---------------------------------------------------------------------%  

:- use_module(library(sets), [merge/3]).

:- data uniontriple/3.

:- export(resetunion/0).
resetunion :-
    retractall_fact(uniontriple(_,_,_)).

:- export(type_union/3).
:- pred type_union(+Type1,+Type2,-Type3): pure_type_term * pure_type_term * pure_type_term #
"
@var{Type3} is the union of @var{Type1} and @var{Type2} and is defined
by a deterministic type rule.
 This is done as follows: 
@begin{itemize} 
@item if @var{Type1} is included in @var{Type2} the union is @var{Type2}.
@item if @var{Type2} is included in @var{Type1} the union is @var{Type1}.
@item Otherwise, if (Type1,Type2,Type3) in @var{Seen} (i.e. the union
of Type1 and Type2 was previously evaluated) the union is
@var{Type3}. Otherwise, it will create a new type simbol Type3, merge
the definitions of Type1 and Type2 in a deterministic way, unfold the
new definition, and insert the new rule.
@end{itemize}
".

type_union(Type1,Type2,Type3):-
        uniontriple(Type1,Type2,Type3),!.
type_union(Type1,Type2,Type3):-
    dz_type_included(Type1,Type2),!,
    Type3=Type2.
type_union(Type1,Type2,Type3):-
    dz_type_included(Type2,Type1),!,
    Type3=Type1.
type_union(Type1,Type2,Type3):-
        new_type_symbol(Type3),
        get_typedefinition(Type1,Def1),
        get_typedefinition(Type2,Def2),
        merge(Def1,Def2,Def_s),
        insert_rule(Type3,Def_s),
        get_native_type_symbols(Def_s,Def_n,Def_nnat),
        union_of_native_types(Def_n,[],Def_natun),
        asserta_fact(uniontriple(Type1,Type2,Type3)),
        make_deterministic(Def_nnat,Defnew), 
        merge(Def_natun,Defnew,Def),
        unfold_type_union(Type3,Def,UDef),     %  unfold test test
        SDef = UDef,  %    simplify_def(UDef,SDef,Type3),
        sort(SDef,SDef_s),
        retract_rule(Type3),
        insert_rule(Type3,SDef_s).

% simplify_def([],[],_Root).
% simplify_def([Type|UDef],[NType|SDef],Root):-
%       compound_pure_type_term(Type,Term,F,A),!,
%       functor(NewTerm,F,A),
%         simplify_arg(A,Term,NewTerm,Root),
%       construct_compound_pure_type_term(NewTerm,NType),
%         simplify_def(UDef,SDef,Root).
% simplify_def([Type|UDef],[Type|SDef],Root):-
%         simplify_def(UDef,SDef,Root).

% simplify_arg(0,_Term,_NewTerm,_Root).
% simplify_arg(A,Term,NewTerm,Root):-
%       arg(A,Term,Type),
%       ( 
%           dz_equivalent_types(Type,Root) ->
%           arg(A,NewTerm,Root)
%       ;
%           arg(A,NewTerm,Type)
%       ),
%       A1 is A - 1,
%         simplify_arg(A1,Term,NewTerm,Root).

get_native_type_symbols([],[],[]).
get_native_type_symbols([T|Def_s],[T|Def_n],Def_nnat):-
    native_type_symbol(T),!,
    get_native_type_symbols(Def_s,Def_n,Def_nnat).
get_native_type_symbols([T|Def_s],Def_n,[T|Def_nnat]):-
    get_native_type_symbols(Def_s,Def_n,Def_nnat).

union_of_native_types([],L,L).
union_of_native_types([T|L],A,R):-
    union_elem_native_type(T,A,A1),
    union_of_native_types(L,A1,R).

union_elem_native_type(T,[],[T]) :- !.
union_elem_native_type(T,[T1|R],[T1|R]):-
    dz_type_included(T,T1),!.
union_elem_native_type(T,[T1|R],[T|R]):-
    dz_type_included(T1,T),!.
union_elem_native_type(T,[T1|R],[T1|R1]):-
    union_elem_native_type(T,R,R1).

:- export(get_typedefinition/2). % TODO: rename or merge with get_type_definition/2 (JFMC)
:- pred get_typedefinition(+Type,-Def): pure_type_term * list(pure_type_term)
   # "Return the definition of @var{Type} if Type is a type simbol. Otherwise return [Type].".

get_typedefinition(Type,Def):-
    ( rule_type_symbol(Type) ->
        get_type_definition(Type,Def)
    ; Def = [Type]
    ).


:- export(make_deterministic/2).
:- pred make_deterministic(+Def1,+Def2):  
 list(pure_type_term) * list(pure_type_term)#  
"
@var{Def1} and @var{Def2} are two sorted lists of type terms with
compound type terms of different functor/arity. @var{Def1} is the
merge of both definitions, if two compound type terms have the same
functor/arity, both are replaced by a new compound type terms whose
arguments are the deterministic union of the formers.
".

make_deterministic([],[]):- !. 
make_deterministic([X],[X]):- !. 
make_deterministic([TermType1,TermType2|Def1],Def):- 
    compare(Order,TermType1,TermType2),
    make_deterministic0(Order,TermType1,TermType2,Def1,Def). 

make_deterministic0(=,_TermType1,TermType2,Def1,Def):- 
    make_deterministic([TermType2|Def1],Def),!. 
make_deterministic0(_,TermType1,TermType2,Def1,Def):- 
    compound_pure_type_term(TermType1,Term1,Name,Arity),
    compound_pure_type_term(TermType2,Term2,Name,Arity),!,
    functor(Term,Name,Arity),
    obtain_new_term(Arity,Term1,Term2,Term),
    construct_compound_pure_type_term(Term,TermType),
    make_deterministic([TermType|Def1],Def). 
make_deterministic0(_,TermType1,TermType2,Def1,[TermType1|Def]):- 
    make_deterministic([TermType2|Def1],Def).


obtain_new_term(0,_,_,_) :- !.
obtain_new_term(N,Term1,Term2,Term):-
    arg(N,Term1,Arg1),
    arg(N,Term2,Arg2),
    type_union(Arg1,Arg2,Arg),
    arg(N,Term,Arg),
    N1 is N - 1,
    asserta_fact(uniontriple(Arg1,Arg2,Arg)),
    obtain_new_term(N1,Term1,Term2,Term).



%---------------------------------------------------------------------%  
%---------------------------------------------------------------------%  
%----------------------END-Deterministic-Union------------------------%  
%---------------------------------------------------------------------%  
%---------------------------------------------------------------------%  
