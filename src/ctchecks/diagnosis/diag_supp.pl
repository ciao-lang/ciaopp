:- module(_,[],[]).

:- use_module(library(compiler/p_unit/program_keys)).
:- use_module(library(compiler/p_unit/p_unit_db), [source_clause/3]).
:- use_module(library(lists), [length/2]).
:- use_module(library(idlists), [member_0/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(engine(io_basic)).

% TODO: duplicated Id
% TODO: merge this with program_keys or operations in the plai_db

% Auxiliary stuff

:- export(get_prev_lit/2).
get_prev_lit(SgKey,PrevKey) :-
    is_clkey(SgKey),!,
    get_last_lit(SgKey,PrevKey).
get_prev_lit(SgKey,PrevKey) :-
    decode_litkey(SgKey,F,A,C,G),
    G1 is G - 1,
    G1 > 0,
    get_litkey(F,A,C,G1,PrevKey).

:- export(get_clause_id/2).
get_clause_id(SgKey,ClKey) :-
    decode_litkey(SgKey,F,A,C,_),
    get_clkey(F,A,C,ClKey),!.
get_clause_id(SgKey,SgKey).

:- export(find_lit/2).
find_lit(((Lit:Key),_),Lit:Key) :-!.
find_lit((_,Lits),Lit) :-!,
    find_lit(Lits,Lit).
find_lit((Lit:Key),Lit:Key) :-!.
find_lit(_,Lit) :-
    displayq('NOT FOUND IN BODY'(Lit)),fail.

:- export(get_last_lit/2).
get_last_lit(ClKey,LastKey) :-
    source_clause(ClKey,clause(_,Body),_),
    find_last(Body,LastKey).

:- export(find_last/2).
find_last((_,B),Last) :-
    find_last(B,Last).
find_last(_:Key,Key).

:- export(get_next_lit/2).
get_next_lit(SgKey,NextKey) :-
    is_last_lit(SgKey),!,
    get_clause_id(SgKey,NextKey).
get_next_lit(SgKey,NextKey) :-
    decode_litkey(SgKey,F,A,C,G),
    G1 is G + 1,
    get_litkey(F,A,C,G1,NextKey).

:- export(get_first_lit_cl/2).
get_first_lit_cl(ClKey,FKey) :-
    decode_clkey(ClKey,F,A,C),
    get_litkey(F,A,C,1,FKey).

:- export(is_last_lit/1).
is_last_lit(SgKey) :-
    get_clause_id(SgKey,ClKey),
    get_last_lit(ClKey,SgKey).

:- export(get_var_name/4).
get_var_name(V,[V0|_],[N|_],N) :-
    V == V0,!.
get_var_name(V,[_|Vs],[_|Ns],N) :-
    get_var_name(V,Vs,Ns,N).

:- export(guess_vars/2).
guess_vars(B,A) :-
    length(B,Max),
    gen_list(Max,1,[_],A),
    subset(A,B).

:- export(subset/2).
subset([A],[A|_]). % TODO: missing cut
subset(S,[A|Ss]) :-
    subset(S1,Ss),
    ( S = S1
    ; S = [A|S1]
    ). % TODO: missing cut

:- export(gen_list/4).
gen_list(_,_,L,L).
gen_list(Max,N1,L,L1):-
    N1 < Max,
    N2 is N1 + 1,
    gen_list(Max,N2,[_|L],L1).

:- export(subset_0/2).
subset_0([],_).
subset_0([S|Ss],Sup) :-
    member_0(S,Sup),
    subset_0(Ss,Sup).

:- export(range/2).
range(ASubs,Range) :-
    varset(ASubs,Range).

:- export(get_init_lit/4).
get_init_lit(_,Head,Lit,Key) :-
    \+ decode_litkey(Key,_,_,_,_),!,
    Lit = Head.
get_init_lit(Body,_,Lit,Key) :-
%       get_prev_lit(Key,PKey),
    find_lit(Body,(Lit:Key)).
