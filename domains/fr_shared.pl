
:- module(fr_shared,
    [ bottomelement/1,
      get_type/2,
      get_useful_AS/2,
      get_var_groups/3,
      get_vars/2,
      get_vars_repvars/3,
      linear/1,
      numerical/1,
      piii_restricted_length/1
    ],
    [ ] ).

:- use_module(library(compiler/p_unit), [curr_language/1]).

:- use_module(domain(fr_sets), 
    [ set_add_el/3,
      set_is_in/2,
      set_union/3,
      ss_add_el/3,
      ss_make_singl/2,
      ss_union/3
    ]).

:- use_module(library(messages)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Abstract Interpretation : Minimal Freeness Domain
% Copyright (C) 1993 Wim Simoens, Veroniek Dumortier
%                and Katholieke Universiteit Leuven.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% predicates that are shared between the minimal freeness analyser and 
% the combined definiteness-minimal freeness analyser
% these predicates are needed in min_fr.pl/min_fr_star_split.pl and
% min_fr_top_split.pl/min_fr_startop_split.pl
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  

bottomelement('$bottom').

%--------------------------------------------------------------------------

get_type(Term, var):- var(Term), !.
get_type(Term, Type):- 
    curr_language(clp),!,
    get_type0(Term, Type).
get_type(_, Type):- 
    curr_language(lp),!,
    Type = herb.
    
get_type0(Term, num):- number(Term), !.
get_type0(+(_,_), num):- !.
get_type0(-(_,_), num):- !.
get_type0(*(_,_), num):- !.
get_type0(/(_,_), num):- !.
get_type0(#(_), num):- !.
get_type0(+(_), num):- !.
get_type0(-(_), num):- !.
get_type0(piii(_), piii):- !.
get_type0(_, herb).

%--------------------------------------------------------------------------

numerical(T):- var(T), !.
numerical(T):- number(T), !.
numerical(+(_,_)).
numerical(-(_,_)).
numerical(*(_,_)).
numerical(/(_,_)).
numerical(+(_)).
numerical(-(_)).


%--------------------------------------------------------------------------

linear(E):- linear(E,_NrVarsE).

:- push_prolog_flag(multi_arity_warnings,off).

linear(E, 1) :- var(E), !.
linear(E, 0) :- number(E), !.
linear(E1 + E2, N) :- linear(E1, N1), linear(E2, N2), N is N1 + N2.
linear(E1 - E2, N) :- linear(E1, N1), linear(E2, N2), N is N1 + N2.
linear(-E, N) :- linear(E, N).
linear(E1 * E2, N) :-
    linear(E1, N1), linear(E2, N2),
    0 is N1*N2,
    N is N1 + N2.
linear(E1 / E2, N) :-
    linear(E1, N1), linear(E2, N2),
    0 is N1*N2,
    N is N1 + N2.
%%% E1*E2 is linear if linear(E1) and linear(E2) and #vars_E1*#vars_E2=0
%%% eg  5*(Y+3) is linear! 
%%%     5*(1 + X*X) or X*(1+Y) is not

:- pop_prolog_flag(multi_arity_warnings).

%--------------------------------------------------------------------------

% get_vars(T, Vars)
% Vars is the ordered set of variables in T
%
get_vars(T, Vars):-
    get_vars_(T, [], Vars).

get_vars_(T, Acc, Vars):- var(T), !, set_add_el(T, Acc, Vars).
get_vars_(T, Acc, Vars):- ground(T), !, Vars = Acc.
get_vars_(T, Acc, Vars):-
    T =.. [_ | Args],
    get_vars_loop(Args, Acc, Vars).

get_vars_loop([], Vars, Vars).
get_vars_loop([A | Args], Acc, Vars):-
    get_vars_(A, Acc, NewAcc),
    get_vars_loop(Args, NewAcc, Vars).

%--------------------------------------------------------------------------

% get_vars_repvars(T, Vars, Rvars)
% Vars is the ordered set of variables in T
% Rvars is the ordered set of variables that occur more than once in T
%
get_vars_repvars(T, Vars, Rvars):-
    get_vars_repvars_(T, [], [], Vars, Rvars).

get_vars_repvars_(T, VAcc, RAcc, Vars, Rvars):-
    var(T), !, set_add_el(T, VAcc, Vars),
    (set_is_in(T, VAcc) -> set_add_el(T, RAcc, Rvars) ; Rvars = RAcc).
get_vars_repvars_(T, VAcc, RAcc, Vars, Rvars):-
    ground(T), !, Vars = VAcc, Rvars = RAcc.
get_vars_repvars_(T, VAcc, RAcc, Vars, Rvars):-
    T =.. [_ | Args],
    get_vars_repvars_loop(Args, VAcc, RAcc, Vars, Rvars).

get_vars_repvars_loop([], Vars, Rvars, Vars, Rvars).
get_vars_repvars_loop([A | Args], VAcc, RAcc, Vars, Rvars):-
    get_vars_repvars_(A, VAcc, RAcc, NewVAcc, NewRAcc),
    get_vars_repvars_loop(Args, NewVAcc, NewRAcc, Vars, Rvars).

%--------------------------------------------------------------------------

% get_var_groups(T, Vars, Vgroups)
% Vars is the ordered set of variables in T
% Vgroups is the ordered set of variable groups in T;
%       each variable group is an ordered set of variables
%       variables in a numerical expression form one group,
%       other variables form singleton groups
% e.g. T = f(X+Y,g(U,A+B),V, U)
%       Vars = [X,Y,U,A,B,V]
%       Vgroups = [[X,Y],[U],[A,B],[V]]
%      T = f(A,A+B)  Vars = [A,B] Vgroups = [[A],[A,B]]
%
get_var_groups(T, Vars, VGroups):-
    get_var_groups_(T, [], [], Vars, VGroups).

get_var_groups_(T, VAcc, GAcc, V, G):-
    var(T), !,
    set_add_el(T, VAcc, V), ss_add_el([T], GAcc, G).
get_var_groups_(T, VAcc, GAcc, V, G):-
    ground(T), !, V = VAcc, G = GAcc.
get_var_groups_(T, VAcc, GAcc, V, G):-
    %  T contains at least one var
    get_type(T, Type),
    get_var_groups_split(Type, T, VAcc, GAcc, V, G).

get_var_groups_split(num, T, VAcc, GAcc, V, G):-
    !,
    get_vars(T, VarsT),     % VarsT \== []
    ( linear(T) ->
            set_union(VAcc, VarsT, V),
            ss_add_el(VarsT, GAcc, G)
    ;
            ss_make_singl(VarsT, Sing),
            ss_union(Sing, GAcc, G)
    ).
get_var_groups_split(_Type, T, VAcc, GAcc, V, G):-
    % Type is piii or herb
    T =.. [_|Args],
    get_var_groups_loop(Args, VAcc, GAcc, V, G).

get_var_groups_loop([], V, G, V, G).
get_var_groups_loop([A | Args], VAcc, GAcc, V, G):-
    get_var_groups_(A, VAcc, GAcc, NewVAcc, NewGAcc),
    get_var_groups_loop(Args, NewVAcc, NewGAcc, V, G).

%--------------------------------------------------------------------------

% get_useful_AS(ListOfAS, Useful_AS)    (S)
% ListOfAS : list of <as>
% Useful_AS is the list of <as> in ListOfAS with not(bottomelement(<as>))
%
% :- mode get_useful_AS(?,o).
get_useful_AS([],[]).
get_useful_AS([AS | LAS], LUAS) :- 
    bottomelement(AS),!,
    get_useful_AS(LAS, LUAS).
get_useful_AS([AS | LAS], [AS | LUAS]) :- 
    get_useful_AS(LAS, LUAS).

%--------------------------------------------------------------------------

% piii_restricted_length(T)
% is true if the list T of piii-parts is either of known length
% or contains a real element (element \== [] or \== Var)
%
piii_restricted_length(T):-
    % deals a.o. with T containing only []
    ground(T), !.
piii_restricted_length(T):-
    piii_restricted_length2(T).

piii_restricted_length2([]):-
    % no real element was found
    !, fail.
piii_restricted_length2([X|Rest]):-
    var(X), !, piii_restricted_length2(Rest).
piii_restricted_length2([[]|Rest]):-
    !, piii_restricted_length2(Rest).
piii_restricted_length2([_|_]). % List contains a real element

%--------------------------------------------------------------------------

%% %% NO LONGER USED
%%
%% %% VD
%% % identical up to order of variables in the set
%% seteq_order([],[]).
%% seteq_order([H|T], L2):-
%%         veroselect(H, L2, L2rest),
%%         seteq_order(T, L2rest).
%%  
%% veroselect(X, [Y|L], L):-
%%         X == Y, !.
%% veroselect(X, [Y|L], [Y|L1]):-
%%         select(X, L, L1).
%%  
%% % identical up to order of sets and order of variables in the sets
%% ss_eq_order([], []).
%% ss_eq_order([S | SS1], SS2):-
%%         ss_select(S, SS2, SS2rest),
%%         ss_eq_order(SS1, SS2rest).
%%  
%% ss_select(A, [B | SS], SS):-
%%         seteq_order(A, B), !.
%% ss_select(A, [B | SS1], [B | SS2]):-
%%         ss_select(A, SS1, SS2).
 
%% %% NO LONGER NEEDED
%%
%% % :- mode promotecombs(i,i,o).
%% % UPDATED
%% %promotecombs(D,P,Comb) :-
%% % D is a list of sets
%% % P is a list
%% % Comb is the result as a list : { S_1 \cup S_2 \mid S_1 \in \wp_\emptyset( D) , S_2 \in P\}$
%% 
%% promotecombs(L,P,C) :-
%%      ss_empty(Ci),
%%      promotecombs(L,P,Ci,C).   
%% 
%% promotecombs([],_L,C,C).
%% promotecombs([S|T],L,Ci,C) :-
%%      % for all elements E of L do add S U E to Ci
%%      union_and_add(L,S,Ci,Cinew),
%%      promotecombs(T,L,Cinew,C).
%% 
%% union_and_add([],_S,C,C).
%% union_and_add([S1 |T], S2,Ci,C) :-
%%      set_union(S1,S2,U),
%%      ss_add_el(U,Ci,Cinew),
%%      union_and_add(T,S2,Cinew,C).



