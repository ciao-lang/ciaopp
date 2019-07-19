%% :- module(basic_type_operations,
%% 	[ belongs_to_type/2,
%% 	  dz_equivalent_types/2,
%% 	  dz_type_included/2,
%% 	  %init_before_type_intersection/0
%% 	  intersec_types/4,
%% 	  is_empty_type/1,
%% 	  is_ground_type/1,
%% 	  is_infinite_type/1
%% 	  %after_type_intersection/0,
%% 	  %replace_vars_by_types/3,
%% 	  %create_new_type_rule/2,
%% 	  %find_type_functor/5,
%% 	  %equivalent_to_numeric/1,
%% 	  %functor_pure_type_term/1,
%% 	  %equiv_type/2
%% 	],
%% 	[ assertions, basicmodes ]).
%% 
%% :- use_module(typeslib(regtype_rules)).

 %% % DTM: Needed for properties assertions checking!!!
 %% :- use_module(typeslib(regtype_basic_lattice) , [pure_type_term/1] ).
 %% 
 %% PLG: No, it was not needed, because in typeslib.pl:
 %% :- reexport(typeslib(regtype_basic_lattice)).
 %% and 
 %% :- include(typeslib(basic_type_operations)). 

% For debugging

%% write_computed_dz_pairs:-
%%   findall(dz_pair(X, Y), dz_pair(X, Y), L),
%%   write_list1(L). 

write_all_computed_type_inclusion :-
  findall(computed_type_inclusion(X, Y), computed_type_inclusion(X, Y), L),
  write_list1(L). 

% End debugging

% TYPE CHECKING RELATED PROCEDURES

:- reexport(typeslib(equiv_type)).

% Counters used to name new created types.

:- data('$already_validated$'/1).

:- data(computed_type_intersec/3).

:- data(computed_infinite_type/1).

% Type symbols which already have been detected to be empty.

:- data(computed_empty_type/1).

% Type symbols which have not been simplified yet.

:- data(no_simplified_type/1).

:- data(pgm_computed_type_inclusion/2).  %% computed type inclusions for the current program.
:- data(lib_computed_type_inclusion/2).  %% computed type inclusions for libraries.

computed_type_inclusion(A,B):-
	pgm_computed_type_inclusion(A,B).
computed_type_inclusion(A,B):-
	lib_computed_type_inclusion(A,B).

% =======================================================================
% EQUIVALENCE AND INCLUSION OF TYPES

:- pred dz_equivalent_types(+Type1, +Type2)

=> pure_type_term * pure_type_term
  
# "Check if @var{Type1} and @var{Type2} are equivalent 
(i.e. denote the same set of terms).".

 %% dz_equivalent_types(Type1, Type2):- 
 %%    dz_type_included(Type1, Type2),
 %%    dz_type_included(Type2, Type1).

dz_equivalent_types(Type1, Type2):-    % PLG Dec-20-2003
   dz_type_included_tabling(Type1, Type2),
   dz_type_included_tabling(Type2, Type1).

:- pred dz_type_included(+Type1, +Type2) 

=> pure_type_term * pure_type_term

# "Check if @var{Type1} is included in @var{Type2}. @tt{IMPORTANT
NOTICE:} We assume that there are not rule type symbols in the type
disjunction of the type rule defining a particular rule type symbol
(i.e. type rules are unfolded).".

 %% dz_type_included(Type1, Type2):- 
 %%      computed_type_inclusion(Type1, Type2),
 %%      !.
 %% dz_type_included(Type1, Type2):- 
 %%      retractall_fact(pgm_dz_pair(_, _)),
 %%      dz_subset(Type1, Type2),
 %%      asserta_fact(pgm_computed_type_inclusion(Type1, Type2)).

 %% Old Dec-9-2003
dz_type_included(Type1, Type2):- 
     retractall_fact(pgm_dz_pair(_, _)),
     dz_subset(Type1, Type2).

 %% dz_type_included(Type1, Type2):- 
 %%      dz_subset(Type1, Type2, []).

dz_type_included_tabling(Type1, Type2):- 
     computed_type_inclusion(Type1, Type2),
     !.
dz_type_included_tabling(Type1, Type2):- 
     dz_type_included(Type1, Type2),
     asserta_fact(pgm_computed_type_inclusion(Type1, Type2)).


:- pred dz_pair(?TypSymb, ?TypSet)

# "States that the type symbol @var{TypSymb} and
   the set @var{TypSet} of pure type terms have already been compared. 
   it is used to ensure termination.". 

dz_pair(TypSymb, TypSet):-
	pgm_dz_pair(TypSymb, TypSet).
dz_pair(TypSymb, TypSet):-
	lib_dz_pair(TypSymb, TypSet).

:- data(pgm_dz_pair/2). %% For user programs.
:- data(lib_dz_pair/2). %% For libraries.

:- pred  dz_subset(+Type1, +Type2) 

=> pure_type_term * pure_type_term

# "Succeds iff @var{Type1} is included in @var{Type2}.".

dz_subset(Type1, Type2):- Type1 == Type2, !.
dz_subset(Type1, _Type2):- bot_type(Type1), !. 
dz_subset(_Type1, Type2):- bot_type(Type2), !, fail. 
dz_subset(_Type1, Type2):- equivalent_to_top_type(Type2), !.  
dz_subset(Type1, _Type2):- top_type(Type1), !, fail.
% Added by PLG May-18-2003 to fix the bug:
% list(num) was not included in gnd.
dz_subset(Type1, Type2):- 
    ground_type(Type2), 
    !,
    is_ground_type(Type1).
% End added
dz_subset(Type1, Type2):- 
    compound_pure_type_term(Type1, _Term1, _Name1, _Arity1),
    !,
    compound_pure_type_term_dz_subset(Type1, Type2). 
%% Added by PLG. Oct, 20, 2004
dz_subset(Type1, Type2):- 
    compound_pure_type_term(Type2, _Term2, _Name2, _Arity2),
    !,
    rule_type_symbol(Type1), 
    dz_subset_v([Type1], [[Type2]]).
%% End Added by PLG.
%% Paco:
%% dz_subset(Type1, Type2):- 
%%      \+ rule_type_symbol(Type1), 
%%      \+ rule_type_symbol(Type2), !, 
%%      dz_subset_lattice(Type1, Type2).
dz_subset(Type1, Type2):- 
      basic_lattice_type_symbol(Type1), 
      basic_lattice_type_symbol(Type2),
      !,
    dz_subset_lattice(Type1, Type2).
%% End Paco
dz_subset(Type1, Type2):- dz_subset_v([Type1], [[Type2]]). 

 %% compound_pure_type_term_dz_subset(Type1, Type2):-  % Redundant -PLG
 %%    ground_type(Type2), !,
 %%    dz_subset_v([Type1], [[Type2]]).
compound_pure_type_term_dz_subset(_Type1, Type2):- 
   struct_type(Type2), !.
compound_pure_type_term_dz_subset(Type1, Type2):-  
   ground_struct_type(Type2), !,
   is_ground_type(Type1).
 %%    set_ground_type(GndType),          % This also should work.
 %%    dz_subset_v([Type1], [[GndType]]). %
compound_pure_type_term_dz_subset(Type1, Type2):-
   compound_pure_type_term(Type2, _Term2, _Name2, _Arity2),
   dz_subset_v([Type1], [[Type2]]).
compound_pure_type_term_dz_subset(Type1, Type2):-    %|
   rule_type_symbol(Type2),                          %| added by claudio
   dz_subset_v([Type1], [[Type2]]).                  %|

:- pred dz_subset_v(+Seq, +SeqSet)

# "@var{Seq} is a n-ary sequence ($n @geq 0$).  
   @var{SeqSet} is a set of n-ary sequences.".

dz_subset_v(_Seq, []):- !, fail.   
dz_subset_v([bot|Seq],SeqSet):-!,
   dz_tails(SeqSet, Tails),
   dz_subset_v(Seq, Tails).            
dz_subset_v([], _):- !.            
dz_subset_v([Type|Seq], SeqSet):-
   rule_type_symbol(Type), % old 
   % type_symbol(Type), 
   findall(TypeSet, dz_pair(Type, TypeSet), SetTypeSet,[[Type]]), % claudio
   % findall(TypeSet, dz_pair(Type, TypeSet), SetTypeSet),
   dz_heads(SeqSet, Heads),
   set_ty_subset(SetTypeSet, Heads), !,
   dz_tails(SeqSet, Tails),
   dz_subset_v(Seq, Tails).
dz_subset_v([Type|Seq], SeqSet):-
   rule_type_symbol(Type), !,
   dz_expand([Type|Seq], SetofSeq),
   dz_heads(SeqSet, Heads),
   asserta_fact(pgm_dz_pair(Type, Heads)), 
   all_dz_subset_v(SetofSeq, SeqSet).   
dz_subset_v([Type|Seq], SeqSet):-
 %% Commented by PLG  Mar 7 98
 %%   (top_type(Type);
 %%    base_type_symbol(Type);
 %%    ground_type(Type);
 %%    compound_pure_type_term(Type, _Comp, _Name, _Arity);
 %%    constant_symbol(Type, _)), !,
   dz_open(Type, [Type|Seq], OpenSeq),
   dz_expands(SeqSet, ExpSeqSet),
   dz_selects(ExpSeqSet, Type, SelExpSeqSet),
   dz_opens(SelExpSeqSet, Type, OpenSelExpSeqSet),
   dz_subset_v(OpenSeq, OpenSelExpSeqSet).

dz_heads([], []).
dz_heads([[Type|_]|SeqSet], [Type|Rest]):-
  dz_heads(SeqSet, Rest).


:- pred set_ty_subset(?S1, ?S2)

# "@var{S2} is a subset of some set in the set of sets @var{S1}.".

% New
% set_ty_subset([], _) :-!. No decomment never !!! PLG
 %%   set_ty_subset([Set1|Residue], Set) :-
 %%       (ty_subset(Set, Set1) -> true ; set_ty_subset(Residue, Set)).

set_ty_subset([Set1|Residue], Set) :-
    (ty_subset(Set1, Set) -> true ; set_ty_subset(Residue, Set)). % changed by claudio


:- pred ty_subset(?S1, ?S2)

# "@var{S1} is a subset of @var{S2}.".

ty_subset([], _):-!.
ty_subset([Element|Residue], Set) :-
	member_0(Element, Set),
	ty_subset(Residue, Set).


dz_tails([], []).
dz_tails([[_|Seq]|SeqSet], [Seq|Rest]):-
  dz_tails(SeqSet, Rest).

:- pred dz_expand(+Seq, -Expansion)

# "Takes the sequence of pure type terms @var{Seq} (implemented as a list)
   and expands it (@var{Expansion}).".

% Preconditions:
%    For all rules T <- [T1, T2, ..., Tn] in the common set of rules:
%    each Ti is not empty, and Ti is either top, or a base type symbol, or 
%    Ti = f(Ti1, ..., Tik) k>=0 (note that for some j different from i, Tj can
%    be of the form f(Tj1, ..., Tjk), i.e. can have the same main 
%    functor/arity). 

% Warning! Shouldn't Seq be a n-ary sequence $n @geq 1$ ?. In that case, 
% the first clause should be removed?
dz_expand([], []):-!.
dz_expand([TypSymbol|Seq], Expansion):-
    rule_type_symbol(TypSymbol), !, 
    get_type_definition(TypSymbol, Defin1),
    sort(Defin1, Defin), % assume the type is defined.
    dz_expand_type_symbol(Defin, Seq, Expansion).
dz_expand(Seq, [Seq]).

dz_expand_type_symbol([], _Seq, []).
dz_expand_type_symbol([Type|Defin], Seq, [[Type|Seq]|Expansion]):-
   dz_expand_type_symbol(Defin, Seq, Expansion).

% In fact we should perform the real union by removing duplicated items. 
% PLG Nov 6 98
dz_expands([], []):-!. 
dz_expands([Seq|Rest], OutExp):-
    dz_expand(Seq, Expan1),
    dz_expands(Rest, Expansion),
    append(Expan1, Expansion, OutExp).
   
all_dz_subset_v([], _):-!.
all_dz_subset_v([Seq|SetofSeq], SeqSet):-
   dz_subset_v(Seq, SeqSet),
   all_dz_subset_v(SetofSeq, SeqSet).

 %% dz_open(+Type, +Seq, -OutSeq)
 %% Type: a pure type term.
 %% Seq: an expanded selected sequence.
 %% OutSeq: a sequence.

dz_open(Type, [_|InSeq], InSeq):-
%  (top_type(Type); 
%   base_type_symbol(Type);
%   struct_type(Type); % Added by PLG 24-5-99
%   ground_type(Type); 
%   type_parameter(Type); % Added by PBC 01-12-03
%   constant_symbol(Type, _)), !.
% replaced by PBC 01-12-03, by:
    basic_lattice_type_symbol(Type), !.
dz_open(Type, [Type1|InSeq], OuSeq):-
  compound_pure_type_term(Type, _Comp, _Name, Arity),
  top_type(Type1), !,
  create_top_sequence(Arity, TopSeq),
  append(TopSeq, InSeq, OuSeq). 
dz_open(Type, [Type1|InSeq], OuSeq):-
  compound_pure_type_term(Type, _Comp, _Name, Arity),
  ground_type(Type1), !,
  create_ground_sequence(Arity, GroundSeq),
  append(GroundSeq, InSeq, OuSeq). 
dz_open(Type, [Type1|InSeq], OuSeq):- % Uncommented -PLG (11 Jul 05)
  compound_pure_type_term(Type, _Comp, _Name, Arity),
  struct_type(Type1), !,
  create_top_sequence(Arity, TopSeq),
  append(TopSeq, InSeq, OuSeq).
dz_open(Type, [Type1|InSeq], OuSeq):- % Added -ASM (5 Sep 12) % TODO:[new-resources] for etermsvar
  compound_pure_type_term(Type, _Comp, _Name, Arity),
  var_type(Type1), !,
  create_var_sequence(Arity, TopSeq),
  append(TopSeq, InSeq, OuSeq). 
dz_open(Type, [Type1|InSeq], OuSeq):-
   compound_pure_type_term(Type, _Comp, Name, Arity), 
   compound_pure_type_term(Type1, Comp1, Name, Arity), 
   Comp1 =.. [_|ArgSeq],
   append(ArgSeq, InSeq, OuSeq). 
   
create_top_sequence(0, []) :- !.
create_top_sequence(A, [Top|Rest]):-
  A > 0,
  set_top_type(Top),
  A1 is A -1,
  create_top_sequence(A1, Rest).

create_ground_sequence(0, []) :- !.
create_ground_sequence(A, [Ground|Rest]):-
  A > 0,
  set_ground_type(Ground),
  A1 is A -1,
  create_ground_sequence(A1, Rest).

% Added -ASM (5 Sep 12) % TODO:[new-resources] for etermsvar
create_var_sequence(0, []) :- !.
create_var_sequence(A, [Var|Rest]):-
  A > 0,
  set_var_type(Var),
  A1 is A -1,
  create_var_sequence(A1, Rest).

 %% dz_opens(+Seq, +Type, -OutSeq)
 %% Seq: a set of expanded selected sequences.
 %% Type: a pure type term.
 %% OutSeq: a set of sequences.

dz_opens([], _, []):-!.
dz_opens([Seq|Rest], Type, [OuSeq|OuRest]):-
    dz_open(Type, Seq, OuSeq),
    dz_opens(Rest, Type, OuRest).

 %% dz_selects(+Seqs, +Type, -Sel)
 %% Type: a type term.
 %% Seqs: an expanded set of sequences.
 %% Sel: a set of sequences.

dz_selects([[Type1|Seq]|Rest], Type, Sel):-
   (dz_type_selects(Type, Type1) -> 
        Sel = [[Type1|Seq]|SRest] ; Sel = SRest),
    dz_selects(Rest, Type, SRest).
dz_selects([], _Type, []).   


% =======================================================================
% EMPTINESS OF TYPES.

:- pred is_empty_type(+Type)

# "Succeeds if the type @var{Type} is equivalent to the empty (bottom)
   type.  If @var{Type} is a type symbol and there is no type rule
   defining it, then it is assumed that @var{Type} is empty.  DO NOT
   memoizes information of type symbols which are known to be empty
   (by using the dynamic predicate
   @verb{computed_empty_type(TypeSymbol)}).".

% Note: we can also use dz_equivalent_types(Type1, Type2) to test if 
% Type1 is equivalent to bottom (Type2).
  
is_empty_type(Type):- 
        empty_type(Type, []).

:- pred  empty_type(+Type, +Seen)

# "Succeeds if the type @var{Type} is equivalent to the empty (bottom)
   type. @var{Type} is a pure type term.  @var{Seen} is a list of
   already proccessed type symbols which are defined by rules, in the
   branch from the root.  @verb{computed_empty_type(Type)} is a
   dynamic predicate used to memoizing types that we already know are
   empty.".

empty_type(Type, _Seen):- 
        bot_type(Type), 
        !.
empty_type(Type, Seen):-
        rule_type_symbol(Type),
        !,
        empty_rule_type_symbol(Type, Seen).
empty_type(Type,  Seen):-
        compound_pure_type_term(Type, Comp, _Name, Arity), 
        type_arg_empty(Arity, Comp, Seen).

empty_rule_type_symbol(Type, _Seen):- 
        computed_empty_type(Type), 
        !.
empty_rule_type_symbol(Type, Seen):-
        member_0(Type, Seen), 
        !.
        % set_computed_empty_type(Type). % DO NOT DECOMMENT THIS IS WRONG!!! PLG
empty_rule_type_symbol(Type, Seen):-
        % get_type_definition(Type, TypUnion),
        % debug_message("get_NP_typedef_default_bot(~q, ~q)", [Type, TypUnion]),
        %% get_NP_typedef_default_bot(Type, TypUnion), %% 14-4-99 PLG
        get_NO_par_type_definition(Type, TypUnion), % Now a type not found is assumed bottom.
        % debug_message("get_NP_typedef_default_bot(~q, ~q)", [Type, TypUnion]),
        empty_type_union(TypUnion, [Type|Seen]).
        % DO NOT DECOMMENT THIS IS WRONG!!! PLG
        % ckeck_empty_type_union_and_assert(TypUnion, Type, [Type|Seen]).

type_arg_empty(Arg_Num, Comp,  Seen):-
      Arg_Num > 0,  
      arg(Arg_Num, Comp, Arg),
     (empty_type(Arg,  Seen) 
         -> true
          ; NArg_Num is Arg_Num - 1,
            type_arg_empty(NArg_Num, Comp,  Seen)).

% DO NOT DECOMMENT THIS IS WRONG!!! PLG
 %% ckeck_empty_type_union_and_assert(TypUnion, Type, Seen):- 
 %%         empty_type_union(TypUnion, Seen), 
 %%         set_computed_empty_type(Type).

empty_type_union([],  _Seen).
empty_type_union([Type|TypUnion],  Seen):-
  empty_type(Type, Seen),
  empty_type_union(TypUnion, Seen).  

% Assert Type as empty (if it is not yet).
set_computed_empty_type(Type):-
  computed_empty_type(Type), 
  !.
set_computed_empty_type(Type):-
  asserta_fact(computed_empty_type(Type)).

% =======================================================================

% CLEANING BEFORE AND AFTER TYPE INTERSECTION

%% init_before_pp_type_analisys:-
%%    retractall_fact(typ_sym_counter(_)),
%%    %2 
%%    retractall_fact(computed_empty_type(_)),
%%    retractall_fact(computed_type_intersec(_, _, _)),
%%    retractall_fact(no_simplified_type(_)),
%%    init_typ_symbol_counter.

init_before_type_intersection :-
%PBC   retractall(typ_sym_counter(_)),
   retractall_fact(computed_empty_type(_)),
   retractall_fact(computed_type_intersec(_, _, _)),
   retractall_fact(no_simplified_type(_)),
%PBC   init_typ_symbol_counter.
   true.

%New PLG
 %% init_before_type_intersection :-
 %%    current_type_symbol_counter_value(Count),
 %%    retractall(previous_typ_sym_counter(_)),
 %%    assert(previous_typ_sym_counter(Count)),
 %%    retractall(computed_empty_type(_)),
 %%    retractall(computed_type_intersec(_, _, _)),
 %%    retractall(no_simplified_type(_)).

%% clean_after_type_intersection :-
%%    retractall_fact(typ_sym_counter(_)),
%%    retractall_fact(computed_type_intersec(_, _, _)).

after_type_intersection :-
   findall(TypSymbol, no_simplified_type(TypSymbol), TypSymbol_List),
   retract_rules(TypSymbol_List),
%PBC   retractall(typ_sym_counter(_)),
   retractall_fact(computed_empty_type(_)),
   retractall_fact(computed_type_intersec(_, _, _)),
   retractall_fact(no_simplified_type(_)).

 %New PLG
 %% after_type_intersection :-
 %%    findall(TypSymbol, no_simplified_type(TypSymbol), TypSymbol_List),
 %%    retract_rules(TypSymbol_List),
 %%    previous_typ_sym_counter(Count),
 %%    retractall(typ_sym_counter(_)),
 %%    retractall(previous_typ_sym_counter(_)),
 %%    assert(typ_sym_counter(Count)),   
 %%    retractall(computed_empty_type(_)),
 %%    retractall(computed_type_intersec(_, _, _)),
 %%    retractall(no_simplified_type(_)).

clean_after_empty_pp_type_intersection:-
   findall(TypSymbol, no_simplified_type(TypSymbol), TypSymbol_List),
   retract_rules(TypSymbol_List),
   retractall_fact(computed_empty_type(_)),
   retractall_fact(computed_type_intersec(_, _, _)),
   retractall_fact(no_simplified_type(_)).

clean_after_NON_empty_pp_type_intersection:-
   retractall_fact(computed_empty_type(_)),
   retractall_fact(computed_type_intersec(_, _, _)),
   retractall_fact(no_simplified_type(_)).

% END OF CLEANING BEFORE AND AFTER TYPE INTERSECTION

% These predicates for eterms:
intersec_types(Var_List, _Var_Types, OTypeAss, OTypeAss):-
   var(Var_List), !.
intersec_types(Var_List, Var_Types, ITypeAss, OTypeAss):-
   nonvar(Var_List), 
   Var_List = [Var|List],
   find_list_entry(Var_Types, Var, vt(_, Types)),
   set_top_type(Top),
   intersec_type_list(Types, Top, LType),
   \+ bot_type(LType),
   intersec_types(List, Var_Types, [Var:LType|ITypeAss], OTypeAss).

intersec_type_list(Type_List, Type, Type):-
   var(Type_List), !.
intersec_type_list(Type_List, InType, OutType):-
   nonvar(Type_List),
   Type_List = [Type | List],
   type_intersection_0(InType, Type, Intersec),
   (is_empty_type(Intersec) -> 
      set_bottom_type(OutType) % , retract_1 -PL
      ;
      intersec_type_list(List, Intersec, OutType)).

type_intersection_0(InType, Type, Intersec):-
   %% type_rule_simplify, % -PL warning !
   type_intersection(InType, Type, Intersec),
   selec_type_rule_simplify, !.

% INTERSECTION OF TYPES

 %%   Intersection Algorithm as described in Philip W. Dart and Justin
 %%   Zobel. A Regular Type Language For Logic Programs. In Types in Logic
 %%   Programming, ed. F. Pfenning, MIT Press, 1987, pp. 157--187.
 %%   NOTE: SOME SIMPLIFICATION OF RULES IS DONE. SEARCH FOR S-PL.

type_intersection(Typ1, Typ2, Typ1):-
    Typ1 == Typ2, !. 
type_intersection(Typ1, Typ2, Typ2):-
    top_type(Typ1), !.
type_intersection(Typ1, Typ2, Typ1):-
    top_type(Typ2), !.
type_intersection(Typ1, _Typ2, Int):-
    bot_type(Typ1), !,
    set_bottom_type(Int).
type_intersection(_Typ1, Typ2, Int):-
    bot_type(Typ2), !,
    set_bottom_type(Int).
type_intersection(Typ1, Typ2, Typ3):-
    computed_type_intersec(Typ1, Typ2, Typ3), !.
type_intersection(Typ1, Typ2, Intersec):-
    rule_type_symbol(Typ1), 
    !,
    get_type_definition(Typ1, Defin1), 
    determine_type_union(Typ2, Defin2),
    type_intersection2(Typ1, Typ2, Defin1, Defin2, Intersec).
type_intersection(Typ1, Typ2, Intersec):-
    rule_type_symbol(Typ2), 
    !,
    get_type_definition(Typ2, Defin2), 
    determine_type_union(Typ1, Defin1),
    type_intersection2(Typ1, Typ2, Defin1, Defin2, Intersec).
type_intersection(Typ1, Typ2, Intersec):-
    regtype_basic_type_intersection(Typ1, Typ2, Intersec), !.
type_intersection(Typ1, Typ2, TypeInter):-
    compound_pure_type_term(Typ1, Comp1, Name1, Arity1), 
    compound_pure_type_term(Typ2, Comp2, Name2, Arity2),
    !,
    ((Name1 == Name2, Arity1 == Arity2) 
        ->
        functor(CompInter, Name2, Arity2),
        arg_typ_inter(Arity2, CompInter, Comp1, Comp2),
        construct_compound_pure_type_term(CompInter, TypeInter)
        ;  
        set_bottom_type(TypeInter)).
type_intersection(Typ1, Typ2, TypeInter):-
    compound_pure_type_term(Typ1, _Comp1, _Name1, _Arity1), 
    !,
    compound_pure_type_term_intersection(Typ1, Typ2, TypeInter).
type_intersection(Typ1, Typ2, TypeInter):-
    compound_pure_type_term(Typ2, _Comp2, _Name2, _Arity2), 
    !,
    compound_pure_type_term_intersection(Typ2, Typ1, TypeInter).
type_intersection(_Typ1, _Typ2, Intersec):- 
     set_bottom_type(Intersec).


compound_pure_type_term_intersection(Typ1, Typ2, TypeInter):-
    basic_lattice_type_includes_compound_type_term(Typ2), 
    !,
    TypeInter = Typ1.
compound_pure_type_term_intersection(Typ1, Typ2, TypeInter):-
    basic_lattice_type_needs_intersection_with_compound_type_term_args(Typ2, Intersec_with), 
    !,
    compound_pure_type_term(Typ1, Comp1, Name1, Arity1), 
    functor(CompInter, Name1, Arity1),
    compound_type_term_args_intersec_with_one_type(Arity1, CompInter, Comp1, Intersec_with),
    construct_compound_pure_type_term(CompInter, TypeInter).
compound_pure_type_term_intersection(_Typ1, _Typ2, TypeInter):-
    set_bottom_type(TypeInter).


arg_typ_inter(0, _Intersec, _Typ1, _Typ2):-!.
arg_typ_inter(Arg, Intersec, Typ1, Typ2):-
       Arg > 0, 
       arg(Arg, Typ1, Arg1),
       arg(Arg, Typ2, Arg2),
       type_intersection(Arg1, Arg2, Arg3),
       arg(Arg, Intersec, Arg3),
       NArg is Arg - 1,
       arg_typ_inter(NArg, Intersec, Typ1, Typ2).

compound_type_term_args_intersec_with_one_type(0, _Intersec, _CompType, _Not_Comp_Type):-!.
compound_type_term_args_intersec_with_one_type(Arg, Intersec, CompType, Not_Comp_Type):-
       Arg > 0, 
       arg(Arg, CompType, Arg1),
       type_intersection(Arg1, Not_Comp_Type, Arg3),
       arg(Arg, Intersec, Arg3),
       NArg is Arg - 1,
       compound_type_term_args_intersec_with_one_type(NArg, Intersec, CompType, Not_Comp_Type).

determine_type_union(Type, Defin):-
    (rule_type_symbol(Type)
       -> get_type_definition(Type, Defin) 
       ;  Defin = [Type]).


:- use_module(domain(deftypes), [approx_as_defined/2]).

type_intersection2(Typ1, Typ2, TypUnion1, TypUnion2, NewIntersec):-
  new_type_symbol(Intersec),
  asserta_fact(computed_type_intersec(Typ1, Typ2, Intersec)),
  % asserta(no_simplified_type(Intersec)), % This is done by insert_new_type_rule 
  cp_intersec(TypUnion1, TypUnion2, [], Union),
  (Union == [] 
     -> set_bottom_type(X), NUnion = [X] 
     ;  NUnion = Union),
   insert_new_type_rule(Intersec, NUnion),
  ( current_pp_flag(types,deftypes) ->
    deftypes:approx_as_defined(Intersec,NewIntersec),
    remove_rule(Intersec)
  ; NewIntersec = Intersec
  ).

cp_intersec([], _TypUnion2, Union, Union):-!.
cp_intersec([Typ1|Union1], TypUnion2, Union, NUnion):-
  cp_intersec_2(TypUnion2, Typ1, Union, IUnion),
  cp_intersec(Union1, TypUnion2, IUnion, NUnion).

cp_intersec_2([], _Typ1, Union, Union):-!.
cp_intersec_2([Typ2|Union2], Typ1, Union, NUnion):-
  type_intersection(Typ1, Typ2, Inter),
  (bot_type(Inter) 
     -> AcUnion = Union 
     ;  AcUnion = [Inter|Union]),
  cp_intersec_2(Union2, Typ1, AcUnion, NUnion).

% End of type intersection.

% ADDED FOR NON-FAILURE

% pure type terms beginning with a functor symbol of arity >= 0. 
% was
% functor_pure_type_term(Type):- 
    % nonvar(Type), \+ type_symbol(Type). 

functor_pure_type_term(Type):- 
    compound_pure_type_term(Type, _Term, _Name, _Arity), 
    !.
functor_pure_type_term(Type):- 
    constant_symbol(Type, _Constant).

% 

equivalent_to_numeric(Type):- 
   numeric_type(Type), !.
equivalent_to_numeric(Type):- 
   em_defined_type_symbol(Type, Defin),
   Defin = [Type1], numeric_type(Type1).


% =======================================================================

% CHECKING INFINITE TYPES (for non-fail).

% is_infinite_type(Type).
% Succeeds iff the type Type is infinite.
% Preconditions:
%   1) T is not empty.
%   2) For all rules T <- [T1, T2, ..., Tn] in the common set of rules:
%   each Ti is not empty, and Ti is either top, or a base type symbol, or 
%   Ti = f(Ti1, ..., Tik) (note that for some j different from i, Tj can
%   be of the form f(Tj1, ..., Tjk), i.e. have the same main functor/arity). 
%
% Example 1: T <- [0, T]. This type is not infinite. Note that the type rule
% does not meet the assumptions.
% Example 2:
% T <- [T1, f(T)].  Do not meet the assumptions.
% T1 <- [T].
% Example 3: T <- [0, f(T)] meets the assumptions.
% Example 4:
% T <- [T1, 0].  Do not meet the assumptions.
% T1 <- [T].
% Example 5:
% T <- [T1, 0].  Do not meet the assumptions.
% T1 <- ['$integer$', T].
% With the above assumption, a type T is infinite when the predicate 
% infinite_type(T, []) succeeds.
% infinite_type(T, Seen) is true iff:
% 1) T is top.
% 2) T is base type symbol.
% 3) T is a type symbol in Seen.
% 4) T is a type symbol defined with the type rule T <- [T1, T2, ..., Tn] 
%    and for some Ti infinite_type(T, [T|Seen]) succeds. 
% 5) T = f(T1, ..., Tk) and for some Ti infinite_type(Ti,Seen) succeds. 

is_infinite_type(Type):- 
   infinite_type(Type, []).

% infinite_type(Type, Seen)
% Type: a type. 
% Seen: a list of already proccessed type symbols which are defined by rules,
%       in the branch from the root.

infinite_type(Type, _Seen):- 
   computed_infinite_type(Type), !.
       % computed_infinite_type(Type) is a dynamic predicate to memoizing the
       % types we already know are infinite.
infinite_type(Type,  _Seen):-
   (top_type(Type); base_type_symbol(Type)), !.
infinite_type(Type,  Seen):- 
     rule_type_symbol(Type), member_0(Type, Seen), !,
     asserta_fact(computed_infinite_type(Type)).
infinite_type(Type,  Seen):- 
   em_defined_type_symbol(Type, TypUnion),!,
   infinite_type_union(TypUnion,  [Type|Seen]),
   asserta_fact(computed_infinite_type(Type)).
infinite_type(Type,  Seen):-
  compound_pure_type_term(Type, Term, _Name, Arity),
  !,
  type_arg_infinite(Arity, Term, Seen).

infinite_type_union([Type|TypUnion], Seen):-
  (infinite_type(Type,  Seen) -> asserta_fact(computed_infinite_type(Type));
  infinite_type_union(TypUnion,  Seen)).  

type_arg_infinite(Arg_Num, Type,  Seen):-
      Arg_Num > 0,  
      arg(Arg_Num, Type, Arg),
     (infinite_type(Arg,  Seen) -> true;
         NArg_Num is Arg_Num - 1,
         type_arg_infinite(NArg_Num, Type,  Seen)).

% g_is_infinite_type(Type)
% Succeeds iff the type Type is infinite, i.e., the same as 
% is_infinite_type(Type) but with the following preconditions:
% Preconditions:
%  1) T is not empty.
%  2) For all rule T <- [T1, T2, ..., Tn] in the common set of rules,  
%     Ti is not empty.
%
% g_infinite_type(T, Seen) is true iff:
% 1) T is top.
% 2) T is base type symbol.
% 3) T is a type symbol in Seen.
% 4) T is a type symbol defined with the type rule T <- [T1, T2, ..., Tn] 
%    and for some Ti infinite_type(T, [T|Seen]) succeds. 
% 5) T = f(T1, ..., Tk) and for some Ti infinite_type(Ti,Seen) succeds. 

%% g_is_infinite_type(Type):- 
%%    g_infinite_type(Type, [], _Flag).
%% 
%% % g_infinite_type(Type,  Seen, Flag)
%% % Type: a type. 
%% % Seen: a list of already proccessed type symbols which are defined by rules,
%% %       in the branch from the root.
%% % Flag: is bounded to "true" (a ground value), when we have "passed through" a 
%% %       functor in the branch from the root.
%% 
%% g_infinite_type(Type,  _Seen, _Flag):-
%%    (top_type(Type); base_type_symbol(Type)), !.
%% g_infinite_type(Type, _Seen, _Flag):- 
%%    computed_infinite_type(Type), !.
%%        % computed_infinite_type(Type) is a dynamic predicate to memoizing the
%%        % types we already know are infinite.
%% g_infinite_type(Type,  Seen, Flag):- 
%%      rule_type_symbol(Type), member_0(Type, Seen), !,
%%      nonvar(Flag), asserta_fact(computed_infinite_type(Type)).
%% g_infinite_type(Type,  Seen, Flag):- 
%%    em_defined_type_symbol(Type, TypUnion),!,
%%    g_infinite_type_union(TypUnion,  [Type|Seen], Flag),
%%    asserta_fact(computed_infinite_type(Type)).
%% g_infinite_type(Type,  Seen, _Flag):-
%%   compound_pure_type_term(Type, Term, _Name, Arity),
%%   !,
%%   g_type_arg_infinite(Arity, Term, Seen, true).
%% 
%% g_infinite_type_union([Type|TypUnion], Seen, Flag):-
%%   (g_infinite_type(Type,  Seen, Flag) -> 
%%        asserta_fact(computed_infinite_type(Type));
%%        g_infinite_type_union(TypUnion,  Seen, Flag)).  
%% 
%% g_type_arg_infinite(Arg_Num, Type,  Seen, Flag):-
%%       Arg_Num > 0,  
%%       arg(Arg_Num, Type, Arg),
%%      (g_infinite_type(Arg,  Seen, Flag) -> true;
%%          NArg_Num is Arg_Num - 1,
%%          g_type_arg_infinite(NArg_Num, Type,  Seen, Flag)).

% END OF CHECKING INFINITE TYPES.


% =======================================================================

% CHECKING TYPE MEMBERSHIP.

belongs_to_type(Term, Type):-
    escaped_type(Term, TypeTerm),
    dz_type_included(TypeTerm, Type).

create_new_type_rule(TypeList, TypeSymbol):-
    new_type_symbol(TypeSymbol),
    insert_rule(TypeSymbol, TypeList).

 %% find_type_functor(+F/+A, +Type, -Type1, -RestTypes).
 %% F/A: functor/arity of the subtype searched.
 %% Type: Type in which the subtype is searched.
 %% Type1: subtype of Type with functor/arity F/A.
 %% RestTypes: rest of types in the definition of Type. It's a list.
 %% Preconditions:
 %% TermAri > 0
 %% Comments: Type1 and the types in RestTypes are a partition of Type
 %%           (this means that they are disjoint). Fails if there is
 %%           no subtype which is a compound pure type term in Type,
 %%           in particular, if type is top, bottom, or a base type symbol.
 %%          
 %%  IMPORTANT: It is possible to write an specialized version asuming
 %%  that the rules are unfolded (or simplified without bottom, and
 %%  top). This version which does not expand the user defined type symbols.

find_type_functor(_, Type, Seen, _, _):-
   rule_type_symbol(Type), member_0(Type, Seen), 
   !, 
   fail.
find_type_functor(TermFun/TermAri, Type, _Seen, Type, []):-
   TermAri =:= 0,
   constant_symbol(Type, TermFun),
   !. 
find_type_functor(TermFun/TermAri, Type, _Seen, Type, []):-
   compound_pure_type_term(Type, _Term, TermFun, TermAri),
   !.
find_type_functor(TermFun/TermAri, Type, Seen, Type1, RestTypes):-
   em_defined_type_symbol(Type, Def), 
   !,
   find_type_funct_in_list(Def, TermFun/TermAri, [Type|Seen], Type1, 
   RestTypes).

find_type_funct_in_list([Type|TypUnion], TermFun/TermAri, Seen, Type1,
                        RestTypes):-
  find_type_functor(TermFun/TermAri, Type, Seen, Type1, RTypes)
    -> append(RTypes, TypUnion, RestTypes)  
    ;  find_type_funct_in_list(TypUnion, TermFun/TermAri, Seen, Type1,
       ReTypes), RestTypes  = [Type|ReTypes].

 %% Specialized version:
 %% 
 %% find_type_functor(TermFun/TermAri, Type, Seen, Type, []):-
 %%    functor_pure_type_term(Type), functor(Type, TermFun, TermAri), !.
 %% find_type_functor(TermFun/TermAri, Type, Seen, Type1, RestTypes):-
 %%    em_defined_type_symbol(Type, Def), !,
 %%    find_type_funct_in_list(Def, TermFun/TermAri, [Type|Seen], Type1, 
 %%    RestTypes).
 %% 
 %% find_type_functor_1(TermFun/TermAri, Type, Seen, Type, []):-
 %%    functor_pure_type_term(Type), functor(Type, TermFun, TermAri), !.
 %% 
 %% find_type_funct_in_list([Type|TypUnion], TermFun/TermAri, Seen, Type1,
 %%                         RestTypes):-
 %%   find_type_functor_1(TermFun/TermAri, Type, Seen, Type1, RTypes)
 %%     -> append(RTypes, TypUnion, RestTypes)  
 %%     ;  find_type_funct_in_list(TypUnion, TermFun/TermAri, Seen, Type1,
 %%        ReTypes), RestTypes  = [Type|ReTypes].
 %% 

% Type define a (possibly) infinite set of ground terms.

is_ground_type(Type):- 
   is_ground_type_2(Type, [], _).

is_ground_type_2(Type,  Seen, Seen):-
   type_included_in_ground(Type),
   !.
is_ground_type_2(Type,  Seen, NewSeen):-
   compound_pure_type_term(Type, Term, _Name, Arity),
   !,
   all_args_ground_type(Arity, Term, Seen, NewSeen).
is_ground_type_2(Type,  Seen, Seen):- 
   rule_type_symbol(Type), 
   member_0(Type, Seen), 
   !.
is_ground_type_2(Type,  Seen, NewSeen):- 
   em_defined_type_symbol(Type, TypUnion),
   !,
   is_ground_type_union(TypUnion,  [Type|Seen], NewSeen).

is_ground_type_union([Type|TypUnion], Seen, NewSeen):-
  !,
  is_ground_type_2(Type,  Seen, TempSeen),
  is_ground_type_union(TypUnion,  TempSeen, NewSeen).  
is_ground_type_union([], Seen, Seen).

all_args_ground_type(0, _Term, Seen, Seen) :- !.
all_args_ground_type(A, Term, Seen, NewSeen):-
       A > 0,
       arg(A, Term, Arg),
       is_ground_type_2(Arg, Seen, TempSeen),
       NA is A - 1,
       all_args_ground_type(NA, Term, TempSeen, NewSeen).

% END ADDED FOR NON-FAILURE

% Are not used at moment.


% retract_1 :-
 %%    recent_created_type_symbols(TypSymbol_List),
 %%    retract_2(TypSymbol_List).

 %% retract_2([]).
 %% retract_2(TypSymbol_List):-
 %%    retract_all_computed_type_rules,

 %% When a type symbol is created, it isasserted as a created type symbol.
 %% This allows us to perform a selective simplification/deletion of
 %% type rules.


 %% memo_intersec_types(Typ1, Typ2, Intersec):-
 %%   (computed_type_intersection(Typ1, Typ2, Intersec) -> true;
 %%         type_intersection(Typ1, Typ2, Intersec),
 %%         asserta(computed_type_intersection(Typ1, Typ2, Intersec))).

% asserta(computed_type_intersec(Typ1, Typ2, Intersec))

 
%* End 29 Oct 97

% =======================================================================

%  Simplification of equivalent types.

dz_equivalent_rules(Rule1, Rule):-
  get_rule_type_predicate(Rule1, Pred1),
  get_rule_type_predicate(Rule, Pred),
  (equiv_type(Pred1, Pred) ; equiv_type(Pred, Pred1)), !.
dz_equivalent_rules(Rule1, Rule):- 
  get_rule_type_symbol(Rule1, TypeSymbol1),
  get_rule_type_symbol(Rule, TypeSymbol),
  dz_equivalent_types(TypeSymbol1, TypeSymbol).


%------------------------------------------------------------------------%
 %% simplify_type_rules(+InRules, -OutRules, -Equiv_Types)
 %% Purpose: Performs simplification of type rules.
 %% Input:  a list of type rules InRules.
 %% Output: 
 %%       a list of type rules OutRules and a list of type equivalences
 %%       Equiv_Types.
 %%       Equiv_Types is a list of items of the form: equiv_type(Type1, Type2),
 %%       where Type1 and Type2 are type symbols. The item represents that 
 %%       Type1 and Type2 are equivalent, and that Type2 is the
 %%       "canonical" form of Type1 (i.e. Type1 is replaced by Type2 in
 %%       all of its occurrences).
 %% 
 %% A sample input list:
 %% 
 %%          [
 %%            (typedef t1 ::= f(t1) ; ^a),
 %%            (typedef t2 ::= ^a ; f(t2)), 
 %%            (typedef t3 ::= ^a ; f(t3)), 
 %%            (typedef t4 ::= ^b ; f(t3) ; f(t1)),
 %%            (typedef t5 ::= ^a ; ^b; f(t5); f(t3) ; f(t2)), 
 %%            (typedef t6 ::= ^a ; f(t1) ; t3), 
 %%            (typedef t7 ::= var; f(t7)),
 %%            (typedef t8 ::= f(t8); var), 
 %%            (typedef t9 ::= ^a ; f(t9) ; t8 ; f(t7) ; var) 
 %%          ]


% full_simplify_type_rules(-OutRules, -Equiv_Types)
 %% full_simplify_type_rules(OutRules, Equiv_Types):-
 %%         bot_type_rule_simplify,
 %%         findall(typedef(TypSymbol, Defin), typedef(TypSymbol, Defin), 
 %%                         InputRules),
 %%         actualize_rules(InputRules),
 %%         unfold_type_rules(InputRules, [], Unfolded_Rules),        
 %%         rever_and_actualize_rules(Unfolded_Rules, AcUnfolded_Rules),
 %%         delete_and_colapse_rules(BuilTypes, InputRules, SimpRules),
 %%         simplify_equiv_types(AcUnfolded_Rules, SimpRules2),
 %%         replace_all_equiv_types_in_rules(SimpRules2, SimpRules3),
 %%         actualize_rules(SimpRules3),
 %%         remove_redundant_simplification(SimpRules3, SimpRules4),
 %%         replace_single_types(SimpRules4, SimpRules4, Rules5),
 %%         actualize_rules(Rules5),
 %%         findall(equiv_type(X, Y), equiv_type(X, Y), Equiv_Types).

%% simplify_type_rules(InRules, OutRules, Equiv_Types) :-
%%         undoall_type_equivs,
%%         retractall_fact(pgm_typedef(_, _)),
%%         translate_rule_list_to_internal(InputRules, InRules), 
%%         actualize_rules(InputRules),
%%         unfold_type_rules(InputRules, [], Unfolded_Rules),        
%%         rever_and_actualize_rules(Unfolded_Rules, AcUnfolded_Rules),
%% %        delete_and_colapse_rules(BuilTypes, InputRules, SimpRules),
%%         simplify_equiv_types(AcUnfolded_Rules, SimpRules2),
%%         replace_all_equiv_types_in_rules(SimpRules2, SimpRules3),
%%         actualize_rules(SimpRules3),
%%         remove_redundant_simplification(SimpRules3, SimpRules4),
%%         replace_all_single_types(SimpRules4, Rules5),
%%         translate_rule_list_to_internal(Rules5, OutRules),
%%         actualize_rules(Rules5),
%%         findall(equiv_type(X, Y), equiv_type(X, Y), Equiv_Types).
%% 
%% slow_full_simplified_type_included(Type1, Type2, InRules, Res, OutRules):-
%%        simplify_type_rules(InRules, OutRules, _Equiv_Types),
%%        replace_equiv_type_symbol(Type1, NType1), 
%%        replace_equiv_type_symbol(Type2, NType2), 
%%        (dz_type_included(NType1, NType2) -> Res = yes ; Res = no).
%% 
%% faster_unfolded_type_included(Type1, Type2, InRules, Res, OutRules):-
%%          undoall_type_equivs,
%%          retractall_fact(pgm_typedef(_, _)),
%%          translate_rule_list_to_internal(InputRules, InRules), 
%%          actualize_rules(InputRules),
%%          unfold_type_rules(InputRules, [], Unfolded_Rules), 
%%          translate_rule_list_to_internal(Unfolded_Rules, OutRules),
%%          actualize_rules(Unfolded_Rules),       
%%         (dz_type_included(Type1, Type2) -> Res = yes ; Res = no).
%% 
%% replace_equiv_type_symbol(X, Y):- 
%%    functor(X, F, Ar),
%%    functor(Y, F, Ar),
%%    arg(1, X, A),	
%%    (equiv_type(A, B)
%%      -> arg(1, Y, B)
%%       ; arg(1, Y, A)).
%% 
%%  %% unfolded_type_included(Type1, Type2, InRules, Res, OutRules, Equiv_Types):-
%%  %%         undoall_type_equivs,
%%  %%         retractall(pgm_typedef(_, _)),
%%  %%         translate_rule_list_to_internal(InputRules, InRules), 
%%  %%         actualize_rules(InputRules),
%%  %%         unfold_type_rules(InputRules, [], Unfolded_Rules),        
%%  %%         rever_and_actualize_rules(Unfolded_Rules, AcUnfolded_Rules),
%%  %%         simplify_equiv_types(AcUnfolded_Rules, SimpRules2),
%%  %%         replace_all_equiv_types_in_rules(SimpRules2, SimpRules3),
%%  %%         actualize_rules(SimpRules3),
%%  %%         remove_redundant_simplification(SimpRules3, SimpRules4),
%%  %%         actualize_rules(SimpRules4),
%%  %%         (dz_type_included(Type1, Type2) -> Res = yes ; Res = no).
%%  %%         translate_rule_list_to_internal(SimpRules4, OutRules),
%%  %%         findall(equiv_type(X, Y), equiv_type(X, Y), Equiv_Types),
%% 
%% 
%% rever_and_actualize_rules(Rules, OuRules):-
%%        retractall_fact(pgm_typedef(_, _)),
%%        reverse_and_actualize_rules(Rules, [], OuRules).
%% 
%% reverse_and_actualize_rules([], Ac, Ac).
%% reverse_and_actualize_rules([typedef(Type,Def)|Rules], Ac, OuRules):-
%%  	asserta_fact(typedef(Type,Def)),
%%  	reverse_and_actualize_rules(Rules, [typedef(Type,Def)|Ac], OuRules).
%% 
%% 
%% %------------------------------------------------------------------------%
%% % Get a type term from a term and a typing of its variables
%% 
%% replace_vars_by_types([], InTerm, InTerm):- !.
%% replace_vars_by_types([ReplaceVar:Type|TypAss], InTerm, OuTerm):-
%%         replace_var_by_term(InTerm, ReplaceVar, Type, OuTerm1),
%% 	replace_vars_by_types(TypAss, OuTerm1, OuTerm).
%% 
%% %------------------------------------------------------------------------
%% replace_vars_in_term((A,Body),InTerm,OuTerm):- !,
%% 	replace_one_term(A,InTerm,OuTerm1),
%% 	replace_vars_in_term(Body,OuTerm1,OuTerm).
%% replace_vars_in_term(A,InTerm,OuTerm):-
%% 	replace_one_term(A,InTerm,OuTerm).
%% 
%% replace_one_term(A,InTerm,OuTerm):-
%% 	functor(A,Type,1),
%% 	arg(1,A,ReplaceVar),
%% 	internal_type_translate(ByTerm, Type),
%% 	replace_var_by_term(InTerm, ReplaceVar, ByTerm, OuTerm).
%% 
%% replace_vars_in_term_l([T|TypesL],Head,Type):-
%%         list_to_conj(TypesL,TypeBody,T),
%% 	replace_vars_in_term(TypeBody,Head,Type).
%% replace_vars_in_term_l([],Head,Head).


 %% replace_single_types([], Rules, Rules):-!.
 %% replace_single_types([Rule|Rules], InRules, OutRules):-
 %%      Rule = typedef(TypSymbol, Defin),
 %%      (  Defin = [D] ->
 %%         replace_one_type_in_rules(InRules, TypSymbol, D, AuxRules)
 %%         ;
 %%         AuxRules = InRules),
 %%     replace_single_types(Rules, AuxRules, OutRules).
 %% replace_one_type_in_rules([], _TypSymbol, _D, []):-!.
 %% replace_one_type_in_rules([Rule|InRules], TypSymbol, D, [ReRule|OutRules]):-
 %%        Rule = typedef(TypSym, Defin),
 %%        replace_var_by_term(Defin, TypSymbol, D, NDefin),
 %%        ReRule = typedef(TypSym, NDefin),
 %%        replace_one_type_in_rules(InRules, TypSymbol, D, OutRules).
