% (included from typeslib.pl)

%% :- module(regtype_rules,
%%      [ % type symbols
%%          internally_defined_type_symbol/2,
%%          legal_user_type_pred/1,
%%          new_type_symbol/1,
%%          new_param_type_symbol/1,
%%          rule_type_symbol/1,
%%          par_rule_type_symbol/1,
%%          non_par_rule_type_symbol/1,
%%          type_symbol/1
%% 
%% 
%%      ],
%%      [ assertions, basicmodes, regtypes ] ).
%% 
%% 
%% :- doc(module,"This module contains the operations required for a 
%%      lattice of regular types formed with the native types plus
%%      types defined by regular rules. Rules can also be parametric.").

% ========================================================================

:- regtype legal_user_type_pred(Prop)

# "@var{Prop} is a @tt{(possibly parametric) type} that can be defined
   by the user. @var{Prop} is the head of the predicate definition.".

legal_user_type_pred(Prop):-
   remove_first_argument(Prop, Type),
   rule_type_symbol(Type).

remove_first_argument(Prop, Type):-
  Prop=..[F,_|Args],
  Type=..[F|Args].


:- regtype rule_type_symbol(Type)

# "@var{Type} is a @tt{(possibly parametric) type symbol}  
   that should be defined by a (possibly parametric) type rule.".

rule_type_symbol(Type):-
   non_par_rule_type_symbol(Type)
 ; par_rule_type_symbol(Type).

% ========================================================================

% TYPE SYMBOL COUNTER OPERATIONS

:- data simplified_type_symbol_counter/1.
:- data typ_sym_counter/1.
:- data lib_typ_sym_counter/1. %% For libraries.

:- pred init_typ_symbol_counter 

# "Initializes the type symbol counter to zero.".

init_typ_symbol_counter:-
    %% create_prefix(RuleSet),
    lib_typ_sym_counter(Count), !,
    set_fact(typ_sym_counter(Count)).
init_typ_symbol_counter:-
    set_fact(typ_sym_counter(0)).

:- pred current_type_symbol_counter_value(-Count)

# "Instantiates @var{Count} to the current type symbol counter value,
if exists. Otherwise initializes the type symbol counter to zero, and
instantiates @var{Count} to it.".

current_type_symbol_counter_value(Count):-
   typ_sym_counter(Count), !.
current_type_symbol_counter_value(Count):-
   init_typ_symbol_counter,
   typ_sym_counter(Count).

:- pred new_type_symbol(-NewTyp)

# "Creates a new (non-parametric) type symbol (using the value of the
 type symbol counter) and instantiates @var{NewTyp} to it. The type
 symbol counter is incremented by 1.".

new_type_symbol(NewTyp):-
    current_type_symbol_counter_value(N),
%    typ_sym_counter(N),                    changed by Claudio
    !,
    retractall_fact(typ_sym_counter(_)),
    N1 is N + 1, 
    asserta_fact(typ_sym_counter(N1)),
    name(N, NName),
    append("rt", NName, TypName),
    name(NewTyp, TypName).

internally_defined_type_symbol(F,1):-
    atom(F),
    atom_concat(rt,N,F),
    atom_number(N,_),
    !.
internally_defined_type_symbol(F,1):-
    type_parameter(F).
    

:- pred new_param_type_symbol(-NewTyp)

# "Creates a new (parametric) type symbol (using the value of the type
 symbol counter) and instantiates @var{NewTyp} to it. The type symbol
 counter is incremented by 1.".

new_param_type_symbol(NewTyp):-
%    param_typ_sym_counter(N), !,
    get_last_type_symbol_counter(N), !,
    retractall_fact(param_typ_sym_counter(_)),
    N1 is N + 1, 
    asserta_fact(param_typ_sym_counter(N1)),
    name(N, NName),
    append("pt", NName, TypName),
    name(NewTyp, TypName).

is_param_type_symbol(F):-
    atom(F),
    atom_concat(pt,N,F),
    atom_number(N,_),
    !.

% TODO: see accept_type/1, add type props
is_user_defined_type_symbol(T) :- typeslib_is_user_type(T).

:- pred get_last_type_symbol_counter(-LastCount)

# "Get the last value (@var{LastCount}) of the counter used for
   creating type symbols for parametric type instances.".

get_last_type_symbol_counter(LastCount):-
   (param_typ_sym_counter(Count) 
      ->  LastCount = Count
%%      ;   LastCount = 0).
    ;
    initialize_type_symbol_counter,
    param_typ_sym_counter(LastCount)
   ).

:- pred initialize_type_symbol_counter

# "Initialize the counter used for creating type symbols for
   parametric type instances. If some parametric type instances
   corresponding to any builtin type have been created, then the value
   is taken from the module builtintables (via
   last_param_typ_sym_counter/1).  Otherwise, the counter is
   initialized to zero. Note: we define a builtin type as that
   appearing in any assertion of a builtin predicate".

initialize_type_symbol_counter:-
%%    retractall_fact(param_typ_sym_counter(_)),
%%    asserta_fact(param_typ_sym_counter(0)).
    (
        lib_param_typ_sym_counter(Count) ->
        set_fact(param_typ_sym_counter(Count))
    ;
        set_fact(param_typ_sym_counter(0))
    ).

%% Need this because sometimes (i.e., in btables) undoall is not called,
%% but the counter needs be initialized anyway

:- data param_typ_sym_counter/1.
%%param_typ_sym_counter(0).
:- data lib_param_typ_sym_counter/1. %% For libraries.

%% %----------------------------------------------
%% assert_simplified_type_symbol_counter:- 
%%     current_type_symbol_counter_value(Count),
%%     retractall_fact(simplified_type_symbol_counter(_)),  
%%     asserta_fact(simplified_type_symbol_counter(Count)).  
%% 
%% current_simplified_type_symbol_counter(Count):- 
%%     simplified_type_symbol_counter(Count),
%%     !.
%% current_simplified_type_symbol_counter(-1). % No simplification peformed yet.

%----------------------------------------------
% END OF TYPE SYMBOL COUNTER OPERATIONS

% CREATION OF TYPES.

%% % This gives the "analyzable" pred definitions of the basic types
%% % (whose intended definitions are in basictypes)
%% % Does not work!!!! (because of magic transformation)
%% basic_types_pred_defs(fdtypes,[]).
%% %% basic_types_pred_defs(fdtypes,
%% %%   [ (clause(term(_),true),clid),
%% %%     (clause(gnd(X),ground(X)),clid),
%% %%     (clause(num(X),number(X)),clid),
%% %%     (clause(atm(X),atom(X)),clid),
%% %%     (clause(flt(X),float(X)),clid),
%% %%     (clause(struct(X),compound(X)),clid),
%% %%   %??  (clause(var(X),var(X)),clid),
%% %%   % These four do belong in fdtypes
%% %%   % (clause(rat(X),??),clid),
%% %%   % (clause(int(X),??),clid),
%% %%   % (clause(nnegint(X),??),clid),
%% %%   % (clause(anyfd(X),??),clid),
%% %%     (clause(regtype(_,_),true),clid)
%% %%   ]).
%% 
%% basic_types_pred_defs(regtypes,
%%      [ (clause(term(_),true),clid),
%%        (clause(gnd(X),ground(X)),clid),
%%        (clause(num(X),number(X)),clid),
%%        (clause(atm(X),atom(X)),clid),
%%        (clause(flt(X),float(X)),clid),
%% %      (clause(struct(X),compound(X)),clid),  compund not a builtin
%%        (clause(struct(X),term(X)),clid),
%%        (clause(rat(X/Y),(integer(X),integer(Y))),clid),
%%        (clause(int(X),integer(X)),clid),
%%        (clause(nnegint(X),(integer(X),X>=0)),clid),
%%        (clause(anyfd(_),true),clid),
%%      % A VERY UGLY HACK, I KNOW (PBC)
%%        (clause('SYSCALL'(_),true),clid)
%%      ]).
%% 
%% basic_types_pred_defs(regtypes,
%%      [ (clause(term(_),true),clid),
%%        (clause(gnd(_),true),clid),
%%        (clause(num(_),true),clid),
%%        (clause(atm(_),true),clid),
%%        (clause(flt(_),true),clid),
%%        (clause(struct(_),true),clid),
%%        (clause(rat(X/Y),(integer(X),integer(Y))),clid),
%%        (clause(int(X),integer(X)),clid),
%%        (clause(nnegint(X),(integer(X),X>=0)),clid),
%%        (clause(anyfd(X),true),clid),
%%      % A VERY UGLY HACK, I KNOW (PBC)
%%        (clause('SYSCALL'(_),true),clid)
%%      ]).


% TYPE RULE REPRESENTATION AND RELATED PROCEDURES  

:- reexport(typeslib(typedef)).

% Change this? 
get_rule_type_predicate(typedef(TypSymbol, _Defin), TypSymbol).

get_rule_type_symbol(typedef(TypSymbol, _Defin), TypSymbol).

type_rule_symbol_def(TypeRule, TypeSymbol, Defin):-
   non_parametric_type_rule_symbol_def(TypeRule, TypeSymbol, Defin), !.
type_rule_symbol_def(TypeRule, TypeSymbol, Defin):-
   parametric_type_rule_symbol_def(TypeRule, TypeSymbol, Defin).

non_parametric_type_rule_symbol_def(typedef(TypSymbol, Defin), 
                                TypSymbol, Defin):-
   non_par_rule_type_symbol(TypSymbol).

parametric_type_rule_symbol_def(paramtypedef(TypSymbol, Defin), 
                            TypSymbol, Defin):-
   par_rule_type_symbol(TypSymbol).

%% %
%% %delete?
%% :- pred defined_type_symbol(+Type, -Defin)
%% 
%% # "If @var{Type} is a rule type symbol that is defined by an
%%    (asserted) type rule, then @var{Defin} is its definition. Otherwise
%%    @var{Defin} is bound to the atom @tt{nodef}. It always succeeds".
%% 
%% defined_type_symbol(Type, Defin):-
%%     (rule_type_symbol(Type) -> 
%%       (find_type_defin(Type, Defin1) -> 
%%                  Defin = Defin1; 
%%                  Defin = nodef)
%%      ; Defin = nodef).
%% 
%% :- pred get_NP_typedef_default_bot(+Type, -Defin)
%% 
%% # "If @var{Type} is a rule type symbol that is defined by an
%%    (asserted) type rule, then @var{Defin} is its definition. Otherwise
%%    find the definition of a type equivalent to @var{Type}. If there is
%%    not definition for none of the equivalent types, then a warning
%%    message is issued and the definition @var{Defin} is unified with
%%    the bottom type [bot].  It always succeeds".
%% 
%% get_NP_typedef_default_bot(Type, Defin):-
%%    (typedef(Type, Defin1) 
%%        -> Defin = Defin1
%%        ; (equiv_type(Type,Type1) % it might be equivalent to another! (PBC)
%%             -> get_NP_typedef_default_bot(Type1, Defin)
%%             ;  definition_not_found_default_bot(Type, Defin))).
%% 
%% definition_not_found_default_bot(Type, Defin):-
%%      Defin = [T],
%%      set_bottom_type(T),
%% %     warning_message("Type ~q not defined, assumed ~q", [Type, T]).
%%      Type=Type.
%% 
%% :- pred pp_find_type_defin(+Type, -Defin)
%% 
%% # "Finds the definition @var{Defin} of @var{Type} in the asserted type
%%    rules.  If there is no type rule defining @var{Type}, then gives a warning
%%    message and returns top type.".
%% 
%% pp_find_type_defin(TypeSymbol, Def):- 
%%    (typedef(TypeSymbol, Def)
%%      -> true
%%       ; definition_not_found(TypeSymbol, Def)).

%delete?
:- pred find_type_defin(+Type, -Defin)

# "Find the definition @var{Defin} of @var{Type} in the asserted type rules.
   If there is no defining type rule, then fails.".

find_type_defin(TypeSymbol, Def):- 
   typedef(TypeSymbol, Def). 

 %% get_NO_par_type_definition(Type, Defin):-
 %%    (typedef(Type, Defin1) 
 %%        -> Defin = Defin1
 %%        ; (equiv_type(Type,Type1) % it might be equivalent to another! (PBC)
 %%             -> get_NO_par_type_definition(Type1, Defin)
 %%             ; compiler_error(type_undefined(Type)),
 %% %             give any (PBC):
 %% %              Defin = nodef).
 %%           Defin = [G],
 %%           set_top_type(T),
 %%           functor(G,T,1),
 %%           arg(1,Type,X),
 %%           arg(1,T,X) )).

get_par_type_definition(Type, Defin):-
   findall(paramtypedef(Type, Defin2), paramtypedef(Type, Defin2), Rules),  
   (Rules = [] ->
       compiler_error(param_type_undefined(Type)),
       Defin = nodef
       ;
       Rules = [Rule1|Rest],
       (Rest = [] 
      -> true 
      ;  compiler_error(multiple_type_defin(Type))),
       type_rule_symbol_def(Rule1, Type, Defin)).

% exist_one_non_par_type_rule(TypeSymbol, Def):-
%      typedef(TypeSymbol, Def). 

:- pred em_defined_type_symbol(+Type, -Defin)

# "Succeeds if and only if @var{Type} is a rule type symbol that is
   defined by an (asserted) type rule and @var{Defin} is its
   definition.".


em_defined_type_symbol(Type, Defin):-
   rule_type_symbol(Type), find_type_defin(Type, Defin).

:- pred insert_rule(+TypeSymbol, +TypeDef)

=> non_par_rule_type_symbol * type_disjunction

# "Asserta a type rule defining @var{TypeSymbol} with the definition 
   @var{TypeDef}.".

insert_rule(TypeSymbol, TypeList):-
  % OLD 21-Dec-98 asserta(typedef(TypeSymbol, TypeList)).
  ( typedef(TypeSymbol,_) ->
    true
  ; assertz_fact(pgm_typedef(TypeSymbol, TypeList))
  ).

remove_rule(TypeSymbol) :-
    retract_fact(pgm_typedef(TypeSymbol, _)).

insert_user_type_pred_def(Prop, Clauses):-
  remove_first_argument(Prop, Type),
  insert_user_type_rule(Type, Clauses).

insert_user_type_rule(Type, Clauses):-
  pred2par_non_par_rule(Type, Clauses, TypeRule),
  assertz_typedef_or_paramtypedef(TypeRule),
  assertz_fact(pgm_user_type(Type)).

assertz_typedef_or_paramtypedef(typedef(TypeSymbol,TypeList)):-
  \+ typedef(TypeSymbol,_),
  assertz_fact(pgm_typedef(TypeSymbol,TypeList)), !.
assertz_typedef_or_paramtypedef(paramtypedef(TypeSymbol,TypeList)):-
  \+ paramtypedef(TypeSymbol,_),
  asserta_fact(pgm_paramtypedef(TypeSymbol,TypeList)).


:- data pgm_user_type/1. %% For user programs.
:- data lib_user_type/1. %% For libraries.

%% user_type(A):-
%%      pgm_user_type(A).
%% user_type(A):-
%%      lib_user_type(A).

insert_new_type_rule(TypeSymbol,  TypeList):-
  insert_rule(TypeSymbol, TypeList),
  asserta_fact(no_simplified_type(TypeSymbol)).

%% create_type_rule(TypeSymbol, TypeList, TypeRule):-
%%    TypeRule = typedef(TypeSymbol, TypeList).
%% 
%% get_symbol_defin_from_type_rule(TypeRule, TypeSymbol, Defin):-
%%    TypeRule = typedef(TypeSymbol, Defin).

%---------------------------------
% RETRACTION OF TYPE RULES 
%---------------------------------

:- pred retract_rule(+TypeSymbol)

=> non_par_rule_type_symbol

# "Retracts the type rule defining @var{TypeSymbol}.".

retract_rule(TypSymbol):-
   retract_fact(pgm_typedef(TypSymbol, _)),
   !.
retract_rule(_TypSymbol). % PLG Dec-6-2003
                      % If there is no type rule for TypSymbol, 
                      % then succeeds as before, but
                      % do not raise any error message.
 %% On Dec-6-2003 was:
 %% retract_rule(TypSymbol):-
 %%    error_message("In retract_rule/1: There is no type rule defining ~q. Failing.", 
 %%                  [TypSymbol]).

%
retract_rules([]).
retract_rules([TypSymbol|List]):-
    retract_rule(TypSymbol),
    retract_rules(List).
%
:- pred selective_retract_rules(+Rules)

=> type_rule_list

# "Retract the type rules defining the type symbols in @var{Rules}.".

selective_retract_rules([typedef(TypSymbol, _Defin)|Types]):-
    retract_rule(TypSymbol),
    selective_retract_rules(Types).
selective_retract_rules([]).

%---------------------------------
% MODIFICATION OF TYPE RULES 
% --------------------------------

assert_unfolded_rules([]).
assert_unfolded_rules([typedef(TypeSymbol, Def)|Rest]):-
   retractall_fact(pgm_typedef(TypeSymbol, _)),
   assertz_fact(pgm_typedef(TypeSymbol, Def)), % assertz or asserta?
   assert_unfolded_rules(Rest).

actualize_rules(RuleList):-
    retract_all_type_rules,
    asserta_type_rule_list(RuleList).

retract_all_type_rules:-
    retractall_fact(pgm_typedef(_, _)). 

%-----------------------------------
% ASSERTION OF TYPE RULES 
% ----------------------------------

:- pred asserta_type_rule_list(+Rules)

# "Asserta the type rules in @var{Rules}.".

asserta_type_rule_list([typedef(Type, Def)|Types]):-
%       assertz_fact(pgm_typedef(Type, Def)),
    insert_rule(Type, Def),
    asserta_type_rule_list(Types).
asserta_type_rule_list([]).

assert_rules_if_not_exist([typedef(Type, Def)|Types]):-
       ( (typedef(Type, _) ; type_parameter(Type))
     -> true
      ; assertz_fact(pgm_typedef(Type, Def))),
    assert_rules_if_not_exist(Types).
assert_rules_if_not_exist([]).

%---------------------------------
% CONSULT OF TYPE RULES 
%---------------------------------

:- pred get_type_definition(+Type, -Defin)

# "If @var{Type} is a rule type symbol that is defined by an
   (asserted) type rule, then @var{Defin} is its definition. Otherwise
   find the definition of a type equivalent to @var{Type}. If there is
   not definition for none of the equivalent types, then a warning
   message is issued and the definition @var{Defin} is unified with
   the bottom type [bot].  It always succeeds".

%pp:
get_type_definition(Type, Defin):-
    type_parameter(Type),!,
    ( param_matching_mode(off) ->
      typedef(Type, Defin)
    ; Defin = [Type]
    ).
get_type_definition(Type, Defin):-
   non_par_rule_type_symbol(Type),
   !,
   get_NO_par_type_definition(Type, Defin).
get_type_definition(Type, Defin):-
   par_rule_type_symbol(Type),
   get_par_type_definition(Type, Defin),!.

get_NO_par_type_definition(Type, Defin):-
   (typedef(Type, Defin1) 
       -> Defin = Defin1
       ; (equiv_type(Type,Type1) % it might be equivalent to another! (PBC)
                             % This shouldn't be necessary if all type symbols
                             % were replaced by their representants in the 
                             % correspondig equivalence class. PLG
         -> get_type_definition(Type1, Defin)
        ;  definition_not_found(Type, Defin))).

definition_not_found(Type, Defin):-
     Defin = [T],
     % set_top_type(T), %% PLG Dec-6-2003
     set_bottom_type(T), %% Now, a type symbol with no defining type rule is considered empty
                     %% (bottom).
%     warning_message("Type ~q not defined, assumed ~q", [Type, T]).
      Type = Type.
%

% Is this used? PLG
get_type_rule(Type,Rule):-
    typedef(Type, Rule).
get_type_rule(Type,Rule):-
    paramtypedef(Type, Rule).
%

:- pred get_type_rules(-Rules)

# "Gets all the non-parametric type rules currently in the database.".

get_type_rules(Rules):-
    findall(typedef(X, Y), typedef(X, Y), Rules).

get_type_rules_pgm(Rules):-
    findall(typedef(X, Y), pgm_typedef(X, Y), Rules).

get_analysis_types(TypeRuleList):-
    findall(typedef(TypSymbol, Def),
       (typedef(TypSymbol, Def), 
         ( internally_defined_type_symbol(TypSymbol,1)
         ; type_parameter(TypSymbol)
%            ; param_type_symbol_renaming(_,TypSymbol)
         )
       ),
       TypeRuleList).

%% get_no_simplified_rules(Count, TypeRules):-
%%    Count =:= -1, % None type rule is simplified.
%%    !,
%%    get_analysis_types(TypeRules).
%% get_no_simplified_rules(Count, TypeRules):-
%%    current_type_symbol_counter_value(TypeSymbCount),
%%    TypeSymbCount =:= Count, % No type rule was created since last simplification.
%%    !,
%%    TypeRules = [].
%% get_no_simplified_rules(Count, TypeRules):-
%%     findall(typedef(TypSymbol, Def),
%%            (typedef(TypSymbol, Def), no_simplified_rule(TypSymbol, Count)),
%%             TypeRules).
%% 
%% no_simplified_rule(TypeSymbol, Count):-
%%    atom_concat(rt, N, TypeSymbol),
%%    atom_codes(N, S), 
%%    number_codes(Num, S), 
%%    !,
%%    Num >= Count.

get_type_symbols([typedef(Type, _Defin)|Rules], [Type|Types]):-
     get_type_symbols(Rules, Types).
get_type_symbols([], []).

%---------------------------------
% END OF CONSULT OF TYPE RULES 
%---------------------------------

%% :- pred get_param_type_symbol_renamings/1
%%      # "Gets all equivalences of parametric type instances 
%%            to nonparametric types currently in the database.".
%% 
%% get_param_type_symbol_renamings(PEquivs):-
%%      findall(param_type_symbol_renaming(X, Y),
%%              param_type_symbol_renaming(X, Y),
%%              PEquivs).

get_type_symbols_instances_of_parametric_types(Types):- 
    findall(NPartyp,
            (param_type_symbol_renaming(_ParTyp, NPartyp),
            typedef(NPartyp, _Def)),    
            Types).

:- pred get_parametric_type_rules(-Rules)

# "Gets all the parametric type rules currently in the database.".

get_parametric_type_rules(Rules):-
    findall(paramtypedef(X, Y), paramtypedef(X, Y), Rules).

%% :- pred get_nonparametric_type_rules(-Rules)
%% 
%% # "Gets all the non-parametric type rules currently in the database.".
%% 
%% get_nonparametric_type_rules(Rules):-
%%         findall(typedef(X, Y), typedef(X, Y), Rules).

:- pred get_type_defs(-Rules)

# "Gets all the non-parametric type rules currently in the database
  and rewites them into external(i.e. pretty) format.".

get_type_defs(TypeDefs):-
    findall(typedef(X, Y), typedef(X, Y), Rules),
    translate_rule_list(Rules,TypeDefs).

translate_rule_list([Rule|Rules],[(:- NewRule)|TypeDefs]):-
    internal_rule_translate(Rule, NewRule),
    translate_rule_list(Rules, TypeDefs).
translate_rule_list([],[]).

