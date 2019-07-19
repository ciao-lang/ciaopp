
 %% assert_type_lattice(Lattice):-
 %%    (Lattice == fdtypes ; Lattice == regtypes),
 %%    retractall(current_type_lattice(_)),
 %%    assert(current_type_lattice(Lattice)).   

is_not_a_type_symbol(Type):- \+ rule_type_symbol(Type).

%% :- dynamic(current_type_lattice/1).

%% % Perform simplification of type definitions.
%% 
%% simplify_typedefs(AutoTypes, NewRules):-
%%         % Table are the definitions of Gallager's types in predicate format.
%%         % remove_unnecessary_types(Table, AutoTypes),
%%         get_type_rules(No_Simp_NoAutoRules), % get all the rules currently in the database
%%         %
%%         % To activate decomment call with simplify.
%%         % debug_message("Checking no auto empty types ..."),
%%         simplify_no_auto_rules(simplify, No_Simp_NoAutoRules, NoAutoRules),
%%         % simplify_no_auto_rules(no_simplify, No_Simp_NoAutoRules, NoAutoRules),
%%         % debug_message("Done checking of no auto empty types."),
%%         %
%% 	%% PBC: put the code in here as a separate (exported) predicate
%%         debug_message("sintactically_simplify_typedefs_0(~q, ~q)", [AutoTypes, NewSimAutoRules]),
%%         sintactically_simplify_typedefs_0(AutoTypes, NewSimAutoRules),
%%         debug_message("sintactically_simplify_typedefs_0(~q, ~q)", [AutoTypes, NewSimAutoRules]),
%%         %
%%         put_par_type_renamings_first(NoAutoRules, NoAutoRules1),
%%         % Keep rules -PLG 29-March-94
%% %%jcf%        asserta_fact(pgm_types_used_to_colapse_others(NoAutoRules1)),
%% 	add_types_used_to_colapse_others(NoAutoRules1),
%%         %debug_message("delete_and_colapse_rules(~q, ~q, ~q)", [NoAutoRules1, 
%%         %                                        NewSimAutoRules, AutoRules1]),
%%         delete_and_colapse_rules(NoAutoRules1, NewSimAutoRules, AutoRules1),
%%         %debug_message("delete_and_colapse_rules(~q, ~q, ~q)", [NoAutoRules1, 
%%         %                                        NewSimAutoRules, AutoRules1]),
%%         %debug_message("delete_and_colapse_rules_1(~q, ~q)", [AutoRules1, AutoRules4]), 
%%         delete_and_colapse_rules_1(AutoRules1, AutoRules4),
%%         %debug_message("delete_and_colapse_rules_1(~q, ~q)", [AutoRules1, AutoRules4]), 
%%         retract_and_assert_rules(AutoRules4),
%%         %here
%%         % remove_redundant_simplification(AutoRules4, Rules5),
%%         %debug_message("remove_redundant_simplification(~q, ~q)", [AutoRules4, SimpRules4]),
%%         remove_redundant_simplification(AutoRules4, SimpRules4),
%%         %debug_message("remove_redundant_simplification(~q, ~q)", [AutoRules4, SimpRules4]),
%% % OLD  replace_all_single_types(SimpRules4, Rules5) loops
%%           % SimpRules4 = Rules5,          
%%         replace_all_single_types(SimpRules4, Rules5),
%%         selective_retract_rules(NewSimAutoRules),
%%           asserta_type_rule_list(Rules5),
%%           get_parametric_type_rules(ParRules),
%%           %debug_message("rewrite_as_parametric_rules(~q, ~q, ~q)", [Rules5, ParRules, TypeSymbols]),
%%           rewrite_as_parametric_rules(Rules5, ParRules, TypeSymbols),
%%           %debug_message("rewrite_as_parametric_rules(~q, ~q, ~q)", [Rules5, ParRules, TypeSymbols]),
%%           % replace_all_single_types(Rules5, Rules7),
%%           select_rules(Rules5, TypeSymbols, Rules6), 
%%           replace_all_equiv_types_in_rules(Rules6, RenRules6),
%%           selective_retract_rules(Rules5),
%%           asserta_type_rule_list(RenRules6),
%%           % Treatment of renaming rules. 
%%           get_all_renaming_rules(RenamingRules),
%%           replace_all_equiv_types_in_rules(RenamingRules, NewRenamingRules),
%%           selective_retract_rules(RenamingRules),
%%           asserta_type_rule_list(NewRenamingRules),
%%           %
%%           replace_all_equiv_types_in_renamings,
%%           unfold_all_types_in_renamings,
%%           replace_all_non_par_types_in_rules(RenRules6, NewRules).
%%         % This is not necessary since it is supposed that the non-parametric 
%%         % which are a renaming of a parametric type rule instance are at the beginning 
%%         % in the list of non-parametric type rules.
%%         % actualize_parametric_type_renamings.
%% 
%%  %% get_pretty_typedefs([TypeSymbol|List], [OuTypeRule|RList]):-
%%  %%         get_type_definition(TypeSymbol, TypeRule1),
%%  %%         simplify_some_typedefs([TypeRule1], [OuTypeRuleList),
%%  %%         get_pretty_typedefs(List, RList).
%%  %% get_pretty_typedefs([], []).
%% 
%% get_pretty_typedefs(TypeSymbolList, TypeRuleList):-
%%         compute_transitive_closure(TypeSymbolList, [], TransClosure),
%%         select_rules_2(TransClosure, RuleList),
%%         simplify_some_typedefs(RuleList, TypeRuleList).

type_rule_diff(TypeRules, NoAutoRules, NoAutoRules1):-
        subtract(TypeRules, NoAutoRules, NoAutoRules1).

:- data types_used_to_colapse_others/1.     %% both user and library types!!
:- data lib_types_used_to_colapse_others/1. %% only library types.
:- data type_symbols_used_to_colapse_others/1.     %% both user and library types!!
:- data lib_type_symbols_used_to_colapse_others/1. %% only library types.

%% It is assumed that L contains the list with *all* types
%% obtained from the user program.
add_types_used_to_colapse_others(L):-
	lib_types_used_to_colapse_others(LLib0),
	!,
	append(L,LLib0,LLib),
	set_fact(types_used_to_colapse_others(LLib)).
add_types_used_to_colapse_others(L):-
	set_fact(types_used_to_colapse_others(L)).

%% It is assumed that L contains the list with *all* types
%% obtained from the user program.
add_type_symbols_used_to_colapse_others(L):-
	lib_type_symbols_used_to_colapse_others(LLib0),
	!,
	append(L,LLib0,LLib),
	set_fact(type_symbols_used_to_colapse_others(LLib)).
add_type_symbols_used_to_colapse_others(L):-
	set_fact(type_symbols_used_to_colapse_others(L)).

%Rev
:- doc(simplify_step1,"Simplifies types in the database and records
	them to later use them to collapse other types to them.").

simplify_step1:-
        get_type_rules_pgm(No_Simp_NoAutoRules), % gets all typedef's
        simplify_no_auto_rules(simplify, No_Simp_NoAutoRules, NoAutoRules),
        % asserta_fact(module_types(NoAutoRules)), % PLG
        partition_par_type_renamings(NoAutoRules, _RenamingRules, NoAutoRules2),
        % put_par_type_renamings_first(NoAutoRules, NoAutoRules1),
	put_user_types_first(NoAutoRules2, NoAutoRules1),

        add_types_used_to_colapse_others(NoAutoRules1),
        get_type_symbols(NoAutoRules1, NoAutoTypes1),
	add_type_symbols_used_to_colapse_others(NoAutoTypes1).
%	retractall(pgm_typedef(_,_)).


:- doc(simplify_step2, "If @verb{type_output} flag value is
	@verb{all}, then simplifies types in the database by creating
	classes of equivalent types. All types in a class can then be
	collapsed to the canonical representative of the class. This
	one is chosen as follows: first, a parametric type, if there
	is one in the class; second, one of the types resulting from
	step1 of simplification, if there is one in the class; third,
	any type in the class.").

% Old version
 %% simplify_step2 :- 
 %%           get_type_rules(TypeRules),
 %%           simplify_some_typedefs(TypeRules, _NewRules).

% simplify_step2 :- select_simplify_step2. % cache + tabling version. PLG 
simplify_step2 :- tabling_simplify_step2. % tabling version. PLG 

% tabling version. PLG
tabling_simplify_step2 :-
    (current_pp_flag(type_output,defined) ->
        simplify_some_typedefs_user
        ; 
        get_analysis_types(TypeRules),
        % get_required_types(TypeRules), % PLG
        select_simplify_some_typedefs(TypeRules, _NewRules)
    ).

%% % cache + tabling version. PLG 
%% select_simplify_step2 :-
%%     current_simplified_type_symbol_counter(Count),
%%     (current_pp_flag(type_output,defined) ->
%%         simplify_some_typedefs_user
%%         ; 
%%         get_no_simplified_rules(Count, TypeRules),
%%         % get_required_types(TypeRules), % PLG
%%         select_simplify_some_typedefs(TypeRules, _NewRules)
%%     ),
%%     assert_simplified_type_symbol_counter.   

% Simplification with cache. % PLG
% select_simplify_some_typedefs([], []):-!.
select_simplify_some_typedefs(TypeRules, NewRules):-
        get_preprocessing_unit_type_rules(NoAutoRules),
        simplify_some_typedefs_(NoAutoRules, TypeRules, NewRules).

get_preprocessing_unit_type_rules(NoAutoRules):-
        types_used_to_colapse_others(NoAutoRules1),
        findall(typedef(NPartyp, Def),
                (param_type_symbol_renaming(_ParTyp, NPartyp),
                typedef(NPartyp, Def)),    
                NoAutoRules0),
        append(NoAutoRules0, NoAutoRules1, NoAutoRules).

simplify_some_typedefs(TypeRules, NewRules):-
        get_preprocessing_unit_type_rules(NoAutoRules),
        type_rule_diff(TypeRules, NoAutoRules, NewSimAutoRules),
        simplify_some_typedefs_(NoAutoRules, NewSimAutoRules, NewRules).
 
simplify_some_typedefs_(NoAutoRules, NewSimAutoRules, NewRules):-
        delete_and_colapse_rules(NoAutoRules, NewSimAutoRules, AutoRules1),
        delete_and_colapse_rules_1(AutoRules1, AutoRules4),
        retract_and_assert_rules(AutoRules4),
        remove_redundant_simplification(AutoRules4, SimpRules4),
        replace_all_single_types(SimpRules4, Rules5),
        selective_retract_rules(NewSimAutoRules),
        asserta_type_rule_list(Rules5),
        get_parametric_type_rules(ParRules),
        rewrite_as_parametric_rules(Rules5, ParRules, TypeSymbols),
        select_rules(Rules5, TypeSymbols, Rules6), 
        replace_all_equiv_types_in_rules(Rules6, RenRules6),
        selective_retract_rules(Rules5),
        asserta_type_rule_list(RenRules6),
        % Treatment of renaming rules. 
        get_all_renaming_rules(RenamingRules),
        replace_all_equiv_types_in_rules(RenamingRules, NewRenamingRules),
        selective_retract_rules(RenamingRules),
        asserta_type_rule_list(NewRenamingRules),
        %
        replace_all_equiv_types_in_renamings,
        unfold_all_types_in_renamings,
        replace_all_non_par_types_in_rules(RenRules6, NewRules).
        % This is not necessary since it is supposed that the non-parametric 
        % which are a renaming of a parametric type rule instance are at the beginning 
        % in the list of non-parametric type rules.
        % actualize_parametric_type_renamings.

%-----------------------------------------------------------------------------------------
% Collapse types only to user types. PLG
 
simplify_some_typedefs_user :-
        get_module_types(P_Unit_Types),
        get_analysis_types(TypeRuleList),
        delete_and_colapse_rules_user(TypeRuleList, P_Unit_Types),
        selective_retract_rules(TypeRuleList),
        replace_all_equiv_types_in_renamings,
        unfold_all_types_in_renamings.
%        replace_all_non_par_types_in_rules(RenRules6, NewRules).

:- pred delete_and_colapse_rules_user(+Rules, +Types)

   # "Collapse the rules @var{Rules} with respect to @var{Types}. As a
     side effect, assert and propagate the type equivalences found
     during the process (e.g.  @verb{equiv_type(Type2, Type1)}).".

delete_and_colapse_rules_user([], _P_Unit_Types).
delete_and_colapse_rules_user([typedef(Symbol, _Def)|R], P_Unit_Types):-
     contain_this_type(P_Unit_Types,Symbol,Types),
     minimaltype(Types,Minimal),
     assert_and_propagate_type_equivalence(Symbol, Minimal),
     delete_and_colapse_rules_user(R, P_Unit_Types).

get_preprocessing_unit_types(P_Unit_Types):- 
    get_type_symbols_instances_of_parametric_types(ParTypes),
    type_symbols_used_to_colapse_others(NonParModuleTypes),
    append(ParTypes, NonParModuleTypes, P_Unit_Types). % parametric types first.

%-----------------------------------------------------------------------------------------

%% sintactically_simplify_typedefs(AutoTypes, NewRules):-
%%         get_type_rules(No_Simp_NoAutoRules), % get all the rules currently in the database
%%         % To activate decomment call with simplify.
%%         % debug_message("Checking no auto empty types ..."),
%%         simplify_no_auto_rules(simplify, No_Simp_NoAutoRules, NoAutoRules),
%%         % simplify_no_auto_rules(no_simplify, No_Simp_NoAutoRules, NoAutoRules),
%%         % debug_message("Done checking of no auto empty types."),
%%         put_par_type_renamings_first(NoAutoRules, NoAutoRules1),
%%         add_types_used_to_colapse_others(NoAutoRules1),
%%         debug_message("sintactically_simplify_typedefs_0(~q, ~q)", [AutoTypes, Rules1]),
%%         sintactically_simplify_typedefs_0(AutoTypes, Rules1),
%%         debug_message("sintactically_simplify_typedefs_0(~q, ~q)", [AutoTypes, Rules1]),
%%         translate_rule_list_to_internal(Rules1, NewRules).
%% 
%% :- pred sintactically_simplify_typedefs_0(+AutoTypes, -NewRules)
%% 
%% # "Perform a light (syntax level) simplification of auto types (those
%% types automatically inferred by Gallager's System).  The resulting
%% rules will be simplified afterwards using a more powerful (semantic
%% level) algorithm. We perform the syntax level simplification to obtain
%% an smaller set of rules so that the semantic level simplification is
%% more efficient. @var{NewRules} is a list of type rules such that some
%% types that are been found to be (sintactically, up to predicate
%% renamings) equivalent are been replaced by a representant. SIDE
%% EFFECTS: 1) asserta equiv_type(Type1,Type2), when find out that two
%% types are (sintactically, up to predicate renamings) equivalent (Type2
%% is the representant). 2) Asserts the unfolded versions of
%% @var{NewRules} asserted.".
%% 
%% sintactically_simplify_typedefs_0(AutoTypes, NewRules):-
%%         simplify_predicate_type_table(AutoTypes, SimAutoTypes, EquivSymbols),
%% 	% Asserta type equivalences. 
%%         recorda_equiv_types(EquivSymbols),
%%         translate_predicates_to_type_rules(SimAutoTypes, SimAutoRules),
%%         % Replace type symbols by the representative of the
%%         % corresponding equivalence class.
%%         replace_all_equiv_types_in_rules(SimAutoRules, NewRules),
%%         unfold_type_rules_0(NewRules).
%%         %% asserta_type_rule_list(NewRules).

%Rev
simplify_no_auto_rules(simplify, No_Simp_NoAutoRules, NoAutoRules):-
      !,
      retractall_fact(computed_empty_type(_)),
      check_and_remove_empty_types_1(No_Simp_NoAutoRules), % We can add an extra argument
      get_type_rules_pgm(AutoRules_1),   % AutoRules_1 to avoid this call to get_type_rules(AutoRules_1).
      unfold_type_rules_0(AutoRules_1),
      get_type_rules_pgm(AutoRules_2),
      remove_redundant_simplification(AutoRules_2, NoAutoRules),
      actualize_rules(NoAutoRules). % Retract all the existing rules (typedef's) and 
                                    % assert the rules in NoAutoRules.
      % get_type_rules(NoAutoRules).
simplify_no_auto_rules(no_simplify, Rules, Rules).

%%  %% NOTE: In the definitions of the non-parametric rules created to define
%%  %% non-parametric type symbols which are a renaming of a paramatric type
%%  %% symbol instance (i.e. those non-parametric type symbols which appear
%%  %% in a renaming of the form: 
%%  %%        param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb) )
%%  %% it can appear:
%%  %% 
%%  %%   1) Non-parametric type symbols defined by external rules.
%%  %%   2) Non-parametric type symbols defined by rules inferred by the type analysis.
%%  %%   3) Non-parametric type symbols in a renaming of the form:
%%  %%       param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb)
%%  %%   
%%  %% 
%%  %% Thus, is is neccessary to replace the types in the rules defining
%%  %% non-parametric renaming type symbol by the corresponding representant
%%  %% of the equivalence class.
%%  %% 
%%  %% However, external rules should be kept unmodified.
%% 
%%  %% NOTE: in the facts equiv_type(Type1, RepresentantType)
%%  %% 
%%  %%   A) Type1 is always a (non-parametric) type symbol inferred by the analysis.
%%  %%   B) RepresentantType can be a:
%%  %%     1) Non-parametric type symbol defined by external rules.
%%  %%     2) Non-parametric type symbol defined by rules inferred by the type analysis.
%%  %%     3) Non-parametric type symbol in a renaming of the form:
%%  %%         param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb)
%%  %% 
%%  %% Thus, after rewriting types rules as parametric, it is neccessary to
%%  %% replace equivalent types in the rules defining:
%%  %%     2) Non-parametric type symbol defined by rules inferred by the type analysis.
%%  %%     3) Non-parametric type symbol in a renaming of the form:
%%  %%         param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb)
%% 
%% 
%% :- pred put_par_type_renamings_first(+Rules, -OutRules)
%% 
%% # "Put the types symbols which are a renaming of a parameric type
%% instance at the begining.".
%% 
%% put_par_type_renamings_first(Rules, OutRules):-
%%    partition_par_type_renamings(Rules, RenamingRules, OtherRules),
%%    append(RenamingRules, OtherRules, OutRules).

partition_par_type_renamings([], [], []):-!.
partition_par_type_renamings([NonParRule|Rules], [NonParRule|RenamingRules], OtherRules):-
     non_parametric_type_rule_symbol_def(NonParRule, NTypeSymbol, _NDefin),
     param_type_symbol_renaming(_ParTyp, NTypeSymbol), !,     
     partition_par_type_renamings(Rules, RenamingRules, OtherRules).
partition_par_type_renamings([NonParRule|Rules], RenamingRules, [NonParRule|OtherRules]):-
     partition_par_type_renamings(Rules, RenamingRules, OtherRules).

select_rules([], _TypeSymbols, []):-!.
select_rules([NonParRule|Rules], TypeSymbols, OutRules):-
       non_parametric_type_rule_symbol_def(NonParRule, NTypeSymbol, _NDefin),
       member_0(NTypeSymbol, TypeSymbols), !,     
       select_rules(Rules, TypeSymbols, OutRules).
select_rules([NonParRule|Rules], TypeSymbols, [NonParRule|OutRules]):-
       select_rules(Rules, TypeSymbols, OutRules).


get_all_renaming_rules(Rules):-
    findall(typedef(NPartyp, Def),
            (param_type_symbol_renaming(_ParTyp, NPartyp), typedef(NPartyp, Def)) ,
            Rules).       

%% actualize_parametric_type_renamings:-
%%        findall(pgm_param_type_symbol_renaming(ParTyp, NPartyp),
%%                 pgm_param_type_symbol_renaming(ParTyp, NPartyp),    
%%                 Renamings),
%%        actualize_all_renamings(Renamings). 
%% 
%% actualize_all_renamings([]).  
%% actualize_all_renamings([pgm_param_type_symbol_renaming(ParTyp, NPartyp)|Renamings]):-
%%      equiv_type_1(NPartyp, EquivNPartyp),
%%      retract_fact(pgm_param_type_symbol_renaming(ParTyp, NPartyp)),
%%      asserta_fact(pgm_param_type_symbol_renaming(ParTyp, EquivNPartyp)),
%%      actualize_all_renamings(Renamings).    

replace_all_equiv_types_in_renamings:-
       findall(pgm_param_type_symbol_renaming(ParTyp, NPartyp),
               pgm_param_type_symbol_renaming(ParTyp, NPartyp),    
               Renamings),
       replace_equivs_in_renamings(Renamings).

replace_equivs_in_renamings([]).  
replace_equivs_in_renamings([pgm_param_type_symbol_renaming(ParTyp, NPartyp)|Renamings]):-
     functor(ParTyp, F, A),
     functor(RParTyp, F, A),
     compound_replace_equiv_types(A, ParTyp, RParTyp),  
     retract_fact(pgm_param_type_symbol_renaming(ParTyp, NPartyp)),
     asserta_fact(pgm_param_type_symbol_renaming(RParTyp, NPartyp)),
     replace_equivs_in_renamings(Renamings).    


%

:- pred unfold_all_types_in_renamings

# "Remove all the renamings types in the facts:
    @verbatim{param_type_symbol_renaming(ParTyp, NPartyp)}.".

unfold_all_types_in_renamings:-
       findall(pgm_param_type_symbol_renaming(ParTyp, NPartyp),
               pgm_param_type_symbol_renaming(ParTyp, NPartyp),    
               Renamings),
       unfold_types_in_renamings(Renamings). 


unfold_types_in_renamings([]).  
unfold_types_in_renamings([pgm_param_type_symbol_renaming(ParTyp, NoPartyp)|Renamings]):-
     unfold_one_type_in_renaming(ParTyp, [NoPartyp], NewParTyp),
     retract_fact(pgm_param_type_symbol_renaming(ParTyp, NoPartyp)),
     asserta_fact(pgm_param_type_symbol_renaming(NewParTyp, NoPartyp)),
     unfold_types_in_renamings(Renamings).    

unfold_one_type_in_renaming(ParTyp, Seen, NewParTyp):-
     functor(ParTyp, F, A),
     functor(RParTyp, F, A),
     compound_unfold_renaming(A, ParTyp, Seen, RParTyp, NewSeen, Flag),
     %unfold_renaming(ParTyp, Seen, RParTyp, NewSeen, Flag),
     (var(Flag) -> 
         NewParTyp = RParTyp
         ; 
         unfold_one_type_in_renaming(RParTyp, NewSeen, NewParTyp)).

 %% unfold_one_type_in_renaming(ParTyp, NoPartyp, Seen, NewParTyp):-
 %%      functor(ParTyp, F, A),
 %%      functor(RParTyp, F, A),
 %%      compound_unfold_renaming(A, ParTyp, [NoPartyp], RParTyp, NewSeen, Flag),
 %%      (var(Flag) -> 
 %%          NewParTyp = RParTyp
 %%          ; 
 %%          unfold_one_type_in_renaming(RParTyp, NoPartyp, NewSeen, NewParTyp)).

unfold_renaming(Type, Seen, NType, [Type|Seen], true):-
   non_par_rule_type_symbol(Type), 
   param_type_symbol_renaming(ParType, Type),
   \+ member_0(Type, Seen), 
   !,
   NType = ParType.
unfold_renaming(Type, Seen, NType, NewSeen, Flag):-
   par_rule_type_symbol(Type),
   !,
   functor(Type, F, A),
   functor(NType, F, A),
   compound_unfold_renaming(A, Type, Seen, NType, NewSeen, Flag).
unfold_renaming(Type, Seen, NType, NewSeen, Flag):-
   compound_pure_type_term(Type, Comp, Name, Arity),
   !,
   functor(NComp, Name, Arity),
   compound_unfold_renaming(Arity, Comp, Seen, NComp, NewSeen, Flag), 
   construct_compound_pure_type_term(NComp, NType).
unfold_renaming(Type, Seen, Type, Seen, _Flag).
   
compound_unfold_renaming(0, _Comp, Seen, _NComp, Seen, _Flag):-!.
compound_unfold_renaming(ArgNum, Comp, Seen, NComp, NewSeen, Flag):-
       ArgNum > 0, 
       arg(ArgNum, Comp, Arg),
       unfold_renaming(Arg, Seen, NArg, TempSeen, Flag),
       arg(ArgNum, NComp, NArg),
       NArgNum is ArgNum - 1,
       compound_unfold_renaming(NArgNum, Comp, TempSeen, NComp, NewSeen, Flag).

% end
%Rev
:- pred delete_and_colapse_rules(+Rules1, +Rules2, -Rules3)

   => type_rule_list * type_rule_list * type_rule_list

   # "Colapse the rules @var{Rules2} with respect to @var{Rules1}
     yielding @var{Rules3}. As a side effect, assert and propagate the
     type equivalences found during the process (e.g. 
     @verb{equiv_type(Type2, Type1)}).".

:- regtype type_rule_list/1.

type_rule_list(A) :-
	list(A, type_rule).

:- regtype type_rule/1.

type_rule(typedef(A,B)) :-
	gnd(A),
	gnd(B).

delete_and_colapse_rules(RuleList, Rules, NewRuleList):-
   compare_and_simplify_rule_list(RuleList, Rules, Rules1),
   replace_all_equiv_types_in_rules(Rules1, NewRuleList).





compare_and_simplify_rule_list([], Rules, Rules).
compare_and_simplify_rule_list([Rule|RestRul], Rules, OuRules):-
   compare_and_delete_rule(Rules, Rule, NewRules),
   compare_and_simplify_rule_list(RestRul, NewRules, OuRules).

:- pred delete_and_colapse_rules_1(+Rules1, -Rules2)

=> type_rule_list * type_rule_list

# "Colapse the rules @var{Rules1} with respect to itself yielding
    @var{Rules2}. As a side effect, assert and propagate the type
    equivalences found during the process (e.g. 
     @verb{equiv_type(Type2, Type1)}).".  

delete_and_colapse_rules_1(AutoRules2, AutoRules4):-
        simplify_equiv_types(AutoRules2, AutoRules3),
        replace_all_equiv_types_in_rules(AutoRules3, AutoRules4).

simplify_equiv_types([], []).
simplify_equiv_types([Rule|RestRul], [Rule|OuRestRul]):-
   compare_and_delete_rule(RestRul, Rule, NewRules),
   simplify_equiv_types(NewRules, OuRestRul).


:- pred compare_and_delete_rule(+Rules, +Rule, -SimpRules)

   => type_rule_list * type_rule * type_rule_list

   # "@var{SimpRules} is @var{Rules} except all those type rules which
     are equivalent to @var{Rule}. As a side effect, assert and
     propagate the type equivalences found during the process.".

compare_and_delete_rule([], _, []).
compare_and_delete_rule([Rule1|Rest], Rule, SimpRules):-
  (dz_equivalent_rules(Rule1, Rule) -> 
           SimpRules = TemSimpRules,
           get_rule_type_predicate(Rule1, Pred1),
           get_rule_type_predicate(Rule, Pred),
           assert_and_propagate_type_equivalence(Pred1, Pred)
           ;
           SimpRules = [Rule1|TemSimpRules]),
   compare_and_delete_rule(Rest, Rule, TemSimpRules).

:- doc(bug, "Warning: check that the transitive closure is
computed in assert_and_propagate_type_equivalence/2.").

% Perhaps this is not neccessary.
assert_and_propagate_type_equivalence(Pred1, Pred):-
   findall(Pred2, equiv_type(Pred2, Pred1), L),
   assert_equivalence_type(L, Pred1, Pred),
   asserta_(equiv_type(Pred1, Pred)).

assert_equivalence_type([Type|Types], Pred1, Equiv):-
   retract_fact(pgm_equiv_type(Type, Pred1)),
   asserta_(equiv_type(Type, Equiv)),
   assert_equivalence_type(Types, Pred1, Equiv).
assert_equivalence_type([],_, _).

%% :- pred recorda_equiv_types(+EquivSymbols)
%% 
%%   # "Asserta type equivalences in @var{EquivSymbols}.".
%% 
%% recorda_equiv_types([st(Equiv,Types)|EquivSymbols]):-
%% 	recorda_equiv_types_table(Types,Equiv),
%% 	recorda_equiv_types(EquivSymbols).
%% recorda_equiv_types([]).
%% 
%% 
%% recorda_equiv_types_table([Type|Types],Equiv):-
%% 	asserta_(equiv_type(Type,Equiv)),
%% 	recorda_equiv_types_table(Types,Equiv).
%% recorda_equiv_types_table([],_Equiv).

asserta_(equiv_type(Type,Type)):- !.
asserta_(equiv_type(Type,Equiv)):-
	asserta_fact(pgm_equiv_type(Type,Equiv)).

:- pred replace_all_equiv_types_in_rules(+Rules, -NewRules)
   :  type_rule_list * var
  => type_rule_list * type_rule_list

  # "@var{NewRules} is  @var{Rules} where 
     type symbols (defined by type rules) are replaced by the representant of the
     corresponding equivalence class.".
 
replace_all_equiv_types_in_rules([], []).
replace_all_equiv_types_in_rules([Rule|Rest], [NewRule|Tail]):-
   replace_equiv_types_in_rule(Rule, NewRule),
   replace_all_equiv_types_in_rules(Rest, Tail).

replace_equiv_types_in_rule(typedef(TypSymbol, Defin), 
                            typedef(TypSymbol, NewDefin)):-
       replace_equiv_types_in_union(Defin, NewDefin).

replace_equiv_types_in_union([], []):-!.
replace_equiv_types_in_union([Type|Defin], [NType|NDefin]):-
   !,
   replace_one_equiv_type(Type, NType),
   replace_equiv_types_in_union(Defin, NDefin).

replace_one_equiv_type(Type, NType):-
   rule_type_symbol(Type), 
   !,
   replace_equiv_rule_type_symbol(Type, NType).
replace_one_equiv_type(Type, NType):-
   compound_pure_type_term(Type, Comp, Name, Arity),
   !,
   functor(NComp, Name, Arity),
   compound_replace_equiv_types(Arity, Comp, NComp), 
   construct_compound_pure_type_term(NComp, NType).
replace_one_equiv_type(Type, Type).
   
compound_replace_equiv_types(0, _Comp, _NComp):-!.
compound_replace_equiv_types(ArgNum, Comp, NComp):-
       ArgNum > 0, 
       arg(ArgNum, Comp, Arg),
       replace_one_equiv_type(Arg, NArg),
       arg(ArgNum, NComp, NArg),
       NArgNum is ArgNum - 1,
       compound_replace_equiv_types(NArgNum, Comp, NComp).

%
% Begin New version os replace single types.

:- pred replace_all_single_types(+Rules, -NewRules)

=> type_rule_list * type_rule_list

# "@var{NewRules} is @var{Rules} except those rules in whose
definition there is only one type. Type symbols occurences are
replaced (unfolded) by their definitions for these classes of
rules. It computes a fixpoint.  Uses a flag, if this flag is an
unbound variable, then no change has been made with respect to the
last iteration.".

replace_all_single_types(Rules, NewRules):-
       select_single_rules(Rules, SingleRules, OtherRules),
       unfold_single_types(SingleRules, URules),
       replace_single_types(URules, OtherRules, OutRules, _Flag),
       append(URules, OutRules, NewRules). 

select_single_rules([], [], []).
select_single_rules([Rule|Rest], [Rule|SingleRules], OtherRules):-
  Rule = typedef(_T, [_D]), 
  !,
  select_single_rules(Rest, SingleRules, OtherRules).
select_single_rules([Rule|Rest], SingleRules, [Rule|OtherRules]):-
  select_single_rules(Rest, SingleRules, OtherRules).

unfold_single_types([], []).  
unfold_single_types([typedef(TypeSymb, [Type])|Rules],
                    [typedef(TypeSymb, [NewType])| Rest]):-
     unfold_one_single_type(Type, [TypeSymb], NewType),
     retractall_fact(pgm_typedef(TypeSymb, _)),
     %% Commented 30-March-99 -PLG
     %% retract(pgm_typedef(TypeSymb, [Type])),
     assertz_fact(pgm_typedef(TypeSymb, [NewType])),
     unfold_single_types(Rules, Rest).    

 %% unfold_one_single_type(ParTyp, Seen, NewParTyp):-
 %%       unfold_single_type(ParTyp, Seen, RParTyp, NewSeen, Flag),
 %%       (var(Flag) -> 
 %%           NewParTyp = RParTyp
 %%           ; 
 %%           unfold_one_single_type(RParTyp, NewSeen, NewParTyp)).
 
unfold_one_single_type(Type, Seen, OutType):-
     find_one_single_type(Type, Seen, SingleTypeSymbol, OneDisjunct, Found),
     (Found == true ->
          replace_one_type_by_defin(Type, SingleTypeSymbol, OneDisjunct, NType, _Flag),
          unfold_one_single_type(NType, [SingleTypeSymbol|Seen], OutType)
          ; 
          OutType = Type).

%% unfold_single_type(Type, Seen, NType, [Type|Seen], true):-
%%    non_par_rule_type_symbol(Type),
%%    get_NO_par_type_definition(Type, [TypDis]),
%%    \+ member_0(Type, Seen), 
%%    !,
%%    NType = TypDis. % Replace Type by its single definition. 
%% unfold_single_type(Type, Seen, NType, NewSeen, Flag):-
%%    par_rule_type_symbol(Type),
%%    !,
%%    functor(Type, F, A),
%%    functor(NType, F, A),
%%    compound_unfold_single_type(A, Type, Seen, NType, NewSeen, Flag).
%% unfold_single_type(Type, Seen, NType, NewSeen, Flag):-
%%    compound_pure_type_term(Type, Comp, Name, Arity),
%%    !,
%%    functor(NComp, Name, Arity),
%%    compound_unfold_single_type(Arity, Comp, Seen, NComp, NewSeen, Flag), 
%%    construct_compound_pure_type_term(NComp, NType).
%% unfold_single_type(Type, Seen, Type, Seen, _Flag).
%%    
%% compound_unfold_single_type(0, _Comp, Seen, _NComp, Seen, _Flag):-!.
%% compound_unfold_single_type(ArgNum, Comp, Seen, NComp, NewSeen, Flag):-
%%        ArgNum > 0, 
%%        arg(ArgNum, Comp, Arg),
%%        unfold_single_type(Arg, Seen, NArg, TempSeen, Flag),
%%        arg(ArgNum, NComp, NArg),
%%        NArgNum is ArgNum - 1,
%%        compound_unfold_single_type(NArgNum, Comp, TempSeen, NComp, NewSeen, Flag).

% find_one_single_type(Type, Seen, SingleTypeSymbol, OneDisjunct, Found)

find_one_single_type(Type, Seen, Type, OneDisjunct, true):-
   non_par_rule_type_symbol(Type),
   \+ member_0(Type, Seen), 
   get_NO_par_type_definition(Type, [OneDisjunct]),
   !.
find_one_single_type(Type, Seen, SingleTypeSymbol, OneDisjunct, Found):-
   par_rule_type_symbol(Type),
   !,
   functor(Type, _F, A),
   compound_find_one_single_type(A, Type, Seen, SingleTypeSymbol, OneDisjunct, Found).
find_one_single_type(Type, Seen, SingleTypeSymbol, OneDisjunct, Found):-
   compound_pure_type_term(Type, Comp, _Name, Arity),
   !,
   compound_find_one_single_type(Arity, Comp, Seen, SingleTypeSymbol, OneDisjunct, Found). 
find_one_single_type(_Type, _Seen, _SingleTypeSymbol, _OneDisjunct, _Found).
   
compound_find_one_single_type(0, _Comp, _Seen, _SingleTypeSymbol, _OneDisjunct, _Found):-!.
compound_find_one_single_type(ArgNum, Comp, Seen, SingleTypeSymbol, OneDisjunct, Found):-
       ArgNum > 0, 
       arg(ArgNum, Comp, Arg),
       find_one_single_type(Arg, Seen, SingleTypeSymbol, OneDisjunct, Found),
       (Found == true -> 
            true
            ;
            NArgNum is ArgNum - 1,
            compound_find_one_single_type(NArgNum, Comp, Seen, SingleTypeSymbol, OneDisjunct, Found)).


:- pred replace_single_types(SingleRules, DisjunctionRules, ReplacedRules, Flag)

# "Replaces all the types symbols in @var{SingleRules} (which are
   defined by only one disjunct) by their definitions in all the rules
   in @var{DisjunctionRules} obtaining @var{ReplacedRules} @var{Flag}
   is not used currently.".

replace_single_types([], Rules, Rules, _):-!.
replace_single_types([Rule|Rules], InRules, OutRules, Flag):-
     Rule = typedef(TypSymbol, [D]),
     replace_one_type_in_rules(InRules, TypSymbol, D, AuxRules, Flag),
     replace_single_types(Rules, AuxRules, OutRules, Flag).

replace_one_type_in_rules([], _TypSymbol, _D, [], _Flag):-!.
replace_one_type_in_rules([Rule|InRules], TypSymbol, D,
                          [ReRule|OutRules], Flag):-
       Rule = typedef(TypSym, Defin),
       replace_type_by_defin(Defin, TypSymbol, D, NDefin, Flag),
       ReRule = typedef(TypSym, NDefin),
       replace_one_type_in_rules(InRules, TypSymbol, D, OutRules, Flag).

% New 

replace_type_by_defin([], _TypSymbol, _D, [], _Flag):-!.
replace_type_by_defin([Type|Defin], TypSymbol, D, [NType|NDefin], Flag):-
   !,
   replace_one_type_by_defin(Type, TypSymbol, D, NType, Flag),
   replace_one_type_by_defin(Defin, TypSymbol, D, NDefin, Flag).

replace_one_type_by_defin(Type, TypSymbol, D, NType, true):-
   non_par_rule_type_symbol(Type),
   !,
   ( Type == TypSymbol -> 
      NType = D 
      ; 
      NType = Type).
replace_one_type_by_defin(Type, TypSymbol, D, NType, Flag):-
   par_rule_type_symbol(Type),
   !,
   functor(Type, F, A),
   functor(NType, F, A),
   compound_replace_single_types(A, Type, TypSymbol, D, NType, Flag).
replace_one_type_by_defin(Type, TypSymbol, D, NType, Flag):-
   compound_pure_type_term(Type, Comp, Name, Arity),
   !,
   functor(NComp, Name, Arity),
   compound_replace_single_types(Arity, Comp, TypSymbol, D, NComp, Flag), 
   construct_compound_pure_type_term(NComp, NType).
replace_one_type_by_defin(Type, _TypSymbol, _D, Type, _Flag).
   
compound_replace_single_types(0, _Comp, _TypSymbol, _D, _NComp, _Flag):-!.
compound_replace_single_types(ArgNum, Comp, TypSymbol, D, NComp, Flag):-
       ArgNum > 0, 
       arg(ArgNum, Comp, Arg),
       replace_one_type_by_defin(Arg, TypSymbol, D, NArg, Flag),
       arg(ArgNum, NComp, NArg),
       NArgNum is ArgNum - 1,
       compound_replace_single_types(NArgNum, Comp, TypSymbol, D, NComp, Flag).


% End New version os replace single types.

%% Control version comment prompting for the file.
%% Local Variables: 
%% mode: CIAO
%% update-version-comments: "on"
%% End:



% Replace single types.

 %% replace_all_single_types
 %% 
 %% :- pred replace_all_equiv_types_in_rules(+Rules, -NewRules)
 %%    :  type_rule_list * var
 %%   => type_rule_list * type_rule_list
 %% 
 %%   ; "@var{NewRules} is  @var{Rules} where 
 %%      type symbols (defined by type rules) are replaced by the representative of the
 %%      corresponding equivalence class.".
 %%  
 %% replace_all_equiv_types_in_rules([], []).
 %% replace_all_equiv_types_in_rules([Rule|Rest], [NewRule|Tail]):-
 %%    replace_equiv_types_in_rule(Rule, NewRule),
 %%    replace_all_equiv_types_in_rules(Rest, Tail).

 %% replace_equiv_types_in_rule(typedef(TypSymbol, Defin), 
 %%                             typedef(TypSymbol, NewDefin)):-
 %%        replace_equiv_types_in_union(Defin, NewDefin).

% End
 %% replace_equiv_type0(X, Y):- 
 %%    arg(1, X, A),	
 %%    (equiv_type(A, B)
 %%      -> arg(1, Y, B)
 %%       ; arg(1, Y, A)).
 %% 

 %% replace_equiv_rule_type_symbol(InType, OuType):- 
 %%     (equiv_type(InType, Type)
 %%       -> OuType = Type
 %%        ; OuType = InType).

replace_equiv_rule_type_symbol(InType, OuType):- 
    non_par_rule_type_symbol(InType), !, 
    (equiv_type(InType, Type)
      -> OuType = Type
       ; OuType = InType).
replace_equiv_rule_type_symbol(InType, OuType):- 
    par_rule_type_symbol(InType),
    functor(InType, F, A),
    functor(OuType, F, A),
    compound_replace_equiv_types(A, InType, OuType).  

%% :- pred simplify_predicate_type_table(+Types, -SimTypes, -EquivSymbols)
%% 
%%  => type_table * type_table * equiv_symb_list
%% 
%% # "Perform a ``light'' (syntax level) simplification of ``auto''
%%    types. The resulting rules will be simplified afterwards
%%    using a more powerful (semantic level) algorithm. We perform
%%    the ``syntax level'' simplification to obtain an smaller set 
%%    of rules so that the semantic level simplification is more efficient.
%%    Note: keeps the types which appears first in the list. 
%%    @var{EquivSymbols} is a list containing the type equivalences found in the 
%%    process.".
%% 
%% :- regtype type_table/1.
%% 
%% type_table(st(A, C, N)) :-
%% 	predname(A),
%% 	list(C,gnd),
%% 	equiv_symb_list(N).
%% 
%% :- regtype equiv_symb_list/1.
%% 
%% equiv_symb_list(A) :-
%% 	list(A, equiv_symb).
%% 
%% :- regtype equiv_symb/1.
%% 
%% equiv_symb(eq(A, B)) :-
%% 	gnd(A),
%% 	gnd(B).
%% 
%% simplify_predicate_type_table(Table, Sim_Tab, EquivSymbols):-
%%        remove_duplicated_clauses_in_table(Table, TemTable),
%%        remove_duplicated_predicates_in_table(TemTable, Sim_Tab, EquivSymbols).
%% 
%% :- pred remove_duplicated_clauses_in_table(+Clauses1, -Clauses2)
%% 
%% # "@var{Clauses2} is @var{Clauses1} without duplicated clauses.". 
%% 
%% remove_duplicated_clauses_in_table([], []).
%% remove_duplicated_clauses_in_table([st(Pred/Arity, Clauses, NumVarClauses)|RestTab], 
%%                                    [st(Pred/Arity, NewClauses, CompClauses)|OuTable]):-
%%       remove_repeated_clauses(Clauses, NumVarClauses, NewClauses, NewNumVarClauses),
%%       sort(NewNumVarClauses, CompClauses),
%%       remove_duplicated_clauses_in_table(RestTab, OuTable).
%% 
%% remove_repeated_clauses([], [], [], []).
%% remove_repeated_clauses([Clause|Rest], [NClause|NumVarClauses],
%%                         [Clause|OutClauses], [NClause|ComClauses]):-
%%     compare_and_delete_clause(Rest, NumVarClauses, NClause, NewClauses, NewNumVarClauses),
%%     remove_repeated_clauses(NewClauses, NewNumVarClauses, OutClauses, ComClauses).
%% 
%% compare_and_delete_clause([], [], _Clause, [], []).
%% compare_and_delete_clause([Clause1|Rest], [NClause1|NumVarClauses], NClause, 
%%                            NewClauses, NewNumVarClauses):-
%%       (equal_clauses(NClause1, NClause) -> 
%%            NewClauses = TemClauses,
%%            NewNumVarClauses = TempNumVarClauses
%%            ;
%%            NewClauses = [Clause1|TemClauses],
%%            NewNumVarClauses = [NClause1|TempNumVarClauses]),
%%    compare_and_delete_clause(Rest, NumVarClauses, NClause, TemClauses, TempNumVarClauses).
%% 
%% equal_clauses(Clause1, Clause2):-
%%    Clause1 == Clause2.
%% 
%%  %% equal_clauses(Clause1, Clause):-
%%  %%    copy_term(Clause1, NClause1),
%%  %%    copy_term(Clause, NClause),
%%  %%    numbervars(NClause1,0,_),   
%%  %%    numbervars(NClause,0,_),
%%  %%    NClause1 == NClause.
%% 
%% :- pred remove_duplicated_predicates_in_table(+Table1, -Table2, -EquivSymbols)
%% 
%% # "@var{Table2} is @var{Table1} where predicates which define the same
%%    type have been colapsed (the first ocurrence is left).
%%    @var{EquivSymbols} is a list containing the type equivalences found
%%    in the process.".
%% 
%% remove_duplicated_predicates_in_table([], [], []).
%% remove_duplicated_predicates_in_table([Entry|RestTab], 
%%                                       [Entry|OuTable],
%%                                       [st(Pred, Symbol_List)|EqSymbols]):-
%%       compare_and_delete_predicate(RestTab, Entry, NewTable, Symbol_List),
%%       get_entry_predicate(Entry, Pred),
%%       remove_duplicated_predicates_in_table(NewTable, OuTable, EqSymbols).
%% 
%% get_entry_predicate(Entry, Pred):-
%%      Entry = st(Pred/_, _, _).
%% 
%% compare_and_delete_predicate([], _, [], []).
%% compare_and_delete_predicate([Entry1|Rest], Entry, NewTable, Symbol_List):-
%%   (equal_predicates(Entry1, Entry) -> 
%%            NewTable = TemTable,
%%            get_entry_predicate(Entry1, Pred1),
%%            Symbol_List = [Pred1|Tem_Symbol_List]
%%            ;
%%            NewTable = [Entry1|TemTable],
%%            Symbol_List = Tem_Symbol_List),
%%    compare_and_delete_predicate(Rest, Entry, TemTable, Tem_Symbol_List).
%% 
%% :- pred equal_predicates(+Pred_Entry1, +Pred_Entry2) 
%% 
%% # "Check whether predicates whose entries are @var{Pred_Entry1} and
%%  @var{Pred_Entry2} define the same type.".
%% 
%% equal_predicates(st(Pred1/_, _, Clauses1), 
%%                  st(Pred/_, _, Clauses)):-
%%    replace_predicate_name_arity(Clauses1, Pred1, Pred, Clauses2),  
%%    sort(Clauses2, SClauses2),
%%    Clauses == SClauses2.
%% 
%% :- pred replace_predicate_name_arity(+InClauses, +Pred, +Pred1, -OutClauses) 
%% 
%% => type_clause_list * pred_arity * pred_arity * type_clause_list
%% 
%% # "Replace predicate name @var{Pred} by @var{Pred1} in @var{InClauses}
%% obtaining @var{OutClauses}.".
%% 
%% :- regtype pred_arity/1.
%% 
%% pred_arity(A) :- nnegint(A).
%% 
%% :- regtype type_clause_list/1.
%% 
%% type_clause_list(A) :-
%% 	list(A, type_clause).
%% 
%% :- regtype type_clause/1.
%% 
%% type_clause(A) :-
%% 	gnd(A).
%% 
%% replace_predicate_name_arity([], _, _, []).
%% replace_predicate_name_arity([Clause|Rest], Pred1, Pred2, 
%%                              [RClause|Rest_clauses]):-
%%   clause_replace_predicate_name_arity(Clause, Pred1, Pred2, RClause),
%%   replace_predicate_name_arity(Rest, Pred1, Pred2, Rest_clauses).
%% 
%% clause_replace_predicate_name_arity(Clause, Pred1, Pred2, (RHead:-RBody)):-
%%   get_head_body_clause(Clause, Head, Body),
%%   (functor(Head, Pred1, 1)
%%       -> functor(RHead, Pred2, 1),
%%          arg(1, Head, Arg), 
%%          arg(1, RHead, Arg)
%%       ;  RHead = Head), 
%%   body_replace_predicate(Body, Pred1, Pred2, RBody).
%% 
%% body_replace_predicate(true, _, _, true):-!.
%% body_replace_predicate((Lit, Body), Pred1, Pred2, (RLit, RBody)):-!,
%%   replace_literal_predicate(Lit, Pred1, Pred2, RLit),
%%   body_replace_predicate(Body, Pred1, Pred2, RBody).
%% body_replace_predicate(Lit, Pred1, Pred2, RLit):-
%%   replace_literal_predicate(Lit, Pred1, Pred2, RLit).
%% 
%% replace_literal_predicate(Lit, Pred1, Pred2, RLit):-
%%   functor(Lit, F, A),
%%   (F/A == Pred1/1 -> 
%%      functor(RLit, Pred2, 1),
%%      arg(1, Lit, Arg),
%%      arg(1, RLit, Arg)
%%      ;
%%      RLit = Lit).

:- pred remove_redundant_simplification(+Rules, -SimpRules)

=> type_rule_list * type_rule_list

# "@var{SimpRules} is @var{Rules} where none of the types in the
   disjunction (definition) of any type rule are pairwise included.".

remove_redundant_simplification([], []).
remove_redundant_simplification([typedef(TypSymbol, Defin)|RuList], 
                                [typedef(TypSymbol, OuDefin)|OutRules]):-
       remove_redundant_types(Defin, OuDefin),
       remove_redundant_simplification(RuList, OutRules).


:- pred remove_redundant_types(+TypeDefin1, -TypeDefin2)

=> type_disjunction * type_disjunction

# "@var{TypeDefin2} is @var{TypeDefin1} where none of the types in the
   disjunction are pairwise included.".

remove_redundant_types(Types, Outypes):-
  remove_redundant_types_3(Types, [], Outypes1),
  % Gives a second pass in reverse order so that a type is compared with
  % the rest of types which appear before it in the list
  remove_redundant_types_3(Outypes1, [], Outypes).

remove_redundant_types_3([], L, L).
remove_redundant_types_3([Type|ResTypes], SeenTypes, OuTypes):-
      (included_in_some_type(ResTypes, Type) ->
            SeenTypes1 = SeenTypes
            ;
            SeenTypes1 = [Type|SeenTypes]),
      remove_redundant_types_3(ResTypes, SeenTypes1, OuTypes).        

 %% Not used. 22-Dec-98 PLG
 %% :- pred remove_redundant_types2(+TypeDefin1, -TypeDefin2)
 %% 
 %% => type_disjunction * type_disjunction
 %% 
 %% # "Gives a second pass in reverse order so that a type is
 %%    compared with the rest of types which appear before it in the list.".
 %% 
 %% remove_redundant_types2([], []).
 %% remove_redundant_types2([Type|ResTypes], OuTypes):-
 %%        (included_in_some_type(ResTypes, Type) 
 %%            -> OuTypes = Types1 ; 
 %%               OuTypes = [Type|Types1]), 
 %%        remove_redundant_types2(ResTypes, Types1).

included_in_some_type([Type1|_ResTypes], Type2):-
      % dz_type_included(Type2, Type1), % PLG 
      dz_type_included_tabling(Type2, Type1), 
      !.
included_in_some_type([_|ResTypes], Type2):-
      included_in_some_type(ResTypes, Type2).

:- pred retract_and_assert_rules(+Rules)

=> type_rule_list

# "Retract the type rules defining the type symbols in @var{Rules} and 
   assert the definitions in @var{Rules}.".

retract_and_assert_rules([typedef(TypSymbol, Defin)|Types]):-
        retract_fact(pgm_typedef(TypSymbol, _)),
  	assertz_fact(pgm_typedef(TypSymbol, Defin)),
 	retract_and_assert_rules(Types).
retract_and_assert_rules([]).



 %% :- pred get_required_rules(+TypeSymbolList, -TypeRuleList)
 %% # "Remove types which are nor used:
 %%   @begin{enumerate}
 %%     @item Collect all types in entry and trusts.
 %%     @item Compute the transitive closure (by traversing type rules).
 %%     @item Retract all type rules whose type symbols are not in the
 %%           transitive closure.
 %%   @end{enumerate}.".

:- pred get_required_rules(+TypeSymbolList, -TypeRuleList)

# "Get all the type rules @var{TypeRuleList} which define the type
  symbols in @var{TypeSymbolList} (and the types appearing in any rule
  of @var{TypeRuleList}, i.e. compute the transitive closure of
  @var{TypeSymbolList}).".

get_required_rules(TypeSymbolList, TypeRuleList):-
     compute_transitive_closure(TypeSymbolList, [], TransClosure),
     select_rules_2(TransClosure, RuleList1),
     replace_all_non_par_types_in_rules(RuleList1, TypeRuleList).

get_necessary_rules(TypeSymbolList, TypeRuleList):-
     compute_transitive_closure(TypeSymbolList, [], TransClosure),
     select_rules_3(TransClosure, TypeRuleList).

compute_transitive_closure([], Seen, Seen):-!.
compute_transitive_closure([TypeSymbol|TypeSymbolList], 
                            Seen, TransClosure):-
  compute_one_type_closure([TypeSymbol|TypeSymbolList], 
                            Seen, NewSeen, NewTypSymList),
  compute_transitive_closure(NewTypSymList, NewSeen, TransClosure).

compute_one_type_closure([TypeSymbol|TypeSymbolList], 
                          Seen, NewSeen, NewTypSymList):-
  ((member_0(TypeSymbol, Seen); is_not_a_type_symbol(TypeSymbol))  
     -> Seen = NewSeen,
        NewTypSymList = TypeSymbolList
     ; 
     (get_type_definition(TypeSymbol, Def) ->
        type_symbols_in_def(Def, [TypeSymbol|TypeSymbolList], NewTypSymList),
        NewSeen = [TypeSymbol|Seen]
        ; 
        compiler_error(req_type_undefined(TypeSymbol)),
        Seen = NewSeen, NewTypSymList = TypeSymbolList)).

type_symbols_in_def([], Types, Types):-!.
type_symbols_in_def([Type|Def], InTypes, DefSymb):-
    type_symbols_0(Type, InTypes, OuTypes),
    type_symbols_in_def(Def, OuTypes, DefSymb).

type_symbols_0(Type, InTypes, TypeSyms):-
     rule_type_symbol(Type), 
     !,      
     add_type_not_duplicates(Type, InTypes, TypeSyms).
type_symbols_0(Type, InTypes, TypeSyms):-
    compound_pure_type_term(Type, Comp, _Name, _Arity),
    !,
    Comp =.. [_|Args],
    type_symbols_in_def(Args, InTypes, TypeSyms).
type_symbols_0(_Type, InTypes, InTypes).
 %% type_symbols_0(Type, InTypes, InTypes):-
 %%     (top_type(Type);
 %%      base_type_symbol(Type); 
 %%      constant_symbol(Type); 
 %%      bot_type(Type);
 %%      var_type(Type);
 %%      ground_type(Type)).

add_type_not_duplicates(Type, List, OuList):-
      member_0(Type, List) -> 
      OuList = List ; OuList = [Type|List].
   
%% replace_equiv_types_in_body((Type,Types),(Type1,Types1)):-!,
%% 	equiv_type0(Type,Type1),
%% 	replace_equiv_types_in_body(Types,Types1).
%% replace_equiv_types_in_body(Lit, Lit1):- 
%%         equiv_type0(Lit, Lit1).

equiv_types([Type|Types],[Type1|Types1]):-
	non_par_equiv_type(Type,Type1),
	equiv_types(Types,Types1).
equiv_types([],[]).

%% % PBC: changed to lists of lists of ...
%% par_equiv_types([Type|Types],[Type1|Types1]):-
%% 	equiv_type0(Type,Type1),
%% 	par_equiv_types(Types,Types1).
%% par_equiv_types([],[]).

%% par_equiv_types([Type|Types],[Type1|Types1]):-
%% 	par_equiv_types0(Type,Type1),
%% 	par_equiv_types(Types,Types1).
%% par_equiv_types([],[]).
%% 
%% par_equiv_types0(Type,Type1):-
%% 	functor(Type,'.',2), !,
%% 	par_equiv_types(Type,Type1).
%% par_equiv_types0(Type,Type1):-
%% 	equiv_type0(Type,Type1).

non_par_equiv_type(Type,Type1):- 
	functor(Type,F,1),
	equiv_type(F,F1), !,
	functor(Type1,F1,1),
	arg(1,Type,A),
	arg(1,Type1,A).
non_par_equiv_type(Type,Type).

%% equiv_type0(Type, Type1):-
%%     functor(Type, F, 1),
%%     !,
%%     equiv_type_1(F, F2),
%%     param_rename_type(F2, ParType),
%%     ParType =.. [Name|Args],
%%     Type1 =.. [Name, _ |Args],
%%     arg(1, Type, A),
%%     arg(1, Type1, A).
%% equiv_type0(Type, Type).
%% 
%% 
%% equiv_type_1(Type, Type1):- 
%% 	equiv_type(Type, Type1), !.
%% equiv_type_1(Type, Type).
%% 
%% param_rename_type(NonParTypeSymb, ParTypeSymb):-
%%           param_type_symbol_renaming(ParTypeSymb, NonParTypeSymb), !.
%% param_rename_type(Type, Type).
%% 
%%  %% equiv_type0(Type,Type1):- 
%%  %% 	functor(Type,F,1),
%%  %% 	equiv_type(F,F1), !,
%%  %% 	functor(Type1,F1,1),
%%  %% 	arg(1,Type,A),
%%  %% 	arg(1,Type1,A).
%%  %% equiv_type0(Type,Type).
%% 
%% replace_predicate_in_list([], _, _, []).
%% replace_predicate_in_list([Lit|Body], Pred1, Pred2, [RLit|RBody]):-
%%   replace_predicate_0(Lit, Pred1, Pred2, RLit),
%%   replace_predicate_in_list(Body, Pred1, Pred2, RBody).
%% 
%% replace_predicate_0(Lit, _Pred1, _Pred2, Lit):-
%%    var(Lit), !.
%% replace_predicate_0(Lit, Pred1, Pred2, RLit):-
%%   nonvar(Lit),
%%   functor(Lit, F, A),
%%   (F/A == Pred1/1 -> 
%%      functor(RLit, Pred2, 1),
%%      arg(1, Lit, Arg),
%%      arg(1, RLit, Arg)
%%      ;
%%      RLit = Lit).
%% 
%% % ASSERTION AND RETRACTION OF INFORMATION
%%  
%% retract_no_simplified_type(TypeSymbol):-
%%  (no_simplified_type(TypeSymbol) -> 
%%      retract_fact(no_simplified_type(TypeSymbol))
%%      ; true).
%% 
%% assert_equiv_simplified_rules([]).
%% assert_equiv_simplified_rules([typedef(TypeSymbol, Def)|Rest]):-
%% %   assertz_fact(pgm_typedef(TypeSymbol, Def)), % assertz or asserta?
%%    insert_rule(TypeSymbol, Def), % assertz or asserta?
%%    assert_equiv_simplified_rules(Rest).

% OPERATIONS ON TYPE RULES

select_rules_3([], []).
select_rules_3([TypSymbol|List], ReqRules):-
    (em_defined_type_symbol(TypSymbol, Def)
       -> non_parametric_type_rule_symbol_def(Rule1, TypSymbol, Def), 
          ReqRules = [Rule1|Rules]
       ;  ReqRules = Rules),
    select_rules_3(List, Rules).

select_rules_2([], []).
select_rules_2([TypSymbol|List], ReqRules):-
    (selected_type(TypSymbol)
       -> get_NO_par_type_definition(TypSymbol, Def),
          non_parametric_type_rule_symbol_def(Rule1, TypSymbol, Def), 
          ReqRules = [Rule1|Rules]
       ;  ReqRules = Rules),
    select_rules_2(List, Rules).

selected_type(TypSymbol):-
   ( internally_defined_type_symbol(TypSymbol,1); type_parameter(TypSymbol) ),
   non_par_rule_type_symbol(TypSymbol).
%   \+ param_type_symbol_renaming(_ParType, TypSymbol). 
 
% SIMPLIFICATION OF TYPE RULES

 %% A type rule is in the format T <- [T1, ..., Tn]
 %% Cases of simplification:
 %% 1) T <- [T1, ..., top, Tn] ==> put T <- [top] and for all types B such that
 %%      B <- [..., T, ...] put B <- [top].
 %% 2) T <- [T1, T1, ..., top, Tn] ==> remove equals T <- [T1, ..., top, Tn]
 %% 3) Remove duplicate definitions of equivalent types in a rule body?
 %% 4) Unfold type symbols until they become base types, top, or 
 %% f(T1, ..., Tn).
 %% 5) remove empty types (including the rules that define them).
 %% 6) T <- [T1] ==> replace T by T1 and remove the rule.
 %% Note: Perhaps we should not eliminate type rules defined by the user. 
 %%       Or leave them without simplification.

%% type_rule_simplify:-
%%    bot_type_rule_simplify,
%%    unfold_type_rule_simplify.
%% 
%% bot_type_rule_simplify:-
%%     findall(TypSymbol, typedef(TypSymbol, _Defin), TypSymbol_List),
%%     del_bot_rules(TypSymbol_List),
%%     retractall_fact(computed_empty_type(_)).
%% 
%% unfold_type_rule_simplify:-
%%   findall(typedef(TypSymbol, Defin), typedef(TypSymbol, Defin), 
%%           Typ_Rule_List),
%%   unfold_type_rules_0(Typ_Rule_List).

simplify_types_after_pp_type_intersection:-
   selec_type_rule_simplify, % Delete empty types and unfold rules (for new created rules). 
   % get_all_not_simplified_type_rules(Unfolded_Non_Empty_Rules),
   get_all_not_simplified_and_not_empty_type_rules(Unfolded_Non_Empty_Rules),
   get_all_simplified_type_rules(SimplifRules),
   delete_and_colapse_rules(SimplifRules, Unfolded_Non_Empty_Rules, ColapRules),
   delete_and_colapse_rules_1(ColapRules, SimRules1),
   retract_and_assert_rules(SimRules1),
   remove_redundant_simplification(SimRules1, SimpRules4),
   replace_all_single_types(SimpRules4, Rules5),
   selective_retract_rules(Unfolded_Non_Empty_Rules),
   asserta_type_rule_list(Rules5),
   get_parametric_type_rules(ParRules),
   rewrite_as_parametric_rules(Rules5, ParRules, TypeSymbols),
   select_rules(Rules5, TypeSymbols, Rules6), 
   replace_all_equiv_types_in_rules(Rules6, RenRules6),
   selective_retract_rules(Rules5),
   asserta_type_rule_list(RenRules6),
   get_all_renaming_rules(RenamingRules),
   replace_all_equiv_types_in_rules(RenamingRules, NewRenamingRules),
   selective_retract_rules(RenamingRules),
   asserta_type_rule_list(NewRenamingRules),
   replace_all_equiv_types_in_renamings,
   unfold_all_types_in_renamings,
   clean_after_NON_empty_pp_type_intersection.

%% rewrite_as_type_symbols(Type_List, Type_Symbol_List):-
%%      find_all_single_type_rules(SingleRules),
%%      rewrite_as_type_symbols_1(Type_List, SingleRules, Type_Symbol_List),
%%      !. 
%% rewrite_as_type_symbols(Type_List, Type_Symbol_List):-
%%      warning_message("rewrite_as_type_symbols(~q, ~q) fails.", [Type_List, Type_Symbol_List]).
%% 
%% find_all_single_type_rules(SingleRules):-
%%     findall(typedef(TypeSymbol, [Type]), typedef(TypeSymbol, [Type]), SingleRules). 
%% 
%% rewrite_as_type_symbols_1([SingleDefin|Type_List], SingleRules, [SingleDefin|OutList]):-
%%      type_symbol(SingleDefin),
%%      !,
%%      rewrite_as_type_symbols_1(Type_List, SingleRules, OutList).
%% rewrite_as_type_symbols_1([SingleDefin|Type_List], SingleRules, [OutTypeSymbol|OutList]):-
%%      !,     
%%      find_equivalent_type_symbol_0(SingleRules, SingleDefin, OutTypeSymbol, OutSingleRules),
%%      rewrite_as_type_symbols_1(Type_List, OutSingleRules, OutList).
%% rewrite_as_type_symbols_1([], _SingleRules, []).
%% 
%% find_equivalent_type_symbol_0(SingleRules, SingleDefin, OutTypeSymbol, OutSingleRules):-
%%     find_equivalent_type_symbol(SingleRules, SingleDefin, OutTypeSymbol, OutTypeRule),
%%     (nonvar(OutTypeRule) ->
%%         OutSingleRules = [OutTypeRule|SingleRules]
%%         ;
%%         OutSingleRules = SingleRules).
%% 
%% :- pred find_equivalent_type_symbol(+SingleRules, SincleDefin, +SingleType, -TypeSymbol)
%% 
%% # "Finds a rule type symbol @var{TypeSymbol} in @var{SingleRules}
%%   which defines a type which is equivalent to the type
%%   @var{SingleType} (which neccessarily is a constant or compound pure
%%   type term). If such rule type symbol does not exists, then creates a
%%   new one, and assert the type rule typedef(TypeSymbol, [SingleType])
%%   in the database.".
%% 
%% find_equivalent_type_symbol([Rule|SingleRules], SingleDefin, OutTypeSymbol, OutTypeRule):-
%%    !,
%%    get_symbol_defin_from_type_rule(Rule, RulTypeSymbol, [Type]),
%%    (dz_equivalent_types(SingleDefin, Type) ->
%%         OutTypeSymbol = RulTypeSymbol
%%         ;
%%         find_equivalent_type_symbol(SingleRules, SingleDefin, OutTypeSymbol, OutTypeRule)).
%% find_equivalent_type_symbol([], SingleDefin, OutTypeSymbol, OutTypeRule):-
%%    new_type_symbol(OutTypeSymbol),
%%    insert_rule(OutTypeSymbol, [SingleDefin]),
%%    create_type_rule(OutTypeSymbol, [SingleDefin], OutTypeRule).

:- pred selec_type_rule_simplify

# "Simplify rules whose types symbols are asserted in a fact
   no_simplified_type(TypSymbol).  First remove empty types, and then
   unfold the remaining rules.".

selec_type_rule_simplify:-
   get_all_not_simplified_type_rules(Rules1),
   check_and_remove_empty_types_1(Rules1),
   get_all_not_simplified_and_not_empty_type_rules(Rules2),
   unfold_type_rules_0(Rules2).

get_all_not_simplified_type_rules(Rules):-
   findall(TypeRule, no_simplified_type_rule(TypeRule), Rules).

no_simplified_type_rule(typedef(TypeSymbol, Def)):-
   no_simplified_type(TypeSymbol),
   typedef(TypeSymbol, Def).

get_all_not_simplified_and_not_empty_type_rules(Rules):-
   findall(TypeRule, no_simplified_and_not_empty_type_rule(TypeRule), Rules).

no_simplified_and_not_empty_type_rule(typedef(TypeSymbol, Def)):-
   no_simplified_type(TypeSymbol),
   \+ computed_empty_type(TypeSymbol),
    typedef(TypeSymbol, Def).

get_all_simplified_type_rules(Simplif_Rules):-
   findall(TypeRule, simplified_type_rule(TypeRule), Simplif_Rules).

simplified_type_rule(typedef(TypeSymbol, Def)):-
   typedef(TypeSymbol, Def),
   \+ no_simplified_type(TypeSymbol).

%Rev
check_and_remove_empty_types_1(TypeRuleList):-
     check_and_remove_empty_types(TypeRuleList, OutTypeRuleList),
     remove_empty_types(OutTypeRuleList).

%Rev
:- pred check_and_remove_empty_types(+TypeRuleList, -OutRules)

# "Checks which types are empty and remove them from the rule base.
 If a (non-parametric) rule type symbol @verb{T} (defined by a type
 rule) is detected to be empty, then gives a warning message and
 retracts the type defining @verb{T} (a rule type symbol without
 defining rule is considered as empty).  @var{OutRules} is
 @var{TypeRuleList} minus rules defining empty types (this rules are
 retracted as datafacts).".

check_and_remove_empty_types([Rule|RuleList], OutRules):-
        Rule = typedef(TypSymbol, _Defin),
        % debug_message("Checking if type ~q is empty (~q)", [TypSymbol, Rule]),
        is_empty_type(TypSymbol),
        !, 
        %% Commented out warning message -PLG Oct, 18, 2004
        %% warning_message("The type ~q IS EMPTY. Its type rule is retracted", [TypSymbol]), 
        set_computed_empty_type(TypSymbol), % Any type rule which is retracted 
        retract_rule(TypSymbol),            % is asserted as computed_empty_type(Type). 
        check_and_remove_empty_types(RuleList, OutRules).
check_and_remove_empty_types([Rule|RuleList], [Rule|OutRules]):-
        !,
        % debug_message("The type ~q is NOT empty", [TypSymbol]),
        check_and_remove_empty_types(RuleList, OutRules).
check_and_remove_empty_types([], []).
%Rev
:- pred remove_empty_types(+RuleList)

# "For each type rule @verb{R} in @var{RuleList} obtains a type rule
   @verb{NR} by removing empty types from @verb{R}. It is assumed that
   @verb{R} is currently asserted. @verb{R} is retracted and @verb{NR}
   asserted.".

remove_empty_types([Rule|RuleList]):-
        !,
        Rule = typedef(TypSymbol, Defin),
        % debug_message("Removing empty types in rule: ~q", [Rule]),
        remove_empty_types_from_union(Defin, OuDefin),
        % debug_message("Done. Simplified definition: ~q", [OuDefin]),
        retract_rule(TypSymbol),
        insert_rule(TypSymbol, OuDefin),        
        remove_empty_types(RuleList).
remove_empty_types([]).
%Rev
remove_empty_types_from_union([Type|TypUnion], OutUnion):-
       contains_an_empty_type(Type),
       !,
       remove_empty_types_from_union(TypUnion, OutUnion).
remove_empty_types_from_union([Type|TypUnion], [Type|OutUnion]):-
       !,
       remove_empty_types_from_union(TypUnion, OutUnion).
remove_empty_types_from_union([], []).        
%Rev
contains_an_empty_type(Type):- 
        bot_type(Type), 
        !.
contains_an_empty_type(Type):-
        non_par_rule_type_symbol(Type), %<- This is redundant because all types in
        computed_empty_type(Type),      %   computed_empty_type(Type) are 
        !.                              %   non_par_rule_type_symbol. PLG Dec-6-2003 
contains_an_empty_type(Type):-
        compound_pure_type_term(Type, Comp, _Name, Arity), 
        !,
        contains_an_empty_type_arg(Arity, Comp).
%Rev
contains_an_empty_type_arg(Arg_Num, Comp):-
      Arg_Num > 0,  
      arg(Arg_Num, Comp, Arg),
     (contains_an_empty_type(Arg) -> 
          true
          ; 
          NArg_Num is Arg_Num - 1,
          contains_an_empty_type_arg(NArg_Num, Comp)).

%% :- pred del_bot_rules(+TypSymbol_List)
%% 
%% # "Removes all the empty types in the body of the type rules which
%%    define the type symbols in @var{TypSymbol_List}.  It also removes
%%    the type rules which define a type symbol @verb{T} in
%%    @var{TypSymbol_List} which is empty, and retracts such type symbol
%%    as @verb{no_simplified_type(T)}.  WARNING: take into account that
%%    such empty type symbol can appear in the program, and thus, should
%%    be replaced by bottom (or removed).
%%  @begin{itemize}
%%    @item Preconditions: none. 
%%    @item Postconditions:
%%          For all rules @verb{typedef(T, [T1, T2, ..., Tn])} 
%%          in the type rule database:
%%          each @verb{Ti} is not empty.
%%  @end{itemize}.".
%% 
%% del_bot_rules(TypSymbol_List):-
%%    del_bot_type_rules(TypSymbol_List).
%%    
%% 
%%  %% del_bot_rules(TypSymbol_List):-
%%  %%    del_bot_type_rules(TypSymbol_List),
%%  %%    retractall(computed_empty_type(_)).
%% 
%% del_bot_type_rules([TypSymbol|List]):-
%%         !,
%%          % debug_message("Checking if type ~q is empty (~q)", [TypSymbol]),
%%         (is_empty_type(TypSymbol) -> 
%%             % debug_message("The type ~q IS EMPTY. Its type rule is retracted", [TypSymbol]),
%%             set_computed_empty_type(TypSymbol),     
%%             retract_rule(TypSymbol)
%%             ;
%%             true
%%             %debug_message("The type ~q is NOT empty", [TypSymbol])
%%         ),
%%         del_bot_type_rules(List).
%% del_bot_type_rules([]).
%% 
%%  %% OLD
%%  %% del_bot_type_rules([]).
%%  %% del_bot_type_rules([TypSymbol|List]):-
%%  %%    (find_type_defin(TypSymbol, Defin) -> 
%%  %%         remove_bot_union(Defin, [], OuDefin),
%%  %%         retract_rule(TypSymbol),
%%  %%         conditional_insert_rule(TypSymbol, OuDefin),        
%%  %%         del_bot_type_rules(List)
%%  %%         ;
%%  %%         del_bot_type_rules(List)).
%% 
%% % What to do with empty types?
%% % a) remove their type rules and assert as empty type somewhere?
%% % b) Assert a type rule defines as bottom.
%% % Note that some procedures assume that when there is no type rule the type is top.
%% 
%%  %% remove_bot_union(TypUnion, InUnion, OutUnion)
%%  %% TypUnion:
%%  %% Seen:
%%  %% InUnion:
%%  %% OutUnion:
%% 
%% remove_bot_union([], InUnion, InUnion).
%% remove_bot_union([Type|TypUnion], InUnion, OutUnion):-
%%   (is_empty_type(Type) -> 
%%       TemUnion = InUnion; 
%%       TemUnion = [Type|InUnion]),  
%%   remove_bot_union(TypUnion, TemUnion, OutUnion).

% UNFOLDING OF RULES

%% Only documentation for this predicate!!!
:- pred unfold_type_rules_0(+Typ_Rule_List)

# "Unfolds all the type rules in @var{Typ_Rule_List}.".

unfold_type_rules_0(Typ_Rule_List):-
   unfold_type_rules(Typ_Rule_List, [], Unfolded_Rules),
   assert_unfolded_rules(Unfolded_Rules).
 % retract and assert a rule when unfolded instead of doing it at the end.
 % PLG

%% :- pred unfold_rules(+TypSymbol_List)
%% 
%% # "Unfolds all the type rules corresponding to the type symbols in 
%%    @var{TypSymbol_List}.
%% 
%% @begin{itemize}
%% 
%%   @item Preconditions:
%% 
%%   For all rule @verb{T <- [T1, T2, ..., Tn]} in the common set of
%%   rules, @verb{Ti} is not empty.
%% 
%%   @item Postconditions:
%% 
%%   Each rule @verb{R} in the common set of
%%   rules is either: 
%%      @begin{itemize}
%%         @item @verb{R = T <- [top]}, where top denotes the @verb{top} 
%%               type in the lattice, or,
%%         @item @verb{T <- [T1, T2, ..., Tn]}, where each @verb{Ti} is not empty, 
%%               nor top, nor a rule type symbol, i.e. each @verb{Ti} is a base type symbol, 
%%               a constant or a compound pure type term of the form
%%               @verb{Ti = f(Ti1, ..., Tik)}. Important note: the unfolded
%%               rule can be non-deterministic, i.e.  for some j different from i,
%%               @verb{Tj} can be of the form @verb{f(Tj1, ..., Tjk)}, i.e. have the
%%               same main functor/arity)
%%      @end{itemize}
%% @end{itemize}
%% 
%% Example 1: the rule @verb{t1 <- [t1, ^a]}, where ^a denotes de atom
%% a, is unfolded to @verb{t1 <- [^a]}. 
%% Example 2: the rule @verb{t1 <- [top, ^a, num]}, is unfolded to @verb{t1 <- [top]}.".
%% 
%%  %% What rule definition for a type symbol should we use? the initial one, or
%%  %% a previously unfolded rule?. Is better to use the initial one, because this
%%  %% way the rule bodies of the unfolded clauses have less repeated types.
%%  %% Example: assume T1, T1, and T3 are type symbols. 
%%  %%    T1 -> [T2, T3, 0]
%%  %%    T2 -> [T1, T3] 
%%  %%    T3 -> [g(T1), T3] 

unfold_type_rules([], InRules, InRules).
unfold_type_rules([Rule|RuList], InRules, OutRules):-
     unfold_type_rule(Rule, Unf_Rule),
     unfold_type_rules(RuList, [Unf_Rule|InRules], OutRules).

unfold_type_rule(Rule, typedef(TypSymbol, OuDefin)):-
     Rule = typedef(TypSymbol, Defin), 
     unfold_type_union_1(Defin, [TypSymbol], [], TmpDefin),
     reverse(TmpDefin, OuDefin). % sort? PLG

unfold_type_union_1([], _Seen, InDefin, InDefin):-
     !.
unfold_type_union_1([Type|_Defin], _Seen, _InDefin, [Top]):-
     top_type(Type), 
     !, 
     set_top_type(Top). 
unfold_type_union_1([Type|Defin], Seen, InDefin, OuDefin):-
     rule_type_symbol(Type), % non_par_rule_type_symbol(Type) instead. 
     member_0(Type, Seen), 
     !,
     unfold_type_union_1(Defin, Seen, InDefin, OuDefin).
unfold_type_union_1([Type|Defin], Seen, InDefin, OuDefin):-
     rule_type_symbol(Type), % non_par_rule_type_symbol(Type) instead. 
     !,
     get_type_definition(Type, TyDefin),
     append(TyDefin, Defin, TemDefin),
     unfold_type_union_1(TemDefin, [Type|Seen], InDefin, OuDefin).
unfold_type_union_1([Type|Defin], Seen, InDefin, OuDefin):-
     unfold_type_union_1(Defin, Seen, [Type|InDefin], OuDefin).

 %% Note, we also can stop unfolding when a type symbol defined in the
 %% initial set of type rules is encountered. This will leave initial type
 %% rules unmodified.

% We assume that we call the type intersection (top level) with nonempty
% types. Afterwards, we remove empty types, and only in the case, the computed
% intersection is not empty, we use it in the program. 
% If a functor pure type term have an empty type symbol, then it is empty,
% thus is not neccessary replacing empty subterms and the generated type
% rules during the intersection computation can be removed. 
% The only thing to do is removing empty types from the rule bodies.
  
 %% We can have into account that existing type symbols defined by rules
 %% that previously have been processed (removed empty types) need not be
 %% processed again.

:- pred replace_all_non_par_types_in_rules(+Rules, -NewRules)
   :  type_rule_list * var
  => type_rule_list * type_rule_list

  # "@var{NewRules} is @var{Rules} (in external format) where
     non-parametric type symbols are replaced by their corresponding
     equivalent parametric type instances (if possible).".

replace_all_non_par_types_in_rules([], []).
replace_all_non_par_types_in_rules([Rule|Rest], [ParRule|Tail]):-
        replace_non_par_types_in_rule(Rule, NewRule),
        internal_rule_translate(NewRule, ParRule),
        replace_all_non_par_types_in_rules(Rest, Tail).

replace_non_par_types_in_rule(typedef(TypSymbol, Defin), 
                              typedef(NewTypSymbol, NewDefin)):-
       replace_non_par_rule_type_symbol(TypSymbol, NewTypSymbol), 
       replace_non_par_types_in_union(Defin, NewDefin).

replace_non_par_types_in_union([], []):-!.
replace_non_par_types_in_union([Type|Defin], [NType|NDefin]):-
   !,
   replace_one_non_par_type(Type, NType),
   replace_non_par_types_in_union(Defin, NDefin).

replace_one_non_par_type(Type, NType):-
   rule_type_symbol(Type), 
   !,
   replace_non_par_rule_type_symbol(Type, NType).
replace_one_non_par_type(Type, NType):-
   compound_pure_type_term(Type, Comp, Name, Arity),
   !,
   functor(NComp, Name, Arity),
   compound_replace_non_par_types(Arity, Comp, NComp), 
   construct_compound_pure_type_term(NComp, NType).
replace_one_non_par_type(Type, Type).
   
compound_replace_non_par_types(0, _Comp, _NComp):-!.
compound_replace_non_par_types(ArgNum, Comp, NComp):-
       ArgNum > 0, 
       arg(ArgNum, Comp, Arg),
       replace_one_non_par_type(Arg, NArg),
       arg(ArgNum, NComp, NArg),
       NArgNum is ArgNum - 1,
       compound_replace_non_par_types(NArgNum, Comp, NComp).

replace_non_par_rule_type_symbol(NonParType, OuType):- 
    (param_type_symbol_renaming(ParType, NonParType) 
      -> OuType = ParType
       ; OuType = NonParType).


put_user_types_first(AllTypes,Sorted) :-
	partition_user_lib(AllTypes,UserTypes,LibTypes),
	append(UserTypes,LibTypes,Sorted).

partition_user_lib([],[],[]).
partition_user_lib([typedef(T,Def)|Ts],User,Lib) :-
	atom_concat(Module,Post,T),
	atom_concat(':',_,Post),
	current_itf(defines_module,Module,Base),
	( is_library(Base) -> 
	  Lib = [typedef(T,Def)|Lib1], User = User1
	; Lib = Lib1, User = [typedef(T,Def)|User1]
	),
	partition_user_lib(Ts,User1,Lib1).
