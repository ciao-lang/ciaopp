:- module(incanal_db, [
    init_clkeys/0,
    clean_incremental_db/0,
    change_id_clause/2,
    insert_after_clkey/2,
    save_clause_db/0,       
    restore_clause_db/0,
    remove_clauses_pred/2,
    add_all_clauses/1,
    add_new_preds/1,
    get_current_clauses/1,
    % assertions
    get_current_assertions/1,
    add_assertion_source_db/1,
    del_assertion_source_db/1,
    % intermod
    add_changed_registry/4,
    get_changed_registry/4,
    clean_incanal_mod_data/0
    ], [assertions, isomodes, datafacts]).

:- doc(title, "Database for incremental analysis").

:- doc(module, "Predicates for mantaining the structures needed for
incremental analysis").

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [append/3, intersection/3, union/3, difference/3]).
:- use_module(library(hiordlib), [maplist/3]).
:- use_module(library(pathnames), [path_basename/2]).

:- use_module(ciaopp(p_unit/clause_db), [cleanup_clause_db/0, source_clause/3]).
:- use_module(ciaopp(p_unit/assrt_db), [pgm_assertion_read/9]).
:- use_module(ciaopp(p_unit/program_keys),
    [decode_litkey/5, decode_clkey/4, decode_predkey/3, get_clkey/4,
     counter/3, make_atom/2]).
%:- use_module(ciaopp(p_unit/p_dump), [add_to_db/1]).
:- use_module(ciaopp(plai/domains), [identical_proj/5, abs_sort/3]).
:- use_module(ciaopp(plai/fixpo_ops), [fixpoint_id/1, fixp_id/1]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

% ----------------------------------------------------------------------
:- doc(section, "Predicates for handling clause IDs").

:- data pred_inc_clkey/3.

:- doc(init_clkeys/0, "This predicate annotates which is the last
    clause identifier that was assinged by module program_key. This
    is needed to give new ids to the clauses that are added to the
    analysis.").
init_clkeys :- % read from the program_keys file
    retractall_fact(pred_inc_clkey(_, _, _)),
    counter(Key, N, _),
    decode_predkey(Key, F, A),
    asserta_fact(pred_inc_clkey(F, A, N)),
    fail.
init_clkeys.

get_inc_clkey(F/A, ClKey) :-
    retract_fact(pred_inc_clkey(F, A, NId)),
    NId1 is NId + 1,
    get_clkey(F, A, NId1, ClKey),
    assertz_fact(pred_inc_clkey(F, A, NId1)).

% TODO: it is assumed that the Ids are always increased
:- export(update_inc_clkey/1).
:- pred update_inc_clkey(NClKey) : atm  #"Updates the value of the last
id assigned by the program_keys module.".
update_inc_clkey(NClKey) :-
    decode_clkey(NClKey, F, A, L), !, % TODO: leaves choicepoint!!
    ( current_fact(pred_inc_clkey(F, A, ClKey), Ref) ->
        ( ClKey < L ->
          erase(Ref),
          assertz_fact(pred_inc_clkey(F, A, L))
        ; true )
    ;
        assertz_fact(pred_inc_clkey(F, A, L))
    ).

% ----------------------------------------------------------------------
:- doc(section, "Predicates for temporal source database (to calculate diff)").

:- doc(clean_incremental_db/0, "Remove databases for incremental analysis.").
clean_incremental_db :-
    retractall_fact(save_source_clause(_, _, _)),
    retractall_fact(pred_inc_clkey(_, _, _)),
    retractall_fact(loaded_mods_(_)),
    retractall_fact(save_assertion_read(_,_,_,_,_,_,_,_,_)).
%  retractall_fact(changed_registry_(_,_,_,_)).

:- data save_source_clause/3.
:- data save_assertion_read/9.

% TODO: unify with backup

:- doc(save_clause_db/0, "Stores locally the current source database of
ciaopp.").
save_clause_db :-
    retractall_fact(save_source_clause(_, _, _)),
    ( % (failure-driven loop)
      source_clause(Id, Cl, D), % Note: Cl may be a directive too!
        assertz_fact(save_source_clause(Id, Cl, D)),
        fail
    ; true
    ),
  retractall_fact(save_assertion_read(_,_,_,_,_,_,_,_,_)),
  ( % (failure-driven loop)
    pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE),
      assertz_fact(save_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)),
        fail
    ; true
    ).

:- doc(restore_clause_db/0, "Restores from a local copy the source database of
    ciaopp.").
restore_clause_db :-
    retractall_fact(source_clause(_, _, _)),
    ( % (failure-driven loop)
      save_source_clause(Id, Cl, D), % Note: Cl may be a directive too!
        assertz_fact(source_clause(Id, Cl, D)),
        fail
    ;
        clean_unused_counters
    ),
  retractall_fact(pgm_assertion_read(_,_,_,_,_,_,_,_,_)),
  ( % (failure-driven loop)
    save_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE),
      assertz_fact(pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)),
        fail
  ;
      true
  ).

clean_unused_counters :-
    pred_inc_clkey(F, A, ClKey),
    \+ used_counter(F, A),
    retract_fact(pred_inc_clkey(F, A, ClKey)),
    fail.
clean_unused_counters.

used_counter(F, A) :-
    source_clause(_, clause(H, _), _),
    functor(H, F, A).

:- pred get_current_clauses(Cls) : var => list #"Returns all clauses
    currently present in the source database.".
get_current_clauses(Cls) :-
    findall((Id, clause(H, B), D), source_clause(Id, clause(H, B), D), Cls).

:- pred remove_clauses_pred(Pred, Cls) #"Removes from the database all
    clauses for predicate @var{Pred} of the form @tt{F/A} and
    returns them in @var{Cls}.".
remove_clauses_pred(F/A, Cls) :-
    findall(Cl, clauses_pred(F/A, Cl), Cls).

clauses_pred(F/A, Cl) :-
    current_fact(save_source_clause(ClKey, clause(H, B), Dic), Ref),
    decode_clkey(ClKey, F, A, _), % TODO: leaves choicepoint!!!!!!!!!
    erase(Ref),
    Cl = (ClKey, clause(H, B), Dic).

:- pred add_new_preds(+Preds) #"This predicates adds predicates which
    were not defined before.

    This predicate is needed for the initialization of the
    counters for Ids.".
add_new_preds([]).
add_new_preds([Cl|Cls]) :-
    add_new_pred(Cl),
    add_new_preds(Cls).

% There should not be conflicts with predicates that were
% removed completely from the analysis
add_new_pred(Cl) :-
    Cl = (ClKey, clause(H, B), Dic),
    %functor(H, F, A),
    update_inc_clkey(ClKey),
    assertz_fact(save_source_clause(ClKey, clause(H, B), Dic)).
    
:- pred add_all_clauses(Cls) : list #"Asserts the list of clauses
@var{Cls} to the temporal database.".
add_all_clauses([]).
add_all_clauses([Cl|Cls]) :-
    Cl = (A, B, C),
    assertz_fact(save_source_clause(A, B, C)),
    add_all_clauses(Cls).

:- pred get_current_assertions(Assrts) : var => list #"Returns all assertions
    currently present in the source database.".
get_current_assertions(Assrts) :-
    findall(pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE),
            pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE),
            Assrts).

% ----------------------------------------------------------------------
:- doc(section, "Predicates for inserting new clauses in db").

:- data update_flag/0.

:- pred insert_after_clkey(Id, Cl) : atm(Id).
insert_after_clkey(first, Cl) :-
    change_id_clause(Cl, (NClKey, clause(NH, B1), NDic)),
    asserta_fact(source_clause(NClKey, clause(NH, B1), NDic)).
insert_after_clkey(Id, Cl) :-
    retractall_fact(update_flag),
    current_fact(source_clause(X, clause(H, B), Dic), Ref),
    ( X = Id ->
         asserta_fact(update_flag),
         change_id_clause(Cl, (NClKey, clause(NH, B1), NDic)),
         assertz_fact(source_clause(NClKey, clause(NH, B1), NDic)),
         fail
    ; true
    ),
    ( update_flag -> 
      ( X = Id -> % TODO: is this check needed? Second round 
          !
      ;
          erase(Ref),
          assertz_fact(source_clause(X, clause(H, B), Dic))
      )
    ),
    fail.
insert_after(_, (_, clause(_, _), _)).

:- pred change_id_clause(Cl, NCl) #"Changes the Ids through @var{Cl}
    so that there is no conflict with other clauses already
    present in the analysis.".
change_id_clause(Cl, NCl) :-
    Cl = (_, clause(H, B), Dic),
    functor(H, F, A),
    get_inc_clkey(F/A, NClKey),
    change_clause_id_body(NClKey, B, NB),
    NCl = (NClKey, clause(H, NB), Dic).

change_clause_id_body(NClKey, Lit1:OldId, Lit1:NId) :- !,
    new_id_body(NClKey, OldId, NId).
change_clause_id_body(NClKey, (Lit1:OldId, B1), (Lit1:NId, B2)) :- !,
    new_id_body(NClKey, OldId, NId),
    change_clause_id_body(NClKey, B1, B2).
change_clause_id_body(NClKey, (Lit, B1), (Lit, B2)) :-
    change_clause_id_body(NClKey, B1, B2).
change_clause_id_body(_, Lit, Lit) :- !.

new_id_body(NClKey, OldId, NewId) :-
    decode_litkey(OldId, _, _, _, LitId),
    make_atom([NClKey, LitId], NewId).

% ----------------------------------------------------------------------
:- doc(section, "Predicates for adding and deleting assertions to the source db").
add_assertion_source_db(A) :-
    A = pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE),
    assertz_fact(save_assertion_read(Goal,M,Status,Type,Body,Dict,Source,LB,LE)).

del_assertion_source_db(A) :-
    A = pgm_assertion_read(Goal,M,Status,Type,Body,Dict,Source,_LB,_LE),
    retract_fact(save_assertion_read(Goal,M,Status,Type,Body,Dict,Source,_,_)), !.

% --------------------------------------------------
:- doc(section, "Predicates for controlling loaded modules.").

:- data loaded_mods_/1.
:- data analyzed_mods_/1.

:- export(all_different_mods/0).
:- doc(all_different_mods/0, "Flag that determines if the set
    of modules to be loaded with @pred{incremental_module/2} is
    disjoint with the set of the previously loaded").
:- data all_different_mods/0.

% TODO: this predicate is not used
% :- export(add_new_files/2).
% :- pred add_new_files(Fs, AddedFs) : list(atm) * list(atm)
%       #"Given a list of files @var{Fs} adds to the database only
%       those that were not already present (@var{AddedFs}).".
% add_new_files(Fs, Fs) :-
%       loaded_mods_(OldFs),
%       intersection(Fs, OldFs, []), !,
%       set_fact(all_different_mods),
%       set_loaded_mods(Fs).
% add_new_files(Fs, AddedFs) :-
%       ( loaded_mods_(OldFs) ->
%           union(Fs, OldFs, NFs)
%       ;
%           OldFs = [],
%           set_fact(all_different_mods),
%           ( list(Fs) ->
%             NFs = Fs
%           ; NFs = [Fs] )
%       ),
%       difference(Fs, OldFs, AddedFs),
%       set_loaded_mods(NFs).

:- export(set_loaded_mods/1).
:- pred set_loaded_mods(M) : list #"Sets the context (as a list
    of loaded modules) of the incremental analysis.".
set_loaded_mods(_M) :-
    current_pp_flag(module_loading,all), !, % TODO: kludge for monolithic analysis
    set_fact(loaded_mods_(monolithic)).
set_loaded_mods(M) :-
    set_fact(loaded_mods_(M)).

:- export(loaded_mods/1).
:- pred loaded_mods(Ms) => list #"Returns the list of currently loaded modules.".
loaded_mods(Ms) :-
    loaded_mods_(Ms).
%       maplist(path_basename, X, Ms).

:- export(set_analyzed_mods/1).
:- pred set_analyzed_mods(M) : list #"Sets the context (as a list
    of loaded modules) of the incremental analysis.".
set_analyzed_mods(_M) :-
    current_pp_flag(module_loading,all), !, % TODO: kludge for monolithic analysis
    set_fact(analyzed_mods_(monolithic)).
set_analyzed_mods(M) :-
    set_fact(analyzed_mods_(M)).

:- export(analyzed_mods/1).
:- pred analyzed_mods(Ms) => list #"Returns the list of currently loaded modules.".
analyzed_mods(Ms) :-
    analyzed_mods_(Ms).

% --------------------------------------------------
:- doc(section, "Predicates for modular analysis.").

:- pred get_changed_registry(Key, CMod, Mod, Reg) :: atm * atm * atm * term
    #"The data of answer of predicate @var{Key} exported by module
    @var{Mod} has changed to @var{Reg}.".
get_changed_registry(A, B, C, D) :-
    retract_fact(changed_registry_(A, B, C, D0)),
    D = D0.

:- data changed_registry_/4.

:- pred add_changed_registry(SgKey, ImMod, Module, Reg) : (atm(SgKey),  atm(Module))
    #"This predicate annotates changes that occurs on the registry
 of predicate @var{SgKey} exported in @var{Module}.".
add_changed_registry(SgKey, ImMod, Mod, Reg) :-
    current_fact(changed_registry_(SgKey, ImMod, Mod, Reg1), Ref),
    Reg = regdata(_,AbsInt,Sg,Call,_,_,_,_,_),
    Reg1 = regdata(_,AbsInt,Sg1,Call1,_,_,_,_,_),
    abs_sort(AbsInt, Call, Call_s),  % IG stored sorted?
    abs_sort(AbsInt, Call1, Call1_s),
    identical_proj(AbsInt,Sg,Call_s,Sg1,Call1_s),
    !,
    erase(Ref),
    assertz_fact(changed_registry_(SgKey, ImMod, Mod, Reg)).
add_changed_registry(Key, ImMod, Mod, Reg) :-
    assertz_fact(changed_registry_(Key, ImMod, Mod, Reg)).

:- doc(clean_incanal_mod_data/0, "Cleans structures needed for
incremental modular analysis.").
clean_incanal_mod_data :-
    retractall_fact(changed_registry_(_, _, _, _)).

% --------------------------------------------------
:- doc(section, "Predicates for fixpoint.").

:- data fixpoint_id_/2.
:- export(fixpoint_id_/2). % to store in dump
% IG this data is used to keep the fixpoint id between change of modules

fixpoint_id(Context, Id) :-
    fixpoint_id_(Context, Id), !.
fixpoint_id(Context, 0) :-
    assertz_fact(fixpoint_id_(Context, 0)).

:- export(store_current_fixpoint_id/1).
store_current_fixpoint_id(Context) :-
    ( fixp_id(NewId) -> true
    ; NewId = 0
    ),
    retractall_fact(fixpoint_id_(Context, _)),
    assertz_fact(fixpoint_id_(Context, NewId)).

:- export(restore_fixpoint_id/1).
restore_fixpoint_id(Context) :-
    fixpoint_id(Context, X),
    set_fact(fixp_id(X)).
