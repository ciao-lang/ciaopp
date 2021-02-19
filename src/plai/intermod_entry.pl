:- module(intermod_entry, [], [assertions, isomodes, nativeprops, datafacts]).

:- include(intermod_options). % intermod compilation options

% ------------------------------------------------------------
:- doc(title, "Intermodular entry policy").
% ------------------------------------------------------------

:- doc(module,"This module provides the entry policy algorithms
    for modular analysis. The entry policy is determined by the
    @code{entry_policy} preprocessing flag.").

:- use_module(library(lists), [member/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(counters), [setcounter/2, inccounter/2]).
:- use_module(library(vndict), [vars_names_dict/3]).

:- use_module(ciaopp(plai/intermod_ops)).
:- use_module(ciaopp(p_unit/itf_db), [get_module_from_sg/2, current_itf/3]). % for multifile
:- use_module(ciaopp(p_unit),   [type_of_goal/2, type_of_directive/2]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3]).
:- use_module(ciaopp(p_unit/assrt_db), [assertion_read/9]). % for entries
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(ciaopp(plai/domains), [identical_proj/5, abs_sort/3]).
:- use_module(ciaopp(plai/domains),
   [unknown_entry/4, unknown_call/5, info_to_asub/7, empty_entry/4]).
:- use_module(ciaopp(plai/transform), [transform_clauses/5]).
:- use_module(ciaopp(plai/apply_assertions), [apply_assrt_call_to_success/8]).
:- use_module(ciaopp(plai/intermod_db),
   [main_module/2, registry/3, registry_header/2, local_ana_module/2]).

%%------------------------------------------------------------------

:- export(check_curr_entry_id/1).
:- pred check_curr_entry_id(+Id) #"Checks that @var{Id} was an entry
    of the last fixpoint analysis.".
check_curr_entry_id(Id) :-
    curr_entry_id_(Id), !.

:- export(curr_entry_id/1).
:- pred curr_entry_id(?Id) #"Enumerates the @var{Id}s of the entries
    of the last fixpoint analysis.".
curr_entry_id(Id) :-
    curr_entry_id_(Id).

:- data curr_entry_id_/1.

% This is done to store which CP are analyzed each mod_plai

:- export(get_entry_info/3).
:- pred get_entry_info(+AbsInt,-Sg,-Proj)
   # "Provides on backtracking entry abstract substitutions for the current
   module in the global level of intermodular analysis. In the case of manual
   scheduling, this predicate should be called for every module in the program
   unit. In the case of automatic scheduling, this predicate should only be
   called with top-level(U).".
get_entry_info(AbsInt,Sg,AProj) :-
    current_pp_flag(success_policy,SP),
    local_ana_module(_,Module),
    registry(_,Module,regdata(_Id,AbsInt,Sg,Proj,_Succ,_Spec,_,_,Mark)),
    ( (may_be_improved_mark(SP,Mark) ; not_valid_mark(SP,Mark)) -> true ; fail ),
    abs_sort(AbsInt,Proj,Proj_s), % TODO: sorting not needed?
    varset(Sg,Sv),
    apply_assrt_call_to_success(AbsInt,Sg,Sv,Proj_s,Sv,Proj_s,AProj,_).

:- pred call_pattern(+Policy,+AbsInt,-Sg,-Call,-Id)
   # "Provides on backtracking the call patterns that must be analyzed for the
   current module in an intermodulaar analysis context. Therefore, it does not
   provide user-defined entry points, which must be obtained using
   non-intermodular mechanisms.".

:- doc(bug,"when using 'force' policy there should be a smarter
    way to know if user entries should be included or not (now
    they are not included unless there is no .reg file or the
    module is the top-level one.)").

%% Reads ALL entries in registry (even if they are unmarked), but only generates
%% user entries if there is no registry file.
call_pattern(force,AbsInt,Sg,Call_s,Id):-
    local_ana_module(_FileBase,CurrModule),
    add_entries_if_needed(top_level,CurrModule,AbsInt),
    registry(_,CurrModule,regdata(Id,AbsInt,Sg,Call,_Succ,_Spec,_,_,_Mark)),
    abs_sort(AbsInt,Call,Call_s).
call_pattern(force_assrt,AbsInt,Sg,Call_s,Id):-
    local_ana_module(_FileBase,CurrModule),
    add_entries_if_needed(top_level,CurrModule,AbsInt),
    registry(_,CurrModule,regdata(Id,AbsInt,Sg,Call,_Succ,_Spec,Imdg,_,_Mark)),
%% Filtering entries from assertions, exported predicate list, and initialization/on_abort.
    ( member('$query',Imdg) -> true ; fail),  %% Executed only once.
    abs_sort(AbsInt,Call,Call_s).
call_pattern(Policy,AbsInt,Sg,Call_s,Id):-
    ( (Policy = all ; Policy = top_level) -> true ; fail ),
    add_entries_if_needed(Policy,_AllModules,AbsInt),
    local_ana_module(_,Module),
    registry(_,Module,regdata(Id,AbsInt,Sg,Call,_Succ,_Spec,_,_,Mark)),
    current_pp_flag(success_policy,SP),
    ( (may_be_improved_mark(SP,Mark) ; not_valid_mark(SP,Mark)) -> true ; fail ),
    abs_sort(AbsInt,Call,Call_s).

%% --------------------------------------------------------------------

:- pred add_entries_if_needed(+Policy,?Module,+AbsInt)
   # "Adds the entries written in the source code of @var{CurrModule} for the
   domains being used, if they have not been added before.".
add_entries_if_needed(Policy,Module,AbsInt):-
    entry_assertions_to_registry(Policy,Module,AbsInt),
    update_registry_header(Policy,Module,AbsInt).

update_registry_header(Policy,CurrModule,AbsInt):-
    local_ana_module(_,CurrModule), %% CurrModule may be a free variable (then all current modules must be updated).
    valid_entry_in_policy(Policy,CurrModule),
    ( current_fact(registry_header(CurrModule,entries_already_analyzed(Domains)),Ref) -> true ; fail),
    \+ member(AbsInt,Domains),
    erase(Ref),
    assertz_fact(registry_header(CurrModule,entries_already_analyzed([AbsInt|Domains]))),
    fail.
update_registry_header(_Policy,_CurrModule,_AbsInt).

valid_entry_in_policy(top_level, Mod) :-
    main_module(_,Mod).
valid_entry_in_policy(all,_).
valid_entry_in_policy(force,_).

:- pred entry_assertions_to_registry(+Policy,?Module,+AbsInt)
   # "Adds the entries written in the source code of the modules loaded
   for the domains being used, if they have not been added before.".
entry_assertions_to_registry(Policy,Module,AbsInt):-
    current_pp_flag(success_policy,SP),
    pending_intermod_entry_point(Policy,AbsInt,Goal,_Qv,Call,Prime,Module),
    functor(Goal,F,A),
    functor(CGoal,F,A),  % direct access to predicate.
    get_predkey(F,A,SgKey),
    ( current_fact(registry(SgKey,Module,regdata(Id,AbsInt,CGoal,CCall,CPrime,CSpec,ImdgList,Chdg,CMark)),Ref),
      abs_sort(AbsInt,Call,Call_s),
      abs_sort(AbsInt,CCall,CCall_s),
      identical_proj(AbsInt,Goal,Call_s,CGoal,CCall_s) ->
        add_to_imdg_list(ImdgList,'$query',NewImdg,Changed),
        ( Changed = y ->
            erase(Ref),
            assertz_fact(registry(SgKey,Module,regdata(Id,AbsInt,CGoal,CCall,CPrime,CSpec,NewImdg,Chdg,CMark)))
        ;
            true
        )
    ; may_be_improved_mark(SP,Mark),
      get_new_reg_id(Id),
      assertz_fact(registry(SgKey,Module,regdata(Id,AbsInt,Goal,Call,Prime,_Spec1,['$query'],[],Mark)))
    ),
    local_ana_module(FileBase,Module),
    add_changed_module(Module,FileBase,Module,current,no),
    fail.
entry_assertions_to_registry(_Policy,_Module,_AbsInt).

%% --------------------------------------------------------------------

:- pred pending_intermod_entry_point(+Policy,+AbsInt,-Goal,Qv,-Call,-Prime,Module)
   # "Enumerates the entries that have not been analyzed yet by looking at the
     registry headers.".
pending_intermod_entry_point(Policy,AbsInt,Goal,Qv,Call,Prime,Module) :-
    intermod_entry_point_policy(Policy,AbsInt,Goal,Qv,Call,Prime,Module),
    ( (current_fact(registry_header(Module,entries_already_analyzed(Domains))),
    \+ member(AbsInt,Domains)) -> true ; fail ).
pending_intermod_entry_point(_Policy,AbsInt,Goal,Qv,Call,Prime,Module) :-
    entry_point(AbsInt,Goal,Qv,Call,Prime,Module).

:- export(intermod_entry_point/7).
:- pred intermod_entry_point/7 #"User-specified entry points for intermodular
   analysis. I.e., according to the policy defined".
% intermodular-dependent entry points
intermod_entry_point(Policy,AbsInt,Goal,Qv,Call,Prime,Module) :-
    intermod_entry_point_policy(Policy,AbsInt,Goal,Qv,Call,Prime,Module).
intermod_entry_point(_Policy,AbsInt,Goal,Qv,Call,Prime,Module) :-
    entry_point(AbsInt,Goal,Qv,Call,Prime,Module).

intermod_entry_point_policy(Policy,AbsInt,Goal,Qv,Call,Prime,Module) :-
    current_itf(exports, Goal, Module), % backtracking here
    ( Policy = top_level -> main_module(_,Module) ; true ), % else Policy = all ; Policy = force
    functor(Goal,F,A),
    functor(G,F,A),
    \+ entry_assertion(G,_,_Call), % entry assertions treated elsewhere (policy-independent)
    varset(Goal,Qv),
    unknown_entry(AbsInt,Goal,Qv,Call),
    unknown_call(AbsInt,Goal,Qv,Call,Prime).

% regular entry points (they have to be analyzed always, i.e., they are
% policy-independent)
entry_point(AbsInt,Goal,Qv,Call,Prime,Module) :-
    current_itf(multifile,Goal,Module),
    type_of_goal(multifile,Goal),        %% multifiles must be analyzed in any case.
    % TODO: ugly hack to ignore multifile introduced (temporarily until we have
    % custom meta_predicatate for phrase?) in by modules using dcg_phrase (e.g.,
    % module/2)
    \+ Goal = 'multifile:\6\call_in_module'(_,_),
    entry_assertion(Goal,_,CInfo), % IG analyze multifiles only if they have an entry assertion
    varset(Goal,Qv),
    info_to_asub(AbsInt,_,CInfo,Qv,Call,Goal,no),
    unknown_call(AbsInt,Goal,Qv,Call,Prime).
entry_point(AbsInt,Name,[],Call,Prime,_Module):- %% init and on_abort must be analyzed always.
    setcounter(0,0),
    ( type_of_directive(initialization,Body)
    ; type_of_directive(on_abort,Body) ),
    inccounter(0,Name), % Name of directive a number
    varset(Body,Bv),
    vars_names_dict(Ds,Bv,_Ns),
    transform_clauses([(clause(Name,Body),Name)],Ds,[nr],[],AbsInt),
    empty_entry(AbsInt,Name,[],Call), % TODO: make sure that Name is right here
    unknown_call(AbsInt,Name,[],Call,Prime). % TODO: make sure that Name is right here
entry_point(AbsInt,Goal,Qv,Call,Prime,Module):-
    %% entries must be analyzed always (if dynamic preds!)
    entry_assertion(Goal,Module,CInfo),
    varset(Goal,Qv),
    info_to_asub(AbsInt,_approx,CInfo,Qv,Call,Goal,no),
    unknown_call(AbsInt,Goal,Qv,Call,Prime).

entry_assertion(Goal,Mod,Call) :-
    assertion_read(Goal,Mod,_Status,entry,Body,_Dict,_S,_LB,_LE),
    assertion_body(Goal,_Compat,Call,_Succ,_Comp,_Comm,Body).

:- pred add_entries_to_registry(+AbsInt) : atm + not_fails.
:- export(add_entries_to_registry/1).
add_entries_to_registry(AbsInt) :-
    retractall_fact(curr_entry_id_(_)),
    current_pp_flag(entry_policy,Policy),
    ( % failure-driven loop
      call_pattern(Policy,AbsInt,_Sg,_Proj,Id),
        assertz_fact(curr_entry_id_(Id)),
        fail
    ; true
    ).
