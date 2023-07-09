:- module(ctchecks_pred,
          [simplify_assertions_all/1, simplify_assertions_mods/2],
          [assertions, regtypes, nativeprops, isomodes, ciaopp(ciaopp_options)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- doc(title, "Compile-time Assertion Checking").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(ciaopp(preprocess_flags)).
:- use_module(ciaopp(ctchecks/ctchecks_pred_messages), [inform_as_change_to_user/5]).
:- use_module(ciaopp(ctchecks/ctchecks_common),
              [abs_exec_one_assertion_all/7, clear_log/0, get_check_assertion/3]).

%% CiaoPP library:
:- use_module(library(compiler/p_unit),
              [predicate_names/1, multifile_predicate_names/1,
               get_pred_mod_defined/2]).
:- use_module(library(compiler/p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(ciaopp(infer), [get_completes_lub/6, get_completes/4, get_info/5]).

%-------------------------------------------------------------------
% all fixed (PP):
%:- doc(bug,"1. Multivariant analysis is not fully exploited. Multiple
%       versions are collapsed into one before simplifying
%       assertions").
%:- doc(bug,"2. Should be reprogrammed so as to not depend on any AbsInt,
%       but use everything that has been analyzed (i.e., use infer.pl).").
%:- doc(bug,"3. Checks for comp assertions not yet integrated.").
%:- doc(bug,"4. Assertions turn true are not shown.").

:- doc(bug,"5. Compatibility properties are not considered at all.").

%-------------------------------------------------------------------
:- export(decide_get_info/4).
% set of completes
decide_get_info(AbsInt,Key,MGoal,Completes):-
    current_pp_flag(multivariant_ctchecks, on),!,
    get_completes(Key,MGoal,AbsInt,Completes).
% completes lub
decide_get_info(AbsInt,Key,MGoal,[complete(MGoal,MCall,[MSuccess],Key,lub)]):-
%       current_pp_flag(collapse_ai_vers, on),
    current_pp_flag(multivariant_ctchecks, off),
    get_completes_lub(Key,MGoal,AbsInt,yes,MCall,MSuccess),!.
% TODO: is the following unreachable? multivariant_ctchecks can only be on or off.
decide_get_info(AbsInt,Key,MGoal,Info) :-
    get_info(AbsInt,pred,Key,MGoal,Info),!. % TODO: make sure that this Info is a list? (JFMC)
decide_get_info(_AbsInt,_Key,_Goal, []).

% ---------------------------------------------------------------------------
:- pred simplify_assertions_all(+AbsInts) : list(atm)
   # "Check calls, success and comp assertions with status @tt{check} for all
   the predicates using the domains @var{AbsInts}.".
simplify_assertions_all(AbsInts):-
    simplify_assertions_mods(AbsInts, all).

:- pred simplify_assertions_mods(+AbsInts, +MaybeModList) : list(atm) * atm.
:- pred simplify_assertions_mods(+AbsInts, +MaybeModList) : list(atm) * list(atm)
   + (not_fails, is_det)
   # "Check calls, success and comp assertions with the check status for all
   the predicates in the modules given by @var{MaybeModList} given the domains
   in @var{AbsInts}. If @var{MaybeModList} is the atom @tt{all}, all predicates are
   considered.".
simplify_assertions_mods(AbsInts, ModList):-
    clear_log,
    ( % (failure-driven loop)
      (predicate_names(Preds) ; multifile_predicate_names(Preds)),
      member(F/A, Preds),
        functor(Sg,F,A),
        ( ModList = all -> true
        ; (get_pred_mod_defined(Sg,Mod), member(Mod,ModList)) -> true
        ; fail
        ),
        check_pred_all(Sg, AbsInts),
        fail
    ; true
    ).

:- pred check_pred_all(+Sg, +AbsInts) + (not_fails, is_det)
   # "Execute abstractly assertions for a predicate @var{Sg} over the domains
     @var{AbsInts}".
check_pred_all(Sg, AbsInts) :-
    ( get_check_assertion(Sg, A, ARef),
      predkey_from_sg(Sg, Key),
      decide_get_info_all(AbsInts, Key, Sg, Info),
      abs_exec_one_assertion_all(AbsInts, Info, A, Key, DomsOut, InfoOut, NA),
      inform_as_change_to_user(A, ARef, NA, DomsOut, InfoOut),
      fail
    ; true
    ).

decide_get_info_all([],_,_,[]).
decide_get_info_all([D|Ds],Key,P,[I|Is]):-
    decide_get_info(D,Key,P,I),
    decide_get_info_all(Ds,Key,P,Is).
