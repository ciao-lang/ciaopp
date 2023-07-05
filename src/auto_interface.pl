:- module(auto_interface, [
    auto_analyze/1,
    auto_optimize/1,
    auto_check_assert/1,
    auto_analyze/2,
    auto_optimize/2,
    auto_check_assert/2,
    customize/0,
    customize/1,
    customize_and_preprocess/0,
    customize_and_preprocess/1,
    customize_but_dont_save/1,
    set_menu_level/1,
    current_menu_level/1,
    again/0,
    set_last_file/1,
    get_last_file/1
    %                         ,opt_menu_branch/2
    %                         ,all_menu_branch/2
], [assertions, fsyntax, dcg, datafacts, ciaopp(ciaopp_options), isomodes]).

:- use_package(menu).

:- compilation_fact(unified_menu).

:- doc(title, "The CiaoPP high-level interface").
:- doc(author, "CiaoPP development team").

:- use_module(ciaopp(frontend_driver), [module/2, output/0, output/1, output/2]).
:- use_module(ciaopp(frontend_driver), [push_history/1, get_output_path/2]).
:- use_module(ciaopp(analyze_driver), [analyze/1, acheck_summary/1, acheck_summary/2, acheck/0, get_assert_count/1]).
:- use_module(ciaopp(transform_driver), [transform/1]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).
%% *** These two for ACC, need to be revised MH
:- use_module(ciaopp(p_dump), [dump/1, dump/2, restore/1]).

:- use_module(ciaopp(plai/fixpo_ops), [store_previous_analysis/1]).
:- use_module(ciaopp(plai/acc_ops), [remove_irrelevant_entries/0]).

%% For modular checking
:- use_module(ciaopp(plai/intermod),
    [inductive_ctcheck_summary/3, intermod_analyze/3, intermod_ctcheck/2,
     valid_mod_analysis/1]).

:- use_module(ciaopp(infer/infer_db),        [domain/1]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(frontend_driver), [is_library/1]).
:- use_module(library(compiler/p_unit), [prop_to_native/2]).
:- use_module(library(compiler/p_unit/p_unit_db), [assertion_read/9, curr_file/2]).
:- use_module(ciaopp(infer/infer_dom),       [knows_of/2]).

:- use_module(engine(io_basic)).
:- use_module(library(lists),         [member/2, append/3]).
:- use_module(library(aggregates),    [findall/3]).
:- use_module(ciaopp(analysis_stats), [pp_statistics/2, set_total_info/1, get_total_info/1, pretty_print_acheck_stats/1]).
:- use_module(library(system),        [file_exists/2]).
:- use_module(library(messages)).
:- reexport(library(menu/menu_generator), [
    get_menu_configs/1,
    save_menu_config/1,
    remove_menu_config/1,
    restore_menu_config/1,
    show_menu_configs/0,
    show_menu_config/1,
    get_menu_flag/3,
    set_menu_flag/3
   ]).
:- use_module(library(prompt),[prompt_for_default/2]).
:- use_module(library(pathnames), [path_splitext/3, path_basename/2]).

:- doc(bug, "1 commented out the question for error file since we
    are generating it in any case (not yet implemented)").

:- doc(bug, "2 when auto_cthecks has the value 'on' (instead of 'auto'),
    the result of compile_time checking is not fully handled yet").

% HOW TO ADD A MENU QUESTION
% --------------------------
%
% These are the steps that you have to follow to add a question to the
% menu. Basically the idea you have to keep in mind is that every question
% in the menu is composed by a _title_ (the text that user sees when
% interacting with the menu) a _flag_ (from preprocess_flags.pl) and a
% _default value_ for the flag. To identify in "which" menu branch (i.e.,
% if it is the optimization menu, or the analyze menu...) the question
% should be asked, an atom (or functor, explained further) is used
% to classify all questions under the "menu branch".
%
% So lets say for example that we want to add a question with the
% title 'This is my question' and the flag, my_flag, with default value,
% defvalue to the optimization menu. Our first point is to locate
% what is the atom that identifies the menu branch. In our case the
% atom is 'opt'. If we read the menu line:
%
% opt, 'Select Optimize'              # inter_optimize - spec.
%
% FOOTNOTE:
% (The question that will appear on the screen corresponding to that
% sentence is:
%
% Select Optimize:            [none, spec, parallelize, slice, poly_spec]
%                             (spec) ?
%
% NOTE that the values between [ and ] are the values of the
% inter_opt flag).
%
% we will notice that the opt menu asks for the inter_optimize flag
% (which has spec as a default value). But then, where is our optimize
% branch? Reading the values of inter_optimize we will realize that:
%
% valid_flag_values(inter_optimize ,
%    member(_, [none,spec,parallelize, slice,poly_spec])).
%
% So, after the opt menu several menu branches can be taken. The glue
% between the different branches is the predicate customize/1:
%
% customize(optimize) :-
%       !,
%       menu(opt, false),
%       get_menu_flag(opt, inter_optimize, NM),
%       menu_level(L),
%       NO =.. [NM, L],
%       customize(NO).
%
% (NOTE: The predicate menu/2 is the one which reads the menu
% declarations and prints the questions on the screen). So the
% conclusion is that opt menu follows the menu branch which has
% exactly the same name as the values of inter_optimize. At this point
% we have to decide in which sub-branch we want our menu question.
% Lets say that we are interested in the spec branch. The spec branch,
% like many other branches, shares questions with the slice branch,
% that is because instead of an atom we use something like:
%
% ~spsl, 'Select Abs Specialization'    # spec_poly - off.
%
% which with the functions package is expanded to spec and slice
% atoms.  Now that once we have located the menu declarations, we only
% have to copy whatever question and paste it under the question we
% want our to appear. The format is:
%
% menu_atom, title # flag - default_value.
%
% Two points make things a bit more complex:
% 1.- naive/expert menus
% 2.- Guards
%
% The first point is clear and easy to explain. Instead of an
% atom for the branch, we specify a functor like:
%
% menu_atm(NUMBER)
%
% where NUMBER indicates the menu level (0 for naive, 1 for expert... in
% the future it could be 0=naive, 1=medium, 2=expert). This explains
% lines like:
%
% ~lt(1), 'Multivariant Success' # multi_success - off <- ana_or_check.
%
% The second point is a little bit more complex. A guard is the field
% after '<-'. The guard itself receives an argument that xis a list
% with the flags that have been selected for asking. The list elements
% are of the form flag=value. If value is a variable it means that the
% question corresponding to that flag has been selected but it has not
% been asked yet. Else, value is the one the user has selected.
%
% For this reason guards are like:
%
% guard cct(X) :-
%       member(ctcheck=Y, X),
%       Y == on.
%
% (NOTE the == !!!)
%
% The "keyword" guard is needed before the guard predicate because the
% guards are rewritten in a special language that allows them to run
% backwards (with a free variable as argument), necessary for the
% conversion to javascript menus.
%
% So in summary, the steps to add a question are:
% 1.- Add a flag to the preprocess_flags.pl file
% 2.- Find out were your question has to take place
% 3.- Copy and paste under the question you would like yours to appear.
% 4.- Add the necessary guards if needed.

:- doc(doinclude, get_menu_configs/1).
:- doc(doinclude, save_menu_config/1).
:- doc(doinclude, restore_menu_config/1).
:- doc(doinclude, show_menu_configs/0).
:- doc(doinclude, show_menu_config/1).
:- doc(doinclude, remove_menu_config/1).

:- doc(hide, analysis/1).
:- doc(hide, menu_default/3).
:- doc(hide, menu_opt/6).
:- doc(hide, set_menu_level/1).
:- doc(hide, current_menu_level/1).
:- doc(hide, set_last_file/1).
:- doc(hide, get_last_file/1).

:- doc(module, "This module defines the high-level interface for
   CiaoPP, which makes it easy to perform some analysis and
   transformation tasks, such as checking program assertions (i.e.,
   types, modes, determinacy, non-failure, cost, etc.), and performing
   optimizations such as specialization and parallelization. The
   results can be observed both as CiaoPP messages and as a
   transformed annotated program. 

   In the @apl{emacs} environment these actions can be performed by
   clicking on the corresponding button in the toolbar or in the
   CiaoPP menus. The high-level interface allows calling these actions
   as predicates from a @bf{CiaoPP top-level} shell:

   @begin{itemize}
   @item @tt{auto_check_assert(File)}: check assertions in File
   @item @tt{auto_analyze(File)}: analyze File
   @item @tt{auto_optimize(File)}: optimize File
   @end{itemize}

   The actions above can be controlled by a set of @bf{preprocessor
   flags}. Note that, depending on some of these flags, processing can
   be of one module or also all the related modules. The default
   values of the CiaoPP flags can be changed with the following
   predicates:

   @begin{itemize}
   @item @tt{customize(all)}: select (interactively) the values for
      the different options (do not perform any action).
   @item @pred{set_menu_flag/3}: select flag values non-interactively.
   @end{itemize}

   The @apl{emacs} environment offers a graphical version of these
   menus.

   These customization menus can be configured to show more or less
   detailed options, depending on the level of expertise of the
   user. This can be configured in the menu changing the @tt{Menu
   Level} flag to @tt{naive} or @tt{expert}.  The following predicates 
   provide handy shortcuts to perform customization and preprocessing
   actions:

   @begin{itemize}
   @item @tt{customize_and_preprocess(File)}: enter a menu to select
     the preprocessing action and options to be performed on file
     @var{File} (or @var{File} and its related modules), select the
     different options, and then perform the action.

   @item @tt{again}: perform again the last actions selected for
      @pred{customize_and_preprocess/1} on the same file (useful for
      re-processing after changing a file).
   @end{itemize}
").

%%  These appear already as separate predicates in the manual.
%%
%%  Provisionaly, and until a new branch in the main menu is created,
%%  the predicates listed below are provided to allow the user to manage
%%  the several menu stored configurations:
%%
%%  @begin{description}
%%
%%   @item get_menu_configs/1. The argument is instantiated to a list
%%   with all current menu stored configurations.
%%
%%   @item save_menu_config/1. Saves the current menu flags value refered
%%   in the future by the atom provided as argument.
%%
%%   @item remove_menu_config/1. Removes a menu configuration referred by
%%   the atom provided as argument.
%%
%%   @item restore_menu_config/1. Restore a menu configuration referred by
%%   the atom provided as argument.
%%
%%   @item show_menu_configs/0. List all the atoms that refers to a menu
%%   configuration.
%%
%%   @item show_menu_config/1. Show the flags values of the meny
%%   configuration referred by the atom provided as argument.
%%
%% @end{description}

%% What's the point of this?
%%
%% :- doc(appendix,"The following is a complete listing of all the
%% options that can be configured through the menu with an explanation of
%% what each of them means:
%%
%% @includedef{menu_opt/6}").
%%

% :- doc(bug, "1.- When executing check assertions branch, if
%             customize analysis flag was on,
%             @pred{auto_check_assert/1}, got flags values from
%             @tt{analysis} menu instead of @tt{check_assertion} menu.").

% ---------------------------------------------------------------------------
% menu HOOKS-GLUE with pp_flags

:- use_module(ciaopp(preprocess_flags), [
    current_pp_flag/2,
    pp_flag/2,
    set_pp_flag/2,
    valid_flag_values/2,
    valid_flag_value/2
   ]).

% (hook)
hook_menu_flag_values(_, Flag, ask(F)) :-
    valid_flag_values(Flag, X),
    functor(X, F, _),
    ( F == int ; F == nnegint ; F == atom ; F == atm ),
    !.
hook_menu_flag_values(_, O, alist(OptsList)) :-
    findall(F, valid_flag_value(O, F), OptsList).

% (hook)
hook_menu_default_option(_, O, Def) :-
    current_pp_flag(O, Def).

% (hook)
hook_menu_flag_help(_, O, Help) :-
    pp_flag(O, Help).

% (hook)
hook_menu_check_flag_value(_, F, V) :-
    valid_flag_value(F, V).

% ---------------------------------------------------------------------------

:- multifile analysis/1.

% :- multifile menu_opt/6.
% :- meta_predicate menu_opt(?, ?, ?, pred(1), pred(0), pred(2)).

:- data menu_level/1.

menu_level(0).

menu_level_tr(naive, 0).
menu_level_tr(expert, 1).

set_menu_level(L) :-
    set_menu_level(~menu_level_tr(L)),
    !.
set_menu_level(X) :-
    int(X), % TODO: integer/1?
    !,
    retract_fact(menu_level(_)),
    asserta_fact(menu_level(X)).
set_menu_level(X) :-
    error_message("~w should be an non-negative integer", [X]).

current_menu_level(X) :-
    menu_level(X).

% (This override the default menu options)
% (hook)
:- if(defined(has_ciaopp_extra)).
menu_default(para, ana_det, det).
menu_default(para, ana_nf, nf). % TODO: was nfg (NFGRAPH-based)
:- endif.

all_tr(optimize, opt).
:- if(defined(unified_menu)).
all_tr(analyze_check, ana). % for unified menu
:- else.
all_tr(analyze, ana).
all_tr(check_assertions, check).
:- endif.
all_tr(A, A).

% NOTE: requires nondet for offline menu generation
all_menu_branch(A, B) :-
    member(inter_all=Br, A),
    member(menu_level=L, A),
    all_tr(Br, BrT),
    ( BrT = check_certificate -> A = B
    ; menu_branch(A, BrT, ~menu_level_tr(L), B)
    ).

:- if(defined(has_ciaopp_extra)).
opt_tr(parallelize, para).
:- endif.
:- if(defined(has_ciaopp_extra)).
opt_tr(poly_spec, sp_poly).
:- endif.
opt_tr(A, A).

opt_menu_branch(A, B) :-
    member(menu_level=L, A),
    member(inter_optimize=Br, A),
    opt_tr(Br, BrT),
    menu_branch(A, BrT, ~menu_level_tr(L), B).

:- if(defined(unified_menu)).
:- include(auto_unified_menu).
ctcheck_menu_name(ana).
:- else.
:- include(auto_old_menu).
ctcheck_menu_name(check).
:- endif.

% to be removed when old_menu is removed
guard expert(X) :-
    member(menu_level=Y, X), Y == expert.

% to be removed when old_menu is removed
guard cct2(X) :-
    ( member(ctcheck=Y, X) ->
        Y \== off
    ;
        member(inter_all=A, X),
        A  == check_assertions,
        member(menu_level=A1, X),
        A1 == naive
    ).

% to be removed when old_menu is removed
guard cct(X) :-
    member(ctcheck=Y, X),
    Y \== off.

guard cct_manual(X) :-
    member(ctcheck=Y, X),
    Y == on.

% guard cct1(X) :-
%       cct(X),
%       member(menu_level=A1,X),
%       ( A1 == naive ->
%         member(ct_modular=E,X),
%         ( E == all ->
%           set_menu_flag(~ctcheck_menu_name,ct_ext_policy,registry),
%           set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,all),
%           set_menu_flag(~ctcheck_menu_name,ext_policy,registry)
%         ; set_menu_flag(~ctcheck_menu_name,ct_ext_policy,assertions),
%           set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,current),
%           set_menu_flag(~ctcheck_menu_name,ext_policy,assertions)
%         )
%       ; true
%       ).

post_mod_check(X,X) :-
    member(menu_level=A1,X),
    ( A1 == naive ->
      member(ct_modular=E,X),
      ( E == all ->
        set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,all), % TODO: useless if intermod=off! enable it? (JF)
        set_menu_flag(~ctcheck_menu_name,ct_regen_reg,on) % IG: probably not working
      ;
        set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,current)
      )
    ; true
    ).

post_mod_ana(X,X) :-
    member(intermod=I,X),
    ( I == on ->
        set_menu_flag(ana,ext_policy,registry),
        set_menu_flag(ana,entry_policy,top_level),
        set_menu_flag(ana,punit_boundary, bundle),
        set_menu_flag(ana,mnu_modules_to_analyze, all),
        set_menu_flag(ana,module_loading, all), % monolithic by default
        set_menu_flag(ana,success_policy, under_all),
        % set_menu_flag(ana,use_libcache, on), % (enabled by default)
        set_menu_flag(ana,output, off)
    ; true ).

post_inc_ana(X,X) :-
    member(incremental=I,X),
    ( I == on ->
        % TODO: this does not seem to be working in the playground
        %   (JF) The playground uses generate_offline_menu(all, _) to
        %   extract a json representation of the possible menu
        %   values. In execution mode X is always unbound so this kind
        %   of rule are never executed. Rewrite as guards that
        %   restrict fixpoint values instead?
        set_menu_flag(ana,fixpoint,dd)
    ; true
    ).

post_ctcheck(X,X) :-
    member(ctcheck=I,X),
    ( I == off ->
        % see comment in inc_ana
        set_menu_flag(ana,dom_sel,manual)
    ; true
    ).

% to be removed when old_menu is removed
post_iter(X,X) :-
    member(ct_mod_iterate=A,X),
    ( A == on ->
        set_menu_flag(~ctcheck_menu_name,ct_ext_policy,registry),
        set_menu_flag(~ctcheck_menu_name,ext_policy,registry),
        set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,all), % TODO: useless if intermod=off! enable it? (JF)
        member(menu_level=A1,X),
        ( A1 == naive ->  % PP: should be ok in most cases
            set_menu_flag(~ctcheck_menu_name,types,terms)
        ; true
        )
    ;
        set_menu_flag(~ctcheck_menu_name,ct_ext_policy,assertions),
        set_menu_flag(~ctcheck_menu_name,ext_policy,assertions),
        set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,current)
    ).

% to be removed when old_menu is removed
reg_reg(X,X):-
    member(ct_regen_reg=A,X),
    ( A==on ->
        set_menu_flag(~ctcheck_menu_name,mnu_modules_to_analyze,all),
        set_menu_flag(~ctcheck_menu_name,ext_policy,registry)
    ; true
    ).

% to be removed when old_menu is removed
guard cct_mod_reg(X) :-
    cct_mod(X),
    member(ct_ext_policy=Y, X),
    Y == registry,
    member(ct_mod_iterate=Y1, X),
    Y1 == on.

% to be removed when old_menu is removed
guard cct_mod(X) :-
    cct(X),
    member(ct_modular=Y, X),
    Y == all.

% True if ctcheck is on (has been selected) OR % it has not
% % been selected (native menu!) and flag value is on.
% guard cct2(X) :-
%       member(ctcheck=Y, X),
%       !,
%       Y == on.
% guard cct2(_) :-
%       get_menu_flag(~ctcheck_menu_name, ctcheck, on).

% guard cct_mod(X) :-
%       member(ct_mod_ana=Y, X),
%       ( Y == monolithic ->
%         set_pp_flag(ct_modular,all),
%         fail
%       ; true
%       ).

% to be removed when old_menu is removed
guard ana_or_check(X)  :-
    member(inter_all=I, X),
    (
        I == check_assertions,
        member(check_config_ana=Y, X),
        Y == on
    ;
        I == analyze
    ).

% to be removed when old_menu is removed
guard ana_or_check_expert(X) :-
    member(menu_level=I, X),
    I == expert,
    ana_or_check(X).

guard dom_manual(X) :-
    member(dom_sel=I, X),
    I == manual.

% to be removed when old_menu is removed
guard ana_or_check_output(X)  :-
    ana_or_check(X),
    member(output=I, X),
    I == on.

% to be removed when old_menu is removed
guard output_on(X)  :-
    member(output=I, X),
    I == on.

% to be removed when old_menu is removed
guard nf_not_selected(X) :-
    ( member(ana_nf=NF, X) ->
        NF == none
    ;
        true
    ).

guard cost_ana(X) :-
    dom_manual(X),
    member(ana_cost=I,X),
    I \== none.

% to be removed when old_menu is removed
% Almost everything have this preconditions
ana_or_check_not_nf(X)  :-
    ana_or_check(X),
    nf_not_selected(X).

guard new_mod(X)  :-
    member(intermod=I, X),
    I == on.

guard new_mod_expert(X)  :-
    expert(X),
    member(intermod=I, X), I == on.

% IG: in the old menu this option was available for all types domains. However,
% the flag is only implemented for terms.
guard types_prec_guard(X) :-
    dom_manual(X),
    member(types=Y, X),
    ( Y == terms ). % Y \= none

guard eval_types_guard(X) :-
    dom_manual(X),
    member(types=Y, X),
    ( Y == eterms ; Y == svterms ). % TODO: ask the domain instead

% to be removed when old_menu is removed
guard ana_or_check_not_nf_evaltypes(X)  :-
    dom_manual(X),
    ana_or_check_not_nf(X),
    member(types=Y, X),
    ( Y == eterms ; Y == svterms ). % TODO: ask the domain instead

% to be removed when old_menu is removed
guard ana_or_check_not_nf_types(X)  :-
    dom_manual(X),
    ana_or_check_not_nf(X),
    member(types=Y, X), Y \== none.

guard custo_fixpoint(X) :-
    expert(X),
    member(custo_fixpo=Y, X), Y == on.

guard custo_fixpoint_ana_gc(X)  :-
    member(fixpoint=Y,X),
    Y \== di, !, fail.
guard custo_fixpoint_ana_gc(X)  :-
    custo_fixpoint(X),
    ana_or_check_not_nf_evaltypes(X),
    member(local_control=Y, X), Y \== off.

guard custo_fixpoint_ana_lc(X)  :-
    member(fixpoint=Y,X),
    Y \== di, !, fail.
guard custo_fixpoint_ana_lc(X)  :-
    custo_fixpoint(X), % TODO: added
    ana_or_check(X),
    member(types=T, X), T \== none,
    !.
guard custo_fixpoint_ana_lc(X)  :-
    custo_fixpoint(X), % TODO: added
    ana_or_check(X),
    member(modes=M, X), M \== none.

:- if(defined(has_ciaopp_extra)).
% to be removed when old_menu is removed
guard paral(X) :-
    member(inter_all=I, X),
    member(inter_optimize=I2, X),
    I  == optimize,
    I2 == parallelize.
:- endif.

% to be removed when old_menu is removed
guard ana_or_check_or_paral(X) :- ana_or_check(X).
:- if(defined(has_ciaopp_extra)).
guard ana_or_check_or_paral(X) :- paral(X).
:- endif.

% to be removed when old_menu is removed
guard ana_or_check_or_paral_uoudg(X) :-
    ana_or_check(X).
:- if(defined(has_ciaopp_extra)).
guard ana_or_check_or_paral_uoudg(X) :-
    paral(X),
    member(para_ann=Y, X),
    (Y == uoudg).  %  ; Y == uudg ; Y == disjwait).
:- endif.

% to be removed when old_menu is removed
guard ana_or_check_or_paral_gr(X) :-
    ana_or_check(X).
:- if(defined(has_ciaopp_extra)).
guard ana_or_check_or_paral_gr(X) :-
    paral(X),
    member(para_grain=Y, X),
    Y == gr.
:- endif.

guard spec_lc(X)   :-
    member(local_control=Y, X),
    Y \== off.

guard spec_lcd(X)  :-
    member(local_control=Y, X),
    ( Y == depth
    ; Y == first_sol_d
    ; Y == det_la
    ).

guard spec_fn(X)   :-
    member(global_control=Y, X),
    Y == hom_emb.

guard spec_hn(X)   :-
    member(local_control=Y, X),
    Y == df_hom_emb_as.

guard spec_pif(X)  :-
    member(spec_poly=Y, X),
    Y \== off.

% to be removed when old_menu is removed
guard gencert(X) :-
    member(gen_certificate=Y, X),
    Y == on.

% guard shpre(X) :-
%       vmember(modes=Y, X),
%       ( Y == share_amgu       ;
%         Y == share_clique     ;
%         Y == sharefree_amgu   ;
%         Y == shfrlin_amgu     ;
%         Y == sharefree_clique ).

guard clipre(X)  :-
    dom_manual(X),
    member(modes=Y, X),
    ( Y == share_clique
    ; Y == sharefree_clique
    ).

% :- if(defined(has_ciaopp_extra)).
% guard para_d1(X)  :-
%       member(para_ann=Y, X),
%       (Y == uoudg).  %  ; Y == uudg ; Y == disjwait).
% 
% %guard para_t1(X)  :-
% %     member(para_grain=Y, X),
% %     Y == gr.
% 
% guard para_n1(X)  :-
%       member(para_grain=Y, X),
%       Y == gr.
% :- endif.

:- if(defined(has_ciaopp_extra)).
guard para_c1(X)  :-
    member(para_grain=Y, X),
    Y == gr.
:- endif.

:- if(defined(has_ciaopp_extra)).
guard polystrat(X)  :-
    member(poly_strategy=Y, X),
    Y == all_sols.

guard polybounded(X)  :-
    member(poly_fitness=F, X),
    F == bounded_size.

guard polyheur(X)  :-
    member(poly_pruning=Y, X),
    ( Y == heuristic
    ; Y == both % missing cut?
    ).

guard polyvar(X)  :-
    member(polyvar_pcpe=Y, X),
    Y == modes.

guard polydepth(X)  :-
    member(poly_pruning=Y, X),
    (Y == bnb;
     Y == both). % missing cut?
:- endif.

guard testing_on(X)  :-
    member(testing=I, X),
    I == on.

guard test_gen_on(X)  :-
    member(test_gen=I, X),
    I == on.

:- push_prolog_flag(multi_arity_warnings, off).

% SPecSLice
spsl(spec).
spsl(slice).

spsl(X, spec(X)).
spsl(X, slice(X)).

:- pop_prolog_flag(multi_arity_warnings).

mtype(ana).
mtype(check).

mtypepar(X) :- mtype(X).
:- if(defined(has_ciaopp_extra)).
mtypepar(para).
:- endif.

mtypeepar(X) :- mtype(X).
:- if(defined(has_ciaopp_extra)).
mtypeepar(para(1)).
:- endif.

anaepar(ana).
:- if(defined(has_ciaopp_extra)).
anaepar(para(1)).
:- endif.

% in which menus to show all output options
moutput(X,ana(X)).
moutput(X,check(X)).
moutput(X,opt(X)).

munified(X,ana(X)).

mfixpo(ana).
mfixpo(check).

lt(X, ana(X)).
lt(X, check(X)).

p_nf(L, LS) :-
    uni_type(L, Z),
    vmember(ana_nf=Y, L),
    (
        eq(Z, Y, none),
%       ->
        L = LS
    ;
        remove_from_list(L, modes=_, L1),
        remove_from_list(L1, types=_, L2),
        %
        append(L2, [ modes          = shfr   ,
                     types          = eterms ,
                     type_precision = all    ,
                     type_output    = all    ,
                     widencall      = onlyfixp ], LS)
    ).

% :- if(defined(has_ciaopp_extra)).
% para_post_g1(L, LS) :-
%       uni_type(L, Z),
%       vmember(para_ann=Y, L),
%       (
%           neq(Z, Y, urlp),
%           L = LS
%       ;
%           remove_from_list(L, para_iap=_, L1 ),
%           append(L1, [ para_iap = post ], LS )
%         ).
% :- endif.

% TODO: rewrite!!!
remove_from_list(A, B, C) :-
    remove_from_list_(A, B, C),
    ( C = [V|_], var(V) ->
        !,
        fail
    ; true
    ).

remove_from_list_([], _, []).
remove_from_list_([X|Xs], X, Ys) :-
    remove_from_list(Xs, X, Ys), !.
remove_from_list_([Y|Xs], X, [Y|Ys]) :- !,
    remove_from_list(Xs, X, Ys).

% ---------------------------------------------------------------------------
show_mcfg :-
    get_menu_configs(C),
    % Note: make sure that this message goes to standard output
    %   (required by ciao-widgets.el)
    pplog(auto_interface, ['Current Saved Menu Configurations: ', C]).

% ---------------------------------------------------------------------------
% Customize

:- data customize__last_file/1.

:- pred set_last_file(File) : atom(File)
   # "Set last file to @var{File}. This option is used by
      customize_and_preprocess, to allow @pred{again/0} to work.".
set_last_file(File) :-
    retractall_fact(customize__last_file(_)),
    asserta_fact(customize__last_file(File)).

:- pred get_last_file(File) : var(File) => atom(File)
   # "@var{File} is the current value of @pred{last_file/1} used by
      @pred{customize_and_preprocess/1} or @pred{customize_and_preprocess/0}.".
get_last_file(File) :-
    current_fact(customize__last_file(File)).

:- pred customize_and_preprocess/0
   # "Select options using @tt{customize/0}, and then call
      @pred{auto_analyze/1}, @pred{auto_optimize/1}, or
      @pred{auto_check_assert/1} (as determined by the selected options) on the
      default file. If no default file is defined, prompt for the name of to be
      processed, which becomes from now on the default file.".
customize_and_preprocess :-
    display('(Main) file to be processed:     ('),
    ( get_last_file(File) -> display(File)
    ; display(none), File = ''
    ),
    display(') ? '),
    prompt_for_default(NewFile,File),
    ( file_exists(NewFile,4) ->
        customize_and_preprocess(NewFile)
    ;  error_message("~w does not exist or cannot be read", [NewFile] )
    ).

:- pred customize_and_preprocess(File)
   # "Select options using @tt{customize/0}, and then call
      @pred{auto_analyze/1}, @pred{auto_optimize/1}, or
      @pred{auto_check_assert/1} (as determined by the selected options) with
      @var{File} as argument. @var{File} is from now on the default file.".
customize_and_preprocess(File) :-
    atom(File),
    customize,
    set_last_file(File),
    again.

:- pred customize_but_dont_save(Option)
   # "Same as customize(@var{Option}), but menu flags will not be modified.".
customize_but_dont_save(Option) :-
    get_menu_flags(L),
    customize(Option),
    restore_menu_flags_list(L).

:- pred again/0
   # "Performs the last actions done by @pred{customize_and_preprocess/1}, on
      the last file previously analyzed, checked, or optimized".
again :-
    get_last_file(File),
    get_menu_flag(all, inter_all, NM),
    exec_auto(NM, File).

exec_auto(optimize, F) :- !,
    auto_optimize(F).
exec_auto(analyze, F) :- !,
    auto_analyze(F).
exec_auto(check_assertions, F) :- !,
    auto_check_assert(F).
exec_auto(check_certificate, F) :- !,
    auto_check_certificate(F).
exec_auto(analyze_check, F) :- !,
    auto_analyze(F).
exec_auto(none, _) :- !.
exec_auto(U, _F) :-
    error_message("Unknown option ~w while executing customize_and_preprocess", [U]).

:- pred customize/0
   # "Enter an interactive menu to select the preprocessing action (analysis /
      assertion checking / transformation / optimization / ...) to be performed
      by default and the different options (i.e., setting the preprocessor
      flags).".
customize :-
    customize(all).

:- pred customize(X)
   # "Customize is used for changing the values of the flags used during
      preprocessing. These flags are grouped into three main classes of actions:
      @em{analyzing}, @em{checking assertions}, or @em{optimizing} programs.
      @var{X} should be instantiated to one of: @tt{analyze},
      @tt{check_assertions}, @tt{optimize}, or @tt{all} (which allows choosing
      among the previous three).".
customize(all) :- !,
    ask_use_config(USE_CONFIG, Bool),
    ( USE_CONFIG == none ->
        menu(all, Bool),
%           get_menu_flag(all, inter_all, NM),
%           get_menu_flag(all, menu_level, ML),
%           set_menu_level(ML),
%           customize(NM),
        ask_save_menu
    ;
        pplog(auto_interface, ['Restoring ', USE_CONFIG, ' Menu Configuration...']),
        restore_menu_config(USE_CONFIG)
    ).
%
% customize(optimize) :- !,
%       menu(opt, false),
%       get_menu_flag(opt, inter_optimize, NM),
%       customize(NM).
% customize(analyze) :- !,
%       menu_level(L),
%       menu(ana, L, false).
% customize(slice) :- !,
%       menu_level(L),
%       menu(slice, L, false).
% % customize(parallelize) :- !,
% %     menu_level(L),
% %     menu(para, L, false).
% :- if(defined(has_ciaopp_extra)).
% customize(poly_spec) :- !.
% :- endif.
% customize(check_assertions) :- !,
%       menu_level(L),
%       menu(check, L, false).
%
customize(check_certificate) :- !.
customize(none) :- !.
customize(X) :-
    atom(X),
    all_tr(X, XT),
    ( X == XT ->
        opt_tr(X, XT2),
        X \= XT2
    ; XT2 = XT
    ),
    menu_level(L),
    menu_level_tr(LT, L),
    menu(XT2, L, false, [menu_level=LT,inter_all=X]),
    !.
customize(X) :-
    menu(X, false),
    !.
customize(A) :-
    error_message("Option ~w not customizable", [A]).

% ---------------------------------------------------------------------------
% Auxiliary

:- pred ask_use_config(Config, B) :: (atm(Config), atm(B))
# "In @var{Config} the selected configuration to use is
  returned. @var{B} tells if printing help message if you are going to
  use more menus.".
ask_use_config(USE_CONFIG, false) :-
    findall(F, valid_flag_value(menu_last_config, F), OptsList),
    OptsList = [_,_|_],
    set_menu_flag(use_cfg, menu_last_config, none),
    menu(use_cfg),
    get_menu_flag(use_cfg, menu_last_config, USE_CONFIG),
    !.
ask_use_config(none, true).

ask_save_menu :-
    set_menu_flag(save_cfg, menu_config_name, none),
    menu(save_cfg, false),
    get_menu_flag(save_cfg, menu_config_name, CONFIG),
    ( CONFIG \== none ->
        save_menu_config(CONFIG)
    ; true
    ).

% ---------------------------------------------------------------------------

:- use_module(library(port_reify), [once_port_reify/2, port_call/1]).

% TODO: reuse with_pp_flags/2
:- meta_predicate with_menu_flags(?, goal).
% Set flags from menu @var{Menu} and execute Goal.
%
% Flags are set before calling Goal and restored independently of
% the exit status of Goal (success, failure, or exception).
%
% Additionally, it shows an error message if Goal fails.

with_menu_flags(Menu, Goal) :-
    save_flags(Menu),
    once_port_reify(Goal, Port),
    restore_flags(Menu),
    ( port_call(Port) -> true
    ; error_message("INTERNAL ERROR: Unexpected error when executing ~w", [Goal]) % TODO: exception?
    ).

% TODO: rename (call it: set flags from menu)
save_flags(Menu) :-
    get_flag_list(Menu, L),
    save_flags_list(L, Menu).

get_flag_list(Menu, L) :-
    findall(A, (menu_opt${ menu => MM, flag => A }, functor(MM, Menu, _)), L).

save_flags_list([A|As], Menu) :- !,
    get_menu_flag(Menu, A, V),
    ( push_pp_flag(A, V) -> true
    ; error_message("Invalid flag value: ~w=~w", [A,V]) % TODO: exception?
    ),
    save_flags_list(As, Menu).
save_flags_list([], _Menu).

% TODO: rename (undo flags from menu)
restore_flags(Menu) :-
    get_flag_list(Menu, L),
    restore_auto_flags_list(L).

restore_auto_flags_list([A|As]) :- !,
    pop_pp_flag(A),
    restore_auto_flags_list(As).
restore_auto_flags_list([]).

% ---------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2, pop_pp_flag/1]).
:- use_module(library(lists), [reverse/2]).

:- meta_predicate with_pp_flags(?, goal).
% Push pp flags Flags ([flag1=val1, flag2=val2, ...]) and 
% execute Goal. Pop these flags independently of the exit
% status of Goal (success, failure, or exception).

with_pp_flags(Flags, Goal) :-
    push_flags(Flags),
    once_port_reify(Goal, Port),
    reverse(Flags, RFlags),
    pop_flags(RFlags),
    port_call(Port).

push_flags([A=V|As]) :- !, push_pp_flag(A, V), push_flags(As).
push_flags([]).

pop_flags([A=_|As]) :- !, pop_pp_flag(A), pop_flags(As).
pop_flags([]).

% ---------------------------------------------------------------------------
% auto_*/? predicates
do_output(OFile, Menu) :-
    % human-readable output
    get_menu_flag(Menu,output,Output),
    ( Output == on ->
        ( current_pp_flag(intermod,on) ->
            warning_message("Output in source program of intermodular analysis currently not supported")
        ;
            ( var(OFile) -> output ; output(OFile) )
        )
    ; true
    ),
    % restorable output
    get_menu_flag(Menu,dump,DOut),
    ( \+ DOut == off ->
        ( var(OFile) -> curr_file(OFile,_), ! ; true ), % assuming one file
        atom_concat(OFile,'.dump', DumpF),
        ( DOut == default -> DOpts = [] ; DOpts = [DOut]), % default or incremental
        dump(DumpF, DOpts),
        note_message("Dumped analysis in ~w", [DumpF])
    ;   true
    ).

% ---------------------------------------------------------------------------
%! # Test case generation
% TODO: move to other file
:- if(defined(has_ciaopp_testgen)).

:- use_module(ciaopp_testgen(ciaotest_driver),[ciaotest/2, processed_test_case/6, clean_processed_cases/0]).
:- use_module(engine(internals), [module_concat/3]).
%:- use_module(library(unittest), [run_tests_in_module/3]).
%:- use_module(library(unittest/unittest_summaries), [show_test_summaries/1]).
%:- use_module(library(unittest/unittest_statistics), [statistical_summary/1, get_statistical_summary/2]).
:- use_module(library(compiler/p_unit/p_unit_db), [add_assertion_read/9, remove_assertion_read/9, assertion_read/9]).
:- use_module(library(counters)).

% Run unit-tests and perform assertion-based random test generation in File
do_testing(File, OutFile) :- 
    ( current_pp_flag(testing, on) -> 
        ( var(OutFile) -> get_output_path(yes, OFile) ; OFile = OutFile ), % TODO: remove this line? 
        output(OFile,[no_written_file_msg,add_srcloc_prop]),
        /* 
        ( current_pp_flag(run_utests, on) ->
            pplog(testing, ['{Executing test assertions from module ' , ~~(OFile), '}']),
            run_tests_in_module(OFile,[],TestSumm),
            show_test_summaries(TestSumm),
            statistical_summary(TestSumm),
            flatten(TestSumm, IdxTestSummaries),
            get_statistical_summary(IdxTestSummaries, Stats),
            Stats = stats(NTests,_,NFailed,_,_,_,_),
            ( NTests == 0 -> pplog(testing, ['{No test assertions found in module ' , ~~(OFile), '}']) ; true )
        ; true ),
        
        ( var(NFailed) -> NFailed = 0 ; true ),
        ( NFailed == 0 ->
            pplog(testing, ['{Generating random test cases for module ' , ~~(OFile), '}']),
        */
        current_pp_flag(run_utests, UTesting),
        current_pp_flag(test_gen, TestGen),
        get_test_selection(UTesting,TestGen,Mode),
        current_pp_flag(verbosity, Verb),
        ( Verb == off ; Verb == low -> VerbLvl = normal ; VerbLvl = high ),
        Opts = [keep_processed_cases(yes),
                test_selection(Mode),
                verbosity(VerbLvl)|O],
        ( current_pp_flag(show_test_cases, on) ->
            O = [show_test_cases(yes)|O2]
        ; O = O2 ),
        current_pp_flag(num_test_cases, N), 
        O2 = [number_tests(N)],
        clean_processed_cases,
        ( ciaotest(OFile,Opts) ->  
            path_splitext(File, Base, _),
            path_basename(Base,M1),
            path_splitext(OFile, Base2, _),
            path_basename(Base2,M2),
            update_assrt_status(M1,M2),
            push_history(testing)
        ; true )
    ; true ).

get_test_selection(on,on,both).
get_test_selection(on,off,user).
get_test_selection(off,on,auto).

update_assrt_status(ModOrig,ModOut) :-
    current_fact(processed_test_case(ModOut,Id,Type,TestCase,Loc,Pass)), !, % get failed test case
    update_assrt_status_(ModOrig,ModOut,Id,Type,TestCase,Loc,Pass),
    update_assrt_status(ModOrig,ModOut).
update_assrt_status(_,_).

update_assrt_status_(ModOrig,ModOut,Id,Type,TestCase,Loc,Pass) :-
    Loc = loc(OSrc,LB,LE),
    functor(TestCase,N,Ar),
    module_concat(ModOrig,N,Name),
    functor(Goal,Name,Ar),
    (   assertion_read(Goal,ModOrig,Status,Type,Body,Dict,OSrc,LB,LE), % find assertion that matches with test case goal
        (Type \== calls) -> true % filter out calls assertions
    ; 
        throw(bug('No assertions found for test case')) 
    ),
    remove_assertion_read(Goal,ModOrig,Status,Type,Body,Dict,Source,LB,LE), % remove assertion from db
    assertion_body(Pred,Compat,Call,Succ,Comp,Comm,Body),
    ( Type \== test ->  
        append(Comp,[ by(Pred, texec(Id)) ],NewComp), update_acheck_counters(Type,ModOrig) 
    ;   
        NewComp = Comp ),
    assertion_body(Pred,Compat,Call,Succ,NewComp,Comm,Body2),
    ( ground(Pass) -> NewStatus = checked ; NewStatus = false ),
    add_assertion_read(Goal,ModOrig,NewStatus,Type,Body2,Dict,Source,LB,LE), % add assertion with false status
    add_texec_assrts(Type,Id,Goal,ModOut,ModOrig,Dict,Source,LB,LE).

add_texec_assrts(Type,Id,Goal,ModOut,ModOrig,Dict,Source,LB,LE) :-
    findall(TestCases,processed_test_case(ModOut,Id,_,TestCases,_,_),Res),
    retractall_fact(processed_test_case(ModOut,Id,_,_,_,_)),  % remove all other test cases for this assertion
    ( Type \== test -> add_texec_assrts_(Res,Id,Goal,ModOrig,Dict,Source,LB,LE) ; true).

add_texec_assrts_([],_,_,_,_,_,_,_).
add_texec_assrts_([TestCase|Cases],Id,Goal,Mod,Dict,Source,LB,LE) :-
    functor(TestCase,F,A),
    functor(Head,F,A),
    flat_head(TestCase, Head, Unifs),
    assertion_body(Head,[],Unifs,[],[ id(Head, Id) ],[],Body), % create body of new test asertion 
    add_assertion_read(Goal,Mod,check,texec,Body,Dict,Source,LB,LE), % add new test assertion to db
    add_texec_assrts_(Cases,Id,Goal,Mod,Dict,Source,LB,LE).

update_acheck_counters(Type,Mod) :-
    ( Type = calls -> T = c ; T = s),
    counter_name(simp,false,T,Counter),
    counter_name(simp,check,T,Counter2),
    safe_inccounter(Counter,_),
    safe_deccounter(Counter2,_),
    get_assert_count(assert_count(CTInfo)),
    set_total_info([assert_count(Mod,CTInfo)]).

safe_inccounter(Counter, Val) :- % in case the counter is not defined
    inccounter(Counter, Val), !.
safe_inccounter(_,_).

safe_deccounter(Counter, Val) :- % in case the counter is not defined
    deccounter(Counter, Val), !.
safe_deccounter(_,_).

counter_name(simp, false, c, simp_false_c).
counter_name(simp, false, s, simp_false_s).
counter_name(simp, check, c, simp_check_c).
counter_name(simp, check, s, simp_check_s).

:- use_module(library(dict)).
flat_head(Head, Head2, Unifs) :-
    Head =.. [N|As],
    Seen = _, % empty dictionary
    flat_head_(As, Seen, As2, Unifs),
    Head2 =.. [N|As2].

flat_head_([], _, [], []).
flat_head_([A|As], Seen, [A2|As2], Unifs) :-
    ( var(A) ->
        % A variable, add as unif only if it appeared before
        ( dic_get(Seen, A, _) ->
            Unifs = [A2 = A|Unifs0]
        ; Unifs = Unifs0,
          A2 = A,
          dic_lookup(Seen, A, yes)
        )
    ; Unifs = [A2 = A|Unifs0]
    ),
    flat_head_(As, Seen, As2, Unifs0).
:- else.
do_testing(_,_).
:- endif. % defined(has_ciaopp_testgen).

% ---------------------------------------------------------------------------

:- pred auto_analyze(F)
   # "Analyze the module @var{F} with the current analysis options (use
      @tt{customize(analyze)} to change these options).".
auto_analyze(File) :-
    auto_analyze(File, _).

:- pred auto_analyze(F, OFile)
   # "Same as @pred{auto_analyze/1} but the output file will be @var{OFile}.".
auto_analyze(File, OFile) :-
    with_menu_flags(ana, auto_analyze_(File, OFile)).

auto_analyze_(File, OFile) :-
    get_menu_flag(ana, ctcheck, Check),
    Check = on, !,
    auto_check_assert(File, OFile).
auto_analyze_(File, OFile) :-
    module(File,Info),
    fail_if_module_error(Info), !,
    get_menu_flag(ana, inter_ana, AnaKinds),
    anakinds_to_absints_menu(AnaKinds, ana, AbsInts),
    analyze(AbsInts),
    %
    get_menu_flag(ana, vers, Vers) ,
    ( Vers == on -> transform(vers) ; true ),
    %
    do_output(OFile, ana),
    set_last_file(File).
auto_analyze_(_, _) :-
    error_message("Analysis aborted.").

fail_if_module_error(Info) :-
    ( member(error,Info) ->
        error_message("Compilation errors detected."), fail
    ; true
    ).

:- pred auto_check_assert(F)
   # "Check the assertions in file @var{F}, with the current options, giving
      errors if assertions are violated (use @tt{customize(check_assertions)} to
      change these options).".
auto_check_assert(File) :-
    auto_check_assert(File, _).

:- pred auto_check_assert(F, OFile)
   # "Same as @pred{auto_check_assrt/1} but the output file will be
      @var{OFile}.".
auto_check_assert(File, OFile) :-
    with_menu_flags(~ctcheck_menu_name, auto_check_assert_(File, OFile)).

% TODO: load module first in both intermod on and off
auto_check_assert_(File, OFile) :-
    % Make sure that we enabled ctchecks in the flags
    get_menu_flag(~ctcheck_menu_name, ctcheck, CTCHECKS),
    ( CTCHECKS == off ->
        error_message("Incompatible flag value: ctcheck = off"), throw(bug)
    ; true
    ),
    % Select and load TopLevel module (or just File if intermod is off)
    ( current_pp_flag(intermod, off) -> TopLevel = File
    ; maybe_main(File,TopLevel)
    ),
    ( current_pp_flag(interleave_an_check,on), 
      \+ current_pp_flag(intermod, off) -> true % TODO: IG: probably this is not working
    ; module(TopLevel,Info),
      ( fail_if_module_error(Info) -> true ; Error = yes )
    ),
    ( Error == yes ->
        error_message("Analysis and checking aborted.")
    ;
        % Decide domains for the given program (if CTCHECKS is auto) or
        % just read from menu.
        get_menu_flag(ana, inter_ana, AnaKinds),
        get_menu_flag(~ctcheck_menu_name, dom_sel, DomSel),
        % pp_statistics(runtime, [T0,_]),
        ( DomSel == auto -> decide_domains(AnaKinds) ; true ),
        anakinds_to_absints(AnaKinds, ~ctcheck_menu_name, AbsInts),
        % pp_statistics(runtime, [T1,_]),
        % T is T1 - T0,
        % pplog(auto_interface, ['{automatic selection of domains in ', time(T), ' msec.}']),
        % pplog(auto_interface, ['{Analyses selected to check assertions: ',~~(AbsInts), '}']),
        % Perform analyses
        exec_analyses_and_acheck(AbsInts, TopLevel, File, OFile)
    ).

exec_analyses_and_acheck(AbsInts, TopLevel, File, OFile) :-
    get_menu_flag(~ctcheck_menu_name, gen_certificate, GENCERT),
    ( GENCERT == on -> % It was "GENCERT == manual" but this option does not exist
        % TODO: *** This needs to be revised... MH
        set_pp_flag(dump_pred,nodep),
        set_pp_flag(dump_pp,off),
        set_pp_flag(fixpoint,di)
    ; true
    ),
    ( current_pp_flag(intermod, off) ->
        analyze(AbsInts),
        acheck_summary(_,AnyError) % TODO: TopLevel vs File?
    ; current_pp_flag(interleave_an_check,on) -> % TODO: IG: probably this is not working
        inductive_ctcheck_summary(AbsInts,TopLevel,AnyError)
    ;
        intermod_analyze(AbsInts,TopLevel,Info),
        ( member(error,Info) ->
            error_message("Compilation error. Checking aborted."),
            AnyError = [error]
        ;
            intermod_ctcheck(AbsInts,[File]),
            % errors not propagated to caller (E.g., for command line, etc.)
            % see decide_summary/1 in analyze_driver
            AnyError = []
        )
    ),
    ( member(error,AnyError) ->
        true
    ;
        gencert_ctchecks(AnyError, File, GENCERT),
        do_testing(File, OFile),
        get_total_info(ACheckInfo),
        pretty_print_acheck_stats(ACheckInfo),
        do_output(OFile, ~ctcheck_menu_name),
        set_last_file(File)
    ).

analyze_each([]).
analyze_each([D|Ds]) :-
    analyze(D),
    analyze_each(Ds).

gencert_ctchecks(Err,_,_):-
    Err == error, !,
    error_message("Errors detected. Further preprocessing aborted.").
gencert_ctchecks(_,File,GENCERT):-
    ( GENCERT == on ->
        atom_concat(File,'.cert',Cert_Name),
        pplog(auto_interface, ['{Generating certificate ',~~(Cert_Name)]),
        pp_statistics(runtime,_),
        ( current_pp_flag(reduced_cert,on) -> remove_irrelevant_entries ; true ),
        dump(Cert_Name),
        pp_statistics(runtime,[_,T]),
        pplog(auto_interface, ['{certificate saved in ', time(T), ' msec.}\n}'])
    ; true
    ).
%       get_menu_flag(~ctcheck_menu_name, optim_comp, OPTIMCOMP),
%       ( OPTIMCOMP == none ->
%           decide_output(OFile)
%       ; optim_comp(OPTIMCOMP)
%       ).

% Extract the (menu flag) selected abstract domains AbsInts from the
% specified analysis kinds AnaKinds.
anakinds_to_absints_menu([],_Menu,[]).
anakinds_to_absints_menu([AnaKind|AnaKinds],Menu,[AbsInt|AbsInts]):-
    get_menu_flag(Menu,AnaKind,AbsInt),
    \+ AbsInt = none,
    !,
    anakinds_to_absints_menu(AnaKinds,Menu,AbsInts).
anakinds_to_absints_menu([_|AnaKinds],Menu,AbsInts):-
    anakinds_to_absints_menu(AnaKinds,Menu,AbsInts).

% ---------------------------------------------------------------------------
%! # Auto selection of domains for ctchecks
%  (based on the properties specified in the program assertions)

% TODO: Auto selection based on assertions does not track where
%   precision is lost during analysis, a more sophisticated domain
%   selection should be semantic (IG&JF).

% TODO: Auto selection for intermodular analysis is dummy (see comment
%   above anyway).

% Decide which domains are needed for the given analysis kinds and
% select them in the corresponding menu flags.
decide_domains(AnaKinds) :-
    ( current_pp_flag(intermod, off) ->
        decide_domains_monolithic(AnaKinds, AnaFlags),
        select_anaflags_monolithic(AnaFlags)
    ; % TODO: this was enabled only for 'get_menu_flag(~ctcheck_menu_name,ct_modular,all)' [IG&JF]
      decide_domains_intermod(AnaKinds, AnaFlags),
      select_anaflags_intermod(AnaFlags)
    ).

%% :- compilation_fact(menu_based_dom_sel).

:- if(defined(menu_based_dom_sel)).

%! # Domains to use from previous analysis

anakinds_to_absints(AnaKinds, Menu, AbsInts) :-
    anakinds_to_absints_menu(AnaKinds, Menu, AbsInts).

% ------------------------------------------------------------------------

%! # Set anaflags after properties analysis

select_anaflags_monolithic(AnaFlags) :-
    select_anaflags_intermod(AnaFlags).

% ------------------------------------------------------------------------

%! # Automatically Pick Domains
% Algorithm to automatically pick what domains to use when verifying
% assertions. Only one domain of each kind can be picked.

decide_domains_monolithic(AnaKinds, AnaFlags) :-
    cleanup_decide_domains,
    decide_domains_monolithic_(AnaKinds, AnaFlags),
    cleanup_decide_domains. % (no longer needed)

decide_domains_monolithic_([],[]).
decide_domains_monolithic_([AnaKind|AnaKinds],[f(AnaKind, AbsInt)|AnaFlags]) :-
    decide_domain_monolithic(AnaKind, AbsInt),
    decide_domains_monolithic_(AnaKinds,AnaFlags).

cleanup_decide_domains :-
    retractall_fact(prop_covered(_,_,_)).

:- data prop_covered/3.
% prop_covered(F,A,AbsInt):
% Cache to store whether a (native) property F/A was already covered in
% previously selected domains AbsInt. E.g., if shfr covers groundness,
% do not run eterms/nf (they also know about groundess).
set_prop_covered(PropF, PropA, AbsInt) :-
    ( prop_covered(PropF, PropA, _) ->
        true
    ; assertz_fact(prop_covered(PropF, PropA, AbsInt))
    ).

% Decide the domain AbsInt necessary to analyze the existing
% properties from any loaded module (curr_file/2). 'none' if this
% analysis is not needed.
decide_domain_monolithic(AnaKind, AbsInt) :-
    preferred_ana(AnaKind,AbsInt0),
    curr_file(_,M), % (for each loaded module) % TODO: do for a selection?
    needed_to_prove_prop(M, AbsInt0, AnaKind),
    !,
    AbsInt = AbsInt0.
decide_domain_monolithic(_AnaKind, none).

needed_to_prove_prop(M, AbsInt, AnaKind) :-
    ( % (failure-driven loop)
      get_one_prop(M, Prop),
      functor(Prop, PropF, PropA),
      \+ prop_covered(PropF, PropA, _),
        ( needed_to_prove(AnaKind, AbsInt, Prop) ->
            set_prop_covered(PropF, PropA, AbsInt)
        ; true
        ),
        fail
    ; true
    ),
    % Check if the domain is needed for some prop
    ( prop_covered(_,_,AbsInt) -> true ; fail ).

needed_to_prove_def(AnaKind, Ana, P) :-
    preferred_ana(AnaKind, Ana),
    P =.. [F,_|Rest],
    PP =..[F|Rest],
    knows_of(PP,Ana),!.

:- doc(bug, "needed_to_prove/3 is a weird predicate, it must be
    more easy to read. --EMM.").

:- pred needed_to_prove(+AnaKind, ?AbsInt, +Prop)
   # "Domain @var{AbsInt}, of kind @var{AnaKind} is needed to prove
     property @var{Prop}.".

% a predicate to avoid different format of knows_of/2
needed_to_prove(modes, _, ground(_)) :- !.
needed_to_prove(modes, _, free(_)) :- !.
% This handles most of the cases
needed_to_prove(AnaKind, AbsInt, P) :- needed_to_prove_def(AnaKind, AbsInt, P), !.
%
needed_to_prove(ana_det, _, P) :- needed_to_prove(ana_cost, _, P).
needed_to_prove(ana_det, _, P) :- needed_to_prove(ana_size, _, P).
% but: we need nf for proving lower bounds or disproving upper bounds
needed_to_prove(ana_nf, _, P) :- needed_to_prove(ana_cost, _, P).
needed_to_prove(ana_nf, _, P) :- needed_to_prove(ana_size, _, P).
% ... and types and modes for other stuff
needed_to_prove(types, _, P) :- needed_to_prove(ana_nf, _, P).
needed_to_prove(types, _, P) :- needed_to_prove(ana_cost, _, P).
needed_to_prove(types, _, P) :- needed_to_prove(ana_size, _, P).
needed_to_prove(types, _, regtype(_)).
needed_to_prove(modes, _, P) :- needed_to_prove(ana_nf, _, P).
needed_to_prove(modes, _, P) :- needed_to_prove(ana_cost, _, P).
needed_to_prove(modes, _, P) :- needed_to_prove(ana_size, _, P).
needed_to_prove(ana_cost, _, P) :-
% because knows_of/2 works differently for size props.
    P =.. [F|As],
    PP =.. [F,_|As],
    needed_to_prove(ana_size, _, PP).
:- else.

%! # Automatic Domain Selection Algorithm
%
% 1. For each property:
%    1. Select what domains to use to verify it (disjunction of
%       conjunctions).
%    2. Add possible instrumental domains, e.g., resources would need
%       to run types, modes, non-failure and determinism domains in
%       advance.
%    3. Simplify obtained disjunction of conjunctions.
% 2. Simplify the obtained conjunction of disjunction of conjunctions,
%    obtaining a disjunctions of conjunctions
% 3. Sort these conjunctions using heuristics.
% 4. Take first combination from the list.
%
% Differences with menu-based approach:
%
% - Former automatic domain selection code iterated over each
%   "preferred domain" and each property; the new algorithm simply
%   iterates over properties.
% - Former code selected domains for each property occurrence in the
%   code; the new algorithm, for each property (using functor/3).
% - Former code chose one domain for each property, which could result
%   in incomplete domain selection; new algorithm obtains all possible
%   complete combinations of domains. E.g., the former algorithm would
%   choose only a domain (shfr, eterms, or steps_ualb) to check a
%   steps_o/2 property; the new algorithm would obtain a disjunction
%   of conjunctions (eterms^shfr^nf^det^steps_ualb or
%   eterms^shfr^nfdet^steps_ualb or nfdet^steps_ualb...).
%

%% For automatic domain selection
:- use_module(spec(static_abs_exec_table), [abs_ex/4]).
:- use_module(spec(abs_exec), [determinable/2]).

:- use_module(library(lists), [cross_product/2]).
:- use_module(library(llists), [append/2, flatten/2]).
:- use_module(library(sort), [keysort/2, sort/2]).

%! ## Domains to use from previous analysis

% Several domains of the same "kind" can be selected.
anakinds_to_absints(_AnaKinds, _Menu, AbsInts) :-
    % TODO: Not needed? current_fact(selected_domains(Selected)) should fail.
    get_menu_flag(~ctcheck_menu_name, dom_sel, auto),
    current_pp_flag(intermod, off), !,
    %
    ( current_fact(selected_domains(Selected)) -> true
    ; throw(no_decide_domains) % bug
    ),
    ( Selected = [] ->
        warning_message("no domain candidates found by decide_domains/1")
    ; true
    ),
    % TODO: Select more than one combination.
    ( Selected = [[]] ->
        warning_message("There are no assertions reachable (from local or imported predicates) and you have not selected any analysis.")
    ; true
    ),
    Selected = [AbsInts|_]. % NOTE: commit to first selection; was nondet: member(AbsInts, Selected). (JFMC)
anakinds_to_absints(AnaKinds, Menu, AbsInts) :-
    anakinds_to_absints_menu(AnaKinds, Menu, AbsInts).

% ------------------------------------------------------------------------

%! ## Set anaflags after properties analysis

:- data selected_domains/1.

cleanup_decide_domains :-
    retractall_fact(prop_covered(_,_,_)),
    retractall_fact(selected_domains(_)).

select_anaflags_monolithic(AnaFlags0) :-
    sort_with_heuristics(AnaFlags0, AnaFlags),
    assertz_fact(selected_domains(AnaFlags)).

sort_with_heuristics(AnaFlags0, AnaFlags) :-
    assign_score(AnaFlags0, AnaFlags1),
    keysort(AnaFlags1, AnaFlags2),
    get_values(AnaFlags2, AnaFlags).

% TODO: Work on heuristics.
assign_score([], []).
assign_score([X|Xs], [H-X|Ys]) :-
    assign_score_(X, H),
    assign_score(Xs, Ys).

assign_score_([], 0).
assign_score_([X|Xs], H) :-
    assign_score_(Xs, H0),
    ( preferred_ana(_, X) ->
        H = H0
    ; H is H0 + 1
    ).

% TODO: Duplicated.
get_values([], []).
get_values([_-V|Xs], [V|Ys]) :-
    get_values(Xs, Ys).

% ------------------------------------------------------------------------

%! ## Automatically Pick Domains
% New algorithm to automatically pick what domains to use when
% verifying assertions. Domain kinds are irrelevant.
% TODO: Be careful when sorting domains, e.g., shfr should run before resources.

% TODO: Take into account combined domains.
decide_domains_monolithic(_AnaKinds, AnaFlags) :-
    cleanup_decide_domains,
    % First, obtain disjunctions conjunctions of needed domains
    ( % (failure-driven loop)
      curr_file(_, M),
      get_one_prop(M, Prop),
      functor(Prop, F, A),
        \+ is_prop_covered(F, A, _),
        findallsort(AbsInt, domain_native_property(Prop, AbsInt), AbsIntDisj),
        \+ AbsIntDisj = [], % Skip properties with no domains --
                            % otherwise we get an empty list of
                            % candidate domains (JFMC) (this bug
                            % manifests with '--gen-lib-cache')
        add_auxiliary_domains(AbsIntDisj, LLAbsInt),
        set_prop_covered(F, A, LLAbsInt),
        fail
    ; true
    ),
    findallsort(Dom, is_prop_covered(F, A, Dom), AnaFlags0),
    % Simplify conjunction of disjunctions of conjunctions to
    % disjunctions of conjunctions.
    domains_disjunction(AnaFlags0, AnaFlags).

:- meta_predicate findallsort(?, goal, ?).

findallsort(Template, Generator, Set) :-
    findall(Template, Generator, List),
    sort(List, Set).

% Cache to store whether a (native) property was already covered in
% previously selected domains AbsInt. E.g., if shfr covers groundness,
% do not run eterms/nf (they also know about groundess).
:- data prop_covered/3.

set_prop_covered(F, A, LLAbsInt) :-
    assertz_fact(prop_covered(F, A, LLAbsInt)).

is_prop_covered(F, A, LLAbsInt) :-
    current_fact(prop_covered(F, A, LLAbsInt)).

%! ### Deciding Domains from Properties
% TODO: Should be a domain operation.

:- multifile(aidomain/1).

% If we have a plai domain understanding the property, we will not use
% nonplai domains.
domain_native_property(Prop, AbsInt) :-
    ( plai_domain_native_property(Prop, _) ->
        plai_domain_native_property(Prop, AbsInt)
    ; nonplai_domain_native_property(Prop, AbsInt)
    ).

plai_domain_native_property(Prop, AbsInt) :-
    functor(Prop,F,A),
    ( F = regtype ->
        Determ = types
    ; abs_ex(F/A,Determ,_,_),
      use_types_just_for_types(Determ,F/A)
    ),
    determinable(AbsInt,Determ).

% Avoid using types domains to analyze instantiation properties
% (ground/1, not_free/1, var/1, free/1).
use_types_just_for_types(types,Prop) :-
    abs_ex(Prop,Determ,_,_),
    Determ \= types, !,
    fail.
use_types_just_for_types(_,_).

nonplai_domain_native_property(Prop, AbsInt) :-
    ( knows_of(Prop, _) ->
        Prop1 = Prop
    ; functor(Prop, P, N),
      M is N - 1,
      functor(Prop1, P, M)
    ),
    knows_of(Prop1, AbsInt).

%! ### Auxiliary domains
% Adds auxiliary domains to list of selected domains.
% TODO: Should be a domain operation

:- doc(add_auxiliary_domains(L0, L1), "Adds auxiliary domains needed
   to run @var{L0}, returning the result in @var{L0}.").

:- pred add_auxiliary_domains(L0, L1)
   : ( list(atom, L0), var(L1) )
   => ( list(atom, L0), list(list(atom), L1) ).

add_auxiliary_domains(AbsInts0, AbsInts) :-
    add_auxiliary_domains_(AbsInts0, AbsInts1),
    append(AbsInts1, AbsInts2),
    sort(AbsInts2, AbsInts).

add_auxiliary_domains_([], []).
add_auxiliary_domains_([AbsInt|AbsInts0], [Needed|AbsInts1]) :-
    auxiliary_domains(AbsInt, Others),
    ( Others = [] ->
        Needed = [[AbsInt]]
    ; cross_product([[AbsInt]|Others], Needed0),
      sort_each(Needed0, Needed1),
      sort(Needed1, Needed)
    ),
    add_auxiliary_domains_(AbsInts0, AbsInts1).

% TODO: Should be a domain operation.
auxiliary_domains(Res, [T,M,N,D]) :-
    ( Res = resources
    ; Res = steps_lb
    ; Res = steps_o
    ; Res = steps_ualb
    ; Res = steps_ub
    ), !,
    all_types_domains(T),
    all_modes_domains(M),
    all_nonfailure_domains(N),
    all_determinism_domains(D).
auxiliary_domains(NfDet, [T,M]) :-
    ( NfDet = nfg
    ; NfDet = detg
    ), !,
    all_types_domains(T),
    all_modes_domains(M).
auxiliary_domains(_, []).

%% :- compilation_fact(complete_aux_dom_selection).

% Exponential number of auxiliary domains.
:- if(defined(complete_aux_dom_selection)).

all_types_domains(T) :-
    findall(Types, determinable(Types, types), T).

all_modes_domains(M) :-
    findall(Modes, determinable(Modes, sharing), M).

all_nonfailure_domains(N) :-
    % TODO: When in determinable/2, use: findall(Nf, determinable(Nf, nonfailure), N).
    findall(Nf, knows_of(not_fails, Nf), N).

all_determinism_domains(D) :-
    % TODO: When in determinable/2, use: findall(Det, determinable(Det, determinism), D).
    findall(Det, knows_of(is_det, Det), D).

% Single "preferred" auxiliary domain.
:- else.

all_types_domains([T]) :-
    preferred_ana(types, T).

all_modes_domains([M]) :-
    preferred_ana(modes, M).

all_nonfailure_domains([N]) :-
    preferred_ana(ana_nf, N).

all_determinism_domains([D]) :-
    preferred_ana(ana_det, D).

:- endif.

sort_each([], []).
sort_each([X|Xs], [Y|Ys]) :-
    sort(X, Y),
    sort_each(Xs, Ys).

%! ### Domains list processing
% Predicates to obtain the final domain list as a disjunction of
% conjunctions.
% TODO: Take into account combined domains.

domains_disjunction(Conjunction, Disjunction) :-
    cross_product(Conjunction, CrossProduct),
    append_each(CrossProduct, Disjunction0),
    sort(Disjunction0, Disjunction).

append_each([], []).
append_each([X|Xs], [Y|Ys]) :-
    append(X, Y0),
    sort(Y0, Y),
    append_each(Xs, Ys).
:- endif.

:- pred preferred_ana(+AnaKind, -AbsInt)
   # "Domain @var{AbsInt} is the preferred analysis of kind
     @var{AnaKind}.".

% Preferred analyses of different kind.
% Cannot use the flags here, as default values of the flags
% are often 'none'
preferred_ana(types,    eterms).
preferred_ana(modes,    shfr).
preferred_ana(ana_num,  polyhedra). %PP: just guessing
preferred_ana(ana_nf,   nf). % TODO: was nfg (NFGRAPH-based)
preferred_ana(ana_cost, steps_ualb). % IG: why duplicated?, possible choicepoints
preferred_ana(ana_cost, resources).
preferred_ana(ana_size, size_ualb).
preferred_ana(ana_det,  det).

% TODO: ad-hoc for modular ct checking (it fixes types and modes)
decide_domains_intermod([], []).
decide_domains_intermod([AnaKind|AnaKinds], [f(AnaKind, AbsInt)|AnaFlags]):-
    decide_domain_intermod(AnaKind, AbsInt),
    decide_domains_intermod(AnaKinds, AnaFlags).

% TODO: ad-hoc for intermod ct checking (it fixes types and modes)
decide_domain_intermod(types, eterms) :- !.
decide_domain_intermod(modes, shfr) :- !.
decide_domain_intermod(_AnaKind, none).

% Select menu flags AnaFlags for analysis (setting each AnaKind to the
% corresponding AbsInt)
select_anaflags_intermod([]).
select_anaflags_intermod([f(AnaKind,AbsInt)|AnaFlags]) :-
    set_menu_flag(~ctcheck_menu_name,AnaKind,AbsInt),
    select_anaflags_intermod(AnaFlags).

% ---------------------------------------------------------------------------
% Decide necessary domains from assertions to be checked

% Enumerate all native props Prop (see prop_to_native/2) from check
% assertions of module M
get_one_prop(M,Prop) :-
    relevant_assertion(M,Body),
    assertion_body(_,_,Call,Succ,Comp,_,Body),
    ( member(Prop0,Succ)
    ; member(Prop0,Call)
    ; member(Prop0,Comp)
    ),
    ( prop_to_native(Prop0,Prop) -> true ).  % Avoids choicepoints.

% The assertion Body is relevant for ctchecks:
%  - calls assertions from libraries
%  - calls, success, or comp assertions if:
%    - M1 is M (our own module)
%    - any module if ct_modular=all
relevant_assertion(M,Body) :-
    % IG: if we use assertion_read instead, all assertions from all libraries
    % are considered. If the libraries are not cached, pgm_assertion_read
    % includes the libraries as well.
    %pgm_assertion_read(_,M1,check,Kind,Body,_,Base,_,_),
    %
    % TODO: JF: using assertion_read/9 again to make sure that we can
    %   check calls to libraries, as it seems to be used in
    %   take_assertion/4
    %
    assertion_read(_,M1,check,Kind,Body,_,Base,_,_),
    ( M \== M1, is_library(Base) ->
        % assume that one does not check libraries with auto
        Kind = calls
    ; ( M == M1
      ; current_pp_flag(ct_modular,all)
      ) ->
        ( Kind = comp ; Kind = success ; Kind = calls )
    ; fail
    ).

% ---------------------------------------------------------------------------
% Auto check certificate

auto_check_certificate(Program) :-
    module(Program,Info),
    fail_if_module_error(Info), !,
    atom_concat(Program,'.cert',Cert_Name),
    restore(Cert_Name),
    domain(Domain),
    store_previous_analysis(Domain),
    checker(Checker),
    catch(with_pp_flags([fixpoint = Checker,
                         widencall = off], analyze(Domain)),
          certif_error(X),
          error_message("Certificate and program do not match")),
    ( var(X)-> acheck ; abort).
auto_check_certificate(_Program) :-
    error_message("Aborted certificate checking.").

%% *** This is cheating a little bit... GP
checker(Fixpoint):-
    get_menu_flag(~ctcheck_menu_name, reduced_cert, REDCERT),
    ( REDCERT = off ->
        Fixpoint = check_di3
    ; Fixpoint = check_reduc_di
    ).

:- push_prolog_flag(multi_arity_warnings, off).

% ---------------------------------------------------------------------------
:- pred auto_optimize(F)
   # "Optimize file @var{F} with the current options (use
   @tt{customize(optimize)} to change these options).".
auto_optimize(File) :-
    auto_optimize(File, _).

:- pred auto_optimize(F, OFile)
   # "Same as @pred{auto_optimize/1} but the output file will be @var{OFile}.".
auto_optimize(File, OFile) :-
    module(File,Info),
    ( fail_if_module_error(Info) ->
        get_menu_flag(opt, inter_optimize, P),
        with_pp_flags([dump_ai = off], exec_optimize_and_output(P, OFile)),
        set_last_file(File)
    ;
        error_message("Optimization aborted.")
    ), !.
auto_optimize(File, _) :-
    error_message("INTERNAL ERROR: Unexpected error when executing ~w", [auto_optimize(File)]).

:- pop_prolog_flag(multi_arity_warnings).

exec_optimize_and_output(P, OFile) :-
    exec_optimize(P),
    ( nonvar(P), own_output(P) ->
        true
    ; do_output(OFile, opt)
    ).

own_output(_) :- fail. % (default)
:- if(defined(has_ciaopp_extra)).
own_output(poly_spec). % TODO: poly_spec performs its own output
:- endif.

% TODO: not used anymore (JF)
% get_domain_list([],_,[],[]).
% get_domain_list([L|Ls],AnaOrCheck,Ds,Ns):-
%     get_menu_flag(AnaOrCheck, L, none),  %No analysis to perform.
%     !,
%     get_domain_list(Ls,AnaOrCheck,Ds,Ns).
% get_domain_list([L|Ls],AnaOrCheck,[D|Ds],Ns):-
%     get_menu_flag(AnaOrCheck, L, D),
%     valid_mod_analysis(D), % Valid modular analysis domain.
%     !,
%     get_domain_list(Ls,AnaOrCheck,Ds,Ns).
% get_domain_list([L|Ls],AnaOrCheck,Ds,[L|Ns]):-
%     get_domain_list(Ls,AnaOrCheck,Ds,[Ns]). % Non-valid modular analysis domain.

entry_policy_value(assertions,force_assrt).
entry_policy_value(registry,top_level).

% success_policy_value(assertions,top).
% success_policy_value(registry,under_all).

exec_optimize(none) :- !.
:- if(defined(has_ciaopp_extra)).
exec_optimize(parallelize) :- !, exec_parallelize.
:- endif.
exec_optimize(spec) :- !, exec_spec.
exec_optimize(slice) :- !, exec_slice.
:- if(defined(has_ciaopp_extra)).
exec_optimize(poly_spec) :- !, exec_poly_spec.
:- endif.
exec_optimize(O) :-
    error_message("Unknown optimization: ~w", [O]).

:- if(defined(has_ciaopp_extra)).
exec_parallelize :-
    get_menu_flag(para, pp_info, PP),
    ( PP == on -> Flags = [dump_ai = on]
    ; Flags = []
    ),
    with_menu_flags(para, with_pp_flags(Flags, exec_parallelize_)).

exec_parallelize_ :-
    get_menu_flag(para, para_ann, Ann),
    get_menu_flag(para, para_grain, Gr),
    get_menu_flag(para, modes, Mode),
    get_menu_flag(para, ana_nf, NF),
    get_menu_flag(para, ana_det, Det),
    get_menu_flag(para, types, Types),
    ( Mode == none -> true
    ; analyze(Mode)
    ),
    ( (Ann == uoudg, Det == det) ->
        analyze(Types),
        analyze(Det)
    ; true
    ),
    ( (Ann == uudg, Det == det) ->
        analyze(Types),
        analyze(Det)
    ; true
    ),
    ( (Ann == disjwait, Det == det) ->
        analyze(Types),
        analyze(Det)
    ; true
    ),
    ( (Ann == tgudg) ->
         analyze(Types),
         analyze(steps_ub)
    ; true
    ),
    ( ( Gr \== none, NF \== none) ->
         analyze(Types),
         analyze(NF)
    ; true
    ),
    transform(Ann),
    %
    get_menu_flag(para, vers, VERS),
    ( VERS == on -> transform(vers) ; true ).
:- endif.

exec_spec :-
    spec_flags(Flags, []),
    with_menu_flags(spec, with_pp_flags(Flags, exec_spec_)).

exec_spec_ :-
    get_menu_flag(spec, peval_ana, P),
    analyze(P),
    get_menu_flag(spec, spec_poly, SP),
    get_menu_flag(spec, min_crit, Min),
    get_menu_flag(spec, inter_opt_arg_filt, AF),
    ( Min == none ->
        ( SP == off  ->
            ( AF == on ->
                transform(codegen_af)
            ; transform(codegen)
            )
        ; transform(codegen),
          decide_transform(SP),
          ( AF = on ->
              transform(arg_filtering)
          ; true
          )
        )
    ; transform(codegen_min)
    ).

spec_flags -->
    { get_menu_flag(spec, local_control, LocalControl) },
    ( { LocalControl \== off } ->
        [fixpoint = di]
    ; []
    ).

exec_slice :-
    spec_flags(Flags, []),
    with_menu_flags(spec, with_pp_flags(Flags, exec_slice_)).

exec_slice_ :-
    get_menu_flag(spec, peval_ana, P),
    analyze(P),
    get_menu_flag(spec, spec_poly, SP),
    get_menu_flag(spec, inter_opt_arg_filt, AF),
    transform(slicing),
    decide_transform(SP),
    ( AF = on ->
        transform(arg_filtering)
    ; true
    ).

:- if(defined(has_ciaopp_extra)).
exec_poly_spec :-
    sp_poly_flags(Flags, []),
    with_menu_flags(sp_poly, with_pp_flags(Flags, exec_poly_spec_)).

exec_poly_spec_ :-
    analyze(pd),
    transform(codegen_poly).

sp_poly_flags -->
    { get_menu_flag(sp_poly, aggressivity, C) },
    set_spec_strategy(C),
    [fixpoint = poly_spec].

set_spec_strategy(aggressive) -->
    [poly_global_control = [hom_emb,dyn]],
    [poly_local_control = [[local_control(det),comp_rule(leftmost),unf_bra_fac(1)],
                           [local_control(df_hom_emb_as),comp_rule(bind_ins_jb),unf_bra_fac(0)]]].
set_spec_strategy(normal) -->
    [poly_global_control = [hom_emb]],
    [poly_local_control = [[local_control(df_hom_emb_as),comp_rule(bind_ins_jb),unf_bra_fac(0)],
                           [local_control(det),comp_rule(leftmost),unf_bra_fac(1)]]].
set_spec_strategy(conservative) -->
    [poly_global_control = [hom_emb]],
    [poly_local_control = [[local_control(inst)],
                           [local_control(det),comp_rule(leftmost),unf_bra_fac(1)]]].
:- endif.

decide_transform(off) :-
    true. % nothing to to
decide_transform(mono) :-
    analyze(seff),
    transform(simp).
decide_transform(poly) :-
    analyze(seff),
    transform(spec).

% ---------------------------------------------------------------------------
% Auxiliary for modular analysis
maybe_main(File, MainFile) :-
    get_menu_flag(~ctcheck_menu_name, main_module,Main),
    ( Main = '$default' -> MainFile = File
    ; MainFile = Main
    ).

% ---------------------------------------------------------------------------

:- if(defined(has_ciaopp_llvm)).
:- include(ciaopp_llvm(auto_interface_llvm)). % LLVM-based frontend
:- endif.

:- if(defined(has_ciaopp_java)).
:- include(ciaopp(auto_interface_java)). % Java support (JNL)
:- endif.
