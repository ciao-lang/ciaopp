:- module(codegen,[codegen/4,codegen_af/4,codegen_min/4, create_all_dicts/2],[datafacts]).

:- use_package(spec(no_debug)).
:- use_package(spec(nomem_usage)).
:- use_package(assertions).

:- use_module(spec(global_control), 
    [spec_def_for/8, spec_wrt/3, locate_spec_definition/3]).
:- use_module(spec(sp_clauses), [sp_clause/2, orig_predicate_names/1]).
:- use_module(spec(arg_filtering), 
    [ 
      clean_up_filters/0,
      create_filters/2,
      create_filters_exported/2,
      filter/3,
      list_exported/3
    ]).
:- use_module(spec(spec_support), [change_call/3]).
:- use_module(spec(spec_multiple), [mult_spec_unf/3]).
:- use_module(spec(s_simpspec), [make_atom/2]).
:- use_module(spec(unfold_times), [global_time_ellapsed/3]).
:- use_module(spec(unfold_operations), [orig_pred_name/2]).
:- use_module(spec(min_unf), 
    [
        is_canonical/1,
        find_canonical_rep/4,
        gen_equivs/0,
        clean_up_min_unf_facts/0,
        generalize_and_flatten/2
     ]).

:- use_module(ciaopp(plai/fixpo_ops), [remove_useless_info/1]).
:- use_module(ciaopp(plai/plai_db), [complete/7, memo_table/6]).
:- use_module(ciaopp(p_unit/program_keys),
    [decode_litkey/5, decode_clkey/4, rewrite_source_all_clauses/2,
     cleanup_program_keys/0, get_predkey/3, get_predkeys/2]).
:- use_module(ciaopp(p_unit/assrt_db), 
    [assertion_read/9,
     add_assertion_read/9, 
     assertion_body/7]).
:- use_module(ciaopp(plai/fixpo_ops), [collect_exported_completes/2]).

:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(terms), [copy_args/3]). 
:- use_module(library(aggregates), [findall/3]). 
:- use_module(ciaopp(analysis_stats), [pp_statistics/2]). 
:- use_module(library(sort), [sort/2]). 
:- use_module(library(lists), [member/2, append/3, length/2]). 
:- use_module(library(vndict), [create_pretty_dict/2]). 

:- doc(codegen(+Abs,-Sp_program,-Sp_Dicts), "@var{Sp_Program} is
      the specialized program generated when analysis performs
      unfolding.").
codegen(Abs,Sp_program,Sp_Dicts,[TimeInfo,MemoryInfo]):-
    common_pre_codegen(Abs,Orig_Prog,Init_sp),
%
    create_filters_exported(Init_sp,Abs),
%
    common_post_codegen(Orig_Prog,Sp_program,Sp_Dicts,T),
    TimeInfo = time(T,[]),
    ask_mem_usage(Delta,Details),
    MemoryInfo = memory(Delta,Details),
    message(inform, ['{transformed by codegen in ', ~~(T),' msec.}']).

:- doc(codegen_af(+Abs,-Sp_program,-Sp_Dicts), "@var{Sp_Program}
      is the specialized program generated when analysis performs
      unfolding and argument filtering is activated.").

codegen_af(Abs,Sp_program,Sp_Dicts,[TimeInfo,MemoryInfo]):-
    common_pre_codegen(Abs,Orig_Prog,Init_sp),
%
    create_filters(Init_sp,Abs),
%
    common_post_codegen(Orig_Prog,Sp_program,Sp_Dicts,T),
    TimeInfo = time(T,[]),
    ask_mem_usage(Delta,Details),
    MemoryInfo = memory(Delta,Details),
    message(inform, ['{transformed by codegen_af in ', ~~(T),' msec.}']).
    
common_pre_codegen(Abs,Orig_Prog,Init_sp):-
    pp_statistics(runtime,_),
    reset_mem_usage,
    clean_up_filters,
    remove_useless_info(Abs),
    collect_exported_completes(Abs,Init),
    list_exported(Init,Abs,Init_sp),
    rename_completes_but_exported(Init_sp),
    rename_memo_tables(Init,Abs),
    rename_orig_clauses(Init_sp,Abs),
    collect_code(Abs,Orig_Prog).%update_mem_usage

common_post_codegen(Orig_Prog,Sp_Prog,Sp_Dicts,T):-
    cleanup_program_keys,
    rewrite_source_all_clauses(Orig_Prog,Orig_Prog1),
    replace_calls(no,Orig_Prog1,Sp_Prog),
    create_all_dicts(Sp_Prog,Sp_Dicts),
    clean_up_filters,
    orig_predicate_names(Preds),
    get_predkeys(Preds,Keys),
    rename_assertions(Preds,Keys),%update_mem_usage
    pp_statistics(runtime,[_,T]).

:- pred rename_completes_but_exported(+Ids) # "This is needed since
       completes remain with the original name of the predicate,
       instead of the newly created predicate. Since predicates which
       are exported are not renamed, @var{Id} is used in order to
       avoid renaming completes for exported call patterns.".
rename_completes_but_exported(Ids):-
    current_fact(complete(_Key,Abs,Sg,D,E,Id,G),Ref),
    Id \== no,
    \+ member(Id,Ids),
    locate_spec_definition(Id,NF,A),
    erase(Ref),
    get_predkey(NF,A,NKey),
    functor(NSg,NF,A),
    copy_args(A,Sg,NSg),
    assertz_fact(complete(NKey,Abs,NSg,D,E,Id,G)),
    fail.
rename_completes_but_exported(_).

:- pred rename_memo_tables(+Ids,+Abs) # "The case of memo tables is
    different from that of completes. Whereas completes after
    analysis still refer to the predicates in the original
    program, memo tables already refer to the newly generated
    predicates. Thus the problem is the contrary, we have to
    rename the memo tables for exported predicates (which are not
    renamed) to use the name of their original predicate".

rename_memo_tables(Ids,AbsInt):-
    findall(OldId,
            (member(Id,Ids),
             current_fact(complete(_,_,_,_,_,Id,_)),
             spec_wrt(Id,AbsInt,OldId)),
             Completes),
    sort(Completes,Completes_s),
    get_definitions(Completes_s,[],Clauses),
    cleanup_program_keys,
    rewrite_source_all_clauses(Clauses,Clauses_Id),
    rename_all_memo_tables(Clauses_Id,AbsInt).

rename_all_memo_tables([],_AbsInt).
%% % facts may not have memo_tables stored.
%% rename_all_memo_tables([clause(Head,true:Id):ClId|Clauses]):-!,
%%      rename_all_memo_tables(Clauses).
rename_all_memo_tables([clause(Head,Body):ClId|Clauses],AbsInt):-
    functor(Head,NF,_),
    orig_pred_name(NF,F),
    rename_all_memo_tables_in_body(Body,F,AbsInt),
    rename_memo_table_for_clause(ClId,F,AbsInt),
    rename_all_memo_tables(Clauses,AbsInt).

rename_memo_table_for_clause(Clid,F,AbsInt):-
    current_fact(memo_table(Clid,AbsInt,Id,Son,Vars_U,Call),Ref),!,
    decode_clkey(Clid,_Pred,Arity,C),
    make_atom([F,Arity,C],NClid),
    erase(Ref),
    assertz_fact(memo_table(NClid,AbsInt,Id,Son,Vars_U,Call)).
% clauses with only a fail in their body do not have memo_tables!
rename_memo_table_for_clause(_Clid,_F,_AbsInt).


rename_all_memo_tables_in_body((L,R),F,AbsInt):-!,
    rename_all_memo_tables_in_literal(L,F,AbsInt),
    rename_all_memo_tables_in_body(R,F,AbsInt).
rename_all_memo_tables_in_body(L,F,AbsInt):-
    rename_all_memo_tables_in_literal(L,F,AbsInt).

rename_all_memo_tables_in_literal(!,_F,_AbsInt):-!.
rename_all_memo_tables_in_literal(\+($(_L,B:OtherKey,_C)):Key,F,AbsInt):-!,
    rename_memo_tables_pp(Key,F,AbsInt),
    find_son_identif(B,OtherKey,SonKey),
    rename_memo_tables_pp(SonKey,F,AbsInt).
rename_all_memo_tables_in_literal('aggregates:findall'(_Var,$(_L,_B:SonKey,_C),_List):Key,F,AbsInt):-
    !,
    rename_memo_tables_pp(Key,F,AbsInt),
    rename_memo_tables_pp(SonKey,F,AbsInt).
rename_all_memo_tables_in_literal('aggregates:setof'(_Var,$(_L,_B:SonKey,_C),_List):Key,F,AbsInt):-
    !,
    rename_memo_tables_pp(Key,F,AbsInt),
    rename_memo_tables_pp(SonKey,F,AbsInt).
rename_all_memo_tables_in_literal('aggregates:bagof'(_Var,$(_L,_B:SonKey,_C),_List):Key,F,AbsInt):-
    !,
    rename_memo_tables_pp(Key,F,AbsInt),
    rename_memo_tables_pp(SonKey,F,AbsInt).
rename_all_memo_tables_in_literal(_:Key,F,AbsInt):-
    rename_memo_tables_pp(Key,F,AbsInt),!.

rename_all_memo_tables_in_literal(Lit,_,_AbsInt):-
    debug('Hmm :'),
    debug(Lit).

rename_memo_tables_pp(Key,F,AbsInt):-
    current_fact(memo_table(Key,AbsInt,Id,Son,Vars_U,Call),Ref),
    decode_litkey(Key,_Pred,Arity,C,L),
    make_atom([F,Arity,C,L],NKey),
    erase(Ref),
    assertz_fact(memo_table(NKey,AbsInt,Id,Son,Vars_U,Call)),
    (Son \== no ->
     replace_pointers(Son,Id,F,AbsInt)
    ),
    fail.
rename_memo_tables_pp(_Key,_F,_AbsInt).

%% rename_memo_tables_id(Id,Abs):-
%%      current_fact(complete(_,Abs,Sg,_,_,Id,_)),
%%      functor(Sg,F,_),
%%      current_fact(memo_table(Key,Abs,Id,Child,Vars_u,Call),Ref),
%%      erase(Ref),
%%      (decode_litkey(Key,_Pred,Arity,C,L) ->
%%          make_atom([F,Arity,C,L],NKey),
%%          replace_pointers(Child,Id,F,Abs)
%%      ;
%%          decode_clkey(Key,_Pred,Arity,C),
%%          make_atom([F,Arity,C],NKey)
%%      ),
%%      asserta_fact(memo_table(NKey,Abs,Id,Child,Vars_u,Call)),
%%      fail.
%% rename_memo_tables_id(_Id,_Abs).
    
:- pred replace_pointers(+Child,+Id,+F,+Abs) # "Since the completes
    for the children of this @var{Id} have pointers with the newly
    generated predicates, since for exported predicates we use the
    original name, we have to reconstruct the backwards pointers
    in the children completes to use the original names.".
replace_pointers(no,_Id,_F,_Abs):-!.
replace_pointers(Child,Id,F,Abs):-
    current_fact(complete(A,Abs,C,D,E,Child,Parents),Ref),
    erase(Ref),
    replace_parents(Parents,Id,F,NewParents),
    assertz_fact(complete(A,Abs,C,D,E,Child,NewParents)).
 
replace_parents([],_Id,_F,[]).
replace_parents([(Key,Id)|Parents],Id,F,NewParents):-!,
    NewParents = [(NKey,Id)|NParents],
    decode_litkey(Key,_,Arity,C,L),
    make_atom([F,Arity,C,L],NKey),
    replace_parents(Parents,Id,F,NParents).
replace_parents([P|Parents],Id,F,[P|NewParents]):-
    replace_parents(Parents,Id,F,NewParents).

:- pred collect_code(+AbsInt,-Clauses) # "Returns in @var{Clauses} the
    code for all predicates in the specialized program. For this,
    we first collect all remaining completes, i.e., predicate
    implementations, and then get the specialized definition for
    each of them.".
collect_code(AbsInt,Clauses):-
    findall(OldId,
            (current_fact(complete(_,_,_,_,_,Id,_)),
             spec_wrt(Id,AbsInt,OldId)),
             Completes),
    sort(Completes,Completes_s),
    get_definitions(Completes_s,[],Clauses).

:- pred collect_code_canonical(+AbsInt,-Clauses) #
    "Returns in @var{Clauses} the code for all predicates in the
    specialized program. For this, we first collect all remaining
    completes, i.e., predicate implementations, and then get the
    specialized definition for each of them.".
collect_code_canonical(AbsInt,Clauses) :-
    findall(OldId,
            (current_fact(complete(_,_,_,_,_,Id,_)),
             spec_wrt(Id,AbsInt,OldId),
             is_canonical(OldId)),
             Completes),
    sort(Completes,Completes_s),
    get_definitions_min(Completes_s,[],Clauses).


:- pred get_definitions_min(+Ids,+Visited,-Clauses) # "Returns in
      @var{Clauses} the specialized definitions for all completes in
      list @var{Ids}. The argument @var{Visited} is needed because it
      can be the case that several completes have the same specialized
      definition. Otherwise, some specialized definitions can appear
      several times in the transformed program.".

get_definitions_min([],_,[]).
get_definitions_min([Id|Ids],Visited,[ClausesPred|MoreClauses]):-
    locate_spec_definition(Id,Name,Arity),
    (member(Name/Arity,Visited) ->
        ClausesPred = [], % later is flattened
        NVisited = Visited
    ;
        functor(Head,Name,Arity),
        findall(clause(Head,Body),
                sp_clause(Head,Body),
                ClausesPred),
%           append(ClausesPred,MoreClauses,Clauses),
        NVisited = [Name/Arity|Visited]),
    get_definitions_min(Ids,NVisited,MoreClauses).




:- pred get_definitions(+Ids,+Visited,-Clauses) # "Returns in
      @var{Clauses} the specialized definitions for all completes in
      list @var{Ids}. The argument @var{Visited} is needed because it
      can be the case that several completes have the same specialized
      definition. Otherwise, some specialized definitions can appear
      several times in the transformed program.".

get_definitions([],_,[]).
get_definitions([Id|Ids],Visited,Clauses):-
    locate_spec_definition(Id,Name,Arity),
    (member(Name/Arity,Visited) ->
        Clauses = MoreClauses,
        NVisited = Visited
    ;
        functor(Head,Name,Arity),
        findall(clause(Head,Body),sp_clause(Head,Body),ClausesPred),
        append(ClausesPred,MoreClauses,Clauses),
        NVisited = [Name/Arity|Visited]),
    get_definitions(Ids,NVisited,MoreClauses).


:- pred replace_calls(Can,Orig_Prog,Sp_Prog) # "Once the clauses for all
    specialized definitions are collected, we have to call the
    appropriate implementation of each predicate in all calls
    which appear in the specialized clauses.".

replace_calls(_,[],[]).
% facts may not have memo_tables stored.
replace_calls(Can,[clause(Head,true:Id):ClId|Clauses],[NewCl|NewClauses]):-!,
    NewCl = clause(NHead,NBody):ClId,
    (current_fact(filter(_,Head,NHead)) ->
        true
    ;
        NHead = Head),
    NBody = true:Id,
    replace_calls(Can,Clauses,NewClauses).
replace_calls(Can,[clause(Head,Body):ClId|Clauses],[NewCl|NewClauses]):-
    NewCl = clause(NHead,NBody):ClId,
    (current_fact(filter(_,Head,NHead)) ->
        true
    ;
        NHead = Head),
    replace_calls_in_body(Can,Body,NBody),
    replace_calls(Can,Clauses,NewClauses).

replace_calls_in_body(Can,(L,R),(NL,NR)):-!,
    replace_calls_in_literal(Can,L,NL),
    replace_calls_in_body(Can,R,NR).
replace_calls_in_body(Can,L,NL):-
    replace_calls_in_literal(Can,L,NL).

replace_calls_in_literal(_,!,!):-!.
replace_calls_in_literal(_,builtin(B):_Clid,B:noinfo):-!.
replace_calls_in_literal(Can,\+($(L,B:OtherKey,C)):Key,NBody):-!,
    NBody = \+($(NL,B:OtherKey,C)):Key,
    find_son_identif(B,OtherKey,SonKey),
    current_fact(memo_table(SonKey,_,_,Son,_,_)),
    (Son = no ->
        NL = L
    ;
        locate_spec_definition(Son,NewName,_),
        find_canonical_rep(Can,L,NewName,Canonical),
        change_call(L,NL0,Canonical),
        (current_fact(filter(_,NL0,NL)) ->
            true
        ;
            NL = NL0
        )
    ),!.
replace_calls_in_literal(Can,'aggregates:findall'(Var,$(L,B:SonKey,C),List):Key,NBody):-
    !,
    NBody = 'aggregates:findall'(Var,$(NL,B:SonKey,C),List):Key,
    current_fact(memo_table(SonKey,_,_,Son,_,_)),
    (Son = no ->
        NL = L
    ;
        locate_spec_definition(Son,NewName,_),
        find_canonical_rep(Can,L,NewName,Canonical),
        change_call(L,NL0,Canonical),
        (current_fact(filter(_,NL0,NL)) ->
            true
        ;
            NL = NL0
        )
    ),!.
replace_calls_in_literal(Can,'aggregates:bagof'(Var,$(L,B:SonKey,C),List):Key,NBody):-
    !,
    NBody = 'aggregates:bagof'(Var,$(NL,B:SonKey,C),List):Key,
    current_fact(memo_table(SonKey,_,_,Son,_,_)),
    (Son = no ->
        NL = L
    ;
        locate_spec_definition(Son,NewName,_),
        find_canonical_rep(Can,L,NewName,Canonical),
        change_call(L,NL0,Canonical),
        (current_fact(filter(_,NL0,NL)) ->
            true
        ;
            NL = NL0
        )
    ),!.
replace_calls_in_literal(Can,'aggregates:setof'(Var,$(L,B:SonKey,C),List):Key,NBody):-
    !,
    NBody = 'aggregates:setof'(Var,$(NL,B:SonKey,C),List):Key,
    current_fact(memo_table(SonKey,_,_,Son,_,_)),
    (Son = no ->
        NL = L
    ;
        locate_spec_definition(Son,NewName,_),
        find_canonical_rep(Can,L,NewName,Canonical),
        change_call(L,NL0,Canonical),
        (current_fact(filter(_,NL0,NL)) ->
            true
        ;
            NL = NL0
        )
    ),!.
replace_calls_in_literal(Can,L:Key,NL:Key):-
    current_fact(memo_table(Key,_,_,Son,_,_)),
    (Son = no ->
        NL = L
    ;           
        locate_spec_definition(Son,NewName,_A),         
        find_canonical_rep(Can,L,NewName,Canonical),
        change_call(L,NL0,Canonical),
        (current_fact(filter(_,NL0,NL)) ->
            true
        ;
            NL = NL0
        )
    ),!.
replace_calls_in_literal(_,Lit,Lit):-
    debug('Hmm :'),
    debug(Lit).

find_son_identif(\+($(_,Body:Key,_)),_,Son):-!,
    find_son_identif(Body,Key,Son).
find_son_identif('hiord_rt:call'($(_,Body:SonKey,_)),_,Son):-!,
    (var(Body) ->
        Son = SonKey
    ;
        find_son_identif(Body,SonKey,Son)
    ).
find_son_identif(_,Key,Key).
    
%%%%%%%%%%%%%%%%%%%%%

:- pred rename_orig_clauses(+Init_sp,+Abs) # "Since we have changed
    the predicate names of exported versions, here we update the
    information stored in @pred{sp_clause/2} and in
    @pred{spec_def_for/8} in order to be consistent.".

rename_orig_clauses([],_).
rename_orig_clauses([Id|Ids],AbsInt):-
    current_fact(complete(_,AbsInt,Sg,_,_,Id,_)),
    functor(Sg,F,A),
    locate_spec_definition(Id,NF,A),
    rename_clauses(F,NF,A),
    get_predkey(F,A,Key),
    rename_unf_vers(Key,F,NF,A),
    rename_orig_clauses(Ids,AbsInt).

rename_clauses(F,NF,A):-
    functor(Head,NF,A),
    current_fact(sp_clause(Head,Body),Ref),
    erase(Ref),
    functor(NHead,F,A),
    copy_args(A,Head,NHead),
    assertz_fact(sp_clause(NHead,Body)),
    fail.
rename_clauses(_F,_NF,_A).

rename_unf_vers(Key,F,NF,A):-
    current_fact(spec_def_for(Key,Sg,Sv,Proj,AbsInt,Id,NF,A),Ref),
    erase(Ref),
    assertz_fact(spec_def_for(Key,Sg,Sv,Proj,AbsInt,Id,F,A)),
    fail.
rename_unf_vers(_Key,_F,_NF,_A).



% search for all predicates in original program
% if found, collect all versions generated
% remove exported ones
% for remaining, replicate assertions.

rename_assertions([],[]).
rename_assertions([Pred|Preds],[Key|Keys]):-
    findall((NF/A),spec_def_for(Key,_,_,_,_,_,NF,A),NewPreds),
    assertions_new_versions(NewPreds,Pred),
    rename_assertions(Preds,Keys).

assertions_new_versions([],_Pred):-!.
%one version only with same name
assertions_new_versions([Pred],Pred):-!. 
assertions_new_versions(NPreds,F/A):-
    functor(Goal,F,A),
    assertion_read(Goal,M,Status,Type,Body,VarNames,S,LB,LE),
    decide_add_extra_assert(Type,NPreds,Goal,M,Status,Body,VarNames,S,LB,LE),
    fail.
assertions_new_versions(_,_).

% entries do not need to be replicated
decide_add_extra_assert(entry,_,_,_,_,_,_,_,_,_):-!,
    fail.
decide_add_extra_assert(Type,NPreds,Goal,M,Status,Body,VarNames,S,LB,LE):-
    add_extra_assert(NPreds,Goal,M,Status,Type,Body,VarNames,S,LB,LE).

add_extra_assert([],_Goal,_M,_Status,_Type,_Body,_VarNames,_S,_LB,_LE).
add_extra_assert([NF/A|NPreds],Goal,M,Status,Type,Body,VarNames,S,LB,LE):-
    assertion_body(Goal,Compat,Call,Succ,Comp,Comm,Body),
    (functor(Goal,NF,_) ->
        true
    ;
        functor(Goal,F,A),
        functor(NewGoal,NF,A),
        copy_args(A,Goal,NewGoal),
        rebuild_comp(Comp,NewComp,F,NF),
        assertion_body(NewGoal,Compat,Call,Succ,NewComp,Comm,NewBody),
        add_assertion_read(NewGoal,M,Status,Type,NewBody,VarNames,_S,_LB,_LE)
    ),
    add_extra_assert(NPreds,Goal,M,Status,Type,Body,VarNames,S,LB,LE).

rebuild_comp([],[],_,_).
rebuild_comp([CProp|CProps],[NCProp|NCProps],F,NF):-
    functor(CProp,C,1),
    functor(NCProp,C,1),
    arg(1,CProp,Goal),
    arg(1,NCProp,NGoal),
    functor(Goal,F,A),
    functor(NGoal,NF,A),
    copy_args(A,Goal,NGoal),!,
    rebuild_comp(CProps,NCProps,F,NF).
rebuild_comp([CProp|CProps],[CProp|NCProps],F,NF):-
    rebuild_comp(CProps,NCProps,F,NF).


create_all_dicts([],[]).
create_all_dicts([Clause|Clauses],[Dict|Dicts]):-
    create_pretty_dict(Clause,Dict),
    create_all_dicts(Clauses,Dicts).

    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
codegen_min(Abs,Sp_Prog,Sp_Dicts,[TimeInfo,MemoryInfo,MinInfo]):-
    pp_statistics(runtime,_),
    reset_mem_usage,
%start minimization
    orig_predicate_names(Preds),
    mult_spec_unf(Preds,Abs,Versions),
    gen_equivs,
    pp_statistics(runtime,[GT1,T1]),
%start codegen  
    clean_up_filters,
    remove_useless_info(Abs),
    collect_exported_completes(Abs,Init),
    list_exported(Init,Abs,Init_sp),
    collect_code_canonical(Abs,Orig_Prog),
    generalize_and_flatten(Orig_Prog,Gen_Prog),
    create_filters_exported(Init_sp,Abs),
    cleanup_program_keys,
    rewrite_source_all_clauses(Gen_Prog,Rewritten_Prog),
    replace_calls(can,Rewritten_Prog,Sp_Prog),
%       add_builtins_to_prog(Sp_Prog,Sp_Program),
    create_all_dicts(Sp_Prog,Sp_Dicts),
    clean_up_filters,
    clean_up_min_unf_facts,
    get_predkeys(Preds,Keys),
    rename_assertions(Preds,Keys),
% end. perform statistics 
    pp_statistics(runtime,[GT,_T]),
    global_time_ellapsed(GT,GT1,T),
    Total is T1 + T,
    TimeInfo = time(Total,[min(T1),codegen(T)]),
    ask_mem_usage(Delta,Details),
    MemoryInfo = memory(Delta,Details),
    get_min_rate(Versions,Rate),
    MinInfo = min(Rate,Versions),
    message(inform, ['{transformed by codegen_min in ', ~~(Total),' msec.}']).


get_min_rate([OV,_,_,MV],Rate):-
    add_all(OV,Orig),
    add_all(MV,Min),
    Rate is Orig/Min.


add_all([],0).
add_all([H|T],R):-
    number(H),!,
    add_all(T,R2),
    R is H+R2.
add_all([H|T],R):-
    list(H),!,
    length(H,H2),
    add_all(T,R2),
    R is H2+R2.
