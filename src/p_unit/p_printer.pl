:- module(p_printer, [
    % TODO: syntax/operators may not be OK! use print_program/1
    print_assrt/2, % from deepfind_src/assrt_string.pl
    print_program/1
   ], [assertions, regtypes, hiord, datafacts]).

:- use_package(ciaopp(p_unit/p_unit_argnames)).

:- use_module(library(lists), [member/2, append/3]).
:- use_module(engine(stream_basic)).
:- use_module(engine(io_basic)).
:- use_module(library(format)).
:- use_module(library(messages)).
:- use_module(library(pretty_print), [pretty_print/4]).
:- use_module(library(assertions/assrt_write)).

:- use_module(library(aggregates)).

:- use_module(ciaopp(preprocess_flags)).
:- use_module(ciaopp(p_unit),
              [get_comment/1, pr_key_get/1, get_commented_assertion/2,
               get_assertion/2, get_output_operator/3]).
:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).

:- use_module(ciaopp(frontend_driver), 
              [check_global_props/2, % TODO: move this pred somewhere else
               add_srcloc_prop/0]). 
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(ciaopp(p_unit/clause_db), [source_clause/3, clause_locator/2]).
:- use_module(ciaopp(p_unit/unexpand), [
    transform_clause_list/3,
    transform_assrt_body/3,
    transform_head/3,
    transform_body/3,
    transform_assrt_body/3]).
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2, current_itf/3]).

:- use_module(engine(runtime_control), [push_prolog_flag/2, pop_prolog_flag/1]). % TODO: find a better solution

:- doc(bug, "translate_assertions/4 throws an error when the analysis
       returns unsolved cost equations instead of cost function").

% ---------------------------------------------------------------------------
:- doc(section, "Print program").

:- pred print_program(S)
    # "Prints the current program information into human readable format.".

print_program(S) :-
    with_mod_syntax(print_program_(S)).

print_program_(S) :-
    % Output comments (at the beginning)
    get_all_comments(Comments),
    print_comments(Comments, S),
    % Print the directives
    get_printable_directives(Direcs),
    print_directives(Direcs, S),
    ( curr_file(_,M) -> true ; true ), % TODO: base mod for unexpand, allow many for multiple output
    % print the clauses and its assertions in the proper order
    ( % (failure-driven loop)
      pr_key_get(Goal), % TODO: wrong name in pr_key_get
        print_from_prkey(S, M, Goal),
        fail
    ; true
    ),
    % impl_defined predicates do not have clauses, and thus are not enumerated
    % by pr_key_get/1, because it is added by p_unit:add_clause/3. Why not
    % enumerate using itf_db?
    ( % (failure-driven loop)
      current_itf(impl_defines,Goal,M),
        print_from_prkey(S, M, Goal),
        fail
    ; true
    ),
    % print new directives added during unexpansion % TODO: is there a better way?
    print_new_directives(Direcs, S).

% Print directive that may have been introduced during the output
% TODO: this is weird... doing output twice could produce different results!
print_new_directives(Direcs, S) :-
    % (failure-driven loop)
    ( get_printable_directives(Direcs2),
      member(D2, Direcs2),
        \+ member(D2, Direcs),
        print_directive(D2, S),
        fail
    ; true
    ).

% TODO: use failure-driven loops instead of findall/3 when possible
print_from_prkey(S, M, PrKey) :- !,
    % Get everything for the given key
    findall(CA, get_commented_assertion(PrKey, CA), CAs),
    get_filtered_assertions(PrKey, AsFiltered),
    % TODO: SLOW! add reverse index from Head to ClIds
    findall(C, get_clause(PrKey, C), Cls),
    % Print everything
    print_assrts(CAs, S),
    print_assrts(AsFiltered, S),
    print_clauses(Cls, M, S),
    nl(S).

get_clause(H, clause(H,B):ClId*Dict) :-
    current_fact(source_clause(ClId,clause(H,B),Dict)).

% ---------------------------------------------------------------------------

get_printable_directives(Direcs) :-
    findall(Cl, get_printable_directive(Cl), Direcs).

get_printable_directive(directive(Body):ClId*Dict) :-
    curr_file(Src, _),
    current_fact(source_clause(ClId, directive(Body), Dict)),
    \+ special_directive(Body),
    ( clause_locator(ClId, loc(Src, _, _)) -> true % declared in curr_file
    ; ClId = '\6\newdirective' % or added by add_directive/1 % TODO: kludge, add a separate db? (not source_clause/3)
    ).

special_directive(D) :-
    functor(D, F, _),
    special_directive_(F).

% TODO: any better way?
special_directive_(comp).
special_directive_(exit). 
special_directive_(entry).
special_directive_(true).
special_directive_(false).
special_directive_(success).
special_directive_(calls).
special_directive_(check).
special_directive_(checked).
special_directive_(pred). % Assertion 
special_directive_(module).
special_directive_(texec).
special_directive_(test).

% ---------------------------------------------------------------------------

:- export(get_filtered_assertions/2).
% Enumerate all (filtered) assertions
get_filtered_assertions(Goal, AsFiltered) :-
    get_all_assertions(Goal, As),
    ( current_pp_flag(output_show_tautologies, off) ->
        filter_tautologies(As, AsFiltered)
    ; As = AsFiltered 
    ).

get_all_assertions(Goal, AsrList) :-
    findall(Asr, get_assertion(Goal, Asr), AsrList).

% TODO: wrong name and probabily not the best idea (calls indicate reachability?)
filter_tautologies( [], [] ).
filter_tautologies( [A|As], AsF ) :-
    is_tautology( A ),
    !,
    filter_tautologies( As, AsF ).
filter_tautologies( [A|As], [A|AsF] ) :-
    filter_tautologies( As, AsF ).

is_tautology(A) :-
    A = as${ type => calls, call => Call },
    it_has_some_true( Call ).

it_has_some_true( [A|As] ) :- 
    (it_has_some_true_1( A ) ; it_has_some_true( As )),!.
it_has_some_true( (A;As) ) :- 
    (it_has_some_true_1( A ) ; it_has_some_true( As )),!.

it_has_some_true_1( [] ) :- !.  

% ---------------------------------------------------------------------------

get_all_comments(Comments) :-
    findall(C, get_comment(C), Comments).

% ---------------------------------------------------------------------------
:- doc(section, "Print directives").

print_directives([], _).
print_directives([Cl|Cls], S) :-
    print_directive(Cl, S),
    print_directives(Cls, S).

print_directive(directive(Body):_ClId*Dic, S) :-
    pretty_print(S, directive(Body), [], Dic),
    nl(S).

% ---------------------------------------------------------------------------
:- doc(section, "Print clauses").

:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(formulae), [llist_to_disj/2]).

:- use_module(ciaopp(infer/infer_db), [domain/1, point_info/5]).
:- use_module(ciaopp(p_unit), [type_of_goal/2]).

print_clauses([], _M, _).
print_clauses([Cl|Cls], M, S) :-
    print_clause(Cl, M, S),
    print_clauses(Cls, M, S).

print_clause(clause(H1,B1):Clid*Dic, M, S) :-
    ( current_pp_flag(pp_info, off) ->
        H = H1, B = B1
    ; % TODO: do as transformation instead? (it simplifies something)
      findall(AbsInt,domain(AbsInt),Domains), % TODO: not here!
      dump_clause(clause(H1, B1), Clid, Domains, clause(H, B))
    ),
    clause_remove_litkey(clause(H, B), Cl1b),
    transform_clause_list([Cl1b], M, Cls2),
    pretty_print(S, Cls2, [], [Dic]).

clause_remove_litkey(clause(A, B), clause(A, BT)) :- !,
    body_remove_litkey(B, BT).
clause_remove_litkey(_, _) :-
    throw(ciaopp_bug(clause_remove_litkey/2)).

body_remove_litkey((L, Ls), (LT, LTs)) :- !,
    body_remove_litkey(L,  LT),
    body_remove_litkey(Ls, LTs).
body_remove_litkey((L ; Ls), (LT ; LTs)) :- !,
    body_remove_litkey(L,  LT),
    body_remove_litkey(Ls, LTs).
body_remove_litkey('->'(L, Ls), '->'(LT, LTs)) :- !,
    body_remove_litkey(L,  LT),
    body_remove_litkey(Ls, LTs).
body_remove_litkey('andprolog_rt:&'(L, Ls),'andprolog_rt:&'(LT, LTs)) :- !, % TODO: can it be moved elsewhere?
    body_remove_litkey(L,  LT),
    body_remove_litkey(Ls, LTs).
body_remove_litkey(':'(L, _), L) :- !.
body_remove_litkey(L, L).

% Insert program point info between body literals
dump_clause(clause(Head,Body),Clid,Domains,clause(Head,NewBody)):- 
    varset((Head,Body),Vars),
    Body2 = (Body,'\6\cl_end_mark'(Clid)),
    dump_body(Body2,dump_lit(Vars,Domains),NewBody).

% TODO: simplify
dump_body(Cl , Hook , NCl) :-
    dump_body_(Cl , Hook , NCl),
    !.
dump_body(Cl , _ , Cl) :-
    error_message("Internal error: dump_body: Unable to process ~p.",[Cl]).

dump_body_(B, Hook, NNB) :-
    dump_body__(B, Hook, NB),
    remove_true_literals(NB, NNB).

dump_body__(Lit, _Hook, Lit) :-
    var(Lit), !.
dump_body__(Lit, Hook, Out) :-
    ( Lit = (A, B) ;
      Lit = (A; B), Out = (NA;NB)  ;
      Lit = (A->B), Out = (NA->NB) ),
    !,
    dump_body__( A , Hook , NA ),
    dump_body__( B , Hook , NB ),
    ( Lit = (_,_) -> literal_concat( NA , NB , Out ) ; true ).
dump_body__( B , Hook , NB ) :-
    Hook = dump_lit(Vars,Domains),
    dump_lit(B, Vars, Domains, NB),
    !.
dump_body__( A , _Hook , A ) :-
    error_message("Internal error: dump_lit: Unable to process ~p.", [A]).

% TODO: be careful when removing 'true'! (code is not always equivalent)
% Remove 'true' from the body @var{L}. The result is @var{NL}.
remove_true_literals(A, A) :-
    var(A),
    !.
remove_true_literals((B,A), B) :-
    (A == (true:_) ; A == true),
    !.
remove_true_literals((A,B), C) :-
    (A == (true:_) ; A == true),
    !,
    remove_true_literals(B, C).
remove_true_literals((A,B), C) :-
    remove_true_literals(A, AC),
    !,
    remove_true_literals(B, BC),
    literal_concat(AC, BC, C).
remove_true_literals((A->B), (AC->BC)) :-
    !,
    remove_true_literals(A, AC),
    remove_true_literals(B, BC).
remove_true_literals((A;B), (A;C)) :-
    !,
    remove_true_literals(B, C).
remove_true_literals(A, A).

%%% --- New Version
% literal_concat((A,B), C, D) :-
%       (A = true ; A = true:_),
%       !,
%       literal_concat(B, C, D).
literal_concat(Lit, C, D) :-
    Lit == (A,B),
    !,
    literal_concat(B, C, D1),
    literal_concat(A, D1, D).
% literal_concat((A,B), C, (A,D)) :-
%       !,
%       literal_concat(B, C, D).
literal_concat(Lit, C, ((A;B),C)) :-
    Lit == (A;B),
    !.
literal_concat(A, B, B) :-
    (A == true ; A == true:_),
    !.
literal_concat(A, B, A) :-
    (B == true ; B == true:_),
    !.
literal_concat(A, B, (A,B)).

dump_lit('\6\cl_end_mark'(Clid),Vars,Domains, AtInfo) :- !,
    atom_info(Domains, Clid, Vars, AtInfo, true).
dump_lit(At:Key, Vars, Domains, AtInfo) :-
    atom_info(Domains, Key, Vars, AtInfo, At:Key),
    !.
dump_lit(At, _Vars, _Domains, At).

atom_info([Dom|Domains], Key, Vars, (Info,InfoT), Tail) :-
    atom_info_(Dom, Key, Vars, Info),
    atom_info(Domains, Key, Vars, InfoT, Tail).
atom_info([], _Key, _Vars, Tail, Tail).

atom_info_(AbsInt, Key, Vars, G) :-
    current_fact(point_info(Key,AbsInt,_Vars,_FVars,_Info)),
    !,
    findall((Vars,Info),
            current_fact(point_info(Key,AbsInt,Vars,_FVars,Info)),
            List),
    get_infos(List, Vars, ListInfo0),
    % take out identical info
    sort(ListInfo0, ListInfo),
    llist_to_disj(ListInfo, Goal),
    (type_of_goal(builtin(true(Goal)),G) -> true
    ; G = true(Goal)).
atom_info_(_Dom, _Key, _Vars, true).

get_infos([(Vars,Info)|List],Vars,[Info|ListInfo]):-
    get_infos(List,Vars,ListInfo).
get_infos([],_Vars,[]).

% ---------------------------------------------------------------------------
:- doc(section, "Print assertions").

print_assrts([], _).
print_assrts([A|As], S) :-
    %( ignore_print_assrt(A) -> true
    %    ; print_assrt(A, S), nl(S)
    %),
    print_assrt(A, S), nl(S),
    print_assrts(As, S).

%ignore_print_assrt(A) :-
%    A = as${
%        type => Type,
%        fromwhere => From
%    },
%    \+ From == commented, % TODO: write test assertions in this case too?
%    Type == test.

print_assrt(A, S) :-
    A = as${
        module => M,
        status => Status,
        type => Type,
        head => Head,
        compat => Compat,
        call => Call,
        succ => Succ,
        comp => Comp0,
        dic => Dic,
        % comment => UserComment,
        fromwhere => From,
        locator => loc(Src, LB, LE)
    },
    ( var(Head) ->
        throw(error(unbound_head, print_assrt/2))
    ; true
    ),
    % --- add original line numbers in comp field
    ( add_srcloc_prop, Type \= texec -> 
        SrcLoc = srcloc(Head, Src, LB, LE),
        ( LB =\= 0, LE =\= 0 -> append(Comp0, [SrcLoc], Comp) ; Comp = Comp0 ) 
    ;
        Comp = Comp0
    ),
    % --- inverse rewrite program
    assertion_body(Head, Compat, Call, Succ, Comp, [], Body),
    % TODO: printing discards the comments of all assertions
    transform_head(Head, M, HeadT),
    transform_assrt_body(Body, M, BodyT),
    check_global_props(BodyT, BodyT2),
    ( Dic = no ->
        % create_dict((HeadT:-BodyT), _VN),
        % dict2varnamesl(_VN, VN)
        create_dict_with_assrt_and_cl(Head, VN)
    ; VN = Dic
    ),
    ( (Type = entry ; Type = prop ; Type = texec) ->
        WriteStatus = nostatus
    ; WriteStatus = status
    ),
    ( From == commented ->
        ( Type == pred ->
            write_assertion_as_double_comment(S, HeadT, Status, Type, BodyT2, VN, WriteStatus)
        ; write_assertion_as_comment(S, HeadT, Status, Type, BodyT2, VN, WriteStatus)
        )
    %; Type == test ->
    %    true
    ; write_assertion(S, HeadT, Status, Type, BodyT2, VN, WriteStatus)
    ).

% ---------------------------------------------------------------------------

:- use_module(library(vndict)).
:- use_module(ciaopp(p_unit/assrt_db)).

% TODO: we still see a lot of _NNN vars; is this not working properly?
% TODO: slow? simpler alternatives? (like get the Dic of the first assertion)

:- pred create_dict_with_assrt_and_cl( Head , NDic )
    : (term(Head),var(NDic))
# "For a given head @var{Head} (from assertion or a clause), a new
  dictionary @var{NDic} is returned using the dictionaries found in
  the assertions and clauses that match the same head. @var{NDic} is
  returned in Assertions Dictionary format. You would have to use
  @pred{varnamesl2dict/2} in order to transform it to Clauses
  Dictionary. Note that @var{Head} can have any constructor on its
  arguments, but those wont be completed.".

create_dict_with_assrt_and_cl(Head, NDic) :-
    functor(Head, FF, AA),
    functor(H, FF, AA),
    findall(hd(H,D), dict_for_head(H, D), HDLIST),
    Head =.. [_|Args],
    complete_goal_dic(HDLIST, Args, [], NDic).

dict_for_head(H, D) :-
    ( assertion_read(H,_,_,_,_,D,_,_,_), D\==no
    ; % TODO: SLOW! add reverse index from Head to ClIds
      current_fact(source_clause(_ClId,clause(H,_B),VND)),
      dict2varnamesl(VND, D)
    ).

:- pred complete_goal_dic(HDLIST, GoalArgsList, InitialDic, Dics)
# "@var{HDLIST} is a list with hd(Goal,Dict) as
   elements. @var{GoalArgList} are the list of arguments of the goal
   we want to complete the dictionary. @var{InitialDic} is the initial
   dictionary we could have. If you do not have it, just use an empty
   list, []. @var{Dics} is the dictionary returned as a list of pair
   atom=variable. Example:

@begin{verbatim}
?- complete_goal_dic( [hd(ap(A1,A2,A3),
                  [=('A',A1),=('B',A2),=('C',A3)])], [E,D,F] , [] , DF ).

D = A2,
DF = ['C'=A3,'B'=A2,'A'=A1],
E = A1,
F = A3 ? 
@end{verbatim}
".

complete_goal_dic([hd(G,D)|Hds], GoalArgs, Dic, DicS) :-
    G =.. [_|GArgs],
    complete_goal_dic__(GArgs, D, GoalArgs, Dic, Dic1),
    complete_goal_dic(Hds, GoalArgs, Dic1, DicS).
complete_goal_dic([], _, D, D).

complete_goal_dic__([GA|GAs], D, [GoalArg|GoalArgs], Dic, Dics) :-
    % GA has some name (A), which is not already used
    var(GA),
    ( member(A=GA0, D), GA == GA0 -> true ; fail ),
    \+ member(A=_, Dic),
    % no name for GoalArg yet
    var(GoalArg),
    \+ ( member(_=GoalArg0, Dic), GoalArg0 == GoalArg ),
    %
    GA = GoalArg,
    !,
    complete_goal_dic__(GAs, D, GoalArgs, [A=GA|Dic], Dics).
complete_goal_dic__([_|GAs], D, [_|GoalArgs], Dic, Dics) :-
    complete_goal_dic__(GAs, D, GoalArgs, Dic, Dics).
complete_goal_dic__([], _, _, Dic, Dic).

% ---------------------------------------------------------------------------
:- doc(section, "Print comments").

% E.g., print_comments(["line1\nline2","line3"], user_output) produces:
%   % line1
%   % line2
%   % line3
% Trailing newlines for each comment string are ignored.

print_comments([], _S).
print_comments([C|Cs], S) :-
    write_comment(C, S),
    print_comments(Cs, S).

write_comment(C, S) :-
    comment_string(C, C2),
    format(S, "~s~n", [C2]).

comment_string(Cs, "% "||Cs2) :-
    comment_string_(Cs, Cs2).

comment_string_([], []) :- !.
comment_string_([0'\n], []) :- !. % remove last nl
comment_string_([0'\n|Cs], [0'\n|Cs2]) :- !, comment_string(Cs, Cs2).
comment_string_([C|Cs], [C|Cs2]) :- !, comment_string_(Cs, Cs2).

% ---------------------------------------------------------------------------
:- doc(section, "Call with an specific operator table").
% TODO: separate in itw own module

:- use_module(library(port_reify), [once_port_reify/2, port_call/1]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(library(compiler/c_itf), [define_ops/0]).
:- use_module(library(operators)).

:- export(with_mod_syntax/1).
:- meta_predicate with_mod_syntax(goal).
:- pred with_mod_syntax(G) # "Call @var{G} with the syntax definitions
   (operators) given by @pred{get_output_operator/3}".

with_mod_syntax(G) :-
    set_mod_operators(Prev),
    push_prolog_flag(write_strings, on), % TODO: make it optional?
    once_port_reify(call(G), Res),
    ( pop_prolog_flag(write_strings) -> true ; true ),
    undo_mod_operators(Prev),
    port_call(Res).

:- pred set_mod_operators(Prev) # "Set operators from
   @pred{get_output_operator/3}, saving the previous setting in @var{Prev}.".

set_mod_operators(Prev) :-
    findall(o(A,B,C), current_op(A, B, C), Prev),
    reset_ops,
    ( get_output_operator(A, B, C),
        op(A, B, C),
        fail
    ; true
    ),
    % TODO: do before or after get_output_operator/3 is used?
    standard_ops,
    define_ops.

:- pred undo_mod_operators(Prev) # "Restore previous operators from @var{Prev}.".
undo_mod_operators(Prev) :-
    reset_ops,
    ( member(o(A,B,C), Prev),
        op(A, B, C),
        fail
    ; true
    ).

reset_ops :-
    ( current_op(_, B, C),
        C \= ',', % (cannot redefine ','/2 in ISO)
        op(0, B, C),
        fail
    ; true
    ).

