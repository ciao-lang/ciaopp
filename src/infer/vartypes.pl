:- module(vartypes,[],[assertions, datafacts]).

:- use_module(ciaopp(infer/infer), [get_info/5]).
:- use_module(ciaopp(infer/infer_db), [inferred/3]).
:- use_module(ciaopp(infer/infer_dom), [knows_of/2]).

:- use_module(ciaopp(p_unit), [prop_to_native/2]).
:- use_module(ciaopp(p_unit/program_keys), [get_predkey/3]).

:- use_module(typeslib(typeslib), [set_top_type/1]).
:- use_module(ciaopp(plai/domains), [asub_to_info/5, unknown_entry/4]).

:- use_module(library(idlists), [memberchk/2]).
:- use_module(library(messages)).
:- use_module(library(terms_vars), [varset/2]).

%-------------------------------------------------------------------------

:- export(gather_vartypes/2).
gather_vartypes(Cls,Trusts):-
    get_type_trusts(Cls,0,Trusts,[]).

get_type_trusts([Cl|Program],K,Trusts,TrustsN):-
    get_type_trust(Cl,K,NK,Trusts,Trusts0),
    get_type_trusts(Program,NK,Trusts0,TrustsN).
get_type_trusts([],_K,Trusts,Trusts).

get_type_trust(clause(H,_):_,K,NK,Trusts,Trusts0):-
    functor(H,F,A),
    K\==F/A, !,
    NK=F/A,
    get_predkey(F,A,Key),
    functor(Goal,F,A),
    get_one_type_trust(Key,Goal,Trusts,Trusts0).
get_type_trust(_,K,K,Trusts,Trusts).

get_one_type_trust(Key,Goal,Trusts,Trusts0):-
    get_info(vartypes,pred,Key,Goal,(Call,Succ)), !,
    Trusts=[( :- trust(Goal,Call,Succ) ) |Trusts0].
get_one_type_trust(_Key,_Goal,Trusts,Trusts).

%-------------------------------------------------------------------------

:- export(get_vartype/4).
get_vartype(Key,Goal,Call,Succ):-
    current_fact(inferred(vartypes,Key,vartype(Goal,Call,Succ))).
get_vartype(Key,Goal,Call,Succ):-
    get_info(free,pred,Key,Goal,(CallF,SuccF)),
    get_info(ground,pred,Key,Goal,(CallG,SuccG)), !,
    get_regtype_info(Key,Goal,CallT,SuccT),
    join_info(CallT,CallF,CallG,Call),
    join_info(SuccT,SuccF,SuccG,Succ),
    asserta_fact(inferred(vartypes,Key,vartype(Goal,Call,Succ))).
%get_vartype(_Key,_Goal,Call,Succ). % should get trusts!

get_regtype_info(Key,Goal,Call,Succ):-
    get_info(regtypes,pred,Key,Goal,(Call,Succ)), !.
get_regtype_info(Key,Goal,ASub,ASub):-
    warning_message("There is no type information for: ~w",[Key]),
    varset(Goal,Qv),
    knows_of(regtypes,AbsInt),
    unknown_entry(AbsInt,Goal,Qv,ASub0),
    asub_to_info(AbsInt,ASub0,Qv,ASub,_).

join_info(CallT,CallF,CallG,Call):-
    set_top_type(Top),
    any_to_free(CallT,Top,CallF,CallG,Call).

any_to_free([Type|Types0],T,Fr,Gr,Types):-
    any_or_type(Type,T,Fr,Gr,Types,Types1),
    any_to_free(Types0,T,Fr,Gr,Types1).
any_to_free([],_Top,_Fr,_Gr,[]).

any_or_type(Type,T,Fr,Gr,Types,Types0):- 
    prop_to_native(Type,regtype(Native)),
    functor(Native,T,1), !,
    arg(1,Type,X),
    any_to_free_one(X,Fr,Gr,Type,Types,Types0).
any_or_type(Type,_Top,_Fr,_Gr,[Type|Types],Types).

any_to_free_one(X,Fr,_Gr,_Type,Types,Types0):-
    memberchk(X,Fr), !,
    Types=[var(X)|Types0].
any_to_free_one(X,_Fr,Gr,_Type,Types,Types0):-
    memberchk(X,Gr), !,
    Types=[gnd(X)|Types0].
any_to_free_one(_,_Fr,_Gr,Type,[Type|Types0],Types0).

