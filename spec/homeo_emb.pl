:- module(homeo_emb, [
    homeomorphic_embedded/2,
    homeomorphic_embedded_num/2,
    homeomorphic_embedded_type/2
], [assertions]).

:- use_module(library(lists), [member/2, length/2]).
:- use_module(library(terms_check), [ask/2]).
:- use_module(library(assertions/assrt_lib), [assertion_body/7]).
:- use_module(library(compiler/p_unit/assrt_db), [assertion_read/9]).
:- use_module(library(aggregates), [findall/3]).
:- use_module(typeslib(typeslib), [get_type_definition/2]).

:- doc(homeomorphic_embedded(Term1,Term2), "The term @var{Term1} is
     homeomorphically embedded in term @var{Term2}.").

%% Code taken from Michael Leuschel %%

%% homeomorphic_embedded(X,Y) :- var(X),!,
%%   (nonvar(Y) -> (print(h(X,Y)),nl) ; true).
%homeomorphic_embedded(X,Y) :- number(X),number(Y),!.
homeomorphic_embedded(X,Y) :- var(X),var(Y),!.
homeomorphic_embedded(_X,Y) :-
    var(Y),!,fail.
%% homeomorphic_embedded(X,Y) :-
%%      nonvar(X),dynamic_term(X),
%%      nonvar(Y),dynamic_term(Y),!.
homeomorphic_embedded(X,Y) :-
    strict_instance_of(X,Y),!,
    % print('$*'),debug_print('$'(X,Y)),
    fail.
homeomorphic_embedded(X,Y) :- /* coupling for unary constructors */
    nonvar(X),nonvar(Y),
    X=..[Func,XArg],
    Y=..[Func,YArg],
    !, /* do not try diving for unary matching constructors */
    homeomorphic_embedded(XArg,YArg),!.
homeomorphic_embedded(X,Y) :- /* coupling */
    nonvar(X),nonvar(Y),
    X=..[Func|XArgs],
    Y=..[Func|YArgs],
    l_homeomorphic_embedded(XArgs,YArgs),!.
homeomorphic_embedded(X,Y) :- /* diving */
    nonvar(Y),
    term_nesting_level(X,NX,SumX),
    sub_term(Y,Sub),
    term_nesting_level(Sub,NSub,SumSub),
    NSub>=NX,
    SumSub>=SumX,
    /*print(sub_term(Y,Sub)),nl,*/
    homeomorphic_embedded(X,Sub),!.

%% l_homeomorphic_embedded(X,Y) :- 
%%      print(l_homeomorphic_embedded(X,Y)),nl,fail.
l_homeomorphic_embedded([],[]).
l_homeomorphic_embedded([X|TX],[Y|TY]) :-
    homeomorphic_embedded(X,Y),!,
    l_homeomorphic_embedded(TX,TY).


/* CHECK WHETHER THIS IS REALLY USEFUL */
/* term_nesting_level(_,0,0) :- !. */

term_nesting_level(X,0,0) :- var(X),!.
term_nesting_level(X,1,1) :- atomic(X),!.
term_nesting_level(X,N,S) :- nonvar(X),!,
    X=..[_F|Args],
    l_term_nesting_level(Args,NA,SA),
    N is NA + 1,
    S is SA + 1.

l_term_nesting_level([],0,0).
l_term_nesting_level([H|T],N,S) :-
    term_nesting_level(H,NH,SH),
    l_term_nesting_level(T,NT,ST),
    max(NH,NT,N),
    S is SH + ST.

sub_term(X,Sub) :-
    nonvar(X),
    X=..[_F|Args],
    member(Sub,Args).

% ciao specific

strict_instance_of(Goal1,Goal2) :-
    copy_term(Goal1,CGoal),
    ask(CGoal,Goal2),
    \+(ask(Goal2,CGoal)).

max(X,Y,X) :- X >= Y,!.
max(X,Y,Y) :- Y > X.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred homeomorphic_embedded_num(T1,T2) # "Same as homeomorphic_embedded,
    but also considers that any number embeds any other number.".

homeomorphic_embedded_num(X,Y) :- number(X),number(Y),!.
homeomorphic_embedded_num(X,Y) :- var(X),var(Y),!.
homeomorphic_embedded_num(_X,Y) :-
    var(Y),!,fail.
%% homeomorphic_embedded_num(X,Y) :-
%%      nonvar(X),dynamic_term(X),
%%      nonvar(Y),dynamic_term(Y),!.
homeomorphic_embedded_num(X,Y) :-
    strict_instance_of(X,Y),!,
    % print('$*'),debug_print('$'(X,Y)),
    fail.
homeomorphic_embedded_num(X,Y) :- /* coupling for unary constructors */
    nonvar(X),nonvar(Y),
    X=..[Func,XArg],
    Y=..[Func,YArg],
    !, /* do not try diving for unary matching constructors */
    homeomorphic_embedded_num(XArg,YArg),!.
homeomorphic_embedded_num(X,Y) :- /* coupling */
    nonvar(X),nonvar(Y),
    X=..[Func|XArgs],
    Y=..[Func|YArgs],
    l_homeomorphic_embedded_num(XArgs,YArgs),!.
homeomorphic_embedded_num(X,Y) :- /* diving */
    nonvar(Y),
    term_nesting_level(X,NX,SumX),
    sub_term(Y,Sub),
    term_nesting_level(Sub,NSub,SumSub),
    NSub>=NX,
    SumSub>=SumX,
    /*print(sub_term(Y,Sub)),nl,*/
    homeomorphic_embedded_num(X,Sub),!.

%% l_homeomorphic_embedded_num(X,Y) :- 
%%      print(l_homeomorphic_embedded_num(X,Y)),nl,fail.
l_homeomorphic_embedded_num([],[]).
l_homeomorphic_embedded_num([X|TX],[Y|TY]) :-
    homeomorphic_embedded_num(X,Y),!,
    l_homeomorphic_embedded_num(TX,TY).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- pred homeomorphic_embedded_type(T1,T2) # "Type-based homeomorphic embedding relation
    over atoms. It relies on emb_t/4 which defines the TbHE over typed terms".
homeomorphic_embedded_type(X,Y) :- % byMiky: Should we keep this rule?
    strict_instance_of(X,Y),!,
    fail.
homeomorphic_embedded_type(X,Y) :- 
    X=..[Func|XArgs],
    Y=..[Func|YArgs],
    collect_types(X,Types), % Looking for the corresponding predicate signatures
    l_emb_t(XArgs,Types,YArgs,Types).

:- pred emb_t(T1,Type1,T2,Type2) # "Type-based homeomorphic embedding relation
    over typed terms".
emb_t(X,_,Y,_) :- var(X),var(Y),!.
emb_t(_,_,Y,_) :- var(Y),!,fail.
emb_t(X,_,Y,_) :-
    strict_instance_of(X,Y),!,
    fail.
emb_t(X,_Tx,Y,'pe_types:f_sig') :- !,
    homeomorphic_embedded(X,Y).
emb_t(_X,_Tx,_Y,'pe_types:i_sig') :- !.
emb_t(X,Tx,Y,Ty) :- /* coupling for unary constructors */
    nonvar(X),nonvar(Y),
    X=..[Funcx,XArg],
    Y=..[Funcy,YArg],
    leq_F(Funcx,Tx,Funcy,Ty,1,[TyArg]),
    !, /* do not try diving for unary matching constructors */
    (Ty == Tx -> TxArg = TyArg
               ; dive_into_type(Tx,Funcx,1,[TxArg],_)),
    emb_t(XArg,TxArg,YArg,TyArg),!.
emb_t(X,Tx,Y,Ty) :- /* coupling */
    nonvar(X),nonvar(Y),
    X=..[Funcx|XArgs], length(XArgs,Arity),
    Y=..[Funcy|YArgs], length(YArgs,Arity),
% This rule is restricted to terms of the same arity -> Efficiency?
    leq_F(Funcx,Tx,Funcy,Ty,Arity,TyArgs),
    !,
    (Ty == Tx -> TxArgs = TyArgs
               ; dive_into_type(Tx,Funcx,Arity,TxArgs,_)),
    l_emb_t(XArgs,TxArgs,YArgs,TyArgs),!.

emb_t(X,Tx,Y,Ty) :- % diving 
    nonvar(Y),
    term_nesting_level(X,NX,SumX),
    sub_typedterm(Y,Ty,Sub,Tsub),
    term_nesting_level(Sub,NSub,SumSub),
    NSub>=NX,
    SumSub>=SumX,
    emb_t(X,Tx,Sub,Tsub),!.

l_emb_t([],[],[],[]).
l_emb_t([X|RX],[Tx|RTx],[Y|RY],[Ty|RTy]) :-
    emb_t(X,Tx,Y,Ty),!,
    l_emb_t(RX,RTx,RY,RTy).

leq_F(F,T,F,T,Arity,TArgs) :- !,
    dive_into_type(T,F,Arity,TArgs,_).
leq_F(_F1,_T1,F2,T2,Arity,T2Args) :-
    dive_into_type(T2,F2,Arity,T2Args,InF),
    (InF == true -> fail
                  ; true).
% This rule assumes that every type rule has at the end the infinite part 'term'

dive_into_type(Type,Func,Arity,TArgs,true) :-
    get_type_definition(Type,TDefs),
    (number(Func) -> TDef = Func
    ; (Func = '.' ->(length(TArgs,Arity),
                     TDef =..[Func|TArgs])
                   ;(TDef =..[^,Aux], 
                     length(TArgs,Arity),
                     Aux =..[Func|TArgs]))),
    member(TDef,TDefs),!.
dive_into_type(_Type,_Func,Arity,TArgs,false) :-
% In case the type is not consistent we assume the pe_type by default (i_sig,..,i_sig)
    length(TArgs,Arity),
    fill_list(TArgs,'pe_types:i_sig').
    
collect_types(Atom,Types) :-
    assertion_read(Atom,_M,Status,comp,Body,_VarNames,_S,_LB,_LE),
    member(Status,[trust,true]),
    assertion_body(Atom,_Compat,Call,_Succ,Comp,_Comm,Body),
    member('basic_props:pe_type'(_Goal),Comp),!,
    findall(FPTi,(member(PTi,Call),functor(PTi,FPTi,_)),Types).
collect_types(Atom,Types) :-
    functor(Atom,_,N),
    length(Types,N),
    fill_list(Types,'pe_types:i_sig').

fill_list([],_).
fill_list([TypeByDefault|R],TypeByDefault) :-
    fill_list(R,TypeByDefault).

sub_typedterm(X,Tx,Sub,Tsub) :-
    X =..[Fx|Argsx],length(Argsx,Arity),
    dive_into_type(Tx,Fx,Arity,TxArgs,_),
    par_member(Sub,Tsub,Argsx,TxArgs).

par_member(X,Y,[X|_],[Y|_]).
par_member(X,Y,[_|T1],[_|T2]) :- par_member(X,Y,T1,T2).
