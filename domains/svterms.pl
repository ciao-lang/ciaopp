:- module(svterms, [], [assertions,regtypes,basicmodes]).

:- doc(title, "svterms: eterms + same value  (abstract domain)").
% TODO: document this domain!

% :- doc(title,"Types Abstract Domain").
% :- doc(author, "Claudio Vaucheret").
% :- doc(author, "Francisco Bueno").

% :- doc(module,"
% 
% This module implements the abstract operations of a types domain
% within the PLAI abstract interpretation framework.  An abstract
% substitution is list of Var:Type elements, where Var is a variable and
% Type is a pure type term @cite{Dart-Zobel}.
% 
% ").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(svterms).

:- use_module(domain(eterms), [                             
    eterms_call_to_entry/9,
    eterms_exit_to_prime/7,
    eterms_project/5,
    eterms_compute_lub_el/3,
    eterms_abs_sort/2,
    eterms_extend/5,
    eterms_less_or_equal/2,
    eterms_glb/3,
    eterms_unknown_call/4,
    eterms_unknown_entry/3,
    eterms_empty_entry/3,
    eterms_special_builtin/5,
    eterms_call_to_success_builtin/6,
    eterms_input_interface/4,
    eterms_input_user_interface/5,
    eterms_asub_to_native/5,
    eterms_identical_abstract/2,
    eterms_widen/3,
    eterms_widencall/3,
    eterms_concrete/3,
    keys_same_value/3,
    replaceintype/5,
    determinate_sel/3,
    getargtypes/6,
    eterms_arg_call_to_success/9]).

:- use_module(library(aggregates), [setof/3]).
:- use_module(library(terms_vars), [
    varsbag/3,
    varset/2]).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(lists), [member/2, dlist/3]).
:- use_module(library(sets), [merge/3, insert/3]).
:- use_module(library(sort), [sort/2]).

:- use_module(library(assoc), [get_assoc/3]).
:- use_module(typeslib(typeslib), [new_type_name/1, insert_type_name/3, concrete/4]).

% :- regtype absu(A) # "@var{A} is an abstract substitution".

% absu('$bottom').
% absu([]).
% absu([Elem|Absu]):- 
%       absu_elem(Elem),
%       absu(Absu).

% :- regtype absu_elem(E) # "@var{E} is a single substitution".

% absu_elem(Var:Type):-
%       var(Var),
%       pure_type_term(Type).

abssubst('$bottom','$bottom','$bottom').
abssubst((TypeComp,SameValueComp),TypeComp,SameValueComp).

abssubst_b('$bottom','$bottom',_).
abssubst_b('$bottom',_,'$bottom').
abssubst_b((TypeComp,SameValueComp),TypeComp,SameValueComp).

svmember(sv(X,Y),SV):-
    ( 
        member(sv(X,Y),SV) 
    ; 
        member(sv(Y,X),SV)
    ).

:- dom_impl(svterms, concrete/3).
:- export(svterms_concrete/3).
svterms_concrete(Var,ASub,List):-
    abssubst(ASub,TypesComp,_SV),
    eterms_concrete(Var,TypesComp,List).

%------------------------------------------------------------------%
:- dom_impl(svterms, compute_lub/2).
:- export(svterms_compute_lub/2).
svterms_compute_lub([ASub1,ASub2|Rest],Lub):-
    svterms_compute_lub_el(ASub1,ASub2,ASub3),
    svterms_compute_lub([ASub3|Rest],Lub).
svterms_compute_lub([ASub],ASub).

:- export(svterms_compute_lub_el/3).
svterms_compute_lub_el(ASub1,ASub2,ASub3):-
    abssubst(ASub1,TypesComp1,SV1),
    abssubst(ASub2,TypesComp2,SV2),
    eterms_compute_lub_el(TypesComp1,TypesComp2,TypesComp3),
    sval_lub(SV1,SV2,SV3,TypesComp3),
    abssubst_b(ASub3,TypesComp3,SV3).

determinate('$bottom',_,'$bottom'):-!.
determinate([],_,[]):-!.
determinate([sv(X/Sx,Y/Sy)|Sv],Types,[sv(X/Sx,Y/Sy)|SvP]):-
    determinate_sel(X,Sx,Types),
    determinate_sel(Y,Sy,Types),!,
    determinate(Sv,Types,SvP).
determinate([_|Sv],Types,SvP):-
    determinate(Sv,Types,SvP).

sval_lub('$bottom','$bottom','$bottom',_).
sval_lub('$bottom',SV2,SV2P,Types):- !,
    determinate(SV2,Types,SV2P).
sval_lub(SV1,'$bottom',SV1P,Types):- !,
    determinate(SV1,Types,SV1P).
sval_lub(SV1,SV2,SV3,Types):-
    determinate(SV1,Types,SV1P),
    determinate(SV2,Types,SV2P),
    (
        setof(sv(X/SVx,Y/SVy),lessrestric(X,Y,SVx,SVy,SV1P,SV2P),SV3) -> true
    ;
        SV3 = []
    ).

lessrestric(X,Y,SVx,SVy,SV1,SV2):-
    svmember(sv(X/Sx,Y/Sy),SV1),
    svmember(sv(X1/Sx1,Y1/Sy1),SV2),
    X == X1,Y == Y1,
    (
        dlist(_,Sx,Sx1),
        dlist(_,Sy,Sy1),
        SVx = Sx,
        SVy = Sy
    ;
        dlist(_,Sx1,Sx),
        dlist(_,Sy1,Sy),
        SVx = Sx1,
        SVy = Sy1
    ).

%------------------------------------------------------------------%
:- dom_impl(svterms, needs/1).
:- export(svterms_needs/1).
svterms_needs(widen).
svterms_needs(auxinfo).

:- dom_impl(svterms, widencall/3).
:- export(svterms_widencall/3).
svterms_widencall(Prime0,Prime1,Result):-
    abssubst(Prime0,TypesPrime0,SVPrime0),
    abssubst(Prime1,TypesPrime1,SVPrime1),
    eterms_widencall(TypesPrime0,TypesPrime1,TypesResult),
    sval_lub(SVPrime0,SVPrime1,SV3,TypesResult),
    abssubst_b(Result,TypesResult,SV3).
    
:- dom_impl(svterms, widen/3).
:- export(svterms_widen/3).
svterms_widen(Prime0,Prime1,NewPrime):-
    abssubst(Prime0,TypesPrime0,SVPrime0),
    abssubst(Prime1,TypesPrime1,SVPrime1),
    eterms_widen(TypesPrime0,TypesPrime1,TypesNewPrime),
    sval_lub(SVPrime0,SVPrime1,SV3,TypesNewPrime),
    abssubst_b(NewPrime,TypesNewPrime,SV3).

%------------------------------------------------------------------%

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).

:- dom_impl(svterms, init_abstract_domain/1).
:- export(svterms_init_abstract_domain/1).
svterms_init_abstract_domain([widen]) :-
    push_pp_flag(widen,on).

%------------------------------------------------------------------%
:- dom_impl(svterms, call_to_entry/9).
:- export(svterms_call_to_entry/9).
svterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,i(ExtraInfoSV,ExtraInfoType)):- 
    abssubst(Proj,TypesProj,SV_Proj),
    eterms_call_to_entry(Sv,Sg,Hv,Head,K,Fv,TypesProj,TypesEntry,ExtraInfoType),
    sv_call_to_entry(Sv,Sg,Hv,Head,K,Fv,SV_Proj,SV_Entry,ExtraInfoSV),
    %% ojo normalizar TypesEntry !!??
    determinate(SV_Entry,TypesEntry,SV_Entry2),
    abssubst_b(Entry,TypesEntry,SV_Entry2).

% :- export(sv_call_to_entry/7).

sv_call_to_entry(_Sv,Sg,_Hv,Head,_K,_Fv,SV_Proj,SV_Entry,yes(SV)):-
    variant(Sg,Head),!,
    varsbag(Sg,VSg,[]),
    varsbag(Head,VHead,[]),
    samevaluelistempty(VHead,VSg,SV),
    sort(SV,SV_s),
    samevalueequiv(SV_s,SV_Proj,SV_Entry).
sv_call_to_entry(_Sv,Sg,_Hv,Head,_K,_Fv,SV_Proj,SV_Entry,no(SV_s)):-
    varset(Head,Vars),
    get_positions_of_vars(Vars,Head,Pos),
    varset(Sg,SgVars),      
    get_positions_of_vars(SgVars,Sg,PosSg),
    samevaluelist(PosSg,Pos,SV1),
    sort(SV1,SV_s),
    samevalueequiv(SV_s,SV_Proj,NSV),
    sort(NSV,NSV_s),
    addimplicit(SV_s,SVI),
    sort(SVI,SVI_s),
    merge(NSV_s,SVI_s,SV_Entry1),
    sv_project(Vars,SV_Entry1,SV_Entry).

samevalueequiv(SV,SV_Proj,NSV):-
    (
        setof(sv(X/Sx,Y/Sy),findequiv(X,Sx,Y,Sy,SV_Proj,SV),NSV) -> true
    ;
        NSV = []
    ).

findequiv(X,Sx,Y,Sy,SV_Proj,SV):-       
    member(sv(Zk/Szk,Zl/Szl),SV_Proj),
    svmember(sv(X/Sxx,Zkk/Szkk),SV),
    Zk == Zkk,
    (
        dlist(Szx,Szk,Szkk),
        dlist(Szx,Sxp,Sxx),
        Szyy = []
    ;
        dlist(Szyy,Szkk,Szk),
        Sxp = Sxx
    ),
    svmember(sv(Y/Syy,Zll/Szll),SV),
    X \== Y,
    Zl == Zll,
    (
        dlist(Szy,Szl,Szll),
        dlist(Szy,Syp,Syy),
        Szxx = []
    ;
        dlist(Szxx,Szll,Szl),
        Syp = Syy
    ),
    dlist(Szxx,Sx,Sxp),   
    dlist(Szyy,Sy,Syp).
    % dlist(Szx,Sx,Sxx),
    % dlist(Szy,Sy,Syy).
    % dlist(Szk,Sx,Sxx),
    % dlist(Szl,Sy,Syy).

samevaluelist(Pos,PosSg,SV):-
    (
        setof(sv(X/Sx,Y/[]),samevaluevar(X,Sx,Y,Pos,PosSg),SV) -> true
    ;
        SV = []
    ).

samevaluevar(X,Sx,Y,Pos,PosSg):-
    member(X:P,Pos),
    member(S,P),
    member(Y:PY,PosSg),
    member(SY,PY),
    dlist(Sx,SY,S).
samevaluevar(X,Sx,Y,PosSg,Pos):-
    member(X:P,Pos),
    member(S,P),
    member(Y:PY,PosSg),
    member(SY,PY),
    dlist(Sx,SY,S),
    Sx\==[].

get_positions_of_vars([],_,[]).
get_positions_of_vars([X|Vars],Arg,[X:P|Pos]):-
    get_pos_var(X,Arg,P,[],[]),
    get_positions_of_vars(Vars,Arg,Pos).

get_pos_var(X,Term,[Sel|Tail],Tail,Sel):- X == Term,!.
get_pos_var(X,Term,P,Tail,Sel):-
    functor(Term,F,A),!,
    get_pos_var_arg(A,X,Term,F,Sel,P,Tail).
get_pos_var(_X,_Term,P,P,_).

get_pos_var_arg(0,_X,_Term,_F,_Sel,P,P).
get_pos_var_arg(A,X,Term,F,Sel,P,Tail):-
    arg(A,Term,Arg),
    get_pos_var(X,Arg,P,P1,[F/A|Sel]),
    A1 is A - 1,
    get_pos_var_arg(A1,X,Term,F,Sel,P1,Tail).


samevaluelistempty([],[],[]).
samevaluelistempty([VH|VHead],[VS|VSg],[sv(VH/[],VS/[])|SV]):-
    samevaluelistempty(VHead,VSg,SV).

addimplicit(SV_s,SV_I):-
    (
        setof(sv(X/Sx,Y/Sy),transitive(X,Sx,Y,Sy,SV_s), SV_I) -> true
    ;
        SV_I = []
    ).
    
transitive(X,Sx,Y,Sy,SV_s):-
      svmember(sv(X/Sxx,Z1/Sz1),SV_s),
      svmember(sv(Y/Syy,Z2/Sz2),SV_s),
      Z1 == Z2,
      ( 
          dlist(S,Sz1,Sz2),
          dlist(S,Sy,Syy),
          Sx = Sxx
      ; 
          dlist(S,Sz2,Sz1),
          dlist(S,Sx,Sxx),
          Sy = Syy
      ),
%         Z1/Sz1 == Z2/Sz2, %% ojo solo es necesario que Sz1 y Sz2 se superpongan
      X/Sx @< Y/Sy.

%-----------------------------------------------------------------------%
:- dom_impl(svterms, exit_to_prime/7).
:- export(svterms_exit_to_prime/7).
svterms_exit_to_prime(Sg,Hv,Head,Sv,Exit,i(ExtraInfoSV,ExtraInfoType),Prime):- 
    abssubst(Exit,TypesExit,SV_Exit),       
    eterms_exit_to_prime(Sg,Hv,Head,Sv,TypesExit,ExtraInfoType,TypesPrime),
    sv_exit_to_prime(Sg,Hv,Head,Sv,SV_Exit,ExtraInfoSV,SV_Prime), 
    %% ojo normalizar TypesPrime !!??
    determinate(SV_Prime,TypesPrime,SV_Prime2),
    abssubst_b(Prime,TypesPrime,SV_Prime2). 

% :- export(sv_exit_to_prime/7).

sv_exit_to_prime(_Sg,_Hv,_Head,_Sv,'$bottom',_ExtraInfo,Prime) :- !,
    Prime = '$bottom'.
sv_exit_to_prime(_Sg,_Hv,_Head,_Sv,SV_Exit,yes(SV),SV_Prime):-
    sort(SV,SV_s),
    samevalueequiv(SV_s,SV_Exit,SV_Prime).
sv_exit_to_prime(_Sg,_Hv,_Head,Sv,SV_Exit,no(SV_s),SV_Prime):-
    samevalueequiv(SV_s,SV_Exit,NSV),
    sort(NSV,NSV_s),
    addimplicit(SV_s,SVI),
    sort(SVI,SVI_s),
    merge(NSV_s,SVI_s,SV_Prime1),
    sv_project(Sv,SV_Prime1,SV_Prime).

%------------------------------------------------------------------%
:- dom_impl(svterms, project/5).
:- export(svterms_project/5).
svterms_project(Sg,Vars,HvFv_u,ASub,Proj):-
    abssubst(ASub,TypesASub,SV),
    eterms_project(Sg,Vars,HvFv_u,TypesASub,TypesProj),
    sv_project(Vars,SV,SVProj),
    abssubst_b(Proj,TypesProj,SVProj).

sv_project(_,'$bottom',SVProj):- SVProj = '$bottom'.
sv_project(Vars,SV,SVProj):-
    sv_project_aux(SV,Vars,SVProj).

sv_project_aux([],_Vars,[]).
sv_project_aux([sv(X/Sx,Y/Sy)|SV],Vars,[sv(X/Sx,Y/Sy)|SVProj]):-
    member(X1,Vars),
    X == X1,
    member(Y1,Vars),
    Y == Y1,!,
    sv_project_aux(SV,Vars,SVProj).
sv_project_aux([_|SV],Vars,SVProj):-
    sv_project_aux(SV,Vars,SVProj).
%------------------------------------------------------------------%

%------------------------------------------------------------------%
:- dom_impl(svterms, abs_sort/2).
:- export(svterms_abs_sort/2).
svterms_abs_sort(ASub,ASub_s):-
    abssubst(ASub,TASub,SV),
    eterms_abs_sort(TASub,TASub_s),
    sv_sort(SV,SV_s),
    abssubst_b(ASub_s,TASub_s,SV_s).        


sv_sort('$bottom','$bottom'):- !.
sv_sort(SV,SV_s):- 
    sort(SV,SV_s).
%------------------------------------------------------------------%

%--------------------------------------------------------------%        
:- dom_impl(svterms, extend/5).
:- export(svterms_extend/5).
svterms_extend(Sg,Prime,Sv,Call,Succ):-
    abssubst(Prime,TPrime,SVPrime),
    abssubst(Call,TCall,SVCall),
    eterms_extend(Sg,TPrime,Sv,TCall,TSucc1),
    sv_extend(SVPrime,SVCall,Sv,TSucc1,TSucc,SVSucc),
    abssubst_b(Succ,TSucc,SVSucc).

sv_extend(SV1,SV2,Sv,TSucc1,TSucc,SVSucc):-
    (
        TSucc1 \== '$bottom' ->
        splitCall(TSucc1,Sv,TOnlyCall,TRest),
        updatecall(TOnlyCall,TRest,SV2,TNewCall),
        merge(TNewCall,TRest,TSucc),
        merge(SV1,SV2,SVSucc0),
            %% ojo normalizar TSucc !!??
        determinate(SVSucc0,TSucc,SVSucc)
    ;
        TSucc = TSucc1,
        SVSucc = '$bottom'
    ).

updatecall([],_,_,[]).
updatecall([A|TOnlyCall],TRest,SV2,[NA|TNewCall]):-
    replacetype(A,TRest,SV2,NA),
    updatecall(TOnlyCall,TRest,SV2,TNewCall).

replacetype(X:Tx,TRest,SV2,X:Txn):-
    (
        svmember(sv(X1/Sx,Y/Sy),SV2),
        %% ojo siempre que no superponga a otro
        X == X1,
        member(Y1:Ty,TRest),
        Y == Y1,
        replaceintype(Tx,Sx,Ty,Sy,Txn) ->  true
    ;
        Txn = Tx
    ).

%% are Call and Prime sorted????? ojo
splitCall([],_,[],[]).
splitCall(TCall,[],TCall,[]).
splitCall([X:Tx|TCall],[Y|Sv],TOnlyCall,[X:Tx|TNewPrime]):-
    X == Y,!,
    splitCall(TCall,Sv,TOnlyCall,TNewPrime).
splitCall([X:Tx|TCall],[Y|Sv],[X:Tx|TOnlyCall],TNewPrime):-
    X @< Y,!,
    splitCall(TCall,[Y|Sv],TOnlyCall,TNewPrime).

%------------------------------------------------------------------%
:- dom_impl(svterms, less_or_equal/2).
:- export(svterms_less_or_equal/2).
svterms_less_or_equal(ASub1,ASub2):-
    abssubst(ASub1,TASub1,SV1),
    abssubst(ASub2,TASub2,SV2),
    eterms_less_or_equal(TASub1,TASub2),
    sval_less_or_equal(SV2,SV1).

sval_less_or_equal('$bottom',_ASub):- !.
sval_less_or_equal([],_):- !.
sval_less_or_equal([SV|SV2],SV1):-
    sval_contain(SV,SV1),
    sval_less_or_equal(SV2,SV1).
                
sval_contain(sv(X/Sx,Y/Sy),SV1):-
    svmember(sv(X1/Sx1,Y1/Sy1),SV1),
    X == X1,Y == Y1,
    dlist(_,Sx,Sx1), 
    dlist(_,Sy,Sy1).

%------------------------------------------------------------------%

%--------------------------------------------------------------%        
:- dom_impl(svterms, glb/3).
:- export(svterms_glb/3).
svterms_glb(ASub0,ASub1,Glb):-
    abssubst(ASub0,TASub0,SV0),
    abssubst(ASub1,TASub1,SV1),
    eterms_glb(TASub0,TASub1,TGlb),
    sv_glb(SV0,SV1,SV),
    abssubst_b(Glb,TGlb,SV).

sv_glb('$bottom',_ASub,'$bottom'):- !.
sv_glb(_ASub,'$bottom','$bottom'):- !.
sv_glb(SV0,SV1,SV):-
    merge(SV0,SV1,SV).

%--------------------------------------------------------------%        
:- dom_impl(svterms, unknown_entry/3).
:- export(svterms_unknown_entry/3).
svterms_unknown_entry(Sg,Vars,ASub):-
    eterms_unknown_entry(Sg,Vars,TASub),
    abssubst_b(ASub,TASub,[]).

%--------------------------------------------------------------%        
:- dom_impl(svterms, empty_entry/3).
:- export(svterms_empty_entry/3).
svterms_empty_entry(Sg,Vars,ASub):-
    eterms_empty_entry(Sg,Vars,TASub),
    abssubst_b(ASub,TASub,[]).

%--------------------------------------------------------------%        
% TODO: (originally marked as TO DO)
:- dom_impl(svterms, unknown_call/4).
:- export(svterms_unknown_call/4).
svterms_unknown_call(Sg,Vars,Call,Succ):-
    abssubst(Call,TCall,_SV),
    eterms_unknown_call(Sg,Vars,TCall,TSucc),
    abssubst_b(Succ,TSucc,[]).

%--------------------------------------------------------------%        
:- dom_impl(svterms, call_to_success_fact/9).
:- export(svterms_call_to_success_fact/9).
svterms_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ):-
    svterms_call_to_entry(Sv,Sg,Hv,Head,K,[],Proj,Entry,ExtraInfo),
    svterms_exit_to_prime(Sg,Hv,Head,Sv,Entry,ExtraInfo,Prime),
    svterms_extend(Sg,Prime,Sv,Call,Succ).

%--------------------------------------------------------------%        
:- dom_impl(svterms, special_builtin/5).
:- export(svterms_special_builtin/5).
svterms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars):-
    eterms_special_builtin(SgKey,Sg,Subgoal,Type,Condvars).

%--------------------------------------------------------------%        
:- dom_impl(svterms, success_builtin/6).
:- export(svterms_success_builtin/6).
svterms_success_builtin(id,_Sv_uns,_Condvars,_,Call,Call).
svterms_success_builtin(bot,_Sv_uns,_Condvars,_,_Call,'$bottom').
svterms_success_builtin(type(T),_Sv_uns,Condvars,_,Call,Succ):-
    keys_same_value(Condvars,T,TPrime),
    abssubst_b(Prime,TPrime,[]),    
    svterms_extend(not_provided_Sg,Prime,Condvars,Call,Succ).

%--------------------------------------------------------------%        
:- dom_impl(svterms, call_to_success_builtin/6).
:- export(svterms_call_to_success_builtin/6).
svterms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):-
    svterms_call_to_success_fact(p(X,Y),[W],p(W,W),not_provided,Sv,Call,Proj,_Prime,Succ). % TODO: add some ClauseKey?

svterms_call_to_success_builtin('is/2',(X is Y),Sv,Call,Proj,Succ):-
    abssubst(Call,TCall,SVCall),
    abssubst(Proj,TProj,_SVProj),
    eterms_call_to_success_builtin('is/2',(X is Y),Sv,TCall,TProj,TSucc1),
    sv_extend([],SVCall,Sv,TSucc1,TSucc,SVSucc),
    abssubst_b(Succ,TSucc,SVSucc).  

svterms_call_to_success_builtin('functor/3',Sg,Sv,Call,Proj,Succ):-
    abssubst(Call,TCall,SVCall),
    abssubst(Proj,TProj,_SVProj),
    eterms_call_to_success_builtin('functor/3',Sg,Sv,TCall,TProj,TSucc1),
    sv_extend([],SVCall,Sv,TSucc1,TSucc,SVSucc),
    abssubst_b(Succ,TSucc,SVSucc).  

svterms_call_to_success_builtin('arg/3',Sg,Sv,Call,Proj,Succ):-
    abssubst(Call,TCall,SVCall),
    abssubst(Proj,TProj,SVProj),
    sort([X,Y,Z],Hv),
    eterms_arg_call_to_success(Sg,Hv,arg(X,Y,Z),Sv,TCall,TProj,TSucc1,TypeX,TypeY),
    sv_call_to_entry(Sv,Sg,Hv,arg(X,Y,Z),not_provided,[],SVProj,_SVEntry,ExtraInfo), % TODO: add some ClauseKey? (JF)
    (
        concrete(TypeX,ValuesX,[],[]) -> 
        (
            getargtypes(TypeY,ValuesX,_,_,SameValues,[]) ->
            buildargsamevalue(SameValues,Y,Z,SVPrime1)
        ;
            SVPrime1 = []
        )
    ;
        SVPrime1 = []
    ),
    sv_exit_to_prime(Sg,Hv,arg(X,Y,Z),Sv,SVPrime1,ExtraInfo,SVPrime),
    sv_extend(SVPrime,SVCall,Sv,TSucc1,TSucc,SVSucc),
    abssubst_b(Succ,TSucc,SVSucc).  


svterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    member(Key,['>/2','>=/2','=</2','</2']),
    abssubst(Call,TCall,SVCall),
    abssubst(Proj,TProj,_SVProj),
    eterms_call_to_success_builtin(Key,Sg,Sv,TCall,TProj,TSucc1),
    sv_extend([],SVCall,Sv,TSucc1,TSucc,SVSucc),
    abssubst_b(Succ,TSucc,SVSucc).  



buildargsamevalue([],_Y,_Z,[]):-!.
buildargsamevalue([Sel|SameValues],Y,Z,[sv(Y/Sel,Z/[])|SVPrime]):-
            buildargsamevalue(SameValues,Y,Z,SVPrime).


%--------------------------------------------------------------%                
:- dom_impl(svterms, input_user_interface/5).
:- export(svterms_input_user_interface/5).
svterms_input_user_interface(InputUser,Qv,ASub,Sg,MaybeCallASub):-
    eterms_input_user_interface(InputUser,Qv,TASub,Sg,MaybeCallASub),
    abssubst_b(ASub,TASub,[]).              

%--------------------------------------------------------------%        
:- dom_impl(svterms, input_interface/4).
:- export(svterms_input_interface/4).
svterms_input_interface(InputUser,Kind,Struct0,Struct1):-
    eterms_input_interface(InputUser,Kind,Struct0,Struct1).

%--------------------------------------------------------------%        
:- dom_impl(svterms, asub_to_native/5).
:- export(svterms_asub_to_native/5).
svterms_asub_to_native(ASub,Qv,OutFlag,OutputUser,Comps):-
    abssubst(ASub,TASub,_SV1),      
    eterms_asub_to_native(TASub,Qv,OutFlag,OutputUser,Comps).

%--------------------------------------------------------------%        
:- export(svterms_output_interface/2). % TODO: used?
svterms_output_interface(ASub,ASub).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- dom_impl(svterms, collect_auxinfo_asub/3).
:- export(svterms_collect_auxinfo_asub/3).
svterms_collect_auxinfo_asub((T,_),Types0,Types):-
    svterms_collect_abstypes_(T,Types0,Types).

svterms_collect_abstypes_([],Types,Types).
svterms_collect_abstypes_([_:(_,Type)|Abs],Types0,Types):-
    insert(Types0,Type,Types1),
    svterms_collect_abstypes_(Abs,Types1,Types).

%% No renaming applicable.
:- dom_impl(svterms, rename_auxinfo_asub/3).
:- export(svterms_rename_auxinfo_asub/3).
svterms_rename_auxinfo_asub((T0,Rest),Dict,(T,Rest)):-  %% JCF: Y Rest que es?
    svterms_rename_abs_(T0,Dict,T).

svterms_rename_abs_([],_,[]).
svterms_rename_abs_([C|Call],Dict,[RenC|RenCall]):-
    Dict = (Types,_),
    C = Var:(_Name,Type),
    RenC = Var:(RenName,RenType),
    get_value_(Types,Type,RenType),
    new_type_name(RenName),
    insert_type_name(RenName,[],0),
    svterms_rename_abs_(Call,Dict,RenCall).

get_value_(Rens,Type,RenType):-
    assoc:get_assoc(Type,Rens,RenType), !.
get_value_(_Rens,Type,Type).

%------------------------------------------------------------------%
:- dom_impl(svterms, identical_abstract/2).
:- export(svterms_identical_abstract/2).
svterms_identical_abstract(ASub1,ASub2):- 
    abssubst(ASub1,TASub1,SV1),
    abssubst(ASub2,TASub2,SV2),
    eterms_identical_abstract(TASub1,TASub2),
    sval_identical_abstract(SV1,SV2).

sval_identical_abstract('$bottom','$bottom'):- !.
sval_identical_abstract('$bottom',_):- !,fail.
sval_identical_abstract(_,'$bottom'):- !,fail.
sval_identical_abstract(SV1,SV2):-
    sort(SV1,SV1_s),
    sort(SV2,SV2_s),
    SV1_s == SV2_s.
