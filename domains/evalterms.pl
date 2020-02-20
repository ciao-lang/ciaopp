:- module(evalterms,[                             
    evalterms_call_to_success_builtin/6,
    evalterms_widen/3,
    evalterms_widencall/3,
    evalterms_special_builtin/5
   ], [assertions,regtypes,basicmodes,datafacts]).

% NOTE: This domain is disconnected! its functionality is subsumed by
%   eterms+type_eval, however it may be worth trying its widening
%   operator (ewiden_el/5).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- use_module(spec(unfold_builtins), [can_be_evaluated/1]).

:- use_module(domain(eterms), [
    eterms_less_or_equal/2,
    eterms_compute_lub_el/3,
    eterms_identical_abstract/2,
    eterms_call_to_success_fact/9,
    eterms_project/5,
    eterms_exit_to_prime/7,
    eterms_call_to_entry/9,
    eterms_glb/3,
    eterms_extend/5,
    eterms_call_to_success_builtin/6,
    eterms_arg_call_to_success/9
]).

:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(sets), [merge/3]).
:- use_module(library(sort), [sort/2]).

:- use_module(typeslib(typeslib), [
    get_type_name/2,
    insert_type_name/3,
    retract_type_name/3,
    pure_type_term/1,
    set_atom_type/1,
    set_int_type/1,
    set_float_type/1,
    set_numeric_type/1,
    set_numexp_type/1,
    set_top_type/1,
    new_type_name/1,
    top_type/1,
    ewiden_el/5
]).

% ---------------------------------------------------------------------------

:- regtype absu(A) # "@var{A} is an abstract substitution".

absu('$bottom').
absu([]).
absu([Elem|Absu]):- 
    absu_elem(Elem),
    absu(Absu).

:- regtype absu_elem(E) # "@var{E} is a single substitution".

absu_elem(Var:Type):-
    var(Var),
    pure_type_term(Type).

% ---------------------------------------------------------------------------

evalterms_special_builtin('!/0',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@=</2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@>/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@>=/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('@</2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('\\==/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('==/2',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('display/1',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('get_code/1',Sg,_Subgoal,type(T),Condvars):-
    set_int_type(T),
    varset(Sg,Condvars).
% eterms_special_builtin('integer/1',Sg,_Subgoal,type(T),Condvars):-
%         set_int_type(T),
%       varset(Sg,Condvars).
evalterms_special_builtin('atom/1',Sg,_Subgoal,type(T),Condvars):-
    set_atom_type(T), % no, it is atom or num type
    varset(Sg,Condvars).
evalterms_special_builtin('atomic/1',Sg,_Subgoal,type(T),Condvars):-
    set_atom_type(T), % no, it is atom or num type
    varset(Sg,Condvars).
evalterms_special_builtin('var/1',_Sg,_Subgoal,id,[]). % needed?
evalterms_special_builtin('free/1',_Sg,_Subgoal,id,[]).
    % set_top_type(T),
    % varset(Sg,Condvars).
evalterms_special_builtin('nonvar/1',_Sg,_Subgoal,id,[]). % needed?
evalterms_special_builtin('not_free/1',_Sg,_Subgoal,id,[]).
    % set_top_type(T),
    % varset(Sg,Condvars).
evalterms_special_builtin('ground/1',_Sg,_Subgoal,id,[]).
    % set_top_type(T),
    % varset(Sg,Condvars).
% eterms_special_builtin('float/1',Sg,_Subgoal,type(T),Condvars):-
%       set_float_type(T),
%       varset(Sg,Condvars).
% eterms_special_builtin('number/1',Sg,_Subgoal,type(T),Condvars):-
%       set_numeric_type(T),
%       varset(Sg,Condvars).
evalterms_special_builtin('fail/0',_Sg,_Subgoal,bot,[]).
evalterms_special_builtin('true/0',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('nl/0',_Sg,_Subgoal,id,[]).
evalterms_special_builtin('repeat/0',_Sg,_Subgoal,id,[]).
%
evalterms_special_builtin('erase/1',Sg,_Subgoal,type(T),Condvars):-
    set_top_type(T),
    varset(Sg,Condvars).
%
evalterms_special_builtin(Key,_Sg,_Subgoal,special(Key),[]):-
    evalterms_very_special_builtin(Key).

evalterms_very_special_builtin('=/2').
evalterms_very_special_builtin('is/2').
evalterms_very_special_builtin('functor/3').
evalterms_very_special_builtin('arg/3').
evalterms_very_special_builtin(Key):-
    can_be_evaluated(Key).

% ---------------------------------------------------------------------------

% TODO: more complex definition (see eterms), why?
evalterms_widencall(Prime0,Prime1,Result):-
    ( eterms_less_or_equal(Prime1,Prime0) ->
        Result = Prime0
    ; do_not_lub(Prime0,Prime1,PrimePrime), % TODO: may fail!!
      eterms_compute_lub_el(Prime0,Prime1,Prime),
      ewiden(Prime0,Prime,Prime2),
      ( eterms_identical_abstract(Prime2,Prime) ->
          Result = PrimePrime
      ; Result = Prime2
      )
    ).

% TODO: why?
do_not_lub([X:(N1,_T1)|ASub1],[Y:(N2,T2)|ASub2],[X:(N1,T2)|ASub3]):-
    X==Y,
    ( top_type(T2) ->
        true 
    ; get_type_name(N2,L2),
      retract_type_name(N1,L1,C1),
      merge(L1,L2,L3),
      insert_type_name(N1,L3,C1)
    ),
    do_not_lub(ASub1,ASub2,ASub3).
do_not_lub([],[],[]).

:- pred evalterms_widen(+Prime0,+Prime1,-NewPrime):
absu * absu * absu #
" 
Induction step on the abstract substitution of a fixpoint.
@var{Prime0} corresponds to non-recursive and @var{Prime1} to
recursive clauses.  @var{NewPrime} is the result of apply one widening
operation to the least upper bound of the formers.  At the moment the
widening operation implemented is ``Type Graph Jungle Widening''.  ".

evalterms_widen(Prime0,Prime1,NewPrime):-
    eterms_compute_lub_el(Prime0,Prime1,Prime),
    ewiden(Prime0,Prime,NewPrime).

ewiden('$bottom','$bottom','$bottom').
ewiden('$bottom',Prime,Prime).
ewiden([],[],[]).
ewiden([X:T1|Prime0],[X:T2|Prime],[X:T|NewPrime]):-
    current_pp_flag(depth,Depthk),
    ewiden_el(T1,T2,T,yes,Depthk),
    ewiden(Prime0,Prime,NewPrime).

%---------------------------------------------------------------------%  

evalterms_call_to_success_builtin('arg/3',Sg,Sv,Call,Proj,Succ):-
    sort([X,Y,Z],Hv),
    eterms_arg_call_to_success(Sg,Hv,arg(X,Y,Z),Sv,Call,Proj,Succ,_,_).
%
evalterms_call_to_success_builtin('functor/3',Sg,Sv,Call,Proj,Succ):- !,
    eterms_call_to_success_builtin('functor/3',Sg,Sv,Call,Proj,Succ).
%        
evalterms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ):- !,
    eterms_call_to_success_builtin('=/2',X=Y,Sv,Call,Proj,Succ).
%
evalterms_call_to_success_builtin('is/2',(X is Y),Sv,Call,Proj,Succ):- !,
    eterms_call_to_success_builtin('is/2',(X is Y),Sv,Call,Proj,Succ).
%
evalterms_call_to_success_builtin(Key,Sg,Sv,Call,Proj,Succ):-
    ( precondition_builtin(Key,Sg) ->
        postcondition_builtin(Key,Bg,Bv,Exit),
        eterms_exit_to_prime(Sg,Bv,Bg,Sv,Exit,(no,Proj),Prime1),
        eterms_glb(Proj,Prime1,Prime),
        eterms_extend(Sg,Prime,Sv,Call,Succ)
    ; Succ = '$bottom'
    ).

precondition_builtin('is/2',(X is _Y)) :- !,
    (var(X);number(X)).
precondition_builtin(_Key,_).

postcondition_builtin('list/1',list(X1),Bv,Exit):-
    TX = list,
    new_type_name(NX),
    insert_type_name(NX,[],0),
    Exit_u = [X1:(NX,TX)],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('number/1',number(X1),Bv,Exit):-
    set_numeric_type(TX),
    new_type_name(NX),
    insert_type_name(NX,[],0),
    Exit_u = [X1:(NX,TX)],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('num/1',num(X1),Bv,Exit):-
    set_numeric_type(TX),
    new_type_name(NX),
    insert_type_name(NX,[],0),
    Exit_u = [X1:(NX,TX)],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('float/1',float(X1),Bv,Exit):-
    set_float_type(TX),
    new_type_name(NX),
    insert_type_name(NX,[],0),
    Exit_u = [X1:(NX,TX)],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('integer/1',integer(X1),Bv,Exit):-
    set_int_type(TX),
    new_type_name(NX),
    insert_type_name(NX,[],0),
    Exit_u = [X1:(NX,TX)],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('int/1',int(X1),Bv,Exit):-
    set_int_type(TX),
    new_type_name(NX),
    insert_type_name(NX,[],0),
    Exit_u = [X1:(NX,TX)],
    Bv_u = [X1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('is/2',(X1 is Y1),Bv,Exit):-
    set_numexp_type(TY),
    set_numeric_type(TX),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
    Bv_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('>/2',(X > Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('>=/2',(X >= Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('</2',(X < Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('=</2',(X =< Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('=\\=/2',(X =\= Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('=:=/2',(X =:= Y),Bv,Exit):-
    set_numexp_type(TX),
    set_numexp_type(TY),
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X:(NX,TX),Y:(NY,TY)],
    Bv_u = [X,Y],
    sort(Exit_u,Exit),
    sort(Bv_u,Bv).
%
postcondition_builtin('functor/3',functor(X1,Y1,Z1),Vars,Exit):-
    set_int_type(TZ),
    set_atom_type(TY),
    set_top_type(TX),
    new_type_name(NX),
    new_type_name(NY),
    new_type_name(NZ),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    insert_type_name(NZ,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('arg/3',arg(X1,Y1,Z1),Vars,Exit):-
    set_int_type(TX),
    set_top_type(TY),
    set_top_type(TZ),
    new_type_name(NX),
    new_type_name(NY),
    new_type_name(NZ),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    insert_type_name(NZ,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('current_op/3',current_op(X1,Y1,Z1),Vars,Exit):-
    set_top_type(TX),
    set_atom_type(TY),
    set_atom_type(TZ),
    new_type_name(NX),
    new_type_name(NY),
    new_type_name(NZ),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    insert_type_name(NZ,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('member/2',member(X1,Y1),Vars,Exit):-
    set_top_type(TX),
    set_top_type(TY), % TY = pt1,
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
    Vars_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('=../2',X1=..Y1,Vars,Exit):-
    set_top_type(TX),
    set_top_type(TY), %TY = pt1,
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
    Vars_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('numbervars/3',numbervars(X1,Y1,Z1),Vars,Exit):-
    set_int_type(TZ),
    set_int_type(TY),
    set_top_type(TX),
    new_type_name(NX),
    new_type_name(NY),
    new_type_name(NZ),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    insert_type_name(NZ,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY),Z1:(NZ,TZ)],
    Vars_u = [X1,Y1,Z1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).
%
postcondition_builtin('name/2',name(X1,Y1),Vars,Exit):-
    set_atom_type(TX),
    set_top_type(TY), % TY = pt1,
    new_type_name(NX),
    new_type_name(NY),
    insert_type_name(NX,[],0),
    insert_type_name(NY,[],0),
    Exit_u = [X1:(NX,TX),Y1:(NY,TY)],
    Vars_u = [X1,Y1],
    sort(Exit_u,Exit),
    sort(Vars_u,Vars).

%--------------------------------------------

% myfunctor(X,Z,Y):- functor(X,Y,Z).

% abs_eval_functor(X,Y,Z,Proj,NProj):-  
%       get_type(X,Proj,TypeX),
%       maybe_get_type_definition(TypeX,DefX),
%       maplist(functor(_Y),DefX,DefZ),
%       maplist(myfunctor(_Z),DefX,DefY),
%       new_type_symbol(TY),
%       new_type_symbol(TZ),
%       sort(DefZ,DefZ_s),
%       sort(DefY,DefY_s),
%       insert_rule(TY,DefY_s),
%       insert_rule(TZ,DefZ_s).
    
