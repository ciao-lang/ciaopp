/*             Copyright (C)1990-91-92-93-94-95 UPM-CLIP                */
/*                          1994-1995 Katholieke Universiteit Leuven.   */

:- module(aeq_top,
    [ aeq_call_to_entry/9,
      aeq_call_to_success_fact/9,
      aeq_compute_lub/2,  
      aeq_exit_to_prime/7,
      aeq_extend/5,       
      aeq_identical_abstract/2, 
      aeq_input_user_interface/5, 
      aeq_input_interface/4,
      aeq_less_or_equal/2,
      aeq_glb/3,
      aeq_eliminate_equivalent/2,     
      aeq_asub_to_native/5,
      aeq_project/5,
      aeq_abs_sort/2,         
      aeq_special_builtin/5,
      aeq_success_builtin/6,
      aeq_unknown_call/4,
      aeq_unknown_entry/3,
      aeq_empty_entry/3
    ], [datafacts]).

:- use_package(hiord). % TODO: See aeq_success_builtin(aeq_comparison,...)! Do in other way?

:- include(ciaopp(plai/plai_domain)).
:- dom_def(aeq).
:- dom_impl(aeq, call_to_entry/9).
:- dom_impl(aeq, exit_to_prime/7).
:- dom_impl(aeq, project/5).
:- dom_impl(aeq, compute_lub/2).
:- dom_impl(aeq, identical_abstract/2).
:- dom_impl(aeq, abs_sort/2).
:- dom_impl(aeq, extend/5).
:- dom_impl(aeq, less_or_equal/2).
:- dom_impl(aeq, glb/3).
:- dom_impl(aeq, eliminate_equivalent/2).
:- dom_impl(aeq, call_to_success_fact/9).
:- dom_impl(aeq, special_builtin/5).
:- dom_impl(aeq, success_builtin/6).
:- dom_impl(aeq, input_interface/4).
:- dom_impl(aeq, input_user_interface/5).
:- dom_impl(aeq, asub_to_native/5).
:- dom_impl(aeq, unknown_call/4).
:- dom_impl(aeq, unknown_entry/3).
:- dom_impl(aeq, empty_entry/3).
%
% :- dom_impl(aeq, propagate_downwards_closed(ASub1,ASub2,ASub), downwards_closed(ASub1,ASub2,ASub)).
% :- dom_impl(aeq, del_real_conjoin(ASub1,ASub2,ASub), real_conjoin(ASub1,ASub2,ASub)).
% :- dom_impl(aeq, del_hash(ASub,Vars,N), hash(ASub,Vars,N)).
% :- dom_impl(aeq, more_instantiate(ASub1,ASub2), more_instantiate(ASub1,ASub2)).
% :- dom_impl(aeq, convex_hull(Old,New,Hull), convex_hull(Old,New,Hull)).
% :- dom_impl(aeq, compute_lub_el(ASub1,ASub2,ASub), lub(ASub1,ASub2,ASub)).
% :- dom_impl(aeq, extend_free(ASub1,Vars,ASub), extend_free(ASub1,Vars,ASub)).
% :- dom_impl(aeq, del_check_cond(Cond,ASub,Sv,Flag,WConds), check_cond(Cond,ASub,Sv,Flag,WConds)).
% :- dom_impl(aeq, del_impose_cond(LCond,Sv,ASub,LASub), impose_cond(LCond,Sv,ASub,LASub)).
%
%% aeq_check_cond(_,_,_,_,_). 
%% aeq_convex_hull(_,_,_).
%% aeq_downwards_closed(_,_,_).
%% aeq_extend_free(_,_,_).
%% aeq_hash(_,_,_).       
%% aeq_impose_cond(_,_,_,_).
%% aeq_lub(_,_,_).        
%% aeq_more_instantiate(_,_). 
%% aeq_real_conjoin(_,_,_).

:- use_module(engine(io_basic)).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(domain(s_eqs), [apply/1, keys_and_values/3]).
:- use_module(domain(sharing), [
    share_input_interface/4,
    share_input_user_interface/5,
    share_project/5,
    share_abs_sort/2
]).
%
:- use_module(library(idlists), [memberchk/2, union_idlists/3]).
:- use_module(library(lists), [member/2, append/3, list_to_list_of_lists/2, union/3]).
:- use_module(library(llists), [flatten/2]).
:- use_module(library(keys), [key_lookup/4]).
:- use_module(library(messages)).
:- use_module(library(sets), 
    [ insert/3, merge/3, ord_intersect/2, ord_subtract/3 ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2]).

% This file contains the domain dependent abstract functions for the
% abstract equation systems analyser developed at KULeuven,
% auxiliary procedures are defined in aeq_aux.pl

:- include(domain(aeq_aux)).
:- use_module(library(arrays)).
:- use_module(library(bitcodesets)).

:- use_module(ciaopp(pool)).

% The _b.pl versions in 0.8 have been ported here. These are reduced.
% The original versions had possibilities for combining pair-sharing
% and other features...

%------------------------------------------------------------------------%
% This file was initially implemented by KULeuven. It has been modified 
% by Maria Garcia de la Banda in 1996 in order to include comments (so
% that future modifications become easier), to tailor it more closely to
% PLAI, and to add the abstract functions required for dynamic scheduling
%------------------------------------------------------------------------%
% _ec:    suffix indicating "external code" (lists of variables, lists of
%         list of variables, terms, etc).
% _ic:    suffix indicating "internal code" (bit codes, lists of bitcodes,
%          extendable arrays with logarithmic access, etc)
% AVar:   Number which identifies an abstract variable. In _ic, the bitcode
%         is used.
% AnnSet: Annotation set representing the different annotations that can
%         be associated to an abstract variable. There exists 4 different
%         AnnSet for set sharing ({a,l,f,ng},{a,nl,f,ng},{a,l,nf,ng}, and 
%         {a,nl,nf,ng}), and 2 for pair sharing ({a,nl,f,g},{a,nl,nf,g})
% Ann:    list of elements of the form AVar-A, where A is in some AnnSet.
%         In the _ic, a bitvector array is used.
% Shr:    Represents either set sharing (list of lists of variables in _ec,
%         and list of bitcodes in _ic) or pair sharing (in _ec pairs of 
%         variables, in _ic ps(Lin,Sh) where Lin is the bitcode of the set 
%         of nonlinears and Sh is the list of bitcodes of the pairs).
% ATerm:  either and abstract variable (i.e., @(AVar)) or a term formed by
%         abstract variables. 
% Depth:  Positive number representing the depth of the ATerms. The default
%         is 1. The depth can be controled at each unification step (default)
%          or only during call_to_entry.
% Eqs:    Set of elements of the form X = ATerm.
% 
% ASub:   Abstract substitution. The external form is aeqs(Eqs, Ann, Shr),
%         the internal form is aeqs(Eqs,Ann,Shr,ASubVars,PossibleNonGround)
%------------------------------------------------------------------------%


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%% :- mode aeq_call_to_entry(+,+,+,+,+,+,+,-,-) .
aeq_call_to_entry(_Sv,_Sg,_Hv,_Head,_K,_Fv,'$bottom','$bottom',_ExtraInfo) :- !.
aeq_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,Flag) :- 
    variant(Sg,Head),!,
    Flag = yes,
    copy_term((Sg,Proj),(NewTerm,NewProj)),
    Head = NewTerm,
    (aeq_current_sharing(pair) ->
      aeq_init_new_varsPS(Fv,0,NewProj,Entry_u)
    ; aeq_init_new_vars(Fv,0,NewProj,Entry_u)),
    aeq_abs_sort(Entry_u,Entry).
aeq_call_to_entry(_Sv,Sgoal,Hv,Head,_K,Fvars,Proj,Entry,no):-
    union_idlists( Hv, Fvars, Vars ),
    aeq_parameter_passing_proj( Sgoal = Head,Vars,Proj,Init_aeqs),
    aeq_solve( Init_aeqs, Entry ).

%------------------------------------------------------------------------------

%% :- mode aeq_exit_to_prime(+,+,+,+,+,+,-) .
aeq_exit_to_prime(_,_,_,_,'$bottom',_,'$bottom') :- !.
aeq_exit_to_prime(Sg,Hv,Head,_,Exit,yes,Prime) :- !,
    aeq_project(Sg,Hv,not_provided_HvFv_u,Exit,BetaPrime),
    copy_term((Head,BetaPrime),(NewTerm,Prime_u)),
    Sg = NewTerm,
    aeq_abs_sort(Prime_u,Prime).
aeq_exit_to_prime(Sg,_,Head,Sv,Exit,_,Prime) :-
    aeq_parameter_passing_proj(Sg=Head, Sv, Exit, Init_aeqs),
    aeq_solve(Init_aeqs, Prime) .

%------------------------------------------------------------------------------

%% REMARK : %%
%% The first version imposes the depth-bound if the `type' of
%% depth-bound is `project'; it is called by the framework on
%% procedure-entry  (see file fixpoint.pl).
%% This is one way to ensure termination of the analysis and
%% reduce the number of call specifications.

%% :- mode aeq_project(+,+,+,+,-) .
aeq_project(_Sg, _Vars, _HvFv_u, '$bottom', '$bottom') :- !.
aeq_project(_Sg, Vars, _HvFv_u, ASub, ASub_proj) :-
    aeq_project_nb(Vars, ASub, ASub_proj_tmp),
    aeq_impose_depth_bound_proj(ASub_proj_tmp, ASub_proj).

%  (tested alternative but less efficient code)
%       aeq_depth_bound(Depth,Type),
%       aeq_impose_depth_bound_proj( Type, Depth, ASub_proj_tmp, ASub_proj ) .

%% REMARK : %%
%% The second version does not impose the depth-bound and should only be
%% called by some other domain dependent operations.

%% %% :- mode aeq_project2(+,+,-) .
%% aeq_project2('$bottom',_Vars,'$bottom') :- !.
%% aeq_project2(ASub, Vars, ASub_proj ) :-
%%      aeq_project_nb(Vars, ASub, ASub_proj ) .

%------------------------------------------------------------------------------

:- push_prolog_flag(multi_arity_warnings,off).

%% :- mode aeq_compute_lub(+,-) .
aeq_compute_lub([],'$bottom') :- !.
aeq_compute_lub([ASub|ListASub],LubASub) :-
    aeq_compute_lub(ListASub,ASub,LubASub) .

%% :- mode aeq_compute_lub(+,+,-) .
aeq_compute_lub([],LubAccum,LubAccum) .
aeq_compute_lub([ASub|ListASub],LubSoFar,LubASub) :-
    aeq_lub(ASub,LubSoFar,LubAccum),
    aeq_compute_lub(ListASub,LubAccum,LubASub) .

:- pop_prolog_flag(multi_arity_warnings).
    
%------------------------------------------------------------------------------

%% :- mode aeq_identical_abstract(+,+) .
aeq_identical_abstract('$bottom', '$bottom') :- !.
aeq_identical_abstract(ASub1,ASub2) :-
    aeq_identical_nb(ASub1,ASub2) .

%------------------------------------------------------------------------------

%% :- mode aeq_less_or_equal(+,+).
aeq_less_or_equal('$bottom',_ASub) :- !.
aeq_less_or_equal(ASub1,ASub2) :-
    aeq_leq_nb(ASub1,ASub2) .

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

aeq_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

% ---------------------------------------------------------------------------

:- use_module(ciaopp(plai/domains), [absub_eliminate_equivalent/3]).

aeq_eliminate_equivalent(TmpLSucc,LSucc) :- absub_eliminate_equivalent(TmpLSucc,aeq,LSucc).

%------------------------------------------------------------------------------

%% :- mode aeq_abs_sort(+,-) .
aeq_abs_sort('$bottom','$bottom').
aeq_abs_sort(ac(Asub_u,Fg),ac(Asub,Fg)) :-
    aeq_abs_sort(Asub_u,Asub).
aeq_abs_sort(d(aeqs(Eqs,Ann,Shr,AVars,NGrAVars),Del),d(aeqs(Eqs_s,Ann,Shr,AVars,NGrAVars),Del)) :-
    sort(Eqs,Eqs_s) .
aeq_abs_sort(aeqs(Eqs,Ann,Shr,AVars,NGrAVars),aeqs(Eqs_s,Ann,Shr,AVars,NGrAVars)) :-
    sort(Eqs,Eqs_s) .

%------------------------------------------------------------------------------

%% :- mode aeq_extend(+,+,+,+,-) .
aeq_extend(_Sg, '$bottom', _Sv, _Call, '$bottom') :- !.
aeq_extend(_Sg, Prime, _Sv, Call, Succ) :-
    aeq_union(Prime, Call, AEqs_union),
    aeq_solve(AEqs_union, Succ).

%------------------------------------------------------------------------------

%% %% :- mode aeq_real_conjoin(+,+,-) .
%% aeq_real_conjoin(_, '$bottom', '$bottom') :- !.
%% aeq_real_conjoin('$bottom', _Call,'$bottom') :- !.
%% aeq_real_conjoin( Prime, Call, Succ) :-
%%      aeq_union( Prime, Call, AEqs_union),
%%      aeq_solve( AEqs_union, Succ ) .

%------------------------------------------------------------------------------

%%  REMARK %% : never used in local version of the PLAI system !!!

%% :- mode aeq_call_to_success_fact(+,+,+,+,+,+,+,-,-) .
aeq_call_to_success_fact(_Sg,_Hv,_Head,_K,_Sv,_Call,'$bottom','$bottom','$bottom')
    :- !.
aeq_call_to_success_fact(Sgoal,Hv,Head,_K,_Sv,_Call,Proj_aeqs,Prime_aeqs,_Succ) :-
    aeq_parameter_passing_rem( Sgoal = Head, Hv, Proj_aeqs, Init_aeqs),
    aeq_solve( Init_aeqs, Prime_aeqs ) .

%       aeq_parameter_passing_rem( Sgoal = Head, Hv, Call, Init_aeqs),
%       aeq_solve( Init_aeqs, Succ ),
%       aeq_project2( Succ, _Sv, Prime_aeqs ) .

%------------------------------------------------------------------------------

%% :- mode aeq_special_builtin(+,+,+,-,-) .

%%  aeq_special_builtin(Sg_key, Sg, Subgoal, Type, InfoSg)

%%  Determines Type and InfoSg based on Sg_key and Sg
%%  REMARK %% : not all builtins are recognized yet; as a result, precision
%%              may be lost.

aeq_special_builtin( 'fail/0',    _Sg,_Subgoal, aeq_fail, _) .
aeq_special_builtin( 'false/0',   _Sg,_Subgoal, aeq_fail, _) .
   
aeq_special_builtin( '</2',       Sg,_Subgoal, aeq_comparison, Sg ) . 
aeq_special_builtin( '=</2',      Sg,_Subgoal, aeq_comparison, Sg ) . 
aeq_special_builtin( '>/2',       Sg,_Subgoal, aeq_comparison, Sg ) . 
aeq_special_builtin( '>=/2',      Sg,_Subgoal, aeq_comparison, Sg ) .
aeq_special_builtin( '=:=/2',     Sg,_Subgoal, aeq_comparison, Sg ) .
% SICStus3 (ISO)
aeq_special_builtin( '=\\=/2',    Sg,_Subgoal, aeq_comparison, Sg ) .
% SICStus2.x
% aeq_special_builtin( '=\=/2',   Sg,_Subgoal, aeq_comparison, Sg ) .

aeq_special_builtin( '@</2',      _Sg,_Subgoal, aeq_unchanged, _) . 
aeq_special_builtin( '@=</2',     _Sg,_Subgoal, aeq_unchanged, _) . 
aeq_special_builtin( '@>/2',      _Sg,_Subgoal, aeq_unchanged, _) . 
aeq_special_builtin( '@>=/2',     _Sg,_Subgoal, aeq_unchanged, _) .

aeq_special_builtin( '==/2',   L == R,   _, '=/2',  L = R ) :-
    ( atomic(L) ; atomic(R) ), ! .
aeq_special_builtin( '==/2',      _Sg,_Subgoal, aeq_unchanged, _) .
% SICStus3 (ISO)
aeq_special_builtin( '\\==/2',     Sg,_Subgoal, '\\==/2',   Sg  ) .
% SICStus2.x
% aeq_special_builtin( '\==/2',    Sg,_Subgoal, '\==/2',    Sg  ) .
% SICStus3 (ISO)
aeq_special_builtin( 'dif/2',      dif(X,Y), _, '\\==/2',   X \== Y  ) .
% SICStus2.x
% aeq_special_builtin( 'dif/2',    dif(X,Y), _, '\==/2',    X \== Y  ) .

aeq_special_builtin( 'repeat/0',  _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( 'true/0',    _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( '!/0',       _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( 'nl/0',      _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( 'ttynl/0',   _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( 'write/1',   _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( 'ttyput/1',  _Sg,_Subgoal, aeq_unchanged, _) .   
aeq_special_builtin( 'display/1', _Sg,_Subgoal, aeq_unchanged, _) .
aeq_special_builtin( 'print/1',   _Sg,_Subgoal, aeq_unchanged, _) .

aeq_special_builtin( '=/2',           Sg,_Subgoal, '=/2', Sg).

aeq_special_builtin( 'is/2',       Sg,_Subgoal, aeq_is, Sg) .
aeq_special_builtin( 'var/1',      Sg,_Subgoal, aeq_var, Sg) . % needed?
aeq_special_builtin( 'free/1',      Sg,_Subgoal, aeq_var, Sg) .
aeq_special_builtin( 'nonvar/1',   Sg,_Subgoal, aeq_nonvar, Sg) . % needed?
aeq_special_builtin( 'not_free/1',   Sg,_Subgoal, aeq_nonvar, Sg) .

aeq_special_builtin( 'atomic/1',     atomic(X), _, aeq_cond_ground, atomic(X)-Vars ):- % REMARK :
    varset(X,Vars).
aeq_special_builtin( 'atom/1',       atom(X), _, aeq_cond_ground, atom(X)-Vars ) :- % these could be made
    varset(X,Vars).
aeq_special_builtin( 'float/1',      float(X), _, aeq_cond_ground, float(X)-Vars ) :- % more precise, detecting
    varset(X,Vars).
aeq_special_builtin( 'integer/1',    integer(X), _, aeq_cond_ground, integer(X)-Vars ) :- % failure at compile-time
    varset(X,Vars).
aeq_special_builtin( 'ground/1',     ground(X), _, aeq_cond_ground, ground(X)-Vars ) :- % in some cases.
    varset(X,Vars).
aeq_special_builtin( 'number/1',     number(X), _, aeq_cond_ground, number(X)-Vars ):- 
    varset(X,Vars).
aeq_special_builtin( 'nl/1',         nl(X), _, aeq_cond_ground, nl(X)-Vars ):- 
    varset(X,Vars).
aeq_special_builtin( 'write/2',      write(X,_), _, aeq_cond_ground, write(X)-Vars ):- 
    varset(X,Vars).
aeq_special_builtin( '$getch/2',     Sg,_Subgoal, aeq_ground, Sg ) .  
aeq_special_builtin( 'get_code/1',       Sg,_Subgoal, aeq_ground, Sg ) .
aeq_special_builtin( '$getch0/2',    Sg,_Subgoal, aeq_ground, Sg ) .
aeq_special_builtin( 'statistics/2', Sg,_Subgoal, aeq_ground, Sg ) .
aeq_special_builtin( 'current_op/3', Sg,_Subgoal, aeq_ground, Sg ) .
aeq_special_builtin( 'recorda/3',    Sg,_Subgoal, aeq_ground, Arg3 ) :-
    arg( 3, Sg, Arg3 ).

aeq_special_builtin( 'erase/1',        Sg,_Subgoal, aeq_cond_ground, Sg - [Arg1]) :-
    arg( 1, Sg, Arg1 ) .
aeq_special_builtin( 'tab/1',          Sg,_Subgoal, aeq_cond_ground, Sg - [Arg1]) :-
    arg( 1, Sg, Arg1 ) .
aeq_special_builtin( '$skip/1',        Sg,_Subgoal, aeq_cond_ground, Sg - [Arg1]) :-
    arg( 1, Sg, Arg1 ) .
aeq_special_builtin( '$prompt/2',      Sg,_Subgoal, aeq_cond_ground, Sg - [Arg2]) :-
    arg( 2, Sg, Arg2 ) .
aeq_special_builtin( 'numbervars/3',   Sg,_Subgoal, aeq_cond_ground, Sg - [Arg2]) :-
    arg( 2, Sg, Arg2 ) .
aeq_special_builtin( '$number_chars/2',Sg,_Subgoal, aeq_cond_ground, Sg - Args) :-
    Sg =.. [_F|Args] .
aeq_special_builtin( '$atom_chars/2',  Sg,_Subgoal, aeq_cond_ground, Sg - Args) :-
    Sg =.. [_F|Args] .
aeq_special_builtin( '$prolog_radix/2',Sg,_Subgoal, aeq_cond_ground, Sg - Args) :-
    Sg =.. [_F|Args] .
aeq_special_builtin( 'name/2',         Sg,_Subgoal, aeq_cond_ground, Sg - Args) :-
    Sg =.. [_F|Args] .
aeq_special_builtin( 'compare/3',         Sg,_Subgoal, aeq_compare, Sg ) .

aeq_special_builtin( 'read/1',     Sg,_Subgoal, aeq_top, Sg ) .
aeq_special_builtin( 'arg/3',      Sg,_Subgoal, aeq_arg, Sg ) .
aeq_special_builtin( 'functor/3', functor(T,F,A), _, Type, Eq ) :-
    ( var( T ), !, 
      ( nonvar(F), nonvar(A), !,
        ( atom(F), integer(A), functor(NV_T,F,A), !, NV_T =.. [F|Args],
          Type = 'aeq_functor_=/2', Eq = ( T=NV_T, Args )
        ; Type = aeq_fail )
      ; Type = aeq_functor, Eq = functor(T,F,A) )
                            % T is var, F or A are unsufficiently instantiated
                            % at analysis time 
    ; functor(T,NV_F,NV_A),
      Type = '=/2', Eq = ( (NV_F,NV_A)=(F,A) ) ) .
aeq_special_builtin( '=../2', L =.. R, _, Type, Eq ) :-
    ( var( L ), !,
      ( nonvar(R), !, 
        ( R = [F|Args], !,
            ( atom( F), finiteclosedlist( Args ), !, NV_L =.. R, 
              Type = '=/2', Eq = ( L=NV_L )
            ; number(F), Args==[], !, NV_L =.. R, 
              Type = '=/2', Eq = ( L=NV_L )                  
            ; var(F), anylist( Args ), !,
              Type = 'aeq_=..', Eq = (L =.. R)
                            % L is var, R unsufficiently instantiated
                            % list of at least one element at analysis time
            ; Type = aeq_fail )
        ; Type = aeq_fail )
      ; Type = 'aeq_=..', Eq = (L =.. R) )
                            % L, R vars at analysis time
    ; L =.. NV_R ,
      Type = '=/2', Eq = ( NV_R=R )) .
aeq_special_builtin( 'sort/2', Sg,_Subgoal, aeq_sort, Sg ) .
aeq_special_builtin( Key,   _Sg,_Subgoal, _, _) :-
    aeq_warning( builtin_undef, Key ), fail .

%------------------------------------------------------------------------------

%% :- mode aeq_success_builtin(+,+,+,+,+,-) .

%%  aeq_success_builtin(Type,Sv_uns,Info_sg,HvFv_u,Call,Succ).

%%  Abstract interpretation of builtins
%%  (note: direct computation, not via projection and extension)
%%  REMARK %% : not all builtins are recognized yet; as a result, precision
%%              may be lost.
%%  REMARK %% : the Succ should be bounded; if necessary, use a call to
%%              aeq_impose_depth_bound/2

aeq_success_builtin( _Type,             _Sv_uns, _Info,_,'$bottom','$bottom'):- !.
aeq_success_builtin( aeq_fail,          _Sv_uns, _Info,_,_Call,'$bottom') .
aeq_success_builtin( aeq_unchanged,     _Sv_uns, _Info,_, Call, Call) .
aeq_success_builtin( '=/2',             _Sv_uns,    Sg,_, Call, Succ):-
    aeq_add_equation( Sg, Call, Init_aeqs),
    aeq_solve( Init_aeqs, Succ ) .
% SICStus3 (ISO)
aeq_success_builtin( '\\==/2',          _Sv_uns, Left \== Right, _, Call, Succ):-
% SICStus2.x
% aeq_success_builtin( '\==/2',         _Sv_uns, Left \== Right, _, Call, Succ):-
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( Left, Eqs_sf, ALeft ),
    aeq_substitute( Right, Eqs_sf, ARight ),
    ( ALeft == ARight, !, Succ = '$bottom'
    ; Call = Succ
    ) .
aeq_success_builtin( aeq_is,            _Sv_uns, Left is Expr, _, Call, Succ):-
    ( aeq_instantiated_Expr( Expr, Call, AVarExpr_ic, A_Expr ),
      aeq_var_or_number( Left, Call, AVarleft_ic ), !,
      ( % REMARK :
        % AVarExpr_ic == 0, !, numeric expression that can be evaluated ;
        % Value is A_Expr,     but this may lead to an infinite loop
        %                      because the domain becomes infinite
        number(A_Expr), !,
        aeq_add_equation( Left = A_Expr, Call, Init_aeqs),
        aeq_solve( Init_aeqs, Succ )
      ; bitset_union( AVarExpr_ic, AVarleft_ic, AVars_ic ),
        aeq_make_ground( AVars_ic, Call, Succ)
      )
    ; Succ = '$bottom'
    ) .
aeq_success_builtin( aeq_var,           _Sv_uns, var(Term), _, Call, Succ):-
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( Term, Eqs_sf, ATerm ),
    ( compound_aeqs( Call, ATerm ), !, Succ = '$bottom'
    ; aeq_make_free( ATerm, Call, Succ)
    ) .
aeq_success_builtin( aeq_nonvar,        _Sv_uns, nonvar(Term), _, Call, Succ):-
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( Term, Eqs_sf, ATerm ),
    ( free_aeqs( Call, ATerm ), !, Succ = '$bottom'
    ; Call = Succ   % REMARK : if the annotation mapping included 'c' (compound-
                    % ness information), we could do something more here.
    ) .
aeq_success_builtin( aeq_ground,        _Sv_uns,        Sg, _, Call, Succ):-
    get_Eqs_aeqs( Call, Eqs_sf),
    avariables_ic_subst( Sg, Eqs_sf, AVars_ic ),
    aeq_make_ground( AVars_ic, Call, Succ) .
aeq_success_builtin( aeq_compare,       _Sv_uns, compare(X,_Y,_Z), _, Call, Succ):-
    get_Eqs_aeqs( Call, Eqs_sf),
    avariables_ic_subst( X, Eqs_sf, AVars_ic ),
    aeq_make_ground( AVars_ic, Call, Succ) .
aeq_success_builtin( aeq_comparison,    _Sv_uns, Sg, _, Call, Succ):-
    Sg =.. [Op,Arg1,Arg2],
    ( aeq_instantiated_Expr( Arg1, Call, AVars1_ic, A_Arg1 ),
      aeq_instantiated_Expr( Arg2, Call, AVars2_ic, A_Arg2 ), !,
      ( number(A_Arg1), number(A_Arg2), !,
        ( A_Sg =.. [Op,A_Arg1,A_Arg2], call(A_Sg), !,
          Call = Succ
        ; Succ = '$bottom'
        )
      ; bitset_union( AVars1_ic, AVars2_ic, AVars_ic ),
        aeq_make_ground( AVars_ic, Call, Succ)
      )
    ; Succ = '$bottom'
    ) .
%% % OLD
%%      get_Eqs_aeqs( Call, Eqs_sf),
%%      aeq_substitute( (Arg1,Arg2), Eqs_sf, (A_Arg1,A_Arg2) ),
%%      ( free_aeqs( Call, A_Arg1 ), !, Succ = '$bottom'
%%      ; free_aeqs( Call, A_Arg2 ), !, Succ = '$bottom'
%%      ; number(A_Arg1), number(A_Arg2), !,
%%        ( A_Sg =.. [Op,A_Arg1,A_Arg2], call(A_Sg), !,
%%          Call = Succ
%%        ; Succ = '$bottom'
%%        )
%%      ; avarORnumber_aeqs( A_Arg1, AVars1_ic ),
%%        avarORnumber_aeqs( A_Arg2, AVars2_ic ), !,
%%        bitset_union( AVars1_ic, AVars2_ic, AVars_ic ),
%%        aeq_make_ground( AVars_ic, Call, Succ)
%%      ; Succ = '$bottom'
%%      ) .
aeq_success_builtin( aeq_cond_ground,   _Sv_uns, Sg - Varlist, _, Call, Succ):-
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( Varlist, Eqs_sf, A_Varlist ),
    ( free_aeqs_list( A_Varlist, Call ), !, Succ = '$bottom'
    ;
      avariables_ic_subst( Sg, Eqs_sf, AVars_ic ),
      aeq_make_ground( AVars_ic, Call, Succ)
    ) .
aeq_success_builtin( aeq_arg,   Sv_uns, Sg, _, Call, Succ):- Sg = arg(Nb,Term,Arg),
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( arg(Nb,Term,Arg), Eqs_sf, arg(A_Nb,A_Term,A_Arg) ),
    ( free_aeqs( Call, A_Term ), !, Succ = '$bottom'
    ; free_aeqs( Call, A_Nb ), !, Succ = '$bottom'
    ; integer(A_Nb), \+(A_Term = '@'(_)), !,
      ( arg(A_Nb,A_Term,A_Term_Arg), !,
        aeq_add_equation( A_Term_Arg = A_Arg, Call, Init_aeqs),
        aeq_solve( Init_aeqs, Succ )
      ; Succ = '$bottom'
      )
    ; avarORnumber_aeqs(A_Nb, A_Nb_ic), !,
      aeq_make_ground( A_Nb_ic, Call, Succ_Sofar),
      ( A_Term == A_Arg, !, Succ = '$bottom'
      ; ( A_Term='@'(_) ; \+ aeq_pair_sharing ), !,
        aeq_jacobs_langen_variant( A_Term, A_Arg, 'arg', Succ_Sofar, Succ)
      ; A_Arg = '@'(_), aeq_pair_sharing, !,
        aeq_jacobs_langen_variant( A_Arg, A_Term, 'arg', Succ_Sofar, Succ)
      ; aeq_warning( builtin_undef, aeq_arg ),
        aeq_unknown_call(Sg,Sv_uns,Succ_Sofar,Succ)
      )
    ; Succ = '$bottom'
    ) .
aeq_success_builtin( 'aeq_=..', _Sv_uns,    Sg, _, Call, Succ):- 
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( Sg, Eqs_sf, A_L =.. A_R ),
    ( free_aeqs( Call, A_L ), free_aeqs( Call, A_R ), !,
      Succ = '$bottom'
    ; A_L='@'(_), !,
      aeq_jacobs_langen_variant( A_L, A_R, '=..', Call, Succ)
    ; A_L =.. L_A_L,
      aeq_add_equation( L_A_L = A_R, Call, Init_aeqs),
      aeq_solve( Init_aeqs, Succ)
    ) .
aeq_success_builtin( aeq_sort,  Sv_uns,    Sg, _, Call, Succ):- 
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( Sg, Eqs_sf, sort(A_L,A_R) ),
    ( free_aeqs( Call, A_L ), !,
      Succ = '$bottom'
    ; A_R = '@'(_), !,
      aeq_jacobs_langen_variant( A_R, A_L, '=..', Call, Succ)
      %% REMARK : switched arguments because A_R will often be free
    ; aeq_warning( builtin_undef, aeq_sort ),
      aeq_unknown_call(Sg,Sv_uns,Call,Succ)
    ) .
aeq_success_builtin( 'aeq_functor_=/2', _Sv_uns, ( Eq, Vars ), _, Call, Succ):- 
    aeq_parameter_passing_rem( Eq, Vars, Call, Init_aeqs),
    aeq_solve( Init_aeqs, Succ ) .
aeq_success_builtin( aeq_functor,       _Sv_uns, functor(T,F,A), _, Call, Succ):- 
    get_Eqs_aeqs( Call, Eqs_sf),
    aeq_substitute( functor(T,F,A), Eqs_sf, functor(A_T,A_F,A_A) ),
    ( aeq_functor_succ(A_T, A_F, A_A, Call, Succ), !
    ; Succ = '$bottom'
    ) .
aeq_success_builtin( aeq_top,           Sv_uns,         Sg, _, Call, Succ):-
    aeq_unknown_call(Sg,Sv_uns,Call,Succ) .

%------------------------------------------------------------------------------

%% :- mode aeq_input_user_interface(+,+,-,+,+).
aeq_input_user_interface(InputUser,Qv,ASub,_Sg,_MaybeCallASub):-
    aeq_input_user_interface_(InputUser,Qv,ASub).

aeq_input_user_interface_(InputUser,_Qv,ASub):-
    member(aeqs(X,Y,Z),InputUser), !,
    aeq_extern_to_intern(X,Y,Z,ASub).
aeq_input_user_interface_(InputUser,Qv,ASub):-
    aeq_input_to_extern(InputUser,Qv,X,Y,Z),
    aeq_extern_to_intern(X,Y,Z,ASub).

aeq_input_interface(Info,Kind,(Sh0,Eqs,Lv,Fv),(Sh,Eqs,Lv,Fv)):-
    share_input_interface(Info,Kind,Sh0,Sh), !.
aeq_input_interface(instance(X,T),perfect,(Sh,Eqs0,Lv,Fv),(Sh,Eqs,Lv,Fv)):-
    var(X),
    myappend(Eqs0,X=T,Eqs).
aeq_input_interface(free(X),perfect,(Sh,Eqs,Lv,Fv0),(Sh,Eqs,Lv,Fv)):-
    var(X),
    myappend(Fv0,X,Fv).

%% son_input_interface(linear(X),perfect,(Sh,Eqs,Lv0,Fv),(Sh,Eqs,Lv,Fv)):-
%%      varset(X,Xs),
%%      may_be_var(Lv0),
%%      append(Lv0,Xs,Lv).

myappend(Vs0,V,Vs):-
    var(Vs0), !,
    Vs=[V].
myappend(Vs,V,[V|Vs]).

% may_be_var(X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------------

%% :- mode aeq_asub_to_native(+,+,+,-,-).
aeq_asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :-
    aeq_asub_to_native_(ASub,OutputUser).

aeq_asub_to_native_(ASub,OutputUser):-
    aeq_intern_to_extern(ASub,Extern),
    aeq_extern_to_output(Extern,OutputUser).

%------------------------------------------------------------------------------

%% :- mode aeq_unknown_call(+,+,+,-).
aeq_unknown_call(_Sg,_Vars_uns,'$bottom','$bottom') :- ! .
aeq_unknown_call(Sg,Vars_uns,Call,Succ) :-
    sort(Vars_uns, Vars),
    aeq_top(Vars, Top_aeqs),
    aeq_extend(Sg, Top_aeqs, not_provided_Sv, Call, Succ).

%------------------------------------------------------------------------------

%% :- mode aeq_unknown_entry(+,+,-).
aeq_unknown_entry(_Sg, QVars, Top_aeqs) :-
    aeq_top(QVars, Top_aeqs).

%% :- mode aeq_empty_entry(+,+,-).
aeq_empty_entry(_Sg, QVars, ASub) :-
    list_to_list_of_lists(QVars,Sh),
    share_input_interface(sharing(Sh),_Kind,_Sh0,ShInfo),
    aeq_input_user_interface_((ShInfo,[],[],QVars),QVars,ASub).

%------------------------------------------------------------------------------
%   NOT NEEDED ?!
% :- mode open_output(+,+,-).
% open_output(aeq,_Vers,_InStream,OutStream) :-
%       open( aeq_output, write, OutStream ) .
%
