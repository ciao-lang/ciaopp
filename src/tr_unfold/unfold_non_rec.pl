:- module(unfold_non_rec,[unfold/5,entryPred/1],[assertions]).

:- doc(title, "Interface to Unfold Transformation of John Gallaghar").
:- doc(author, "Alejandro Serrano").
:- doc(author, "Jose F. Morales (simplified version)"). % TODO: this module requires more changes

:- doc(module, "This module provides an interface to unfold
       transformation implemented in @file{unfold_core.pl}. It transforms
       CiaoPP internal representation of code into the representation
       used in the unfold step and performs such unfolding.").

:- use_module(engine(runtime_control), [module_split/3]).
:- use_module(library(vndict)).
:- use_module(library(lists)).
:- use_module(library(aggregates)).

:- use_module(ciaopp(frontend_driver), [entry_assertion/3]).
:- use_module(library(compiler/p_unit/program_keys)).
:- use_module(library(compiler/p_unit/clause_db)).
:- use_module(ciaopp(preprocess_flags)).
:- use_module(unfold_core).
:- use_module(chclibs_readprog).

% (archived)
% :- if(defined(has_ciaopp_llvm)).
% :- use_module(ciaopp_llvm(xs1/xs1_transformation), [preds2unfold/2]). % TODO: this should not be here
% :- endif.

:- op(1150, fx, entry).

% TODO: document
unfold(Cs,Ds,RemoveUnsat,FinalCls,FinalDs) :-
    jpg_program_format(Cs,Ds,Cls),
    setof(E,entryPred(E),Entries1),
    %
    get_unfold_entries(Entries1, Entries),
    %
    unfold_core:unfold(Cls,Entries,UCls),
    jpg_program_format_inverse(UCls,UCls2,UDs2),
    ( RemoveUnsat = yes ->
        remove_unsat(UCls2,UDs2,UCls3,FinalDs)
    ; UCls2 = UCls3, UDs2 = FinalDs
    ),
    rewrite_source_all_clauses(UCls3,FinalCls),
    !. % TODO: why cut?

% (archived)
% :- if(defined(has_ciaopp_llvm)).
% get_unfold_entries(Entries1, Entries) :- current_pp_flag(xc_layer, isa), !,
%     % TODO: fixme (e.g., add entries from xs1_transformation?)
%     Entries1=[ModuleName_|_Rs],
%     ModuleName_=_F/__A,
%     module_split(_F, ModuleName, _),
%     xs1_transformation:preds2unfold(ModuleName, PredsNotToUnfold),
%     append(PredsNotToUnfold, Entries1, Entries).
% :- endif.
get_unfold_entries(Entries, Entries).

% TODO: document
entryPred(P/N) :-
    entry_assertion(G,_,_),
    functor(G,P,N).
 
% flatten jpg representation, switch to clause/2 and create dictionaries
jpg_program_format_inverse([],[],[]).
jpg_program_format_inverse([Es|Rs],Cs,Ds) :-
    jpg_program_format_inverse_(Es,Cs,Cs1,Ds,Ds1),
    jpg_program_format_inverse(Rs,Cs1,Ds1).

jpg_program_format_inverse_([],Cs,Cs,Ds,Ds).
jpg_program_format_inverse_([(A :- B)|Cls],[clause(A,B)|Cs],Cs0,[D|Ds],Ds0) :-
    create_dict(A,D),
    jpg_program_format_inverse_(Cls,Cs,Cs0,Ds,Ds0).

% ---------------------------------------------------------------------------
% (Umer Liqat, Nov 2014)

% TODO: (JF) this is a quick implementation for a particular use (see
%   'unfold_entry' transformation) that IS NOT correct in general.
%   See (abstract) partial evaluation for a better approach.

remove_unsat([],[],[],[]).
remove_unsat([clause(H,Body)|Cls0], [_D|Ds0], Cls, Ds) :-
    is_unsat_clause(clause(H,Body)),
    !,
    remove_unsat(Cls0, Ds0, Cls, Ds).
remove_unsat([Cl|Cls0], [D|Ds0], [Cl|Cls], [D|Ds]) :- !,
    remove_unsat(Cls0, Ds0, Cls, Ds).

% TODO: ugly! why twice?
is_unsat_clause(clause(H,Body)) :-
    \+ (is_sat(clause(H,Body)),
        is_sat(clause(H,Body))).

is_sat(clause(_H,Body)) :- !,
    is_sat_aux(Body).
is_sat(_H).

is_sat_aux('$VAR'(_)) :- !.
is_sat_aux(true) :- !.
is_sat_aux((B,Bs)) :- !,
    is_sat_aux(B),
    is_sat_aux(Bs).

is_sat_aux('arithmetic:=<'(X, E)) :- !,
    _B = 'arithmetic:=<'(X, E).
is_sat_aux('term_basic:\\='(X,Y)) :- 
    \+var(X), \+var(Y),!,
    _B = 'term_basic:\\='(X,Y),
    term_basic:(X\=Y).
is_sat_aux('arithmetic:is'(X,Y)) :- 
    \+var(Y), num(Y),!,
    _B = 'arithmetic:is'(X,Y),
    arithmetic:(X is Y).
is_sat_aux('term_basic:='(X,Y)) :- !,
    _B = 'term_basic:='(X,Y),
    term_basic:(X=Y).
is_sat_aux(_B).
