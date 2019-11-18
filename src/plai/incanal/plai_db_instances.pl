:- module(plai_db_instances, [copy_db/2, plai_db_tuple/8], [assertions, regtypes, datafacts]).

:- doc(title, "plai_db (answer table) instances").
:- doc(author, "Isabel Garcia-Contreras").

:- doc(module, " 
This module stores instances of plai_db, independently of their
representation (@pred{complete/7} and @pred{registry/3}).

And offers a unified representation (see @pred{plai_db_tuple/8}).

@section{Usage}

At any point of the execution of an analysis its state can be copied with
@pred{copy_db/2}

").

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(lists), [append/3]).

:- data plai_db_tuple_/8.
:- data local_id/2.  % Data to assign an id to local database when the
                 % original one lacks.

new_local_id(DBId, Id) :-
    local_id(DBId, LastId), !,
    Id is LastId + 1,
    retractall_fact(local_id(DBId, _)),
    assertz_fact(local_id(DBId, Id)).
new_local_id(DBId, 1) :-
    assertz_fact(local_id(DBId, 1)).

clean_plai_db_tuples :-
    clean_plai_db_tuple(_).

clean_plai_db_tuple(DBId) :-
    retractall_fact(local_id(DBId, _)),
    retractall_fact(plai_db_tuple_(DBId, _, _, _, _, _, _, _)).

:- pred copy_db(FromId, ToId) : atm * atm #"Copies a plai_db a DB that is
    enumerated with @var{Generator} to a local database with id
    @var{DBId}.".
copy_db(_, ToId) :-     
    reserved_db_id(ToId), !,        
    % For safety, copying to datas used in plai in runtime is not allowed.
    throw(copy_error("Not able to copy to ", ToId)).
copy_db(FromId, ToId) :-
    clean_plai_db_tuple(ToId),
    ( % failure-driven loop
      plai_db_tuple(FromId, SgKey, AbsInt, Sg, Call, Succ, Id, Adds),
        ( var(Id) -> new_local_id(ToId, Id) % the tuple did not have an id
        ; true),
          assertz_fact(plai_db_tuple_(ToId, SgKey, AbsInt, Sg, Call, Succ, Id, Adds)),
          fail
    ;   true
    ).

% ------------------------------------------------------------------------
:- doc(section, "Unified interface to plai_db.").

:- use_module(ciaopp(plai/plai_db), [complete/7]).
:- use_module(ciaopp(p_unit/p_abs), [registry/3]).

:- pred plai_db_tuple(DBId, SgKey, AbsInt, Sg, Call, Succ, Id, Add)
    #"Unified interface for plai_db instances. Variables in the tuple are:

Same as @pred{complete/7} for @var{SgKey}, @var{AbsInt}, @var{Sg},
@var{Call} and @var{Succ}.

@begin{itemize}
@item @var{Id}: Is an id of the tuple (it can be a free variable if the
external database has no ids, and an Id will be generated in this
module).  
@item @var{Add}: Additional user information (which will not be used for
comparison), for example, for keeping track of the calls.
@end{itemize}
".
plai_db_tuple(complete, SgKey, AbsInt, Sg, Call, Succ, Id, Parents) :-
    complete(SgKey,AbsInt,Sg, Call,Succ,Id,Parents).
plai_db_tuple(registry, SgKey, AbsInt, Sg, Call, [Succ], _, add([Spec, Imdg,Chdg])) :-
    registry(SgKey, _, Reg),
    Reg = regdata(_,AbsInt,Sg,Call,Succ,Spec, Imdg, Chdg,_Mark).
plai_db_tuple(DBId, SgKey, AbsInt, Sg, Call, Succ, Id, Add) :-
    plai_db_tuple_(DBId, SgKey, AbsInt, Sg, Call, Succ, Id, Add).

:- export(reserved_db_id/1).
:- regtype reserved_db_id/1.
:- doc(reserved_db_id(Id), "@var{Id} is an identifier of a database
    used at runtime in CiaoPP.").
reserved_db_id(complete).
reserved_db_id(registry).
