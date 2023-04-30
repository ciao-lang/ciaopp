:- module(static_abs_exec_table, [abs_ex/4], [assertions, datafacts]).

:- doc(title,"Static Abstract Executability Table").
:- doc(author, "Germ@'{a}n Puebla").
:- doc(module," This module contains the static abstract
      executability table for predicates which are supposed to be
      predefined in the system, such as builtins and in standard
      libraries. This table now coexists with a dynamic table and may
      be replaced by it in the future.").

:- use_module(ciaopp(p_unit), [language/1]).

:- doc(bug,"1. Handling of ground should be improved so that it is
   done by assertions and also calls to ground with lists of variables is
   handled accurately").

%-------------------------------------------------------------------%
% abs_ex(+,+,+,-)                                                   %
% abs_ex(Pred,Abs,Sense,Cond)                                       %
%  Pred is abstractly executable to Sense with abstract domain Abs  %
%  if Cond holds                                                    %
%-------------------------------------------------------------------%

% obtain_pred(Key,Name,Arity):-
%       atom_codes(Key,B),
%       append(Name1,[47],C),
%       append(C,Arity1,B),
%       atom_codes(Name,Name1),
%       atom_codes(Arity2,Arity1),
%       atom_number(Arity2,Arity).

%-------------------------------------------------------------------%
% Predicates abstractly executable to true with type   info         %
%-------------------------------------------------------------------%

%abs_ex( integer/1     , types , true , type_incl(1,int) ).
abs_ex( atom/1        , types , true , type_incl(1,atm) ).
abs_ex( float/1       , types , true , type_incl(1,flt) ).
abs_ex( number/1      , types , true , type_incl(1,num) ).
abs_ex( list/1        , types , true , type_incl(1,'basic_props:list')).
abs_ex( '='/2         , types , true , one_concr_equal  ).
abs_ex( ground/1      , types , true , all_ground_types ).
abs_ex( not_free/1    , types , true , notvartype(1) ).

%-------------------------------------------------------------------%
% Predicates abstractly executable to fail with type   info         %
%-------------------------------------------------------------------%
%abs_ex( integer/1     , types , fail , incomp_type(1,int) ).
abs_ex( float/1       , types , fail , incomp_type(1,flt) ).
abs_ex( number/1      , types , fail , incomp_type(1,num) ).
abs_ex( list/1        , types , fail , incomp_type(1,list)).
abs_ex( '='/2         , types , fail , one_concr_nequal   ).
abs_ex( var/1         , types , fail , notvartype(1)      ).
% this one is needed since the native property for 
% term_typing:var/1 is free/1
abs_ex( free/1         , types , fail , notvartype(1)      ).
%-------------------------------------------------------------------%
% Predicates abstractly executable to fail with groundness info     %
%-------------------------------------------------------------------%
%abs_ex( open_null_stream/1 , ground , fail , ground(1)). % in assertion
abs_ex( assert/2  , ground , fail , ground(2)).
abs_ex( asserta/2 , ground , fail , ground(2)).
abs_ex( assertz/2 , ground , fail , ground(2)).
%abs_ex( var/1     , ground , fail , ground(1)). %in assertion
% this one is needed since the native property for 
% term_typing:var/1 is free/1
abs_ex( free/1    , ground , fail , ground(1)).
abs_ex( recorda/3 , ground , fail , ground(3)).
abs_ex( recordz/3 , ground , fail , ground(3)). % it is just fail in ap

%-------------------------------------------------------------------%
% Predicates abstractly executable to true with groundness info     %
%-------------------------------------------------------------------%
% abs_ex(nonvar/1,ground,true,ground(1)). %in assertion
% ground/1 is treated in a special way (it can have a list as argument)
% since native prop for nonvar is not_free.
abs_ex(not_free/1,ground,true,ground(1)). 

%-------------------------------------------------------------------%
% Predicates abstractly executable to true with independence info   %
%-------------------------------------------------------------------%
abs_ex(indep/2,indep,true,indep(1,2)).
% indep/1 is treated in a special way (it can have a list as argument)


%-------------------------------------------------------------------%
% Predicates abstractly executable to fail with freeness info       %
%-------------------------------------------------------------------%
%abs_ex( atom/1    , free , fail , free(1) ). %in assertion
%abs_ex( atomic/1  , free , fail , free(1) ). %in assertion
%abs_ex( float/1   , free , fail , free(1) ). %in assertion
%abs_ex( integer/1 , free , fail , free(1) ). %in assertion
%abs_ex( nonvar/1  , free , fail , free(1) ). %in assertion
%abs_ex( number/1  , free , fail , free(1) ). %in assertion
%abs_ex(portray_clause/1,free,fail,free(1)). 
abs_ex(recorded/3,free,fail,free(1)). 
abs_ex(recorda/3 , free , fail , free(1)).
abs_ex('=='/2,[free,ground],fail,[frgr(1,2),frgr(2,1)]).
abs_ex('SYSCALL/1',free,fail,free(1)).
abs_ex(not_free/1,free,fail,free(1)). 

%-------------------------------------------------------------------%
% Predicates abstractly executable to true in free domain           %
%-------------------------------------------------------------------%
%abs_ex(var/1,free,true,free(1)). %in assertion
% this one is needed since the native property for 
% term_typing:var/1 is free/1
abs_ex(free/1,free,true,free(1)). %this one cannot be in assertion

%-------------------------------------------------------------------%
% Predicates abstractly executable to error with freeness info      %
%-------------------------------------------------------------------%
abs_ex( abolish/1,        free, error,  free(1)).
%abs_ex( abolish/2,        free, error, [free(1), free(2)]). no longer exists
abs_ex( absolute_file_name/2, free, error, free(1)). 

% Arg1 must be an integer
abs_ex( arg/3,            free, error, [free(1), free(2)]). 
% and Arg2 must be a functor no matter if its arguments are free or not
abs_ex( assert/1,         free, error,  free(1)). 
abs_ex( assert/2,         free, error,  free(1)). 
abs_ex( asserta/1,        free, error,  free(1)). 
abs_ex( asserta/2,        free, error,  free(1)). 
abs_ex( assertz/1,        free, error,  free(1)). 
abs_ex( assertz/2,        free, error,  free(1)). 
abs_ex( bagof/3,          free, error,  free(2)). 
abs_ex( clause/2,         free, error,  free(1)).
abs_ex( clause/3,         free, error,  free(1, 3)).
abs_ex( compile/1,        free, error,  free(1)).  
abs_ex( consult/1,        free, error,  free(1)). 
abs_ex( erase/1,          free, error,  free(1)).  
abs_ex( flush_output/1,   free, error,  free(1)). 
abs_ex( format/2,         free, error,  free(1)).
abs_ex( format/3,         free, error, [free(1), free(2)]).
abs_ex( functor/3,        free, error, [free(1, 2), free(1, 3)]). 
abs_ex( get_code/2,       free, error,  free(1)). % Arg1 must be a stream
abs_ex( get1_code/2,      free, error,  free(1)).
abs_ex( incore/1,         free, error,  free(1)). 
abs_ex( instance/2,       free, error,  free(1)).
abs_ex( is/2,             free, error,  freerec(2)).
abs_ex( keysort/2,        free, error,  free(1)). 
abs_ex( leash/1,          free, error,  free(1)). 
abs_ex( load_foreign_files/2, free, error, [free(1), free(2)]).
abs_ex( maxdepth/1,       free, error,  free(1)). 
abs_ex( name/2,           free, error,  free(1, 2)).

%the argument must be a stream
abs_ex( nl/1,             free, error,  free(1)). 
abs_ex( numbervars/3,     free, error,  free(2)).
abs_ex( op/3,             free, error, [free(1), free(2), free(3)]). 
abs_ex( phrase/2,         free, error,  free(1)). 
abs_ex( phrase/3,         free, error,  free(1)). 
abs_ex( plsys/1,          free, error,  free(1)).  
abs_ex( print/2,          free, error,  free(1)).
abs_ex( prolog_flag/2,    free, error,  free(1)). 
abs_ex( prolog_flag/3,   [free, 
                      indep], error, [free(1), frindep(2, 3)]). 
abs_ex( put_code/1,       free, error,  free(1)).
abs_ex( put_code/2,       free, error, [free(1), free(2)]).
abs_ex( read/2,           free, error,  free(1)).
abs_ex( reconsult/1,      free, error,  free(1)).  
abs_ex( recorda/3,        free, error,  free(1)). 
abs_ex( retract/1,        free, error,  free(1)). 
abs_ex( retractall/1,     free, error,  free(1)).
abs_ex( see/1,            free, error,  free(1)). 
abs_ex( setarg/3,         free, error, [free(1), free(2)]).
abs_ex( setof/3,          free, error,  free(2)). 
abs_ex( skip_code/1,      free, error,  free(1)).
abs_ex( skip_code/2,      free, error, [free(1), free(2)]).
abs_ex( sort/2,           free, error,  free(1)). 
abs_ex( (spy)/1,          free, error,  free(1)). 
abs_ex( stream_code/2,    free, error,  free(1, 2)).
abs_ex( tab/1,            free, error,  free(1)).
abs_ex( tab/2,            free, error, [free(1), free(2)]).
abs_ex( tell/1,           free, error,  free(1)). 
abs_ex( ttyput/1,         free, error,  free(1)).
abs_ex( ttyskip/1,        free, error,  free(1)).
abs_ex( ttytab/1,         free, error,  free(1)).

% it is just fail in ap
abs_ex( unix/1,           free, error,  free(1)). 
abs_ex( unknown/2,       [free, indep], error, frindep(1, 2)).
abs_ex( write/2,          free, error,  free(1)).
abs_ex( write_canonical/2,free, error,  free(1)).
abs_ex( writeq/2,         free, error,  free(1)).
abs_ex( '<'/2, Determ, Sense, Cond):-
    abs_ex_if_not_constraint(Determ, Sense, Cond).
abs_ex( '=..'/2,     free, error, free(1, 2)).
abs_ex( '=:='/2,     free, error, [freerec(1), freerec(2)]).
abs_ex( '=<'/2, Determ, Sense, Cond):-
    abs_ex_if_not_constraint(Determ, Sense, Cond).
abs_ex( (=\=)/2,     free, error, [freerec(1), freerec(2)]).
abs_ex( '>'/2, Determ, Sense, Cond):-
    abs_ex_if_not_constraint(Determ, Sense, Cond).
abs_ex( '>='/2, Determ, Sense, Cond):-
    abs_ex_if_not_constraint(Determ, Sense, Cond).


%-------------------------------------------------------------------%
% Predicates abstractly executable to fail with nongroundness info  %
%-------------------------------------------------------------------%
abs_ex(ground/1,not_ground,fail,not_ground(1)).

%-------------------------------------------------------------------%
% Predicates abstractly executable to fail with nonindep info       %
%-------------------------------------------------------------------%
abs_ex(indep/2,not_indep,fail,not_indep(1,2)).

%-------------------------------------------------------------------%
% Predicates abstractly executable to true with unlinked info       %
%-------------------------------------------------------------------%
abs_ex(unlinked/2,unlinked,true,unlinked(1,2)).

%-------------------------------------------------------------------%
% Predicates abstractly executable to true with nonvar info         %
%-------------------------------------------------------------------%
abs_ex(nonvar/1,nonvar,true,nonvar(1)).

%-------------------------------------------------------------------%
% Predicates abstractly executable to fail with nonvar info         %
%-------------------------------------------------------------------%
abs_ex(var/1,nonvar,fail,nonvar(1)).
% this one is needed since the native property for 
% term_typing:var/1 is free/1
abs_ex(free/1,nonvar,fail,nonvar(1)).

%-------------------------------------------------------------------%
% Predicates abstractly executable to true with polyhedra info      %
%-------------------------------------------------------------------%
abs_ex(constraint/1,polyhedra,true,polyhedra_constraint).

%-----------------------------------------------------------------------%
% Predicates with a special treatment. They can have lists as arguments %
%-----------------------------------------------------------------------%
%GP this line commented out. handling of ground with lists of arguments
% will have to be rethought about (is now disabled)
%abs_ex(ground/1,ground,ground,true):-!.
abs_ex(ground/1,ground,true,ground(1)).
abs_ex(indep/1,ground,true,ground(1)).
abs_ex(indep/1,indep,true,indep(1)).

abs_ex(sharing/2,sharing,true,sharing(1,2)).

abs_ex(freeze/2,ground,freeze,true):-!.
abs_ex(freeze/2,nonvar,freeze,true).

abs_ex(when/2,ground,when,true):-!.
abs_ex(when/2,nonvar,when,true).
% abs_ex(when/2,nonground,when,true):-!.
% abs_ex(when/2,free,when,true):-!.

abs_ex_if_not_constraint(Determ,Sense,Cond):-
    language(lp),
    Determ = free,
    Sense = error,
    Cond = [freerec(1),freerec(2)].
