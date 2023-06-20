:- module(_, [],
    [
        assertions,
        basicmodes,
        regtypes,
        nativeprops,
        datafacts,
        ciaopp(ciaopp_options)
    ]).

%------------------------------------------------------------------------

:- doc(title, "Transform driver (monolithic)").
% TODO: add incremental/modular (with parts as a plugin)?

:- doc(usage, "@tt{:- use_module(ciaopp(transform_driver))}.
   This module is loaded by default in the CiaoPP toplevel and
   reexported from the @lib{ciaopp} module.").

:- doc(module, "This module provides the main entry points for for
   performing program transformations. It requires loading the
   program before (e.g., with @lib{frontend_driver}).

   @section{Adding new transformation}

   To include a new program transformation, add a clause for
   @tt{transform/2} (and for @tt{transformation/1}).

   As an alternative, you can add clauses for the multifile predicates
   @tt{transformation/4} and @tt{transformation/1}, directly in your
   own sources.

   See the file @tt{examples/Extending/myspecializer.pl} in the source
   directory for an example of this.
").

% ---------------------------------------------------------------------------
% (Common)

:- use_module(engine(messages_basic), [message/2]).

:- use_module(ciaopp(preprocess_flags),
              [current_pp_flag/2, set_pp_flag/2, push_pp_flag/2, pop_pp_flag/1]).
:- use_module(ciaopp(ciaopp_log), [pplog/2]).

% ===========================================================================
:- doc(section, "Program transformation").
    
:- use_module(ciaopp(p_unit/itf_db), [curr_file/2]).
:- use_module(ciaopp(p_unit), [program/2]). 
:- use_module(ciaopp(frontend_driver), [push_history/1]).

:- if(defined(with_fullpp)).
:- use_module(ciaopp(p_unit), [replace_program/2]).

:- use_module(ciaopp(plai/normalize_args), [normalize_args/4]).

:- use_module(ciaopp(plai/re_analysis), [update_ai_info_case/4]).

:- use_module(spec(spec), [simplify_specialize/6]).
:- use_module(spec(spec_multiple), [all_versions/5]).
:- use_module(spec(codegen), [codegen/4, codegen_af/4, codegen_min/4]).
:- if(defined(has_ciaopp_extra)).
:- use_module(poly_spec(codegen_pcpe), [print_all_solutions/2]).
:- use_module(poly_spec(heuristic_pcpe), [get_all_solutions/1]).
:- endif.
:- use_module(spec(slicing), [slicing/3]).
:- use_module(spec(arg_filtering), [arg_filtering/5]).
%
:- use_module(ciaopp(tr_unfold/unfold_non_rec), [unfold/5]).

:- if(defined(has_ciaopp_extra)).
%:- use_module(ciaopp(tr_parallel/tr_granul),[annotate_granul/6]).
:- use_module(ciaopp(tr_parallel), []). % Enable parallel transformations
:- endif.

:- endif. % with_fullpp

:- use_module(ciaopp(analyze_driver), [last_domain_used/1]).

:- export(transform/1).
:- pred transform(-Trans) => transformation
    # "Returns on backtracking all available program transformation identifiers.".
:- pred transform(+Trans) : transformation
    # "Performs transformation @var{Trans} on the current module.".
transform(Trans):- var(Trans), !, transformation(Trans). % TODO: ugly
transform(Trans):- transform(Trans,_Info).

:- export(transform/2).
:- pred transform(+Trans,-Info) 
# "Same as transform(@var{Trans}) but returns information that can be
    used to check the results of the transformation.".

transform(Trans,Info):-
    transformation(Trans), !,
    curr_file(File,_),
    pplog(transform_module, ['{Transforming ',~~(File)]),
    program(Cls,Ds),
    push_history(Trans),
    transform_(Trans,Cls,Ds,Info),
    pplog(transform_module, ['}']).
transform(Trans,_Info):-
    message(error0, ['{Not a valid program transformation: ',~~(Trans),'}']),
    fail.

:- if(defined(with_fullpp)).
transform_(spec,Cls,Ds,Info):- !,
    simpspec(spec,Cls,Ds,Info).
transform_(simp,Cls,Ds,Info):- !,
    simpspec(simp,Cls,Ds,Info).
transform_(vers,Cls,Ds,Info):- !,
    simpspec(vers,Cls,Ds,Info).
transform_(codegen,Cls,Ds,Info):- !,
    simpspec(codegen,Cls,Ds,Info).
transform_(codegen_af,Cls,Ds,Info):- !,
    simpspec(codegen_af,Cls,Ds,Info).
transform_(codegen_min,Cls,Ds,Info):- !,
    simpspec(codegen_min,Cls,Ds,Info).
transform_(slicing,Cls,Ds,Info):- !,
    simpspec(slicing,Cls,Ds,Info).
:- if(defined(has_ciaopp_extra)).
transform_(codegen_poly,_Cls,_Ds,Info):- !,
    ( current_pp_flag(fixpoint,poly_spec) ->
        % last_used_domain(AbsInt),
        get_all_solutions(Solutions),
        print_all_solutions(Solutions,Info)
    ; true
    ).
:- endif.
transform_(arg_filtering,Cls,Ds,_Info):- !,
    last_domain_used(AbsInt),
    arg_filtering(Cls,Ds,AbsInt,NCls,NDs),
    replace_program(NCls,NDs).
transform_(unfold_entry,Cls,Ds,_Info) :- !,
    unfold(Cls,Ds,yes,Cls1,Ds1),
    replace_program(Cls1,Ds1).
transform_(normalize, Cls, Ds, _Info ) :- !,
    normalize_args(Cls,Ds,Cls1,Ds1), % TODO: what is this?
    replace_program(Cls1,Ds1).
:- endif. % with_fullpp
transform_(Tr,Cls,Ds,Info):-
    transformation(Tr,Cls,Ds,Info).
%       last_domain_used(AbsInt),
%       codegen_min(Cls,Ds,Info).

:- if(defined(with_fullpp)).

:- use_module(ciaopp(analyze_driver), [cleanup_for_codegen/0]).

simpspec(Spec,Cls,Ds,Info):-
    last_domain_used(AbsInt), !, 
    simpspec_(Spec,AbsInt,Cls,Ds,TmpCls,TmpDs,Info),
    decide_update_ai_info_case(Spec,TmpCls,TmpDs,NewCls,NewDs),
    replace_program(NewCls,NewDs).
simpspec(Spec,_Cls,_Ds,_Info):-
    message(error, ['{Required analysis info not available for ', ~~(Spec), '}']),
    fail.

simpspec_(vers,AbsInt,Cls,Ds,NewCls,NewDs,_Info):- !,
    all_versions(Cls,Ds,AbsInt,NewCls,NewDs).
simpspec_(codegen,AbsInt,Cls,Ds,NewCls,NewDs,Info):- !,
    ( current_pp_flag(local_control,off) -> 
      NewCls = Cls,
        NewDs = Ds 
    ;
        codegen(AbsInt,NewCls,NewDs,Info)
    ).
simpspec_(codegen_af,AbsInt,Cls,Ds,NewCls,NewDs,Info):- !,
    ( current_pp_flag(local_control,off) -> 
      NewCls = Cls,
        NewDs = Ds 
    ;
        codegen_af(AbsInt,NewCls,NewDs,Info)
    ).
simpspec_(codegen_min,AbsInt,Cls,Ds,NewCls,NewDs,Info):- !,
    ( current_pp_flag(local_control,off) -> 
      NewCls = Cls,
        NewDs = Ds 
    ;
        codegen_min(AbsInt,NewCls,NewDs,Info)
    ).
simpspec_(slicing,AbsInt,Cls,Ds,NewCls,NewDs,_Info):- !,
    ( current_pp_flag(local_control,off) -> 
      NewCls = Cls,
        NewDs = Ds 
    ;
        slicing(AbsInt,NewCls,NewDs)
    ).
simpspec_(Spec,AbsInt,Cls,Ds,NewCls,NewDs,_Info):-
    simplify_specialize(AbsInt,Spec,Cls,Ds,NewCls,NewDs).

decide_update_ai_info_case(codegen,Cls,Ds,Cls,Ds):- !.
decide_update_ai_info_case(codegen_af,Cls,Ds,Cls,Ds):-!,
    cleanup_for_codegen.
decide_update_ai_info_case(codegen_min,Cls,Ds,Cls,Ds):-!,
    cleanup_for_codegen.
decide_update_ai_info_case(_Spec,TmpCls,TmpDs,NewCls,NewDs):-
    update_ai_info_case(TmpCls,TmpDs,NewCls,NewDs).
:- endif. % with_fullpp

:- push_prolog_flag(multi_arity_warnings,off).

:- pred transformation(Transformation,Clauses,Dictionaries,Info)
    : transformation(Transformation)
    # "Performs @var{Transformation} on program @var{Clauses}.".
:- multifile transformation/4.

:- prop transformation(Transformation)
    # "@var{Transformation} is a valid transformation identifier.".
:- multifile transformation/1.

:- if(defined(with_fullpp)).
transformation( normalize     ).
transformation( spec          ).
transformation( simp          ).
transformation( vers          ).
transformation( codegen       ).
transformation( codegen_af    ).
:- if(defined(has_ciaopp_extra)).
transformation( codegen_poly  ).
:- endif.
transformation( slicing       ).
transformation( arg_filtering ).
transformation( granul        ).
transformation( rtc           ).
transformation( codegen_min   ).
transformation( unfold_entry  ).
:- endif. % with_fullpp

:- pop_prolog_flag(multi_arity_warnings).

