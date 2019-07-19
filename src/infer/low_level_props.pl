:- module(low_level_props,[decide_low_level_format/4],[assertions]).

:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- prop decide_low_level_format(Prop0,Comp0,Prop,Comp)

# "Transforms the properties in @var{Prop0} and @var{Comp0},
   generating the results in @var{Prop} and @var{Comp}
   respectively. If @tt{low_level_format} flag is set to @tt{off},
   then it does nothing.".

%% CompProps is currently not transformed.
decide_low_level_format(OutputUser0,CompProps,OutputUser,CompProps):-
	current_pp_flag(low_level_format,on), !,
	translate_to_low_level(OutputUser0,OutputUser).
decide_low_level_format(OutputUser,CompProps,OutputUser,CompProps).

translate_to_low_level([],[]).
translate_to_low_level([Prop0|Prop0s],[Prop|Props]):-
	low_level_equivalent(Prop0,Prop), !,
	translate_to_low_level(Prop0s,Props).
translate_to_low_level([_Prop0|Prop0s],Props):-
	translate_to_low_level(Prop0s,Props).


% Freeness
low_level_equivalent('term_typing:var'(X),'$trust_type'(X,var)).
% Determinism
%low_level_equivalent('native_props:non_det'(_),'$props'([impnat=ptoc])).
%low_level_equivalent('native_props:is_det'(_),'$props'([impnat=ptoc, imp=semidet])).
% Basic types
low_level_equivalent('basic_props:num'(X),'$trust_type'(X,number)).
low_level_equivalent('basic_props:int'(X),'$trust_type'(X,smallint)).  %% Incorrect, but temporarily ok.
low_level_equivalent('basic_props:flt'(X),'$trust_type'(X,float)).
low_level_equivalent('basic_props:term'(X),'$trust_type'(X,any)).
% Other types not considered (defined types only).
% low_level_equivalent(Type0,'$trust_type'(Arg,Type)):-
% 	functor(Type0,F,1),  %% Only with arity 1.
% 	arg(1,Type0,Arg),
% 	get_required_types(LTypes),
% 	member(typedef(::=(F,Def)),LTypes),
% 	low_level_equivalent_from_values(Def,Type).
%
% low_level_equivalent_from_values(Def,smallint):-
% 	is_int_disjunction(Def), !.
% low_level_equivalent_from_values(Def,float):-
% 	is_float_disjunction(Def), !.
% low_level_equivalent_from_values(_Def,any).
%
% is_int_disjunction(I):-
% 	integer(I).
% is_int_disjunction((I1;I2)):-
% 	is_int_disjunction(I1),
% 	is_int_disjunction(I2).
%
% is_float_disjunction(I):-
% 	float(I).
% is_float_disjunction((I1;I2)):-
% 	is_float_disjunction(I1),
% 	is_float_disjunction(I2).


