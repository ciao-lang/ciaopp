:- module(domains, [], [assertions,regtypes,isomodes,nativeprops, ciaopp(ciaopp_options)]).

:- doc(title,"Plug-in points for abstract domains").

:- doc(author,"Maria Garcia de la Banda").
:- doc(author,"Francisco Bueno").

:- doc(module,"This module contains the predicates for selecting
   the abstract operations that correspond to an analysis domain. The
   selection depends on the name of the domain given as first argument
   to all predicates. Whenever a new domain is added to the system, a
   new clause for each predicate exported here will be needed to call
   the corresponding domain operation in the domain module. Some local
   operations used but not exported by this module would have to be
   defined, too. See the following chapter for an example domain module.

   Adding an analysis domain to PLAI requires only changes in this module.
   However, in order for other CiaoPP operations to work, you may need to
   change other modules. See, for example, module @tt{infer_dom}.

   In this chapter, arguments referred to as @tt{Sv}, @tt{Hv}, @tt{Fv},
   @tt{Qv}, @tt{Vars} are lists of program variables and are supposed to 
   always be sorted. Abstract substitutions are referred to as @tt{ASub}, 
   and are also supposed sorted (except where indicated), although this 
   depends on the domain.
").

:- doc(bug,"When interpreting assertions (and native) should take 
	into account things like sourcename(X):- atom(X) and
        true pred atom(X) => atm(X).").
:- doc(bug,"@pred{body_succ_builtin/9} seems to introduce spurious 
	choice-points.").
:- doc(bug,"Property @tt{covered/2} is not well understood by the
	domains.").
:- doc(bug,"Operation @tt{amgu/5} is missing.").

% TODO: Define extend/5 and project/5 without the extra Subgoal
% argument.  Define extend/6 and project/6 just for those domains and
% fixpoints that require them.

% ===========================================================================

:- use_module(ciaopp(p_unit), [native_prop/2, native_props/2]).
:- use_module(ciaopp(plai/fixpo_ops), [each_exit_to_prime/8, each_abs_sort/3]).

:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars),  [varset/2]).
%:- use_module(library(assertions/native_props), [linear/1]).
:- use_module(library(assertions/native_props_rtc), [rtc_linear/1]). % TODO: code that implements rtc_linear/1 should be in terms_check (like variant/2, etc.)

:- use_module(library(terms_check), [instance/2]).

:- use_module(ciaopp(infer/low_level_props), [decide_low_level_format/4]).

%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
%  AbsInt  : identifier of the abstract interpreter being used           %
%  Sg      : Subgoal being analysed                                      %
%  SgKey   : Subgoal key (represented by functor/arity)                  %
%  Head    : Head of the clause being analysed                           %
%  Sv      : Subgoal variables                                           %
%  Hv      : Head variables                                              %
%  Fv      : Free variables in the body of the clause being considered   %
%  Vars    : Any possible set of variables                               %
%  Call    : Abstract call substitution                                  %
%  Proj    : Call projected onto Sv                                      %
%  Entry   : Abstract entry substitution (i.e. the abstract subtitution  %
%            obtained after the abstract unification of Sg and Head      %
%            projected onto Hv + Fv)                                     %
%  Exit    : Abstract exit substitution (i.e. the abstract subtitution   %
%            obtained after the analysis of the clause being considered  %
%            projected onto Hv)                                          %
%  Prime   : Abstract prime substitution (i.e. the abstract subtitution  %
%            obtained after the analysis of the clause being considered  %
%            projected onto Sv)                                          %
%  Succ    : Abstract success substitution (i.e. the abstract subtitution%
%            obtained after the analysis of the clause being considered  %
%            extended to the variables of the clause in which Sg appears)%
%  ASub    : Any possible abstract substitution                          %
%  R_flag  : Flag which represents the recursive characteristics of a    %
%            predicate. It will be "nr" in case the predicate be non     % 
%            recursive. Otherwise it will be r (recursive)
% List     : (can be represented as OldList,List,AddList,IdList,NewList) %
%            current the list of nodes which a given node depends on.    %
% _s       : The suffix _s means that the term to which the variable is  %
%            bound to has been sorted. By default they are always sorted %
%            thus _s is added only when it appears neccessary to say it  %
%            explicitely                                                 %
% _uns     : The suffix _uns means that the term to which the variable   %
%            is bound is not sorted                                      %
% ExtraInfo: Info computed during the call_to_entry that can be reused   %
%            during the exit_to_prime step                               %
%------------------------------------------------------------------------%

% ===========================================================================
:- doc(section, "Domain declaration").

:- doc(aidomain(AbsInt),"Declares that @var{AbsInt} identifies
	an abstract domain.").
:- multifile aidomain/1. % TODO: remove this multifile decl (and others)

% ===========================================================================
:- doc(section, "Initialization").

:- export(init_abstract_domain/2).
% init_abstract_domain(+,-)
:- doc(init_abstract_domain(AbsInt,PushedFlags), "Initializes abstract
   domain @var{AbsInt}. Tells the list of modified (pushed) PP flags to
   pop afterwards.").
% TODO: This initialization predicate silently overwrites some
%   pp_flags. This may be very confusing for the user.
% TODO: This should be part of the definition of the domain. 
%% terms_init:- repush_types.

% ===========================================================================
:- doc(section, "Basic domain operations").

:- export(amgu/5).
:- pred amgu(+AbsInt,+Sg,+Head,+ASub,-AMGU) : atm(AbsInt) + not_fails
        #"Perform the abstract unification @var{AMGU} between @var{Sg} and
          @var{Head} given an initial abstract substitution @var{ASub} and
          abstract domain @var{AbsInt}.".

:- export(augment_asub/4).
% augment_asub(+,+,+,-)
:- doc(augment_asub(AbsInt,ASub,Vars,ASub0), "Augment the abstract
   substitution @var{ASub} adding the variables @var{Vars} and then
   resulting the abstract substitution @var{ASub0}.").

:- export(augment_two_asub/4).
% augment_two_asub(+,+,+,-)
:- doc(augment_two_asub(AbsInt,ASub0,ASub1,ASub), "@var{ASub} is an
           abstract substitution resulting of augmenting two abstract
           substitutions: @var{ASub0} and @var{ASub1} whose domains are
           disjoint.").

:- export(call_to_entry/10).
:- pred call_to_entry(+AbsInt,+Sv,+Sg,+Hv,+Head,+ClauseKey,+Fv,+Proj,-Entry,-ExtraInfo)
        : (atm(AbsInt), list(Sv), list(Hv), list(Fv)) + not_fails
  #"Obtains the abstract substitution @var{Entry} which results from
   adding the abstraction of the unification @var{Sg} = @var{Head} to
   abstract substitution @var{Proj} (the call substitution for
   @var{Sg} projected on its variables @var{Sv}) and then projecting
   the resulting substitution onto @var{Hv} (the variables of
   @var{Head}) plus @var{Fv} (the free variables of the relevant
   clause). @var{ExtraInfo} is information which may be reused later
   in other abstract operations.".
% TODO: Document ClauseKey (required by res_plai)
% TODO: Document ClauseKey=not_provided

:- export(exit_to_prime/8).
:- pred exit_to_prime(+AbsInt,+Sg,+Hv,+Head,+Sv,+Exit,?ExtraInfo,-Prime)
        : (atm(AbsInt), list(Hv,var), list(Sv, var)) + not_fails
   #"Computes the abstract substitution @var{Prime} which results from
   adding the abstraction of the unification @var{Sg} = @var{Head} to
   abstract substitution @var{Exit} (the exit substitution for a
   clause @var{Head} projected over its variables @var{Hv}),
   projecting the resulting substitution onto @var{Sv}.".

% TODO:[new-resources] compatibility with project/5 (unbound Sg!)
:- export(project/5).
:- pred project(+AbsInt,+Vars,+HvFv_u,+ASub,-Proj)
        : atm * list * list * term * term + not_fails
        #"Projects the abstract substitution @var{ASub} onto the variables of
         list @var{Vars} resulting in the projected abstract substitution
         @var{Proj}.".
project(AbsInt,Vars,HvFv,ASub,Proj) :-
	project(AbsInt,_,Vars,HvFv,ASub,Proj). % TODO: Unbound Sg is a problem! (IG)

% TODO:[new-resources] version with Sg, really needed?
:- export(project/6). % TODO:[new-resources] (extra)
:- pred project(+AbsInt,+Sg,+Vars,+HvFv_u,+ASub,-Proj)
        : atm * term * list * list * term * term + not_fails
        #"Projects the abstract substitution @var{ASub} onto the variables of
          list @var{Vars} resulting in the projected abstract substitution
          @var{Proj}.".

:- export(widencall/4).
:- pred widencall(+AbsInt,+ASub0,+ASub1,-ASub) : atm(AbsInt)
        #"@var{ASub} is the result of widening abstract substitution @var{ASub0}
          and @var{ASub1}, which are supposed to be consecutive call patterns in
         a fixpoint computation.

         @begin{alert} This predicate is allowed to fail and it fails if the
         domain does not define a widening on calls.
         @end{alert} ".

:- export(dual_widencall/4).
% dual_widencall(+,+,+,-)
:- doc(dual_widencall(AbsInt,ASub0,ASub1,ASub),"@var{ASub} is the result of
   dual widening abstract substitution @var{ASub0} and @var{ASub1}, which
   are supposed to be consecutive call patterns in a fixpoint computation.").
dual_widencall(_AbsInt,_ASub0,_ASub1,_ASub) :- fail.
% TODO: [IG]This is only used in fixpo_plai_gfp.

:- export(widen/4).
:- pred widen(+AbsInt,+ASub0,+ASub1,-ASub) : atm(AbsInt) + not_fails
        #"@var{ASub} is the result of widening abstract substitution @var{ASub0}
          and @var{ASub1}, which are supposed to be consecutive approximations
          to the same abstract value.".

:- export(dual_widen/4).
% dual_widen(+,+,+,-)
:- doc(dual_widen(AbsInt,ASub0,ASub1,ASub),"@var{ASub} is the result of
   dual widening abstract substitution @var{ASub0} and @var{ASub1}, which
   are supposed to be consecutive approximations to the same abstract
   value.").

dual_widen(AbsInt,Prime0,Prime1,NewPrime) :-
	compute_glb(AbsInt,[Prime0,Prime1],NewPrime).
% TODO: [IG] I think this name is not correct to perform the glb
% TODO: only used in fixpo_plai_gfp and fixpo_ops_gfp

:- export(normalize_asub/3).
% normalize_asub(+,+,-)
:- doc(normalize_asub(AbsInt,ASub0,ASub1),"@var{ASub1} is the
   result of normalizing abstract substitution @var{ASub0}. This is
   required in some domains, specially to perform the widening.").
% some domains need normalization to perform the widening:
normalize_asub(_AbsInt,Prime,Prime).
% [IG] This fixpo_plai and fixpo_plai_gfp each time an internal fixpoint is
% started if the widen flag is set to on, maybe because the widening on calls is
% needed

:- export(compute_lub/3).
:- pred compute_lub(+AbsInt,+ListASub,-LubASub) : atm * list * term
        #"@var{LubASub} is the least upper bound of the abstract substitutions
         in list @var{ListASub}.".

:- export(compute_glb/3).
% compute_glb(+,+,-)
:- doc(compute_glb(AbsInt,ListASub,GlbASub),"@var{GlbASub} is the
   greatest lower bound of the abstract substitutions in list @var{ListASub}.").
% TODO:[new-resources] needed?
compute_glb(AbsInt,[A,B],Glb) :-
        glb(AbsInt,A,B,Glb). % For backwards compatibility

:- doc(hide,compute_clauses_lub/4).
:- export(compute_clauses_lub/4).

:- doc(hide,compute_clauses_glb/4).
:- export(compute_clauses_glb/4).

%% :- export(lub_all/4).
%% % lub_all(+,+,+,-)
%% % lub_all(AbsInt,ListPatterns,Goal,LubbedPattern)
%% % It computes the lub of a set of patterns (AGoal,AProj,APrime) wrt Goal
%% % returning the pattern (Goal,Proj,Prime)
%% 
%% lub_all(AbsInt,[(Goal0,Proj0,Prime0)|Patterns],Goal,Lub) :-
%% 	varset(Goal,Hv),
%% 	project_pattern(Goal0,Proj0,Prime0,AbsInt,Goal,Hv,Proj,Prime),
%% 	lub_all0(Patterns,Goal,Hv,Proj,Prime,AbsInt,Lub).
%% 
%% lub_all0([(Goal0,Proj0,Prime0)|Patterns],Goal,Hv,Proj1,Prime1,AbsInt,Lub) :-
%% 	project_pattern(Goal0,Proj0,Prime0,AbsInt,Goal,Hv,Proj2,Prime2),
%% 	compute_lub_el(AbsInt,Proj1,Proj2,Proj),
%% 	compute_lub_el(AbsInt,Prime1,Prime2,Prime),
%% 	lub_all0(Patterns,Goal,Hv,Proj,Prime,AbsInt,Lub).
%% lub_all0([],Goal,_Hv,Proj,Prime,_AbsInt,(Goal,Proj,Prime)).
%% 
%% project_pattern(Goal0,Proj0,Prime0,AbsInt,Goal,Hv,Proj,Prime) :-
%% 	varset(Goal0,Sv),
%% 	abs_sort(AbsInt,Proj0,Proj_s),
%% 	call_to_entry0(Proj_s,AbsInt,Sv,Goal0,Hv,Goal,[],Proj,_),
%% 	abs_sort(AbsInt,Prime0,Prime_s),
%% 	call_to_entry0(Prime_s,AbsInt,Sv,Goal0,Hv,Goal,[],Prime,_).
%% 
%% call_to_entry0('$bottom',_AbsInt,_Sv,_Goal0,_Hv,_Goal,_Fv,'$bottom',_E) :- !.
%% call_to_entry0(Proj_s,AbsInt,Sv,Goal0,Hv,Goal,Fv,Proj,E) :-
%% 	call_to_entry(AbsInt,Sv,Goal0,Hv,Goal,not_provided,Fv,Proj_s,Proj,E).

:- export(identical_proj/5).
:- pred identical_proj(+AbsInt,+Sg,+Proj,+Sg1,+Proj1) : atm(AbsInt)
        #"Abstract patterns @var{Sg}:@var{Proj} and @var{Sg1}:@var{Proj1} are
          equivalent in domain @var{AbsInt}. Note that @var{Proj} is assumed to
          be already sorted.".
identical_proj(AbsInt,Sg,Proj,Sg1,Proj1) :-
	variant(Sg,Sg1),
	Sg = Sg1,
	abs_sort(AbsInt,Proj1,Proj1_s),
	identical_abstract(AbsInt,Proj,Proj1_s).

:- export(identical_proj_1/7).
:- pred identical_proj_1(AbsInt,Sg,Proj,Sg1,Proj1,Prime1,Prime2)
 #"Abstract patterns @var{Sg}:@var{Proj} and @var{Sg1}:@var{Proj1} are
   equivalent in domain @var{AbsInt}. Note that @var{Proj} is assumed to be
   already sorted. It is different from @tt{identical_proj/5} because it can be
   true although @var{Sg} and @var{Sg1} are not variant".
identical_proj_1(AbsInt,Sg,Proj,Sg1,Proj1,Prime1,Prime2) :-
	\+ variant(Sg,Sg1),
	rtc_linear(Sg1),
	%
	varset(Sg1,Hv),
	varset(Sg,Hvv),
	%
	functor(Sg,F,A),
	functor(Norm,F,A),
	varset(Norm,Hvnorm),
	%
	call_to_entry(AbsInt,_Sv,Sg,Hvnorm,Norm,not_provided,[],Proj,Entry,_), % TODO: add some ClauseKey? (JF)
	call_to_entry(AbsInt,_Sv,Sg1,Hvnorm,Norm,not_provided,[],Proj1,Entry1,_), % TODO: add some ClauseKey? (JF)
	identical_abstract(AbsInt,Entry,Entry1),
	%
	% call_to_entry(AbsInt,_Sv,Sg,Hv,Sg1,not_provided,[],Proj,Entry,_),
        % abs_sort(AbsInt,Entry,Entry_s),
        % abs_sort(AbsInt,Proj1,Proj1_s),
	% identical_abstract(AbsInt,Proj1_s,Entry_s),
	%
	% call_to_entry(AbsInt,_Sv,Sg1,Hvv,Sg,not_provided,[],Proj1,Entry1,_),
        % abs_sort(AbsInt,Entry1,Entry1_s),
        % abs_sort(AbsInt,Proj,Proj_s),
	% identical_abstract(AbsInt,Proj_s,Entry1_s),
	%
	each_abs_sort(Prime1,AbsInt,Prime1_s),
	each_exit_to_prime(Prime1_s,AbsInt,Sg,Hv,Sg1,Hvv,(no,Proj),Prime2).

:- export(identical_abstract/3).
:- pred identical_abstract(+AbsInt,+ASub1,+ASub2) : atm(AbsInt)
        #"Succeeds if, in the particular abstract domain, the two abstract
          substitutions @var{ASub1} and @var{ASub2} are defined on the same
          variables and are equivalent.".
% TODO: [IG] This should be implemented in each domain

:- doc(hide,fixpoint_covered/3).
:- export(fixpoint_covered/3).

:- doc(hide,fixpoint_covered_gfp/3).
:- export(fixpoint_covered_gfp/3).

:- export(abs_sort/3).
:- pred abs_sort(+AbsInt,+ASub_u,ASub) : atm(AbsInt) + not_fails
        #"@var{ASub} is the result of sorting abstract substitution
         @var{ASub_u}.".

% TODO:[new-resources] compatibility with extend/5 (unbound Sg!)
:- export(extend/5).
:- pred extend(+AbsInt,+Prime,+Sv,+Call,-Succ) : atm(AbsInt) + not_fails
        #"@var{Succ} is the extension the information given by @var{Prime}
          (success abstract substitution over the goal variables @var{Sv}) to
          the rest of the variables of the clause in which the goal occurs
          (those over which abstract substitution @var{Call} is defined on).
          I.e., it is like a conjunction of the information in @var{Prime} and
          @var{Call}, except that they are defined over different sets of
          variables, and that @var{Prime} is a successor substitution to
          @var{Call} in the execution of the program.".
extend(AbsInt,Prime,Sv,Call,Prime) :-
	extend(AbsInt,_,Prime,Sv,Call,Prime).

% TODO:[new-resources] version with Sg, really needed?
:- export(extend/6). % TODO:[new-resources] (extra)
:- pred extend(+AbsInt,+Sg,+Prime,+Sv,+Call,-Succ) : atm(AbsInt) + not_fails
   #"@var{Succ} is the extension the information given by @var{Prime} (success
    abstract substitution over the goal variables @var{Sv}) to the rest of the
    variables of the clause in which the goal occurs (those over which
    abstract substitution @var{Call} is defined on). I.e., it is like a
    conjunction of the information in @var{Prime} and @var{Call}, except that
    they are defined over different sets of variables, and that @var{Prime} is
    a successor substitution to @var{Call} in the execution of the program.
    ".

:- export(less_or_equal_proj/5).
:- pred less_or_equal_proj(+AbsInt,+Sg,+Proj,+Sg1,+Proj1) : atm(AbsInt)
   #"Abstract pattern @var{Sg}:@var{Proj} is less general or equivalent to
    abstract pattern @var{Sg1}:@var{Proj1} in domain @var{AbsInt}.".
less_or_equal_proj(AbsInt,Sg,Proj,Sg1,Proj1) :-
	variant(Sg,Sg1),
	Sg = Sg1,
	abs_sort(AbsInt,Proj1,Proj1_s),
	less_or_equal(AbsInt,Proj,Proj1_s).

:- export(less_or_equal/3).
:- pred less_or_equal(+AbsInt,+ASub0,+ASub1) : atm(AbsInt)
        #"Succeeds if @var{ASub1} is more general or equivalent to @var{ASub0}.".

:- export(glb/4).
:- pred glb(+AbsInt,+ASub0,+ASub1,-GlbASub) : atm(AbsInt) + not_fails
        #"@var{GlbASub} is the greatest lower bound of abstract substitutions
         @var{ASub0} and @var{ASub1}.".

% ===========================================================================
:- doc(section, "Specialized operations (including builtin handling)").

:- export(eliminate_equivalent/3).
% eliminate_equivalent(+,+,-)
:- doc(eliminate_equivalent(AbsInt,TmpLSucc,LSucc),
   "The list @var{LSucc} is reduced wrt the list @var{TmpLSucc} in that it
    does not contain abstract substitutions which are equivalent.").

:- export(abs_subset/3).
% abs_subset(+,+,+)
:- doc(abs_subset(AbsInt,LASub1,LASub2),
   "Succeeds if each abstract substitution in list @var{LASub1} is equivalent
    to some abstract substitution in list @var{LASub2}.").

:- export(call_to_success_fact/10). % TODO:[new-resources] (extra)
:- pred call_to_success_fact(+AbsInt,+Sg,+Hv,+Head,+K,+Sv,+Call,+Proj,-Prime,-Succ)
        : atm(AbsInt) + not_fails
        #"Specialized version of call_to_entry + entry_to_exit + exit_to_prime
          for a fact @var{Head}.".

% TODO: fix modes, it was: special_builtin(+,+,+,-,-)
:- export(special_builtin/6).
:- pred special_builtin(+AbsInt,+SgKey,+Sg,?Subgoal,-Type,-Condvars) : atm(AbsInt)
        #"Predicate @var{Sg} is considered a ""builtin"" of type @var{Type} in
          domain @var{AbsInt}. Types are domain dependent. Domains may have two
          different ways to treat these predicates: see
          @tt{body_succ_builtin/9}.".

:- doc(hide,combined_special_builtin/3).
:- export(combined_special_builtin/3).

:- doc(hide,split_combined_domain/4).
:- export(split_combined_domain/4).

% TODO: fix modes, it was: body_succ_builtin(+,+,+,+,+,+,+,+,-)
:- export(body_succ_builtin/9).
:- pred body_succ_builtin(+AbsInt,+Type,+Sg,?Vs,+Sv,+Hv,+Call,+Proj,-Succ) :
        atm(AbsInt) + not_fails % this predicate should not fail
   #"Specialized version of call_to_entry + entry_to_exit + exit_to_prime +
    extend for predicate @var{Sg} considered a ""builtin"" of type @var{Type}
    in domain @var{AbsInt}. Whether a predicate is ""builtin"" in a domain is
    determined by @tt{special_builtin/5}.  There are two different ways to
    treat these predicates, depending on @var{Type}: @tt{success_builtin}
    handles more usual types of ""builtins"", @tt{call_to_success_builtin}
    handles particular predicates. The later is called when @var{Type} is of
    the form @tt{special(SgKey)}.".

:- doc(doinclude,success_builtin/7).
:- pred success_builtin(AbsInt,Type,Sv,Condvars,HvFv_u,Call,Succ)
        : atm(AbsInt) + not_fails
 #"@var{Succ} is the success substitution on domain @var{AbsInt} for a call
   @var{Call} to a goal of a ""builtin"" (domain dependent) type @var{Type}
   with variables @var{Sv}. @var{Condvars} can be used to transfer some
   information from @tt{special_builtin/5}.".

:- doc(doinclude,call_to_success_builtin/7).
:- pred call_to_success_builtin(AbsInt,Type,Sg,Sv,Call,Proj,Succ) + not_fails
        #"@var{Succ} is the success substitution on domain @var{AbsInt} for a
          call @var{Call} to a goal @var{Sg} with variables @var{Sv} considered
          of a ""builtin"" (domain dependent) type @var{Type}. @var{Proj} is
          @var{Call} projected on @var{Sv}.".

% ===========================================================================
:- doc(section, "Properties directly from domain").

:- export(obtain_info/5).
:- pred obtain_info(+AbsInt,+Prop,+Vars,+ASub,-Info) : atm(AbsInt)
        #"Obtains variables @var{Info} for which property @var{Prop} holds given
          abstract substitution @var{ASub} on variables @var{Vars} for domain
          @var{AbsInt}.".

% ===========================================================================
:- doc(section, "Properties to domain and viceversa").

:- export(info_to_asub/7).
% info_to_asub(+,+,+,+,-,+,+)
:- doc(info_to_asub(AbsInt,Kind,InputUser,Qv,ASub,Sg,MaybeCallASub),
   "Obtains the abstract substitution @var{ASub} on variables @var{Qv} for
    domain @var{AbsInt} from the user supplied information @var{InputUser}
    refering to properties on @var{Qv}. It works by calling
    @tt{input_interface/5} on each property of @var{InputUser} which is a
    native property, so that they are accumulated, and then calls
    @tt{input_user_interface/6}."). % TODO: Document MaybeCallASub
info_to_asub(AbsInt,Kind,InputUser,Qv,ASub,Sg,MaybeCallASub) :-
	info_to_asub_(InputUser,AbsInt,Kind,_,Input),
	input_user_interface(AbsInt,Input,Qv,ASub,Sg,MaybeCallASub),
	!. % TODO: make sure that cut is not needed

info_to_asub_([],_AbsInt,_Kind,Acc,Acc).
info_to_asub_([I|Info],AbsInt,_Kind,Acc0,Acc) :-
	( native_prop(I,P),
	  input_interface(AbsInt,P,_Kind1,Acc0,Acc1) -> true
	; Acc1=Acc0 ),
	info_to_asub_(Info,AbsInt,_Kind2,Acc1,Acc).

%% Commented out by PLG 8 Jun 2003
%% info_to_asub_([],_AbsInt,_Kind,Acc,Acc).
%% info_to_asub_([I|Info],AbsInt,Kind,Acc0,Acc) :-
%% 	( native_prop(I,P),
%% 	  input_interface(AbsInt,P,Kind,Acc0,Acc1) -> true
%% 	; Acc1=Acc0 ),
%% 	info_to_asub_(Info,AbsInt,Kind,Acc1,Acc).

:- export(full_info_to_asub/5).
:- doc(full_info_to_asub(AbsInt,InputUser,Qv,ASub,Sg),
   "Same as @tt{info_to_asub(AbsInt,InputUser,Qv,ASub)} except that it fails
    if some property in @var{InputUser} is not native or not relevant to the
    domain @var{AbsInt}.").

full_info_to_asub(AbsInt,InputUser,Qv,ASub,Sg) :-
	full_info_to_asub_(InputUser,AbsInt,_,Input),
	input_user_interface(AbsInt,Input,Qv,ASub,Sg,no),
	!. % TODO: make sure that cut is not needed

full_info_to_asub_([],_AbsInt,Acc,Acc).
full_info_to_asub_([I|Info],AbsInt,Acc0,Acc) :-
	native_prop(I,P),
	input_interface(AbsInt,P,perfect,Acc0,Acc1), !, % P is enough (PBC)
	                                                % do not backtrack
	full_info_to_asub_(Info,AbsInt,Acc1,Acc).       % into native_prop

:- doc(doinclude,input_interface/5).
:- doc(input_interface(AbsInt,Prop,Kind,Struc0,Struc1),
   "@var{Prop} is a native property that is relevant to domain @var{AbsInt}
    (i.e., the domain knows how to fully --@var{+Kind}=perfect-- or 
    approximately --@var{-Kind}=approx-- abstract it) and @var{Struct1} is a
    (domain defined) structure resulting of adding the (domain dependent)
    information conveyed by @var{Prop} to structure @var{Struct0}. This way,
    the properties relevant to a domain are being accumulated.").

:- doc(doinclude,input_user_interface/6).
:- doc(input_user_interface(AbsInt,Struct,Qv,ASub,Sg,MaybeCallASub),
   "@var{ASub} is the abstraction in @var{AbsInt} of the information collected
    in @var{Struct} (a domain defined structure) on variables @var{Qv}.").

:- export(asub_to_info/5).
% asub_to_info(+,+,+,-,-)
:- doc(asub_to_info(AbsInt,ASub,Qv,OutputUser,CompProps),
   "Transforms an abstract substitution @var{ASub} on variables @var{Qv} for a
    domain @var{AbsInt} to a list of state properties @var{OutputUser} and
    computation properties @var{CompProps}, such that properties are
    visible in the preprocessing unit. It fails if @var{ASub} represents
    bottom. It works by calling @tt{asub_to_native/6}.").

asub_to_info(AbsInt,ASub,Qv,OutputUser,CompProps) :-
	asub_to_native(AbsInt,ASub,Qv,no,Info,Comp),
	native_props(Info,OutputUser),
	native_props(Comp,CompProps).

:- doc(hide,asub_to_out/5).
:- export(asub_to_out/5).
asub_to_out(AbsInt,ASub,Qv,OutputUser,CompProps) :-
	asub_to_native(AbsInt,ASub,Qv,yes,Info,Comp),
	native_props(Info,OutputUser0),
	native_props(Comp,CompProps0),
	decide_low_level_format(OutputUser0,CompProps0,OutputUser,CompProps).
	
:- export(asub_to_native/6).
:- doc(asub_to_native(AbsInt,ASub,Qv,OutFlag,NativeStat,NativeComp),
   "@var{NativeStat} and @var{NativeComp} are the list of native (state and
    computational, resp.) properties that are the concretization
    of abstract substitution @var{ASub} on variables @var{Qv} for domain
    @var{AbsInt}. These are later translated to the properties which are
    visible in the preprocessing unit."). % TODO: document OutFlag=yes for output

:- export(concrete/4).
% concrete(+,+,+,-)
:- doc(concrete(AbsInt,Var,ASub,List),
   "@var{List} are (all) the terms to which @var{Var} can be bound in the 
    concretization of @var{ASub}, if they are a finite number of finite
    terms. Otherwise, the predicate fails.").

% TODO: body_succ0('$var',...) passes unbound Sg (due to metacall), use call(Sg) (or similar) instead? (JF)
:- export(unknown_call/5).
:- pred unknown_call(+AbsInt,+Sg,+Vars,+Call,-Succ)
        : (atm(AbsInt), list(Vars)) + not_fails
        #"@var{Succ} is the result of adding to @var{Call} the ``topmost''
          abstraction in domain @var{AbsInt} of the variables @var{Vars}
          involved in a literal @var{Sg} whose definition is not present in the
          preprocessing unit. I.e., it is like the conjunction of the
          information in @var{Call} with the top for a subset of its variables.".

:- export(unknown_entry/4).
:- pred unknown_entry(+AbsInt,+Sg,+Vars,-Entry) : (atm(AbsInt), list(Vars)) + not_fails
   #"@var{Entry} is the ""topmost"" abstraction in domain @var{AbsInt} of 
    variables @var{Vars} corresponding to literal @var{Sg}.".

:- export(empty_entry/3).
:- pred empty_entry(+AbsInt,+Vars,-Entry) : atm * list * term + not_fails
        #"@var{Entry} is the ""empty"" abstraction in domain @var{AbsInt} of
          variables @var{Vars}. I.e., it is the abstraction of a substitution on
          @var{Vars} in which all variables are unbound: free and unaliased.".

% ===========================================================================
:- doc(section, "Other particular operations").

%% :- export(propagate_downwards_closed/4).
%% % propagate_downwards_closed(+,+,+,-)
%% % propagate_downwards_closed(AbsInt,ASub1,ASub2,ASub)
%% % Propagates the downwards closed properties from ASub1 to ASub2
%% 
%% :- export(del_real_conjoin/4).
%% % del_real_conjoin(+,+,+,-)
%% % del_real_conjoin(AbsInt,ASub1,ASub2,ASub)
%% % Propagates the downwards closed properties from ASub1 to ASub2
%% 
%% :- export(del_hash/4).
%% % del_hash(+,+,+,-)
%% % del_hash(AbsInt,ASub,Vars,N)
%% % Returns a number which identifies ASub
%% 
%% :- export(more_instantiate/3).
%% % more_instantiate(+,+,+)
%% % more_instantiate(AbsInt,ASub1,ASub2)
%% % Succesdes if ASub2 is possibly more instantiated than ASub1
%% 
%% :- export(convex_hull/4).
%% % convex_hull(+,+,+,-)
%% % convex_hull(AbsInt,ASub1,ASub2,Hull)
%% 
%% :- export(compute_lub_el/4).
%% % compute_lub_el(+,+,+,-)
%% % compute_lub_el(AbsInt,ASub1,ASub2,Lub)
%% % Lub is the lub of abstractions ASub1 and ASub2
%% 
%% :- export(extend_free/4).
%% % extend_free(+,+,+,-)
%% % extend_free(AbsInt,ASub,Vars,ExtASub)
%% % It extends ASub to the new (free) vars in Vars
%% 
%% :- export(del_check_cond/6).
%% % del_check_cond(+,+,+,+,-,-)
%% % del_check_cond(AbsInt,Cond,ASub,Sv,Flag,WConds)
%% % Determines if a subgoal is definitely awake (Flag = w), definitely
%% % delayed (Flag = d), or possibly awake (Flag = set of abstractions
%% % under which the subgoal can be woken), w.r.t. abstraction ASub
%% 
%% :- export(del_impose_cond/5).
%% % del_impose_cond(+,+,+,+,-)
%% % del_impose_cond(AbsInt,Cond,Sv,ASub,NewASub)

:- export(part_conc/5).
:- doc(part_conc(AbsInt,Sg,Subs,NSg,NSubs), "This operation
     returns in @var{NSg} an instance of @var{Sg} in which the
     deterministic structure information available in @var{Subs} is
     materialized. The substitution @var{NSubs} refers to the
     variables in @var{NSg}. ").

:- export(multi_part_conc/4).
:- doc(multi_part_conc(AbsInt,Sg,Subs,List), "Similar to part_conc
     but it gives instantiations of goals even in the case types are
     not deterministic, it generates a @var{List} of pairs of goals
     and substitutions. It stops unfolding types as soon as they are
     recursive.").

% ---------------------------------------------------------------------------
% % TODO: [IG] move?

:- export(collect_types_in_abs/4).  % TODO: [IG] only used in typeslib/dumper.pl
:- doc(collect_types_in_abs(ASub,AbsInt,Types,Tail), "Collects
	the type symbols occurring in @var{ASub} of domain @var{AbsInt}
        in a difference list @var{Types}-@var{Tail}.").

collect_types_in_abs('$bottom',_AbsInt,Types0,Types) :- !,
	Types = Types0.
collect_types_in_abs(ASub,AbsInt,Types0,Types) :-
	collect_abstypes_abs(AbsInt,ASub,Types0,Types).

% :- export(collect_abstypes_abs/4).

:- export(rename_types_in_abs/4).  % TODO: [IG] only used in typeslib/dumper.pl
:- doc(rename_types_in_abs(ASub0,AbsInt,Dict,ASub1), "Renames
	the type symbols occurring in @var{ASub0} of domain @var{AbsInt}
        for the corresponding symbols as in (avl-tree) @var{Dict}
        yielding @var{ASub1}.").

rename_types_in_abs('$bottom',_AbsInt,_Dict,ASub) :- !,
	ASub = '$bottom'.
rename_types_in_abs(ASub0,AbsInt,Dict,ASub1) :-
	rename_abstypes_abs(AbsInt,ASub0,Dict,ASub1).

% :- export(rename_abstypes_abs/4).

:- export(dom_statistics/2).
:- doc(dom_statistics(AbsInt, Info), "Obtains in list @var{Info}
   statistics about the results of the abstract interpreter
   @var{AbsInt}.").

:- export(abstract_instance/5).
:- pred abstract_instance(AbsInt,Sg1,Proj1,Sg2,Proj2) # "The pair
	<Sg1,Proj1> is an abstract instance of the pair <Sg2,Proj2>, i.e., the
        concretization of <Sg1,Proj1> is included in the concretization of
        <Sg2,Proj2>.".

abstract_instance(AbsInt,Sg1,Proj1,Sg2,Proj2) :- 
	part_conc(AbsInt,Sg1,Proj1,Sg1C,Proj1C),
	part_conc(AbsInt,Sg2,Proj2,Sg2C,Proj2C),
	instance(Sg1C,Sg2C),
	varset(Sg2C,S2Cv),
	varset(Sg1C,S1Cv),
	call_to_entry(AbsInt,S2Cv,Sg2C,S1Cv,Sg1C,not_provided,[],Proj2C,Entry,_ExtraInfo), % TODO: add some ClauseKey? (JF)
	Entry \== '$bottom',
	less_or_equal(AbsInt,Proj1C,Entry).

:- export(contains_parameters/2).
:- doc(contains_parameters(AbsInt,Subst), "True if an abstract substitution
   @var{Subst} contains type parameters").

% ===========================================================================

:- include(ciaopp(plai/domains_hooks)).
