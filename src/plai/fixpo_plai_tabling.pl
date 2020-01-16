/*             Copyright (C)1990-2002 UPM-CLIP                          */
    
:- module(fixpo_plai_tabling,
    [
        query/8,
        init_fixpoint/0,
        cleanup_fixpoint/1,
        entry_to_exit/9
    ],
    [assertions, datafacts]).

:- use_package(.(notrace)). % inhibits the tracing

% Ciao library
:- use_module(engine(io_basic)).

:- use_module(library(aggregates), [bagof/3, (^)/2]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(terms_vars), [varset/2]).
:- use_module(library(terms_check)).
:- use_module(library(sets), [merge/3, ord_subtract/3]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(messages)).
:- use_module(library(write)).

:- use_module(library(format)).
% my_format(A,B):- format(A,B).
my_format(_,_).

% CiaoPP library
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2, set_pp_flag/2]).

% Plai library
:- use_module(ciaopp(plai/fixpo_ops), [inexistent/2, variable/2, bottom/1, 
    singleton/2, fixpoint_id_reuse_prev/5, fixpoint_id/1, fixp_id/1,
    each_abs_sort/3,
    % each_concrete/4,
    each_extend/6, each_project/6, each_exit_to_prime/8, each_unknown_call/5,
    each_body_succ_builtin/12, body_succ_meta/7, reduce_equivalent/3,
    each_apply_trusted/7,   widen_succ/4,   decide_memo/6,clause_applies/2,
    abs_subset_/3, fixpoint_get_new_id/5]).

:- use_module(ciaopp(plai/domains)).
:- use_module(ciaopp(plai/trace_fixp), [fixpoint_trace/7, cleanup/0]).
:- use_module(ciaopp(plai/plai_db), 
    [ complete/7, memo_call/5, memo_table/6, cleanup_plai_db/1, patch_parents/6 ]).
:- use_module(ciaopp(plai/psets), [update_if_member_idlist/3]).
:- use_module(ciaopp(plai/plai_db), [erase_previous_memo_tables_and_parents/4]).
:- use_module(ciaopp(plai/transform), [body_info0/4, trans_clause/3]).
:- use_module(ciaopp(plai/apply_assertions_old),
    [ apply_trusted0/7, 
      cleanup_trusts/1 ]).

%% :- use_module(spec(unfold), 
%%      [ init_unfold/0 ]).

:- doc(author,"Joaquin Arias").

:- doc(module,"This module adapt the implementation of the top-down
	fixpoint algorithm of PLAI, under TCLP with aggregates and an
	extension which also check call entailment.").

:- doc(stability, alpha).

:- doc(bug,"1. Check analysis of meta_calls works after introducing
    fixpoint_reuse_prev_id/5. See, e.g., mmatrix_parallelized.").
:- doc(bug,"2. Add support for mono-variance on calls, in two
    fashions: (1) one call-pattern per predicate, (2) one 
    call-pattern per predicate atom in the program.").
:- doc(bug,"3. Check support for analyzing meta-calls: it does not work
    in success multivariance, and also the constants should be 
    module-expanded. Also, what about [Body|...] in a meta-call?"). 
:- doc(bug,"4. Check analysis of bagof(X,Y^T,Z)").
:- doc(bug,"5. Add support for approximating non-native properties in 
    trusts.").
:- doc(bug,"6. Should we assert complete for meta-calls?").
:- doc(bug,"7. Revise treatment of builtins. Specially when not
    supported by the domain.").
:- doc(bug,"8. Revise all the treatment of bottom. Should probably stop
    inmmediately.").
:- doc(bug,"9. Check the processing for success multivariance.").
:- doc(bug,"10. $meta has extra variables because of the meta-terms. 
    This is confusing (specially on output, maybe also for analysis
    -- see body_succ0). Should not be there, and only added to
    analyze the meta-term.").

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 1/12/90                              %
%                       programmer: Kalyan Muthukumar,                   %
%                          completed: 15/10/92                           %
%              programmers:    M. Garcia de la Banda, F. Bueno           %
%                                                                        %
%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
%  AbsInt  : identifier of the abstract interpreter being used           %
%  Sg      : Subgoal being analysed                                      %
%  SgKey   : Subgoal key (represented by functor/arity)                  %
%  Head    : Head of one of the clauses which define the Sg predicate    %
%  Sv      : Subgoal variables                                           %
%  Hv      : Head variables                                              %
%  Fv      : Free variables in the body of the clause being considered   %
%  HvFv    : Clause variables (Hv + Fv)                                  %
%  Qv      : Q variables                                                 %
%  Vars    : Any possible set of variables                               %
%  Call    : Abstract call substitution                                  %
%  Proj    : Call projected onto Sv                                      %
%  Entry   : Abstract entry substitution (i.e. the abstract subtitution  %
%            obtained after the abstract unification of Sg and Head      %
%            projected onto HvFv)                                        %
%  Exit    : Abstract exit substitution (i.e. the abstract subtitution   %
%            obtained after the analysis of the clause being considered  %
%            projected onto Hv)                                          %
%  Prime   : Abstract prime substitution (i.e. the abstract subtitution  %
%            obtained after the analysis of the clause being considered  %
%            projected onto Sv)                                          %
%  Succ    : Abstract success substitution (i.e. the abstract subtitution%
%            obtained after the analysis of the clause being considered  %
%            extended to the variables of the clause in which Sg appears)%
%  RFlag   : Flag which represents the recursive characteristics of a    %
%            predicate. It will be "nr" in case the predicate be non     % 
%            recursive. Otherwise it will be r (recursive)               %
% List     : (can be represented as OldList,List,AddList,IdList,NewList) %
%            the current list of nodes which a given node depends on.    %
% _s       : The suffix _s means that the term to which the variable is  %
%            bound to has been sorted. By default they are always sorted %
%            thus _s is added only when it appears neccessary to say it  %
%            explicitely                                                 %
% _u       : The suffix _u means that the term to which the variable is  %
%            bound is not sorted                                         %
% ExtraInfo: Info computed during the call_to_entry that can be reused   %
%            during the exit_to_prime step                               %
%   F      : Literal that originated the call (Father)                   %
%   N      : Number of specialized version of the father predicate       %
%  NewN    : Number of specialized version of this predicate             %
%   Id     : Id of the and-or graph node in analysis                     %
%------------------------------------------------------------------------%

:- doc(init_fixpoint/0,"Cleanups the database of analysis of
    temporary information.").

init_fixpoint.

:- doc(cleanup_fixpoint(AbsInt),"Cleanups the database of analysis, of both
    temporary as well as permanent information regarding abstract
    domain @var{AbsInt}.").

cleanup_fixpoint(_AbsInt).

%------------------------------------------------------------------------%
% call_to_success(+,+,+,+,+,+,+,-,-,+,+,+)                               %
% call_to_success(RFlag,SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,List,F,N,NewN) %
% It obtains the Succ for a given Sg and Call, and the List.             %
%  * If complete information for the same Sg and Call (i.e. for the same %
%    node) has been already inferred, the first clause will be used.     %
%  * else if Sg is non recursive the second clause will be used          %
%  * else if Sg is already in a fixpoint, (i.e. some parent              %
%    initiated a fixpoint with same Call and Sg) the third clause will   %
%    detect it in order not to start an infinite computation.            %
%  * else if Sg with the same Call has been already analyzed but it      %
%    depends on some other nodes whose fixpoint is not completed, and    %
%    therefore the its information is labeled as "approx" then 4th clause%
%    will be used. This clause distinguishes two cases:                  %
%     - The information on which the predicate depends on has not        %
%       been modified. Then nothing must be done.                        %
%     - The information on which the predicate depends on has been modified
%       Then the label of the register approx(Sg,Proj,Prime,Id) is       %
%       changed to fixpoint(Sg,Proj,Prime,Id) and a new fixpoint         %
%       computation is started. After the computation the register       %
%       fixpoint(Sg,Proj,Prime,Id) is changed to either                  %
%       complete(Sg,Proj,NewPrime,Id) if the list of nodes which the     %
%       predicate depends on is empty, or to                             %
%       approx(Sg,Proj,NewPrime,Id) if it is not                         %
% In order to maintain the dependencies among nodes (i.e. each recursive %
% predicate with each abstract call substitution) during the computations%
% the following things are done:                                         %
%     - any time that the approximate information (TempPrime) of a       %
%       fixpoint node changes, it updates a number in the data base      %
%       increasing in one (for example, if the node was the 3 it reads   %
%       something like ch_id(3,Num), erases it, increases Num in one     %
%       obtaining Num', and records ch_id(3,Num').                       %
%     - any time a node uses the information of another recursive        %
%       node, it reads in the data base the associated number and keeps  %
%       it in the list of nodes (for example, if the node 4 is using     %
%       information of the node 3, it reads ch_id(3,Num), and keeps 3/Num%
%       in the list of nodes).                                           %
% The way to see if the information on which the predicate depends on    %
% has been modified or not is the following:                             %
%     - the approx node depend_list is read (the list of                 %
%       node/num it depends on) and checks if the correspondent          %
%       ch_id(node,num) register exists. If this is the case, the        %
%       information has not changed. Otherwise it has changed.           %
% * Finally, if a fixpoint computation for a Sg has to be started, the   %
%   5th clause will be used. First the non recursive clauses are analyzed%
%   Then the registers fixpoint(Sg,Proj,TempPrime,Id1) and ch_id(Id1,1)  %
%   are recordered. Then fixpoint computation is started. After the      %
%   computation the register fixpoint(Sg,Proj,TempPrime,Id1) is changed  %
%   to either "complete" if the list of nodes to which the predicate     %
%   depends on is empty, or to "approx" if it is not. Also, the register %
%   ch_id(Id1,1) is erased.
%------------------------------------------------------------------------%

%% From 8 diferent clauses to 1 clause
%% From 13 Args to 7 Args
%%   call_to_success(RFlag,QKey,Call,Proj,Query,Qv,AbsInt,0,Succ,_,N,0,Id)

% call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,Succ) :-  
% 	format("Call (\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n)",
% 	[SgKey,Call,Proj,Sg,Sv,AbsInt,Succ]),
% 	 fail.

% call_to_success(_SgKey,_Call,_Proj,_Sg,_Sv,_AbsInt,_Succ) :-  
% 	format("|",[]),	inc(plai_tab_counter(inc_call,_)),
% 	fail.

call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,Succ) :-  
	my_format("\nEntry_call_to_success(
		SgKey:  ~p
		Call:   ~p
		Proj:   ~p
		Sg:     ~p
		Sv:     ~p
		AbsInt: ~p
		Succ:   ~p
                     ).\n",
	[SgKey,Call,Proj,Sg,Sv,AbsInt,Succ]),

	 call_to_success_fixpoint(SgKey,Sg,st(Sv,Call,Proj,AbsInt,Prime)),

	my_format("\nBefore each_extend Exit_call_to_success(
		SgKey:  ~p
		Sg:     ~p
		Sv:     ~p
		Call:   ~p
		Proj:   ~p
		AbsInt: ~p
		Prime:   ~p
                     ).\n",
	[SgKey,Sg,Sv,Call,Proj,AbsInt,Prime]),

	 each_extend(Sg,Prime,AbsInt,Sv,Call,Succ), % Domain call

	 my_format("\nExit_call_to_success(
	 	SgKey:  ~p
	 	Call:   ~p
	 	Proj:   ~p
	 	Sg:     ~p
	 	Sv:     ~p
	 	AbsInt: ~p
	 	Succ:   ~p
                     ).\n",
	 [SgKey,Call,Proj,Sg,Sv,AbsInt,Succ]),

	  nop(call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,Succ,Prime)).

%-------------------------------------------------------------------------
% proj_to_prime(+,+,+,+,+,+,-,+,+,+)                                     %
% proj_to_prime(SgKey,Sg,Sv,Call,Proj,AbsInt,ListPrime,F,N,Id)           %
% This predicate obtains the list of Prime corresponding to each non     %
% recursive clause of Sg for a given Call. It first reads those non      %
% recursive clauses by means of a bagof and then proccess each one with  %
% a loop. If there is no non recursive clause, the answer will be        %
% ['$bottom'].                                                           %
%-------------------------------------------------------------------------

%%%%%%%%%%%% - TCLP(ground) - %%%%%%%%%%%%%
 :- use_package(tclp_ground).
 :- table call_to_success_fixpoint(_,_,abst_lub).
nop(_).

ground_entail(abst_lub, st(V,_,ProjA,AbsInt,_), st(V,_,ProjB,AbsInt,_)) :-
% display('c'), inc(plai_tab_counter(inc_check,_)),
	% less_or_equal(AbsInt,ProjA,ProjB),
	identical_abstract(AbsInt,ProjA,ProjB),
% display('+'), inc(plai_tab_counter(inc_ok,_)),
	!.

ground_compare(abst_lub, st(V,_,_,AbsInt,PrimeAs), st(V,_,_,AbsInt,PrimeBs),1) :-
%	format("compare answer\n\t ~p \n\t+ ~p\n",[PrimeAs, PrimeBs]),
	singleton(PrimeA,PrimeAs),
	singleton(PrimeB,PrimeBs),
 	less_or_equal(AbsInt,PrimeA,PrimeB),
% display('e'), inc(plai_tab_counter(inc_ans,_)),
%	format("less or equal\n",[]),
	!.

ground_join(abst_lub,st(V,_,_,AbsInt,PrimeAs), st(V,_,_,AbsInt,PrimeBs), st(V,_,_,AbsInt,PrimeNews)) :-
%	format("wide/lub answer\n\t ~p \n\t+ ~p\n",[PrimeAs, PrimeBs]),
% display('j'), inc(plai_tab_counter(inc_join,_)),
	singleton(PrimeA,PrimeAs),
	singleton(PrimeB,PrimeBs),
	singleton(PrimeNew,PrimeNews),
	(
	    current_pp_flag(widen,on) ->
	    widen(AbsInt,PrimeA,PrimeB,PrimeNew)
	;
	    compute_lub(AbsInt,[PrimeA,PrimeB],PrimeNew)
	),
%	format("\t= ~p\n",[PrimeNews]),
	!.

ground_apply(abst_lub, st(V,_,_,Ab,A), st(V,_,_,Ab,B)) :-
	A = B.


call_to_success_fixpoint(SgKey,Sg,st(Sv,Call,Proj,AbsInt,Primes)) :-
	trans_clause(SgKey,_,Clause),
	do_nr_cl(Clause,Sg,Sv,Call,Proj,AbsInt,Primes).
call_to_success_fixpoint(SgKey,Sg,st(Sv,_Call,Proj,AbsInt,Primes)) :-
	\+ trans_clause(SgKey,_,_),
%	format("apply trusr ~p\n",[SgKey]),
	apply_trusted0(Proj,SgKey,Sg,Sv,AbsInt,_ClId,Prime),
	singleton(Prime,Primes).
%%%%%%%%%%%% - TCLP(ground) - %%%%%%%%%%%%%

do_nr_cl(Clause,Sg,Sv,Call,Proj,AbsInt,Primes):-
    Clause = clause(Head,Vars_u,K,Body),
    clause_applies(Head,Sg), !,
    varset(Head,Hv),
    sort(Vars_u,Vars),
    ord_subtract(Vars,Hv,Fv),
    process_body(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,Call,Proj,Primes,_Id).
do_nr_cl(_Clause,_Sg,_Sv,_Call,_Proj,_AbsInt,[[]]).

process_body(Body,K,AbsInt,Sg,Hv,_Fv,_,Head,Sv,Call,Proj,LPrime,_Id):- 
    Body = g(_,[],'$built'(_,true,_),'true/0',true), !,
    singleton(Prime,LPrime),
    call_to_success_fact(AbsInt,Sg,Hv,Head,K,Sv,Call,Proj,Prime,_Succ). % Domain call
process_body(Body,K,AbsInt,Sg,Hv,Fv,Vars_u,Head,Sv,_,Proj,Prime,Id):-
    call_to_entry(AbsInt,Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo), % Domain call
    singleton(Entry,LEntry),
    entry_to_exit(Body,K,LEntry,Exit,[],_,Vars_u,AbsInt,Id),
    each_exit_to_prime(Exit,AbsInt,Sg,Hv,Head,Sv,ExtraInfo,Prime).

%-------------------------------------------------------------------------
% fixpoint_compute(+,+,+,+,+,+,+,+,+,-,+,-)                              %
% fixpoint_compute(Clauses,SgKey,Sg,Sv,Call,Proj,AbsInt,LEntryInf        %
%                                       TempPrime,Prime,Id,List)         %
% It obtains the Prime for the recursive predicate Sg with Call (which   %
% has been assigned to node Id), and the list of nodes it depends on     %
% In doing this it performs an iteration over the recursive clauses of Sg%
% by calling to compute/13 and then checks if the fixpoint has been      %
% reached by calling to fixpoint/13. Fixpoint is reached if either       %
% NewList is empty (it means that Id does not depend on any node) or if  %
% Flag is a variable (it means that the information has not been         %
% modified within the iteration)                                         %
% LEntryInf is the list of (Entry,ExtraInfo) couples for each Clause. It %
% will be computed in the first iteration and used in subsequent ones    %
%-------------------------------------------------------------------------


%-------------------------------------------------------------------------
% entry_to_exit(+,+,+,-,+,-,+,+,+)                                       %
% entry_to_exit(Body,Key,Call,Exit,OldList,NewList,Vars_u,AbsInt,NewN)   %
% Traverses the body of a clause (first argument) obtaining the Exit for %
% a given Entry (represented by Call, since it is both the Entry of the  %
% clause and the Call for the first subgoal). Also it obtains the list of%
% nodes whose information has been used during the analysis of the clause%
%-------------------------------------------------------------------------

entry_to_exit((Sg,Rest),K,Call,Exit,OldList,NewList,Vars_u,AbsInt,NewN):- !,
    body_succ(Call,Sg,Succ,OldList,IntList,Vars_u,AbsInt,K,NewN,_),
    entry_to_exit(Rest,K,Succ,Exit,IntList,NewList,Vars_u,AbsInt,NewN).
entry_to_exit(true,_,Call,Call,List,List,_,_,_):- !.
%entry_to_exit(g(_,[],'$built'(_,true,_),'true/0',true),_,Call,Call,List,List,_,_,_):- !.
entry_to_exit(Sg,Key,Call,Exit,OldList,NewList,Vars_u,AbsInt,NewN):- 
    body_succ(Call,Sg,Exit,OldList,NewList,Vars_u,AbsInt,Key,NewN,_),
    true.

%-------------------------------------------------------------------------
% body_succ(+,+,-,+,-,+,+,+,+,-)                                         %
% body_succ(Call,Atom,Succ,List,NewList,HvFv,AbsInt,ClId,ParentId,ChildId)
% Atom has the form [Key,Sv,(I1,I2,Sg)]                                  %
% First, the lub between the abstract call substitution and the already  %
% computed information for this program point (if any) is computed. Then %
% the lub is recordered.                                                 %
% If the abstract call substitution is bottom (case handled by the first %
% clause) the success abstract substitution is also bottom and nothing   %
% more is needed. Otherwise (second clause) the computation of the       %
% success abstract substitution procceeds.                               %
%-------------------------------------------------------------------------

% body_succ(Call,Atom,Succ,List,List,HvFv_u,AbsInt,_ClId,ParentId,N):-
% 	format("\nBody_succ(\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n\t~p\n",
% 	[Call,Atom,Succ,List,List,HvFv_u,AbsInt,_ClId,ParentId,N]),fail.

body_succ(Call,_Atom,Succ,List,List,_HvFv_u,_AbsInt,_ClId,_ParentId,no):-
    bottom(Call), !,
    Succ = Call.
body_succ(Call,Atom,Succ,List,NewList,HvFv_u,AbsInt,ClId,ParentId,Id):- 
    Atom=g(Key,Sv,Info,SgKey,Sg),
    body_succ_(Info,SgKey,Sg,Sv,HvFv_u,Call,Succ,List,NewList,AbsInt,
               ClId,Key,ParentId,Id).

body_succ_(Info,SgKey,Sg,Sv,HFv,Call,Succ,L,NewL,AbsInt,ClId,Key,PId,Id):-
    Info = [_|_], !,
    split_combined_domain(AbsInt,Call,Calls,Domains), % Domain call
    map_body_succ(Info,SgKey,Sg,Sv,HFv,Calls,Succs,L,NewL,Domains,
                  ClId,Key,PId,Id),
    split_combined_domain(AbsInt,Succ,Succs,Domains).
body_succ_(Info,SgKey,Sg,Sv,HFv,Call,Succ,L,NewL,AbsInt,ClId,Key,PId,Id):-
    body_succ0(Info,SgKey,Sg,Sv,HFv,Call,Succ,L,NewL,AbsInt,
               ClId,Key,PId,Id).

% L=NewL and Id=no is not quite correct!!!
map_body_succ([],_SgKey,_Sg,_Sv,_HFv,[],[],L,L,[],_ClId,_Key,_PId,no).
map_body_succ([I|Info],SgKey,Sg,Sv,HFv,[Call|Calls],[Succ|Succs],L,NewL,
          [AbsInt|Domains],ClId,Key,PId,Id):-
    body_succ0(I,SgKey,Sg,Sv,HFv,Call,Succ,L,_NewL,AbsInt,
               ClId,Key,PId,_Id), !,
    map_body_succ(Info,SgKey,Sg,Sv,HFv,Calls,Succs,L,NewL,Domains,
               ClId,Key,PId,Id).

%-------------------------------------------------------------------------
% body_succ0(+,+,+,+,+,+,-,+,-,+,+,+,-)                                  %
% body_succ0(RFlag,SgKey,Sg,Sv,HvFv,Call,Succ,List0,List,AbsInt,F,NewN,Id)%
% This predicate handles the special cases of the subgoals, i.e. when    %
% the subgoal is a builtin (also when it is a constraint since they are) %
% internally represented as builtins). Otherwise, computation proceeds.  %
%-------------------------------------------------------------------------

body_succ0('$var',SgKey,Sg,_Sv_u,HvFv_u,Calls,Succs,List0,List,AbsInt,
        	_ClId,_F,_N,_Id):-
%        format("enter body01\n",[]),
    !,
    ( Calls=[Call],
      concrete(AbsInt,Sg,Call,Concretes),
      concretes_to_body(Concretes,SgKey,AbsInt,B)
    -> meta_call(B,HvFv_u,Calls,[],Succs,List0,List,AbsInt,_ClId,_Id,_Ids)
    ;  List=List0,
       each_unknown_call(Calls,AbsInt,Sg,[Sg],Succs) % Sg is a variable % TODO: use call(Sg) or similar? (JF)
    ).
body_succ0('$meta'(T,B,_),SgKey,Sg,Sv_u,HvFv_u,Call,Succ,List0,List,AbsInt,
	    _ClId,_F,_N,_Id):-
 %       format("enter body02\n",[]),
    !,
    meta_call(B,HvFv_u,Call,[],Exits,List0,List,AbsInt,_ClId,_Id,_Ids),
    ( body_succ_meta(T,AbsInt,Sv_u,HvFv_u,Call,Exits,Succ) ->
        true
    ; % for the trusts, if any:
        varset(Sg,Sv_r), % Sv_u contains extra vars (from meta-term)
        % which will confuse apply_trusted
        body_succ0(nr,SgKey,Sg,Sv_r,HvFv_u,Call,Succ,[],_List,AbsInt,
        _ClId,_F,_N,_Id0)  % TODO: Why forced nr? Can this make the fixpoint not to finish?
    ).
body_succ0('$built'(T,Tg,Vs),SgKey,Sg,Sv_u,HvFv_u,Call,Succ,List0,List,AbsInt,
	    _ClId,_F,_N,_Id):-
%        format("enter body03\n",[]),
    !,
    List=List0,
    sort(Sv_u,Sv),
    each_body_succ_builtin_(Call,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,Succ).
body_succ0(_RFlag,SgKey,Sg,Sv_u,HvFv_u,Call,Succ,_List0,_List,AbsInt,
	   _ClId,_F,_N,_Id):-
%        format("enter body04\n",[]),
    sort(Sv_u,Sv),
    each_call_to_success(Call,SgKey,Sg,Sv,HvFv_u,AbsInt,Succ).

% % % % :- table each_body_succ_builtin_tabling/10.
% each_body_succ_builtin_tabling(Call,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,Succ):-
% 	each_body_succ_builtin_(Call,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,Succ).

%% New predicate from fixpo_ops
each_body_succ_builtin_([],_,_T,_Tg,_,_,_Sg,_Sv,_HvFv_u,[]).
each_body_succ_builtin_([Call|Calls],AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,[Succ|Succs]):-
    project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
    
    body_succ_builtin(T,AbsInt,Tg,Vs,Sv,HvFv_u,Call,Proj,Succ),!, %% Doamin call
    
    %	format("\nCalling builtin with\n T = ~p\n AbsInt = ~p\n Tg = ~p\n Vs = ~p\n Sv = ~p\n HvFv_u = ~p\n Call = ~p\n Proj = ~p\n Succ = ~p\n",[T,AbsInt,Tg,Vs,Sv,HvFv_u,Call,Proj,Succ]),
    
    each_body_succ_builtin_(Calls,AbsInt,T,Tg,Vs,SgKey,Sg,Sv,HvFv_u,Succs).





each_call_to_success([Call],SgKey,Sg,Sv,HvFv_u,AbsInt,Succ):-
    !,
    project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
    my_format("\nenter_1\n",[]),
    call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,Succ),
    my_format("\nexit_1\n",[]).

each_call_to_success(LCall,SgKey,Sg,Sv,HvFv_u,AbsInt,LSucc):-
    each_call_to_success0(LCall,SgKey,Sg,Sv,HvFv_u,AbsInt,
                              LSucc).

each_call_to_success0([],_SgK,_Sg,_Sv,_HvFv,_AbsInt,[]).
each_call_to_success0([Call|LCall],SgKey,Sg,Sv,HvFv_u,AbsInt,LSucc):-
    project(AbsInt,Sg,Sv,HvFv_u,Call,Proj),
    my_format("\nenter_2\n",[]),
    call_to_success(SgKey,Call,Proj,Sg,Sv,AbsInt,LSucc0),
    my_format("\nexit_2\n",[]),
    append(LSucc0,LSucc1,LSucc),
    each_call_to_success0(LCall,SgKey,Sg,Sv,HvFv_u,AbsInt,LSucc1).

%GP if the list of Bodies is empty, then there is nothing to analyze 
%   and we can make Succ = Call. Some more thinking is welcome
meta_call([],_HvFv_u,Call,[],Call,List,List,_AbsInt,_ClId,_Id,[]).
meta_call([Body|Bodies],HvFv_u,Call,Succ0,Succ,L0,List,AbsInt,ClId,Id,Ids):-
    meta_call_([Body|Bodies],HvFv_u,Call,Succ0,Succ,L0,List,AbsInt,ClId,Id,Ids).

meta_call_([Body|Bodies],HvFv_u,Call,Succ0,Succ,L0,List,AbsInt,ClId,Id,Ids):-
    meta_call_body(Body,ClId,Call,Succ1,L0,L1,HvFv_u,AbsInt,Id,Ids0),
%       widen_succ(AbsInt,Succ0,Succ1,Succ2),
    append(Succ0,Succ1,Succ2),
    append(Ids0,Ids1,Ids),
    meta_call_(Bodies,HvFv_u,Call,Succ2,Succ,L1,List,AbsInt,ClId,Id,Ids1).
meta_call_([],_HvFv_u,_Call,Succ,Succ,List,List,_AbsInt,_ClId,_Id,[]).

meta_call_body((Sg,Rest),K,Call,Exit,OldList,NewList,Vars_u,AbsInt,PId,CIds):-
    !,
    CIds=[Id|Ids],
    body_succ(Call,Sg,Succ,OldList,IntList,Vars_u,AbsInt,K,PId,Id),
    meta_call_body(Rest,K,Succ,Exit,IntList,NewList,Vars_u,AbsInt,PId,Ids).
meta_call_body(true,_,Call,Call,List,List,_,_,_,[no]):- !.
meta_call_body(Sg,Key,Call,Exit,OldList,NewList,Vars_u,AbsInt,PId,[Id]):- 
    body_succ(Call,Sg,Exit,OldList,NewList,Vars_u,AbsInt,Key,PId,Id).

concretes_to_body([],_SgKey,_AbsInt,[]).
concretes_to_body([Sg|Sgs],SgKey,AbsInt,[B|Bs]):-
    % have to module-expand Sg!!!!
    body_info0(Sg:SgKey,[],AbsInt,B),
    concretes_to_body(Sgs,SgKey,AbsInt,Bs).

%-------------------------------------------------------------------------
% query(+,+,+,+,+,+,+,-)
%-------------------------------------------------------------------------

:- doc(query(AbsInt,QKey,Query,Qv,RFlag,N,Call,Succ),
    "The success pattern of @var{Query} with @var{Call} is
     @var{Succ} in the analysis domain @var{AbsInt}. The predicate
     called is identified by @var{QKey}, and @var{RFlag} says if it
     is recursive or not. The goal @var{Query} has variables @var{Qv},
     and the call pattern is uniquely identified by @var{N}.").

:- use_module(engine(runtime_control)).
:- data plai_tab_time/1, plai_tab_counter/2.
:- export(plai_tab_time/1).
:- export(plai_tab_counter/2).

query(AbsInt,QKey,Query,Qv,_RFlag,_N,Call,Succ) :-
    init_counters,
    
    format("Query \t ~p\t~p\n", [QKey,Call]),
    
%%	set_pp_flag(type_eval,on),
    
    statistics(runtime,_),
    project(AbsInt,Query,Qv,Qv,Call,Proj), % Domain call
    call_to_success(QKey,Call,Proj,Query,Qv,AbsInt,Succ), 
    statistics(runtime,[_,T]),
    assertz_fact(plai_tab_time(T)),
    
    format("   -> \t ~p\n TIME = ~2f\n",	[Succ,T]),
    !.

query(_AbsInt,_QKey,_Query,_Qv,_RFlag,_N,_Call,_Succ):-
% should never happen, but...
    error_message("SOMETHING HAS FAILED!").


init_counters:-
    retractall_fact(plai_tab_counter(_,_)),
    assertz_fact(plai_tab_counter(inc_ans,0)),
    assertz_fact(plai_tab_counter(inc_join,0)),
    assertz_fact(plai_tab_counter(inc_call,0)),
    assertz_fact(plai_tab_counter(inc_check,0)),
    assertz_fact(plai_tab_counter(inc_ok,0)).

inc(plai_tab_counter(Counter,_)) :-
    plai_tab_counter(Counter,Value),
    retract_fact(plai_tab_counter(Counter,Value)),
    Value1 is Value + 1,
    assertz_fact(plai_tab_counter(Counter,Value1)).