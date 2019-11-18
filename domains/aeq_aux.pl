/*             Copyright (C)1990-91-92-93-94-95 UPM-CLIP                */
/*                          1994-1995 Katholieke Universiteit Leuven.        */

% This file contains the auxiliary procedures for the
% abstract equation systems analyser developed at KULeuven

%------------------------------------------------------------------------%
% This file was initially implemented by KULeuven. It has been modified 
% by Maria Garcia de la Banda in 1996 in order to include comments (so
% that future modifications become easier), to tailor it more closely to
% PLAI, and to add the abstract functions required for dynamic scheduling
%------------------------------------------------------------------------%

:- use_package(datafacts).
:- use_module(library(lists), [member/2]).
:- use_module(domain(share_aux), [if_not_nil/4]).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following are the default values for the system, i.e., set-sharing
% and depth 1 imposed at the end of each unification since the second 
% argument of aeq_depth_bound which indicates the type of depth, is set 
% to solve rather than to 'project' (which would impose the depth only at 
% call_to_entry). 
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).

:- data aeq_current_sharing/1, aeq_current_bound/2.

% aeq_allowed_sharing(set).
% aeq_allowed_sharing(pair).

aeq_current_sharing(set).

% aeq_allowed_bound(solve).
% aeq_allowed_bound(project).

%aeq_current_bound(1,solve).    
%aeq_current_bound(0,solve).    
%aeq_current_bound(0,project).  

current_bound(D,T):- aeq_current_bound(D,T), !.
current_bound(D,project):-
    current_pp_flag(depth,K),
    D is K-1.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following are the predicates to change the system parameters 
% They should be included in topdriver.pl
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%% aeq_depth(D) :-
%%      integer(D),D >= 0,
%%      retract_fact(aeq_current_bound(_,Type)),
%%      asserta_fact(aeq_current_bound(D,Type)).
%% 
%% aeq_depth_star(D) :-
%%      integer(D), D >= 0,
%%      retract_fact(aeq_current_bound(_,_)),
%%      asserta_fact(aeq_current_bound(D,project)).
%% 
%% aeq_version(Shr,Depth) :-
%%      integer(Depth), Depth >= 0,
%%      retract_fact(aeq_current_bound(_,Type)),
%%      asserta_fact(aeq_current_bound(Depth,Type)),
%%      aeq_allowed_sharing(Shr),
%%      retract_fact(aeq_current_sharing(_)),
%%      asserta_fact(aeq_current_sharing(Shr)).
%% 
%% aeq_version_star(Shr,Depth) :-
%%      integer(Depth), Depth >= 0,
%%      retract_fact(aeq_current_bound(_,_)),
%%      asserta_fact(aeq_current_bound(Depth,project)),
%%      aeq_allowed_sharing(Shr),
%%      retract_fact(aeq_current_sharing(_)),
%%      asserta_fact(aeq_current_sharing(Shr)).

% This used to work... 8-(
aeq_pair_sharing:- fail.

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following are error and warning messages. They should be included 
% in topdriver.pl
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%% :- mode aeq_warning(+,+) .
aeq_warning(empty_shr,_) :- 
    warning_message("Input Aeq: Empty sharing group removed.",[]).
aeq_warning(builtin_undef,Key) :- 
    warning_message("Analyser Aeq: interpretation of a not defined builtin ~w",[Key]).

aeq_error(redAVars_shr,H) :- 
    error_message("Input Aeq: Sharing group with redundant AVar(s) ~w",[H]),
    abort .
aeq_error(bad_entry,_):-
    warning_message("Bad module or entry declaration found: no analysis performed").

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following are the predicates needed to collect the bitcodes of the
% variables (both abstract or not) which appear in a term. They do not
% depend on the particular annotation set.
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% avar(+)
% avar(AVar)
%------------------------------------------------------------------------%
% Satisfied if AVar is an abstract variable
%------------------------------------------------------------------------%

% avar('@'(_)).

%------------------------------------------------------------------------%
% avar_ic(+,-)
% avar_ic(AVar,AVar_ic)
%------------------------------------------------------------------------%
% Satisfied if AVar is an abstract variable and AVar_ic is its bitcode
%------------------------------------------------------------------------%

avar_ic('@'(AVar),AVar_ic) :- 
    AVar_ic is 1 << AVar .          

%------------------------------------------------------------------------%
% avariables_ic_subst(+,+,-)
% avariables_ic_subst(Term,Eqs_sf,AVarSet_ic) 
%------------------------------------------------------------------------%
% For each abstract variable in Term and for variable X in Term whose
% corresponding abstract term ATerm in Eqs_sf contains abstract variables,
% the bitcode of those abstract variables is added (union) to AVarSet_ic.
%------------------------------------------------------------------------%
avariables_ic_subst(Term,Eqs_sf,AVarSet_ic) :-
    avariables_ic_subst(Term,Eqs_sf,0,AVarSet_ic).

avariables_ic_subst(Term,Eqs_sf,SoFar,AVarSet_ic) :-
    var(Term),!,
    member_key(Term,Eqs_sf,ATerm),
    avariables_ic(ATerm, AVar_ic),
    AVarSet_ic is AVar_ic \/ SoFar.
avariables_ic_subst(Term,_Eqs_sf,AVarSet_ic,AVarSet_ic) :-
    atomic(Term),!.
avariables_ic_subst('@'(Num),_Eqs_sf,SoFar,AVarSet_ic) :- !,
    Num_ic is 1 << Num,
    AVarSet_ic is Num_ic \/ SoFar.
avariables_ic_subst([H|T],Eqs_sf,SoFar,VarSet_ic) :- !,
    avariables_ic_subst(H,Eqs_sf,SoFar,Accum),
    avariables_ic_subst(T,Eqs_sf,Accum,VarSet_ic).
avariables_ic_subst(Term,Eqs_sf,SoFar,VarSet_ic) :-
    functor(Term,_,Arity),
    avariables_ic_subst(Arity,Term,Eqs_sf,SoFar,VarSet_ic).

avariables_ic_subst(0,_,_,AVarSet_ic,AVarSet_ic):- !.
avariables_ic_subst(Arity,Term,Eqs_sf,SoFar,AVarSet_ic):-
    arg(Arity,Term,Arg),
    avariables_ic_subst(Arg,Eqs_sf,SoFar,SoFar0),
    Arity0 is Arity - 1,
    avariables_ic_subst(Arity0,Term,Eqs_sf,SoFar0,AVarSet_ic).

member_key(X,[Y=A|_],A) :- 
    X == Y, !.
member_key(X,[_|Ys],A) :- 
    member_key(X,Ys,A).

%------------------------------------------------------------------------%
% avariables_ic(+,-)
% avariables_ic(Term,AVarSet_ic)
%------------------------------------------------------------------------%
% For each abstract variable @(Num) in Term, the bitcode of Num is added
% (union) to AVarSet_ic.
%------------------------------------------------------------------------%
avariables_ic(Term,AVarSet_ic) :-
    avariables_ic(Term,0,AVarSet_ic).

avariables_ic(Term,AVarSet_ic,AVarSet_ic) :-
    (atomic(Term) ; var(Term)), !.
avariables_ic('@'(Num),SoFar,AVarSet_ic) :- !,
    Num_ic is 1 << Num,
    AVarSet_ic is Num_ic \/ SoFar.
avariables_ic([H|T],SoFar,VarSet_ic) :- !,
    avariables_ic(H,SoFar,Accum),
    avariables_ic(T,Accum,VarSet_ic).
avariables_ic(Term,SoFar,AVarSet_ic) :-
    functor(Term,_,Arity),
    avariables_ic(Arity,Term,SoFar,AVarSet_ic).

avariables_ic(0,_,AVarSet_ic,AVarSet_ic):- !.
avariables_ic(Arity,Term,SoFar,AVarSet_ic):-
    arg(Arity,Term,Arg),
    avariables_ic(Arg,SoFar,SoFar0),
    Arity0 is Arity - 1,
    avariables_ic(Arity0,Term,SoFar0,AVarSet_ic).

%------------------------------------------------------------------------%
% avariables_ec(+,-)
% avariables_ec(Term,AVarSet_ec)
%------------------------------------------------------------------------%
% For each abstract variable @(Num) in Term, Num is added to AVarSet_ec,
% which is finally sorted.
%------------------------------------------------------------------------%
avariables_ec(Term,AVarSet_ec) :-
    avariables_ec(Term,AVarSet_ec_u,[]),
    sort(AVarSet_ec_u,AVarSet_ec).

avariables_ec(Term,AVarSet_ec,Tail) :-
    (atomic(Term) ; var(Term)), !,
    AVarSet_ec = Tail.
avariables_ec('@'(AVar_ec),[AVar_ec|Tail],Tail) :- !.
avariables_ec([H|T],AVarSet_ec,Tail) :- !,
    avariables_ec(H,AVarSet_ec,Tail1),
    avariables_ec(T,Tail1,Tail).
avariables_ec(Term,AVarSet_ec,Tail) :-
    functor(Term,_,Arity),
    avariables_ec(Arity,Term,AVarSet_ec,Tail).

avariables_ec(0,_,AVarSet_ec,AVarSet_ec):- !.
avariables_ec(Arity,Term,AVarSet_ec,Tail):-
    arg(Arity,Term,Arg),
    avariables_ec(Arg,AVarSet_ec,Tail1),
    Arity0 is Arity - 1,
    avariables_ec(Arity0,Term,Tail1,Tail).
                            
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following are the predicates needed to transform internal and 
% external representations of abstract substitutions into each other.
% They have to change of the annotation set changes.
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% aeq_input_to_extern(+,+,-,-,-)
% aeq_input_to_extern(InputUser,Qv,AEqs,Ann,Shr)
%------------------------------------------------------------------------%
% Transforms the user information into an external aeqs representation
% aeqs(Eqs,Ann,Shr)
%------------------------------------------------------------------------%

aeq_input_to_extern((Sh,Eqs_u,Lin_u,Free_u),Qv,AEqs,Ann,Shr):-
    sort(Eqs_u,Eqs),
    eqs_ranges(Qv,Eqs,Terms,Vars,[],AVarSet),
    copy_term(t(Terms,AVarSet),t(ATerms,AtVarSet)),
    aeq_unify_avar(AtVarSet,0),
    keys_and_values(Qv,ATerms,AEqs),
    copy_term(t(Vars,AVarSet),t(AVars,NumVarSet)),
    aeq_unify_num(NumVarSet,0),
    keys_and_values(Qv,AVars,Pairs),
%
    share_input_user_interface(Sh,Qv,ShASub,sg_not_provided,no),
    copy_term(t(ShASub,Pairs),t(Share0,Pairs_sh)),
    apply(Pairs_sh),
    flatten_lists(Share0,Share1),
    share_project(not_provided_Sg,NumVarSet,not_provided_HvFv_u,Share1,Share2),
    share_abs_sort(Share2,Shr),
%
    aeq_input_to_annot(Lin_u,Pairs,l,Ann_u,Ann0),
    aeq_input_to_annot(Free_u,Pairs,f,Ann0,Ann1),
%
    varset(ShASub,Vars_sh),
    ord_subtract(Qv,Vars_sh,Gv),
    aeq_input_to_annot(Gv,Pairs,g,Ann1,Ann2),
%
    sort(Lin_u,Lin),
    ord_subtract(Vars_sh,Lin,Vars_a0),
    sort(Free_u,Free),
    ord_subtract(Vars_a0,Free,Vars_a),
    aeq_input_to_annot(Vars_a,Pairs,a,Ann2,[]),
    sort(Ann_u,Ann).
       
eqs_ranges([X|Dom],Eqs,[Term|Terms],[Vars0|Vars],VarSet0,VarSet):-
    key_lookup(X,Eqs,Term,Eqs0), !,
    varset(Term,Vars0),
    merge(VarSet0,Vars0,VarSet1),
    eqs_ranges(Dom,Eqs0,Terms,Vars,VarSet1,VarSet).
eqs_ranges([_|Dom],Eqs,[Y|Terms],[[Y]|Vars],VarSet0,VarSet):-
    insert(VarSet0,Y,VarSet1),
    eqs_ranges(Dom,Eqs,Terms,Vars,VarSet1,VarSet).
eqs_ranges([],[],[],[],VarSet,VarSet).

aeq_unify_avar(['@'(N)|VarSet],N):-
    N1 is N+1,
    aeq_unify_avar(VarSet,N1).
aeq_unify_avar([],_N).

aeq_unify_num([N|VarSet],N):-
    N1 is N+1,
    aeq_unify_num(VarSet,N1).
aeq_unify_num([],_N).

aeq_input_to_annot(List,Pairs,Flag,Ann,TailAnn):-
    copy_term(t(List,Pairs),t(List0,Pairs0)),
    apply(Pairs0),
    flatten(List0,List1),
    aeq_annotations(List1,Flag,Ann,TailAnn).

aeq_annotations([X|Xs],Flag,[X-Flag|Ann],TailAnn):-
    aeq_annotations(Xs,Flag,Ann,TailAnn).
aeq_annotations([],_Flag,Ann,Ann).

%% % now imported (PBC)
%% flatten(Xs,Ys) :- flatten(Xs,Ys,[]).
%% 
%% flatten([], Xs, Xs).
%% 
%% flatten([X|Xs],Ys,Zs) :-
%%         flatten(X,Ys,Ys1),
%%         flatten(Xs,Ys1,Zs).
%% 
%% flatten(X, [X|Xs], Xs) :-
%%         atomic(X), X \== [].

flatten_lists([L|List],[Flat|Flats]):-
    flatten(L,Flat),
    flatten_lists(List,Flats).
flatten_lists([],[]).

%------------------------------------------------------------------------%
% aeq_intern_to_extern(+,-)
% aeq_intern_to_extern(ASub_ic,ASub_ec).
%------------------------------------------------------------------------%
% Transforms the internal ASub into an external one.
%------------------------------------------------------------------------%
aeq_intern_to_extern('$bottom','$bottom') .
aeq_intern_to_extern(ac(ACons,Flag),(Output,Flag)):-
    aeq_intern_to_extern(ACons,Output).
aeq_intern_to_extern(d(AEqs,Del),Output):-
    aeq_intern_to_extern(AEqs,Out),
    del_output(Del,Out,Output).
aeq_intern_to_extern(aeqs(Eqs_ec,Ann_ic,Shr_ic,_,_),
                 aeqs(Eqs_ec,Ann_ec,Shr_ec)) :-
    array_to_list(Ann_ic,Ann_ec),
    lbitcode_to_llist(Shr_ic,Shr_ec0),
    sort_sh_ex(Shr_ec0,Shr_ec).

sort_sh_ex(ps(X_u,Y_u),ps(X,Y)):- !,
    sort(X_u,X),
    share_abs_sort(Y_u,Y).
sort_sh_ex(X_u,X):- 
    share_abs_sort(X_u,X).

%------------------------------------------------------------------------%
% aeq_extern_to_output(+,-)
% aeq_extern_to_output(Extern,OutputUser)
%------------------------------------------------------------------------%
% Transforms the external aeqs representation aeqs(Eqs,Ann,Shr) into
% user information
%------------------------------------------------------------------------%
% fail: aeq_extern_to_output('$bottom',[solutions(0)]):- !.
aeq_extern_to_output((ACons,Flag),[flag(Flag)|Output]):- 
    Flag = g(_,_,_), !,
    aeq_extern_to_output(ACons,Output).
%% aeq_extern_to_output((ACons,g(_,_,_)),Output):- !,
%%      aeq_extern_to_output(ACons,Output).
aeq_extern_to_output((aeqs(AEqs,Ann,Shr),Del),OutputUser):- !,
    aeq_extern_to_output(aeqs(AEqs,Ann,Shr),OutputUser0),
    OutputUser=[del(Del)|OutputUser0].
aeq_extern_to_output(aeqs(AEqs,Ann,Shr),OutputUser):- !,
    aeq_substitute_vars(AEqs,AEqs,p(Ann,Shr),AEqs0,p(Ann0,Shr0)),
    ann_to_output(Ann0,F_u,G_u,L_u,NG_u,NF_u,Dic),
    key_rename_eqs(AEqs0,Dic,Eqs_u),
    key_rename_list_of_lists(Shr0,Dic,Share_u),
    sort(F_u,F),
    sort(G_u,G),
    sort(L_u,L),
    sort(NG_u,NG),
    sort(NF_u,NF),
    sort(Eqs_u,Eqs),
    share_abs_sort(Share_u,Share),
    support_user_interface([ground(G),sharing(Share),free(F),linear(L),
                            not_ground(NG),not_free(NF)],OutputUser0),
    append(Eqs,OutputUser0,OutputUser).
% fail: aeq_extern_to_output(Extern,Extern).

support_user_interface([],[]).
support_user_interface([P|Props],Output):-
    arg(1,P,L),
    if_not_nil(L,P,Output,Output1),
    support_user_interface(Props,Output1).

aeq_substitute_vars([],Eqs,Term,Eqs,Term).
aeq_substitute_vars([X=ATerm|AEqs],Eqs0,Term0,Eqs,Term):-
    ( ATerm = '@'(AVar) ->
    aeq_substitute_myavar(Eqs0,ATerm,X,Eqs1),
    aeq_substitute_myavar(Term0,AVar,X,Term1)
    ;   Eqs1 = Eqs0,
    Term1 = Term0),
    aeq_substitute_vars(AEqs,Eqs1,Term1,Eqs,Term).

ann_to_output([N-A|Ann],F,G,L,NG,NF,Dic):-
    ( number(N) ->
        Dic = [N=X|Dic1],
        flag_to_set(A,X,F,G,L,NG,NF,FT,GT,LT,NGT,NFT)
    ;    Dic = Dic1,
        flag_to_set(A,N,F,G,L,NG,NF,FT,GT,LT,NGT,NFT)),
    ann_to_output(Ann,FT,GT,LT,NGT,NFT,Dic1).
ann_to_output([],[],[],[],[],[],[]).

flag_to_set(a,_,F,G,L,NG,NF,F,G,L,NG,NF).
flag_to_set(f,X,[X|F],G,L,NG,NF,F,G,L,NG,NF).
flag_to_set(g,X,F,[X|G],L,NG,NF,F,G,L,NG,NF).
flag_to_set(l,X,F,G,[X|L],NG,NF,F,G,L,NG,NF).
flag_to_set(lng,X,F,G,[X|L],[X|NG],NF,F,G,L,NG,NF).
flag_to_set(lnf,X,F,G,[X|L],NG,[X|NF],F,G,L,NG,NF).
flag_to_set(lngf,X,F,G,[X|L],[X|NG],[X|NF],F,G,L,NG,NF).
flag_to_set(ng,X,F,G,L,[X|NG],NF,F,G,L,NG,NF).
flag_to_set(nf,X,F,G,L,NG,[X|NF],F,G,L,NG,NF).
flag_to_set(ngf,X,F,G,L,[X|NG],[X|NF],F,G,L,NG,NF).

key_rename_eqs([X=ATerm|AEqs],Dic,Eqs):-
    ( X == ATerm ->
        Eqs1 = Eqs
    ; key_rename_term(ATerm,Dic,Term),
      Eqs = [X=Term|Eqs1]),
    key_rename_eqs(AEqs,Dic,Eqs1).
key_rename_eqs([],_Dic,[]).

key_rename_term('@'(X),Dic,Term):- !,
    key_lookup(X,Dic,Term,_).
key_rename_term([],_,[]):- !.
key_rename_term([X|Xs],Dic,[Name|Names]):- !,
    key_rename_term(X,Dic,Name),          
    key_rename_term(Xs,Dic,Names).
key_rename_term(X,Dic,Term):-
    X=..[F|Args],
    key_rename_term(Args,Dic,Names),
    Term=..[F|Names].

key_rename_list([X|Xs],Dic,Ys):-
    ( number(X) ->
        key_lookup(X,Dic,Y,Dic0),
        Ys = [Y|Ys1]
    ;   Dic0 = Dic, 
        Ys = [X|Ys1]),
    key_rename_list(Xs,Dic0,Ys1).
key_rename_list([],_Dic,[]).

key_rename_list_of_lists([X|Xs],Dic,[Y|Ys]):-
    key_rename_list(X,Dic,Y),
    key_rename_list_of_lists(Xs,Dic,Ys).
key_rename_list_of_lists([],_Dic,[]).

%------------------------------------------------------------------------%
% aeq_extern_to_intern(+,-)
% aeq_extern_to_intern(ASub_ec,ASub_ic)
%------------------------------------------------------------------------%
% Transforms the external ASub in an internal one. The code requires the
% user to provide annotations for all abstract variables in Ann_ec (i.e.,
% those obtained in AVarSet_ic).
%------------------------------------------------------------------------%

aeq_extern_to_intern(Eqs_ec,Ann_ec,Shr_ec,aeqs(Eqs_ec,Ann_ic,Shr_ic,AVarSet_ic,NonGr_ic)) :-
    avariables_ic(Eqs_ec,AVarSet_ic),
    (aeq_current_sharing(pair) ->
      Shr_ic = ps(InShr_ic,ExShr_ic),
      encode_and_check_shrP(Shr_ec,AVarSet_ic,[],ExShr_ic,0,NonGr_ic),
      encode_and_check_annP(Ann_ec,AVarSet_ic,NonGr_ic,Ann_ic,0,InShr_ic)
    ; encode_and_check_shr(Shr_ec,AVarSet_ic,Shr_ic,0,NonGr_ic),
      encode_and_check_ann(Ann_ec,AVarSet_ic,NonGr_ic,Ann_ic)
    ) .

%------------------------------------------------------------------------%
% encode_and_check_shrP(+,+,+,-,+,-)
% encode_and_check_shrP(Shr_ec,AVarSet_ic,ExShr,ExShr,NonGr,NonGr).
%------------------------------------------------------------------------%
% For each non-empty set H in Shr_ec, it obtains its bitcode, checks that
% it is a subset of the abstract variables appearing in the equations
% given by the user, adds it to Accum since it is not a ground variable,
% and then transforms H into the set of the bitcode of each of its 
% pairs (transforms set-sharing into pair-sharing).
%------------------------------------------------------------------------%
encode_and_check_shrP([],_,Shr,Shr,NonGr,NonGr).
encode_and_check_shrP([H|T],AVarSet_ic,ExShr_i,ExShr_o,Sofar,NonGr) :- !,
    ( H = [] ->
        aeq_warning(empty_shr,_),
        ExShr_m = ExShr_i,
        Accum = Sofar
    ;  set_to_bitcode(H,H_ic),
       ( H_ic is H_ic /\ AVarSet_ic  ->
           true
       ;   aeq_error(redAVars_shr,H)),
       Accum is Sofar \/ H_ic,
       aeq_add_pairs(H,ExShr_i,ExShr_m)
       ),
    encode_and_check_shrP(T,AVarSet_ic,ExShr_m,ExShr_o,Accum,NonGr).

%------------------------------------------------------------------------%
% encode_and_check_shr(+,+,+,-,+,-)
% encode_and_check_shr(Shr_ec,AVarSet_ic,Shr_ic,AccGr,NonGr).
%------------------------------------------------------------------------%
% Similar to the one above but for set-sharing (the pairs obtained above
% from H are not needed).
%------------------------------------------------------------------------%

encode_and_check_shr([],_AVarSet_ic,[],NonGr,NonGr).
encode_and_check_shr([H|T],AVarSet_ic,Shr_ic,Sofar,NonGr) :- 
    ( H = [] ->
        aeq_warning(empty_shr,_),
        Shr_ic = Tail,
        Accum = Sofar
    ;  set_to_bitcode(H,H_ic),
       ( H_ic is H_ic /\ AVarSet_ic  ->
           true
       ;   aeq_error(redAVars_shr,H)),
       Shr_ic = [H_ic|Tail],
       Accum is Sofar \/ H_ic,
       encode_and_check_shr(T,AVarSet_ic,Tail,Accum,NonGr)).

%------------------------------------------------------------------------%
% encode_and_check_annP(+,+,+,-,+,-)
% encode_and_check_annP(Ann_ec,AVarSet_ic,NonGr_ic,Ann_ic,InShr_i,InShr_o)
%------------------------------------------------------------------------%
% Transforms an external annotation (list of Num-Ann) into an internal one
% (array of bitcodes), checking that (a) the annotations are consistent with
% the rest of annotations and with the pair-sharing and (b) there are 
% annotations for all abstract variables. 
%------------------------------------------------------------------------%
encode_and_check_annP(Ann_ec,AVarSet_ic,NonGr_ic,Ann_ic,InShr_i,InShr_o) :-
    new_array(Array),
    encode_and_check_annP(Ann_ec,AVarSet_ic,NonGr_ic,0,Array,Ann_ic,InShr_i,InShr_o).

encode_and_check_annP([],AVarSet_ic,_NonGr_ic,Annted,Array,Array,InShr,InShr) :-
    (AVarSet_ic =  Annted ->
        true
    ; aeq_error(bad_entry,_)).
encode_and_check_annP([AVar - H |T],AVarSet_ic,NonGr_ic,Annted_i,Array_i,Array_o,InShr_i,InShr_o) :-
    AVar_ic is 1 << AVar,
    check_ann(H,AVar_ic,AVarSet_ic,NonGr_ic,InShr_i,InShr_m),
    aset(AVar,Array_i,H,Array_m),
    bitset_union(AVar_ic,Annted_i,Annted_o),
    encode_and_check_annP(T,AVarSet_ic,NonGr_ic,Annted_o,Array_m,Array_o,InShr_m,InShr_o) .

%------------------------------------------------------------------------%
% encode_and_check_ann(+,+,+,-)
% encode_and_check_ann(Ann_ec,AVarSet_ic,NonGr_ic,Ann_ic) 
%------------------------------------------------------------------------%
% Identical to the one above but for set sharing.
%------------------------------------------------------------------------%
encode_and_check_ann(Ann_ec,AVarSet_ic,NonGr_ic,Ann_ic) :-
    new_array(Array),
    encode_and_check_ann(Ann_ec,AVarSet_ic,NonGr_ic,0,Array,Ann_ic).

encode_and_check_ann([],AVarSet_ic,_NonGr_ic,Annted,Array,Array) :-
    (AVarSet_ic = Annted ->
        true
    ; aeq_error(bad_entry,_)).
encode_and_check_ann([AVar - H |T],AVarSet_ic,NonGr_ic,Annted_i,Array_i,Array_o) :-
    AVar_ic is 1 << AVar,
    check_ann(H,AVar_ic,AVarSet_ic,NonGr_ic,0,_),
    aset(AVar,Array_i,H,Array_m),
    bitset_union(AVar_ic,Annted_i,Annted_o),
    encode_and_check_ann(T,AVarSet_ic,NonGr_ic,Annted_o,Array_m,Array_o) .

%------------------------------------------------------------------------%
% check_ann(+,+,+,+,+,-)
% check_ann(Item,AVar_ic,AVarSet_ic,NonGr_ic,InShr_i,InShr_m)
%------------------------------------------------------------------------%
% This predicate checks that the annotation Item for AVar is consistent
% with the rest of information: the total set of variables (AVarSet_ic)
% and the set of possibly non-ground variables (NonGr_ic). It also
% creates the bitset of possibly non-linear variables.
%------------------------------------------------------------------------%

check_ann(f,AVar_ic,_,NonGr_ic,InShr,InShr):-
    bitset_member(AVar_ic,NonGr_ic),!.
check_ann(g,AVar_ic,AVarSet_ic,NonGr_ic,InShr,InShr):-
    bitset_member(AVar_ic,AVarSet_ic), 
    not_bitset_member(AVar_ic,NonGr_ic),!.
check_ann(l,AVar_ic,_,NonGr_ic,InShr,InShr):-
    bitset_member(AVar_ic,NonGr_ic),!.
check_ann(lng,AVar_ic,_,NonGr_ic,InShr,InShr):-
    bitset_member(AVar_ic,NonGr_ic),!.
check_ann(lnf,AVar_ic,_,NonGr_ic,InShr,InShr):-
    bitset_member(AVar_ic,NonGr_ic),!.
check_ann(lngf,AVar_ic,_,NonGr_ic,InShr,InShr):-
    bitset_member(AVar_ic,NonGr_ic),!.
check_ann(ng,AVar_ic,_,NonGr_ic,InShr_i,InShr_o):-
    bitset_member(AVar_ic,NonGr_ic),!,
    bitset_union(AVar_ic,InShr_i,InShr_o).
check_ann(nf,AVar_ic,_,NonGr_ic,InShr_i,InShr_o):-
    bitset_member(AVar_ic,NonGr_ic),!,
    bitset_union(AVar_ic,InShr_i,InShr_o).
check_ann(ngf,AVar_ic,_,NonGr_ic,InShr_i,InShr_o):-
    bitset_member(AVar_ic,NonGr_ic),!,
    bitset_union(AVar_ic,InShr_i,InShr_o).
check_ann(a,AVar_ic,_,NonGr_ic,InShr_i,InShr_o):-
    bitset_member(AVar_ic,NonGr_ic),!,
    bitset_union(AVar_ic,InShr_i,InShr_o).
check_ann(_,_,_,_,_,_):-
    aeq_error(bad_entry,_), fail.

%------------------------------------------------------------------------%
% aeq_add_pairs(+,+,-)
% aeq_add_pairs(LNum,ExShr_i,ExShr_o)
%------------------------------------------------------------------------%
% ExShr_i is an accumulator. ExShr_o is the list of bitcodes representing
% each of all the possible couples obtained from LNum,i.e., is the 
% bitcode representation of the "top" pair-sharing obtained from LNum.
%------------------------------------------------------------------------%
aeq_add_pairs([],ExShr,ExShr) .
aeq_add_pairs([_],ExShr,ExShr) :- ! .
aeq_add_pairs([H | T],ExShr_i,ExShr_o) :-
    aeq_add_pairs(T,H,ExShr_i,ExShr_m),
    aeq_add_pairs(T,ExShr_m,ExShr_o) .

aeq_add_pairs([],_H,ExShr_u,ExShr) :-
    sort(ExShr_u,ExShr).
aeq_add_pairs([T1|T2],H,ExShr_i,ExShr_o) :-
    set_to_bitcode([T1,H],T1_H_ic),
    aeq_add_pairs(T2,H,[T1_H_ic|ExShr_i],ExShr_o) .

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The follwoing are the lub and leq operations for the annotation set
% They have to change of the annotation set changes
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% ann_leq(+,+)
% ann_leq(Item1,Item2)
%------------------------------------------------------------------------%
% Satisfied iff Item1 is less or equal than Item2 in the lattice.
%------------------------------------------------------------------------%
ann_leq(a,a).
ann_leq(f,Item2) :-   ann_f_leq(Item2).
ann_leq(g,Item2) :-   ann_g_leq(Item2).
ann_leq(lngf,Item2):- ann_lngf_leq(Item2).
ann_leq(lng,Item2):-  ann_lng_leq(Item2).
ann_leq(lnf,Item2):-  ann_lng_leq(Item2).
ann_leq(l,Item2):-    ann_l_leq(Item2).
ann_leq(ngf,Item2):-  ann_ngf_leq(Item2).
ann_leq(ng,Item2):-   ann_ng_leq(Item2).
ann_leq(nf,Item2):-   ann_nf_leq(Item2).

ann_f_leq(f).
ann_f_leq(lng).
ann_f_leq(ng).
ann_f_leq(l).
ann_f_leq(a).

ann_g_leq(g).
ann_g_leq(lnf).
ann_g_leq(nf).
ann_g_leq(l).
ann_g_leq(a).

ann_lngf_leq(a).
ann_lngf_leq(ng).
ann_lngf_leq(nf).
ann_lngf_leq(ngf).
ann_lngf_leq(l).
ann_lngf_leq(lng).
ann_lngf_leq(lnf).

ann_lng_leq(lng).
ann_lng_leq(ng).
ann_lng_leq(l).
ann_lng_leq(a).

%% ann_lnf_leq(lnf).
%% ann_lnf_leq(nf).
%% ann_lnf_leq(l).
%% ann_lnf_leq(a).

ann_ngf_leq(a).
ann_ngf_leq(ng).
ann_ngf_leq(nf).
ann_ngf_leq(ngf).

ann_l_leq(l).
ann_l_leq(a).

ann_ng_leq(ng).
ann_ng_leq(a).

ann_nf_leq(nf).
ann_nf_leq(a).

%------------------------------------------------------------------------%
% ann_lub(+,+,-)
% ann_lub(Item1,Item2,Lub)
%------------------------------------------------------------------------%
% Computes the lub of Item1 and Item2
%------------------------------------------------------------------------%
ann_lub(a,_,a).
ann_lub(f,Item2,Lub):-    ann_lub_f(Item2,Lub).
ann_lub(g,Item2,Lub):-    ann_lub_g(Item2,Lub).
ann_lub(lngf,Item2,Lub):- ann_lub_lngf(Item2,Lub).
ann_lub(lng,Item2,Lub):-  ann_lub_lng(Item2,Lub).
ann_lub(lnf,Item2,Lub):-  ann_lub_lnf(Item2,Lub).
ann_lub(l,Item2,Lub):-    ann_lub_l(Item2,Lub).
ann_lub(ngf,Item2,Lub):-  ann_lub_ngf(Item2,Lub).
ann_lub(ng,Item2,Lub):-   ann_lub_ng(Item2,Lub).
ann_lub(nf,Item2,Lub):-   ann_lub_nf(Item2,Lub).

ann_lub_f(a,a).
ann_lub_f(f,f).
ann_lub_f(g,l).
ann_lub_f(lngf,lng).
ann_lub_f(lng,lng).
ann_lub_f(lnf,l).
ann_lub_f(l,l).
ann_lub_f(ngf,ng).
ann_lub_f(ng,ng).
ann_lub_f(nf,a).

ann_lub_g(a,a).
ann_lub_g(f,l).
ann_lub_g(g,g).
ann_lub_g(lngf,lnf).
ann_lub_g(lng,l).
ann_lub_g(lnf,lnf).
ann_lub_g(l,l).
ann_lub_g(ngf,nf).
ann_lub_g(ng,a).
ann_lub_g(nf,nf).

ann_lub_lngf(a,a).
ann_lub_lngf(f,lng).
ann_lub_lngf(g,lnf).
ann_lub_lngf(lngf,lngf).
ann_lub_lngf(lng,lng).
ann_lub_lngf(lnf,lnf).
ann_lub_lngf(l,l).
ann_lub_lngf(ngf,ngf).
ann_lub_lngf(ng,ng).
ann_lub_lngf(nf,nf).

ann_lub_lng(a,a).
ann_lub_lng(f,lng).
ann_lub_lng(g,l).
ann_lub_lng(lngf,lng).
ann_lub_lng(lng,lng).
ann_lub_lng(lnf,l).
ann_lub_lng(l,l).
ann_lub_lng(ngf,ng).
ann_lub_lng(ng,ng).
ann_lub_lng(nf,a).

ann_lub_lnf(a,a).
ann_lub_lnf(f,l).
ann_lub_lnf(g,lnf).
ann_lub_lnf(lngf,lnf).
ann_lub_lnf(lng,l).
ann_lub_lnf(lnf,lnf).
ann_lub_lnf(l,l).
ann_lub_lnf(ngf,nf).
ann_lub_lnf(ng,a).
ann_lub_lnf(nf,nf).

ann_lub_l(a,a).
ann_lub_l(f,l).
ann_lub_l(g,l).
ann_lub_l(lngf,l).
ann_lub_l(lng,l).
ann_lub_l(lnf,l).
ann_lub_l(l,l).
ann_lub_l(ngf,a).
ann_lub_l(ng,a).
ann_lub_l(nf,a).

ann_lub_ngf(a,a).
ann_lub_ngf(f,ng).
ann_lub_ngf(g,nf).
ann_lub_ngf(lngf,ngf).
ann_lub_ngf(lng,ng).
ann_lub_ngf(lnf,nf).
ann_lub_ngf(l,a).
ann_lub_ngf(ngf,ngf).
ann_lub_ngf(ng,ng).
ann_lub_ngf(nf,nf).

ann_lub_ng(a,a).
ann_lub_ng(f,ng).
ann_lub_ng(g,a).
ann_lub_ng(lngf,ng).
ann_lub_ng(lng,ng).
ann_lub_ng(lnf,a).
ann_lub_ng(l,a).
ann_lub_ng(ngf,ng).
ann_lub_ng(ng,ng).
ann_lub_ng(nf,a).

ann_lub_nf(a,a).
ann_lub_nf(f,a).
ann_lub_nf(g,nf).
ann_lub_nf(lngf,nf).
ann_lub_nf(lng,a).
ann_lub_nf(lnf,nf).
ann_lub_nf(l,a).
ann_lub_nf(ngf,nf).
ann_lub_nf(ng,a).
ann_lub_nf(nf,nf).

%------------------------------------------------------------------------%
% ann_conj(+,+,-)
% ann_conj(Item1,Item2,AnnA)
%------------------------------------------------------------------------%
% Item2 and Item1 are the annotations corresponding to an abstract 
% variable A and a (possibly var) abstract term ATerm. This predicate
% computes the annotation for A resulting from the unification of A and
% ATerm. We assume they do not share variables.
%------------------------------------------------------------------------%

ann_conj(a,Item2,AnnA):- ann_remove_linear_non_ground(Item2,AnnA).
ann_conj(f,Item2,Item2).
ann_conj(g,_,g).
ann_conj(lngf,Item2,Conj):- ann_conj_lngf(Item2,Conj).
ann_conj(lng,Item2,Conj):-  ann_conj_lng(Item2,Conj).
ann_conj(lnf,Item2,Conj):-  ann_conj_lnf(Item2,Conj).
ann_conj(l,Item2,Conj):-    ann_conj_l(Item2,Conj).
ann_conj(ngf,Item2,Conj):-  ann_conj_ngf(Item2,Conj).
ann_conj(ng,Item2,Conj):-   ann_conj_ng(Item2,Conj).
ann_conj(nf,Item2,Conj):-   ann_conj_nf(Item2,Conj).

ann_conj_lngf(a,nf).
ann_conj_lngf(f,lngf).
ann_conj_lngf(g,g).
ann_conj_lngf(lngf,lnf).
ann_conj_lngf(lng,lnf).
ann_conj_lngf(lnf,lnf).
ann_conj_lngf(l,lnf).
ann_conj_lngf(ngf,nf).
ann_conj_lngf(ng,nf).
ann_conj_lngf(nf,nf).

ann_conj_lng(a,a).
ann_conj_lng(f,lng).
ann_conj_lng(g,g).
ann_conj_lng(lngf,lnf).
ann_conj_lng(lng,l).
ann_conj_lng(lnf,lnf).
ann_conj_lng(l,l).
ann_conj_lng(ngf,nf).
ann_conj_lng(ng,a).
ann_conj_lng(nf,nf).

ann_conj_lnf(a,nf).
ann_conj_lnf(f,lnf).
ann_conj_lnf(g,g).
ann_conj_lnf(lngf,lnf).
ann_conj_lnf(lng,lnf).
ann_conj_lnf(lnf,lnf).
ann_conj_lnf(l,lnf).
ann_conj_lnf(ngf,nf).
ann_conj_lnf(ng,nf).
ann_conj_lnf(nf,nf).

ann_conj_l(a,a).
ann_conj_l(f,l).
ann_conj_l(g,g).
ann_conj_l(lngf,lnf).
ann_conj_l(lng,l).
ann_conj_l(lnf,lnf).
ann_conj_l(l,l).
ann_conj_l(ngf,nf).
ann_conj_l(ng,a).
ann_conj_l(nf,nf).

ann_conj_ngf(a,nf).
ann_conj_ngf(f,ngf).
ann_conj_ngf(g,g).
ann_conj_ngf(lngf,nf).
ann_conj_ngf(lng,nf).
ann_conj_ngf(lnf,nf).
ann_conj_ngf(l,nf).
ann_conj_ngf(ngf,nf).
ann_conj_ngf(ng,nf).
ann_conj_ngf(nf,nf).

ann_conj_ng(a,a).
ann_conj_ng(f,ng).
ann_conj_ng(g,g).
ann_conj_ng(lngf,l).
ann_conj_ng(lng,l).
ann_conj_ng(lnf,nf).
ann_conj_ng(l,l).
ann_conj_ng(ngf,nf).
ann_conj_ng(ng,a).
ann_conj_ng(nf,nf).

ann_conj_nf(a,nf).
ann_conj_nf(f,nf).
ann_conj_nf(g,g).
ann_conj_nf(lngf,lnf).
ann_conj_nf(lng,lnf).
ann_conj_nf(lnf,lnf).
ann_conj_nf(l,lnf).
ann_conj_nf(ngf,nf).
ann_conj_nf(ng,nf).
ann_conj_nf(nf,nf).

%------------------------------------------------------------------------%
% ann_linear(+)
% Satisfied if the annotation corresponds to a linear abstract var.
%------------------------------------------------------------------------%
ann_linear(lngf).
ann_linear(lnf).
ann_linear(lng).
ann_linear(f).
ann_linear(g).
ann_linear(l).

%------------------------------------------------------------------------%
% ann_non_linear(+)
% Satisfied if the annotation corresponds to a possibly non linear var.
%------------------------------------------------------------------------%
ann_non_linear(ngf).
ann_non_linear(nf).
ann_non_linear(ng).
ann_non_linear(a).

%% %------------------------------------------------------------------------%
%% % ann_possibly_ground(+)
%% % Satisfied if the annotation corresponds to a possibly ground var.
%% %------------------------------------------------------------------------%
%% ann_possibly_ground(a).
%% ann_possibly_ground(l).
%% ann_possibly_ground(lnf).
%% ann_possibly_ground(nf).
%% ann_possibly_ground(g).

%------------------------------------------------------------------------%
% ann_non_ground(+)
% Satisfied if the annotation corresponds to a non ground var.
%------------------------------------------------------------------------%
ann_non_ground(f).
ann_non_ground(lng).
ann_non_ground(lngf).
ann_non_ground(ng).
ann_non_ground(ngf).

%% %------------------------------------------------------------------------%
%% % ann_non_free(+)
%% % Satisfied if the annotation corresponds to a non-free var.
%% %------------------------------------------------------------------------%
%% ann_non_free(lngf).
%% ann_non_free(ngf).
%% ann_non_free(nf).
%% ann_non_free(lnf).
%% ann_non_free(g).

ann_linear(AVar_ec,Ann) :-
    aref(AVar_ec,Ann,Item),
    ann_linear(Item).

%% ann_linearP(AVar_ic,ps(InShr,_ExShr)) :-
%%      not_bitset_member(AVar_ic,InShr) .
%% 
%% ann_add_non_free(a,nf).
%% ann_add_non_free(lngf,lngf).
%% ann_add_non_free(lng,lngf).
%% ann_add_non_free(lnf,lnf).
%% ann_add_non_free(l,lnf).
%% ann_add_non_free(f,lnf).
%% ann_add_non_free(g,g).
%% ann_add_non_free(ngf,ngf).
%% ann_add_non_free(ng,ngf).
%% ann_add_non_free(nf,nf).

ann_remove_linear_non_ground(a,a).
ann_remove_linear_non_ground(f,a).
ann_remove_linear_non_ground(g,g).
ann_remove_linear_non_ground(lngf,nf).
ann_remove_linear_non_ground(lng,a).
ann_remove_linear_non_ground(lnf,nf).
ann_remove_linear_non_ground(l,a).
ann_remove_linear_non_ground(ngf,nf).
ann_remove_linear_non_ground(ng,a).
ann_remove_linear_non_ground(nf,nf).

ann_remove_linear(a,a).
ann_remove_linear(f,ng).
ann_remove_linear(g,g).
ann_remove_linear(lngf,ngf).
ann_remove_linear(lng,ng).
ann_remove_linear(lnf,nf).
ann_remove_linear(l,a).
ann_remove_linear(ngf,ngf).
ann_remove_linear(ng,ng).
ann_remove_linear(nf,nf).

ann_remove_non_ground(a,a).
ann_remove_non_ground(f,l).
ann_remove_non_ground(g,g).
ann_remove_non_ground(lngf,lnf).
ann_remove_non_ground(lng,l).
ann_remove_non_ground(lnf,lnf).
ann_remove_non_ground(l,l).
ann_remove_non_ground(ngf,nf).
ann_remove_non_ground(ng,a).
ann_remove_non_ground(nf,nf).

%------------------------------------------------------------------------%
% get_ann_aterm(+,+,-)
% get_ann_aterm(AEqs,ATerm,AnnT)
%------------------------------------------------------------------------%
% Computes the annotation corresponding to an absract term. If it is
% a variable, it is just a question of reading its annotation. Otherwise
% we have to get the list of annotations LAnn corresponding to each 
% abstract variable in the term, the flag indicating linearity, and decide.
%------------------------------------------------------------------------%
get_ann_aterm(aeqs(_,Ann,Shr,_,_),ATerm,AnnT):-
    ( ATerm = '@'(N) ->
        aref(N,Ann,AnnT)
    ; get_ann_aterm(ATerm,Ann,Shr,LFlag,0,_,LAnn,[]),
      sort(LAnn,LAnn_s),
      aeq_decide_ann(LFlag,LAnn_s,AnnT)).

get_ann_aterm(aeqs(_,Ann,Shr,_,_),ATerm,LAnn_s,AnnT):-
    ( ATerm = '@'(N) ->
        aref(N,Ann,AnnT),
        LAnn = [AnnT]
    ; get_ann_aterm(ATerm,Ann,Shr,LFlag,0,_,LAnn,[]),
      sort(LAnn,LAnn_s),
      aeq_decide_ann(LFlag,LAnn_s,AnnT)).


get_ann_aterm(ATerm,_,_,_,AVars0,AVars,LAnn0,LAnn):-
    atomic(ATerm),!,
    AVars0 = AVars,
    LAnn0 = [g|LAnn].
get_ann_aterm([H|T],Ann,Shr,L,AVars0,AVars,LAnn0,LAnn) :- !,
    get_ann_aterm(H,Ann,Shr,L,AVars0,AVars1,LAnn0,LAnn1),
    get_ann_aterm(T,Ann,Shr,L,AVars1,AVars,LAnn1,LAnn).
get_ann_aterm('@'(AVar_ec),Ann,Shr,L,AVars0,AVars,[Item|LAnn],LAnn) :- !,
    AVar_ic is 1 << AVar_ec,
    bitset_union(AVar_ic,AVars0,AVars),
    aref(AVar_ec,Ann,Item),
    ( (L == nl ; ann_non_linear(Item)) ->
        L = nl
    ;  ( (bitset_member(AVar_ic,AVars0); share_shr(Shr,AVar_ic,AVars0)) -> 
              L = nl
       ; true)).
get_ann_aterm(ATerm,Ann,Shr,L,AVars0,AVars,LAnn0,LAnn) :-
    functor(ATerm,_,Arity),
    get_ann_aterm(Arity,ATerm,Ann,Shr,L,AVars0,AVars,LAnn0,LAnn).

get_ann_aterm(0,_,_,_,_,AVars,AVars,LAnn,LAnn):- !.
get_ann_aterm(Arity,ATerm,Ann,Shr,L,AVars0,AVars,LAnn0,LAnn) :-
    arg(Arity,ATerm,Arg),
    get_ann_aterm(Arg,Ann,Shr,L,AVars0,AVars1,LAnn0,LAnn1),
    Arity0 is Arity - 1,
    get_ann_aterm(Arity0,ATerm,Ann,Shr,L,AVars1,AVars,LAnn1,LAnn).

aeq_decide_ann(l,LAnn,AnnT):- !,
    ( LAnn = [g] ->
        AnnT = g
      ; ( ord_intersect([f,lng,lngf],LAnn) ->
             AnnT = lngf
         ; AnnT = lnf)).
aeq_decide_ann(nl,LAnn,AnnT):- 
    ( ord_intersect([f,lng,lngf,ng,ngf],LAnn) ->
            AnnT = ngf
    ;   AnnT = nf).
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following code answers questions about the abstract equations and
% manipulates them
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% free_aeqs(+,+)
% free_aeqs(ASub_ic,Term)
%------------------------------------------------------------------------%
% Succeeds if Term is a free abstract variable.
%------------------------------------------------------------------------%
free_aeqs(aeqs(_,Ann,_,_,_),'@'(AVar_ec)) :-
    aref(AVar_ec,Ann,f) .

%------------------------------------------------------------------------%
% free_aeqs_list(+,+)
% free_aeqs_list(LAVars,ASub_ic).
%------------------------------------------------------------------------%
% Succeeds if each element of LAVars is a free abstract variable.
%------------------------------------------------------------------------%
free_aeqs_list([],_).
free_aeqs_list([H|T],AEqs) :-
    free_aeqs(AEqs,H),
    free_aeqs_list(T,AEqs).

%------------------------------------------------------------------------%
% ground_aeqs(+,+)
% ground_aeqs(ASub,ATerm)
%------------------------------------------------------------------------%
% Succeeds if all variables in ATerm are ground (none appear in NGrAVars)
%------------------------------------------------------------------------%
ground_aeqs(aeqs(_,_,_,_,NGrAVars),ATerm) :-
    avariables_ic(ATerm,AVarsATerm_ic),
    bitset_intersect(AVarsATerm_ic,NGrAVars,0) .

%------------------------------------------------------------------------%
% compound_aeqs(+,+)
% compound_aeqs(ASub,ATerm) 
%------------------------------------------------------------------------%
% Succeeds if ATerm is either a variable which is ground or not a variable.
%------------------------------------------------------------------------%
compound_aeqs(aeqs(_,_,_,_,NGrAVars),'@'(AVar_ec)) :- !,
    AVar_ic is 1 << AVar_ec, 
    bitset_intersect(AVar_ic,NGrAVars,0) .
compound_aeqs(_AEqs,_ATerm) .

%------------------------------------------------------------------------%
% share_shr(+,+,+)
% share_shr(Shr,AVar_ic, AVars_ic) 
%------------------------------------------------------------------------%
% Succeeds iff AVar_ic shares with at least a variable in AVars_ic
%------------------------------------------------------------------------%
share_shr(ps(_,Shr),AVar_ic,OtherAVars_ic) :- 
    share_shr(Shr,AVar_ic,OtherAVars_ic). 
share_shr([SG|_Shr],AVar_ic,OtherAVars_ic) :- 
    bitset_member(AVar_ic,SG),
    bitset_intersect(OtherAVars_ic,SG,Intersection),
    Intersection =\= 0,!.
share_shr([_|Shr],AVar_ic,OtherAVars_ic) :- 
    share_shr(Shr,AVar_ic,OtherAVars_ic) .

%% %------------------------------------------------------------------------%
%% % share_aeqs(+,+,+)
%% % share_aeqs(ASub,ATerm,AVar)
%% %------------------------------------------------------------------------%
%% % Satisfied iff AVar and  ATerm share.
%% %------------------------------------------------------------------------%
%% share_aeqs(ASub,ATerm,AVar) :-
%%      avariables_ic(ATerm,AVarsATerm_ic),
%%      avar_ic(AVar,AVar_ic),
%%      share_aeqs_ic(ASub,AVarsATerm_ic,AVar_ic).

share_aeqs_ic(aeqs(_,_,Shr,_,NGrAVars),AVarsATerm_ic,AVar_ic) :-
    (bitset_member(AVar_ic,AVarsATerm_ic) ->
      bitset_member(AVar_ic,NGrAVars)
    ; share_shr(Shr,AVar_ic,AVarsATerm_ic)).

%------------------------------------------------------------------------%
% linear_aeqs(+,+) 
% linear_aeqs(AEqs,ATerm) 
%------------------------------------------------------------------------%
% Succeeds if ATerm is linear w.r.t. AEqs. i.e. iff each abstract var:
%    1- is ground (does not appear in NGrAVars), or
%    2- does not appear twice,  (does not appear in AVars_SoFar), is 
%       linear and does not share with any other var in ATerm.
%------------------------------------------------------------------------%
linear_aeqs(AEqs,ATerm) :-
    linear_aeqs(ATerm,AEqs,0,_) .

linear_aeqs(ATerm,_AEqs,AVars_SoFar,AVars_SoFar) :-
    atomic(ATerm),!.
linear_aeqs([H|T],AEqs,AVars_in,AVars_out) :- !,
    linear_aeqs(H,AEqs,AVars_in,Accum),
    linear_aeqs(T,AEqs,Accum,AVars_out).
linear_aeqs('@'(AVar_ec),aeqs(_,Ann,Shr,_,NGrAVars),AVars_SoFar,AVars) :- !,
    AVar_ic is 1 << AVar_ec,
    ( bitset_member(AVar_ic,NGrAVars) ->   % var is possibly non-ground
        not_bitset_member(AVar_ic,AVars_SoFar),
        (  Shr = ps(InShr,ExShr) ->
            \+ bitset_member(AVar_ic,InShr),
            \+ share_shr(ExShr,AVar_ic,AVars_SoFar)
        ; ann_linear(AVar_ec,Ann),
          \+ share_shr(Shr,AVar_ic,AVars_SoFar)
       ),
        bitset_union(AVar_ic,AVars_SoFar,AVars)
    ; AVars = AVars_SoFar).
linear_aeqs(ATerm,AEqs,AVars_in,AVars_out) :-
    functor(ATerm,_,Arity),
    linear_aeqs(Arity,ATerm,AEqs,AVars_in,AVars_out).

linear_aeqs(0,_,_,AVars,AVars):- !.
linear_aeqs(Arity,ATerm,AEqs,AVars_in,AVars_out) :-
    arg(Arity,ATerm,Arg),
    linear_aeqs(Arg,AEqs,AVars_in,AVars_m),
    Arity0 is Arity - 1,
    linear_aeqs(Arity0,ATerm,AEqs,AVars_m,AVars_out).

%------------------------------------------------------------------------%
% ground_ann(+,+) 
% ground_ann(ATerm,Ann) 
%------------------------------------------------------------------------%
% Succeeds if ATerm is ground w.r.t. Ann
%------------------------------------------------------------------------%
%% ground_ann([],_):- !.
%% ground_ann([H|T],Ann):- !,
%%      ground_ann(H,Ann),
%%      ground_ann(T,Ann).
%% ground_ann('@'(AVar_ec),Ann) :- 
%%      aref(AVar_ec,Ann,Item),
%%      Item == g,!.
%% ground_ann(ATerm,Ann):- 
%%      ATerm =.. [_|Args],
%%      ground_ann(Args,Ann).

%------------------------------------------------------------------------%
% Several predicates that read diffferent arguments of an ASub
%------------------------------------------------------------------------%

get_Eqs_aeqs(aeqs(Eqs_nsf,_Ann,_Shr,_AVarSet,_NGrAVars),Eqs_nsf) .

% get_Eqs_NGr_aeqs(aeqs(Eqs_nsf,_Ann,_Shr,_AVarSet,NGrAVars),Eqs_nsf,NGrAVars) .

get_Eqs_Ann_aeqs(aeqs(Eqs_nsf,Ann,_Shr,_AVarSet,_NGrAVars),Eqs_nsf,Ann) .

%% get_Shr_aeqs(aeqs(_Eqs_nsf,_Ann,Shr,_AVarSet,_NGrAVars),Shr) .
%% 
%% get_Ann_aeqs(aeqs(_Eqs_nsf,Ann,_Shr,_AVarSet,_NGrAVars),Ann) .
%% 
%% get_Ann_item(AVar_ec,aeqs(_,Ann,_,_,_),Item):-
%%      aref(AVar_ec,Ann,Item).

%------------------------------------------------------------------------%
% delta_bar_ShrP(+,+,+,-,-,-)
% delta_bar_ShrP(ExShr,A_ic,T_ic,AVarsATerm_ic,ExShr_o,ExShr_r,ExShr_b) .
%------------------------------------------------------------------------%
delta_bar_ShrP(ps(InShr,ExShr),A_ic,T_ic,AVarsATerm_ic,
                                            ps(InShr,ExShr_o),
                                            ps(InShr_r,ExShr_r),
                                            ps(InShr_b,ExShr_b)) :-
    bitset_intersect(InShr,AVarsATerm_ic,InShr_r),
    bitset_subtract(InShr,AVarsATerm_ic,InShr_b),
    delta_bar_Shr2(ExShr,A_ic,T_ic,ExShr_o,ExShr_r,ExShr_b) .

%------------------------------------------------------------------------%
% delta_bar_Shr2(+,+,+,-,-,-)
% delta_bar_Shr2(ExShr,A_ic,T_ic,ExShr_o,ExShr_r,ExShr_b) .
%------------------------------------------------------------------------%
% ExShr_b contains those sets in ExShr disjoint from A_ic and  T_ic. 
% ExShr_r contains those sets in ExShr disjoint from either A_ic or  T_ic. 
% ExShr_o contains those in ExShr_b and ExShr_r
%------------------------------------------------------------------------%
delta_bar_Shr2([],_A_ic,_T_ic,[],[],[]) .
delta_bar_Shr2([H|T],A_ic,T_ic,Shr_o,Shr_r,Shr_b):-
    ( bitset_intersect(H,A_ic,0) ->
        Shr_o = [H|R1],
        ( bitset_intersect(H,T_ic,0) ->
            Shr_r = R2,
            Shr_b = [H|R3]
        ;   Shr_r = [H|R2],
            Shr_b = R3)
    ;   Shr_b = R3,
        ( bitset_intersect(H,T_ic,0) ->
            Shr_o = [H|R1],
            Shr_r = [H|R2]
        ;   Shr_o = R1,
            Shr_r = R2)),
    delta_bar_Shr2(T,A_ic,T_ic,R1,R2,R3).

%------------------------------------------------------------------------%
% aeq_split_intersect_disjoint(+,+,-,-)
% aeq_split_intersect_disjoint(Shr,AVarsATerm_ic,NewShr1,NewShr2).
%------------------------------------------------------------------------%
% Splits Shr into those sets containing vars in AVarsATerm_ic (NewShr1), 
% and those which do not.
%------------------------------------------------------------------------%
aeq_split_intersect_disjoint(ps(InShr,ExShr),AVarsATerm_ic,ps(InShr_r,ExShr_r),
                                                    ps(InShr_b,ExShr_b)) :-
    bitset_intersect(InShr,AVarsATerm_ic,InShr_r),
    bitset_subtract(InShr,AVarsATerm_ic,InShr_b),
    aeq_split_intersect_disjoint(ExShr,AVarsATerm_ic,ExShr_r,ExShr_b) .
aeq_split_intersect_disjoint([],_AVarsATerm_ic,[],[]) .
aeq_split_intersect_disjoint([H|T],AVarsATerm_ic,NShr1,NShr2) :-
    ( bitset_intersect(H,AVarsATerm_ic,0) ->
        NShr1 = R1,NShr2 = [H|R2]
    ;   NShr1 = [H|R1],NShr2 = R2),
    aeq_split_intersect_disjoint(T,AVarsATerm_ic,R1,R2) .

%------------------------------------------------------------------------%
% aeq_split_disjoint(+,+,-)
% aeq_split_disjoint(Shr,AVarsATerm_ic,NewShr).
%------------------------------------------------------------------------%
% Makes the abstract variables AVarsATerm_ic ground in Shr, i.e., NewShr
% contains the sharing sets which do not intersect with AVarsATerm_ic.
%------------------------------------------------------------------------%
aeq_split_disjoint(ps(I,E),AVarsATerm_ic,ps(I_e,E_e)) :- 
    bitset_subtract(I,AVarsATerm_ic,I_e),
    aeq_split_disjoint(E,AVarsATerm_ic,E_e) .
aeq_split_disjoint([],_AVarsATerm_ic,[]) .
aeq_split_disjoint([H|T],AVarsATerm_ic,NShr) :-
    ( bitset_intersect(H,AVarsATerm_ic,0) ->
        NShr = [H|R]
    ;   NShr = R),
    aeq_split_disjoint(T,AVarsATerm_ic,R).

%------------------------------------------------------------------------%
% aeq_split_intersect(+,+,+,-)
% aeq_split_intersect(Shr,A_ic,T_ic,NewShr).
%------------------------------------------------------------------------%
% NewShr contains the sharing sets which intersect with A_ic or T_ic
%------------------------------------------------------------------------%
aeq_split_intersect([],_A_ic,_T_ic,[]) .
aeq_split_intersect([H|T],_A_ic,_T_ic,Sh) :-
    ( (bitset_intersect(H,_A_ic,0);bitset_intersect(H,_T_ic,0)) ->
        Sh = [H|ShT]
    ;   Sh = ShT),
    aeq_split_intersect(T,_A_ic,_T_ic,ShT).


%------------------------------------------------------------------------%
% delta_Shr(+,+,+,-,-,-)
% delta_Shr(ExShr,A_ic,T_ic,ExShr_o,ExShr_r,ExShr_b) .
%------------------------------------------------------------------------%
% ExShr_b contains those sets in ExShr disjoint from A_ic and  T_ic. 
% ExShr_r contains those sets in ExShr which intersect with T_ic.
% ExShr_o contains those sets in ExShr which intersect with A_ic.
%------------------------------------------------------------------------%
delta_Shr([],_,_,[],[],[]) .
delta_Shr([H|T],A_ic,T_ic,Shr_o,Shr_r,Shr_b):-
    ( bitset_intersect(H,A_ic,0) ->
        Shr_o = R1,
        ( bitset_intersect(H,T_ic,0) ->
            Shr_r = R2,
            Shr_b = [H|R3]
        ;   Shr_r = [H|R2],
            Shr_b = R3)
    ;   Shr_o = [H|R1],
        Shr_b = R3,
        ( bitset_intersect(H,T_ic,0) ->
            Shr_r = R2
        ;   Shr_r = [H|R2])),
    delta_Shr(T,A_ic,T_ic,R1,R2,R3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  Extensions to   `../basics.pl'
%%%%%%%%%%%%

%% :- mode finiteclosedlist(?),         %  
%%      openendedlist(?),               %  
%%      anylist(?),                     %  
%%      insert_groundSet(+,+,-).        %  For unsorted ground lists.

finiteclosedlist(Args) :- var(Args),!,fail.
finiteclosedlist([]) .
finiteclosedlist([_|Args]) :- finiteclosedlist(Args) .

% openendedlist(Args) :- var(Args),!.
% openendedlist([_|Args]) :- openendedlist(Args) .

anylist(Args) :- var(Args),!.
anylist([]) .
anylist([_|Args]) :- anylist(Args) .

insert_groundSet(Element,Set,Set) :-
    member(Element,Set),!.
insert_groundSet(Element,Set,[Element|Set]) .

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The following predicates implement the abstract projection. They do
% not depend on the anotation set.
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% aeq_project_nb(+,+,-)
% aeq_project_nb(Vars,ASub,Proj)
%------------------------------------------------------------------------%
% Performs the abstract projection as follows. First it projects the 
% abstract equations computing at the same the bitcode representation of 
% all abstract variables in the projection. If those are the same as the 
% original AVars, the projected ASub is identical to the original. 
% Otherwise, it performs the projection of the sharing, non-ground vars
% and annotation components.
%------------------------------------------------------------------------%
aeq_project_nb(Vars,AEqs,Proj):-
    AEqs = aeqs(Eqs,_,_,_,_),
    aeq_project_eqs(Vars,Eqs,Eqs_proj,AVars_proj),
    aeq_project_vars(AVars_proj,Eqs_proj,AEqs,Proj).

aeq_project_vars(AVars_p,Eqs_p,AEqs,aeqs(Eqs_p,Ann_p,Shr_p,AVars_p,NGrAVars_p)):-
    AEqs = aeqs(_,Ann,Shr,AVars,NGrAVars),
    (AVars_p == AVars ->
        Ann = Ann_p,
        Shr = Shr_p,
        NGrAVars = NGrAVars_p
    ; ( aeq_current_sharing(pair) ->
           aeq_project_shrP(Shr,AVars_p,Shr_p)
      ;    aeq_project_shr(Shr,AVars_p,Shr_p)),
      NGrAVars_p is NGrAVars /\ AVars_p,
      aeq_project_ann(Ann,AVars_p,Ann_p)).

%------------------------------------------------------------------------%
% aeq_project_eqs(+,+,-,-)
% aeq_project_eqs(Vars,Eqs,Eqs_proj,AVars_proj)
%------------------------------------------------------------------------%
% Eqs_proj = {X=ATerm | X \in Vars}, AVars_proj is the bitunion of all 
% abstract variables in each ATerm s.t. X = ATerm in Eqs_proj
%------------------------------------------------------------------------%
aeq_project_eqs([],_,[],0) :- ! .
aeq_project_eqs(Vars,Eqs,Eqs_proj,AVars_proj) :-
    aeq_project_eqs(Eqs,Vars,Eqs_proj,0,AVars_proj) .

aeq_project_eqs([],_,[],AVars_proj,AVars_proj).
aeq_project_eqs([CVar = ATerm|Eqs],Vars,Eqs_proj,AVars_proj_i,AVars_proj_o) :-
    ( memberchk(CVar,Vars) ->
        Eqs_proj = [CVar = ATerm|Eqs0_proj],
        avariables_ic(ATerm,AVars_ATerm),
        AVars_proj_m is AVars_proj_i \/ AVars_ATerm 
    ;   Eqs_proj = Eqs0_proj,
        AVars_proj_m = AVars_proj_i),
    aeq_project_eqs(Eqs,Vars,Eqs0_proj,AVars_proj_m,AVars_proj_o).

%------------------------------------------------------------------------%
% aeq_project_shrP(+,+,-)
% aeq_project_shrP(PairShr,AVars_proj,PairShr_proj)
%------------------------------------------------------------------------%
% Pair_sharing projection: first non-linears, then the set of pairs.
%------------------------------------------------------------------------%
aeq_project_shrP(_PS,0,ps(0,[])) :- ! .
aeq_project_shrP(ps(InShr,ExShr),AVars_proj,ps(InShr_o,ExShr_o)) :-
    InShr_o is InShr /\ AVars_proj,
    aeq_project_shr_nnP(ExShr,AVars_proj,ExShr_o) .

aeq_project_shr_nnP([],_,[]).
aeq_project_shr_nnP([SG|Shr],AVars_proj,Shr_proj) :- 
    ( bitset_subset(SG,AVars_proj) ->
        Shr_proj = [SG|Tail]
    ;   Shr_proj = Tail),
    aeq_project_shr_nnP(Shr,AVars_proj,Tail).

%------------------------------------------------------------------------%
% aeq_project_shr(+,+,-)
% aeq_project_shr(SetShr,AVars_proj,SetShr_proj)
%------------------------------------------------------------------------%
% Set_sharing projection.
%------------------------------------------------------------------------%
aeq_project_shr(_Shr,0,[]) :- ! .
aeq_project_shr(Shr,AVars_proj,Shr_proj) :-
    aeq_project_shr_nn(Shr,AVars_proj,Shr_proj_u),
    sort(Shr_proj_u,Shr_proj).

aeq_project_shr_nn([],_,[]).
aeq_project_shr_nn([SG|Shr],AVars_proj,Shr_proj) :- 
    bitset_intersect(SG,AVars_proj,SG_proj),
    ( SG_proj = 0 ->
        Shr_proj = Tail
    ;   Shr_proj = [SG_proj|Tail]),
    aeq_project_shr_nn(Shr,AVars_proj,Tail).

%------------------------------------------------------------------------%
% aeq_project_ann(+,+,-)
% aeq_project_ann(Ann,AVars_proj,Ann_proj)
%------------------------------------------------------------------------%
% Projects the annotation (i.e., the bitcode array).
%------------------------------------------------------------------------%
aeq_project_ann(_Ann,0,Ann_proj) :- ! ,
    new_array(Ann_proj) .
aeq_project_ann(Ann,AVars_proj,Ann_proj) :-
    proj_array_to_array(Ann,AVars_proj,Ann_proj) .

%------------------------------------------------------------------------%
% aeq_impose_depth_bound(+,-)
% aeq_impose_depth_bound(AEqs_i,AEqs_o
%------------------------------------------------------------------------%
% Imposes the depth bound. Does not have to be 
%------------------------------------------------------------------------%
aeq_impose_depth_bound('$bottom','$bottom') :- !.
aeq_impose_depth_bound(AEqs_i,AEqs_o) :-
    current_bound(Depth,Type),
    ((Type == project ; aeq_bounded(AEqs_i,Depth)) ->
        AEqs_o = AEqs_i
    ; aeq_impose_depth_bound(AEqs_i,Depth,AEqs_o)) .    %,! .
%%         current_bound(Depth,_),
%%         aeq_impose_depth_bound(AEqs_i,Depth,AEqs_o).

aeq_impose_depth_bound(AEqs_i,Depth,aeqs(Eqs,Ann,Shr,AVars,NGrAVars)) :-
    AEqs_i = aeqs(Eqs_i,_,Shr_i,_,NGrAVars_i),
    new_array(Ann_i), new_array(ASGs_i),
    aeq_depth_eqs_ann(Eqs_i,AEqs_i,Depth,Eqs,
                    info(Ann_i,0,0,[],ASGs_i,0),
                    info(Ann,AVars,_,_,ASGs_o,NLVars_o)),
    aeq_lub_shr(Shr_i,ASGs_o,NGrAVars_i,NLVars_o,Shr),
    aeq_det_ngroundvars(Shr,Ann,NGrAVars).

%------------------------------------------------------------------------%
% aeq_depth_eqs_ann(+,+,+,-,+,-)
% aeq_depth_eqs_ann(Eqs_i,AEqs,Depth,Eqs_o,Info_i,Info_o)
%------------------------------------------------------------------------%
% Imposes the depth bound in the input equations Eqs_i obtaining the
% output equations Eqs_o and the new info regarding annotation, new set
% of variables, non-linear variables (for pair sharing).
%------------------------------------------------------------------------%
aeq_depth_eqs_ann([],_AEqs,_Depth,[],Info,Info).
aeq_depth_eqs_ann([X = T|Eqs],AEqs,Depth,[X = Tdepth|Eqsdepth],Info_i,Info_o):-
    term_depth(T,AEqs,Depth,Tdepth,Info_i,Info_new),
    aeq_depth_eqs_ann(Eqs,AEqs,Depth,Eqsdepth,Info_new,Info_o) .

%------------------------------------------------------------------------%
% term_depth(+,+,+,-,+,-)
% term_depth(T,AEqs,Depth,T_o,Info_i,Info_o)
%------------------------------------------------------------------------%
% Imposes the depth bound in the input abstract term T obtaining the
% output abstract term T_o and the new info regarding annotation, new set
% of variables, non-linear variables (for pair sharing). 
%------------------------------------------------------------------------%
term_depth(Term,AEqs,0,'@'(Var_ec_i),
                    info(Ann_i,AVars_i,Var_ec_i,Sigma,ASGs_i,NLVars_i),
                    info(Ann_o,AVars_o,Var_ec_o,Sigma,ASGs_o,NLVars_o)) :- !,
%               Bound == 0 
    get_ann_aterm(AEqs,Term,Ann_T),
    aset(Var_ec_i,Ann_i,Ann_T,Ann_o),
    Var_ic_i is 1 << Var_ec_i,
    bitset_union(AVars_i,Var_ic_i,AVars_o),
    (ann_non_linear(Ann_T),!,bitset_union(NLVars_i,Var_ic_i,NLVars_o)
    ; NLVars_i = NLVars_o),
    Var_ec_o is Var_ec_i + 1,
    avariables_ec(Term,Avars_T_ec),
    update_asgs_list(Avars_T_ec,Var_ic_i,ASGs_i,ASGs_o) .
term_depth(T_Compound,AEqs,_Bound,'@'(Var_ec),
                    info(Ann_i,AVars_i,Var_ec_i,Sigma_i,ASGs_i,NLVars_i),
                    info(Ann_o,AVars_o,Var_ec_o,Sigma_o,ASGs_o,NLVars_o)) :-
%               atomic( Term ) 
    atomic(T_Compound),!, 
    (member((T_Compound,Var_ec),Sigma_i),!,
       Ann_i = Ann_o,AVars_i = AVars_o,Var_ec_i = Var_ec_o,
       Sigma_i = Sigma_o,ASGs_i = ASGs_o,NLVars_i = NLVars_o
       ; Var_ec = Var_ec_i,
      get_ann_aterm(AEqs,T_Compound,Ann_T),
      aset(Var_ec_i,Ann_i,Ann_T,Ann_o),
      Var_ic_i is 1 << Var_ec_i,
      bitset_union(AVars_i,Var_ic_i,AVars_o),
      (ann_non_linear(Ann_T),!,bitset_union(NLVars_i,Var_ic_i,NLVars_o)
    ; NLVars_i = NLVars_o),
    Var_ec_o is Var_ec_i + 1,
    Sigma_o = [(T_Compound,Var_ec_i) | Sigma_i ],
    avariables_ec(T_Compound,Avars_T_ec),
    update_asgs_list(Avars_T_ec,Var_ic_i,ASGs_i,ASGs_o)
    ) .
term_depth(Term,AEqs,_Bound,'@'(Var_ec_i),
                    info(Ann_i,AVars_i,Var_ec_i,Sigma,ASGs_i,NLVars),
                    info(Ann_o,AVars_o,Var_ec_o,Sigma,ASGs_o,NLVars)) :- 
    \+(Term = '@'(_)),
    ground_aeqs(AEqs,Term),!,
%               Term is ground
    aset(Var_ec_i,Ann_i,g,Ann_o),
    Var_ic_i is 1 << Var_ec_i,
    bitset_union(AVars_i,Var_ic_i,AVars_o),
    Var_ec_o is Var_ec_i + 1,
    avariables_ec(Term,Avars_T_ec),
    update_asgs_list(Avars_T_ec,Var_ic_i,ASGs_i,ASGs_o) .
term_depth(T_Compound,AEqs,Bound,T_Bound,Info_i,Info_o) :-
            %% Bound > 0,
    \+(T_Compound = '@'(_)),!,
    T_Compound =.. [F| Args],
    Limit is Bound-1,
    depth_bound_list(Args,AEqs,Limit,Args_depth,Info_i,Info_o),
    T_Bound =.. [F| Args_depth] .
term_depth(T_Compound,AEqs,_Bound,'@'(Var_ec),
                    info(Ann_i,AVars_i,Var_ec_i,Sigma_i,ASGs_i,NLVars_i),
                    info(Ann_o,AVars_o,Var_ec_o,Sigma_o,ASGs_o,NLVars_o)) :-
            %% Bound > 0, avar(T_Compound), 
    (member((T_Compound,Var_ec),Sigma_i),!,
    Ann_i = Ann_o,AVars_i = AVars_o,Var_ec_i = Var_ec_o,
    Sigma_i = Sigma_o,ASGs_i = ASGs_o,NLVars_i = NLVars_o
    ; Var_ec = Var_ec_i,
    get_ann_aterm(AEqs,T_Compound,Ann_T),
    aset(Var_ec_i,Ann_i,Ann_T,Ann_o),
    Var_ic_i is 1 << Var_ec_i,
    bitset_union(AVars_i,Var_ic_i,AVars_o),
    (ann_non_linear(Ann_T),!,bitset_union(NLVars_i,Var_ic_i,NLVars_o)
    ; NLVars_i = NLVars_o),
    Var_ec_o is Var_ec_i + 1,
    Sigma_o = [(T_Compound,Var_ec_i) | Sigma_i ],
    avariables_ec(T_Compound,Avars_T_ec),
    update_asgs_list(Avars_T_ec,Var_ic_i,ASGs_i,ASGs_o)
            ) .

depth_bound_list([],_,_,[],Info,Info) :- !.
depth_bound_list([H|T],AEqs,Limit,[Hdepth|Tdepth],Info_i,Info_o) :-
    term_depth(H,AEqs,Limit,Hdepth,Info_i,Info_new),
    depth_bound_list(T,AEqs,Limit,Tdepth,Info_new,Info_o).

%------------------------------------------------------------------------%
% aeq_det_ngroundvars(+,+,-)
% aeq_det_ngroundvars(Shr,Ann,NGrAVars)
%------------------------------------------------------------------------%
% Computes the set of possibly non-ground vars. If it is pair sharing,
% it has to look through Ann . Otherwise, it is the union of the 
% sharing sets. (this could also apply to pair-sharing but it is slower)
%------------------------------------------------------------------------%
aeq_det_ngroundvars(ps(_I,_E),Ann,NGrAVars) :- !,
    aeq_det_ngroundvars_array(Ann,NGrAVars) .
aeq_det_ngroundvars(Shr,_Ann,NGrAVars) :-
    bitset_union_list(Shr,NGrAVars) .

%-------------------------------------------------------------------------
% aeq_det_ngroundvars_array(+.-).
% aeq_det_ngroundvars_array(Array,NGrAVars).
% Returns in NGrAvars all variables in Array whose annotation is different 
% from 'g'.
%-------------------------------------------------------------------------
aeq_det_ngroundvars_array(array($(A0,A1,A2,A3),Size),NGrAVars) :-
    N is Size-2,
    aeq_det_ngroundvars_array(0,N,0,A0,0,L1),
    aeq_det_ngroundvars_array(1,N,0,A1,L1,L2),
    aeq_det_ngroundvars_array(2,N,0,A2,L2,L3),
    aeq_det_ngroundvars_array(3,N,0,A3,L3,NGrAVars).

aeq_det_ngroundvars_array(_K,_N,_M,$,L,L) :- ! .
aeq_det_ngroundvars_array(K,0,M,Val,Lin,Lout) :- !,
    (Val = g ->
        Lout = Lin
    ; N is K+M,N_ic is 1 << N,
      bitset_union(N_ic,Lin,Lout)).
aeq_det_ngroundvars_array(K,N,M,$(A0,A1,A2,A3),Lin,Lout):-
    N1 is N-2,
    M1 is (K+M)<<2,
    aeq_det_ngroundvars_array(0,N1,M1,A0,Lin,L0),
    aeq_det_ngroundvars_array(1,N1,M1,A1,L0,L1),
    aeq_det_ngroundvars_array(2,N1,M1,A2,L1,L2),
    aeq_det_ngroundvars_array(3,N1,M1,A3,L2,Lout).


%-------------------------------------------------------------------------
% aeq_impose_depth_bound_proj(+,-)
%-------------------------------------------------------------------------
aeq_impose_depth_bound_proj(AEqs_i,AEqs_o) :-
    current_bound(Depth,Type),
    ((Type == solve ; aeq_bounded(AEqs_i,Depth)),!,
         AEqs_o = AEqs_i
    ; aeq_impose_depth_bound(AEqs_i,Depth,AEqs_o)) .
%%      current_bound(Depth,_),
%%      aeq_impose_depth_bound(AEqs_i,Depth,AEqs_o).

    aeq_bounded(AEqs_i,Depth) :-
            AEqs_i = aeqs(Eqs,_,_,_,_),
            aeq_bounded_eqlist(Eqs,(0,0),Depth).

    aeq_bounded_eqlist([],_Vars,_Depth) .
    aeq_bounded_eqlist([_V = Term| Tail],Vars,Depth) :-
            aeq_bounded_mterm(Term,Vars,Depth,Vars_m),
            aeq_bounded_eqlist(Tail,Vars_m,Depth) .

    aeq_bounded_mterm(Term,(Vars,Vars_d),0,(Vars,Vars_d_o)) :- !,
            avar_ic(Term,Term_ic),
            not_bitset_member(Term_ic,Vars),
            not_bitset_member(Term_ic,Vars_d),
            bitset_union(Term_ic,Vars_d,Vars_d_o) .
    aeq_bounded_mterm(Term,Vars,_Depth,Vars) :-
            %% Depth > 0,
            (var(Term) ; atomic(Term)),!,
            fail .  %% REMARK : widening,to enforce collapsing numbers and
                    %%          atoms together.
    aeq_bounded_mterm(Term,(Vars,Vars_d),_Depth,(Vars_o,Vars_d)) :-
            %% Depth > 0,
            avar_ic(Term,Term_ic),!,
            not_bitset_member(Term_ic,Vars_d),
            bitset_union(Term_ic,Vars,Vars_o) .
    aeq_bounded_mterm(Term,Vars,Depth,Vars_o) :-
            %% Depth > 0,
            Term =.. [_F| Args],
            Limit is Depth-1,
            aeq_bounded_list(Args,Vars,Limit,Vars_o) .

    aeq_bounded_list([],Vars,_Depth,Vars) .
    aeq_bounded_list([Term| Tail],Vars_i,Depth,Vars_o) :-
            aeq_bounded_mterm(Term,Vars_i,Depth,Vars_m),
            aeq_bounded_list(Tail,Vars_m,Depth,Vars_o) .


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The follwoing predicates compute the abstract lub for the complete
% abstraction. It first computes the lub for the equations and annotation
% set. Then for the sharing, and finally computes the output non-ground 
% vars
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
aeq_lub(AEqs,'$bottom',AEqs) :- ! .
aeq_lub('$bottom',AEqs,AEqs) :- !.
aeq_lub(AEqs1,AEqs2,aeqs(Eqs,Ann,Shr,AVars,NGrAVars)) :-
    AEqs1 = aeqs(Eqs1,_,Shr1,_,NGr1),sort(Eqs1,Eqs1_s),
    AEqs2 = aeqs(Eqs2,_,Shr2,_,NGr2),sort(Eqs2,Eqs2_s),
    new_array(Ann_i), 
    new_array(ASGs1_i),new_array(ASGs2_i),
    aeq_lub_eqs_ann(Eqs1_s,AEqs1,Eqs2_s,AEqs2,Eqs,
                            ann_lub(Ann_i,0,0,0),
                            ann_lub(Ann,AVars,_Var_ec,NLin),
                            [],(ASGs1_i,ASGs2_i),ASGs_o),
    aeq_lub_shr(Shr1,Shr2,ASGs_o,NGr1,NGr2,NLin,Shr),
    aeq_det_ngroundvars(Shr,Ann,NGrAVars) .

%------------------------------------------------------------------------%
% aeq_lub_eqs_ann(Eqs1,AEqs1,Eqs2,AEqs2,Eqs,AnnLub0,AnnLub1,

%------------------------------------------------------------------------%
aeq_lub_eqs_ann([],_,[],_,[],Ann_lub,Ann_lub,_,ASGs,ASGs).
aeq_lub_eqs_ann([X = T1| Eqs1],AEqs1,[_Y = T2| Eqs2],AEqs2,[X = Tlub| Eqslub],
                    Ann_lub_i,Ann_lub_o,Sigma,ASGs_i,ASGs_o) :-
    term_lub(T1,AEqs1,T2,AEqs2,Tlub,Ann_lub_i,Ann_lub_new,
                    Sigma,Sigma_new,ASGs_i,ASGs_new),
    aeq_lub_eqs_ann(Eqs1,AEqs1,Eqs2,AEqs2,Eqslub,Ann_lub_new,Ann_lub_o,
                     Sigma_new,ASGs_new,ASGs_o) .

term_lub([],_AEqs1,[],_AEqs2,[],Ann_lub,Ann_lub,Sigma,Sigma,ASGs,ASGs) :- ! .
term_lub([H1|T1],AEqs1,[H2|T2],AEqs2,[Hlub|Tlub],Ann_lub_i,Ann_lub_o,
                    Sigma_i,Sigma_o,ASGs_i,ASGs_o) :- !,
            term_lub(H1,AEqs1,H2,AEqs2,Hlub,Ann_lub_i,Ann_lub_new,
                    Sigma_i,Sigma_new,ASGs_i,ASGs_new),
            term_lub(T1,AEqs1,T2,AEqs2,Tlub,Ann_lub_new,Ann_lub_o,
                    Sigma_new,Sigma_o,ASGs_new,ASGs_o).
term_lub(T1,AEqs1,T2,AEqs2,Tlub,Ann_lub_i,Ann_lub_o,
                    Sigma_i,Sigma_o,ASGs_i,ASGs_o) :-
            functor(T2,Func,Arity),functor(T1,Func,Arity),Func \== '@',!,
            functor(Tlub,Func,Arity),
            T2 =.. [Func |Args2],T1 =.. [Func |Args1],
            term_lub(Args1,AEqs1,Args2,AEqs2,Argslub,
                    Ann_lub_i,Ann_lub_o,
                    Sigma_i,Sigma_o,ASGs_i,ASGs_o),
             Tlub =.. [Func |Argslub] .
term_lub(T1,AEqs1,T2,AEqs2,'@'(Tlub_ec),Ann_lub_i,Ann_lub_o,
                    Sigma_i,Sigma_o,ASGs_i,ASGs_o) :-
            (member((T1,T2) - Tlub_ec,Sigma_i),!,
              Ann_lub_i = Ann_lub_o,
              Sigma_i = Sigma_o,ASGs_i = ASGs_o
            ; Ann_lub_i = ann_lub(Ann_i,AVars_i,Tlub_ec,NLin_i),
              Ann_lub_o = ann_lub(Ann_o,AVars_o,VN_o,NLin_o),
              aeq_lub_ann(T1,AEqs1,T2,AEqs2,Tlub_ec,Ann_i,Ann_o,Item),
              Tlub_ic is 1 << Tlub_ec,
              bitset_union(AVars_i,Tlub_ic,AVars_o),
              (ann_non_linear(Item),!,bitset_union(NLin_i,Tlub_ic,NLin_o)
              ; NLin_i = NLin_o),
              VN_o is Tlub_ec + 1,
              Sigma_o = [(T1,T2) - Tlub_ec | Sigma_i ],
              update_asgs(T1,T2,Tlub_ic,ASGs_i,ASGs_o)
            ) .

    update_asgs(T1,T2,Var_ic,(ASGs1_i,ASGs2_i),(ASGs1_o,ASGs2_o)) :-
            avariables_ec(T1,Avars1_ec),
            avariables_ec(T2,Avars2_ec),
            update_asgs_list(Avars1_ec,Var_ic,ASGs1_i,ASGs1_o),
            update_asgs_list(Avars2_ec,Var_ic,ASGs2_i,ASGs2_o) .

aeq_lub_ann(ATerm1,AEqs1,ATerm2,AEqs2,Tlub_ec,Ann_i,Ann_o,AnnTlub) :-
    get_ann_aterm(AEqs1,ATerm1,Ann1),
    get_ann_aterm(AEqs2,ATerm2,Ann2),
    ann_lub(Ann1,Ann2,AnnTlub),
    aset(Tlub_ec,Ann_i,AnnTlub,Ann_o) .

aeq_lub_shr(Shr1,Shr2,(ASGs1_i,ASGs2_i),NGr1,NGr2,NLin,Shr) :-
    (aeq_current_sharing(pair),!,
      aeq_lub_shr_accP(Shr1,ASGs1_i,NGr1,ps(NLin,[]),Sofar),
      aeq_lub_shr_accP(Shr2,ASGs2_i,NGr2,Sofar,Shr)
    ; aeq_lub_shr_accS(Shr1,ASGs1_i,[],Sofar),
      aeq_lub_shr_accS(Shr2,ASGs2_i,Sofar,Shr)
    ) .

aeq_lub_shr(Shr,ASGs_i,NGr,NLin,Shr_o) :-
    (aeq_current_sharing(pair),!,
      aeq_lub_shr_accP(Shr,ASGs_i,NGr,ps(NLin,[]),Shr_o)
    ; aeq_lub_shr_accS(Shr,ASGs_i,[],Shr_o)
    ) .

    aeq_lub_shr_accS([],_ASGs_i,Sofar,Sofar) .
    aeq_lub_shr_accS([SG|Tail_Shr],ASGs_i,Sofar,Shr) :-
            bitcode_to_set(SG,SG_ec),
            union_asgs(SG_ec,ASGs_i,0,U_ASG_SG),
            insert_groundSet(U_ASG_SG,Sofar,Sofar_new),
            aeq_lub_shr_accS(Tail_Shr,ASGs_i,Sofar_new,Shr) .

    aeq_lub_shr_accP(ps(InS,ExS),ASGs_i,NGr,PS_sofar,PS_out) :- !,
            bitcode_to_set_array(ASGs_i,ASGs_lic),
            bitcode_to_set(InS,InS_ec),
            lbitcode_to_llistS(ExS,ExS_ec),
            bitcode_to_set(NGr,NGr_ec),
            aeq_add_cartprod_In(InS_ec,ASGs_lic,PS_sofar,PS_M1),
            aeq_add_cartprod_Ex(ExS_ec,ASGs_lic,PS_M1,PS_M2),
            aeq_add_cartprod_Gr(NGr_ec,ASGs_lic,PS_M2,PS_out) .

    aeq_add_cartprod_Gr([],_ASGs_lic,PS,PS) .
    aeq_add_cartprod_Gr([NGr_ec|T],ASGs_lic,PS_i,PS_o) :-
            aref(NGr_ec,ASGs_lic,NGr_ASG_lic),
            aeq_add_cartprod_Gr(NGr_ASG_lic,PS_i,PS_m),
            aeq_add_cartprod_Gr(T,ASGs_lic,PS_m,PS_o) .

            aeq_add_cartprod_Gr([],PS,PS) .
            aeq_add_cartprod_Gr([_],PS,PS) :- !.
            aeq_add_cartprod_Gr([NGr_ic|T],PS_i,PS_o) :-
                    aeq_add_cartprod_Gr2(T,NGr_ic,PS_i,PS_m),
                    aeq_add_cartprod_Gr(T,PS_m,PS_o) .

            aeq_add_cartprod_Gr2([],_NGr_ic,PS,PS) .
            aeq_add_cartprod_Gr2([H_ic|T],NGr_ic,ps(I,E),ps(I_o,E_o)) :- !,
                    bitset_union(H_ic,NGr_ic,HNGr_ic),
                    insert_groundSet(HNGr_ic,E,E_m),
                    aeq_add_cartprod_Gr2(T,NGr_ic,ps(I,E_m),ps(I_o,E_o)) .

    aeq_add_cartprod_In([],_ASGs_lic,PS,PS) .
    aeq_add_cartprod_In([InS_ec|T],ASGs_lic,PS_i,PS_o) :-
            aref(InS_ec,ASGs_lic,InS_ASG_lic),
            aeq_add_cartprod_In(InS_ASG_lic,PS_i,PS_m),
            aeq_add_cartprod_In(T,ASGs_lic,PS_m,PS_o) .

            aeq_add_cartprod_In([],PS,PS) .
            aeq_add_cartprod_In([InS_ic],ps(I,E),ps(I_o,E)) :- !,
                     bitset_union(InS_ic,I,I_o) .
            aeq_add_cartprod_In([InS_ic|T],ps(I,E),PS_o) :-
                    bitset_union(InS_ic,I,I_m),
                    aeq_add_cartprod_Gr2(T,InS_ic,ps(I_m,E),PS_m),
                    aeq_add_cartprod_In(T,PS_m,PS_o) .

    aeq_add_cartprod_Ex([],_ASGs_lic,PS,PS) .
    aeq_add_cartprod_Ex([[E1_ec,E2_ec]|T],ASGs_lic,PS_i,PS_o) :-
            aref(E1_ec,ASGs_lic,E1_ASG_lic),
            aref(E2_ec,ASGs_lic,E2_ASG_lic),
            aeq_add_cartprod_Ex2(E1_ASG_lic,E2_ASG_lic,PS_i,PS_m),
            aeq_add_cartprod_Ex(T,ASGs_lic,PS_m,PS_o) .

            aeq_add_cartprod_Ex2([],_E2_ASG_lic,PS,PS) .
            aeq_add_cartprod_Ex2([H_ic|T],E2_ASG_lic,PS_i,PS_o) :- !,
                    aeq_add_cartprod_Ex3(E2_ASG_lic,H_ic,PS_i,PS_m),
                    aeq_add_cartprod_Ex2(T,E2_ASG_lic,PS_m,PS_o).

            aeq_add_cartprod_Ex3([],_NGr_ic,PS,PS) .
            aeq_add_cartprod_Ex3([H_ic|T],NGr_ic,ps(I,E),ps(I_o,E_o)) :- !,
                    (H_ic == NGr_ic,!,
                      bitset_union(NGr_ic,I,I_m),
                      aeq_add_cartprod_Ex3(T,NGr_ic,ps(I_m,E),ps(I_o,E_o))
                    ; bitset_union(H_ic,NGr_ic,HNGr_ic),
                      insert_groundSet(HNGr_ic,E,E_m),
                      aeq_add_cartprod_Ex3(T,NGr_ic,ps(I,E_m),ps(I_o,E_o))
                    ) .



%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% The following code implements the identity check betwen abstractions
% It does not depend on the annotation set
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% aeq_identical_nb(+,+,)
% aeq_identical_nb(ASub1,ASub2)
%-------------------------------------------------------------------------
% Satisfied iff the abstractions are identical up to renaming. This is true
% if: If the equations are identical (no renaming needed), then the 
% annotations and the sharing must also be identical. Otherwise, it first 
% checks the equations and the annotations, while doing this it computes
% the renaming in the array ASGs_i, and finally checks the sharing.
%-------------------------------------------------------------------------
aeq_identical_nb(aeqs(Eqs1,Ann1,Shr1,AVars_ic,_),aeqs(Eqs2,Ann2,Shr2,_,_)) :-
    sort(Eqs1,Eqs1_s),sort(Eqs2,Eqs2_s),sort_sh(Shr2,Shr2_s),
    ( Eqs1_s == Eqs2_s ->
        sort_sh(Shr1,Shr2_s),
        bitcode_to_set(AVars_ic,SetVars),
        aeq_iden_ann(SetVars,Ann1,Ann2)
    ;   new_array(Sigma_i),
        new_array(ASGs_i),
        aeq_iden_eqs_ann(Eqs1_s,Ann1,Eqs2_s,Ann2,Sigma_i,ASGs_i,ASGs_o),
        shr_rename(Shr1,ASGs_o,Shr1_ren),
        sort_sh(Shr1_ren,Shr2_s)).

sort_sh(ps(X,Y_u),Sort):- !,
    Sort = ps(X,Y),
    sort(Y_u,Y).
sort_sh(X_u,X):- 
    sort(X_u,X).

aeq_iden_ann([],_,_).
aeq_iden_ann([Var_ec|SetVars],Ann1,Ann2):-
    aref( Var_ec, Ann1, A ),
    aref( Var_ec, Ann2, A ),
    aeq_iden_ann(SetVars,Ann1,Ann2).

%-------------------------------------------------------------------------
% aeq_iden_eqs_ann(+,+,+,+,+,+,-)
% aeq_iden_eqs_ann(Eqs1,Ann1,Eqs2,Ann2,Sigma_i,ASGs_i,ASGs_o),
%-------------------------------------------------------------------------
% It checks that Eqs1 and Eqs2 are identical up to renaming of their 
% abstract variables. While doing this, it also checks that those abstract 
% variables have the same annotation in their corresponding abstractions, 
% and it creates an array (ASGS) in which the bitcode of each abstract 
% variable in Eqs2 appears in the position of its "renamed" variable in 
% Eqs1 (so that this renaming can be used later for renaming the sharing).
%-------------------------------------------------------------------------
aeq_iden_eqs_ann([],_,[],_,_,ASGs,ASGs).
aeq_iden_eqs_ann([_=T1| Eqs1],Ann1,[_=T2| Eqs2],Ann2,Sigma,ASGs_i,ASGs_o) :-
    avar_renaming(T1,Ann1,T2,Ann2,Sigma,Sigma_new,ASGs_i,ASGs_new),
    aeq_iden_eqs_ann(Eqs1,Ann1,Eqs2,Ann2,Sigma_new,ASGs_new,ASGs_o) .

avar_renaming('@'(T1_ec),Ann1,T2,Ann2,Sigma_i,Sigma_o,ASGs_i,ASGs_o) :- !,
    T2 = '@'(T2_ec),
    arefl(T2_ec,Sigma_i,T2_sigma),
    (T2_sigma == [] ->
         arefl(T1_ec,ASGs_i,T1_sigma),T1_sigma == [],
         aref(T1_ec,Ann1,A),
         aref(T2_ec,Ann2,A),
         aset(T2_ec,Sigma_i,T1_ec,Sigma_o),
         T2_ic is 1 << T2_ec,
         update_asgs_list([T1_ec],T2_ic,ASGs_i,ASGs_o)
     ; T2_sigma == T1_ec, Sigma_i = Sigma_o,ASGs_i = ASGs_o).
avar_renaming([],_Ann1,[],_Ann2,Sigma,Sigma,ASGs,ASGs) :- ! .
avar_renaming([H1|T1],Ann1,[H2|T2],Ann2,Sigma_i,Sigma_o,ASGs_i,ASGs_o) :- !,
    avar_renaming(H1,Ann1,H2,Ann2,Sigma_i,Sigma_new,ASGs_i,ASGs_new),
    avar_renaming(T1,Ann1,T2,Ann2,Sigma_new,Sigma_o,ASGs_new,ASGs_o).
avar_renaming(T1,Ann1,T2,Ann2,Sigma_i,Sigma_o,ASGs_i,ASGs_o) :-
    functor(T2,Func,Arity),functor(T1,Func,Arity),
    avar_renaming(Arity,T1,Ann1,T2,Ann2,Sigma_i,Sigma_o,ASGs_i,ASGs_o).

avar_renaming(0,_,_,_,_,Sigma,Sigma,ASGs,ASGs):- !.
avar_renaming(Arity,T1,Ann1,T2,Ann2,Sigma_i,Sigma_o,ASGs_i,ASGs_o):-
    arg(Arity,T1,Arg1),
    arg(Arity,T2,Arg2),
    avar_renaming(Arg1,Ann1,Arg2,Ann2,Sigma_i,Sigma_m,ASGs_i,ASGs_m),
    Arity0 is Arity - 1,
    avar_renaming(Arity0,T1,Ann1,T2,Ann2,Sigma_m,Sigma_o,ASGs_m,ASGs_o).

%-------------------------------------------------------------------------
% shr_rename(+,+,-)
% shr_rename(Shr,Array,Shr_ren)
%-------------------------------------------------------------------------
% Renames Shr according to Array. Shr can be set or pair sharing.
% ATTENTION: I have changed this completely, hope it is correct.
%-------------------------------------------------------------------------
shr_rename([],_ASGs_array,[]) .
shr_rename([SG |Tail],ASGs_array,[SG_ren |Tail_ren]) :-
    bitcode_to_set(SG,SG_ec),
    union_asgs(SG_ec,ASGs_array,0,SG_ren),
    shr_rename(Tail,ASGs_array,Tail_ren) .
shr_rename(ps(InS,ExS),ASGs_array,ps(InS_ren,ExS_ren)) :- 
    bitcode_to_set(InS,InS_ec),
    union_asgs(InS_ec,ASGs_array,0,InS_ren),
    shr_rename(ExS,ASGs_array,ExS_ren).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% The following code correspondes to the less_or_equal operation
% It does not depend on the annotation set
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

%% :- mode
%%      aeq_leq_nb(+,+),                  %  AEqs1 (<> $bottom),AEqs2 (<> $bottom) ?
%%      aeq_leq_eqs_ann(+,+,+,+,+,+,-),   %  Eqs1_s,AEqs1,Eqs2_s,AEqs2,Sigma_array,
%%                                        %             ASGs_Acc_array -> ASGs_array
%%         can_be_mapped(+,+,+,+,+,-,+,-),%  AT1,AEqs1,AT2,AEqs2,Sigma_Acc -> Sigma,
%%                                        %             ASGs_Acc_array -> ASGs_array
%%         update_asgs(+,+,+,-),          %  AV2_sigma,AV2,ASGs_Acc_array -> ASGs_array
%%         update_asgs_list(+,+,+,-),     %  AVars1_ec,AV2_ic,ASGs_Acc_array
%%                                        %                      -> ASGs_array
%%      aeq_leq_ann(+,+,+,+),             %  ATerm1,AEqs1,ATerm2,AEqs2 ?
%%      aeq_leq_shr(+,+,+,+),             %  Shr1,Shr2,ASGs,NGr1 ?
%%      aeq_leq_shr(+,+,+),               %  Shr1,Shr2,ASGs ?
%%         union_asgs(+,+,+,-) .          %  SG1_ec,ASGs_array,U_ASG_Acc -> U_ASG

%-------------------------------------------------------------------------
% aeq_leq_nb(+,+)
% aeq_leq_nb(AEqs1,AEqs2)
%-------------------------------------------------------------------------
% Satisfied iff AEqs1 is less or equal than AEqs2. Very similar than to
% the one above, but rather than a renaming, we are looking for a mapping
% from one to another (a substitution that applied to AEqs2 returns AEqs1)
% 
% Assumptions: They are not '$bottom'
%-------------------------------------------------------------------------
aeq_leq_nb(AEqs1,AEqs2) :-
    AEqs1 = aeqs(Eqs1,_,Shr1,_,_),
    AEqs2 = aeqs(Eqs2,_,Shr2,_,_),
    sort(Eqs1,Eqs1_s),sort(Eqs2,Eqs2_s),
    new_array(Sigma_i),new_array(ASGs_i),
    aeq_leq_eqs_ann(Eqs1_s,AEqs1,Eqs2_s,AEqs2,Sigma_i,ASGs_i,ASGs_o),
    aeq_leq_shr(Shr1,Shr2,ASGs_o).

aeq_leq_eqs_ann([],_,[],_,_,ASGs,ASGs).
aeq_leq_eqs_ann([_=T1|Eqs1],AEqs1,[_=T2|Eqs2],AEqs2,Sigma,ASGs_i,ASGs_o) :-
    can_be_mapped(T1,AEqs1,T2,AEqs2,Sigma,Sigma_new,ASGs_i,ASGs_new),
    aeq_leq_eqs_ann(Eqs1,AEqs1,Eqs2,AEqs2,Sigma_new,ASGs_new,ASGs_o) .

can_be_mapped([],_AEqs1,[],_AEqs2,Sigma,Sigma,ASGs,ASGs) :- ! .
can_be_mapped([H1|T1],AEqs1,[H2|T2],AEqs2,Sigma_i,Sigma_o,ASGs_i,ASGs_o) :- !,
    can_be_mapped(H1,AEqs1,H2,AEqs2,Sigma_i,Sigma_new,ASGs_i,ASGs_new),
    can_be_mapped(T1,AEqs1,T2,AEqs2,Sigma_new,Sigma_o,ASGs_new,ASGs_o).
can_be_mapped(T1,AEqs1,'@'(T2_ec),AEqs2,Sigma_i,Sigma_o,ASGs_i,ASGs_o) :- !,
    arefl(T2_ec,Sigma_i,T2_sigma),
    (T2_sigma == [] ->
        aeq_leq_ann(T1,AEqs1,'@'(T2_ec),AEqs2),
        aset(T2_ec,Sigma_i,T1,Sigma_o),
        update_asgs(T1,'@'(T2_ec),ASGs_i,ASGs_o)
    ;  T2_sigma == T1,
       Sigma_i = Sigma_o,ASGs_i = ASGs_o ) .
can_be_mapped(T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o,ASGs_i,ASGs_o) :-
    functor(T2,Func,Arity),functor(T1,Func,Arity),
    can_be_mapped(Arity,T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o,ASGs_i,ASGs_o).

can_be_mapped(0,_,_,_,_,Sigma,Sigma,ASGs,ASGs):- !.
can_be_mapped(Arity,T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o,ASGs_i,ASGs_o):-
    arg(Arity,T1,Arg1),
    arg(Arity,T2,Arg2),
    can_be_mapped(Arg1,AEqs1,Arg2,AEqs2,Sigma_i,Sigma_m,ASGs_i,ASGs_m),
    Arity0 is Arity - 1,
    can_be_mapped(Arity0,T1,AEqs1,T2,AEqs2,Sigma_m,Sigma_o,ASGs_m,ASGs_o).

%-------------------------------------------------------------------------
% aeq_leq_ann(+,+,+,+)
% aeq_leq_ann(T1,AEqs1,T2,AEqs2)
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
aeq_leq_ann(T1,AEqs1,T2,AEqs2) :-
    get_ann_aterm(AEqs1,T1,T1_Ann),
    get_ann_aterm(AEqs2,T2,T2_Ann),
    ann_leq(T1_Ann,T2_Ann).

%-------------------------------------------------------------------------
% aeq_leq_shr(+,+,-)
% aeq_leq_shr(Shr1,Shr2,ASGs_array)
%-------------------------------------------------------------------------
% Satisfied if each element of Shr1, afetr being renamed according to the
% arrary, is an element of of Shr2. 
% ATTENTION: I have changed this completely, hope it is correct.
%-------------------------------------------------------------------------
aeq_leq_shr([],_Shr2,_ASGs_array) .
aeq_leq_shr([SG1 |Tail_Shr1],Shr2,ASGs_array) :-
    bitcode_to_set(SG1,SG1_ec),
    union_asgs(SG1_ec,ASGs_array,0,U_ASG_SG1),
    member(U_ASG_SG1,Shr2),!,
    aeq_leq_shr(Tail_Shr1,Shr2,ASGs_array) .
aeq_leq_shr(ps(In1,Ex1),ps(In2,Ex2),ASGs_array) :-
    bitset_subset(In1,In2),
    aeq_leq_shr(Ex1,Ex2,ASGs_array).

%-------------------------------------------------------------------------
% update_asgs(+,+,+,-)
% update_asgs(ATerm,AVar,ASGs_i,ASG_o)
%-------------------------------------------------------------------------
% It adds the bitcode of AVar to the position in ASGs_i of each abstract 
% variable in ATerm (if no position existed for some variable, it sets
% a new one to the bitcode).
%-------------------------------------------------------------------------
update_asgs(T1,'@'(T2),ASGs_i,ASGs_o) :-
    avariables_ec(T1,Avars_ec),
    T2_ic is 1 << T2,
    update_asgs_list(Avars_ec,T2_ic,ASGs_i,ASGs_o) .

update_asgs_list([],_T2_ic,ASGs,ASGs) .
update_asgs_list([Avar_ec| Avars],T2_ic,ASGs_i,ASGs_o) :-
    arefl(Avar_ec,ASGs_i,Avar_ASG),
    (Avar_ASG == [] ->
        aset(Avar_ec,ASGs_i,T2_ic,ASGs_new)
    ;  bitset_union(Avar_ASG,T2_ic,Avar_ASG_new),
       aset(Avar_ec,ASGs_i,Avar_ASG_new,ASGs_new)),
    update_asgs_list(Avars,T2_ic,ASGs_new,ASGs_o) .

%-------------------------------------------------------------------------
% union_asgs(_,_,_,-)
% union_asgs(LNum,Array,Acc,NewLNum),
%-------------------------------------------------------------------------
% For each Var_ec in LNum, it adds to Acc the bitcode in Array with position
% Var_ec
%-------------------------------------------------------------------------
union_asgs([],_,U_ASG,U_ASG) .
union_asgs([Var_ec | Tail],ASGs_array,U_ASG_i,U_ASG_o) :-
    aref(Var_ec,ASGs_array,Var_ASG),
    bitset_union(U_ASG_i,Var_ASG,U_ASG_m),
    union_asgs(Tail,ASGs_array,U_ASG_m,U_ASG_o) .

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% The following are the operations related to the entry and exit operations
% They do not depend on the anotation set (except for the anotation of free)
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% aeq_parameter_passing_proj(+,+,+,-)
% aeq_parameter_passing_proj(Eq,CVars,AEqs,AEqs_out) 
%-------------------------------------------------------------------------
% Eq is an equation resulting from the unification of a Head and a Subgoal.
% CVars is the set of Hv+Fv. This predicate performs the preliminary work 
% for adding the equation Eq to the abstraction AEqs. In particular, it
% first initializes the vars in CVars as new vars, then 
%-------------------------------------------------------------------------
aeq_parameter_passing_proj(Eq,CVars,AEqs,AEqs_out) :-
    (aeq_current_sharing(pair) ->
      aeq_init_new_varsPS(CVars,0,AEqs,AEqs_new)
    ; aeq_init_new_vars(CVars,0,AEqs,AEqs_new)),
    aeq_add_equation_proj(Eq,CVars,AEqs_new,AEqs_out) .

%-------------------------------------------------------------------------
% aeq_init_new_vars(+,+,+,+,-)
% aeq_init_new_vars(NewVars,Free_ann,Num,AEqs,AEqs_new)
%-------------------------------------------------------------------------
% It initializes the vars in NewVars as new vars in the abstraction by 
% (a) adding them to Eqs with the appropriate unused AVar number, (b) 
% annotating them as free_vars in the annotation array and (b) adding
% them to the set sharing as singletons (in pair sharing, the next
% predicate, this is not needed).
%-------------------------------------------------------------------------
aeq_init_new_vars([],_,Aeqs,Aeqs) .
aeq_init_new_vars([CVar|CVars],Nb_i,aeqs(Eqs_i,Ann_i,Shr,AVars_i,NGrAVars_i),Aeqs_o):-
    aeq_select_unused_var(Nb_i,AVars_i,Nb_ec,Nb_ic),
    AVars is AVars_i \/ Nb_ic,
    NGrAVars is NGrAVars_i \/ Nb_ic,
    aset(Nb_ec,Ann_i,f,Ann),
    Nb_new is Nb_ec + 1,
    aeq_init_new_vars(CVars,Nb_new,
            aeqs([CVar='@'(Nb_ec)|Eqs_i],Ann,[Nb_ic| Shr],AVars,NGrAVars),Aeqs_o) .

aeq_init_new_varsPS([],_Nb,Aeqs,Aeqs).
aeq_init_new_varsPS([CVar|CVars],Nb_i,aeqs(Eqs_i,Ann_i,Shr,AVars_i,NGrAVars_i),Aeqs_o):-
    aeq_select_unused_var(Nb_i,AVars_i,Nb_ec,Nb_ic),
    AVars is AVars_i \/ Nb_ic,
    NGrAVars is NGrAVars_i \/ Nb_ic,
    aset(Nb_ec,Ann_i,f,Ann),
    Nb_new is Nb_ec + 1,
    aeq_init_new_varsPS(CVars,Nb_new,
            aeqs([CVar='@'(Nb_ec)|Eqs_i],Ann,Shr,AVars,NGrAVars),Aeqs_o) .

%-------------------------------------------------------------------------
% aeq_select_unused_var(+,+,-,-)
% aeq_select_unused_var(Nb,AVars_ic,Nb_ec,Nb_ic)
%-------------------------------------------------------------------------
% Returns the lowest number (and its bitcode) which is not already 
% represented by the bitsetcode AVars_ic.
%-------------------------------------------------------------------------
aeq_select_unused_var(Nb,AVars_ic,Nb_ec,Nb_ic) :-
    Var_ic is 1 << Nb,
    (bitset_member(Var_ic,AVars_ic) ->
      Nb_new is Nb + 1,
      aeq_select_unused_var(Nb_new,AVars_ic,Nb_ec,Nb_ic)
    ; Nb_ec = Nb,Nb_ic = Var_ic).

aeq_parameter_passing_rem(Eq,CVars,AEqs,AEqs_out) :-
    (aeq_current_sharing(pair) ->
      aeq_init_new_varsPS(CVars,0,AEqs,AEqs_new)
    ; aeq_init_new_vars(CVars,0,AEqs,AEqs_new)),
    aeq_add_equation_rem(Eq,CVars,AEqs_new,AEqs_out) .

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% The following predicates correspond to the abstract unification
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

%-------------------------------------------------------------------------
% aeq_solve(+,-)
% aeq_solve(Aeqs_i,Aeqs_o)
%-------------------------------------------------------------------------
% Aeqs_i is an intermediate abstraction with the only difference w.r.t.
% a normal one that the first component is eqs(SF,ListAEq,End), where
% SF is the normal set of abstract equations, ListAEq is the list of new 
% concrete equations to be added, and End is its tail. This predicate
% first adds all this new concrete equations and then imposes the depth
% bound if necessary.
%-------------------------------------------------------------------------
aeq_solve(Aeqs_i,Aeqs_o) :- 
    (aeq_current_sharing(pair) ->
      aeq_solve_tr(Aeqs_i,ps,Aeqs_o_nb)
    ; aeq_solve_tr(Aeqs_i,ss,Aeqs_o_nb)),
    aeq_impose_depth_bound(Aeqs_o_nb,Aeqs_o).

aeq_solve_tr('$bottom',_,'$bottom').
aeq_solve_tr(aeqs(eqs(Sf,NSf,End),Ann,Shr,AVars,NGrAVars),ShFg,Aeqs) :-
    ( NSf == End ->
        Aeqs = aeqs(Sf,Ann,Shr,AVars,NGrAVars)
    ; ( NSf = [AEq|Rest] ->
          aeq_solve_equation(AEq,ShFg,aeqs(eqs(Sf,Rest,End),Ann,Shr,AVars,NGrAVars),Aeqs_tmp),
          aeq_solve_tr(Aeqs_tmp,ShFg,Aeqs)
      ; Aeqs = aeqs(eqs(Sf,NSf,End),Ann,Shr,AVars,NGrAVars))).

%-------------------------------------------------------------------------
% aeq_solve_equation(+,+,+,-)
% aeq_solve_equation(Eq,ShFg,Aeqs,Aeqs_o)
%-------------------------------------------------------------------------
% Eq is the new concrete equation. It s either of the form T1 = T2, or of
% the form asubst(T1=T2). The latter means that the equation has already
% been "seen" before but it was postponed, because there might be still 
% grounding equations to processed. It proceeds as follows. It first
% checks is 
%-------------------------------------------------------------------------
aeq_solve_equation(asubst(AT1 = AT2),ShFg,Aeqs,Aeqs_o):-
    avariables_ic(AT2,AT2_ic),
    aeq_one(ShFg,AT1,AT2,AT2_ic,Aeqs,Aeqs_o) .
aeq_solve_equation(AT1 = AT2,ShFg,Aeqs,Aeqs_o):-
    ( AT1 == AT2 ->
        Aeqs = aeqs(Eqs,_,_,_,_),
        avariables_ic(Eqs,AVars_proj),
        aeq_project_vars(AVars_proj,Eqs,Aeqs,Aeqs_o)
    ; ( avar_ic(AT1,AT1_ic) ->
          aeq_solve_equation_one_var(AT1,AT1_ic,AT2,ShFg,Aeqs,Aeqs_o)
      ;  ( avar_ic(AT2,AT2_ic) ->
               aeq_solve_equation_one_var(AT2,AT2_ic,AT1,ShFg,Aeqs,Aeqs_o)
         ; functor(AT1,F,AR),
           ( functor(AT2,F,AR) ->
               AT1 =..[ F | Args1 ],
               AT2 =..[ F | Args2 ],
               Aeqs = aeqs(eqs(Sf,NSf,End),Ann,Shr,AVars,NGrAVars),
               aeq_add_equations(Args1,Args2,NSf,NSf_new),
               Aeqs_o = aeqs(eqs(Sf,NSf_new,End),Ann,Shr,AVars,NGrAVars)
           ; Aeqs_o = '$bottom')))).

%-------------------------------------------------------------------------
% aeq_solve_equation_one_var(+,+,+,+,+,-)
% aeq_solve_equation_one_var(AT1,AT1_ic,AT2,ShFg,Aeqs,Aeqs_o)
%-------------------------------------------------------------------------
% Abstract unification of AT1 = AT2 where AT1 is known to be an abstract var
%-------------------------------------------------------------------------
aeq_solve_equation_one_var(AT1,AT1_ic,AT2,_,aeqs(eqs(Sf,NSf,End),Ann,Shr,AVars,NGrAVars),AEqs_o):- 
    avariables_ic(AT2,AT2_ic),
    (bitset_member(AT1_ic,AT2_ic) ->
      AEqs_o = '$bottom'
    ; ( (bitset_intersect(AT1_ic,NGrAVars,0) ; bitset_intersect(AT2_ic,NGrAVars,0)) ->
         bitset_union(AT1_ic,AT2_ic,Gr),
         aeq_make_ground(Gr,aeqs(Sf,Ann,Shr,AVars,NGrAVars),aeqs(_,TmpAnn_o,Shr_o,_,TmpNGrAVars_o)),
         avariables_ic([Sf|NSf],AVars_o),
         bitset_intersect(TmpNGrAVars_o,AVars_o,NGrAVars_o),
         aeq_project_ann(TmpAnn_o,AVars_o,Ann_o),
         AEqs_o = aeqs(eqs(Sf,NSf,End),Ann_o,Shr_o,AVars_o,NGrAVars_o)
       ; aeq_substitute_avar(Sf,AT1,AT2,Sf_new),
         aeq_substitute_avar(NSf,AT1,AT2,NSf_new),
         End = [ asubst(AT1 = AT2) |New_end],
         AEqs_o = aeqs(eqs(Sf_new,NSf_new,New_end),Ann,Shr,AVars,NGrAVars)
      )
    ) .

aeq_one(ps,AT1,AT2,AT2_ic,Aeqs,Aeqs_o):-
    aeq_sondergaard(AT1,AT2,AT2_ic,Aeqs,Aeqs_o).
aeq_one(ss,AT1,AT2,AT2_ic,Aeqs,Aeqs_o):-
    aeq_jacobs_langen(AT1,AT2,AT2_ic,Aeqs,Aeqs_o).


aeq_add_equations([],[],Eqs,Eqs) .
aeq_add_equations([H1|T1],[H2|T2],Tail,[H1=H2|Tail_new]) :-
    aeq_add_equations(T1,T2,Tail,Tail_new) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

aeq_sondergaard(A,T,T_ic,AEqs,
               aeqs(Eqs_nsf,Ann_o,Shr_o,AVars_o,NGrAVars_o)) :-
    get_Eqs_Ann_aeqs(AEqs,Eqs_nsf,Ann_i),
    avariables_ic(Eqs_nsf,AVars_o),
    shr_sondergaard(A,T,T_ic,AEqs,NGrAVars_o,AVars_o,Shr_o),
    ann_jacobs_langen(Ann_i,info(A,T,T_ic,AEqs,AVars_o,NGrAVars_o),Ann_o) .

    shr_sondergaard(A,T,T_ic,AEqs,NGrAVars_o,AVars_o,Shr_o) :-
            AEqs = aeqs(_,_Ann,Shr_i,_AVars,NGrAVars),
            avar_ic(A,A_ic),
            bitset_union(A_ic,T_ic,AT_ic),
            %%  REMARK : the next OR-construct is an optimisation assuming that
            %%              the occur-check is performed
            (free_aeqs(AEqs,A),compound_aeqs(AEqs,T),!,
              delta_bar_ShrP(Shr_i,A_ic,T_ic,AT_ic,Shr,Delta_AT,Delta_Bar)
            ; aeq_split_intersect_disjoint(Shr_i,AT_ic,Delta_AT,Delta_Bar),
              Shr = Shr_i),
            ((bitset_intersect(A_ic,NGrAVars,0)
              ; bitset_intersect(T_ic,NGrAVars,0)),!,
              Shr_o = Delta_Bar,
              bitset_subtract(NGrAVars,AT_ic,NGrAVars_o)
            ; bitset_intersect(T_ic,NGrAVars,NGrT_ic),
              newshr_sondergaard(A,A_ic,T,NGrT_ic,AEqs,New_Shr),
              aeq_paths3(Delta_AT,New_Shr,Paths3),
              aeq_union_shrP(Shr,New_Shr,Paths3,Shr_oo),
              aeq_project_shrP(Shr_oo,AVars_o,Shr_o),
              bitset_intersect(AVars_o,NGrAVars,NGrAVars_o) 
            ) .

    aeq_paths3(ps(_I_old,E_old),ps(I_new,E_new),Paths3) :-
            aeq_E_new(E_new,E_old,ps(0,[]),Paths3_m),
            bitcode_to_listofbitcode(I_new,I_list),
            aeq_I_new(I_list,E_old,Paths3_m,Paths3) . 

    aeq_I_new([],_E_old,Paths3,Paths3) .
    aeq_I_new([H_n|T_n],E_old,Paths3i,Paths3o) :-
            aeq_I_aux(E_old,H_n,Paths3i,Paths3m),
            aeq_I_new(T_n,E_old,Paths3m,Paths3o) .

    aeq_I_aux([],_H_n,Paths3,Paths3) .
    aeq_I_aux([H_o|T_o],H_n,ps(I,E),Paths3o) :-
            bitset_member(H_n,H_o),!,
            bitset_subtract(H_o,H_n,Ai),
            bitset_union(Ai,I,I_new),
            aeq_paths3_aux3(T_o,H_n,Ai,ps(I_new,E),Paths3m),
            aeq_I_aux(T_o,H_n,Paths3m,Paths3o) .
    aeq_I_aux([_H_o|T_o],H_n,Paths3i,Paths3m) :-
            aeq_I_aux(T_o,H_n,Paths3i,Paths3m) .

    aeq_E_new([],_E_old,Paths3,Paths3) .
    aeq_E_new([H_n|T_n],E_old,ps(I1,E1),ps(I2,E2)) :-
            bitcode_to_listofbitcode(H_n,[Ak,Aj]),
            aeq_paths3_aux(E_old,Ak,Aj,ps(I1,E1),ps(I,E)),
            aeq_E_new(T_n,E_old,ps(I,E),ps(I2,E2)) .

    aeq_paths3_aux([],_Ak,_Aj,PS,PS) .
    aeq_paths3_aux([H_o|T_o],Ak,Aj,ps(I1,E1),PS) :-
            bitset_member(Ak,H_o),!,
            bitset_subtract(H_o,Ak,Ai),
            (Ai == Aj,!,
              bitset_union(I1,Aj,I1_new),
              aeq_paths3_aux3(T_o,Aj,Aj,ps(I1_new,E1),PS_m)
            ; bitset_union(Aj,Ai,Aji),
              insert_groundSet(Aji,E1,E1_new),
              aeq_paths3_aux3(T_o,Aj,Ai,ps(I1,E1_new),PS_m)
            ),
            aeq_paths3_aux(T_o,Ak,Aj,PS_m,PS) .
    aeq_paths3_aux([H_o|T_o],Ak,Aj,ps(I1,E1),PS) :-
            bitset_member(Aj,H_o),!,
            bitset_subtract(H_o,Aj,Ai),
            bitset_union(Ak,Ai,Aki),
            insert_groundSet(Aki,E1,E1_new),
            aeq_paths3_aux3(T_o,Ak,Ai,ps(I1,E1_new),PS_m),
            aeq_paths3_aux(T_o,Ak,Aj,PS_m,PS) .
    aeq_paths3_aux([_H_o|T_o],Ak,Aj,PSi,PSo) :-
            aeq_paths3_aux(T_o,Ak,Aj,PSi,PSo) .

    aeq_paths3_aux3([],_Aj,_Ai,PS,PS) .
    aeq_paths3_aux3([H_o|T_o],Aj,Ai,ps(I1,E1),PS) :-
            bitset_member(Aj,H_o),!,
            bitset_subtract(H_o,Aj,Al),
            (Ai == Al,!,
              bitset_union(I1,Ai,I1_new),
              aeq_paths3_aux3(T_o,Aj,Ai,ps(I1_new,E1),PS)
            ; bitset_union(Al,Ai,Ali),
              insert_groundSet(Ali,E1,E1_new),
              aeq_paths3_aux3(T_o,Aj,Ai,ps(I1,E1_new),PS)
            ) .
    aeq_paths3_aux3([_H_o|T_o],Aj,Ai,PSi,PSo) :-
            aeq_paths3_aux3(T_o,Aj,Ai,PSi,PSo) .

    aeq_union_shrP(ps(I1,E1),ps(I2,E2),ps(I3,E3),ps(I123,E123)) :- 
            bitset_union(I1,I2,I12),
            bitset_union(I12,I3,I123),
            union(E2,E1,E12),
            union(E3,E12,E123) .

    newshr_sondergaard(A,A_ic,T,NGrT_ic,AEqs,PShr_o) :-
            bitcode_to_listofbitcode(NGrT_ic,NGrT_lic),
            aeq_add_cartprod_SP(NGrT_lic,A_ic,E),
            (linear_aeqs(AEqs,A),!,
              (linear_aeqs(AEqs,T),!,
                PShr_o = ps(0,E)
              ; PShr_o = ps(A_ic,E)
             )
            ; (linear_aeqs(AEqs,T),!,
                aeq_add_cartprod_In(NGrT_lic,ps(0,E),PShr_o)
              ; aeq_add_cartprod_In(NGrT_lic,ps(A_ic,E),PShr_o)
             )
            ) .

    aeq_add_cartprod_SP([],_A_ic,[]) .
    aeq_add_cartprod_SP([H_ic|T],A_ic,[AH_ic|E]) :- !,
            bitset_union(H_ic,A_ic,AH_ic),
            aeq_add_cartprod_SP(T,A_ic,E) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

aeq_jacobs_langen(A,T,T_ic,AEqs,
               aeqs(Eqs_nsf,Ann_o,Shr_o,AVars_o,NGrAVars_o)) :-
    avar_ic(A,A_ic),
    test_occur(AEqs,A,A_ic,T,T_ic,Eqs_nsf,Ann_i,AEqs_i),!,
    avariables_ic(Eqs_nsf,AVars_o),
    shr_jacobs_langen(A,A_ic,T,T_ic,AEqs_i,AVars_o,Shr_o),
    bitset_union_list(Shr_o,NGrAVars_o),
    ann_jacobs_langen(Ann_i,info(A,T,T_ic,AEqs_i,AVars_o,NGrAVars_o),Ann_o) .
aeq_jacobs_langen(_A,_T,_T_ic,_AEqs,'$bottom') .

    test_occur(AEqs,A,A_ic,T,T_ic,Eqs_nsf,Ann,AEqs_o) :-
            %%  REMARK : the next OR-construct is an optimisation assuming that
            %%              the occur-check is performed
            AEqs = aeqs(Eqs_nsf,Ann,Shr,AVarSet,NGrAVars),
            (free_aeqs(AEqs,A),compound_aeqs(AEqs,T),!,
              aeq_split_intersect(Shr,A_ic,T_ic,Shr_o),
              bitset_union_list(Shr_o,NGrAVars_o),
              bitset_subtract(NGrAVars,NGrAVars_o,NowGr),
              (NowGr == 0 ;
                ann_free_vars(Ann,FreeVars),
                bitset_intersect(FreeVars,NowGr,0)
             ),!,
              AEqs_o = aeqs(Eqs_nsf,Ann,Shr_o,AVarSet,NGrAVars_o)
            ; AEqs_o = AEqs) .


    shr_jacobs_langen(A,A_ic,T,T_ic,AEqs,AVars_o,Shr_o) :-
            AEqs = aeqs(_,_Ann,Shr,_AVars,NGrAVars),
            delta_Shr(Shr,A_ic,T_ic,Delta_A,Delta_T,Delta_Bar),
            ((bitset_intersect(A_ic,NGrAVars,0)
              ; bitset_intersect(T_ic,NGrAVars,0)),!,
              Shr_o = Delta_Bar
            ; (free_aeqs(AEqs,A) ; free_aeqs(AEqs,T)),!,
%                 single_set_closure(Delta_A,Delta_T,Delta_Bar,Shr_oo), % us_l
              sort(Delta_Bar,Delta_Bar_s),                          % s_l
              single_set_closure(Delta_A,Delta_T,Delta_Bar_s,Shr_oo),       % s_l
%                 sort_btree(Delta_Bar,Delta_Bar_s),                    % b_t
%                 single_set_closure(Delta_A,Delta_T,Delta_Bar_s),      % b_t
%                 btree2list(Delta_Bar_s,[],Shr_oo),                    % b_t
%                 ss_list_to_23(Delta_Bar,Delta_Bar_s),                   %23_t
%                 single_set_closure23(Delta_A,Delta_T,Delta_Bar_s,Delta_Bar_o), %23_t
%                 gen_23_to_list(Delta_Bar_o,[],Shr_oo),                          %23_t
              aeq_project_shr(Shr_oo,AVars_o,Shr_o) 
            ; (\+ share_aeqs_ic(AEqs,T_ic,A_ic),!,
                (linear_aeqs(AEqs,A),!,
                  S_T = Delta_T,
                  (linear_aeqs(AEqs,T),!,
                    S_A = Delta_A
                  ; full_set_closure(Delta_A,S_A) 
                 )
                ; full_set_closure(Delta_T,S_T),
                  (linear_aeqs(AEqs,T),!,
                    S_A = Delta_A
                  ; full_set_closure(Delta_A,S_A) 
                 )
               )
              ; full_set_closure(Delta_T,S_T),
                full_set_closure(Delta_A,S_A) 
             ),
%                 single_set_closure(S_A,S_T,Delta_Bar,Shr_oo), % us_l
              sort(Delta_Bar,Delta_Bar_s),                  % s_l
              single_set_closure(S_A,S_T,Delta_Bar_s,Shr_oo),       % s_l
%                 sort_btree(Delta_Bar,Delta_Bar_s),            % b_t
%                 single_set_closure(S_A,S_T,Delta_Bar_s),      % b_t
%                 btree2list(Delta_Bar_s,[],Shr_oo),            % b_t
%                 ss_list_to_23(Delta_Bar,Delta_Bar_s),                 %23_t
%                 single_set_closure23(S_A,S_T,Delta_Bar_s,Delta_Bar_o),        %23_t
%                 gen_23_to_list(Delta_Bar_o,[],Shr_oo),                        %23_t
              aeq_project_shr(Shr_oo,AVars_o,Shr_o) 
            ) .
    single_set_closure([],_Delta_T,Sofar,Sofar) .   % s_l
    single_set_closure([H|Delta_A],Delta_T,Sofar,Shr_o) :-
            bitset_union_list_list_s(Delta_T,H,Sofar,Accum),
            single_set_closure(Delta_A,Delta_T,Accum,Shr_o) .

    full_set_closure(Shr_set,Closure) :-
            make_oel(Shr_set,Closure,End),
            full_set_closure(Closure,End,Closure,End,[]) .

    full_set_closure(Shr_set,End,_Closure,CEnd,CEnd) :-
            Shr_set == End,! .
    full_set_closure([H|T],End,Closure,SofarEnd,CEnd) :-
            bitset_union_closure(T,SofarEnd,H,Closure,SofarEnd,SofarNewEnd),
            full_set_closure(T,End,Closure,SofarNewEnd,CEnd) .

    bitset_union_closure(T,End,_H,_Closure,SEnd,SEnd) :-
            T == End,! .
    bitset_union_closure([SG|T],End,H,Closure,SEnd,CEnd) :-
            bitset_union(SG,H,SG_H),
            ((SG_H =:= SG; SG_H =:= H),!,
              bitset_union_closure(T,End,H,Closure,SEnd,CEnd) 
            ; insert_oel(SG_H,Closure,SEnd,NewEnd),
              bitset_union_closure(T,End,H,Closure,NewEnd,CEnd)
            ) . 

    insert_oel(SG_H,Closure,CEnd,NewEnd) :-
            Closure == CEnd,!,Closure = [SG_H| NewEnd] .
    insert_oel(SG_H,[CH|_CT],CEnd,CEnd) :-
            SG_H =:= CH,! .
    insert_oel(SG_H,[_CH|CT],CEnd,NewEnd) :-
            insert_oel(SG_H,CT,CEnd,NewEnd) .

    make_oel([],End,End) .
    make_oel([H|T],[H|T_oel],End) :-
            make_oel(T,T_oel,End) .
%------------------------------------------------------------------------%
% ann_jacobs_langen(+,+,-)
% ann_jacobs_langen(Ann_i,info(A,T,T_ic,AEqs,AVars_o,NGrAVars_o),Ann_o) .
%------------------------------------------------------------------------%
% A is an abstract variable and T is an abstract term (possibly a variable)
% AEqs is the original abstraction (the sharing is the original, not
% the one after performing the unification),and NGrAVars_o is after the 
% sharing propagation so if A=T has grounded some variables in A or T, they
% will not appear in NGrAVars_o.
% This predicate computes the output annotation array Ann_o obtained by
% adding the information from A=T to Ann_i. This is done by computing
% the annotation of T (ItemT), that of A after unifying it with T (ItemAT)
% ( note that we assume they do not share), and then traversing the
% old annotation array and, for each abstract variable N of Ann_i with 
% annotation Item_i:
%    (1) If N_ic in NGrAVars:
%          (1.1) If N_ic and A are renamed variables, N_ic's 
%                anotation is the same as A_ic's (i.e., ItemAT).
%          (1.2) If T is a variable:
%                (1.2.1) If either N_ic is identical to T_ic or they are
%                   renamed, N_ic's annotation is the same as T's
%          (1.3) Otherwise
%    (2) Otherwise:
%       (2.1) If N_ic in AVars (the variable is still in the solved form)
%         the new annotation is the ground one (ann_groundtern(GR_Ann)
%       (2.2) Otherwise $ is the output annotation (the variable disappears
%         from the array)
%------------------------------------------------------------------------%
ann_jacobs_langen(Ann_i,info(A,T,T_ic,AEqs,AVars_o,NGrAVars_o),Ann_o):-
    A = '@'(A_ec),
    AEqs = aeqs(_,Ann,Shr,_,_),
    aref(A_ec,Ann,ItemA),
    get_ann_aterm(AEqs,T,LAnn,ItemT),
    ann_conj(ItemT,ItemA,ItemAT),
    A_ic is 1 << A_ec,
    ann_get_coupled_strongly(Shr,A_ic,CoupA,StrCoupA),
    ann_get_coupled_strongly(Shr,T_ic,CoupT,StrCoupT),
    ann_jacobs_langen0(Ann_i,info(ItemA,A_ic,T,T_ic,ItemT,ItemAT,CoupA,StrCoupA,CoupT,StrCoupT,LAnn,AVars_o,NGrAVars_o),Ann_o).
    
ann_jacobs_langen0(array($(A0,A1,A2,A3),Size),Info,array($(L0,L1,L2,L3),Size)) :-
    N is Size-2,
    ann_solve(0,N,0,A0,Info,L0),
    ann_solve(1,N,0,A1,Info,L1),
    ann_solve(2,N,0,A2,Info,L2),
    ann_solve(3,N,0,A3,Info,L3).

ann_solve(_K,_N,_M,$,_Info,$) :- ! .
ann_solve(K,0,M,Item_i,info(ItemA,A_ic,T,T_ic,ItemT,ItemAT,CoupA,StrCoupA,CoupT,StrCoupT,LAnn,AVars_ic,NGrAVars),Item_o) :- !,
    N is K+M,N_ic is 1 << N,
    ( bitset_member(N_ic,NGrAVars) -> % (1)
         ( (ItemA = f, Item_i = f, bitset_member(N_ic,StrCoupA)) ->
             Item_o = ItemAT % (1.1)
         ; ( T = '@'(_) ->
                 ann_solve_var(Item_i,N_ic,A_ic,T_ic,ItemT,ItemAT,CoupA,CoupT,StrCoupT,Item_o)
           ;   ann_solve_term(Item_i,N_ic,ItemA,T_ic,ItemT,CoupA,CoupT,LAnn,Item_o)))
    ; ( bitset_member(N_ic,AVars_ic)  ->   
           Item_o = g    % (2.1)
      ;    Item_o = $)). % (2.2)
ann_solve(K,N,M,$(A0,A1,A2,A3),Info,$(L0,L1,L2,L3)) :-
    N>0,
    N1 is N-2,
    M1 is (K+M)<<2,
    ann_solve(0,N1,M1,A0,Info,L0),
    ann_solve(1,N1,M1,A1,Info,L1),
    ann_solve(2,N1,M1,A2,Info,L2),
    ann_solve(3,N1,M1,A3,Info,L3).

%% ann_solve_var(N_ic,Item_i,ItemA,T_ic,ItemT,ItemAT,CoupA,CoupT,StrCoupT,Item_o):-
%%      ( ( N_ic = T_ic ; (Item_i = f, ItemT = f, bitset_member(N_ic,StrCoupT))) ->
%%          Item_o = ItemAT  % (1.2.1)
%%      ; ( bitset_member(N_ic,CoupA) ->
%%          ( ItemT = f ->
%%              Item_o = Item_i
%%          ; ( ann_linear(ItemT), not_bitset_member(N_ic,CoupT) ->
%%                 ann_remove_non_ground(Item_i,Item_o)
%%             ;   ann_remove_linear_non_ground(Item_i,Item_o)))
%%        ; ( bitset_member(N_ic,CoupT) ->
%%           ( ItemA = f ->
%%               Item_o = Item_i
%%           ; ( ann_linear(ItemA), not_bitset_member(N_ic,CoupA) ->
%%                  ann_remove_non_ground(Item_i,Item_o)
%%             ;   ann_remove_linear_non_ground(Item_i,Item_o)))
%%          ; Item_o = Item_i))).
%% 

ann_solve_var(g,_,_,_,_,_,_,_,_,g):- !.
ann_solve_var(_,N_ic,N_ic,_,_,ItemAT,_,CoupT,_,Item_o):- !,  %% N_ic = A_ic
    ( bitset_member(N_ic,CoupT) ->
        ann_remove_linear(ItemAT,Item_o)
    ; Item_o = ItemAT).
ann_solve_var(_,N_ic,_,N_ic,_,ItemAT,CoupA,_,_,Item_o):- !,  %% N_ic = T_ic
    ( bitset_member(N_ic,CoupA) ->
        ann_remove_linear(ItemAT,Item_o)
    ; Item_o = ItemAT).
ann_solve_var(f,N_ic,_,_,ItemT,ItemAT,CoupA,CoupT,StrCoupT,Item_o):- !,
    ( ( bitset_member(N_ic,CoupT);bitset_member(N_ic,CoupA)) ->
        ( (ItemAT = f;ItemT = f, bitset_member(N_ic,StrCoupT)) ->
            Item_o = ItemAT 
        ; ann_lub_f(ItemAT,Item_o))
    ;  Item_o = f).
ann_solve_var(Item_i,N_ic,_,_,_,ItemAT,CoupA,CoupT,_,Item_o):- 
    ann_linear(Item_i),!, %% l,lnf,lng,lngf
    ( ann_linear(ItemAT) ->
        ( bitset_member(N_ic,CoupT), bitset_member(N_ic,CoupA) ->
            ann_remove_linear(Item_i,Item0_o),
            ann_check_non_ground(N_ic,Item0_o,ItemAT,CoupA,CoupT,Item_o)
        ;   Item_o = Item_i)
    ; ( ( bitset_member(N_ic,CoupT);bitset_member(N_ic,CoupA)) ->
            ann_remove_linear(Item_i,Item0_o),
            ann_check_non_ground(N_ic,Item0_o,ItemAT,CoupA,CoupT,Item_o)
        ;   Item_o = Item_i)).
ann_solve_var(Item_i,N_ic,_,_,_,ItemAT,CoupA,CoupT,_,Item_o):- 
%% a,nf,ng,ngf
    ann_check_non_ground(N_ic,Item_i,ItemAT,CoupA,CoupT,Item_o).

ann_check_non_ground(N_ic,Item_i,ItemAT,CoupA,CoupT,Item_o):-
    ( ann_non_ground(ItemAT), (bitset_member(N_ic,CoupT);bitset_member(N_ic,CoupA)) ->
         ann_remove_non_ground(Item_i,Item_o)
    ;    Item_o = Item_i).
        

    
    
ann_solve_term(Item_i,N_ic,ItemA,T_ic,_,CoupA,_,_,Item_o):- 
    bitset_member(N_ic,T_ic),!,
    ( ItemA = f ->
        Item_o = Item_i
    ; ( ann_linear(ItemA), not_bitset_member(N_ic,CoupA)) ->
               ann_remove_non_ground(Item_i,Item_o)
       ;   ann_remove_linear_non_ground(Item_i,Item_o)).
ann_solve_term(f,N_ic,ItemA,_,ItemT,CoupA,CoupT,LAnn,Item_o):- !,
    ( bitset_member(N_ic,CoupA) ->
        ( ann_linear(ItemT), not_bitset_member(N_ic,CoupT) ->
               TmpItem_i = lng
          ;    TmpItem_i = ng),
        ( LAnn == [f] ->
            Item_o = TmpItem_i
        ;  ann_remove_non_ground(TmpItem_i,Item_o))
    ; ( bitset_member(N_ic,CoupT) ->
        ( ItemA = f ->
            Item_o = f
        ; ( ann_linear(ItemA), not_bitset_member(N_ic,CoupA) ->
               Item_o = l
         ;   Item_o = a))
      ; Item_o = f)).
ann_solve_term(Item_i,N_ic,ItemA,_,ItemT,CoupA,CoupT,LAnn,Item_o):- 
    ( bitset_member(N_ic,CoupA) ->
        ( ann_linear(ItemT), not_bitset_member(N_ic,CoupT) ->
               TmpItem_i = Item_i
          ;   ann_remove_linear(Item_i,TmpItem_i)),
        ( LAnn == [f] ->
            Item_o = TmpItem_i
        ;  ann_remove_non_ground(TmpItem_i,Item_o))
    ; ( bitset_member(N_ic,CoupT) ->
        ( ItemA = f ->
            Item_o = Item_i
        ; ( ann_linear(ItemA), not_bitset_member(N_ic,CoupA) ->
               ann_remove_non_ground(Item_i,Item_o)
         ;   ann_remove_linear_non_ground(Item_i,Item_o)))
      ; Item_o = Item_i)).

ann_get_coupled_strongly(p(_,Shr),A_ic,Coup,A_ic):- !,
    aeq_split_intersect_disjoint(Shr,A_ic,Inters,_),        
    bitset_union_list([A_ic|Inters],Coup).
ann_get_coupled_strongly(Shr,A_ic,Coup,Str):-
    aeq_split_intersect_disjoint(Shr,A_ic,Inters,Disj),     
    bitset_union_list([A_ic|Inters],Coup),
    bitset_union_list(Disj,NonSh),
    bitset_subtract(Coup,NonSh,Str).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  aux. proc. for the   `aeq_success_builtin',`aeq_parameter_passing_proj',
%%  `aeq_parameter_passing_rem' domain-dep. operation
%%%%%%%%%%%%

aeq_add_equation(Eq,aeqs(SF,Ann,Shr,AVars,NGrAVars),
                    aeqs(eqs(SF,[AEq|End],End),Ann,Shr,AVars,NGrAVars)):-
    aeq_substitute(Eq,SF,AEq) .

%-------------------------------------------------------------------------
% aeq_substitute(+,+,-)
% aeq_substitute(Term,Eqs_sf,Term_sub)
%-------------------------------------------------------------------------
% Term_sub is the result of substituting the program variables in Term
% by the abstract terms associated to them by Eqs_sf.
%-------------------------------------------------------------------------
aeq_substitute(Term,Eqs_sf,Term_sub) :-
    var(Term),!,
    member_key(Term,Eqs_sf,Term_sub).
aeq_substitute(Term,_Eqs_sf,Term) :-
    (atomic(Term) ; Term = '@'(_)), !.
aeq_substitute([H|T],Eqs_sf,[H_sub|T_sub]) :- !,
    aeq_substitute(H,Eqs_sf,H_sub),
    aeq_substitute(T,Eqs_sf,T_sub).
aeq_substitute(Term,Eqs_sf,Term_sub) :-
    Term =.. [Functor| Args],
    aeq_substitute(Args,Eqs_sf,Args_sub),
    Term_sub =.. [Functor| Args_sub] .

%-------------------------------------------------------------------------
% aeq_substitute_avar(+,+,+,-)
% aeq_substitute_avar(TermX,X,Y,TermY)
%-------------------------------------------------------------------------
% TermX is the result of substituting in TermX, X by Y.
%-------------------------------------------------------------------------
aeq_substitute_avar(Term,AT1,AT2,AT2) :-
    Term == AT1,! .
aeq_substitute_avar(Term,_AT1,_AT2,Term) :-
    (atomic(Term) ; var(Term)), !.
aeq_substitute_avar([H|T],AT1,AT2,[H_sub|T_sub]) :- !,
    aeq_substitute_avar(H,AT1,AT2,H_sub),
    aeq_substitute_avar(T,AT1,AT2,T_sub).
aeq_substitute_avar(Term,AT1,AT2,Term_sub) :-
    Term =.. [Functor| Args],
    aeq_substitute_avar(Args,AT1,AT2,Args_sub),
    Term_sub =.. [Functor| Args_sub] .

%-------------------------------------------------------------------------
% aeq_substitute_myavar(+,+,+,-)
% aeq_substitute_myavar(TermX,X,Y,TermY)
%-------------------------------------------------------------------------
% Same as before but do not going inside of $VARs.
%-------------------------------------------------------------------------
aeq_substitute_myavar(Term,AT1,AT2,AT2) :-
    Term == AT1,! .
aeq_substitute_myavar(Term,_AT1,_AT2,Term) :-
    (atomic(Term) ; var(Term)), !.
aeq_substitute_myavar('$VAR'(A),_,_,'$VAR'(A)) :- !.
aeq_substitute_myavar([H|T],AT1,AT2,[H_sub|T_sub]) :- !,
    aeq_substitute_myavar(H,AT1,AT2,H_sub),
    aeq_substitute_myavar(T,AT1,AT2,T_sub).
aeq_substitute_myavar(Term,AT1,AT2,Term_sub) :-
    Term =.. [Functor| Args],
    aeq_substitute_myavar(Args,AT1,AT2,Args_sub),
    Term_sub =.. [Functor| Args_sub] .

%-------------------------------------------------------------------------
% aeq_add_equation_proj(+,+,+,-)
% aeq_add_equation_proj(Eq,CVars,AEqs,AEqs_out).
%-------------------------------------------------------------------------
% Eq is the equation Sg = Head to be added to the abstraction AEqs during
% entry and exit. CVars is Hv+Fv. This predicates simply projects the 
% abstraction AEqs over CVars but also keeping all the abstract variables
% related to both CVars and Sv. It works as follows:
% * Computes AEq, which is the result of substituting the program 
%      variables in Eq by the abstract terms associated to them by SF
% * Obtains in Avars_AEq the bitsetcode of the set of abstract variables 
%      in AEq.
% * Computes P_SF: the equations X=ATerm in SF s.t. X is in CVars
% * Computes AVars_o: the union of Avars_AEq and the abstract variables
%      in each ATerm in P_SF.
% * Projects the rest of the abstract components over AVars_o (note that this
%      includes the abstract variables associated to program vars in Sg).
%-------------------------------------------------------------------------
aeq_add_equation_proj(Eq,CVars,AEqs,
            aeqs(eqs(P_SF,[AEq|End],End),Ann_o,Shr_o,AVars_o,NGrAVars_o)):-
    AEqs = aeqs(SF,_,_,_,_),
    aeq_substitute(Eq,SF,AEq),
    avariables_ic(AEq,Avars_AEq),
    aeq_project_eqs(SF,CVars,P_SF,Avars_AEq,AVars_o),
    aeq_project_vars(AVars_o,_,AEqs,aeqs(_,Ann_o,Shr_o,AVars_o,NGrAVars_o)).

aeq_add_equation_rem(Eq,CVars,aeqs(SF,Ann,Shr,AVars,NGrAVars),
                    aeqs(eqs(P_SF,[AEq|End],End),Ann,Shr,AVars,NGrAVars)):-
    aeq_substitute(Eq,SF,AEq),
    aeq_project_eqs_rm(SF,CVars,P_SF) .

aeq_project_eqs_rm([],_Vars,[]).
aeq_project_eqs_rm([CVar = ATerm|Eqs],Vars,AVars_proj) :-
    ( memberchk(CVar,Vars) ->
        AVars_proj = Tail
    ;   AVars_proj = [CVar=ATerm|Tail]
       ),
    aeq_project_eqs_rm(Eqs,Vars,Tail) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%  aux. proc. for the   `aeq_extend'  domain-dep. operation
%%%%%%%%%%%%

aeq_union(aeqs(Eqs_pr,Ann_pr,Shr_pr,AVars_pr,NGrAVars_pr),
       aeqs(Eqs_cl,Ann_cl,Shr_cl,AVars_cl,NGrAVars_cl),
       aeqs(eqs(Eqs_cl,Eqs_ren,End),Ann_un,Shr_un,AVars_un,NGrAVars_un)) :-
    bitcode_to_set(AVars_pr,AVars_pr_ec),
    new_array(Ren_array_i),
    renaming_apart(AVars_pr_ec,Ann_pr,AVars_cl,Ann_cl,
                    AVars_un,Ann_un,0,Ren_array_i,Ren_array_o),
    eqs_rename(Eqs_pr,Eqs_cl,Ren_array_o,Eqs_ren-End),
    (aeq_current_sharing(pair) ->
      shr_renameP(Shr_pr,Ren_array_o,Shr_cl,Shr_un,
                            NGrAVars_pr,NGrAVars_cl,NGrAVars_un)
    ; shr_rename(Shr_pr,Ren_array_o,Shr_cl,Shr_un,NGrAVars_cl,NGrAVars_un)
    ) .

    renaming_apart([],_Ann_pr,AVars,Ann,
                    AVars,Ann,_Nb,Ren_array,Ren_array) .
    renaming_apart([AVar_Nb|T],Ann_pr,AVars_cl,Ann_cl,
                    AVars_o,Ann_o,Nb,Ren_array_i,Ren_array_o) :-
            aeq_select_unused_var(Nb,AVars_cl,Nb_new_ec,Nb_new_ic),
            aset(AVar_Nb,Ren_array_i,Nb_new_ic,Ren_array_new),
            bitset_union(AVars_cl,Nb_new_ic,AVars_new),
            aref(AVar_Nb,Ann_pr,AVar_Ann),
            aset(Nb_new_ec,Ann_cl,AVar_Ann,Ann_new),
            Nb_new is Nb_new_ec + 1,
            renaming_apart(T,Ann_pr,AVars_new,Ann_new,
                    AVars_o,Ann_o,Nb_new,Ren_array_new,Ren_array_o) .

    eqs_rename([],_Eqs_cl,_Ren_array,End-End) .
    eqs_rename([ X = AT |Tail],Eqs_cl,Ren_array,[AT_ren = AX |Tail_ren]-End) :-
            %
            % REMARK : the equations are switched in order to give the
            % abstract variables of the calling clause a higher priority
            % then those of the Prime_AEqs returned; this eases the reading
            % of the final annotated program,since there is less abstract
            % variable renaming.  Also some efficiency is gained.
            %
            aeq_substitute(X,Eqs_cl,AX),
            term_rename(AT,Ren_array,AT_ren),
            eqs_rename(Tail,Eqs_cl,Ren_array,Tail_ren-End) .

            term_rename(MTerm,_Ren_array,MTerm) :-
                    (atomic(MTerm) ; var(MTerm)), !.
            term_rename(MTerm,Ren_array,'@'(Ec_ren)) :-
                    MTerm = '@'(AVar_ec),!,
                    aref(AVar_ec,Ren_array,Ic_ren),
                    bitcode_to_set(Ic_ren,[Ec_ren]) .
            term_rename([H|T],Ren_array,[H_ren|T_ren]) :- !,
                    term_rename(H,Ren_array,H_ren),
                    term_rename(T,Ren_array,T_ren).
            term_rename(Term,Ren_array,Term_ren) :-
                    Term =.. [Functor| Args],
                    term_rename(Args,Ren_array,Args_ren),
                    Term_ren =.. [Functor| Args_ren] .

    shr_renameP(ps(I_pr,E_pr),Ren_array,ps(I_cl,E_cl),ps(I_un,E_un),
                                    NGrAVars_pr,NGrAVars_cl,NGrAVars_un) :-
            bitcode_to_set(I_pr,I_pr_ec),
            union_asgs(I_pr_ec,Ren_array,0,I_pr_ren),
            bitset_union(I_pr_ren,I_cl,I_un),
            bitcode_to_set(NGrAVars_pr,NGrAVars_pr_ec),
            union_asgs(NGrAVars_pr_ec,Ren_array,0,NGrAVars_pr_ren),
            bitset_union(NGrAVars_pr_ren,NGrAVars_cl,NGrAVars_un),
            shr_rename(E_pr,Ren_array,E_cl,E_un) .

    shr_rename([],_Ren_array,Shr,Shr) .
    shr_rename([SG |Tail],Ren_array,Shr_Sofar,[SG_ren |Tail_ren]) :-
            bitcode_to_set(SG,SG_ec),
            union_asgs(SG_ec,Ren_array,0,SG_ren),
            shr_rename(Tail,Ren_array,Shr_Sofar,Tail_ren) .

    shr_rename([],_Ren_array,Shr,Shr,NGrAVars,NGrAVars) .
    shr_rename([SG |Tail],Ren_array,Shr_Sofar,[SG_ren |Tail_ren],
                    NGrAVars_i,NGrAVars_o) :-
            bitcode_to_set(SG,SG_ec),
            union_asgs(SG_ec,Ren_array,0,SG_ren),
            bitset_union(SG_ren,NGrAVars_i,NGrAVars_new),
            shr_rename(Tail,Ren_array,Shr_Sofar,Tail_ren,
                    NGrAVars_new,NGrAVars_o) .


%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% The follwoing implements the unknown_call and unknown_entry
% Independent of the annotation set
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
aeq_top(CVars,TopAEqs) :-
    new_array(Ann),
    (aeq_current_sharing(pair) ->
      aeq_topP(CVars,0,aeqs([],Ann,ps(0,[]),0,0),TopAEqs)
    ; aeq_top(CVars,0,aeqs([],Ann,[],0,0),TopAEqs)) .

aeq_topP([],_Nb,TopAEqs,TopAEqs) .
aeq_topP([CVar|CVars],Nb,aeqs(Eqs,Ann_i,Shr_i,AVars_i,NGrAVars_i),TopAEqs) :-
    Nb_ic is 1 << Nb,
    bitset_union(AVars_i,Nb_ic,AVars),
    bitset_union(NGrAVars_i,Nb_ic,NGrAVars),
    top_shrP(Shr_i,Nb_ic,AVars_i,Shr),
    aset(Nb,Ann_i,a,Ann),
    NewNb is Nb + 1,
    aeq_topP(CVars,NewNb,
            aeqs([CVar='@'(Nb)|Eqs],Ann,Shr,AVars,NGrAVars),TopAEqs) .

aeq_top([],_Nb,TopAEqs,TopAEqs) .
aeq_top([CVar|CVars],Nb,aeqs(Eqs,Ann_i,Shr_i,AVars_i,NGrAVars_i),TopAEqs) :-
    Nb_ic is 1 << Nb,
    bitset_union(AVars_i,Nb_ic,AVars),
    bitset_union(NGrAVars_i,Nb_ic,NGrAVars),
    top_shr(Shr_i,Nb_ic,[ Nb_ic| Shr_i],Shr),
    aset(Nb,Ann_i,a,Ann),
    NewNb is Nb + 1,
    aeq_top(CVars,NewNb,
            aeqs([CVar='@'(Nb)|Eqs],Ann,Shr,AVars,NGrAVars),TopAEqs) .


top_shrP(ps(I_i,E_i),Nb_ic,AVars_i,ps(I_e,E_e)) :-
    bitset_union(I_i,Nb_ic,I_e),
    bitcode_to_listofbitcode(AVars_i,AVars_list),
    top_shrPex(AVars_list,Nb_ic,E_i,E_e) .

    top_shrPex([],_Nb_ic,E,E) .
    top_shrPex([H|T],Nb_ic,Sofar,E_e) :-
            bitset_union(H,Nb_ic,HNb_ic),
            top_shrPex(T,Nb_ic,[HNb_ic|Sofar],E_e) .

top_shr([],_Nb_ic,Sofar,Sofar) .
top_shr([SG | ShrTail],Nb_ic,Sofar,Shr) :-
    bitset_union(SG,Nb_ic,SG_and_Nb),
    top_shr(ShrTail,Nb_ic,[SG_and_Nb | Sofar],Shr) .

%------------------------------------------------------------------------%
% The following are auxiliar procedures for success_builtin
%------------------------------------------------------------------------%
aeq_var_or_number(Var,AEqs,AVar_ic) :-
    (var(Var),
      get_Eqs_aeqs(AEqs,Eqs),
      member(Var1 = Term,Eqs),Var==Var1,!,
      avar_ic(Term,AVar_ic)
    ; number(Var),AVar_ic is 0
    ),! .

avarORatom_aeqs(A_F,Avar_F_ic) :-
    (atom(A_F),!,Avar_F_ic = 0
    ; avar_ic(A_F,Avar_F_ic)
    ) .

avarORinteger_aeqs(A_A,Avar_A_ic) :-
    (integer(A_A),!,Avar_A_ic = 0
    ; avar_ic(A_A,Avar_A_ic)
    ) .

avarORnumber_aeqs(A_A,Avar_A_ic) :-
    (number(A_A),!,Avar_A_ic = 0
    ; avar_ic(A_A,Avar_A_ic)
    ) .

aeq_instantiated_Expr(Expr,AEqs,AVarExpr_ic,AExpr) :-
    (var(Expr),!,
      get_Eqs_aeqs(AEqs,Eqs),
      member(Expr1 = Term,Eqs),Expr==Expr1,!,
      aeq_instantiated_Expr(Term,AEqs,AVarExpr_ic,AExpr)
    ; avar_ic(Expr,AVarExpr_ic),!,\+ free_aeqs(AEqs,Expr),
      AExpr = Expr
    ; number(Expr),!,AVarExpr_ic = 0,
      AExpr = Expr
    ; Expr =.. [Op|Args],
      valid_operator(Op),!,
      aeq_instantiated_Expr_list(Args,AEqs,0,AVarExpr_ic,A_Args),
      AExpr =.. [Op|A_Args]
    ) .

    aeq_instantiated_Expr_list([],_AEqs,Sofar,Sofar,[]) .
    aeq_instantiated_Expr_list([H|T],AEqs,Sofar_i,Sofar_o,[A_H|A_T]) :-
            aeq_instantiated_Expr(H,AEqs,AVarH_ic,A_H),
            bitset_union(AVarH_ic,Sofar_i,Sofar),
            aeq_instantiated_Expr_list(T,AEqs,Sofar,Sofar_o,A_T) .

aeq_make_ground(AVars_ic,
            aeqs(Eqs,Ann_i,Shr_i,AVars,NGrAVars_i),
            aeqs(Eqs,Ann_o,Shr_o,AVars,NGrAVars_o)) :-
    aeq_split_disjoint(Shr_i,AVars_ic,Shr_o),
    bitset_union_list(Shr_o,NGrAVars_o),
    bitset_subtract(NGrAVars_i,NGrAVars_o,ToMakeGround_ic),
    bitcode_to_set(ToMakeGround_ic,ToMakeGround_ec),
    aeq_make_ground_list(ToMakeGround_ec,Ann_i,Ann_o).

    aeq_make_ground_list([],Ann,Ann) .
    aeq_make_ground_list([H|T],Ann_i,Ann_o) :-
            aeq_make_ground_avar(H,Ann_i,Ann),
            aeq_make_ground_list(T,Ann,Ann_o) .
    
    aeq_make_ground_avar(H,Ann,Ann) :-
             aref(H,Ann,g),! .
    aeq_make_ground_avar(H,Ann_i,Ann_o) :-
             aset(H,Ann_i,g,Ann_o) .

aeq_make_free(AVar,   aeqs(Eqs,Ann_i,Shr_i,AVars,NGrAVars),
                    aeqs(Eqs,Ann_o,Shr_o,AVars,NGrAVars)) :-
    AVar = '@'(AVar_ec),
    aset(AVar_ec,Ann_i,f,Ann_o),
    aeq_make_free_shr(AVar,Shr_i,Shr_o) .

    aeq_make_free_shr(AVar,ps(I_i,E),ps(I_o,E)) :- !,
            avar_ic(AVar,AVar_ic),
            bitset_subtract(I_i,AVar_ic,I_o) .
    aeq_make_free_shr(_AVar,Shr,Shr) .

% Here you know that AVar is free; so the sharing component need not be changed
aeq_make_linear(AVar, aeqs(Eqs,Ann_i,Shr,AVars,NGrAVars),
                    aeqs(Eqs,Ann_o,Shr,AVars,NGrAVars)) :-
    AVar = '@'(AVar_ec),
    aset(AVar_ec,Ann_i,l,Ann_o) .


% list is not complete
valid_operator(+) .
valid_operator(-) .
valid_operator(#) .
valid_operator(\/) .
valid_operator(/\) .
valid_operator(*) .
valid_operator(/) .
valid_operator(//) .
valid_operator(<<) .
valid_operator(>>) .
valid_operator(mod) .
valid_operator(~) .
valid_operator(^) .
valid_operator(\) .
valid_operator(integer) .
valid_operator(float) .
valid_operator(min) .
valid_operator(max) .

aeq_functor_succ(A_T,A_F,A_A,Call,Succ) :-
    avarORatom_aeqs(A_F,Avar_F_ic),
    avarORinteger_aeqs(A_A,Avar_A_ic),
    (free_aeqs(Call,A_T),!,
       (free_aeqs(Call,A_F),!,fail
       ; free_aeqs(Call,A_A),!,fail
       ; bitset_union(Avar_F_ic,Avar_A_ic,Avar_FA_ic),
         aeq_make_ground(Avar_FA_ic,Call,Sofar),
         aeq_make_linear(A_T,Sofar,Succ)
      )
    ; bitset_union(Avar_F_ic,Avar_A_ic,Avar_FA_ic), % REMARK : this could be
      aeq_make_ground(Avar_FA_ic,Call,Succ)      % made more precise
    ) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

aeq_jacobs_langen_variant(A,T,Variant,AEqs,
               aeqs(Eqs,Ann_o,Shr_o,AVars,NGrAVars_o)) :-
    AEqs =     aeqs(Eqs,Ann_i,_Shr_i,AVars,_NGrAVars_i),
    avariables_ic(T,T_ic),
    (aeq_current_sharing(pair),!,
      shr_sondergaard_variant(A,T,T_ic,Variant,AEqs,NGrAVars_o,Shr_o)
    ; shr_jacobs_langen_variant(A,T,T_ic,Variant,AEqs,Shr_o),
      bitset_union_list(Shr_o,NGrAVars_o)
    ),
    ann_jacobs_langen(Ann_i,info(A,T,T_ic,AEqs,AVars,NGrAVars_o),Ann_o) .

    shr_sondergaard_variant(A,T,T_ic,Variant,AEqs,NGrAVars_o,Shr_o) :-
            AEqs = aeqs(_,_Ann,Shr,_AVars,NGrAVars),
            avariables_ic(A,A_ic),
            bitset_union(A_ic,T_ic,AT_ic),
            aeq_split_intersect_disjoint(Shr,AT_ic,Delta_AT,Delta_Bar),
            ((bitset_intersect(A_ic,NGrAVars,0)
              ; Variant == '=..',bitset_intersect(T_ic,NGrAVars,0)),!,
              Shr_o = Delta_Bar,
              bitset_subtract(NGrAVars,AT_ic,NGrAVars_o)
            ; bitset_intersect(T_ic,NGrAVars,NGrT_ic),
              newshr_sondergaard(A,A_ic,T,NGrT_ic,AEqs,New_Shr),
              aeq_paths3(Delta_AT,New_Shr,Paths3),
              aeq_union_shrP(Shr,New_Shr,Paths3,Shr_o),
              NGrAVars_o = NGrAVars 
            ) .

    shr_jacobs_langen_variant(A,T,T_ic,Variant,AEqs,Shr_o) :-
            AEqs = aeqs(_,_Ann,Shr,_AVars,NGrAVars),
            avariables_ic(A,A_ic),
            delta_Shr(Shr,A_ic,T_ic,Delta_A,Delta_T,Delta_Bar),
            ((bitset_intersect(A_ic,NGrAVars,0)
              ; Variant == '=..',bitset_intersect(T_ic,NGrAVars,0)),!,
              Shr_o = Delta_Bar
            ; Variant == '=..',
              (free_aeqs(AEqs,A) ; free_aeqs(AEqs,T)),!,
%                 single_set_closure(Delta_A,Delta_T,Delta_Bar,Shr_o)   % us_l
              sort(Delta_Bar,Delta_Bar_s),                          % s_l
              single_set_closure(Delta_A,Delta_T,Delta_Bar_s,Shr_o) % s_l
%                 sort_btree(Delta_Bar,Delta_Bar_s),                    % b_t
%                 single_set_closure(Delta_A,Delta_T,Delta_Bar_s),      % b_t
%                 btree2list(Delta_Bar_s,[],Shr_o)                      % b_t
%                 ss_list_to_23(Delta_Bar,Delta_Bar_s),                   % 23_t
%                 single_set_closure23(Delta_A,Delta_T,Delta_Bar_s,Delta_Bar_o), % 23_t
%                 gen_23_to_list(Delta_Bar_o,[],Shr_o)                    % 23_t
            ; (\+ share_aeqs_ic(AEqs,T_ic,A_ic),!,
                (linear_aeqs(AEqs,A),!,
                  S_T = Delta_T,
                  (linear_aeqs(AEqs,T),!,
                    S_A = Delta_A
                  ; full_set_closure(Delta_A,S_A) 
                 )
                ; full_set_closure(Delta_T,S_T),
                  (linear_aeqs(AEqs,T),!,
                    S_A = Delta_A
                  ; full_set_closure(Delta_A,S_A) 
                 )
               )
              ; full_set_closure(Delta_T,S_T),
                full_set_closure(Delta_A,S_A) 
             ),
              sort(Delta_Bar,Delta_Bar_s),          % s_l
%                 sort_btree(Delta_Bar,Delta_Bar_s),            % b_t
%                 ss_list_to_23(Delta_Bar,Delta_Bar_s), % 23_t
              (Variant == 'arg',!,
%                   single_set_closure(S_A,[0|S_T],Delta_Bar,Shr_o)               % us_l
                single_set_closure(S_A,[0|S_T],Delta_Bar_s,Shr_o)     % s_l
%                   single_set_closure(S_A,[0|S_T],Delta_Bar_s)           % b_t
%                   single_set_closure23(Delta_A,Delta_T,Delta_Bar_s,Delta_Bar_o) % 23_t
              ; Variant == '=..',
%                   single_set_closure(S_A,S_T,Delta_Bar,Shr_o)           % us_l
                single_set_closure(S_A,S_T,Delta_Bar_s,Shr_o)                 % s_l
%                   single_set_closure(S_A,S_T,Delta_Bar_s)                       % b_t
%                   single_set_closure23(Delta_A,Delta_T,Delta_Bar_s,Delta_Bar_o) % 23_t
             ) % ,
%                 btree2list(Delta_Bar_s,[],Shr_o)              % b_t
%                 gen_23_to_list(Delta_Bar_o,[],Shr_o)  % 23_t
            ) .

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% %% :- mode  aeq_partition(+,-) .
%% aeq_partition('$bottom',['$bottom']) .
%% aeq_partition(aeqs(_Eqs,Ann,Shr,_AVars,_NGrAVars),Aeqs_list) :-
%%      ann_free_vars(Ann,Freevars),
%%      findall(aeqs_part(ShrPart,NGrPart,ShrRedun,Eq) ,
%%               aeq_partition_shr(Shr,Freevars,ShrPart,NGrPart,ShrRedun,Eq),
%%               Aeqs_list) .

%% :- mode  ann_free_vars(+,-) .
ann_free_vars(array($(A0,A1,A2,A3),Size),Freevars) :-
    N is Size-2,
    ann_free_vars(0,N,0,A0,0,F1),
    ann_free_vars(1,N,0,A1,F1,F2),
    ann_free_vars(2,N,0,A2,F2,F3),
    ann_free_vars(3,N,0,A3,F3,Freevars).

    ann_free_vars(_K,_N,_M,$,Freevars,Freevars) :- ! .
    ann_free_vars(K,0,M,f,F_in,F_out) :-
            N is K+M,N_ic is 1 << N,
            bitset_union(F_in,N_ic,F_out),! .
    ann_free_vars(_K,0,_M,_Item,Freevars,Freevars) :- ! .
    ann_free_vars(K,N,M,$(A0,A1,A2,A3),F_in,F_out) :-
            N>0,
            N1 is N-2,
            M1 is (K+M)<<2,
            ann_free_vars(0,N1,M1,A0,F_in,F1),
            ann_free_vars(1,N1,M1,A1,F1,F2),
            ann_free_vars(2,N1,M1,A2,F2,F3),
            ann_free_vars(3,N1,M1,A3,F3,F_out).

%% %% :- mode  aeq_partition_shr(+,+,-,-,-,-) .
%% aeq_partition_shr([],_Freevars,[],0,[],End-End) :- ! .
%% aeq_partition_shr(Shr,0,Shr,NGrPart,[],End-End) :- !,
%%      bitset_union_list(Shr,NGrPart) .
%% aeq_partition_shr(Shr,Freevars,ShrPart,NGrPart,ShrRedun,Equations) :-
%%      delta_Free(Shr,Freevars,Shr_F,Shr_NF),
%%      bitset_union_list(Shr_NF,NGr_Shr_NF),
%%      aeq_generate_part(Shr_F,Freevars,0,[],Shr_NF,NGr_Shr_NF,
%%                      ShrPart,NGrPart,ShrRedun,[],Eq),
%%      aeq_make_equations(Eq,Equations) .
%% 
%%      delta_Free([],_Freevars,[],[]) .
%%      delta_Free([H|T],Freevars,T_F,[H|T_NF]) :-
%%              bitset_intersect(H,Freevars,0),!,
%%              delta_Free(T,Freevars,T_F,T_NF) .
%%      delta_Free([H|T],Freevars,[H|T_F],T_NF) :-
%%              delta_Free(T,Freevars,T_F,T_NF) .
%% 
%%      aeq_make_equations([],End - End) .
%%      aeq_make_equations([Eq| Tail],Eqs1 - End) :-
%%              aeq_make_eqs(Eq,Eqs1 - Eqs2),
%%              aeq_make_equations(Tail,Eqs2 - End) .
%% 
%%      aeq_make_eqs([H1,H2|T],Equations) :- !,
%%              aeq_make_eqs([H2|T],H1,Equations) .
%%      aeq_make_eqs(_,End - End) .
%% 
%%      aeq_make_eqs([],_H1,End - End) .
%%      aeq_make_eqs([H2|T],H1,['@'(H2) = '@'(H1) |Eqs] - End) :-
%%              aeq_make_eqs(T,H1,Eqs- End) .

%% %% :- mode aeq_generate_part(+,+,+,+,+,+,-,-,-,+,-) .
%% aeq_generate_part(Shr_F,0,_FV_seen,Shr_red,Shr_sofar,NGr_sofar,
%%                      Shr_sofar,NGr_sofar,ShrRedun,Eq,Eq) :- !,
%%      append(Shr_red,Shr_F,ShrRedun) .
%% aeq_generate_part([H_F|T_F],FV_unseen,FV_seen,Shr_red,Shr_sofar,NGr_sofar,
%%                      ShrPart,NGrPart,ShrRedun,Eq_in,[Make_equal|Eq_out]) :-
%%      bitset_intersect(FV_seen,H_F,0),
%%      bitset_intersect(FV_unseen,H_F,SeeFreeVars),SeeFreeVars =\= 0,
%%      bitcode_to_set(SeeFreeVars,Make_equal),
%%      bitset_union(FV_seen,SeeFreeVars,FV_seen_new),
%%      bitset_subtract(FV_unseen,FV_seen_new,FV_unseen_new),
%%      bitset_union(H_F,NGr_sofar,NGr_sofar_new),
%%      aeq_generate_part(T_F,FV_unseen_new,FV_seen_new,Shr_red,
%%                      [H_F|Shr_sofar],NGr_sofar_new,
%%                      ShrPart,NGrPart,ShrRedun,Eq_in,Eq_out) .
%% aeq_generate_part([H_F|T_F],FV_unseen,FV_seen,Shr_red,Shr_sofar,NGr_sofar,
%%                      ShrPart,NGrPart,ShrRedun,Eq_in,Eq_out) :-
%%      aeq_generate_part(T_F,FV_unseen,FV_seen,[H_F|Shr_red],Shr_sofar,NGr_sofar,
%%                      ShrPart,NGrPart,ShrRedun,Eq_in,Eq_out) .
%% 
%% 
%% %------------------------------------------------------------------------%
%% %-------------------------------------------------------------------------
%% %                        DELAY PREDICATES
%% %------------------------------------------------------------------------%
%% %-------------------------------------------------------------------------
%% % Assumptions: programs are normalized.
%% %------------------------------------------------------------------------%
%% 
%% %-------------------------------------------------------------------------
%% % aeq_check_cond(+,+,+,-)
%% % aeq_check_cond(Conds,ACns,Sv,Flag)
%% %-------------------------------------------------------------------------
%% % This predicates decides if the delaying conditions in Conds are satified 
%% % w.r.t. ACns. In doing this, it first computes the bitcode union of all 
%% % abstract variables which are non-ground, free, and non-free, respectively.
%% % Then itobtains the set of program variables in Sv which are ground,
%% % non-ground, free, and non-free, respectively. Finally, if the goal delays
%% % Flag is set to d, if it does not delay, it is set to w, and otherwise,
%% % it will contain the set of abtsractions under which the goal is woken.
%% %-------------------------------------------------------------------------
%% aeq_check_cond(Conds,AEqs,Sv,Flag,WConds):-
%%      aeq_abs_sort(AEqs,AEqs_s),
%%      aeq_check_cond(Conds,AEqs_s,Sv,[],Flag,[],WConds).
%% 
%% %-------------------------------------------------------------------------
%% % aeq_check_cond(+,+,+,+,+,+,+,+,-)
%% % aeq_check_cond(Conds,AEqs,G,NG,F,NF,Acc,Sv,Flag)
%% %-------------------------------------------------------------------------
%% % G,NG,F and NF are the set of program ground, non-ground, free, and 
%% % non-free program variables in the subgoal, respectively.
%% % Conds is a list of elements of the form (Gr,Nv), where Gr and Nv are 
%% % ordered sets of program variables. It represents the conditions under
%% %  which a subgoal will be woken or delayed.
%% %   * If forall (Gr,Nv), at least one variable in Gr or Nv is non-ground 
%% %     or variable, respectively, w.r.t. ACons, Flag = d (the goal is 
%% %     definitely delayed)
%% %   * If for at least one (Gr,Nv), all variables in Gr and Nv are ground 
%% %     and non-var, respectively, w.r.t ACons, Flag = w (the goal is 
%% %     definitely woken)
%% %   * Otherwise, Flag is the set of abstractions under which the goal will
%% %     be woken, projected over Sv.
%% %-------------------------------------------------------------------------
%% 
%% aeq_check_cond([],_,_,Acc,Flag,WAcc,WConds):-
%%      ( Acc = [] -> % all conditions failed -> definitely woken
%%          Flag = d
%%      ; Flag = Acc,
%%        WConds = WAcc).
%% aeq_check_cond([(Gr,Nv,Eq)|Rest],AEqs,Sv,Acc,Flag,WAcc,WConds):-
%%      ( aeq_make_awoken(AEqs,Gr,Nv,Eq,Sv,Flag2) -> 
%%          ( Flag2 = w ->
%%              Flag = w,
%%              WConds = [(Gr,Nv,Eq)]
%%          ;   aeq_check_cond(Rest,AEqs,Sv,[Flag2|Acc],Flag,[(Gr,Nv,Eq)|WAcc],WConds))
%%      ; aeq_check_cond(Rest,AEqs,Sv,Acc,Flag,WAcc,WConds)).
%%          
%% %-------------------------------------------------------------------------
%% % aeq_make_awoken(+,+,+,+,-)
%% % aeq_make_awoken(AEqs,G,NF,Sv,Flag)
%% %-------------------------------------------------------------------------
%% % It obtains NewAEqs, which is the result of making the program variables
%% % in G and NF ground and non-free in AEqs, without obtaining an incomparable
%% % abstraction (i.e., without making a free variables become instantiated) 
%% % In doing this we first look for the abstract variables in AEqs corresponding
%% % to G and NF which are possible non-ground (appear in NonGr).
%% % We then eliminate sharing sets which contain vars in G_ic. If set-sharing
%% % is being computed, we have also to check that no free or non-ground vars 
%% % have become ground. So we collect in G1_ic the total list of variables
%% % that have to become ground.  Also, if the annotation contains 'g', we 
%% % eliminate from NF_ic those abstract vars which have to be made 
%% % ground (G1_ic) obtaining NF1_ic. Finally, we change the annotation and
%% % project the resulting abstraction over Sv. 
%% % If 
%% %-------------------------------------------------------------------------
%% aeq_make_awoken(aeqs(Eqs,Ann,Shr,AVars_ic,NonGr),G,NF,Eq,Sv,Flag):-
%%      aeq_get_g_ic_nf_ic(G,NF,Eqs,0,G0_ic,0,NF0_ic),
%%      bitset_intersect(G0_ic,NonGr,G_ic),
%%      bitset_intersect(NF0_ic,NonGr,NF_ic),
%%      ( G_ic = 0 ->
%%          Shr_o = Shr,
%%          NonGr_o = NonGr,
%%          Ann0 = Ann,
%%          NF1_ic = NF_ic
%%      ; aeq_split_disjoint(Shr,G_ic,Shr_o),
%%        ( aeq_current_sharing(pair) ->
%%            bitset_subtract(NonGr,G_ic,NonGr_o),
%%            G1_ic = G_ic
%%        ;  bitset_union_list(Shr_o,NonGr_o),
%%           bitset_subtract(NonGr,NonGr_o,G1_ic)
%%        ),
%%        bitcode_to_set(G1_ic,G_ec),
%%        aeq_make_old_ground(G_ec,Ann,Ann0,Fl),
%%        bitset_subtract(NF_ic,G1_ic,NF1_ic)),
%%      bitcode_to_set(NF1_ic,NF_ec),
%%      aeq_make_old_non_free(NF_ec,Ann0,Ann_o,Fl),
%%      ( Fl = equiv ->
%%          bitset_subtract(AVars_ic,NonGr_o,Gr_ic),
%%          aeq_check_eq(Eq,Eqs,Ann_o,Shr_o,AVars_ic,NonGr_o,Gr_ic,Sv,Flag)
%%      ; aeq_project(aeqs(Eqs,Ann_o,Shr_o,AVars_ic,NonGr_o),Sv,Flag)).
%% 
%% aeq_check_eq(Eq,Eqs,_,Shr,_,_,G_ic,_,Flag):-
%%      aeq_satisf_eq(Eq,Eqs,Shr,G_ic),!,
%%      Flag = w.
%% aeq_check_eq(Eq,Eqs,Ann,Shr,_,_,_,_,_):-
%%      aeq_fail_eq(Eq,Eqs,Ann,Shr),!,
%%      fail.
%% aeq_check_eq(_,Eqs,Ann,Shr,AVars_ic,NonGr,_,Sv,Flag):-
%%      aeq_project(aeqs(Eqs,Ann,Shr,AVars_ic,NonGr),Sv,Flag).
%% 
%% aeq_satisf_eq([],_,_,_).
%% aeq_satisf_eq([eq(X,Y)|Eq],Eqs,Shr,G_ic):-
%%      aeq_substitute(X,Eqs,AX),
%%      aeq_substitute(Y,Eqs,AY),
%%      aeq_satisf_eq([AX=AY],Shr,G_ic),!,
%%      aeq_satisf_eq(Eq,Eqs,Shr,G_ic).
%% 
%% aeq_satisf_eq([],_,_).
%% aeq_satisf_eq([X=Y|Rest],Shr,G_ic):-
%%      ( X == Y ->
%%          NRest = Rest
%%      ; ( avar_ic(X,X_ic) ->
%%           aeq_satisf_eq_one(Y,X_ic,Shr,G_ic),
%%           NRest = Rest
%%        ; ( avar_ic(Y,Y_ic) ->
%%           aeq_satisf_eq_one(X,Y_ic,Shr,G_ic),
%%           NRest = Rest
%%          ; X =..[ F | Args1 ],
%%            Y =..[ F | Args2 ],
%%            aeq_add_equations(Args1,Args2,Rest,NRest)))),
%%       aeq_satisf_eq(NRest,Shr,G_ic).
%% 
%% 
%% aeq_satisf_eq_one(X,Y_ic,Shr,G_ic):-
%%      avariables_ic(X,X_ic),
%%      bitset_union(X_ic,Y_ic,XY_ic),
%%      ( bitset_subset(XY_ic,G_ic) ->
%%          true
%%      ; \+ (bitset_member(Y_ic,G_ic)),
%%        \+ (bitset_subset(X_ic,G_ic)),
%%        aeq_split_intersect_disjoint(Shr,XY_ic,Intersect,_),
%%        ( aeq_split_intersect_disjoint(Intersect,Y_ic,_,[]); ord_split_lists(Intersect,X_ic,_,[]))).
%% 
%% 
%% aeq_fail_eq([eq(X,Y)|_],Eqs,Ann,Shr):-
%%      aeq_substitute(X,Eqs,AX),
%%      aeq_substitute(Y,Eqs,AY),
%%      aeq_fail_eq([AX=AY],Ann,Shr),!.
%% aeq_fail_eq([_|Eq],Eqs,Ann,Shr):-
%%      aeq_fail_eq(Eq,Eqs,Ann,Shr).
%%   
%% aeq_fail_eq([X=Y|Rest],Ann,Shr):-
%%      ( X == Y ->
%%       aeq_fail_eq(Rest,Ann,Shr)
%%      ; ( X = '@'(X_ec),
%%           (aeq_fail_eq_one(Y,X_ec,Ann,Shr);aeq_fail_eq(Rest,Ann,Shr))
%%        ; ( Y = '@'(Y_ec) ->
%%           (aeq_fail_eq_one(X,Y_ec,Ann,Shr);aeq_fail_eq(Rest,Ann,Shr))
%%          ; X =..[ F | Args1 ],
%%            Y =..[ F | Args2 ],
%%            aeq_add_equations(Args1,Args2,Rest,NRest),
%%            aeq_fail_eq(NRest,Ann,Shr)))).
%% 
%% aeq_fail_eq_one(X,Y_ec,Ann,Shr) :-
%%      aref(Y_ec,Ann,AnnY),
%%      avariables_ic(X, X_ic),
%%      Y_ic is 1 << Y_ec,
%%      ( AnnY = f ->
%%        aeq_split_intersect_disjoint(Shr,X_ic,Intersect,_),
%%        aeq_split_intersect_disjoint(Shr,Y_ic,0,_)
%%        ;( X = '@'(X_ec),
%%        aref(X_ec,Ann,AnnX),
%%        AnnX = f,
%%        aeq_split_intersect_disjoint(Shr,X_ic,Intersect,_),
%%        aeq_split_intersect_disjoint(Shr,Y_ic,0,_))).
%%      
%% 
%% %------------------------------------------------------------------------%
%% % aeq_get_g_ic_nf_ic(+,+,+,+,-,+,-)
%% % aeq_get_g_ic_nf_ic(G,NF,Eqs,0,G_ic,0,NF_ic),
%% %------------------------------------------------------------------------%
%% % Given the set of program variables G and NF, and the set of abstract 
%% % equations Eqs, it obtains in G_ic the set of abstract variables 
%% % associated to the program vars in G, and it obtains in NF_ic all 
%% % abstract variables s.t. X \in NF, X = '@'(N) \in Eqs.
%% % Assumption: G and NF are disjoint
%% %------------------------------------------------------------------------%
%% aeq_get_g_ic_nf_ic([],[],_,G_ic,G_ic,NF_ic,NF_ic):- !.
%% aeq_get_g_ic_nf_ic(G,NF,[X=ATerm|Eqs],G0_ic,G_ic,NF0_ic,NF_ic):-
%%      ( G = [Y|GT], X == Y ->
%%          avariables_ic(ATerm,G0_ic,G1_ic),
%%          NFT = NF,
%%          NF1_ic = NF0_ic
%%      ; G = GT, G1_ic = G0_ic,
%%        ( NF = [Y|NFT], X == Y ->
%%          ( avar_ic(ATerm,AVar_ic) ->
%%              NF1_ic is NF0_ic \/ AVar_ic
%%          ;  NF1_ic = NF0_ic)
%%        ;  NFT = NF, NF1_ic = NF0_ic)),
%%      aeq_get_g_ic_nf_ic(GT,NFT,Eqs,G1_ic,G_ic,NF1_ic,NF_ic).
%% 
%% %-------------------------------------------------------------------------
%% % aeq_make_old_ground(+,+,-)
%% % aeq_make_old_ground(G_ec,Ann0,Ann):-
%% %-------------------------------------------------------------------------
%% % Ann is the result of making all variables in G_ec ground. It fails if
%% % there exists at least a non-ground variable in G_ec.
%% %-------------------------------------------------------------------------
%% aeq_make_old_ground([],Ann,Ann,_).
%% aeq_make_old_ground([X|G],Ann0,Ann,Flag):-
%%      aref(X,Ann0,Ref),
%%      ann_possibly_ground(Ref),
%%      ( Ref = g ->
%%          Ann1 = Ann0
%%      ;   aset(X,Ann0,g,Ann1),
%%          Flag = diff),
%%      aeq_make_old_ground(G,Ann1,Ann,Flag).
%%      
%% %-------------------------------------------------------------------------
%% % aeq_make_old_non_free(+,+,-)
%% % aeq_make_old_non_free(NF_ec,Ann0,Ann):-
%% %-------------------------------------------------------------------------
%% % Ann is the result of making all variables in NF_ec non-free. It fails if
%% % there exists at least a free variable in NF_ec.
%% %-------------------------------------------------------------------------
%% aeq_make_old_non_free([],Ann,Ann,_).
%% aeq_make_old_non_free([X|NF],Ann0,Ann,Flag):-
%%      aref(X,Ann0,Ref),
%%      Ref \== f,
%%      ( ann_non_free(Ref) ->
%%          Ann1 = Ann0
%%      ; ann_add_non_free(Ref,AnnX),
%%        aset(X,Ann0,AnnX,Ann1),
%%           Flag = diff),
%%      aeq_make_old_non_free(NF,Ann1,Ann,Flag).
%%      
%% %------------------------------------------------------------------------%
%% % aeq_more_instantiate(+,+)                                              %
%% % aeq_more_instantiate(ASub0,ASub1)                                      %
%% %------------------------------------------------------------------------%
%% % Succeeds if ASub1 is possibly more instantiated or equal to ASub0. In  %
%% % fact what we want to prove is that ASub1 corresponds to a node in the  %
%% % abstract ADN-OR tree which is greater than that of ASub0 (so it must   %
%% % be more instantiated)                                                  %
%% % By now, this means:                                                    %
%% %   - there must exists a substitution Theta s.t. for each X = ATerm0, 
%% %     X = ATerm1, ATerm0 Theta = ATerm1
%% %   - Once applied, everything ground in ASub0 must be ground in ASub1 
%% %   - for each X free in ASub1, X cannot be ground in ASub0, neither nonvar
%% % WARNING, incomplete since definite dependencies in ASub0 afecting      %
%% % variables which are also free in ASub1, must appear in ASub1           %
%% %------------------------------------------------------------------------%
%% 
%% aeq_more_instantiate(AEqs0,AEqs1):-
%%      AEqs0 = aeqs(Eqs0,_,_,_,_),
%%      AEqs1 = aeqs(Eqs1,_,_,_,_),
%%      sort(Eqs0,Eqs0_s),sort(Eqs1,Eqs1_s),
%%      new_array(Sigma_i),
%%      aeq_more_instantiate(Eqs1_s,AEqs1,Eqs0_s,AEqs0,Sigma_i),!.
%% %% aeq_more_instantiate(_,_):-
%% %%   write('aeq_more_instantiate/2 fails'),nl,
%% %% %%        myspy,
%% %%   fail.

%% myspy.
%% 
%% my_print_aeqs(AEqs):-
%%      aeq_abs_sort(AEqs,AEqs_s), aeq_intern_to_extern(AEqs_s,AEqsN),
%%      write(AEqsN),nl.

%% aeq_more_instantiate([],_,[],_,_).
%% aeq_more_instantiate([_=T1|Eqs1],AEqs1,[_=T2|Eqs2],AEqs2,Sigma) :-
%%      aeq_can_be_more_instantiate(T1,AEqs1,T2,AEqs2,Sigma,Sigma_new),
%%      aeq_more_instantiate(Eqs1,AEqs1,Eqs2,AEqs2,Sigma_new) .
%% 
%% aeq_can_be_more_instantiate([],_AEqs1,[],_AEqs2,Sigma,Sigma) :- ! .
%% aeq_can_be_more_instantiate([H1|T1],AEqs1,[H2|T2],AEqs2,Sigma_i,Sigma_o) :- !,
%%      aeq_can_be_more_instantiate(H1,AEqs1,H2,AEqs2,Sigma_i,Sigma_new),
%%      aeq_can_be_more_instantiate(T1,AEqs1,T2,AEqs2,Sigma_new,Sigma_o).
%% aeq_can_be_more_instantiate(T1,AEqs1,'@'(T2_ec),AEqs2,Sigma_i,Sigma_o) :- !,
%%      arefl(T2_ec,Sigma_i,T2_sigma),
%%      (T2_sigma == [] ->
%%          AEqs2 = aeqs(_,Ann,_,_,_),
%%          aref(T2_ec,Ann,AnnT2),
%%          aeq_more_instant_ann(AnnT2,T1,AEqs1),
%%          aset(T2_ec,Sigma_i,T1,Sigma_o)
%%      ;  T2_sigma == T1,
%%         Sigma_i = Sigma_o) .
%% aeq_can_be_more_instantiate(T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o) :-
%%      functor(T2,Func,Arity),functor(T1,Func,Arity),
%%      aeq_can_be_more_instantiate(Arity,T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o).
%% 
%% aeq_can_be_more_instantiate(0,_,_,_,_,Sigma,Sigma):- !.
%% aeq_can_be_more_instantiate(Arity,T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o):-
%%      arg(Arity,T1,Arg1),
%%      arg(Arity,T2,Arg2),
%%      aeq_can_be_more_instantiate(Arg1,AEqs1,Arg2,AEqs2,Sigma_i,Sigma_m),
%%      Arity0 is Arity - 1,
%%      aeq_can_be_more_instantiate(Arity0,T1,AEqs1,T2,AEqs2,Sigma_m,Sigma_o).
%% 
%% % satisfied if Ann2 is more instantiated than Ann1
%% 
%% aeq_more_instant_ann(f,_,_).
%% aeq_more_instant_ann(a,_,_).
%% aeq_more_instant_ann(l,_,_).
%% aeq_more_instant_ann(ng,_,_).
%% aeq_more_instant_ann(lng,_,_).
%% aeq_more_instant_ann(nf,ATerm,AEqs):-
%%      \+ free_aeqs(AEqs,ATerm).
%% aeq_more_instant_ann(lnf,ATerm,AEqs):-
%%      \+ free_aeqs(AEqs,ATerm).
%% aeq_more_instant_ann(ngf,ATerm,AEqs):-
%%      \+ free_aeqs(AEqs,ATerm).
%% aeq_more_instant_ann(lngf,ATerm,AEqs):-
%%      \+ free_aeqs(AEqs,ATerm).
%% aeq_more_instant_ann(g,ATerm,AEqs):-
%%      ground_aeqs(AEqs,ATerm).
%% 
%% %------------------------------------------------------------------------%
%% %-------------------------------------------------------------------------
%% % aeq_downwards_closed(+,+,-)
%% % aeq_downwards_closed(ACns1,ACns2,ACns)
%% %-------------------------------------------------------------------------
%% % ACns2 must be more instantiated than ACns1 but some downwards closed
%% % properties might have been lost due to a later lub. Thus, those
%% % properties must be returned to ACns2. Iff something non ground becomes 
%% % ground or something free becomes non-free in ACns2, ACns1 is more 
%% % instantiated than ACns2 and we fail. Otherwise we propagate these
%% % properties from ACns1 to ACns2.
%% %-------------------------------------------------------------------------
%% 
%% aeq_downwards_closed(AEqs1,AEqs2,AEqs):- 
%%      AEqs1 = aeqs(Eqs1,_,_,_,_),
%%      AEqs2 = aeqs(Eqs2,_,_,_,_),
%%      sort(Eqs1,Eqs1_s),sort(Eqs2,Eqs2_s),
%%      new_array(Sigma_i),
%%      aeq_downwards(Eqs1_s,AEqs1,Eqs2_s,AEqs2,Sigma_i,AEqs).
%% 
%% 
%% aeq_downwards([],_,[],AEqs2,_,AEqs2).
%% aeq_downwards([_=T1|Eqs1],AEqs1,[_=T2|Eqs2],AEqs2,Sigma,AEqs) :-
%%      aeq_can_be_downwards(T1,AEqs1,T2,AEqs2,Sigma,Sigma_new,AEqs2_new),
%%      aeq_downwards(Eqs1,AEqs1,Eqs2,AEqs2_new,Sigma_new,AEqs) .
%% 
%% aeq_can_be_downwards([],_,[],AEqs,Sigma,Sigma,AEqs) :- ! .
%% aeq_can_be_downwards([H1|T1],AEqs1,[H2|T2],AEqs2,Sigma_i,Sigma_o,AEqs_new) :- !,
%%      aeq_can_be_downwards(H1,AEqs1,H2,AEqs2,Sigma_i,Sigma_new,AEqs2_o),
%%      aeq_can_be_downwards(T1,AEqs1,T2,AEqs2_o,Sigma_new,Sigma_o,AEqs_new).
%% aeq_can_be_downwards('@'(T1_ec),AEqs1,T2,AEqs2,Sigma_i,Sigma_o,AEqs2_new) :- !,
%%      arefl(T1_ec,Sigma_i,T1_sigma),
%%      (T1_sigma == [] ->
%%          AEqs1 = aeqs(_,Ann,_,_,_),
%%          aref(T1_ec,Ann,AnnT1),
%%          aeq_downwards_ann(AnnT1,T2,AEqs2,AEqs2_new),
%%          aset(T1_ec,Sigma_i,T2,Sigma_o)
%%      ;  T1_sigma == T2,
%%         Sigma_i = Sigma_o,
%%         AEqs2_new = AEqs2).
%% aeq_can_be_downwards(T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o,AEqs2_new) :-
%%      functor(T2,Func,Arity),functor(T1,Func,Arity),
%%      aeq_can_be_downwards(Arity,T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o,AEqs2_new).
%% 
%% aeq_can_be_downwards(0,_,_,_,AEqs2,Sigma,Sigma,AEqs2):- !.
%% aeq_can_be_downwards(Arity,T1,AEqs1,T2,AEqs2,Sigma_i,Sigma_o,AEqs2_new):-
%%      arg(Arity,T1,Arg1),
%%      arg(Arity,T2,Arg2),
%%      aeq_can_be_downwards(Arg1,AEqs1,Arg2,AEqs2,Sigma_i,Sigma_m,AEqs2_o),
%%      Arity0 is Arity - 1,
%%      aeq_can_be_downwards(Arity0,T1,AEqs1,T2,AEqs2_o,Sigma_m,Sigma_o,AEqs2_new).
%%      
%% aeq_downwards_ann(f,_,AEqs2,AEqs2).
%% aeq_downwards_ann(a,_,AEqs2,AEqs2).
%% aeq_downwards_ann(l,_,AEqs2,AEqs2).
%% aeq_downwards_ann(ng,_,AEqs2,AEqs2).
%% aeq_downwards_ann(lng,_,AEqs2,AEqs2).
%% aeq_downwards_ann(nf,ATerm,AEqs2,AEqs2_new):-
%%      check_nonfree(ATerm,AEqs2,AEqs2_new).
%% aeq_downwards_ann(lnf,ATerm,AEqs2,AEqs2_new):-
%%      check_nonfree(ATerm,AEqs2,AEqs2_new).
%% aeq_downwards_ann(ngf,ATerm,AEqs2,AEqs2_new):-
%%      check_nonfree(ATerm,AEqs2,AEqs2_new).
%% aeq_downwards_ann(lngf,ATerm,AEqs2,AEqs2_new):-
%%      check_nonfree(ATerm,AEqs2,AEqs2_new).
%% aeq_downwards_ann(g,ATerm,AEqs2,AEqs2_new):-
%%      avariables_ec(ATerm,Vars_ec),
%%      AEqs2 = aeqs(A,Ann,B,C,D),
%%      aeq_make_old_ground(Vars_ec,Ann,Ann0,_),
%%      AEqs2_new = aeqs(A,Ann0,B,C,D).
%% 
%% check_nonfree('@'(T2_ec),AEqs2,AEqs2_new):- !,
%%      AEqs2 = aeqs(A,Ann,B,C,D),
%%      aref(T2_ec,Ann,Item2),
%%      Item2 \== f,
%%      ann_add_non_free(Item2,NewItem2),
%%      aset(T2_ec,Ann,NewItem2,NewAnn),
%%      AEqs2_new = aeqs(A,NewAnn,B,C,D).
%% check_nonfree(_,AEqs2,AEqs2).
%% 
%% %-------------------------------------------------------------------------
%% % aeq_extend_free(+,+,-)
%% % aeq_extend_free(ASub,Vars,NewASub)
%% %-------------------------------------------------------------------------
%% % Extends ASub to include the variables in Vars as free vars.
%% %-------------------------------------------------------------------------
%% 
%% aeq_extend_free(AEqs,Vars,AEqs_new):-
%%      (aeq_current_sharing(pair) ->
%%        aeq_init_new_varsPS(Vars,0,AEqs,AEqs_new)
%%      ; aeq_init_new_vars(Vars,0,AEqs,AEqs_new)).
%% 
%% %------------------------------------------------------------------------%
%% % aeq_hash(+,-)
%% % aeq_hash(ASub,N)
%% %------------------------------------------------------------------------%
%% % Returns an atom which identifies ASub
%% %------------------------------------------------------------------------%
%% 
%% aeq_hash('$bottom',_,-2).
%% aeq_hash(true,_,0).
%% aeq_hash(aeqs(Eqs,Ann,_,_,_),Fnv,N):-
%%      \+ \+
%%      (  primes(Primes),
%% %%      aeq_collect_main_vars(Eqs,Vars),
%% %%      append(Vars,_,Primes),
%%         append(Fnv,_,Primes),
%%         aeq_hash(Eqs,Ann,0,N1),
%%         recorda_internal('$hash',N1,_) ),
%%      recorded_internal('$hash',N,Ref),
%%      erase(Ref).
%% 
%% aeq_collect_main_vars([],[]).
%% aeq_collect_main_vars([X=_|Eqs],[X|Vars]):-
%%      aeq_collect_main_vars(Eqs,Vars).
%% 
%% aeq_hash([],_,N,N).
%% aeq_hash([P=ATerm|Rest],Ann,N0,N):-
%%      aeq_hash_aterm(ATerm,Ann,P,N0,N1),
%%      aeq_hash(Rest,Ann,N1,N).
%% 
%% aeq_hash_aterm(Term,_,_,N0,N) :-
%%      atomic(Term),!,
%%      N0 = N.
%% aeq_hash_aterm('@'(AVar_ec),Ann,P,N0,N) :- !,
%%      aref(AVar_ec,Ann,Item),
%%      ( Item == g ->
%%          N is N0+P
%%      ; ( Item == f ->
%%            N is N0-P
%%        ; N = N0)).
%% aeq_hash_aterm([H|T],Ann,P,N0,N) :- !,
%%      aeq_hash_aterm(H,Ann,P,N0,N1),
%%      aeq_hash_aterm(T,Ann,P,N1,N).
%% aeq_hash_aterm(Term,Ann,P,N0,N) :-
%%      functor(Term,_,Arity),
%%      aeq_hash_aterm(Arity,Term,Ann,P,N0,N).
%% 
%% aeq_hash_aterm(0,_,_,_,N0,N0):- !.
%% aeq_hash_aterm(Arity,Term,Ann,P,N0,N):-
%%      arg(Arity,Term,Arg),
%%      aeq_hash_aterm(Arg,Ann,P,N0,N1),
%%      Arity0 is Arity - 1,
%%      aeq_hash_aterm(Arity0,Term,Ann,P,N1,N).
%% 
%% %-------------------------------------------------------------------------
%% % aeq_impose_cond(+,+,+,-)
%% % aeq_impose_cond(Conds,ACns,Sv,LASub)
%% %-------------------------------------------------------------------------
%% 
%% aeq_impose_cond([],_,_,[]).
%% aeq_impose_cond([(Gr,Nv,_)|Rest],Sv,ASub,[ASub1|LASub]):-
%%      get_Eqs_aeqs(ASub, Eqs_sf),
%%      avariables_ic_subst(Gr,Eqs_sf,Gr_ic),
%%      aeq_make_ground(Gr_ic,ASub,TmpASub),
%%      avariables_ic_subst(Nv,Eqs_sf,Nv_ic),
%%      bitcode_to_set(Nv_ic,Nv_ec),
%%      TmpASub = aeqs(Eqs_nsf,TmpAnn,Shr,AVarSet,NGrAVars),
%%      aeq_make_non_free(Nv_ec,TmpAnn,Ann),
%%      ASub0 = aeqs(Eqs_nsf,Ann,Shr,AVarSet,NGrAVars),
%%      aeq_project(ASub0,Sv,ASub1),
%%      aeq_impose_cond(Rest,Sv,ASub,LASub).
%% 
%% aeq_make_non_free([],Ann,Ann).
%% aeq_make_non_free([Nv_ec|Rest],Ann0,Ann):-
%%      aref(Nv_ec,Ann0,Item),
%%      ann_add_non_free(Item,Item0),
%%      aset(Nv_ec,Ann0,Item0,Ann1),
%%      aeq_make_non_free(Rest,Ann1,Ann).
%% 
%% %------------------------------------------------------------------------%
%% % aeq_convex_hull(+,+,-)
%% % aeq_convex_hull(Old,New,Hull)
%% %------------------------------------------------------------------------%
%% % Computes the convex hull between the initial abstraction Old and the
%% % more instantiated one New           
%% %------------------------------------------------------------------------%
%% 
%% aeq_convex_hull(aeqs(Eqs0,Ann0,Sh0,Vars,NgVars),AEqs1,aeqs(Eqs0,Ann,Sh,Vars,NgVars)):- !,
%%      full_set_closure(Sh0,Sh),
%%      AEqs1 = aeqs(Eqs1,_,_,_,_),
%%      sort(Eqs0,Eqs0_s),sort(Eqs1,Eqs1_s),
%%      new_array(Sigma_i),
%%      aeq_convex_hull_ann(Eqs0_s,Ann0,Eqs1_s,AEqs1,Sigma_i,Ann).
%% aeq_convex_hull(_,_,'$bottom').
%% 
%% aeq_convex_hull_ann([],Ann,[],_,_,Ann).
%% aeq_convex_hull_ann([_=T1|Eqs1],Ann1,[_=T2|Eqs2],AEqs2,Sigma,Ann) :-
%%      aeq_can_be_convex_hull_ann(T1,Ann1,T2,AEqs2,Sigma,Sigma_new,Ann2),
%%      aeq_convex_hull_ann(Eqs1,Ann2,Eqs2,AEqs2,Sigma_new,Ann).
%% 
%% aeq_can_be_convex_hull_ann([],Ann,[],_,Sigma,Sigma,Ann) :- ! .
%% aeq_can_be_convex_hull_ann([H1|T1],Ann1,[H2|T2],AEqs2,Sigma_i,Sigma_o,Ann) :- !,
%%      aeq_can_be_convex_hull_ann(H1,Ann1,H2,AEqs2,Sigma_i,Sigma_new,Ann2),
%%      aeq_can_be_convex_hull_ann(T1,Ann2,T2,AEqs2,Sigma_new,Sigma_o,Ann).
%% aeq_can_be_convex_hull_ann('@'(T1_ec),Ann1,T2,AEqs2,Sigma_i,Sigma_o,Ann) :- !,
%%      arefl(T1_ec,Sigma_i,T1_sigma),
%%      (T1_sigma == [] ->
%%          aref(T1_ec,Ann1,Item1),
%%          get_ann_aterm(AEqs2,T2,Item2),
%%          ann_hull(Item1,Item2,Item),
%%          aset(T1_ec,Ann1,Item,Ann),
%%          aset(T1_ec,Sigma_i,T2,Sigma_o)
%%      ;  T1_sigma == T2,
%%         Sigma_i = Sigma_o, Ann = Ann1) .
%% aeq_can_be_convex_hull_ann(T1,Ann1,T2,AEqs2,Sigma_i,Sigma_o,Ann) :-
%%      functor(T2,Func,Arity),functor(T1,Func,Arity),
%%      aeq_can_be_convex_hull_ann(Arity,T1,Ann1,T2,AEqs2,Sigma_i,Sigma_o,Ann).
%% 
%% aeq_can_be_convex_hull_ann(0,_,Ann,_,_,Sigma,Sigma,Ann):- !.
%% aeq_can_be_convex_hull_ann(Arity,T1,Ann1,T2,AEqs2,Sigma_i,Sigma_o,Ann):-
%%      arg(Arity,T1,Arg1),
%%      arg(Arity,T2,Arg2),
%%      aeq_can_be_convex_hull_ann(Arg1,Ann1,Arg2,AEqs2,Sigma_i,Sigma_m,Ann2),
%%      Arity0 is Arity - 1,
%%      aeq_can_be_convex_hull_ann(Arity0,T1,Ann2,T2,AEqs2,Sigma_m,Sigma_o,Ann).
%% 
%% %------------------------------------------------------------------------%
%% % ann_hull(+,+,-)
%% % ann_hull(Item1,Item2,Lub)
%% %------------------------------------------------------------------------%
%% % Computes the lub of Item1 and Item2 knowing that Item1 must be less
%% % instantiated than Item2
%% %------------------------------------------------------------------------%
%% ann_hull(a,_,a).
%% ann_hull(f,Item2,Lub):-    ann_hull_f(Item2,Lub).
%% ann_hull(g,g,g).
%% ann_hull(lngf,Item2,Lub):- ann_hull_lngf(Item2,Lub).
%% ann_hull(lng,Item2,Lub):-  ann_hull_lng(Item2,Lub).
%% ann_hull(lnf,Item2,Lub):-  ann_hull_lnf(Item2,Lub).
%% ann_hull(l,Item2,Lub):-    ann_hull_l(Item2,Lub).
%% ann_hull(ngf,Item2,Lub):-  ann_hull_ngf(Item2,Lub).
%% ann_hull(ng,Item2,Lub):-   ann_hull_ng(Item2,Lub).
%% ann_hull(nf,Item2,Lub):-   ann_hull_nf(Item2,Lub).
%% 
%% ann_hull_f(a,a).
%% ann_hull_f(f,f).
%% ann_hull_f(g,a).
%% ann_hull_f(lngf,lng).
%% ann_hull_f(lng,lng).
%% ann_hull_f(lnf,l).
%% ann_hull_f(l,l).
%% ann_hull_f(ngf,ng).
%% ann_hull_f(ng,ng).
%% ann_hull_f(nf,a).
%% 
%% ann_hull_lngf(g,nf).
%% ann_hull_lngf(lngf,lngf).
%% ann_hull_lngf(lnf,lnf).
%% ann_hull_lngf(ngf,ngf).
%% ann_hull_lngf(nf,nf).
%% 
%% ann_hull_lng(a,a).
%% ann_hull_lng(g,a).
%% ann_hull_lng(lngf,lng).
%% ann_hull_lng(lng,lng).
%% ann_hull_lng(lnf,l).
%% ann_hull_lng(l,l).
%% ann_hull_lng(ngf,ng).
%% ann_hull_lng(ng,ng).
%% ann_hull_lng(nf,a).
%% 
%% ann_hull_lnf(g,nf).
%% ann_hull_lnf(lnf,lnf).
%% ann_hull_lnf(ngf,nf).
%% ann_hull_lnf(nf,nf).
%% 
%% ann_hull_l(a,a).
%% ann_hull_l(g,a).
%% ann_hull_l(lnf,l).
%% ann_hull_l(l,l).
%% ann_hull_l(nf,a).
%% 
%% ann_hull_ngf(a,a).
%% ann_hull_ngf(g,a).
%% ann_hull_ngf(ngf,ngf).
%% ann_hull_ngf(nf,nf).
%% 
%% ann_hull_ng(a,a).
%% ann_hull_ng(g,a).
%% ann_hull_ng(ngf,ng).
%% ann_hull_ng(ng,ng).
%% ann_hull_ng(nf,a).
%% 
%% ann_hull_nf(g,nf).
%% ann_hull_nf(nf,nf).

%% :- mode
%%      proj_array_to_array(+,+,-),             
%%      proj_subarray_to_array(+,+,+,+,+,-). 

%-------------------------------------------------------------------------
% proj_array_to_array(+,+,-) 
% proj_array_to_array(Array, IndexSet_ic, Proj_Array) 
%-------------------------------------------------------------------------
% Proj_Array contains the elements in Array that have been set and 
% belong to IndexSet_ic.
%-------------------------------------------------------------------------
proj_array_to_array(array($(A0,A1,A2,A3),Size), AVars, array($(L0,L1,L2,L3),Size)) :-
    N is Size-2,
    proj_subarray_to_array(0, N, 0, A0, AVars, L0), 
    proj_subarray_to_array(1, N, 0, A1, AVars, L1), 
    proj_subarray_to_array(2, N, 0, A2, AVars, L2), 
    proj_subarray_to_array(3, N, 0, A3, AVars, L3).

proj_subarray_to_array(_K, _N, _M, $, _AVars, $) :- ! .
proj_subarray_to_array(K, 0, M, Item, AVars, L) :- !,
    N is K+M, 
    N_ic is 1 << N,  
    ( bitset_member( N_ic, AVars) -> 
        L = Item
    ;   L = $).
proj_subarray_to_array(K, N, M, $(A0,A1,A2,A3), AVars, $(L0,L1,L2,L3) ) :-
    N1 is N-2,
    M1 is (K+M)<<2,
    proj_subarray_to_array(0, N1, M1, A0, AVars, L0),
    proj_subarray_to_array(1, N1, M1, A1, AVars, L1),
    proj_subarray_to_array(2, N1, M1, A2, AVars, L2),
    proj_subarray_to_array(3, N1, M1, A3, AVars, L3).

:- pop_prolog_flag(multi_arity_warnings).
