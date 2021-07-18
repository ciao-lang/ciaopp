:- module(lsign,
    [ lsign_init_abstract_domain/1,
      lsign_call_to_entry/9,
      lsign_call_to_success_fact/9,  
      lsign_compute_lub/2,
      lsign_extend/5,   
      lsign_eliminate_equivalent/2,
      lsign_exit_to_prime/7,
      lsign_global_info/5,
      lsign_input_user_interface/5,  
      lsign_input_interface/4,  
      lsign_asub_to_native/5,
      lsign_abs_subset/2,
      lsign_less_or_equal/2,
      lsign_glb/3,
      lsign_project/5,    
      lsign_abs_sort/2,       
      lsign_special_builtin/5,
      lsign_success_builtin/6,
      lsign_unknown_call/4,
      lsign_unknown_entry/3,
      lsign_empty_entry/3
    ], [assertions]).

:- doc(title, "lsign domain").

:- include(ciaopp(plai/plai_domain)).
:- dom_def(lsign).
:- dom_impl(lsign, init_abstract_domain/1).
:- dom_impl(lsign, call_to_entry/9).
:- dom_impl(lsign, exit_to_prime/7).
:- dom_impl(lsign, project/5).
:- dom_impl(lsign, compute_lub/2).
:- dom_impl(lsign, abs_sort/2).
:- dom_impl(lsign, extend/5).
:- dom_impl(lsign, less_or_equal/2).
:- dom_impl(lsign, glb/3).
:- dom_impl(lsign, eliminate_equivalent/2).
:- dom_impl(lsign, abs_subset/2).
:- dom_impl(lsign, call_to_success_fact/9).
:- dom_impl(lsign, special_builtin/5).
:- dom_impl(lsign, success_builtin/6).
:- dom_impl(lsign, input_interface/4).
:- dom_impl(lsign, input_user_interface/5).
:- dom_impl(lsign, asub_to_native/5).
:- dom_impl(lsign, unknown_call/4).
:- dom_impl(lsign, unknown_entry/3).
:- dom_impl(lsign, empty_entry/3).

:- use_module(engine(io_basic)).
:- use_module(domain(deftools), [find_type/2]).
:- use_module(domain(s_grshfr), 
    [ asubs_to_dep/3,
      asubs_to_indep/2,
      dep_to_indep/3,
      change_values_insert/4,
      collect_vars_freeness/2,
      create_values/3,
      ground_conds/3,
      indep_imply_indep/5,
      not_ground_conds/3,
      not_indep_conds_one_var/4
    ]).

:- use_module(library(lists), 
    [ append/3,
      length/2,
      list_to_list_of_lists/2,
      powerset/2,
      reverse/2
    ]).
:- use_module(library(lsets), [transitive_closure_lists/3]).
:- use_module(library(lsets), 
    [ closure_under_union/2,
      merge_list_of_lists/2, 
      ord_split_lists/4,
      ord_split_lists_from_list/4
    ]).
:- use_module(library(messages)).
:- use_module(library(sets), 
    [ insert/3, 
      merge/3,
      ord_intersect/2,
      ord_intersection/3,
      ord_member/2, 
      ord_subset/2, 
      ord_subtract/3,
      ord_union_diff/4
    ]).
:- use_module(library(sort)).
:- use_module(library(terms_check), [variant/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(domain(share_aux), [if_not_nil/4]).

:- use_module(ciaopp(plai/plai_errors), [compiler_error/1]).

%------------------------------------------------------------------------%
%                                                                        %
%                          started: 1/5/95                               %
%                       programmer: M. Garcia de la Banda                %
%                                                                        %
%------------------------------------------------------------------------%
%                                                                        %
% PBC -- the intended meaning of Op is a constraint operator plus the    %
%        multiplicity of constraints abstracted                          %
%      - eq is =,  leq is =<,  less is <                                 %
%      - =< and < are assumed multiplicity Any                           %
%      - the multiplicity for = is given by:                             %
%            eq is One, eq+ is ZweoOrOne, eq? is Any, eqx is OneOrMore   %
%           (not sure about eq+ and eqx, might be the other way around)  %
%                                                                        %
%------------------------------------------------------------------------%
%                    Meaning of the Program Variables                    %
%                                                                        %
% Sign     : sign of a particular coefficient. It is an element of       %
%            {+,-,0,t} (positive, negative, zero, top).                  %
% Expr     : ordered list of elements of the form X/Sign, where X is a   %
%            variable and Sign is its sign, s.t. Sign \== 0 (if Sign=0,  %
%            X is removed from the expression)                           %
% Op       : constraint predicate symbol for equation or inequation,     %
%            thus it is an element of {eq,eq+,eq?,eqx,leq,less}.         %
% Eq       : Equation, it has the form eq(Op,Sign,Expr), where Op is an  %
%            element of {eq,eq+,eq?,eqx}.                                %
% LEq      : List of equations                                           %
% In       : Inequation, it has the form eq(Op,Sign,Expr), where Op is   %
%            an element of {leq,less}.                                   %
% LIn      : List of inequations                                         %
% EqIn     : Equation or inequation.                                     %
% ACons    : abstract constraint, it is of the form a(S,AEqIn,Non), where%
%            S is the set of ground variables, AEqIn is the abstract set %
%            of linear equations and inequations, and Non is the set of  %
%            abstract non linear equations, possibly non woken. The      %
%            elements of S are of the form X/Sign where X is a variable  %
%            and Sign is in {+,-,0,t}. It represents the abstrcat        %
%            equation eq(Op,Sign,[X/+]}, where Op is in {eq,eq+}. Note   %
%            that AEqIn includes the abstractions for the equations      %
%            represented in the S component.                             %
%------------------------------------------------------------------------%

:- op(600,xfx,'<=').
:- op(500,xfx,eq).
:- op(500,xfx,'eq+').
:- op(500,xfx,'eq?').
:- op(500,xfx,eqx).
:- op(500,xfx,leq).
:- op(500,xfx,less).

%-------------------------------------------------------------------------

:- use_module(ciaopp(preprocess_flags), [push_pp_flag/2]).
lsign_init_abstract_domain([normalize,variants]) :-
    push_pp_flag(normalize,on),
    push_pp_flag(variants,off).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
%                    NORMALIZATION FUNCTIONS
%-------------------------------------------------------------------------
% lsign_normalize(+,+,+,-)
% lsign_normalize(Op,Sign,Expr,EqIn)
%-------------------------------------------------------------------------
% This predicate normalizes the abstract element eq(Op,Sign,Expr) as 
% follows:
%   - If  the element is an inequation (Op in {leq,less}), it is 
%     already in normal form.
%   - If the element is an equation (Op in {eq,eq+,eq?,eqx}) and Sign
%     is '+', it is also already in normal form.
%   - If the element is an equation and Sign is '-', then the normalized
%     element is eq(Op,'+',NewExpr), where NewExpr is the result of 
%     negating Expr
%   - If the element is an equation and Sign is in {t,0}, then the 
%     normalized element is eq(Op,Sign,NewExpr), where NewExpr is 
%     computed as follows. Let Expr = [X1/S1,X2/S2,...,Xn/Sn], and
%     let Si be the first sign in {+,-}. If Si=+, NewExpr = Expr, 
%     otherwise:
%     NewExpr=[X1/S1,...,Xi-1/Si-1] \cup neg_expr([Xi/Si,...,Xn/Sn])
%
% Assumption made:
%    - none
%-------------------------------------------------------------------------

lsign_normalize(Op,Sign,Expr,Eq):- 
    Op @< leq,!,
    lsign_normalize0(Sign,Op,Expr,Eq).
lsign_normalize(Op,Sign,Expr,eq(Op,Sign,Expr)).

lsign_normalize0('+',Op,Expr,eq(Op,'+',Expr)).
lsign_normalize0('-',Op,Expr,eq(Op,'+',NExpr)):-
    neg_expr(Expr,NExpr).
lsign_normalize0(t,Op,Expr,eq(Op,t,NExpr)):-
    first_coeff_positive(Expr,NExpr).
lsign_normalize0(0,Op,Expr,eq(Op,0,NExpr)):-
    first_coeff_positive(Expr,NExpr).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACTION FUNCTIONS
%-------------------------------------------------------------------------
% lsign_abstract_expr(+,+,+,-,-,?)
% lsign_abstract_expr(Expr,Op0,C0,C,AExpr,Tail)
%-------------------------------------------------------------------------
% Expr is an arithmetic expression of the form:
%             C1 * X1 op2  C2 * X2 op3 ...  opn Cn * Xn
% This predicate abstracts the expression:
%        Op0(C1 * X1) op1  C2 * X2 op2 ...  opn Cn * Xn
% where Op0 is an element of {+,-}. The resulting abstract expression 
% is of the form:  [X1/S1, X2/S2,...,Xn/Sn] where Si is the sign obtained 
% by multiplying the signs of Ci and opi (C1 and Op0).
% 
% Assumptions made:  
%     * Expr is a linear expression
%-------------------------------------------------------------------------

lsign_abstract_expr(Expr,Sign,C0,C,AExpr,Tail):-
    var(Expr),!,
    C = C0, 
    AExpr = [Expr/Sign|Tail].
lsign_abstract_expr(+(Expr),Sign,C0,C,AExpr,Tail):-
    var(Expr),!,
    C = C0, 
    AExpr = [Expr/Sign|Tail].
lsign_abstract_expr(-(Expr),Sign,C0,C,AExpr,Tail):-
    var(Expr),!,
    C0 = C,
    neg_sign(Sign,NSign),
    AExpr = [Expr/NSign|Tail].
lsign_abstract_expr(Expr,Sign,C0,C,AExpr,Tail):-
    number(Expr),!,
    ( Sign = '+' ->
        C is C0 + Expr
    ;   C is C0 - Expr
    ),
    AExpr = Tail.
lsign_abstract_expr(+(Expr),Sign,C0,C,AExpr,Tail):-
    number(Expr),!,
    ( Sign = '+' ->
        C is C0 + Expr
    ;   C is C0 - Expr
    ),
    AExpr = Tail.
lsign_abstract_expr(-(Expr),Sign,C0,C,AExpr,Tail):-
    number(Expr),!,
    ( Sign = '+' ->
        C is C0 - Expr
    ;   C is C0 + Expr
    ),
    AExpr = Tail.
lsign_abstract_expr(X*Expr,Sign,C0,C,AExpr,Tail):- 
    var(Expr),!,
    C = C0,
    ( X > 0 ->
        NSign = Sign
    ;   neg_sign(Sign,NSign)
    ),
    AExpr = [Expr/NSign|Tail].
lsign_abstract_expr(Expr1+Expr2,Sign,C0,C,AExpr,Tail):-
    lsign_abstract_expr(Expr2,'+',C0,C1,AExpr,Tail1),
    lsign_abstract_expr(Expr1,Sign,C1,C,Tail1,Tail).
lsign_abstract_expr(Expr1-Expr2,Sign,C0,C,AExpr,Tail):-
    lsign_abstract_expr(Expr2,'-',C0,C1,AExpr,Tail1),
    lsign_abstract_expr(Expr1,Sign,C1,C,Tail1,Tail).
lsign_abstract_expr(Expr1/Expr2,Sign,C0,C,AExpr,Tail):-
    number(Expr1),
    number(Expr2),
    Expr is Expr1/Expr2,
    lsign_abstract_expr(Expr,Sign,C0,C,AExpr,Tail).

%-------------------------------------------------------------------------
% lsign_abstract_equation(+,+,-,-)
% lsign_abstract_equation(Lhs,Rhs,Sign,Expr)
%-------------------------------------------------------------------------
% The abstraction of the equation Lhs = Rhs is the normalized element
% eq(eq,Sign,Expr). This predicate computes Sign and Expr.
% 
% Assumptions made:
%     * Lhs is a number
%     * Rhs is a linear expression
%-------------------------------------------------------------------------

lsign_abstract_equation(Lhs,Rhs,Sign,Expr):-
    lsign_abstract_expr(Rhs-Lhs,'+',0,C,Expr_u,[]),
    sort(Expr_u,TmpExpr),
    compare(Order,C,0),
    lsign_abstract_equation0(Order,TmpExpr,Sign,Expr).
    
lsign_abstract_equation0(<,Expr,+,Expr).
lsign_abstract_equation0(=,Expr0,0,Expr):-
    first_coeff_positive(Expr0,Expr).
lsign_abstract_equation0(>,Expr0,+,Expr):-
    neg_expr(Expr0,Expr).

%-------------------------------------------------------------------------
% lsign_abstract_inequation(+,+,-,-)
% lsign_abstract_inequation(Lhs,Rhs,Sign,Expr)
%-------------------------------------------------------------------------
% The abstraction of the inequation Lhs {<=,<} Rhs is the normalized element
% eq(eq,Sign,Expr). This predicate computes Sign and Expr.
% 
% Assumptions made:
%     * Lhs is a number
%     * Rhs is a linear expression
%-------------------------------------------------------------------------

lsign_abstract_inequation(Lhs,Rhs,Sign,Expr):-
    lsign_abstract_expr(Rhs-Lhs,'+',0,C,Expr_u,[]),
    sort(Expr_u,Expr),
    get_sign(C,Sign).

get_sign(Number,Sign):-
    compare(Order,Number,0),
    get_sign0(Order,Sign).
    
get_sign0(=,0).
get_sign0(<,-).
get_sign0(>,+).

%------------------------------------------------------------------------%
% lsign_abstract_non_linear(+,+,-)
% lsign_abstract_non_linear(NonLinear,X,AEqIn)
%------------------------------------------------------------------------%
% It abstracts the non linear equation X = NonLinear where X is either a
% variable or a coefficient and NonLinear is a one of the simple non 
% linear functions. This is performed whenever we are not able to ensure
% (thanks to variables which are known to have a particular sign), if the
% non-linear equation is in fact a linear equation.
%     * X = min(Y,Z), max(Y,Z)                 -> X eq? Y, X eq?  Z
%     * X = abs(Y)                             -> X eq? Y, X eq? -Y
%     * X = sin(Y),cos(Y),arcsin(Y),arccos(Y)  -> t eqx X + Y
%     * X = pow(Y,Z),Y*Z                       -> t eqx X + Y + Z
% 
% Assumptions made:
%     X, Y and Z are variables.
%------------------------------------------------------------------------%

lsign_abstract_non_linear(min(Y,Z),X,AEqIn,Tail):- 
    lsign_abstract_equation(X,Y,Sign1,Expr1),
    Eq1 = eq('eq?',Sign1,Expr1),
    lsign_abstract_equation(X,Z,Sign2,Expr2),
    Eq2 = eq('eq?',Sign2,Expr2),
    AEqIn = [Eq1,Eq2|Tail].
lsign_abstract_non_linear(max(Y,Z),X,AEqIn,Tail):- 
    lsign_abstract_equation(X,Y,Sign1,Expr1),
    Eq1 = eq('eq?',Sign1,Expr1),
    lsign_abstract_equation(X,Z,Sign2,Expr2),
    Eq2 = eq('eq?',Sign2,Expr2),
    AEqIn = [Eq1,Eq2|Tail].
lsign_abstract_non_linear(abs(Y),X,AEqIn,Tail):- 
    lsign_abstract_equation(X,Y,Sign1,Expr1),
    Eq1 = eq('eq?',Sign1,Expr1),
    lsign_abstract_equation(X,-(Y),Sign2,Expr2),
    Eq2 = eq('eq?',Sign2,Expr2),
    AEqIn = [Eq1,Eq2|Tail].
lsign_abstract_non_linear(sin(Y),X,[eq(eqx,t,Expr)|Tail],Tail):-
    sort([X,Y],Vars),
    create_values(Vars,Expr,+).
lsign_abstract_non_linear(cos(Y),X,[eq(eqx,t,Expr)|Tail],Tail):-
    sort([X,Y],Vars),
    create_values(Vars,Expr,+).
lsign_abstract_non_linear(arcsin(Y),X,[eq(eqx,t,Expr)|Tail],Tail):-
    sort([X,Y],Vars),
    create_values(Vars,Expr,+).
lsign_abstract_non_linear(arccos(Y),X,[eq(eqx,t,Expr)|Tail],Tail):-
    sort([X,Y],Vars),
    create_values(Vars,Expr,+).
lsign_abstract_non_linear(pow(Y,Z),X,[eq(eqx,t,Expr)|Tail],Tail):-
    sort([X,Y,Z],Vars),
    create_values(Vars,Expr,+).
lsign_abstract_non_linear(Y*Z,X,[eq(eqx,t,Expr)|Tail],Tail):-
    sort([X,Y,Z],Vars),
    create_values(Vars,Expr,+).

%-------------------------------------------------------------------------
% lsign_abstract_positive(+,-,-)
% lsign_abstract_positive(Vars,AEqIn,Tail)
%-------------------------------------------------------------------------
% The following predicates abstract the information provided by a set of 
% variables which are known to be positive, negative, ground (although the 
% sign is not known) and bound to a possibly non-ground herbrand term,
% respectively. Used when abstracting builtins.
% 
% Assumptions made:
%   - none
%-------------------------------------------------------------------------

lsign_abstract_positive([],Tail,Tail).
lsign_abstract_positive([X|Pos],[eq(eq,'+',[X/'+'])|AEqIn],Tail):-
    lsign_abstract_positive(Pos,AEqIn,Tail).

lsign_abstract_negative([],Tail,Tail).
lsign_abstract_negative([X|Neg],[eq(eq,'+',[X/'-'])|AEqIn],Tail):-
    lsign_abstract_negative(Neg,AEqIn,Tail).

lsign_abstract_unsigned([],Tail,Tail).
lsign_abstract_unsigned([X|Ground],[eq(eq,t,[X/'+'])|AEqIn],Tail):-
    lsign_abstract_unsigned(Ground,AEqIn,Tail).

lsign_abstract_top([],Tail,Tail).
lsign_abstract_top([X|Top],[eq('eq?',t,[X/'+'])|AEqIn],Tail):-
    lsign_abstract_top(Top,AEqIn,Tail).

%-------------------------------------------------------------------------
% lsign_abstract_herbrand_eq(+,+,-,?)
% lsign_abstract_herbrand_eq(VarsTerm,X,AEqIn,Tail)
%-------------------------------------------------------------------------
% The following predicates abstract the information provided by the 
% herbrand equation X = Term, where X is a variable which is not known to
% be definite in the abstraction and VarsTerm are the variables in Term
% which are not known to be definite in the abstraction. It is done as 
% follows:
%  - If Term is ground (VarsTerm = []), eq(eq,t,[X/'+']) is added
%  - Otherwise, for each Y_i \in VarsTerm + {X}, eq(eq?,t,[Y_i/'+']) is added
%    together with eq(eq,t,[X/'+',Y_1/'+',....,Y_n/'+']).%
% 
% Assumptions made:
%    - none
%-------------------------------------------------------------------------

lsign_abstract_herbrand_eq([],X,AEqIn,Tail):- !,
    AEqIn = [eq(eq,t,[X/'+'])|Tail].
lsign_abstract_herbrand_eq(VarsY,X,AEqIn,Tail):-
    insert(VarsY,X,Vars),
    lsign_unknown_entry0(Vars,AEqIn,Tail).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Entry                            %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% lsign_call_to_entry(+,+,+,+,+,+,+,-,-)
% lsign_call_to_entry(Sv,Sg,Hv,Head,K,Fv,Proj,Entry,ExtraInfo) 
%------------------------------------------------------------------------%
% Assumptions made:
%   * the program is normalized
%   * Fv and Proj are sorted
%------------------------------------------------------------------------%

lsign_call_to_entry(_Sv,Sg,_Hv,Head,_K,Fv,Proj,Entry,ExtraInfo):-
    variant(Sg,Head),!,
    ExtraInfo = (yes,Fv),
    copy_term((Sg,Proj),(NewTerm,NewEntry)),
    Head = NewTerm,
    lsign_abs_sort(NewEntry,Entry).
lsign_call_to_entry(_Sv,Sg,_Hv,Head,_K,_,_,_,_):-
    compiler_error(not_normalized(Sg,Head)).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Exit To Prime
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% lsign_exit_to_prime(+,+,+,+,+,+,-)
% lsign_exit_to_prime(Sg,Hv,Head,Sv,Exit,ExtraInfo,Prime) 
%------------------------------------------------------------------------%
% Assumptions made:
%   * the program is normalized
%   * Hv and Exit and Fv within ExtraInfor are sorted
%------------------------------------------------------------------------%

lsign_exit_to_prime(_,_,_,_,'$bottom',_,Prime) :- !,
    Prime = '$bottom'.
lsign_exit_to_prime(Sg,Hv,Head,_Sv,Exit,(yes,Fv),Prime):- 
    lsign_project(Sg,Hv,Fv,Exit,BPrime),
    copy_term((Head,BPrime),(NewTerm,NewPrime)),
    Sg = NewTerm,
    lsign_abs_sort(NewPrime,Prime).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Call To Success Fact                     %
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% lsign_call_to_success_fact(+,+,+,+,+,+,+,-,-)
% lsign_call_to_success_fact(Sg,Hv,Head,K,Sv,Call,Proj,Prime,Succ) 
%------------------------------------------------------------------------%
% Assumptions made:
%   * the program is normalized
%------------------------------------------------------------------------%

lsign_call_to_success_fact(Sg,_Hv,Head,_K,_Sv,Call,Proj,Prime,Succ):-
    variant(Sg,Head),!,
    Prime = Proj,
    Succ = Call.
lsign_call_to_success_fact(Sg,_Hv,Head,_K,_Sv,_Call,_Proj,_Prime,_Succ):-
    compiler_error(not_normalized(Sg,Head)).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT SORT
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% lsign_abs_sort(+,-) 
% lsign_abs_sort(ACons_u,ACons)
%------------------------------------------------------------------------%

lsign_abs_sort('$bottom','$bottom').
lsign_abs_sort(a(S_u,AEqIn_u,Non_u),a(S,AEqIn,Non)):-
    sort(S_u,S),
    lsign_sort_each(AEqIn_u,TmpAEqIn),
    sort(Non_u,Non),
    sort(TmpAEqIn,AEqIn).

lsign_sort_each([],[]).
lsign_sort_each([eq(Op,Sign,Expr_u)|AEqIn_u],[eq(Op,Sign,Expr)|AEqIn]):-
    sort(Expr_u,Expr),
    lsign_sort_each(AEqIn_u,AEqIn).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT LUB
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% lsign_compute_lub(+,-)
% lsign_compute_lub(ListACons,Lub)
%------------------------------------------------------------------------%
% Assumptions made:
%    - Each abstraction in ListACons is sorted
%------------------------------------------------------------------------%

lsign_compute_lub([Xss,Yss|Rest],Lub) :- !,
    lsign_lub(Xss,Yss,Zss),
    lsign_compute_lub([Zss|Rest],Lub).
lsign_compute_lub([X],X).

lsign_lub('$bottom',Yss,Zss):- !,
    Zss = Yss.
lsign_lub(Xss,'$bottom',Zss):- !,
    Zss = Xss.
lsign_lub(Xss,Yss,Zss) :-
    Xss == Yss,!,
    Zss = Xss.
lsign_lub(a(S1,AEqIn1,Non1),a(S2,AEqIn2,Non2),a(S,AEqIn,Non)):-
    lsign_ord_intersection(S1,S2,S),
    lsign_lub0(AEqIn1,AEqIn2,AEqIn3),
    sort(AEqIn3,AEqIn),
    lsign_lub0(Non1,Non2,Non3),
    sort(Non3,Non).

%------------------------------------------------------------------------%
% lsign_lub0(+,+,-)
% lsign_lub0(AEqIn1,AEqIn2,Lub)
%------------------------------------------------------------------------%
% Lub is recursively computed as follows:
%  1/ if AEqIn1=[], AEqIn is computed by lsign_lub_nil(AEqIn2,AEqIn,[]).
%  2/ if AEqIn2=[], AEqIn is computed by lsign_lub_nil(AEqIn1,AEqIn,[]).
%  3/ Otherwise, for each element EqIn = eq(Op,Sign,Expr) in AEqIn1 we 
%     look for an element EqIn2 in AEqIn2 such that EqIn2=eq(Op2,Sign,Expr)
%      (a) If such an element exists:
%           * the element eq(NOp,Sign,Expr) is added to AEqIn (where NOp
%             is computed by lub_unique(Op,Op2,NOp))
%           * Disjunct = AEqIn2 \ {EqIn2}
%      (b) If such EqIn2 does not exists:
%           * the element eq(NOp,Sign,Expr) is added to AEqIn (where NOp
%             is computed by lub_unique(Op,NOp))
%           * Disjunct = AEqIn2
%
% Assumptions made:
%    - AEqIn1 and AEqIn2 are sorted
%------------------------------------------------------------------------%

lsign_lub0(AEqIn1,[],AEqIn):-  !,
    lsign_lub_nil(AEqIn1,AEqIn,[]).
lsign_lub0([],AEqIn2,AEqIn):-  !,
    lsign_lub_nil(AEqIn2,AEqIn,[]).
lsign_lub0([eq(Op,Sign,Expr)|AEqIn1],AEqIn2,[eq(NOp,Sign,Expr)|AEqIn]):- 
    split_identical_expr(AEqIn2,Sign,Expr,Op2,Disjunct),
    ( Op2 = no ->
        lub_unique(Op,NOp)
    ;   cross_op(Op,Op2,NOp)
    ),
    lsign_lub0(AEqIn1,Disjunct,AEqIn).

%------------------------------------------------------------------------%
% lsign_lub_nil(+,-,?)
% lsign_lub_nil(AEqIn,Lub,Tail)
%------------------------------------------------------------------------%
% Lub is an open-ended list (ended by the variable Tail) whose elements 
% are {eq(NOp,Sign,Expr)|eq(Op,Sign,Expr) \in AEqIn2, lub_unique(Op,NOp)}
%------------------------------------------------------------------------%

lsign_lub_nil([],X,X).
lsign_lub_nil([eq(Op,Sign,AExpr)|AEqIn1],[eq(NOp,Sign,AExpr)|AEqIn],Tail):-
    lub_unique(Op,NOp),
    lsign_lub_nil(AEqIn1,AEqIn,Tail).

lub_unique(eq,'eq?').
lub_unique('eq?','eq?').
lub_unique('eq+',eqx).
lub_unique(eqx,eqx).
lub_unique(leq,leq).
lub_unique(less,less).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT Extend
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
% lsign_extend(+,+,+,+,-)
% lsign_extend(Sg,Prime,Sv,Call,Succ)
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

lsign_extend(_Sg,'$bottom',_Sv,_Call,Succ):- !,
    Succ = '$bottom'.
lsign_extend(_Sg,Prime,_Sv,Call,Succ):-
    lsign_sum(Prime,Call,Succ).

%------------------------------------------------------------------------%
% lsign_sum(+,+,-)
% lsign_sum(ACons1,ACons2,ACons).
%------------------------------------------------------------------------%
% Abstractly conjuncts ACons1 and ACons2 (satisfying the assumptions) as 
% follows. Let ACons1 = a(S1,AEqIn1,Non1), ACons2 = a(S2,AEqIn2,Non2)
%   (1) We first propagate the new definite sign information (Diff) in S1
%       to ACons2, obtaining S (the final definite sign info), NAEqIn2
%       and NNon2.
%   (2) If inconsistency is not found (F = incons), we then conjunct
%       AEqIn1 with NAEqIn2, and Non1 with NNon2.
%   (3) Otherwise ACons = '$bottom'
%       
% Assumptions made:
%   - ACons1 is more constrained (or equal) than ACons 2.
%   - ACons1 and ACons 2 are sorted
%------------------------------------------------------------------------%

:- export(lsign_sum/3).
lsign_sum(a(S1,AEqIn1,Non1),a(S2,AEqIn2,Non2),ACons):-
    ord_union_diff(S2,S1,Union,Diff),
    lsign_propagate_fixpoint(Diff,AEqIn2,Non2,NAEqIn2,NNon2,Union,S,F),
    ( F = cons ->
        lsign_sum0(AEqIn1,NAEqIn2,AEqIn0),
        sort(AEqIn0,AEqIn),
        lsign_sum0(Non1,NNon2,Non0),
        sort(Non0,Non),
        ACons = a(S,AEqIn,Non)
    ; ACons = '$bottom'
    ).

%------------------------------------------------------------------------%
% lsign_sum0(+,+,-)
% lsign_sum0(AEqIn1,AEqIn2,AEqIn)
%------------------------------------------------------------------------%
% This predicate performs the abstract conjunction of AEqIn1 and AEqIn2
% obtaining AEqIn. This is recursively performed as follows:
%  1/  If AEqIn1 = [], AEqIn = AEqIn2.
%  2/  If AEqIn2 = [], AEqIn = AEqIn1.
%  3/  Otherwise, for each EqIn = eq(Op,Sign,Expr) in AEqIn1 we look
%      for an element EqIn2 in AEqIn2 such that EqIn2 = eq(Op2,Sign,Expr)
%      (a) If such an element exists:
%           * the element eq(NOp,Sign,Expr) is added to AEqIn (where NOp
%             is computed by lsign_sum_op(Op,Op2,NOp))
%           * Disjunct = AEqIn2 \ {EqIn2}
%      (b) If such EqIn2 does not exists:
%           * EqIn is added to AEqIn
%           * Disjunct = AEqIn2
%------------------------------------------------------------------------%

lsign_sum0([],ACons2,ACons):- !,
    ACons = ACons2.
lsign_sum0(ACons1,[],ACons):- !,
    ACons = ACons1.
lsign_sum0([eq(Op,Sign,Expr)|ACons1],ACons2,ACons):-
    split_identical_expr(ACons2,Sign,Expr,Op2,Disjunct),
    ( Op2 = no ->
        NewOp = Op
    ; lsign_sum_op(Op,Op2,NewOp)
    ),
    ACons = [eq(NewOp,Sign,Expr)|RestACons],
    lsign_sum0(ACons1,Disjunct,RestACons).

%------------------------------------------------------------------------%
% lsign_sum_op(+,+,-)
% lsign_sum_op(Op1,Op2,Op)
%------------------------------------------------------------------------%
% Computes Op from Op1 and Op2 as follows
%
%              | eq  eq+  eq?  eqx  leq  less
%         -----------------------------------
%          eq  | eq+ eq+  eq+  eq+  eq+  eq+
%          eq+ | eq+ eq+  eq+  eq+  eq+  eq+
%          eq? | eq+ eq+  eqx  eqx  eqx  eqx
%          eqx | eq+ eq+  eqx  eqx  eqx  eqx
%          leq | eq+ eq+  eqx  eqx  leq  less
%          less| eq+ eq+  eqx  eqx  less less
%------------------------------------------------------------------------%

lsign_sum_op(eq,_,'eq+').
lsign_sum_op('eq+',_,'eq+').
lsign_sum_op('eq?',Op2,Op):-
    lsign_sum_op_question_star(Op2,Op).
lsign_sum_op(eqx,Op2,Op):-
    lsign_sum_op_question_star(Op2,Op).
lsign_sum_op(leq,Op2,Op):-
    lsign_sum_op_leq(Op2,Op).
lsign_sum_op(less,Op2,Op):-
    lsign_sum_op_less(Op2,Op).

lsign_sum_op_question_star(eq,'eq+').
lsign_sum_op_question_star('eq+','eq+').
lsign_sum_op_question_star('eq?',eqx).
lsign_sum_op_question_star(eqx,eqx).
lsign_sum_op_question_star(leq,eqx).
lsign_sum_op_question_star(less,eqx).

lsign_sum_op_leq(eq,'eq+').
lsign_sum_op_leq('eq+','eq+').
lsign_sum_op_leq('eq?',eqx).
lsign_sum_op_leq(eqx,eqx).
lsign_sum_op_leq(leq,leq).
lsign_sum_op_leq(less,less).

lsign_sum_op_less(eq,'eq+').
lsign_sum_op_less('eq+','eq+').
lsign_sum_op_less('eq?',eqx).
lsign_sum_op_less(eqx,eqx).
lsign_sum_op_less(leq,less).
lsign_sum_op_less(less,less).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                      ABSTRACT PROJECTION
%------------------------------------------------------------------------%
% lsign_project(+,+,+,+,-) 
% lsign_project(Sg,Vars,HvFv_u,ACons,Proj)
%------------------------------------------------------------------------%
% This predicate projects the abstract constraint ACons onto the 
% variables in the sorted list Vars, obtaining Proj, as follows. If Vars
% is empty, the abstraction is empty (we do not check for consistency 
% here because is too expensive). Otherwise,  we compute the set of 
% variables which have to be projected out (OutVars).  If OutVars=[] we 
% have finished, and Proj = ACons. Otherwise, let ACons=a(S,AEqIn,Non):
%   (1) Project S over Vars.
%   (2) Abtract any equation Eq in Non s.t. vars(Eq) \not subset of Vars, 
%       obtaining NAEqIn. The rest remain in Non0.
%   (3) Add NAEqIn to AEqIn obtaining TmpAEqIn.
%   (4) Project out OutVars from TmpAEqIn, obtaining AEqIn0
%   (5) If AEqIn0 = '$bottom', Proj = '$bottom'
%   (6) Otherwise, we collect all sign information (Union) from AEqIn0, 
%       and eliminate what we already knew (PS) obtaining Diff (the new
%       sign information).
%   (7) We propagate this to AEqIn0 and Non0.
% Assumptions:
%   - Vars and ACons are sorted
%------------------------------------------------------------------------%

lsign_project(_Sg,_,_,'$bottom',Proj):- !,
    Proj = '$bottom'.
lsign_project(_Sg,[],_,_,Proj):- !,
    Proj = a([],[],[]).
lsign_project(_Sg,Vars,HvFv_u,ACons,Proj):-
    sort(HvFv_u,HvFv),
    ord_subtract(HvFv,Vars,OutVars),
    lsign_project_(OutVars,Vars,ACons,Proj).

lsign_project_([],_,ACons,Proj):- !,
    Proj = ACons.
lsign_project_(OutVars,Vars,a(S,AEqIn,Non),Proj):-
    lsign_project_signed(Vars,S,PS),
    lsign_project_non(Non,Vars,Non0,NAEqIn),
    lsign_sum0(NAEqIn,AEqIn,TmpAEqIn),
    lsign_project0(OutVars,TmpAEqIn,AEqIn0),
    ( AEqIn0 = '$bottom' ->
        Proj = '$bottom'
    ; get_signed(AEqIn0,PS,Union,F),
      ord_subtract(Union,PS,Diff),
      lsign_propagate_fixpoint(Diff,AEqIn0,Non0,AEqIn1,Non1,Union,S1,F),
      ( F = cons -> 
          Proj = a(S1,AEqIn1,Non1)
      ; Proj = '$bottom'
      )
    ).

%------------------------------------------------------------------------%
% lsign_project_non(+,+,-,-)
% lsign_project_non(Non,Vars,NNon,NEqIn)
%------------------------------------------------------------------------%
% Vars is a nonempty set of variables. Non is a set of non-linear 
% equations. NNon will contain any Eq in Non such that vars(Eq) is a 
% subset of Vars. The rest are abstracted and left in NEqIn.
%------------------------------------------------------------------------%

lsign_project_non([],_,[],[]).
lsign_project_non([Eq|Non],Vars,Non1,NewAEqIn):-
    Eq = eq(_,X,Y),
    varset(p(X,Y),V),
    ( ord_subset(V,Vars) ->
        Non1 = [Eq|Tail1],
        NewAEqIn = Tail2
    ;   Non1 = Tail1,
        lsign_abstract_non_linear(Y,X,NewAEqIn,Tail2)
    ),
    lsign_project_non(Non,Vars,Tail1,Tail2).

%------------------------------------------------------------------------%
% lsign_project0(+,+,-)
% lsign_project0(OutVars,AEqIn,Proj)
%------------------------------------------------------------------------%
% Note that if an element of the form eq(Op,Sign,[]) is obtained during
% projection, it is never added to the result projected constraint, and
% Proj = '$bottom' if it is definitely inconsistency.
%------------------------------------------------------------------------%

lsign_project0([],AEqIn,Proj):- !,
    Proj = AEqIn.
lsign_project0(OutVars,AEqIn,Proj):-
    lsign_project00(OutVars,AEqIn,Proj0,Subset),
    ( Proj0 = '$bottom' ->
            Proj = '$bottom'
    ; sort(Proj0,Proj00),
      lsign_sum0(Subset,Proj00,Proj1),
      sort(Proj1,Proj)
    ).

lsign_project00(OutVars,AEqIn,Proj,Subset):-
    lsign_get_data(AEqIn,OutVars,[],Data,AEqIn0,Subset),
    lsign_get_unique_vars(Data,Unique),
    lsign_fixpoint_unique(Unique,OutVars,Data,AEqIn0,Vars1,Data1,AEqIn1),
    lsign_get_best_var(Data1,[],EqorEqplus),
    ( EqorEqplus = [] ->
        afourier_step(Vars1,AEqIn1,Proj)
    ; EqorEqplus = X/_,
      look_for_eq_or_eqplus(AEqIn1,X,SignX,Eq,AEqIn3),
      agauss_step(Eq,X,SignX,AEqIn3,AEqIn4),
      ( AEqIn4 = '$bottom' ->
          Proj = '$bottom'
      ;  ord_subtract(Vars1,[X],RestVars),
         lsign_project0(RestVars,AEqIn4,Proj)
      )
    ).

%------------------------------------------------------------------------%
% afourier_step(+,+,-)
% afourier_step(Vars,AEqIn,Proj)
%------------------------------------------------------------------------%
% Projects out the variables in Vars from AEqIn, resulting in Proj, 
% following the fourier elimination, as follows:
%  * If Vars=[], Proj = AEqIn.
%  * Otherwise, for each X in Vars:
%      1/ splits AEqIn into C0, Ct+, Ct-, the elements in which X has 
%         sign 0, t or +, and t or -, respectively.
%      2/ If Ct+ or Ct- = [], NewAEqIn = C0.
%      3/ Otherwise, for each eq(Op1,Sign1,Expr1) in Ct+ and each 
%         eq(Op2,Sign2,Expr2) in Ct-, it combines the two expressions
%         into eq(Op,Sign,Expr), normalizes it obtaining EqIn, and 
%         joins it with C0.
% Assmptions:
%   - AEqIn is sorted
%------------------------------------------------------------------------%

afourier_step([],AEqIn,AEqIn).
afourier_step([X|Vars],AEqIn,Proj):-
    split_sign(AEqIn,X,C0,Ctplus,Ctminus,_),
    afourier(Ctplus,Ctminus,C0,X,NAEqIn_u),
    ( NAEqIn_u = '$bottom' ->
        Proj = '$bottom'
    ; sort(NAEqIn_u,NAEqIn),
      afourier_step(Vars,NAEqIn,Proj)
    ).

afourier(_,_,'$bottom',_,NewD):- !,
    NewD = '$bottom'.
afourier([],_,D,_,NewD):- !,
    NewD = D.
afourier(_,[],D,_,NewD):- !,
    NewD = D.
afourier([EqIn|Ctplus],Ctminus,D,X,NewD):-
    acombine(Ctminus,EqIn,X,D,TmpD),
    afourier(Ctplus,Ctminus,TmpD,X,NewD).

%------------------------------------------------------------------------%
% agauss_step(+,+,+,+,-)
% agauss_step(Eq,X,SignX,ACons0,Proj)
%------------------------------------------------------------------------%
% Projects out the variable X from ACons (which is ACons0 \cup {Eq}), 
% resulting in Proj, following the gaussian elimination and using the 
% equation Eq = eq(Op,Sign,Expr). We know that Op in {eq,eq+} and that 
% SignX is the sign of X in Expr. This is performed as follows:
%   1/ If Op=eq, ACons1=ACons0  otherwise = ACons0 \cup eq(eqx,Sign,Expr)
%   2/ Eq+=Eq  and Eq-=negated(Eq) if SignX='-', and vice versa otherwise.
%   3/ Then we split ACons1 into C0, Ct+, Ct-, and Ct, as before.
%   4/ We combine Eq- with each element of Ct+, combining the result tp C0.
%   5/ We combine Eq+ with each element of Ct-, combining the result tp C0.
%   6/ For each EqIn in Ct, we weaken the operator, eliminate X/Si 
%      from the expression, normalise the resulting equation and COMBINE
%      the result with CO.
% Assmptions:
%   - ACons0 is sorted
%------------------------------------------------------------------------%

agauss_step(Eq,X,SignX,ACons0,NewD):-
    Eq = eq(Op,Sign,Expr),
    ( Op = eq ->
        ACons1 = ACons0
    ;   insert(ACons0,eq(eqx,Sign,Expr),ACons1)
    ),
    ( SignX = '-' ->
         anegate(Eq,Eqplus),
         Eqminus = Eq
    ;  Eqplus = Eq,
       anegate(Eq,Eqminus)
    ),
    split_sign(ACons1,X,C0,Ctplus,Ctminus,Ct),
    acombine(Ctplus,Eqminus,X,C0,D),
    acombine(Ctminus,Eqplus,X,D,TmpD),
    agauss_each_top(Ct,X,TmpD,NewD).

agauss_each_top(_,_,'$bottom',D):- !,
    D = '$bottom'.
agauss_each_top([],_,D,D):- !.
agauss_each_top([eq(Op,Sign,Expr)|Ct],X,D,NewD):-
    ( Op = eq ->
        NewOp = 'eq?'
    ; ( Op = 'eq+' -> 
          NewOp = eqx
      ;  NewOp = Op
      )
    ),
    acombine_expr(Expr,[X/'-'],X,NewExpr,_),
    lsign_normalize(NewOp,Sign,NewExpr,EqIn),
    lsign_sum_el(EqIn,D,TmpD),
    agauss_each_top(Ct,X,TmpD,NewD).

%------------------------------------------------------------------------%
% lsign_sum_el(+,+,-)
% lsign_sum_el(eq(Op,Sign,Expr),ACons1,ACons)
%------------------------------------------------------------------------%
% It adds EqIn=eq(Op,Sign,Expr) (which has been obtained during projection)
% to ACons resulting in ACons, as follows:
%   - If Expr = [] (i.e, it is 0) then:
%        * if the equations is definitely inconsistent, ACons = '$bottom'
%        * Otherwise EqIn is not added, thus ACons = ACons1.
%   - Else:
%        - if there exists an element EqIn1=eq(Op2,Sign,Expr) in ACons1 
%          the NewOp is computed and the result inserted in Disjunct = 
%          ACons1\EqIn1
%        - Otherwise Op2=no, Disjunct = ACons1, and EqIn is inserted in
%          ACons1
% Assumptions:
%   - ACons1 is ordered
%------------------------------------------------------------------------%

lsign_sum_el(eq(Op,Sign,[]),ACons1,ACons):- !,
    ( lsign_consistent(Op,Sign,0) ->
        ACons = ACons1
    ; ACons = '$bottom'
    ).
lsign_sum_el(eq(Op,Sign,Expr),ACons1,ACons):-
    split_identical_expr(ACons1,Sign,Expr,Op2,Disjunct),
    ( Op2 = no ->
        NewOp = Op
    ;   lsign_sum_op(Op,Op2,NewOp)
    ),
    insert(Disjunct,eq(NewOp,Sign,Expr),ACons).

%------------------------------------------------------------------------%
% acombine(+,+,+,+,-)
% acombine(ACons,EqIn,X,D,NewD)
%------------------------------------------------------------------------%
% EqIn is an equation or inequation in which the variable X appears. ACons
% is an abstract constraint containing equations or inequations in which X 
% also appears. This predicate combines EqIn1=eq(Op1,Sign1,Expr1) with each 
% EqIn2=eq(Op2,Sign2,Expr2) obtaining EqIn=eq(Op,Sign,Expr). EqIn is then
% joined with D, obtaining NewD.
% Assumptions:
%   - none
%------------------------------------------------------------------------%

acombine(_,_,_,'$bottom',D):- !,
    D = '$bottom'.
acombine([],_,_,D,D):- !.
acombine([eq(Op2,Sign2,Expr2)|Ctminus],EqIn1,X,D,NewD):-
    EqIn1 = eq(Op1,Sign1,Expr1),
    cross_op(Op1,Op2,TmpOp),
    cross_sign(Sign1,Sign2,Sign),
    acombine_expr(Expr1,Expr2,X,Expr,(SignX1,SignX2)),
    ( (SignX1=t;SignX2=t) ->
        ( TmpOp = eq ->
            Op = 'eq?'
        ; ( TmpOp = 'eq+' ->
            Op = eqx
          ; Op = TmpOp
          )
        )
    ; Op = TmpOp
    ),
    lsign_normalize(Op,Sign,Expr,EqIn),
    lsign_sum_el(EqIn,D,TmpD),
    acombine(Ctminus,EqIn1,X,TmpD,NewD).

%------------------------------------------------------------------------%
% cross_op(+,+,-)
% cross_op(X,Y,Cross)
%------------------------------------------------------------------------%
% Obtains Cross from the following table:
%
%              | eq   eq+  eq?  eqx  leq  less
%         ------------------------------------
%          eq  | eq   eq+  eq?  eqx  leq  less
%          eq+ | eq+  eq+  eqx  eqx  leq  less
%          eq? | eq?  eqx  eq?  eqx  leq  less
%          eqx | eqx  eqx  eqx  eqx  leq  less
%          leq | leq  leq  leq  leq  leq  less
%          less| less less less less less less
% 
%------------------------------------------------------------------------%

cross_op(eq,Y,Y).
cross_op('eq+',Y,Cross):-
    cross_op_plus(Y,Cross).
cross_op('eq?',Y,Cross):- 
    cross_op_question(Y,Cross).
cross_op(eqx,Y,Cross):-
    cross_op_star(Y,Cross).
cross_op(leq,Y,Cross):- 
    cross_op_leq(Y,Cross).
cross_op(less,_,less).

cross_op_plus(eq,'eq+').
cross_op_plus('eq+','eq+').
cross_op_plus('eq?',eqx).
cross_op_plus(eqx,eqx).
cross_op_plus(leq,leq).
cross_op_plus(less,less).

cross_op_question(eq,'eq?').
cross_op_question('eq+',eqx).
cross_op_question('eq?','eq?').
cross_op_question(eqx,eqx).
cross_op_question(leq,leq).
cross_op_question(less,less).

cross_op_star(eq,eqx).
cross_op_star('eq+',eqx).
cross_op_star('eq?',eqx).
cross_op_star(eqx,eqx).
cross_op_star(leq,leq).
cross_op_star(less,less).

cross_op_leq(eq,leq).
cross_op_leq('eq+',leq).
cross_op_leq('eq?',leq).
cross_op_leq(eqx,leq).
cross_op_leq(leq,leq).
cross_op_leq(less,less).

%------------------------------------------------------------------------%
% cross_sign(+,+,-)
% cross_sign(X,Y,Cross)
%------------------------------------------------------------------------%
% Obtains Cross from the following table:
%                   |  0   +   -   t   
%              ----------------------
%                 0 |  0   +   -   t
%                 + |  +   +   t   t
%                 - |  -   t   -   t
%                 t |  t   t   t   t
%------------------------------------------------------------------------%


cross_sign(0,Y,Y).
cross_sign(t,_,t).
cross_sign(+,Y,Cross):- 
    cross_sign_plus(Y,Cross).
cross_sign(-,Y,Cross):- 
    cross_sign_minus(Y,Cross).

cross_sign_plus(0,+).
cross_sign_plus(+,+).
cross_sign_plus(-,t).
cross_sign_plus(t,t).

cross_sign_minus(0,-).
cross_sign_minus(+,t).
cross_sign_minus(-,-).
cross_sign_minus(t,t).

%------------------------------------------------------------------------%
% acombine_expr(+,+,+,-,-)
% acombine_expr(Expr1,Expr2,Var,Expr,(Sign1,Sign2))
%------------------------------------------------------------------------%
% Combines the expressions Expr1 and Expr2 w.r.t. Var into Expr, and 
% returns in Sign1, Sign2, the signs of Var in Expr1, and Expr2, 
% respectively (Note that then Var must appear in both Expr1 and Expr2).
% Let Expr1 = [X1/S1,X2/S2,...,Xn/Sn] and Expr2 = [Y1/R1,Y2/R2,...,Yn/Rn]
% Then Expr = 
%  {Xi/Si \in Expr1|Xi/Ri not in Expr2} \cup
%  {Yi/Ri \in Expr2|Xi/Si not in Expr1} \cup
%  {Xi/Ti|Xi/Si in Expr1,Yi/Ri in Expr2,Xi=Yi,Xi\== Var,cross_sign(Si,Ri,Ti)}
% Assumptions:
%   - Expr1 and Epr2 are sorted
%------------------------------------------------------------------------%

:- push_prolog_flag(multi_arity_warnings,off).

acombine_expr(Expr1,[],_,Expr1,_) :- !.
acombine_expr([],Expr2,_,Expr2,_):- !.
acombine_expr([X/SignX|Tail1],[Y/SignY|Tail2],Var,Union,Signs) :-
    compare(Order,X,Y),
    acombine_expr(Order,X/SignX,Tail1,Y,SignY,Tail2,Var,Union,Signs).

acombine_expr(<,X,[],Y,SignY,Tail2,_,[X,Y/SignY|Tail2],_) :- !.
acombine_expr(<,X0,[X/SignX|Tail1],Y,SignY,Tail2,Var,[X0|Union],Signs) :-
    compare(Order,X,Y),
    acombine_expr(Order,X/SignX,Tail1,Y,SignY,Tail2,Var,Union,Signs).
acombine_expr(=,_/SignX,Tail1,Y,SignY,Tail2,Var,Union,(SignX,SignY)) :-
    Y == Var,!,
    acombine_expr(Tail1,Tail2,a,Union,_).
acombine_expr(=,_/SignX,Tail1,Y,SignY,Tail2,Var,[Y/Sign|Union],Signs) :-
    cross_sign(SignX,SignY,Sign),
    acombine_expr(Tail1,Tail2,Var,Union,Signs).
acombine_expr(>,X,Tail1,Y,SignY,[],_,[Y/SignY,X|Tail1],_) :- !.
acombine_expr(>,X/SignX,Tail1,Y0,SignY0,[Y/SignY|Tail2],Var,[Y0/SignY0|Union],Signs) :-
    compare(Order,X,Y),
    acombine_expr(Order,X/SignX,Tail1,Y,SignY,Tail2,Var,Union,Signs).

:- pop_prolog_flag(multi_arity_warnings).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                     OTHER ABSTRACT FUNCTIONS
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% lsign_unknown_call(+,+,+,-) 
% lsign_unknown_call(Sg,Vars,Call,Succ) 
%------------------------------------------------------------------------%

lsign_unknown_call(_Sg,Vars,Call,Succ):-
    lsign_unknown_entry0(Vars,AEqIn,[]),
    Call = a(S,_,_),
    lsign_propagate_fixpoint(S,AEqIn,[],TmpEqIn,_,S,_,F),
    ( F = cons ->
        get_signed(TmpEqIn,[],NewS,_),
        lsign_sum(a(NewS,TmpEqIn,[]),Call,Succ)
    ; Succ = '$bottom'
    ).

%------------------------------------------------------------------------%
% lsign_unknown_entry(+,+,-) 
% lsign_unknown_entry(Sg,Qv,Call) 
%------------------------------------------------------------------------%

lsign_unknown_entry(_Sg,Vars,a([],AEqIn,[])):-
    lsign_unknown_entry0(Vars,AEqIn,[]).

lsign_unknown_entry0([],X,X):- !.
lsign_unknown_entry0(Vars,[Eq|AEqIn],Tail):-
    create_values(Vars,Expr,'+'),
    Eq=eq(eq,t,Expr),
    lsign_abstract_top(Vars,AEqIn,Tail).

lsign_empty_entry(_Sg,_Qv,_Call):-
    throw(not_implemented(lsign_empty_entry)).

%------------------------------------------------------------------------%
% lsign_output_interface(+,-) 
% lsign_output_interface(ACons,ACons_user) 
% New assumptions:
%    - none
%------------------------------------------------------------------------%

lsign_asub_to_native(ASub,_Qv,_OutFlag,OutputUser,[]) :- lsign_output_interface(ASub,OutputUser).

% fail: lsign_output_interface('$bottom',[solutions(0)]).
:- export(lsign_output_interface/2).
lsign_output_interface(a(S,AEqIn,Non),Info):-
    lsign_output_user_interface0(AEqIn,NAEqIn),
    if_not_nil(S,a(S),Info,Info0),
    if_not_nil(Non,non(S),Info0,NAEqIn).

lsign_output_user_interface0([],[]).
lsign_output_user_interface0([eq(Op,X,Y)|ACons],[EqIn|AConsOut]):-
    reverse(Y,NY0),
    lsign_build_expr(NY0,NY),
    functor(EqIn,Op,2),
    arg(1,EqIn,X),
    arg(2,EqIn,NY),
    lsign_output_user_interface0(ACons,AConsOut).

lsign_build_expr([],0).
lsign_build_expr([X],NExpr):- !,
    lsign_build_elem(X,last,NExpr,_).
lsign_build_expr([X|Expr],NExpr):-
    lsign_build_elem(X,no,NExpr,Tail),
    lsign_build_expr(Expr,Tail).

lsign_build_elem(X/'+',Last,Rhs,Tail):-
    ( Last = last ->
        Rhs = X
    ;   Rhs = Tail + X
    ).
lsign_build_elem(X/'-',Last,Rhs,Tail):-
    ( Last = last ->
        Rhs = - X
    ;   Rhs = Tail - X
    ).
lsign_build_elem(X/t,Last,Rhs,Tail):-
    ( Last = last ->
        Rhs = t*X
    ;   Rhs = Tail + t*X
    ).

%------------------------------------------------------------------------%
% lsign_input_user_interface(+,+,-,+,+) 
% lsign_input_user_interface(InputUser,Qv,ACons,Sg,MaybeCallASub) 
%------------------------------------------------------------------------%
% Identical to the original but for the addition of a new component
% New assumptions:
%    - There is no information about non linear equations
%------------------------------------------------------------------------%

lsign_input_user_interface((Pv,Nv,Gv),Qv,a(S,AEqIn,[]),_Sg,_MaybeCallASub):-
    may_be_var(Pv),
    may_be_var(Nv),
    may_be_var(Gv),
    lsign_abstract_positive(Pv,AEqIn_u,Tail),
    lsign_abstract_negative(Nv,Tail,Tail1),
    merge(Nv,Pv,Signedv),
    ord_subtract(Gv,Signedv,Unsignedv),     
    lsign_abstract_unsigned(Unsignedv,Tail1,Tail2),
    ord_subtract(Qv,Gv,NonGroundv),
    ord_subtract(NonGroundv,Signedv,NonGroundHerbrandv),
    lsign_abstract_top(NonGroundHerbrandv,Tail2,[]),
    create_values(Pv,Tmp1,'+'),
    change_values_insert(Nv,Tmp1,Tmp2,'-'),
    change_values_insert(Unsignedv,Tmp2,S,t),
    sort(AEqIn_u,AEqIn).

lsign_input_interface(positive(X),perfect,(P0,N,G),(P,N,G)):-
    var(X),
    myinsert(P0,X,P).
lsign_input_interface(negative(X),perfect,(P,N0,G),(P,N,G)):-
    var(X),
    myinsert(N0,X,N).
lsign_input_interface(ground(X),perfect,(P,N,G0),(P,N,G)):-
    varset(X,Xs),
    myappend(G0,Xs,G).

myinsert(Vs0,V,Vs):-
    var(Vs0), !,
    Vs=[V].
myinsert(Vs0,V,Vs):-
    insert(Vs0,V,Vs).

myappend(Vs,V0,V):-
    var(Vs), !,
    V=V0.
myappend(Vs,V0,V):-
    merge(Vs,V0,V).

may_be_var(X):- ( X=[] ; true ), !.

%------------------------------------------------------------------------%
% lsign_less_or_equal(+,+) 
% lsign_less_or_equal(ACons0,ACons1) 
%------------------------------------------------------------------------%

lsign_less_or_equal(_ACons0,_ACons1):-
    throw(not_implemented(lsign_less_or_equal)).

lsign_abs_subset(_LASub1,_LASub2):-
    throw(not_implemented(lsign_abs_subset)).

lsign_eliminate_equivalent(LSucc0,LSucc):- !, sort(LSucc0,LSucc).
lsign_eliminate_equivalent(_LSucc0,_LSucc):-
    throw(not_implemented(lsign_eliminate_equivalent)).

%------------------------------------------------------------------------%

lsign_glb(_ASub0,_ASub1,_ASub) :- compiler_error(op_not_implemented(glb)), fail.

%------------------------------------------------------------------------%
% lsign_special_builtin(+,+,+,-,-) 
% lsign_special_builtin(SgKey,Sg,Subgoal,Type,Condvars) 
%------------------------------------------------------------------------%
% It divides builtins into groups determined by the flag returned in the |
% second argument + some special handling for some builtins:             |
%                                                                        |
% (1) bottom if the builtin always causes the execution to fail          |
% (2) herbrand if the builtin makes all variables ground and they are    |
%     known to be herbrand                                               |
% (3) old_herbrand if the builtin requires all variables to be ground    |
%     they are known to be herbrand                                      |
% (4) unchanged if the buitlin does not change the value of its arguments|
%     and we we cannot infer anything from them                          |
% (5) positive if the builtin makes all variables positive               |
% (6) unsigned if the builtin makes all variables ground but their sign  |
%     is not known                                                       |
% (7) old_unsigned if the builtin requires all variables to be ground    |
%     but their sign is not known                                        |
% (8) some_old_herbrand if the builtin requires some variables to be     |
%     ground and they are known to be herbrand                           |
% (9) some_herbrand if the builtin makes some variables ground and they  |
%     are known to be herbrand                                           |
%(10) positive_old_herbrand if the builtin makes some variables positive |
%     and some others are required to be ground herbrand                 |
%(11) positive_herbrand if the builtin makes some variables positive and |
%     some others become ground herbrand                                 |
% (6) Sgkey, special handling of some particular builtins                |
%------------------------------------------------------------------------%

%-------------------------------------------------------------------------
lsign_special_builtin('abort/0',_,_,bottom,_).
lsign_special_builtin('fail/0',_,_,bottom,_).
lsign_special_builtin('false/0',_,_,bottom,_).
lsign_special_builtin('halt/0',_,_,bottom,_).
%-------------------------------------------------------------------------
lsign_special_builtin('CHOICE IDIOM/1',_,_,herbrand,_).
lsign_special_builtin('$metachoice/1',_,_,herbrand,_).
lsign_special_builtin('current_atom/1',_,_,herbrand,_).
lsign_special_builtin('current_input/1',_,_,herbrand,_).
lsign_special_builtin('current_module/1',_,_,herbrand,_).
lsign_special_builtin('current_output/1',_,_,herbrand,_).
lsign_special_builtin('current_op/3',_,_,herbrand,_).
lsign_special_builtin('prolog_flag/2',_,_,herbrand,_).
lsign_special_builtin('prolog_flag/3',_,_,herbrand,_).
lsign_special_builtin('seeing/1',_,_,herbrand,_).
lsign_special_builtin('telling/1',_,_,herbrand,_).
lsign_special_builtin(':/2',(prolog:'$metachoice'(_)),_,herbrand,_).
%-------------------------------------------------------------------------
lsign_special_builtin('atom/1',_,_,old_herbrand,_).
lsign_special_builtin('close/1',_,_,old_herbrand,_).
lsign_special_builtin('CUT IDIOM/1',_,_,old_herbrand,_).
lsign_special_builtin('ensure_loaded/1',_,_,old_herbrand,_).
lsign_special_builtin('erase/1',_,_,old_herbrand,_).
lsign_special_builtin('flush_output/1',_,_,old_herbrand,_).
lsign_special_builtin('$metacut/1',_,_,old_herbrand,_).
lsign_special_builtin('nl/1',_,_,old_herbrand,_).
lsign_special_builtin('op/3',_,_,old_herbrand,_).
lsign_special_builtin('save_event_trace/1',_,_,old_herbrand,_).
lsign_special_builtin('see/1',_,_,old_herbrand,_).
lsign_special_builtin('tell/1',_,_,old_herbrand,_).
lsign_special_builtin(':/2',(prolog:'$metacut'(_)),_,old_herbrand,_).
%-------------------------------------------------------------------------
lsign_special_builtin('!/0',_,_,unchanged,_).
lsign_special_builtin('assert/1',_,_,unchanged,_).
lsign_special_builtin('asserta/1',_,_,unchanged,_).
lsign_special_builtin('assertz/1',_,_,unchanged,_).
lsign_special_builtin('debug/0',_,_,unchanged,_).
lsign_special_builtin('debugging/0',_,_,unchanged,_).
lsign_special_builtin('dif/2',_,_,unchanged,_).  %%%%%%
lsign_special_builtin('display/1',_,_,unchanged,_).
lsign_special_builtin('garbage_collect/0',_,_,unchanged,_).
lsign_special_builtin('gc/0',_,_,unchanged,_).
lsign_special_builtin('listing/0',_,_,unchanged,_).
lsign_special_builtin('listing/1',_,_,unchanged,_).
lsign_special_builtin('nl/0',_,_,unchanged,_).
lsign_special_builtin('nogc/0',_,_,unchanged,_).
lsign_special_builtin('print/1',_,_,unchanged,_).
lsign_special_builtin('repeat/0',_,_,unchanged,_).
lsign_special_builtin('start_event_trace/0',_,_,unchanged,_).
lsign_special_builtin('stop_event_trace/0',_,_,unchanged,_).
lsign_special_builtin('seen/0',_,_,unchanged,_).
lsign_special_builtin('told/0',_,_,unchanged,_).
lsign_special_builtin('true/0',_,_,unchanged,_).
lsign_special_builtin('ttyflush/0',_,_,unchanged,_).
lsign_special_builtin('otherwise/0',_,_,unchanged,_).
lsign_special_builtin('ttynl/0',_,_,unchanged,_).
lsign_special_builtin('write/1',_,_,unchanged,_).
lsign_special_builtin('writeq/1',_,_,unchanged,_).
% SICStus3 (ISO)
lsign_special_builtin('\\==/2',_,_,unchanged,_).
% SICStus2.x
% lsign_special_builtin('\==/2',_,_,unchanged,_).
lsign_special_builtin('@>=/2',_,_,unchanged,_).
lsign_special_builtin('@=</2',_,_,unchanged,_).
lsign_special_builtin('@>/2',_,_,unchanged,_).
lsign_special_builtin('@</2',_,_,unchanged,_).
%-------------------------------------------------------------------------
lsign_special_builtin('depth/1',_,_,positive,_).
lsign_special_builtin('get_code/1',_,_,positive,_).
lsign_special_builtin('get1_code/1',_,_,positive,_).
lsign_special_builtin('put_code/1',_,_,positive,_).
lsign_special_builtin('tab/1',_,_,positive,_).
lsign_special_builtin('ttyput/1',_,_,positive,_).
%-------------------------------------------------------------------------
% SICStus3 (ISO)
lsign_special_builtin('=\\=/2',_,_,unsigned,_).
% SICStus2.x
% lsign_special_builtin('=\=/2',_,_,unsigned,_).
%-------------------------------------------------------------------------
lsign_special_builtin('atomic/1',_,_,old_unsigned,_).
lsign_special_builtin('float/1',_,_,old_unsigned,_).
lsign_special_builtin('ground/1',_,_,old_unsigned,_).
lsign_special_builtin('integer/1',_,_,old_unsigned,_).
lsign_special_builtin('number/1',_,_,old_unsigned,_).
%-------------------------------------------------------------------------
lsign_special_builtin('assert/2',assert(_,Y),_,some_old_herbrand,Y).
lsign_special_builtin('asserta/2',asserta(_,Y),_,some_old_herbrand,Y).
lsign_special_builtin('assertz/2',assertz(_,Y),_,some_old_herbrand,Y).
lsign_special_builtin('format/2',format(X,_),_,some_old_herbrand,X).
lsign_special_builtin('format/3',format(X,Y,_),_,some_old_herbrand,p(X,Y)).
lsign_special_builtin('print/2',print(X,_),_,some_old_herbrand,X).
lsign_special_builtin('recorda/3',recorda(_,_,Z),_,some_old_herbrand,Z).
lsign_special_builtin('recordz/3',recordz(_,_,Z),_,some_old_herbrand,Z).
lsign_special_builtin('write/2',write(X,_),_,some_old_herbrand,X).
%-------------------------------------------------------------------------
lsign_special_builtin('compare/3',compare(X,_,_),_,some_herbrand,X).
%-------------------------------------------------------------------------
lsign_special_builtin('put_code/2',put_code(X,Y),_,positive_old_herbrand,p(Y,X)).
lsign_special_builtin('tab/2',tab(X,Y),_,positive_old_herbrand,p(Y,X)).
lsign_special_builtin('get_code/2',get_code(X,Y),_,positive_old_herbrand,p(Y,X)).
lsign_special_builtin('get1_code/2',get1_code(X,Y),_,positive_old_herbrand,p(Y,X)).
%-------------------------------------------------------------------------
lsign_special_builtin('statistics/2',statistics(X,Y),_,positive_herbrand,p(Y,X)).
%-------------------------------------------------------------------------
lsign_special_builtin('open/3',open(X,Y,Z),_,herbrand_old_herbrand,p(Z,p(X,Y))).
%-------------------------------------------------------------------------
%%%%%%%%%% Constraints
lsign_special_builtin('=/2','='(X,Y),_,'=/2',p(X,Y)).
lsign_special_builtin('>/2','>'(X,Y),_,inequation,eq(less,Y,X)).
lsign_special_builtin('</2','<'(X,Y),_,inequation,eq(less,X,Y)).
lsign_special_builtin('=</2','=<'(X,Y),_,inequation,eq(leq,X,Y)).
lsign_special_builtin('>=/2','>='(X,Y),_,inequation,eq(leq,Y,X)).
lsign_special_builtin('.=./2','.=.'(X,Y),_,'=/2',p(X,Y)).
lsign_special_builtin('.>./2','.>.'(X,Y),_,inequation,eq(less,Y,X)).
lsign_special_builtin('.<./2','.<.'(X,Y),_,inequation,eq(less,X,Y)).
lsign_special_builtin('.=<./2','.=<.'(X,Y),_,inequation,eq(leq,X,Y)).
lsign_special_builtin('.>=./2','.>=.'(X,Y),_,inequation,eq(leq,Y,X)).
%-------------------------------------------------------------------------
lsign_special_builtin('is/2',Sg,_,is,Sg).
%-------------------------------------------------------------------------
%% lsign_special_builtin('nonvar/1',_,_,unchanged,_). % needed?
%% lsign_special_builtin('not_free/1',_,_,unchanged,_).
%% lsign_special_builtin('var/1',_,_,unchanged,_). % needed?
%% lsign_special_builtin('free/1',_,_,unchanged,_).
%% lsign_special_builtin('functor/3',functor(_,Y,Z),_,ground_herbrand,p(Y,Z)).
%% lsign_special_builtin('length/2',length(_,Y),_,ground_arithmetic,Y).
%% lsign_special_builtin('dif/2',_,_,unchanged,_).
%% lsign_special_builtin('=:=/2',_,_,old_ground,_).
%% % SICStus3 (ISO)
%% lsign_special_builtin('=\\=/2',_,_,old_ground,_).
%% % SICStus2.x
%% % lsign_special_builtin('=\=/2',_,_,old_ground,_).
%% lsign_special_builtin('numbervars/3',_,_,usigned_herbrand,Sg).
%% lsign_special_builtin('absolute_file_name/2',_,_,ground_herbrand,_).
%% lsign_special_builtin('name/2',_,_,herbrand,_).

%-------------------------------------------------------------------------
% lsign_success_builtin(+,+,+,+,-,-) 
% lsign_success_builtin(Type,Sv_u,Condv,HvFv_u,Call,Succ) 
%-------------------------------------------------------------------------
% Adds the information of builtins
%-------------------------------------------------------------------------

lsign_success_builtin(bottom,_,_,_,_,'$bottom').
lsign_success_builtin(unchanged,_,_,_,Call,Call).
lsign_success_builtin(herbrand,Sv_u,_,_,a(S,AEqIn,Non),Succ):-
    sort(Sv_u,Sv),
    ord_subtract_signed(Sv,S,NewGround),
    ( NewGround = [] ->
        Succ = a(S,AEqIn,Non)
    ; change_values_insert(NewGround,S,TmpS,t),
      create_values(NewGround,NG,t),
      lsign_propagate_herbrand(AEqIn,NG,NAEqIn,TmpS,NS),
      ord_subtract(NS,TmpS,Diff),
      lsign_propagate_fixpoint(Diff,NAEqIn,Non,NAEqIn2,NNon,NS,S2,_),
      Succ = a(S2,NAEqIn2,NNon)
    ).
lsign_success_builtin(old_herbrand,Sv_u,_,_,Call,Succ):-
    lsign_success_builtin(herbrand,Sv_u,_,_,Call,Succ).
lsign_success_builtin(positive,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    create_values(Sv,Pos,+),
    Call = a(S,_,_),
    lsign_merge_signed(Pos,S,NewS,F),
    ( F = cons ->
        lsign_abstract_positive(Sv,AEqIn,[]),
        lsign_sum(a(NewS,AEqIn,[]),Call,Succ)
    ; Succ = '$bottom'
    ).
lsign_success_builtin(unsigned,Sv_u,_,_,Call,Succ):-
    sort(Sv_u,Sv),
    Call = a(S,_,_),
    ord_subtract_signed(Sv,S,NewUnsigned),
    create_values(NewUnsigned,NewS,[]),
    lsign_abstract_unsigned(NewUnsigned,AEqIn,[]),
    lsign_sum(a(NewS,AEqIn,[]),Call,Succ).
lsign_success_builtin(old_unsigned,Sv_u,_,_,Call,Succ):-
    lsign_success_builtin(unsigned,Sv_u,_,_,Call,Succ).
lsign_success_builtin(some_herbrand,_,Some,_,Call,Succ):-
    varset(Some,Sv),
    lsign_success_builtin(herbrand,Sv,_,_,Call,Succ).
lsign_success_builtin(some_old_herbrand,_,Some,_,Call,Succ):-
    lsign_success_builtin(some_herbrand,_,Some,_,Call,Succ).
lsign_success_builtin(positive_herbrand,_,p(Pos,Her),_,Call,Succ):-
    varset(Pos,Pv),
    lsign_success_builtin(positive,Pv,_,_,Call,Succ0),
    ( Succ0= '$bottom' ->
        Succ = '$bottom'
    ; varset(Her,Hev),
      lsign_success_builtin(herbrand,Hev,_,_,Succ0,Succ)
    ).
lsign_success_builtin(positive_old_herbrand,_,PH,_,Call,Succ):-
    lsign_success_builtin(positive_herbrand,_,PH,_,Call,Succ).
lsign_success_builtin('=/2',_,p(X,Y),_,Call,Succ):-
    nonvar(Y),
    lsign_non_linear(Y),!,
    lsign_add_non_linear(Y,X,Call,Succ).
lsign_success_builtin('=/2',_,p(X,Y),_,Call,Succ):-
    var(X),!,
    ( nonvar(Y),find_type(Y,num) ->
        lsign_abstract_equation(X,Y,Sign,Expr),
        lsign_add_linear(eq(eq,Sign,Expr),Call,Succ)
    ;     varset(Y,VarsY),  
          Call = a(S,_,_),
          ord_subtract_signed(VarsY,S,NonSignedY),
          ord_subtract_signed([X],S,P),
          lsign_add_herbrand(NonSignedY,P,X,Y,Call,Succ)
    ).          
lsign_success_builtin('=/2',_,p(X,Y),_,Call,Succ):-
    number(X),
    lsign_abstract_equation(X,Y,Sign,Expr),!,
    lsign_add_linear(eq(eq,Sign,Expr),Call,Succ).
lsign_success_builtin('=/2',_,_,_,_,'$bottom').
lsign_success_builtin(inequation,_,eq(Op,X,Y),_,Call,Succ):-
    Call = a(S,AEqIn,Non),
    lsign_abstract_inequation(X,Y,Sign,Expr),
    lsign_propagate_fixpoint(S,[eq(Op,Sign,Expr)],[],TmpEqIn,_,S,_,_),
    lsign_sum0(TmpEqIn,AEqIn,SuccAEqIn),
    Succ = a(S,SuccAEqIn,Non).
lsign_success_builtin(is,_,is(X,Y),HvFv_u,Call,Succ):- 
    sort(HvFv_u,HvFv),
    Call = a(S,AEqIn,Non),
    varset(Y,VarsY),
    ord_subtract_signed(VarsY,S,OldGround),
    lsign_project_each(OldGround,Call,HvFv,S,[],TmpS),!,
    collect_vars_freeness(TmpS,Ground1),
    ord_subtract(OldGround,Ground1,Ground2),
    insert(Ground2,X,Ground3),
    change_values_insert(Ground3,TmpS,NewS,t),
    ord_union_diff(S,NewS,Union,Diff),
    lsign_propagate_fixpoint(Diff,AEqIn,Non,NAEqIn,NNon,Union,NS,F),
    ( F = cons ->
        lsign_success_builtin('=/2',_,p(X,Y),HvFv_u,a(NS,NAEqIn,NNon),Succ)
    ; Succ = '$bottom'
    ).
lsign_success_builtin(is,_,_,_,_,'$bottom').
    
%-------------------------------------------------------------------------
% lsign_non_linear(+)
% lsign_non_linear(X)
%-------------------------------------------------------------------------
% Satisfied if X is a non-linear function
%-------------------------------------------------------------------------

lsign_non_linear(_*_).
lsign_non_linear(sin(_)).    
lsign_non_linear(arcsin(_)). 
lsign_non_linear(cos(_)).    
lsign_non_linear(arccos(_)). 
lsign_non_linear(pow(_,_)).  
lsign_non_linear(max(_,_)).  
lsign_non_linear(min(_,_)).  
lsign_non_linear(abs(_)).    

%------------------------------------------------------------------------%
% lsign_add_non_linear(+,+,+,-,?,-)
% lsign_add_non_linear(Y,X,S,AEqIn,Tail,F)
%------------------------------------------------------------------------%
% Adds the information given by the non linear equation X = Y, where X
% is a variable and Y a non-linear function
%------------------------------------------------------------------------%

lsign_add_non_linear(Y,X,Call,Succ):- 
    Call = a(S,_,_),
    lsign_propagate_fixpoint(S,[],[eq(eq,X,Y)],TmpEqIn,TmpNon,S,S1,F),
    ( F = cons ->
        ord_subtract(S1,S,NewS),
        lsign_sum(a(NewS,TmpEqIn,TmpNon),Call,Succ)
    ; Succ = '$bottom'
    ).

%------------------------------------------------------------------------%
% lsign_add_herbrand(+,+,-)
% lsign_add_herbrand(NonSignedY,NonSignedX,X,Y,Call,Succ)
%------------------------------------------------------------------------%
% It adds the information provided by the Herbrand unification X = Y, 
% where X is a variables and Y any herbrand term. NonSignedY and NonSignedX
% are the set of variables in Yand X respectively,  which are not known to 
% have a prticular sign.
%------------------------------------------------------------------------%

lsign_add_herbrand([],[],_,_,Call,Succ):- !,
    Succ = Call.
lsign_add_herbrand([],_,X,_,a(S,AEqIn,Non),Succ):- !,
    change_values_insert([X],S,TmpS,t),
    lsign_propagate_herbrand([X],AEqIn,NAEqIn,TmpS,NS),
    ord_subtract(NS,TmpS,Diff),
    lsign_propagate_fixpoint(Diff,NAEqIn,Non,NAEqIn2,NNon,NS,S2,_),
    Succ = a(S2,NAEqIn2,NNon).
lsign_add_herbrand(NonSignedY,[],_,_,Call,Succ):- !,
    create_values(NonSignedY,S,t),
    lsign_abstract_unsigned(NonSignedY,AEqIn,[]),
    lsign_sum(a(S,AEqIn,[]),Call,Succ).
lsign_add_herbrand(NonSignedY,_,X,_,a(S,AEqInCall,Non),Succ):-
    lsign_abstract_herbrand_eq(NonSignedY,X,TmpAEqIn,[]),
    sort(TmpAEqIn,AEqIn),
    lsign_sum0(AEqIn,AEqInCall,AEqInSucc),
    Succ = a(S,AEqInSucc,Non).
    
%------------------------------------------------------------------------%
% lsign_add_linear(+,+,-)
% lsign_add_linear(Eq,Call,Succ)
%------------------------------------------------------------------------%
% Eq is a linear equation.
%------------------------------------------------------------------------%

lsign_add_linear(Eq,Call,Succ):-
    Call = a(S,_,_),
    lsign_propagate_fixpoint(S,[Eq],[],TmpEqIn,_,S,_,F),
    ( F = cons ->
        get_signed(TmpEqIn,[],NewS,_),
        lsign_sum(a(NewS,TmpEqIn,[]),Call,Succ)
    ; Succ = '$bottom'
    ).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%
%                        UTILITIES
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

%------------------------------------------------------------------------%
% neg_expr(+,-)
% neg_expr(Expr0,Expr)
%------------------------------------------------------------------------%
% It negeates the sign of each element in Expr0, resulting in Expr
%------------------------------------------------------------------------%

neg_expr([],[]).
neg_expr([X/Sign0|Expr0],[X/Sign|Expr]):-
    neg_sign(Sign0,Sign),
    neg_expr(Expr0,Expr).

neg_sign(0,0).
neg_sign(+,-).
neg_sign(-,+).
neg_sign(t,t).

%------------------------------------------------------------------------%
% first_coeff_positive(+,-)
% first_coeff_positive(Expr0,Expr)
%------------------------------------------------------------------------%
% Let Expr0 = [X_1/Sign_1, ..., X_n/Sign_n] and let Sign_i be the first
% sign different from 't'. If Sign_i = '+', Expr = Expr0. Otherwise,
% Expr = [X_1/Sign_1, ...,X_{i-1}/Sign_{i-1}] + Rest, while Rest is the
% result of negating the expression [X_i/Sign_i,....,X_n/Sign_n]
%------------------------------------------------------------------------%

first_coeff_positive([],[]).
first_coeff_positive([X/'+'|Expr0],Expr):- !,
    Expr = [X/'+'|Expr0].
first_coeff_positive([X/'-'|Expr0],[X/'+'|Expr]):- !,
    neg_expr(Expr0,Expr).
first_coeff_positive([X/t|Expr0],[X/t|Expr]):- 
    first_coeff_positive(Expr0,Expr).

%------------------------------------------------------------------------%
% look_for_eq_or_eqplus(+,+,-,-,-)                                       %
% look_for_eq_or_eqplus(ACons,X,SignX,Eq,ACons0)                         %
%------------------------------------------------------------------------%
% This predicate looks for an element Eq = eq(Op,Sign,Expr) in ACons 
% such that Op in {eq,eq+}, and X/SignX in Expr, with SignX in {+,-}. 
% Then, ACons0 is ACons \ {Eq}.
% Assumptions:
%   - ACons and Vars are sorted
%   - Such an equation exists.
%------------------------------------------------------------------------%

look_for_eq_or_eqplus([],_,_,_,_):-
    error_message('Equality not found').
look_for_eq_or_eqplus([Eq0|ACons],X,SignX,Eq,ACons0):-
    Eq0 = eq(_,_,Expr),
    look_for_plus_or_minus(Expr,X,SignX),!,
    Eq = Eq0,
    ACons0 = ACons. 
look_for_eq_or_eqplus([Eq0|ACons],X,SignX,Eq,[Eq0|ACons0]):- 
    look_for_eq_or_eqplus(ACons,X,SignX,Eq,ACons0).

look_for_plus_or_minus([Y/SignX|_],X,SignX):-
    X == Y,!.
look_for_plus_or_minus([_|Expr],X,SignX):-
    look_for_plus_or_minus(Expr,X,SignX).

%------------------------------------------------------------------------%
% split_from_list_vars(+,+,-)
% split_from_list_vars(ACons,Vars,IntersectACons)
%------------------------------------------------------------------------%
% IntersectACons contains all elements in ACons in which at least a 
% variable from Vars appears.
% Assumptions: 
%  - Vars is ordered
%------------------------------------------------------------------------%

split_from_list_vars(ACons,[],ACons):- !.
split_from_list_vars(ACons,Vars,ACons1):- 
    split_from_list_vars0(ACons,Vars,ACons1).

split_from_list_vars0([],_,[]).
split_from_list_vars0([EqIn|ACons],Vars,Disjunct):-
    EqIn = eq(_,_,Expr),
    ( ord_intersect_expr(Vars,Expr) ->
        Disjunct0 = Disjunct
    ;   Disjunct = [EqIn|Disjunct0]
    ),
    split_from_list_vars0(ACons,Vars,Disjunct0).

%------------------------------------------------------------------------%
% split_identical_expr(+,+,+,-,-)
% split_identical_expr(ACons,Sign,Expr,Op2,Disjunct)
%------------------------------------------------------------------------%
% Sign and Expr are part of an abstraction
% If there exists in ACons another abtraction Eq=eq(Op1,Sign1,Expr1), such 
% that Sign1==Sign and Expr1==Expr, then Op2=Op and Disjunct=ACons\InEq. 
% Otherwise, Op2=no, Disjunct=ACons.
% Assumptions:
%   * Sign and Sign1 are ground
%------------------------------------------------------------------------%

split_identical_expr([],_,_,no,[]).
split_identical_expr([eq(Op,Sign,Expr1)|ACons],Sign,Expr,Op2,Disjunct):-
    Expr1 == Expr,!,
    Op2 = Op,
    Disjunct = ACons.
split_identical_expr([Eq|ACons],Sign,Expr,Op2,[Eq|Disjunct]):-
    split_identical_expr(ACons,Sign,Expr,Op2,Disjunct).

%------------------------------------------------------------------------%
% split_sign(+,+,+,-,-,-)
% split_sign(ACons,X,C0,Ct+,Ct-,Ct)
%------------------------------------------------------------------------%
% It splits ACons into C0,Ct+, Ct-, and Ct, i.e. those elements in which 
% the variable X appears with 0 coefficient (does not appear), t or +
% coefficient, t or - coeffcicient, and t, respectively.
% Assumptions:
%   - none
%------------------------------------------------------------------------%

split_sign([],_,[],[],[],[]).
split_sign([EqIn|ACons],X,C0,Ctplus,Ctminus,Ct):-
    EqIn = eq(_,_,Expr),
    find_sign(Expr,X,Sign),
    insert_eq(Sign,EqIn,C0,Ctplus,Ctminus,Ct,TC0,TCtplus,TCtminus,TCt),
    split_sign(ACons,X,TC0,TCtplus,TCtminus,TCt).

find_sign([],_,no).
find_sign([Y/Sig|Tail],X,Sign) :-
    compare(Order,Y,X),
    find_sign_(Order,Sig,Tail,X,Sign).

find_sign_(<,_,Tail,X,Sign) :-
    find_sign(Tail,X,Sign).
find_sign_(=,Sign,_,_,Sign).
find_sign_(>,_,_,_,no).

insert_eq(no,EqIn,[EqIn|C0],Ctplus,Ctminus,Ct,C0,Ctplus,Ctminus,Ct).
insert_eq(+,EqIn,C0,[EqIn|Ctplus],Ctminus,Ct,C0,Ctplus,Ctminus,Ct).
insert_eq(-,EqIn,C0,Ctplus,[EqIn|Ctminus],Ct,C0,Ctplus,Ctminus,Ct).
insert_eq(t,EqIn,C0,[EqIn|Ctplus],[EqIn|Ctminus],[EqIn|Ct],C0,Ctplus,Ctminus,Ct).
    
%------------------------------------------------------------------------%
% anegate(+,-)
% anegate(EqIn,NegatedEqIn)
%------------------------------------------------------------------------%
% Negates the equation EqIn.
%------------------------------------------------------------------------%

anegate(eq(Op,Sign,Expr),eq(Op,NSign,NExpr)):-
    neg_sign(Sign,NSign),
    neg_expr(Expr,NExpr).

%------------------------------------------------------------------------%
% lsign_project_signed(+,+,-)                
% lsign_project_signed(Vars,LS,Proj)                             
%------------------------------------------------------------------------%
% Projects the information in LS onto the variables in Vars
% Assumptions:
%      - Vars and LS are sorted
%------------------------------------------------------------------------%

lsign_project_signed([],_,Proj):- !,
    Proj = [].
lsign_project_signed(_,[],Proj):- !,
    Proj = [].
lsign_project_signed([X|Vars],[Y/Sign|LS],Proj) :-
    compare(Order,X,Y),
    lsign_project_signed_(Order,X,Vars,Y/Sign,LS,Proj).

lsign_project_signed_(>,_,_,_,[],[]) :- !.
lsign_project_signed_(>,X,Vars,_,[Y/SignY|LS],Proj) :-
    compare(Order,X,Y),
    lsign_project_signed_(Order,X,Vars,Y/SignY,LS,Proj).
lsign_project_signed_(=,_,Vars,Y,LS,[Y|Proj]) :-
    lsign_project_signed(Vars,LS,Proj).
lsign_project_signed_(<,_,[],_,_,[]) :- !.
lsign_project_signed_(<,_,[X|Vars],Y/SignY,LS,Proj) :-
    compare(Order,X,Y),
    lsign_project_signed_(Order,X,Vars,Y/SignY,LS,Proj).

%------------------------------------------------------------------------%
% lsign_sign(+,+,+,-,-).
% lsign_sign(Op,Sign,Expr,X,SignX)
%------------------------------------------------------------------------%
% Satisfied if eq(Op,Sign,Expr) uniquely determines X to be ground
% with sign SignX. Op must be in {eq,eq+}. Let Expr be [X/Sign1], SignX 
% is computed from Sign and Sign1 as follows:
%                                +   -   t  (Sign1)
%                            ---------------------------
%                            + | +   -   t
%                            - | *   *   *
%                            0 | 0   0   @
%                            t | t   *   @
%                          Sign
% where * means impossible (due to normalization) and @ means that X is not 
% uniquely determined to a sign.
%------------------------------------------------------------------------%

lsign_sign(eq,Sign,[X/Sign1],X,SignX):-
    lsign_compute_sign(Sign,Sign1,SignX).
lsign_sign('eq+',Sign,[X/Sign1],X,SignX):-
    lsign_compute_sign(Sign,Sign1,SignX).

lsign_compute_sign(+,X,X).
lsign_compute_sign(t,+,t).
lsign_compute_sign(0,+,0):- !.
lsign_compute_sign(0,-,0).

%------------------------------------------------------------------------%
% lsign_merge_signed(+,+,-,-)                
% lsign_merge_signed(LS1,LS2,LS,Flag)
%------------------------------------------------------------------------%
% LS is the result of combining the sign information in LS1 and LS2. Flag
% will be a variables is such combination is possibly consistent, or 
% the constant 'incons' otherwise.
% Assumptions:
%      - Ls1 and Ls2 are sorted
%      - Flag is a variable
%------------------------------------------------------------------------%

lsign_merge_signed([],LS,LS,_) :- !.
lsign_merge_signed(LS,[],LS,_) :- !.
lsign_merge_signed([X/SignX|LS1],[Y/SignY|LS2],LS,F) :-
    compare(Order,X,Y),
    lsign_merge_signed_(Order,X,SignX,LS1,Y,SignY,LS2,LS,F).

lsign_merge_signed_(<,X,SignX,[],Y,SignY,LS2,[X/SignX,Y/SignY|LS2],_) :- !.
lsign_merge_signed_(<,X0,SignX0,[X/SignX|LS1],Y,SignY,LS2,[X0/SignX0|LS],F) :-
    compare(Order,X,Y),
    lsign_merge_signed_(Order,X,SignX,LS1,Y,SignY,LS2,LS,F).
lsign_merge_signed_(=,X,SignX,LS1,_,SignY,LS2,[X/Sign|LS],F) :- 
    consistent_signs(SignX,SignY,Sign),!,
    lsign_merge_signed(LS1,LS2,LS,F).
lsign_merge_signed_(=,_,_,_,_,_,_,_,incons).
lsign_merge_signed_(>,X,SignX,LS1,Y,SignY,[],[Y/SignY,X/SignX|LS1],_) :- !.
lsign_merge_signed_(>,X,SignX,LS1,Y0,SignY0,[Y/SignY|LS2],[Y0/SignY0|LS],F) :-
    compare(Order,X,Y),
    lsign_merge_signed_(Order,X,SignX,LS1,Y,SignY,LS2,LS,F).

consistent_signs(Sign,Sign,Sign):- !.
consistent_signs(t,Sign,Sign):- !.
consistent_signs(Sign,t,Sign).

%------------------------------------------------------------------------%
% ord_intersect_expr(+,+)
% ord_intersect_expr(Vars,Expr)
%------------------------------------------------------------------------%
% Satisfied if at least a variable in Vars appears in the expression Expr
% Assumptions: 
%  - Vars and Expr are ordered
%------------------------------------------------------------------------%

ord_intersect_expr([X|Vars],[Y/_|Expr]) :-
    compare(Order,X,Y),
    ord_intersect_expr_(Order,X,Vars,Y,Expr).

ord_intersect_expr_(<,_,[X|Vars],Y,Expr) :-
    compare(Order,X,Y),
    ord_intersect_expr_(Order,X,Vars,Y,Expr).
ord_intersect_expr_(=,_,_,_,_).
ord_intersect_expr_(>,X,Vars,_,[Y/_|Expr]) :-
    compare(Order,X,Y),
    ord_intersect_expr_(Order,X,Vars,Y,Expr).

%------------------------------------------------------------------------%
% ord_subtract_signed(+,+,-)                
% ord_subtract_signed(Vars,LS,Difference)
%------------------------------------------------------------------------%
% Difference is the result of eliminating from Vars any variable X such 
% that  X/_ appears in LS
%------------------------------------------------------------------------%

ord_subtract_signed([],_,[]) :- !.
ord_subtract_signed(Vars,[],Vars) :- !.
ord_subtract_signed([X|Vars],[Y/_|LS],Difference) :-
    compare(Order,X,Y),
    ord_subtract_signed_(Order,X,Vars,Y,LS,Difference).

ord_subtract_signed_(<,X,[],_,_,[X]) :- !.
ord_subtract_signed_(<,X0,[X|Vars],Y,LS,[X0|Difference]) :-
    compare(Order,X,Y),
    ord_subtract_signed_(Order,X,Vars,Y,LS,Difference).
ord_subtract_signed_(=,_,Vars,_,LS,Difference) :-
    ord_subtract_signed(Vars,LS,Difference).
ord_subtract_signed_(>,X,Vars,_,[],[X|Vars]) :- !.
ord_subtract_signed_(>,X,Vars,_,[Y/_|LS],Difference) :-
    compare(Order,X,Y),
    ord_subtract_signed_(Order,X,Vars,Y,LS,Difference).

%------------------------------------------------------------------------%
% lsign_ord_intersection(+,+,-)                
% lsign_ord_intersection(S1,S2,Intersection)
%------------------------------------------------------------------------%
% Intersection = {X/Sign | X/Sign1 in S1, X/Sign2 in S2, and
%                 lsign_lub_sign(Sign1,Sign2,Sign)}
% 
% Assumptions:
%  * S1 and S2 are ordered
%------------------------------------------------------------------------%
    
lsign_ord_intersection([],_,[]) :- !.
lsign_ord_intersection(_,[],[]) :- !.
lsign_ord_intersection([X/SignX|S1],[Y/SignY|S2],Intersection) :-
    compare(Order,X,Y),
    lsign_ord_intersection_(Order,X,SignX,S1,Y,SignY,S2,Intersection).

lsign_ord_intersection_(<,_,_,[],_,_,_,[]) :- !.
lsign_ord_intersection_(<,_,_,[X/SignX|S1],Y,SignY,S2,Intersection) :-
    compare(Order,X,Y),
    lsign_ord_intersection_(Order,X,SignX,S1,Y,SignY,S2,Intersection).
lsign_ord_intersection_(=,X,SignX,S1,_,SignY,S2,[X/Sign|Intersection]) :-
    lsign_lub_sign(SignX,SignY,Sign),
    lsign_ord_intersection(S1,S2,Intersection).
lsign_ord_intersection_(>,_,_,_,_,_,[],[]) :- !.
lsign_ord_intersection_(>,X,SignX,S1,_,_,[Y/SignY|S2],Intersection) :-
    compare(Order,X,Y),
    lsign_ord_intersection_(Order,X,SignX,S1,Y,SignY,S2,Intersection).

%------------------------------------------------------------------------%
% get_signed(+,+,-,-)
% get_signed(ACons,AccS,Union,F)
%------------------------------------------------------------------------%
% for each Eq = eq(Op,Sign,Expr) in ACons such that Eq uniquely 
% determines variable X to to have sign SignX, X/SignX is added to AccS
% F=incons if for at least a variable the signs assigned are incompatible
%------------------------------------------------------------------------%

get_signed([eq(Op,Sign,Expr)|ACons],S,Union,F):-
    Op @=< 'eq+',!,
    ( lsign_sign(Op,Sign,Expr,Y,SignY) ->
        lsign_merge_signed(S,[Y/SignY],S1,F1),
        ( F1 = cons ->
            get_signed(ACons,S1,Union,F)
        ; Union = [],
          F = incons
        )
    ; get_signed(ACons,S,Union,F)
    ).
get_signed(_,S,S,_).

%------------------------------------------------------------------------%
% lsign_propagate_herbrand(+,+,-,+,-)
% lsign_propagate_herbrand(AEqIn,LS,NAEqIn,OldLS,FinalLS)
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

lsign_propagate_herbrand([],_,[],S,S).
lsign_propagate_herbrand([EqIn|AEqIn],S1,NAEqIn,S2,S):-
    EqIn = eq(Op,_,Expr),
    propagate_expr_top(Expr,S1,Expr0,Chg),
    ( Chg = unchanged ->
        NewEqIn = EqIn,
        S22 = S2
    ; lsign_normalize(Op,t,Expr0,NewEqIn),
      NewEqIn = eq(Op,NewSign,NewExpr),
      ( lsign_sign(Op,NewSign,NewExpr,Y,SignY) ->
          lsign_merge_signed([Y/SignY],S2,S22,_)
      ;  S22 = S2
      )
    ),
    NAEqIn = [NewEqIn|Tail],
    lsign_propagate_herbrand(AEqIn,S1,Tail,S22,S).

%------------------------------------------------------------------------%
% lsign_propagate_fixpoint(+,+,-,+,-,-)
% lsign_propagate_fixpoint(LS,AEqIn,NAEqIn,OldLS,FinalLS,Flag)
%------------------------------------------------------------------------%
% Propagates the (new) signed information from LS to AEqIn, obtaining
% NAEqIn and the NewLS, which are merged with OLdLS to give FinalLs.
% Fixpoint is called depending on NewLs. The variable Flag will become
% 'incons' if during the process inconsistency is detected.
% Assumptions
%------------------------------------------------------------------------%

:- export(lsign_propagate_fixpoint/8).
lsign_propagate_fixpoint([],AEqIn_u,Non_u,AEqIn,Non,S2,S,_):- !,
    sort(AEqIn_u,AEqIn),
    sort(Non_u,Non),
    S = S2.
lsign_propagate_fixpoint(S1,AEqIn,Non,NAEqIn,NNon,S2,S,F):-
    lsign_propagate(AEqIn,S1,NAEqIn0,S2,S3,F1),
    ( F1 = cons -> 
        lsign_propagate_non(Non,S3,NNon0,NAEqIn1,NAEqIn0,S4,F),
        ord_subtract(S4,S2,NewS),
        lsign_propagate_fixpoint(NewS,NAEqIn1,NNon0,NAEqIn,NNon,S4,S,F)
    ; S = [],
      F = incons
    ).

%------------------------------------------------------------------------%
% lsign_propagate(+,+,-,+,-,-)
% lsign_propagate(AEqIn,LS,NAEqIn,OldLS,FinalLS,Flag)
%------------------------------------------------------------------------%
% Propagates the (new) signed information from LS to each equation or
% inequation in AEqIn. The variable Flag will become  'incons' if during 
% the process inconsistency is detected. OldLS is an accumulator
% for FinalS.
%------------------------------------------------------------------------%

lsign_propagate([],_,[],S,S,_).
lsign_propagate([EqIn|AEqIn],S1,NAEqIn,S2,S,F):-
    EqIn = eq(Op,Sign,Expr),
    ( Sign = t ->
        propagate_expr_top(Expr,S1,Expr0,Chg),
        SumSign = t,
        S11 = S1
    ; propagate_expr(Expr,S1,0,Expr0,SumSign,Exprt,SumSignt,Chg),
      ( SumSignt = 0 ->
          S11 = S1
      ; lsign_normalize(Op,t,Exprt,NewEqIn),
        NewEqIn = eq(Op1,Expr1,Sign1),
        ( lsign_sign(Op1,Sign1,Expr1,Y,SignY) ->
             lsign_merge_signed([Y/SignY],S1,S11,_)
        ; S11 = S1
        )
      )
    ),
    check_propagate(Chg,Op,SumSign,Expr0,EqIn,AEqIn,S11,NAEqIn,S2,S,F).

%------------------------------------------------------------------------%
% propagate_expr_top(+,+,+,-,-,-)
% propagate_expr_top(Expr1,LS,Sign,Expr,Sign1,Flag)
%------------------------------------------------------------------------%

propagate_expr_top([],_,[],_) :- !.
propagate_expr_top(Expr,[],Expr,_) :- !.
propagate_expr_top([X/SignX|Expr1],[Y/V2|Expr],Diff,F) :-
    compare(Order,X,Y),
    propagate_expr_top_(Order,X/SignX,Expr1,Y,V2,Expr,Diff,F).

propagate_expr_top_(<,X,[],_,_,_,[X],_) :- !.
propagate_expr_top_(<,X0,[X/SignX|Expr1],Y,SignY,Expr,[X0|Diff],F):-
    compare(Order,X,Y),
    propagate_expr_top_(Order,X/SignX,Expr1,Y,SignY,Expr,Diff,F).
propagate_expr_top_(=,_,Expr1,_,_,Expr,Diff,changed) :-
    propagate_expr_top(Expr1,Expr,Diff,_).
propagate_expr_top_(>,X,Expr1,_,_,[],[X|Expr1],_) :- !.
propagate_expr_top_(>,X/SignX,Expr1,_,_,[Y/SignY|Expr],Diff,F) :-
    compare(Order,X,Y),
    propagate_expr_top_(Order,X/SignX,Expr1,Y,SignY,Expr,Diff,F).

%------------------------------------------------------------------------%
% propagate_expr(+,+,+,-,-,-)
% propagate_expr(Expr1,LS,Sign,Expr,Sign1,Exprt,Signt,Flag)
%------------------------------------------------------------------------%

propagate_expr([],_,S,[],S,[],_,_) :- !.
propagate_expr(Expr,[],S,Expr,S,Expr,_,_) :- !.
propagate_expr([X/SignX|Expr1],[Y/V2|Expr],Sign0,Diff,Sign,Difft,Signt,F) :-
    compare(Order,X,Y),
    propagate_expr_(Order,X/SignX,Expr1,Y,V2,Expr,Sign0,Diff,Sign,Difft,Signt,F).

propagate_expr_(<,X,[],_,_,_,S,[X],S,[X],_,_) :- !.
propagate_expr_(<,X0,[X/SignX|Expr1],Y,SignY,Expr,Sign0,[X0|Diff],Sign,[X0|Difft],Signt,F):-
    compare(Order,X,Y),
    propagate_expr_(Order,X/SignX,Expr1,Y,SignY,Expr,Sign0,Diff,Sign,Difft,Signt,F).
propagate_expr_(=,X,Expr1,_,t,Expr,S,[X|Diff],Sign,Difft,t,F) :- !,
    propagate_expr(Expr1,Expr,S,Diff,Sign,Difft,_,F).
propagate_expr_(=,_/SignX,Expr1,_,SignY,Expr,S,Diff,Sign,Difft,Signt,changed) :-
    vals_mult(SignX,SignY,V3),
    vals_sum(V3,S,NS),
    propagate_expr(Expr1,Expr,NS,Diff,Sign,Difft,Signt,_).
propagate_expr_(>,X,Expr1,_,_,[],S,[X|Expr1],S,[X|Expr1],_,_) :- !.
propagate_expr_(>,X/SignX,Expr1,_,_,[Y/SignY|Expr],S,Diff,Sign,Difft,Signt,F) :-
    compare(Order,X,Y),
    propagate_expr_(Order,X/SignX,Expr1,Y,SignY,Expr,S,Diff,Sign,Difft,Signt,F).

vals_mult(0,_,0).
vals_mult(+,X,X).
vals_mult(-,X,Y):-
    vals_mult_minus(X,Y).
vals_mult(t,X,Y):-
    vals_mult_top(X,Y).

vals_mult_top(0,0).
vals_mult_top(+,t).
vals_mult_top(-,t).
vals_mult_top(t,t).

vals_mult_minus(0,0).
vals_mult_minus(+,-).
vals_mult_minus(-,+).
vals_mult_minus(t,t).

vals_sum(0,X,X).
vals_sum(+,X,Y):-
    vals_sum_plus(X,Y).
vals_sum(-,X,Y):-
    vals_sum_minus(X,Y).
vals_sum(t,_,t).

vals_sum_plus(0,+).
vals_sum_plus(+,+).
vals_sum_plus(-,t).
vals_sum_plus(t,t).

vals_sum_minus(0,-).
vals_sum_minus(+,t).
vals_sum_minus(-,-).
vals_sum_minus(t,t).


%------------------------------------------------------------------------%
% check_propagate(+,+,+,-,+,-,-)
% check_propagate(Chg,Op,SumSign,Expr0,EqIn,AEqIn,S1,NAEqIn,S2,S,F)
%------------------------------------------------------------------------%
% Let EqIn = eq(Op,Sign,Expr). Expr0 is the result of propagating
% S1 to Expr. Chg=changed if the exprestion has been touched. SumSign is
% the sign of the coeficient resulting from substitution the info in S1
% in Expr. 
% - If Chg = unchanged, the equation has not been touched and we continue
% - Elseif Op in {eq?,eqx,leq,less}, the:
%        * If Expr0=[], we continue (thus EqIn has been eliminated).
%        * Otherwise,  NAEqIn = [NewEqIn|AEqIn] where NewEqIn is the 
%          result of normalizing eq(Op,Sign0,Expr0)
% - Else
%    * If Expr=[]:
%         # If the resulting constraint eq(Op,SignSumSign) is consistent
%           
%------------------------------------------------------------------------%

check_propagate(unchanged,_,_,_,EqIn,AEqIn,S1,NAEqIn,S2,S,F):- !,
    NAEqIn = [EqIn|NAEqIn0],
    lsign_propagate(AEqIn,S1,NAEqIn0,S2,S,F).
check_propagate(_,Op,SumSign,Expr0,EqIn,AEqIn,S1,NAEqIn,S2,S,F):- 
    Op @< 'eq?',!,
    check_eq(Expr0,SumSign,EqIn,AEqIn,S1,NAEqIn,S2,S,F).
check_propagate(_,_,SumSign,Expr0,EqIn,AEqIn,S1,NAEqIn,S2,S,F):- 
    check_ineq(Expr0,SumSign,EqIn,AEqIn,S1,NAEqIn,S2,S,F).

check_ineq([],_,_,AEqIn,S1,NAEqIn,S2,S,F):- !,
    lsign_propagate(AEqIn,S1,NAEqIn,S2,S,F).
check_ineq(Expr0,SumSign,eq(Op,Sign,_),AEqIn,S1,NAEqIn,S2,S,F):-
    signed_new_sign(SumSign,Sign,Sign0),
    lsign_normalize(Op,Sign0,Expr0,NewEqIn),
    NAEqIn = [NewEqIn|NAEqIn0],
    lsign_propagate(AEqIn,S1,NAEqIn0,S2,S,F).

check_eq([],SumSign,EqIn,AEqIn,S1,NAEqIn,S2,S,F):-
    EqIn = eq(Op,Sign,Expr),
    lsign_consistent(Op,Sign,SumSign),!,
    ( lsign_sign(Op,Sign,Expr,_,_) ->
        NAEqIn = [EqIn|NAEqIn0]
    ;   NAEqIn = NAEqIn0
    ),
    lsign_propagate(AEqIn,S1,NAEqIn0,S2,S,F).
check_eq([],_,_,_,_,_,_,[],incons):- !.
check_eq(Expr0,SumSign,eq(Op,Sign,_),AEqIn,S1,NAEqIn,S2,S,F):- 
    signed_new_sign(SumSign,Sign,Sign0),
    lsign_normalize(Op,Sign0,Expr0,NewEqIn),
    NewEqIn = eq(Op,NewSign,NewExpr),
    NAEqIn = [NewEqIn|NAEqIn0],
    ( lsign_sign(Op,NewSign,NewExpr,Y,SignY) ->
        lsign_merge_signed([Y/SignY],S2,S22,F1),
        ( F1 = cons ->
            insert(S1,Y/SignY,S11),
            lsign_propagate(AEqIn,S11,NAEqIn0,S22,S,F)
        ; F = uncons,
          S = []
        )           
    ;  lsign_propagate(AEqIn,S1,NAEqIn0,S2,S,F)
    ),!.

%------------------------------------------------------------------------%
% lsign_consistent(+,+,+)
% lsign_consistent(Op,Sign,SumSign)
%------------------------------------------------------------------------%
% Satisfied if the constraint Sign Op SumSign is possibly satisfiable.
% This is true if:
%      - Op in {eq?,eqx,leq,less}
%      - If Op in {eq,eq+}:
%                                +     -      0       t     (SumSign)
%                             ---------------------------
%                            + | true  false  false  true
%                            0 | false false  true   true
%                            t | true  true   true   true
%                           (Sign)
% Note that Sign cannot be '-' due to normalization.
%------------------------------------------------------------------------%

lsign_consistent(eq,Sign,SumSign):-
    compatible_signs(Sign,SumSign).
lsign_consistent('eq+',Sign,SumSign):-
    compatible_signs(Sign,SumSign).
lsign_consistent('eq?',_,_).
lsign_consistent(eqx,_,_).
lsign_consistent(leq,_,_).
lsign_consistent(less,_,_).

compatible_signs(+,X):-
    compatible_plus(X).
compatible_signs(0,X):-
    compatible_zero(X).
compatible_signs(t,_).

compatible_plus(t).
compatible_plus(+).

compatible_zero(t).
compatible_zero(0).

%------------------------------------------------------------------------%
% signed_new_sign(+,+,-)
% signed_new_sign(SumSign,Sign,NewSign)
%------------------------------------------------------------------------%
% Sign is the Lhs sign of a constraint. SumSign is the sign of the 
% possible coefficient in the Rhs. This predicate computes the NewSign 
% of the constraint which would result from negating SumSign and add it
% to Sign, this is computed as follows:
%                                +   -   0   t  (SumSign)
%                            ---------------------------
%                            + | t   +   +   t
%                            - | -   t   -   t
%                            0 | -   +   0   t
%                            t | t   t   t   t
%                          Sign
%------------------------------------------------------------------------%

signed_new_sign(0,Sign,Sign).
signed_new_sign(+,Sign,NewSign):-
    signed_new_sign_plus(Sign,NewSign).
signed_new_sign(-,Sign,NewSign):-
    signed_new_sign_minus(Sign,NewSign).
signed_new_sign(t,_,t).

signed_new_sign_plus(+,t).
signed_new_sign_plus(-,-).
signed_new_sign_plus(0,-).
signed_new_sign_plus(t,t).

signed_new_sign_minus(+,+).
signed_new_sign_minus(-,t).
signed_new_sign_minus(0,+).
signed_new_sign_minus(t,t).

%------------------------------------------------------------------------%
% lsign_propagate_non(+,+,-,-,?,-,-)
% lsign_propagate_non(Non,LS,NNon,AEqIn,Tail,FinalLS,Flag)
%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

lsign_propagate_non([],S,[],Tail,Tail,S,_).
lsign_propagate_non([NL|Non],S1,NNon,AEqIn,Tail,S,F):-
    NL = eq(Op,X,Y),
    propagate_non(Y,X,Op,NNon,Tail1,AEqIn,Tail2,S1,S2,F1),
    ( F1 = cons ->
        lsign_propagate_non(Non,S2,Tail1,Tail2,Tail,S,F)
    ; S = [],
      F = incons
    ).

propagate_non(Y*Z,X,Op,NNon,Tail1,AEqIn,Tail2,S1,S,F):-
    sort([Y,Z],Vars),
    lsign_project_signed(Vars,S1,PS),
    propagate_non_mult(PS,Y*Z,X,Op,NNon,Tail1,AEqIn,Tail2,S1,S,F).
propagate_non(abs(Y),X,Op,NNon,Tail1,AEqIn,Tail2,S1,S,F):-
    lsign_project_signed([X],S1,XS),
    ( XS = [_/'-'] ->
        F = incons,
        S = []
    ; lsign_project_signed([Y],S1,YS),
      propagate_non_abs(YS,Y,X,Op,NNon,Tail1,AEqIn,Tail2,S1,S,F)
    ).

propagate_non_abs([],Y,X,Op,[eq(Op,X,abs(Y))|Tail1],Tail1,Tail2,Tail2,S,S,_).
propagate_non_abs([_/SignY],_,X,_,NNon,Tail1,AEqIn,Tail2,S1,S,F):-
    ( SignY = 0 ->
        SignX = 0
    ;   SignX = '+'
    ),
    lsign_merge_signed(S1,[X/SignX],S,F1),
    ( F1 = cons ->
        NNon = Tail1,
        AEqIn = [eq(eq,SignX,[X/'+'])|Tail2]
    ; F = incons,
      S = []
    ).


propagate_non_mult([],Y,X,Op,NNon,Tail1,AEqIn,Tail2,S1,S,_):- 
    NNon = [eq(Op,X,Y)|Tail1],
    AEqIn = Tail2,
    S = S1.
propagate_non_mult([_/VA,_/VB],_,X,_,NNon,Tail1,AEqIn,Tail2,S1,S,F):- !,
    vals_mult(VA,VB,SignX),
    lsign_merge_signed(S1,[X/SignX],S,F1),
    ( F1 = cons ->
        NNon = Tail1,
        lsign_normalize(eq,SignX,[X/'+'],Eq),
        AEqIn = [Eq|Tail2]
    ; F = incons,
      S = []
    ).
propagate_non_mult([_/t],Y,X,Op,NNon,Tail1,AEqIn,Tail2,S1,S,_):-  !,
    NNon = [eq(Op,X,Y)|Tail1],
    AEqIn = Tail2,
    S = S1.
propagate_non_mult([_/0],_,X,_,NNon,Tail1,AEqIn,Tail2,S1,S,F):- !,
    lsign_merge_signed(S1,[X/0],S,F1),
    ( F1 = cons ->
        NNon = Tail1,
        AEqIn = [eq(eq,0,[X/'+'])|Tail2]
    ; F = incons,
      S = []
    ).
propagate_non_mult([A/VA],Y*Z,X,_,Tail1,Tail1,AEqIn,Tail2,S1,S,F):- 
    ( A == Y ->
        B = Z
    ;  B = Y
    ),
    sort([B/VA,X/'-'],Expr),
    lsign_normalize(eq,0,Expr,Eq),
    lsign_add_linear(Eq,a(S1,[],[]),Succ),
    ( Succ = '$bottom' ->
        F = incons,
        S = []
    ; Succ = a(S,[Eq1],[]),
      AEqIn = [Eq1|Tail2]
    ).
      
%------------------------------------------------------------------------%
% lsign_lub_sign(+,+,-)
% lsign_lub_sign(X,Y,Lub)
%------------------------------------------------------------------------%
% Obtains Lub from the following table:
%                   |  0   +   -   t   
%              ----------------------
%                 0 |  0   t   t   t
%                 + |  t   +   t   t
%                 - |  t   t   -   t
%                 t |  t   t   t   t
%------------------------------------------------------------------------%

lsign_lub_sign(Sign,Sign,Sign):- !.
lsign_lub_sign(_,_,t).

%------------------------------------------------------------------------%
%------------------------------------------------------------------------%

lsign_fixpoint_unique([],Vars,Data,ACons,Vars,Data,ACons):- !.
lsign_fixpoint_unique(Unique0,Vars0,_,ACons0,Vars,Data,ACons):-
    split_from_list_vars(ACons0,Unique0,ACons1),
    ord_subtract(Vars0,Unique0,Vars1),
    lsign_get_data(ACons1,Vars1,[],Data1,ACons2,_),
    lsign_get_unique_vars(Data1,Unique1),
    lsign_fixpoint_unique(Unique1,Vars1,Data1,ACons2,Vars,Data,ACons).

%------------------------------------------------------------------------%
% lsign_get_data(+,+,+,-,-,-)
% lsign_get_data(ACons,Vars,Data0,Data,ACons1,Subset)
%------------------------------------------------------------------------%
%  
%------------------------------------------------------------------------%

lsign_get_data([],_,Data,Data,[],[]).
lsign_get_data([Eq|ACons],Vars,Data0,Data,ACons1,Subset):-
    Eq = eq(Op,_,Expr),
    lsign_get_data0(Expr,Vars,Op,Data0,Data1,F),
    ( F = untouched ->
        ACons1 = ACons2,
        Subset = [Eq|Tail1]
    ;   ACons1 = [Eq|ACons2],
        Subset = Tail1
    ),
    lsign_get_data(ACons,Vars,Data1,Data,ACons2,Tail1).

lsign_get_data0([],_,_,Data,Data,_) :- !.
lsign_get_data0(_,[],_,Data,Data,_) :- !.
lsign_get_data0([X/Sign|Expr],[Y|Vars],Op,Data0,Data,F) :-
    compare(Order,X,Y),
    lsign_get_data1(Order,X/Sign,Expr,Y,Vars,Op,Data0,Data,F).

lsign_get_data1(<,_,[],_,_,_,Data,Data,_):- !.
lsign_get_data1(<,_,[X/Sign|Expr],Y,Vars,Op,Data0,Data,F):-
    compare(Order,X,Y),
    lsign_get_data1(Order,X/Sign,Expr,Y,Vars,Op,Data0,Data,F).
lsign_get_data1(=,X/Sign,Expr,_,Vars,Op,Data0,Data,changed):-
    lsign_data_var(Data0,X,Sign,Op,Data,Tail,RestData),
    lsign_get_data0(Expr,Vars,Op,RestData,Tail,_).
lsign_get_data1(>,_,_,_,[],_,Data,Data,_):- !.
lsign_get_data1(>,X/Sign,Expr,_,[Y|Vars],Op,Data0,Data,F) :-
    compare(Order,X,Y),
    lsign_get_data1(Order,X/Sign,Expr,Y,Vars,Op,Data0,Data,F).

%------------------------------------------------------------------------%
% lsign_data_var(+,+,+,+,-,-,-)
% lsign_data_var(Data,X,NewSign,NewOp,NewData,Tail,RestData)
%------------------------------------------------------------------------%
% Updates Data for X with the information of NewSign and NewOp.
% NewData = [v(X1,Op1,Eq1,NS1),....,v(Xn,Opn,Eqn,NSn),v(X,Op,Eq,NS)|Tail] 
% such that X1,...,Xn < X.
% RestData = [v(Xn+1,Opn+1,Eqn+1,NS1),....]
%------------------------------------------------------------------------%

lsign_data_var([],X,NewSign,NewOp,[ElX|Tail],Tail,[]):-
    lsign_get_var_data(NewSign,0,Sign,NewOp,0,Op),
    ElX = v(X,Op,1,Sign).
lsign_data_var([El|Data0],X,Sign,Op,Data,Tail,RestData):-
    El = v(Y,_,_,_),
    compare(Order,Y,X),
    lsign_data_var0(Order,El,Data0,X,Sign,Op,Data,Tail,RestData).

lsign_data_var0(<,El,[],X,NewSign,NewOp,[El,ElX|Tail],Tail,[]):- !,
    lsign_get_var_data(NewSign,0,Sign,NewOp,0,Op),
    ElX = v(X,Op,1,Sign).
lsign_data_var0(<,El,[El0|Data0],X,Sign,Op,[El|Data],Tail,RestData):-
    El0 = v(Y,_,_,_),
    compare(Order,Y,X),
    lsign_data_var0(Order,El0,Data0,X,Sign,Op,Data,Tail,RestData).
lsign_data_var0(=,v(_,OldOp,OldEq,OldSign),Data0,X,NewSign,NewOp,
                                        [ElX|Tail],Tail,Data0):-
    lsign_get_var_data(NewSign,OldSign,Sign,NewOp,OldOp,Op),
    Eq is OldEq + 1,
    ElX = v(X,Op,Eq,Sign).
lsign_data_var0(>,El,Data0,X,NewSign,NewOp,[ElX|Tail],Tail,[El|Data0]):-
    lsign_get_var_data(NewSign,0,Sign,NewOp,0,Op),
    ElX = v(X,Op,1,Sign).

%------------------------------------------------------------------------%
% lsign_get_var_data(+,+,-,+,+,-)
% lsign_get_var_data(NewSign,OldSign,Sign,NewOp,OldOp,Op)
%------------------------------------------------------------------------%
% If NewSign = t, Sign = OldSign, Op = OldOp.
% Otherwise, Sign = OldSign + 1, and:
%            - If NewOp = eq or eq+,  Op = OldOp +1
%            - Otherwise,  Op = OldOp
%------------------------------------------------------------------------%

lsign_get_var_data('+',OldSign,Sign,NewOp,OldOp,Op):-
    Sign is OldSign+1,
    lsign_get_var_data0(NewOp,OldOp,Op).
lsign_get_var_data('-',OldSign,Sign,NewOp,OldOp,Op):-
    Sign is OldSign+1,
    lsign_get_var_data0(NewOp,OldOp,Op).
lsign_get_var_data(t,Sign,Sign,_,Op,Op).

lsign_get_var_data0(eq,OldOp,Op):- 
    Op is OldOp +1.
lsign_get_var_data0('eq+',OldOp,Op):- 
    Op is OldOp +1.
lsign_get_var_data0('eq?',Op,Op).
lsign_get_var_data0(eqx,Op,Op).
lsign_get_var_data0(leq,Op,Op).
lsign_get_var_data0(less,Op,Op).

%------------------------------------------------------------------------%
% lsign_get_unique_vars(+,-)
% lsign_get_unique_vars(Data,UniqueVars)
%------------------------------------------------------------------------%
% UniqueVars = { X | v(X,_,1,_) in Data}
%------------------------------------------------------------------------%

lsign_get_unique_vars([],[]).
lsign_get_unique_vars([v(X,_,1,_)|Data],UniqueVars):-  !,
    UniqueVars = [X|Rest],
    lsign_get_unique_vars(Data,Rest).
lsign_get_unique_vars([_|Data],UniqueVars):- 
    lsign_get_unique_vars(Data,UniqueVars).

%------------------------------------------------------------------------%
% lsign_get_best_var(+,+,-)
% lsign_get_best_var(Data,BestVar,Var).
%------------------------------------------------------------------------%
% This predicate looks for a variable X such that v(X,OpX,_,NSX) in Data
% with OpX > 0, and there is no other variable Y such that v(Y,OpY,_,NSY)
% with OpY > 0 and NSY < NSX. If it exists Var = X/NSX.
%------------------------------------------------------------------------%

lsign_get_best_var([],X,X).
lsign_get_best_var([v(X,Op,_,Sign)|Data],BestVar,Var):-
    lsign_get_best_var0(Op,X,Sign,BestVar,TB),
    lsign_get_best_var(Data,TB,Var).
    
lsign_get_best_var0(0,_,_,BestVar,TB):- !,
    TB = BestVar.
lsign_get_best_var0(_,X,Sign,[],TB):- !,
    TB = X/Sign.
lsign_get_best_var0(_,_,Sign,Y/SignY,TB):- 
    SignY < Sign,!,
    TB = Y/SignY.
lsign_get_best_var0(_,X,Sign,_,X/Sign).


% ------------------------------------------------------------------------%
%                  LSign DOMAIN
%------------------------------------------------------------------------%
% An abstract constraint Abs is a 3-tuple a(S,AEqIn,Non) where :
%     * S is the set of ground variables.The elements of S are of the
%       form X/Sign where X is a variable and Sign is in {+,-,0,t}
%     * AEqIn represents the set of linear equations and inequations. The
%       elements of AEqIn are of teh form eq(Op,Sign,Expr), where:
%       - Op represents a constraint predicate symbol for equation or
%         inequation, thus it is an element of {eq,eq+,eq?,eqx,leq,less}.
%       - Sign represents the sign of a particular coefficient. It is
%         an element of {+,-,0,t} (positive, negative, zero, top). 
%       - Expr is an ordered list of elements of the form X/Sign, where
%         X is a variable and Sign is in {+,-,t}. Note that if the 
%         sign (i.e., X's coefficient) is zero X is eliminated from Expr.
%     * Non respresents the set of possibly non-linear equations. The
%       elements of Non are of the form eq(Op,X,NonL). It abstracts the
%       non linear equation X = NonL, where X is a variable and NonL is
%       one of the simple non linear functions: min(Y,Z), max(Y,Z), abs(Y)
%       sin(Y), cos(Y), arcsin(Y), arccos(Y) , pow(Y,Z), Y*Z. A 
%       non-linear constraint AEq is kept in Non until either AEq becomes 
%       linear, or the abstraction is projected over a set of variables
%       which does not include all variables in AEq (i.e., some variables
%       of AEq are projected out). If so, AEq is safely abstracted as a 
%       linear equation (with some loss of information).
%------------------------------------------------------------------------%
%                     ABOUT THE SOLVED FORM
%------------------------------------------------------------------------%
% Abs=a(S,AEqIn,Non) is kept in some kind of solved form:
%   * for each X/Sign in S, s.t. Sign in {+,-,0} (i.e. Sign \== t), the 
%     groundness of X is propagated to all constraints in AEqIn and Non.
%     This can possibly ground other variables, which in turn will be 
%     added to S and propagated. While doing this, inconsistencies can be 
%     detected, yielding '$bottom'
%   * for each X/t in S, the groundness of X is only propagated to 
%     the rest of constraints in such a way that if later the sign of 
%     X is inferred, no information will be lost. Consider for example
%     eq(eq,+, [X/+, Y/+]) (i.e. + = X + Y). If we propagate the 't' of
%     X, we will obtain the constraint eq(eq,t,[Y/+]), thsu we know that
%     Y is ground but we do not know its sign. On the other hand 
%     if we later infer that X is '-', we could have obtained
%     eq(eq,+,[Y/+]), thus knowing that Y is positive. This means that the         
%     groundness of X is not propagated to the constraints in Non, and
%     only propagated to a constraint eq(Op,Sign,Expr) in AEqIn, if Sign
%     is 't'. 
%   * It is possible that AEqIn contains groundness information which is 
%     not in S. For example, if we have in AEqIn both eq(eq,+,[X/+,Y/+]) 
%     and eq(eq,+,[X/-,Y/+]), we can infer that Y is positive and X is 
%     ground (unknown sign). However, this is not detected and it will 
%     not be known until the abstraction is projected over either X or Y. 
%------------------------------------------------------------------------%
%                 A PRIORI CONDITION
%------------------------------------------------------------------------%
% The translation of an abstract constraint Abs = a(S,EqIn,Non) into
% an element (Pos,Neg,Imp) of the abstract domain GI is as follows:
%
%   * To compute the groundness, we will first project Abs over each 
%     variable X s.t. X/_ not in S. Let NewS be the result of adding all to
%     S the groundness information obtained during the projections.
%     Then the groundness information in Pos  is { ground(X)| X/_ in NewS}
%   * Once we have projected Abs over each X, s.t. X/_ not in S, computing
%     the groundness information in Neg is simple: those for which the
%     projection is empty, i.e. { \neg ground(X)| project(Abs,[X]) = []}
%   * To compute the independence, we will first propagate the information
%     in NewS to AEqIn, and Non. To simplify things all constraints in Non
%     are transformed into linear constraints and integrated in AEqIn,
%     obtaining AEqIn0. This can cause some loss of accuracy but (bu now) 
%     is simpler. So, we propagate NewS to AEqIn0. This time, ground variables 
%     are propagated to all constraints in AEqIn0, even if their sign in NewS 
%     is 't'. This is just to improve independence since no more groundness 
%     can be inferred (and thus no fixpoint is required) and no inconsistency 
%     can be detected during the propagation. We obtain NAEqIn.
%   * Once propagation has been performed,  \neg indep(X,Y) in Neg is 
%     obtained as the closure under transitivity of the following set:
%     {\neg indep(X,Y) | \neg ground(X) in Neg, and exists 
%                       eq(Op,Sign,[X/_,Y/_]) in NAEqIn} \cup
%     {\neg indep(X,Y) | \neg ground(X), \neg ground(Y) in Neg, and exists 
%                        exists eq(Op,Sign,Expr) in NAEqIn, Op in {eq,eq+}, 
%                        X/SignX,Y/SignY in Expr, SignX \== t, SignY \== t}
%   * For computing indep(X,Y), and the implications indep -> indep, we 
%     transform the equations into set sharing by computing the closure of
%        { [X] | not exists eq(Op,Sign,Expr) in NAEqIn, X/_ in Expr} \cup
%        { Vars | Vars = vars(Expr), forall eq(Op,Sign,Expr) in NAEqIn}
%   * Implications indep(X,Y) -> ground(Z) can only be obtained if:
%            * X and Y never appear toghether, 
%            * the coupled variables of X and Y in the abstractions
%              with Op in {eq,eq+} share exactly one variable Z, where the 
%              coupled variables of X are those which appear in at least 
%              one equation with X. Note that if no variable is shared,
%              X and Y are independent (already captured before).
%            * the coupled variables of X and Y in the rest of abstractions
%              do not share any variable.
%   * Computing ground -> ground and ground -> indep cannot be done by 
%     using some kind of set sharing. It has to be done by grounding the
%     variables and see what happens in the Abs. Furthermore, let X and Y
%     be the set of vars. Let GX and GY be the set of vars which Abs knows
%     become ground when X and Y become ground, respectively. Then 
%     GX \cup GY es un subconjunto de be GXY, where GXY is the set of vars
%     which Abs knows become ground when both X and Y become gound. As a 
%     result we have to consider the groundness of each set of the powerset
%     of Vars (and be careful when adding information in order to avoid
%      adding ground([X,Y]) -> ground(Z), when ground(X) -> ground(Z), was 
%     already there.
%------------------------------------------------------------------------%

lsign_global_info(Abs,HvFv,Pos,Neg,Imp):-
    Abs = a(S,AEqIn,Non),
    collect_vars_freeness(S,Gv),
    ord_subtract(HvFv,Gv,PossibleNGVars),
    lsign_project_each(PossibleNGVars,Abs,HvFv,S,NGVars,NewS),
    collect_vars_freeness(NewS,GVars),
    ground_conds(GVars,Pos,Pos1),
    not_ground_conds(NGVars,Neg,Neg1),
    length(PossibleNGVars,N),
    ( N < 2 ->
        Pos1 = [],
        Neg1 = [],
        Imp =[]
    ;  lsign_project_non(Non,[],_,AEqIn0),
       append(AEqIn0,AEqIn,AEqIn1),
       lsign_propagate_total(AEqIn1,NewS,NAEqIn),
       lsign_get_dependent(NAEqIn,NGVars,[],Dep),
       list_to_list_of_lists(NGVars,Singletons),
       transitive_closure_lists(Dep,Singletons,ClosureDep),
       lsign_not_indep(ClosureDep,Neg1,[]),
       lsign_go_to_set_sharing(NAEqIn,NGVars,Sh,ShEq,ShEqx),
       asubs_to_dep(Sh,ShDep,NewPossibleNGVars),
       dep_to_indep(NewPossibleNGVars,ShDep,Pos1),
       indep_imply_indep(NewPossibleNGVars,NewPossibleNGVars,ShDep,Imp,Imp1),
       lsign_indep_imply_ground(NewPossibleNGVars,ShEq,ShEqx,Imp1,Imp2),
       ord_subtract(NewPossibleNGVars,NGVars,PossibleGVars),
       powerset(PossibleGVars,Powerset_u),
       sort(Powerset_u,Powerset),
       lsign_get_ground_implies(Powerset,NAEqIn,[],Imp2)
    ).

%------------------------------------------------------------------------
%------------------------------------------------------------------------

lsign_project_each([],_,_,NewS,[],NewS).
lsign_project_each([X|PossibleNonGround],Abs,HvFv,S0,NonGround,NewS):-
    lsign_project(sg_not_provided,[X],HvFv,Abs,Proj), % TODO: add Sg
    Proj = a(S,AEqIn,Non), % What to do if Proj = '$bottom'?
    ( S = [], AEqIn = [], Non = [] ->
        NonGround = [X|NonGround0]
    ;   NonGround0 = NonGround
    ),
    lsign_merge_signed(S0,S,S1,_),
    lsign_project_each(PossibleNonGround,Abs,HvFv,S1,NonGround0,NewS).
    
%------------------------------------------------------------------------
%------------------------------------------------------------------------

lsign_propagate_total([],_,[]).
lsign_propagate_total([eq(Op,Sign,Expr)|AEqIn],NewS,NAEqIn):-
    propagate_expr(Expr,NewS,0,_,SumSign,Expr0,SumSignt,_),
    ( SumSignt = 0 ->
        SumSign0 = t
    ;   SumSign0 = SumSign
    ),
    ( Expr0 = [] ->
      NAEqIn = NAEqIn0
    ; signed_new_sign(SumSign0,Sign,Sign0),
      lsign_normalize(Op,Sign0,Expr0,NewEqIn),
      NAEqIn = [NewEqIn|NAEqIn0]
    ),
    lsign_propagate_total(AEqIn,NewS,NAEqIn0).

%------------------------------------------------------------------------
%------------------------------------------------------------------------

lsign_get_dependent([eq(Op,_,Expr)|NEqIn],NGVars,Dep0,Dep):-
    Op @=< 'eq+',!,
    lsign_get_dependent0(Expr,NGVars,Dep0,Dep1),
    lsign_get_dependent(NEqIn,NGVars,Dep1,Dep).
lsign_get_dependent(_,_,Dep,Dep).

lsign_get_dependent0([X/_,Y/_],NGVars,Dep0,Dep1):-
    ord_intersect([X,Y],NGVars),!,
    Dep0 = [[X,Y]|Dep1].
lsign_get_dependent0(Expr,NGVars,Dep0,Dep1):-
    look_for_first_nonground(Expr,NGVars,Expr0,First),
    more_nonground(Expr0,NGVars,First,Dep0,Dep1).

look_for_first_nonground([],_,[],[]).
look_for_first_nonground([X/Sign|Expr],NGVars,Expr0,First):-
    Sign \== t,
    ord_member(X,NGVars),!,
    First = [X],
    Expr0 = Expr.
look_for_first_nonground([_|Expr],NGVars,Expr0,First):-
    look_for_first_nonground(Expr,NGVars,Expr0,First).

more_nonground([],_,_,Dep,Dep).
more_nonground([X/Sign|Expr0],NGVars,First,Dep0,Dep):-
    Sign \== t,
    ord_member(X,NGVars),!,
    First = [Y],
    Dep0 = [[Y,X]|Dep1],
    more_nonground(Expr0,NGVars,First,Dep1,Dep).

%------------------------------------------------------------------------
% lsign_not_indep(+,-,?)
% lsign_not_indep(ClosureDep,Neg1,Neg)
%------------------------------------------------------------------------

lsign_not_indep([],Neg,Neg).
lsign_not_indep([Xs|ClosureDep],Neg1,Neg):-
    lsign_not_indep0(Xs,Neg1,Neg2),
    lsign_not_indep(ClosureDep,Neg2,Neg).

lsign_not_indep0([],Neg,Neg).
lsign_not_indep0([X|Xs],Neg1,Neg):-
    not_indep_conds_one_var(Xs,X,Neg1,Neg2),
    lsign_not_indep0(Xs,Neg2,Neg).

%------------------------------------------------------------------------
% lsign_go_to_set_sharing(+,+,+,-,-,-)
% lsign_go_to_set_sharing(AEqIn,FreeVars,Sh,ShEq,ShEqx)
%------------------------------------------------------------------------

lsign_go_to_set_sharing(AEqIn,FreeVars,Sh,ShEq,ShEqx):-
    lsign_go_to_set_sharing0(AEqIn,FreeVars,[],Sh,ShEq_u,ShEqx_u),
    sort(ShEq_u,ShEq),
    sort(ShEqx_u,ShEqx).

lsign_go_to_set_sharing0([],FreeVars,Sh0,Sh,ShEq,[]):-
    list_to_list_of_lists(FreeVars,ShEq),
    merge(Sh0,ShEq,Sh).
lsign_go_to_set_sharing0([eq(Op,_,Expr)|NAEqIn],FreeVars,Sh0,Sh,ShEq,ShEqx):-
    collect_vars_freeness(Expr,Vars),
    ord_split_lists_from_list(Vars,Sh0,Intersect,Disjunct),
    closure_under_union([Vars|Intersect],Sh1),
    merge(Sh1,Disjunct,Sh2),
    ord_subtract(FreeVars,Vars,FreeVars0),
    ( Op @< 'eq?' ->
        ShEq = [Vars|ShEq0],
        ShEqx = ShEqx0
    ;  ShEq = ShEq0,
       ShEqx = [Vars|ShEqx0]
    ),
    lsign_go_to_set_sharing0(NAEqIn,FreeVars0,Sh2,Sh,ShEq0,ShEqx0).

%------------------------------------------------------------------------
% lsign_indep_imply_ground(+,+,+,-,?)
% lsign_indep_imply_ground(Vars,ShEq,ShEqx,Imp1,Imp)
%------------------------------------------------------------------------

lsign_indep_imply_ground([],_,_,Imp,Imp).
lsign_indep_imply_ground([X|Vars],ShEq,ShEqx,Imp1,Imp):-
    ord_split_lists(ShEq,X,IntEq,DisjEq),
    merge_list_of_lists(IntEq,DepVarsEq),
    ord_split_lists(ShEqx,X,IntEqx,DisjEqx),
    merge_list_of_lists(IntEqx,DepVarsEqx),
    ord_subtract(Vars,DepVarsEq,PosIndep0),
    ord_subtract(PosIndep0,DepVarsEqx,PosIndep),
    lsign_indep_imply_ground0(PosIndep,X,DepVarsEq,DisjEq,DepVarsEqx,DisjEqx,Imp1,Imp2),
    lsign_indep_imply_ground(Vars,ShEq,ShEqx,Imp2,Imp).
    
lsign_indep_imply_ground0([],_,_,_,_,_,Imp,Imp).
lsign_indep_imply_ground0([Y|PosIndep],X,DepVarsEq,DisjEq,DepVarsEqx,DisjEqx,Imp1,Imp):-
    ord_split_lists(DisjEqx,Y,IntEqx,_),
    merge_list_of_lists(IntEqx,DepVarsEqxY),
    ord_intersection(DepVarsEqx,DepVarsEqxY,[]),
    ord_split_lists(DisjEq,Y,IntEq,_),
    merge_list_of_lists(IntEq,DepVarsEqY),
    ord_intersection(DepVarsEq,DepVarsEqY,[Z]),!,
    Imp1 = [(indep(X,Y) -> ground(Z))|Imp2],
    lsign_indep_imply_ground0(PosIndep,X,DepVarsEq,DisjEq,DepVarsEqx,DisjEqx,Imp2,Imp).
lsign_indep_imply_ground0([_|PosIndep],X,DepVarsEq,DisjEq,DepVarsEqx,DisjEqx,Imp1,Imp):-
    lsign_indep_imply_ground0(PosIndep,X,DepVarsEq,DisjEq,DepVarsEqx,DisjEqx,Imp1,Imp).
    

lsign_get_ground_implies([],_,P,P).
lsign_get_ground_implies([[X]|Powerset],AEqIn,Imp0,Imp):-
    lsign_propagate_total(AEqIn,[X/t],NAEqIn),
    lsign_obtain_ground_indep(NAEqIn,GroundIndep),
    lsign_eliminate_supersets(GroundIndep,Imp0,ground(X),Imp1),
    lsign_get_ground_implies0(Powerset,NAEqIn,AEqIn,Imp1,Imp).

lsign_get_ground_implies0([],_,_,Imp,Imp).
lsign_get_ground_implies0([[Y]|Powerset],_,OrigAEqIn,Imp0,Imp):- !,
    lsign_propagate_total(OrigAEqIn,[Y/t],NAEqIn),
    lsign_obtain_ground_indep(NAEqIn,GroundIndep),
    lsign_eliminate_supersets(GroundIndep,Imp0,ground(Y),Imp1),
    lsign_get_ground_implies0(Powerset,NAEqIn,OrigAEqIn,Imp1,Imp).
lsign_get_ground_implies0([Xs|Powerset],NAEqIn,OrigAEqIn,Imp0,Imp):-
    create_values(Xs,S,t),
    lsign_propagate_total(NAEqIn,S,NAEqIn0),
    lsign_obtain_ground_indep(NAEqIn0,GroundIndep),
    lsign_eliminate_supersets(GroundIndep,Imp0,ground(Xs),Imp1),
    lsign_get_ground_implies0(Powerset,NAEqIn,OrigAEqIn,Imp1,Imp).


lsign_obtain_ground_indep([],[]):- !.
lsign_obtain_ground_indep(AEqIn,GroundIndep):-
    get_signed(AEqIn,[],Union,_),
    collect_vars_freeness(Union,Ground),
    ground_conds(Ground,GroundIndep,Tail),
    lsign_go_to_set_sharing(AEqIn,[],Sh,_,_),
    asubs_to_indep(Sh,Tail).

lsign_eliminate_supersets([],Imp,_,Imp).
lsign_eliminate_supersets([Consec|GroundIndep],Imp0,Antecedent,Imp):-
    superset_antecedents(Imp0,Antecedent,Consec,Imp1),
    lsign_eliminate_supersets(GroundIndep,Imp1,Antecedent,Imp).

superset_antecedents([],Ant,Consec,Imp):-
    Imp = [(Ant -> Consec)].
superset_antecedents([(Ant0 -> Consec0)|Imp0],Ant,Consec,Imp):-
    Consec0 == Consec,!,
    ( lsign_super(Ant0,Ant,SmallAnt) ->
        Imp = [(SmallAnt -> Consec)|Imp0]
    ;   superset_antecedents(Imp0,Ant,Consec,Imp)
    ).
superset_antecedents([X|Imp0],Ant,Consec,[X|Imp]):-
    superset_antecedents(Imp0,Ant,Consec,Imp).

lsign_super(ground(X),ground(Y),SmallAnt):-
    varset(X,VX),
    varset(Y,VY),
    ord_union_diff(VX,VY,Union,YminusX),
    ( YminusX = [] ->
        SmallAnt = ground(Y)
    ; Union == VY,
      SmallAnt = ground(X)
    ).
lsign_super(indep(X),indep(Y),SmallAnt):-
    varset(X,VX),
    varset(Y,VY),
    ord_union_diff(VX,VY,Union,YminusX),
    ( YminusX = [] ->
        SmallAnt = indep(Y)
    ; Union == VY,
      SmallAnt = indep(X)
    ).
