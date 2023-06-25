/*             Copyright (C)1990-94 UPM-CLIP                            */
:- module(deftools,
    [ def_abstract_equation/4,
      def_conjunct_constr/3,
      def_decide_arg/6,
      def_herbrand_equation/4,
      def_merge/3,
      def_minimize_each/3,
      def_numerical_equation0/4,
      def_project_each/3,
      def_remain_if_element/5,
      def_remain_if_element_all/3,
      find_type/2
    ],
    [ ]).

%------------------------------------------------------------------------%
% This portion contains the auxiliar functions for the definiteness      %
% analyzer for CLP languages by  M.J. Garcia de la Banda and             %
% M. Hermenegildo                                                        %
% The Meaning of the program variables is as in def.pl
%------------------------------------------------------------------------%
%                                                                        %
%        programmer: M. Garcia de la Banda                               %
%                                                                        %
%------------------------------------------------------------------------%

:- use_module(library(lists), [append/3, length/2]).
:- use_module(library(messages), [warning_message/2]).
:- use_module(library(sets), 
    [  merge/3, ord_member/2, ord_subset/2, ord_subtract/3, insert/3 ]).
:- use_module(library(sort), [sort/2]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(library(compiler/p_unit), [language/1]).

:- use_module(domain(s_grshfr), [merge_no_supersets/3]).

:- push_prolog_flag(multi_arity_warnings,off).

%-------------------------------------------------------------------------
%                 CONJUNCTING A HERBRAND CONSTRAINT                     %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% def_herbrand_equation(+,+,+,+,+,-),                                    %
% def_herbrand_equation(N1,N2,Term1,Term2,Call,Succ)                     %
% Term1 and Term2 are complex herbrand terms.                            %
% It will first check that both have the same predicate functor an arity.%
% If so, it will add to Call the information corresponding to the set of %
% equations =(Arg1,Arg2) which results from the herbrand unification     % 
% Term1= Term2 by recursively calling to def_abstract_equation/4,        %
% obtaining Succ.                                                        %
% Otherwise Succ = '$bottom'                                             %
%-------------------------------------------------------------------------

def_herbrand_equation(Term1,Term2,Call,Succ):-
    functor(Term1,F,A),
    functor(Term2,F,A),!,
    def_herbrand_equation(0,A,Term1,Term2,Call,Succ).
def_herbrand_equation(_Term1,_Term2,_Call,'$bottom').

def_herbrand_equation(N,N,_Term1,_Term2,Call,Call):- !.
def_herbrand_equation(N1,N,Term1,Term2,Call,Succ):-
    N2 is N1 + 1,
    arg(N2,Term1,Arg1),
    arg(N2,Term2,Arg2),
    def_abstract_equation(Arg1,Arg2,Call,NewCall),
    def_decide_herbrand(NewCall,N2,N,Term1,Term2,Succ).

def_decide_herbrand('$bottom',_N2,_N,_Term1,_Term2,'$bottom'):- !.
def_decide_herbrand(NewCall,N2,N,Term1,Term2,Succ):-
    def_herbrand_equation(N2,N,Term1,Term2,NewCall,Succ).

%-------------------------------------------------------------------------
% def_abstract_equation(+,+,+,-),                                        %
% def_abstract_equation(Term1,Term2,Call,Succ)                           %
% It adds the information provided by the equation Term1 = Term2 to Call %
% resulting in Succ.                                                     %
%  * If Term1 is a variable, it will call def_abstract_equation0/4.      %
%  * If Term1 is a nonvariable term and Term2 is a variable it will      %
%    obtain the type of Term1 and call def_abstract_var/5.               %
%  * If both are nonvariable terms it will obtain their types (checking  %
%    that they have the same type) and call def_abstract_nonvar/5        %
%  * Otherwise the equation is not consistent and Succ = '$bottom'       %
%-------------------------------------------------------------------------

def_abstract_equation(Term1,Term2,Call,Succ):-
    var(Term1),!,
    def_abstract_equation0(Term1,Term2,Call,Succ).
def_abstract_equation(Term1,Term2,Call,Succ):-
    var(Term2),!,
    find_type(Term1,Type),
    def_abstract_var(Type,Term2,Term1,Call,Succ).
def_abstract_equation(Term1,Term2,Call,Succ):-
    find_type(Term1,Type),
    find_type(Term2,Type),!,
    def_abstract_nonvar(Type,Term1,Term2,Call,Succ).
def_abstract_equation(_Term1,_Term2,_Call,'$bottom').

%-------------------------------------------------------------------------
%  def_abstract_equation0(+,+,+,-)                                       %
%  def_abstract_equation0(Var,Term,Call,Succ).                           %
%  It adds the information of the equation Var = Term to Call obtaining  %
%  Succ. If Term is a variable, then the information inferred is the     %
%  same that the one derived from a linear numerical equation with the   %
%  only variables being Var and Term.                                    %
%  Otherwise, it obtains the type of Term and calls def_abstract_var/5   %
%-------------------------------------------------------------------------

def_abstract_equation0(Var,Term,Call,Succ):-
    var(Term),!,
    sort([Var,Term],Lin),
    def_numerical_equation0([],Lin,Call,Succ).
def_abstract_equation0(Var,Term,Call,Succ):-
    find_type(Term,Type),
    def_abstract_var(Type,Var,Term,Call,Succ).

%-------------------------------------------------------------------------
% find_type(+,-)                                                         %
% find_type(Term,Type)                                                   %
% It will receive a nonvariable Term and obtain its type. The types are: %
%  - piii corresponding to a PrologIII list                              %
%  - num  corresponding to a numerical term (including numbers)          %
%  - herb corresponding to a herbrand term (for now only PrologIII and   %
%    numerical constraints are allowed, thus any term different from     %
%    piii or num must be herb                                            %
%-------------------------------------------------------------------------
find_type(X,Type):-
    language(clp),!,
    find_type0(X,Type).
find_type(_,Type):-
    language(lp),!,
    Type = herb.

find_type0(piii(_),piii):- !.
find_type0(+(_,_),num):- !.
find_type0(-(_,_),num):- !.
find_type0(/(_,_),num):- !.
find_type0(+(_),num):- !.
find_type0(-(_),num):- !.
find_type0(#(X),Type):- 
    atom(X),!,
    Type = num.
find_type0(X,Type):- 
    lsign_non_linear(X),!,
    Type = num.
find_type0(X,Type):-
    number(X),!,
    Type = num.
find_type0(_,herb).

% :- use_module(domain(delaytools), [lsign_non_linear/1]).
lsign_non_linear(_). % TODO: copy definition from lsign.pl?

%-------------------------------------------------------------------------
% def_abstract_var(+,+,+,+,-)                                            %
% def_abstract_one(Type,Var,Term,Call,Succ)                              %
% Var is a variable and Term is a nonvariable term.                      %
% It will call the appropiate 
% obtaining Succ. It will depend on Type (the type of Term):             %
%    * herb (herbrand)                                                   %
%    * piii (prologiii list)                                             %
%    * num numerical equation (could be linear or nonlinear)             %
%-------------------------------------------------------------------------

def_abstract_var(herb,Var,Term,Call,Succ):- 
    def_primitive_herbrand(Var,Term,Call,Succ).
def_abstract_var(piii,Var,piii(Term),Call,Succ):-
    def_primitive_piii(Term,Var,Call,Succ).
def_abstract_var(num,Var,Term,Call,Succ):-
    def_numerical_equation(Var+Term,Call,Succ).

%-------------------------------------------------------------------------
% def_abstract_nonvar(+,+,-)                                             %
% def_abstract_nonvar(Type,Term1,Term2,Call,Succ)                        %
% Term1 and Term2 are not variables. Type is the type of Term1 and Term2,%
% which can be the following:                                            %
%    * num numerical equation (could be linear or nonlinear)             %
%    * piii prologiii list equation (could be linear or nonlinear)       %
%    * herb herbrand equation                                            %
% It will add the information contained in the equation Term1 = Term2    %
% to Call obtaining Succ                                                 %
% Careful, herb must be the first because Type might be var in this case %
%-------------------------------------------------------------------------

def_abstract_nonvar(herb,Term1,Term2,Call,Succ):-
    def_herbrand_equation(Term1,Term2,Call,Succ).
def_abstract_nonvar(piii,piii(Term1),piii(Term2),Call,Succ):-
    def_piii_equation(Term1,Term2,Call,Succ).
def_abstract_nonvar(num,Term1,Term2,Call,Succ):-
    def_numerical_equation(Term1+Term2,Call,Succ).

%-------------------------------------------------------------------------
% def_primitive_herbrand(+,+,+,-)                                        %
% def_primitive_herbrand(Var,Term,Call,Succ)                             %
% Var is a variables and Term is a complex Herbrand term. It adds the    %
% information inferred from Var = Term to Call obtaining Succ.           %
% First the information for Var is added:                                %
%      * If Var is ground in Call, the information is already there      %
%      * Otherwise (X,[NonGroundVars]) is added to Call where            %
%        NonGroundVars is the subset of vars in Term which are not ground%
% Then the information for the vars in each argument of Term is added    %
%-------------------------------------------------------------------------

def_primitive_herbrand(Var,Term,Call,Succ):-
    Call = a(G,_),
    ord_member(Var,G),!,
    functor(Term,_F,A),
    def_primitive_herbrand(0,A,Term,[],Call,Succ).
def_primitive_herbrand(Var,Term,Call,Succ):- 
    varset(Term,VarsTerm),
    Call = a(G,_),
    ord_subtract(VarsTerm,G,NonGroundVars),
    def_decide_primitive_herbrand(NonGroundVars,Var,Term,Call,Succ).

def_decide_primitive_herbrand([],Var,_Term,Call,Succ):- !,
    Constr1= a([Var],[]),
    def_conjunct_constr(Constr1,Call,Succ).
def_decide_primitive_herbrand([X],Var,_Term,Call,Succ):- !,
    sort([X,Var],Lin),
    def_numerical_equation0([],Lin,Call,Succ).
def_decide_primitive_herbrand(NonGroundVars,Var,Term,Call,Succ):- 
    functor(Term,_F,A),
    def_primitive_herbrand(0,A,Term,[Var],Call,Call1),
    Constr1= a([],[(Var,[NonGroundVars])]),
    def_conjunct_constr(Constr1,Call1,Succ).

%-------------------------------------------------------------------------
% def_primitive_herbrand(+,+,+,+,+,-)                                    %
% def_primitive_herbrand(I,A,Term,Vars,Call,Succ)                        %
% The information for Var has been already added to Call. Thus, only the %
% information fro the variables in each argument of Term need to be added%
% In each iteration the ith-argument of Term is handeled.                %
%  *  All ith-arguments Arg such that Arg is a variable, are kept in     %
%     the accumulator Herb since for all of them the information inferred%
%     will be (Arg,[[Var]]). This information will be added at the end   %
%     of the iteration.                                                  %
%  *  Otherwise, def_add_argument will be called.                        %
%-------------------------------------------------------------------------

def_primitive_herbrand(A,A,_Term,_Vars,Call,Call):- !.
def_primitive_herbrand(I,A,Term,Vars,Call,Succ):-
    I1 is I +1,
    arg(I1,Term,Arg),
    def_primitive_one(Arg,Vars,Call,Call1),
    def_primitive_herbrand(I1,A,Term,Vars,Call1,Succ).

def_primitive_one(Arg,Vars,Call,Succ):-
    var(Arg),!,
    Call =a(G,_),
    ( ord_member(Arg,G) ->
       Succ = Call
    ; def_build_non_linear([Arg],Vars,[],Ground,Set),
      def_conjunct_constr(a(Ground,Set),Call,Succ)
    ).
def_primitive_one(Arg,Vars,Call,Succ):-
    find_type(Arg,Type),
    def_primitive_type(Type,Arg,Vars,Call,Succ).

def_primitive_type(herb,Arg,Vars,Call,Succ):-
    functor(Arg,_F,A),
    def_primitive_herbrand(0,A,Arg,Vars,Call,Succ).
def_primitive_type(num,Arg,Vars,Call,Succ):-
    def_find_linearity_num(Arg,Lin,NonLin),
    merge(NonLin,Vars,NewNonLin),
    def_numerical_equation0(NewNonLin,Lin,Call,Succ).
def_primitive_type(piii,Arg,Vars,Call,Succ):-
    def_primitive_piii0(Arg,Vars,Call,Succ).

%-------------------------------------------------------------------------
%                 CONJUNCTING A NUMERICAL CONSTRAINT                     %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% def_numerical_equation(+,+,-)                                          %
% def_numerical_equation(Term,Call,Succ)                                 %
% Term is the numerical term resulting from a numerical equation (i.e.   %
% a Term is Term1 + Term2 where Term1 = Term2 was the original equation) %
% It will add the information of the numerical equation to Call obtaining%
% Succ. It first computes NonLin (the set of variables in Term which are %
% involved in a nonlinear subterm) and TempLin (the set of variables     %
% involved in linear subterms). Then it subtracts form TempLin those     %
% variables which are nonlinear (aappear both in linear and non linear   %
% subterms) obtaining Lin.                                               %
% Then it calls to def_numerical_equation0 (separated because it is      %
% called by itself) which builds the abstraction of the numerical        %
% constraint and calls def_conjunct_constr.                              %
%-------------------------------------------------------------------------

def_numerical_equation(Term,Call,Succ):-
    def_find_linearity_num(Term,TempLin,NonLin),
    ord_subtract(TempLin,NonLin,Lin),
    def_numerical_equation0(NonLin,Lin,Call,Succ).

def_numerical_equation0(NonLin,Lin,Call,Succ):-
    def_build_numerical_constraint(NonLin,Lin,Call,Constr),
    def_conjunct_constr(Constr,Call,Succ).

%-------------------------------------------------------------------------
% def_build_numerical_constraint(+,+,+,-)                                %
% def_build_numerical_constraint(NonLin,Lin,Call,Constr)                 %
% Recives two sets of variables. NonLin contains the variables which     %
% do not depend on any other variable. Lin contains the set of variables %
% such that each variable X depends on NonLin \cup ( Lin \minus \{X\})   %
% We first compute NonGroundLin and NonGroundNonLin. Then we call        %
% def_build_nonlinear which returns the appropriate set of dependencies  %
% and finally we build the constraint.                                   %
% Note that the ground information of Call has already been propagated   %
% to Constr (when computing NonGroundLin and NoNGroundNonLin). This will %
% be true any time def_conjunct_constr(Constr,Call,Succ) be called.      %
%-------------------------------------------------------------------------

def_build_numerical_constraint(NonLin,Lin,Call,Constr):- 
    Call = a(G,_S),
    ord_subtract(Lin,G,NonGroundLin),
    ord_subtract(NonLin,G,NonGroundNonLin),
    merge(NonGroundLin,NonGroundNonLin,Vars),
    def_build_non_linear(NonGroundLin,Vars,[],Ground,Set),  
    Constr = a(Ground,Set).

%-------------------------------------------------------------------------
% def_build_non_linear(+,+,+,-,-)                                        %
% def_build_non_linear(Lin,AllVars,TempGround,Ground,Set)                %
% Builds the dependency component (Set) of the abstraction of a non linear 
% constraint in which Lin is the set of linear variables and Allvars is  %
% the set of all the variables involved in the constraint. TempGround is %
% an accmulation parameter for Ground                                    %
%      Set =  {(X,[S]) | X in Lin, S = (AllVars \minus [X]), S\== []}    %
%      Ground = {X in Lin | AllVars \minus [X] = []}                     %
%-------------------------------------------------------------------------

def_build_non_linear([],_Vars,Temp,Temp,[]).
def_build_non_linear([X|Lin],Vars,Temp,Ground,Constr):-
    ord_subtract(Vars,[X],NewTerm),
    def_decide_ground(NewTerm,X,Temp,NewTemp,Constr,NewConstr),
    def_build_non_linear(Lin,Vars,NewTemp,Ground,NewConstr).

def_decide_ground([],X,Temp,NewTemp,Constr,NewConstr):- !,
    insert(Temp,X,NewTemp),
    NewConstr = Constr.
def_decide_ground(NewTerm,X,Temp,Temp,[(X,[NewTerm])|NewConstr],NewConstr).

%-------------------------------------------------------------------------
% def_find_linearity_num(+,-,-)
% def_find_linearity_num(Term,Lin,NonLin)
% If term is linear (corresponding to a linear equation) then 
% Lin = VarsTerm, NonLin = []. Otherwise, Lin = LinearVarsTerm, 
% NonLin = NonlinearVarsTerm
%-------------------------------------------------------------------------

def_find_linearity_num(X,Lin,NonLin):- 
    var(X),!,
    Lin = [X],NonLin = [].
def_find_linearity_num(X,Lin,NonLin):- 
    ground(X),!,
    Lin = [], NonLin = [].
def_find_linearity_num(sin(X),[],NonLin):-
    varset(X,NonLin).
def_find_linearity_num(arcsin(X),Lin,[]):-
    varset(X,Lin).
def_find_linearity_num(cos(X),[],NonLin):-
    varset(X,NonLin).
def_find_linearity_num(arccos(X),Lin,[]):-
    varset(X,Lin).
def_find_linearity_num(pow(X,Y),[],NonLin):-
    varset(p(X,Y),NonLin).
def_find_linearity_num(min(X,Y),[],NonLin):-
    varset(p(X,Y),NonLin).
def_find_linearity_num(max(X,Y),[],NonLin):-
    varset(p(X,Y),NonLin).
def_find_linearity_num(abs(X),[],NonLin):-
    varset(X,NonLin).
def_find_linearity_num(eval(X),[],NonLin):-
    varset(X,NonLin).
def_find_linearity_num(+(X,Y),Lin,NonLin):- 
    def_find_linearity_num(X,Lin1,NonLin1),
    def_find_linearity_num(Y,Lin2,NonLin2),
    merge(Lin1,Lin2,Lin3),
    merge(NonLin1,NonLin2,NonLin),
    ord_subtract(Lin3,NonLin,Lin).
def_find_linearity_num(-(X,Y),Lin,NonLin):- 
    def_find_linearity_num(X,Lin1,NonLin1),
    def_find_linearity_num(Y,Lin2,NonLin2),
    merge(Lin1,Lin2,Lin3),
    merge(NonLin1,NonLin2,NonLin),
    ord_subtract(Lin3,NonLin,Lin).
def_find_linearity_num(*(X,Y),Lin,NonLin):- 
    varset(X,VarsX),
    ( VarsX = [] ->
        def_find_linearity_num(Y,Lin,NonLin)
    ; varset(Y,VarsY),
      ( VarsY = [] ->
          def_find_linearity_num(X,Lin,NonLin)
      ; Lin = [],
        merge(VarsX,VarsY,NonLin)
      )
    ).
def_find_linearity_num(/(X,Y),Lin,NonLin):-  !,
    ( ground(Y) ->
        def_find_linearity_num(X,Lin,NonLin)
    ;  warning_message("Non-normalized division ~w",[X/Y])
    ).
def_find_linearity_num(+(X),Lin,NonLin):- 
    def_find_linearity_num(X,Lin,NonLin).
def_find_linearity_num(-(X),Lin,NonLin):- 
    def_find_linearity_num(X,Lin,NonLin).

%-------------------------------------------------------------------------
%            CONJUNCTING A PrologIII LIST CONSTRAINT                     %
%-------------------------------------------------------------------------
%-------------------------------------------------------------------------
% def_piii_equation(+,+,+,-)
% def_piii_equation(Term1,Term2,Call,Succ)
% It will obtain the abstract constraint resulting form the equation
% Term1 = Term2 where both Terms are prologiii lists. The prologiii      %
% lists are translated into something readable by Prolog. For example:   %
%           <>          -> piii([])                                      %
%           <>.X        -> piii([[],X])                                  %
%           X.Y         -> piii([X,Y])                                   %
%           <X>.Y       -> piii([[X],Y])                                 %
%           <X>.<Y>.Z   -> piii([[X],[Y],Z)                              %
%           <X,Y>.Z     -> piii([[X,Y],Z])                               %
%           <X.Y>.Z     -> piii([ [piii([X,Y])] , Z ])                   %
%           <<X>.Y>.Z   -> piii([ [piii([[X],Y]], Z ]).                  %
% Then:                                                                  %
%  * If both = [] the Call = Succ                                        %
%  * If one (say Term1) is [] and the other (say Term2) is not, then:    %
%       - If all arguments in Term2 are variables then they must be "nil"%
%         and thus they are ground                                       %
%       - Otherwise it is an inconsistent constraint so Succ = '$bottom' %
%  * If one (say Term1) is [X], then def_primitive_piii/4 is called      %
%  * If both Term1 and Term2 start by a "definitely length defined"      %
%    element (i.e. a nonvar) then new equations correspoding to each     %
%    argument of the list elements will be obtained. If one list is      %
%    longer than the other, the rest of the longer will remain for the   %
%    recursive call.                                                     %
%  * Otherwise the information for each element of Term1 and Term2 will  %
%    built separately by def_piii_equation_each/6                        %
%-------------------------------------------------------------------------

def_piii_equation([],[],Call,Call):- !.
def_piii_equation([],Y,Call,Succ):- !,
    def_take_nonvars(Y,NonVars),
    def_decide_ground_piii(NonVars,Y,Call,Succ).
def_piii_equation(X,[],Call,Succ):- !,
    def_take_nonvars(X,NonVars),
    def_decide_ground_piii(NonVars,X,Call,Succ).
def_piii_equation([X],Y,Call,Succ):-
    var(X),!,
    def_primitive_piii(Y,X,Call,Succ).
def_piii_equation(X,[Y],Call,Succ):-
    var(Y),!,
    def_primitive_piii(X,Y,Call,Succ).
def_piii_equation([X|RestX],[Y|RestY],Call,Succ):-
    nonvar(X),nonvar(Y),!,
    def_decide_piii(X,Y,RestX,RestY,NX,NY,Call,Call1),
    def_piii_equation(NX,NY,Call1,Succ).
def_piii_equation(X,Y,Call,Succ):-
    def_piii_equation_each(X,X,[],Y,Call,Call1),
    def_piii_equation_each(Y,Y,[],X,Call1,Succ).

%-------------------------------------------------------------------------
% def_decide_ground_piii(+,+,+,-,-)                                      %
% def_decide_ground_piii(NonVars,Y,Call,Succ)                            %
% Nonvars are the nonvariable arguments of a prologiii list Y which has  %
% been constrained to be []. Thus, if Nonvars is [] then the variable    %
% arguments in Y must be ground. Otherwise the constraint is inconsistent%
%-------------------------------------------------------------------------

def_decide_ground_piii([],Y,a(G,S),Succ):- !,
    varset(Y,Ground),
    ord_subtract(Ground,G,NewGround),
    def_conjunct_constr(a(NewGround,[]),a(G,S),Succ).
def_decide_ground_piii(_,_,_,'$bottom').

%-------------------------------------------------------------------------
% def_primitive_piii(+,+,+,-),                                           %
% def_primitive_piii(Var,Term,Call,Succ)                                 %
% It will add to Call the information corresponding to the prologiii list%
% constraint Var = Term , where Var is a variable and Term is a prologiii%
% list (different from a variable).                                      %
% The idea is to first add the information for Var and then call the     %
% appropriate predicate. The information for var is (Var, [VarsTerm])    %
% However, has mentioned before, any time def_conjunct_constr is called  %
% the groundness information of Call has to be already propagated to the %
% Constraint. Thus:
%   * If Var is already ground in call, the information for Var is       %
%     already in Call and def_primitive_piii0 will be called directly.   %
%   * Otherwise NonGroundVars (set of nonground variables in Term) is    %
%     computed. Then:
%       - if NonGroundVars = [], the only thing to be done is to make Var%
%         ground in Call.
%       - If NonGroundVars = [X] the only thing to be done is add the
%         information (Var, [[X]]),(X,[[Var]]) to Call. Note that since  %
%         this abstraction is the same that the one obtained form a      %
%         linear numerical equation in which X and Y appear, we can call %
%         def_numerical_equation0([],Lin,Call,Succ)                      %
%       - Otherwise, we eliminate Var from NonGroundVars (just in case)  %
%         obtaining NGVars1, add (Var,[NGVars1]) to Call and then call   %
%         def_primitive_piii0(Term,[Var],Call1,Succ)                     %
%-------------------------------------------------------------------------

def_primitive_piii(Term,Var,Call,Succ):- 
    Call = a(G,_),
    ord_member(Var,G),!,
    def_primitive_piii0(Term,[],Call,Succ).
def_primitive_piii(Term,Var,Call,Succ):- 
    varset(Term,VarsTerm),
    Call = a(G,_),
    ord_subtract(VarsTerm,G,NonGroundVars),
    def_decide_primitive_piii(NonGroundVars,Var,Term,Call,Succ).

def_decide_primitive_piii([],Var,_Term,Call,Succ):- !,
    Constr1= a([Var],[]),
    def_conjunct_constr(Constr1,Call,Succ).
%% def_decide_primitive_piii(Vars,Var,Term,_Call,Succ):- 
%%      ord_member(Var,Vars),
%%      def_take_nonvars(Term,Non),
%%      Non \== [],!,
%%      Succ = '$bottom'.
def_decide_primitive_piii([X],Var,_Term,Call,Succ):-  !,
    sort([X,Var],Lin),
    def_numerical_equation0([],Lin,Call,Succ).
def_decide_primitive_piii(NGVars,Var,Term,Call,Succ):- 
    ord_subtract(NGVars,[Var],NGVars1),
    Constr1= a([],[(Var,[NGVars1])]),
    def_conjunct_constr(Constr1,Call,Call1),
    def_primitive_piii0(Term,[Var],Call1,Succ).

%-------------------------------------------------------------------------
% def_primitive_piii0(+,+,+,-)                                           %
% def_primitive_piii0(Term,Vars,Call,Succ)                               %
% Term is a prologiii list in which each argument depends on Vars        %
%-------------------------------------------------------------------------

def_primitive_piii0(Term,Vars,Call,Succ):-
    def_primitive_piii1(Term,Vars,Call,[],Succ).

def_primitive_piii1([],Vars,Call,Lin,Succ):-
    merge(Vars,Lin,Vars1),
    def_build_non_linear(Lin,Vars1,[],Ground,Set),
    def_conjunct_constr(a(Ground,Set),Call,Succ).
def_primitive_piii1([X|Rest],Vars,Call,Lin,Succ):-
    var(X),!,
    Call = a(G,_),
    ( ord_member(X,G) ->
      NewLin = Lin
    ; insert(Lin,X,NewLin)
    ),
    def_primitive_piii1(Rest,Vars,Call,NewLin,Succ).
def_primitive_piii1([TermSeq|Rest],Vars,Call,Lin,Succ):-
    def_primitive_piii_ground(TermSeq,Vars,Call,Lin,Call1),
    def_collect_main_vars(Rest,RestLin),
    sort(RestLin,RestLin_s),
    def_primitive_piii_ground(TermSeq,Vars,Call1,RestLin_s,Call2),
    def_primitive_piii1(Rest,Vars,Call2,Lin,Succ).

def_primitive_piii_ground([],_Vars,Call,_,Call).
def_primitive_piii_ground([X|TermSeq],Vars,Call,Lin,Succ):-
    nonvar(X), X = piii(Y),!,
    merge(Vars,Lin,Vars1),
    def_primitive_one(Y,Vars1,Call,Call1),
    def_primitive_piii_ground(TermSeq,Vars,Call1,Lin,Succ). 
def_primitive_piii_ground([X|TermSeq],Vars,Call,Lin,Succ):-
    merge(Vars,Lin,Vars1),
    def_primitive_one(X,Vars1,Call,Call1),
    def_primitive_piii_ground(TermSeq,Vars,Call1,Lin,Succ).
    
def_collect_main_vars([],[]).
def_collect_main_vars([X|Xs],Vars):-
    var(X),!,
    Vars = [X|NewVars],
    def_collect_main_vars(Xs,NewVars).
def_collect_main_vars([_X|Xs],Vars):-
    def_collect_main_vars(Xs,Vars).

%-------------------------------------------------------------------------
%-------------------------------------------------------------------------

def_piii_equation_each([],_TempX,_Y,_TempY,Call,Call).
def_piii_equation_each([X|RestX],TermX,TempX,TermY,Call,Succ):-
    var(X),!,
    Call = a(G,_),
    ( ord_member(X,G) ->
      Call1 = Call,
      NewTempX = TempX
    ; def_collect_main_vars(TermX,Vars1),
      sort(Vars1,Vars1_s),
      def_collect_main_vars_but_last(TermY,[],[],NonVar,TempVars),
      def_decide_nonvars(NonVar,RestX,TempVars,Vars2),
      merge(Vars1_s,Vars2,Vars),
      ord_subtract(Vars,G,NGVars),
      def_build_non_linear([X],NGVars,[],Ground,Set),         
      def_conjunct_constr(a(Ground,Set),Call,Call1),
      NewTempX = [X|TempX]
    ),
    def_piii_equation_each(RestX,TermX,NewTempX,TermY,Call1,Succ).
def_piii_equation_each([X|RestX],TermX,TempX,TermY,Call,Succ):-
    varset(TempX,Vars1),
    varset(TermY,Vars2),
    merge(Vars1,Vars2,Vars3),
    Call = a(G,_),
    ord_subtract(Vars3,G,NGVars1),
    find_type(X,Type),
    def_primitive_type(Type,X,NGVars1,Call,Call1),
    def_collect_main_vars(RestX,Vars4),
    sort(Vars4,Vars4_s),
    merge(Vars4_s,Vars2,Vars5),
    ord_subtract(Vars5,G,NGVars2),
    def_primitive_type(Type,X,NGVars2,Call1,Call2),
    def_piii_equation_each(RestX,TermX,TempX,TermY,Call2,Succ).


def_decide_nonvars([],_RestX,Vars,Vars):- !.
def_decide_nonvars(NonVar,RestX,TempVars,Vars):-
    length_each(NonVar,0,N,[],Args),
    def_take_nonvars(RestX,NonVars),
    length_each(NonVars,0,N1,[],_),
    N2 is N - N1,
    def_take_last(N2,Args,[],Vars1),
    merge(TempVars,Vars1,Vars).

def_take_last(0,_Args,Temp,Temp):- !.
def_take_last(N,[Arg|Args],Temp,Vars):-
    N > 0,!,
    varset(Arg,Vars1),
    merge(Temp,Vars1,NewTemp),
    N1 is N -1,
    def_take_last(N1,Args,NewTemp,Vars).
def_take_last(_N,_,_,[]).


def_take_nonvars([],[]).
def_take_nonvars([X|RestX],NonVars):-
    var(X),!,
    def_take_nonvars(RestX,NonVars).
def_take_nonvars([[]|RestX],NonVars):- !,
    def_take_nonvars(RestX,NonVars).
def_take_nonvars([X|RestX],[X|NonVars]):-
    def_take_nonvars(RestX,NonVars).

length_each([],N,N,Temp,Temp).
length_each([X|NonVar],N1,N,Temp,Args):-
    length(X,N2),
    N3 is N1 + N2,
    append(X,Temp,NewTemp),
    length_each(NonVar,N3,N,NewTemp,Args).



def_collect_main_vars_but_last([],Temp,NonVar,NonVar,Temp).
def_collect_main_vars_but_last([X|Xs],Temp1,Temp2,NonVar,Vars):-
    var(X),!,
    varset(Temp2,VarsTemp2),
    merge(Temp1,VarsTemp2,Temp),
    insert(Temp,X,NewTemp),
    def_collect_main_vars_but_last(Xs,NewTemp,[],NonVar,Vars).
def_collect_main_vars_but_last([X|Xs],Temp1,Temp2,NonVar,Vars):-
    def_collect_main_vars_but_last(Xs,Temp1,[X|Temp2],NonVar,Vars).

%% def_piii_equation([X|Rest],[],Call,Succ):-
%%      X = [],!,
%%      def_piii_equation(Rest,[],Call,Succ).
%% def_piii_equation([],[Y|Rest],Call,Succ):-
%%      Y = [],!,
%%      def_piii_equation(Rest,[],Call,Succ).
%% def_piii_equation(_X,_Y,_Call,'$bottom').

    
%% def_piii_bottom_equation('$bottom',_NX,_NY,'$bottom'):- !.
%% def_piii_bottom_equation(NewCall,NX,NY,Succ):- 
%%      def_piii_equation(NX,NY,NewCall,Succ).

def_decide_piii([],[],RX,RY,RX,RY,Call,Call):- !.
def_decide_piii(Term,[],RX,RY,[Term|RX],RY,Call,Call):- !.
def_decide_piii([],Term,RX,RY,RX,[Term|RY],Call,Call).
def_decide_piii([X|RestX],[Y|RestY],RX,RY,NX,NY,Call,Succ):- 
    def_abstract_equation(X,Y,Call,NewCall), 
    def_decide_bottom_piii(NewCall,RestX,RestY,RX,RY,NX,NY,Succ).

def_decide_bottom_piii('$bottom',_RestX,_RestY,_RX,_RY,_NX,_NY,'$bottom'):- !.
def_decide_bottom_piii(NewCall,RestX,RestY,RX,RY,NX,NY,Succ):-
    def_decide_piii(RestX,RestY,RX,RY,NX,NY,NewCall,Succ).

%-------------------------------------------------------------------------
% def_conjunct_constr(+,+,-)
% def_conjunct_constr(Constr1,Constr2,Succ).
% It obtains the abstract constraint resulting from the abstract conjunction 
% of the abstract consraints in the first (Constr1) and second (Constr2) 
% arguments. We assume that all variables in Constr are in Lambda (not vice
% versa). Also we will asume that all the variables in Constr1 which are 
% uniquely defined in Constr2, are also uniquely defined in Constr1
% (this is because when computing the extend, this is true, and also
% when abstracting a primitive constraint, this is taken into account
% for reducing the amount of work.
%  - If Constr1 = a([],_,[]) then no new information is provided by Constr1
%    Thus Succ. 
%  - If Constr1 = a(G1,_,[]) and Constr2 = a(G2,T2,[]) then all the 
%    information is uniquely define variables or top variables. Thus
%    Succ = (NewG,NewT,[]), where NewG is G1 union G2, and NewT is
%    T2\T1.
%  - If Constr1 = a([],_,S1) and Constr2= a(G2,T2,[]) then all the
%    relationships are in S1, all the groundness information is in G2
%    and the top information is in T2 minus the variables in S1
%    Thus, SUcc = (G1,NewTop,S1) where NewTop is T2\{X | (X,_) in S1}
%  - If Constr1 = a(G1,_,S1) and Constr2= a(G2,T2,[]) then situation is 
%    identical to the one above but now, new groundness information is 
%    provided by G1. Thus, Succ = (NewG,NewTop,S1) where NewG is G1 union G2
%    and NewTop is T2\( {X | (X,_) in S1} union G1)
%  - Otherwise, will:
%    - merge the information in both abstract constraints (Temp_Lambda).
%      computing Changed = (Ground,Set) where Ground is the set of variables
%      in G1 which are not in G2, and Set is the set of those elements in 
%      Temp_Lambda which are different from those either in Set1 or Set2.
%    - Then it propagates the information until reching a fixpoint
%-------------------------------------------------------------------------

def_conjunct_constr(a(G1,S1),a(G2,[]),Lambda):- !,
    merge(G1,G2,G),
    Lambda = a(G,S1).
def_conjunct_constr(a(G1,[]),a(G2,S2),Lambda):- !,
    ord_subtract(G1,G2,NewG1),
    def_eliminate_if_element_all(NewG1,S2,TempS),
    propagate(NewG1,TempS,NewG1,NewS,NewG2),
    merge(NewG2,G2,NewG),
    Lambda = a(NewG,NewS).
def_conjunct_constr(a(G1,S1),a(G2,S2),a(TG,TSet)):- 
%%      myspy,
    ord_disjunction_merge(G1,G2,CG,TmpG),
    propagate(CG,S2,TmpG,TmpS2,TG),
    propagate_inform(S1,TmpS2,TSet_u),
    sort(TSet_u,TSet).
%%      ( \+ \+ (numbervars(p(G1,S1,G2,S2),0,_),
%%               write(user,a(G1,S1)),nl(user),
%%               write(user,a(G2,S2)),nl(user),
%%               write(user,a(TG,TSet)),nl(user)
%%               )).

propagate_inform([],S2,S2).
propagate_inform([(Y,Ty)|Xs],S2,[(Y,NewTy)|UpdatedS2]):-
    propagate_s2_to_y(S2,Y,Ty,NewTy,Flag),
    ( Flag == yes ->
        TmpS2 = S2
    ; propagate_tmpy_to_s2(S2,Y,NewTy,TmpS2)
    ),
    propagate_inform(Xs,TmpS2,UpdatedS2).

propagate_tmpy_to_s2([],_,_,[]).
propagate_tmpy_to_s2([(X,Tx)|S2],Y,Ty,[(X,TmpTx)|NewS2]):-
    propagate_first_to_sec(Y,Ty,X,Tx,TmpTx,_),
    propagate_tmpy_to_s2(S2,Y,Ty,NewS2).

propagate_s2_to_y([],_,Ty,Ty,_).
propagate_s2_to_y([(X,Tx)|S2],Y,Ty,NewTy,Flag):-
    propagate_first_to_sec(X,Tx,Y,Ty,TmpTy,Flag),
    ( Flag == yes ->
        NewTy = Ty
    ; propagate_s2_to_y(S2,Y,TmpTy,NewTy,Flag)
    ).

%% %-------------------------------------------------------------------------
%% % def_add_inform_diff(+,+,-,-)
%% % def_add_inform_diff(Constr,Lambda,Temp_Lambda,Changed)
%% % It adds the information in the ordered Constr (first argument)
%% % to the ordered Lambda (second argument), obtaining Temp_lambda (third 
%% % argument) and leting in the fourth argument those elements which have 
%% % changed  w.r.t. either Constr or Lambda.
%% % Let Constr = (G1,T1,S1), Lambda = (G2,T2,S2), Temp_Lambda= a(TG,TT,TSet) 
%% % and Changed = a(CG,CSet).
%% %     - CG is G1 minus G2 (assumes that all relevant G2 is in G1)
%% %     - TG is G1 union G2
%% %     - TT is T2 minus (CG union VS1) where VS1= {X| (X,_) in S1}
%% %     - TSet and CSet are computed by calling to def_add_inform_diff_set/7
%% %-------------------------------------------------------------------------
%% 
%% def_add_inform_diff(a(G1,S1),a(G2,S2),a(TG,TSet),a(CG,CSet)):- 
%%      ord_disjunction_merge(G1,G2,CG,TG),
%%      def_add_inform_diff_set(S1,S2,CG,TSet,CSet).
%% 
%% %-------------------------------------------------------------------------
%% % def_add_inform_diff_set(+,+,+,+,-,-,-).
%% % def_add_inform_diff_set(S1,S2,CG,T1,TSet,CSet,VS1)
%% % It received the set components (S1 and S2) of two abstract constraints C1
%% % and C2, the set of variables (CG) in C2 which are now ground due to C1
%% % and the set of top variables (T1) in C1.
%% % The aim is to obtain TSet, the abstract conjunction of S1 and S2, and also
%% % CSet, the set of (X,SS) such that the information for X is different either 
%% % in C1 or C2. This will be done by traversing both S1 and S2 (in traversing
%% %  it VS1, the set of variables X s.t. (X,_) in S1, will be obtained),
%% % in th follwoing way, for each (X,SS1) in S1:
%% %      - if there is no (X,_) in S2, then it is clear that X is top in C2
%% %        and therefore (X,SS1) will be part of TSet and also CSet
%% %      - if there is an (X,SS2) in S2 then we will combine SS1 and SS2
%% %        by calling to def_add_element/4 obtaining NewTx, which will be 
%% %        added to TSet, and a Flag which indicates if NewTx is different 
%% %        w.r.t. either SS1 or SS2.  If it is, (X,NewTx) will be added also
%% %        to CSet.
%% % Finally, for each (X,SS2) in S2 s.t. there is no (X,_)in S1:
%% %      - (X,SS2) will be in TSet if X is not in CG. The reason is that
%% %        if X is CG, after the conjuntion it will be ground. Otherwise
%% %        X either is top in C1 or is not considered by C1. In both case
%% %        (X,SS2) must appear in TSet
%% %      - (X,SS2) will be in CSet if X is in T1. The reason is that
%% %        if X is T1, it has changed. Otherwise X either is ground in C1 
%% %        or is not considered by C1. 
%% %-------------------------------------------------------------------------
%% 
%% def_add_inform_diff_set([],X,CG,TSet,CSet):- !,
%%      def_eliminate_if_element_all(CG,X,TSet),
%%      TSet = CSet.
%% def_add_inform_diff_set(X,[],_CG,X,X):- !.
%% def_add_inform_diff_set([(X,Tx)|Tl1],[(Y,Ty)|Tl2],CG,TSet,CSet) :-
%%      compare(Ord, X, Y),
%%      def_add_inform_diff(Ord,(X,Tx),Tl1,(Y,Ty),Tl2,CG,TSet,CSet).
%% 
%% % def_add_inform(+,+,+,+,+,+,-)
%% def_add_inform_diff(=,(X,Tx),Tl1,(_,Ty),Tl2,CG,[(X,NTx)|TSet],CSet):-
%%         compare(Order,Tx,Ty),
%%      def_add_element(Order,Tx,Ty,NTx,Flag),
%%      def_changed(Flag,(X,NTx),CSet,NCSet), 
%%      def_add_inform_diff_set(Tl1,Tl2,CG,TSet,NCSet).
%% def_add_inform_diff(>,Hd1,Tl1,Hd0,Tl2,CG,TSet,CSet) :-
%%      def_eliminate_if_element(CG,Hd0,TSet,NTSet,NCG),
%%      def_eliminate_if_element(CG,Hd0,CSet,NCSet,_NCG),
%%      def_add_inform_diff_set([Hd1|Tl1],Tl2,NCG,NTSet,NCSet).
%% def_add_inform_diff(<,Hd0,Tl1,Hd2,Tl2,GC,[Hd0|TSet],[Hd0|CSet]) :-
%%      def_add_inform_diff_set(Tl1,[Hd2|Tl2],GC,TSet,CSet).

% def_add_element(+,+,-,-)
def_add_element(=,Tx,_Ty,Tx,yes).
def_add_element(>,Tx,Ty,New_Ty,no):- 
    merge_no_supersets(Tx,Ty,New_Ty).
def_add_element(<,Tx,Ty,New_Ty,no):- 
    merge_no_supersets(Tx,Ty,New_Ty).

%def_changed(+,+,-,-).
%
%% def_changed(yes,_NewElem,CSet,CSet).
%% def_changed(no,NewElem,[NewElem|CSet],CSet).

%-------------------------------------------------------------------------
% def_remain_if_element_all(+,+,-)
% def_remain_if_element_all(Vars,Elements,CSet):- !.
% Returns the list of elements (X,SS) in the second argument Elements s.t.
% X appear in the sorted list of variables Vars
%-------------------------------------------------------------------------

def_remain_if_element_all([],_X,[]):- !.
def_remain_if_element_all(T1,Elem,CSet):-
    def_remain_if_element_set(Elem,T1,CSet).

def_remain_if_element_set([],_T1,[]).
def_remain_if_element_set([X|Xs],T1,CSet):-
    def_remain_if_element(T1,X,CSet,NewCSet,NewT1),
    def_remain_if_element_set(Xs,NewT1,NewCSet).


def_remain_if_element([],_Elem,CSet,CSet,[]).
def_remain_if_element([T|T1],(X,Set),CSet,NewCSet,NewT1):-
    compare(Ord,T,X),
    def_remain_if_element(Ord,T,T1,(X,Set),CSet,NewCSet,NewT1).

def_remain_if_element(=,_T,T1,Elem,[Elem|CSet],CSet,T1).
def_remain_if_element(<,_T,T1,Elem,CSet,NewCSet,NewT1):-
    def_remain_if_element(T1,Elem,CSet,NewCSet,NewT1).
def_remain_if_element(>,T,T1,_Elem,CSet,CSet,[T|T1]).
    

%-------------------------------------------------------------------------
% def_eliminate_if_element_all(+,+,-)
% def_eliminate_if_element_all(Vars,Elements,CSet):- !.
% Returns the list of elements (X,SS) in the second argument Elements s.t.
% X does not appear in the sorted list of variables Vars
%-------------------------------------------------------------------------
def_eliminate_if_element_all([],X,X):- !.
def_eliminate_if_element_all(CG,X,TSet):-
    def_eliminate_if_element_set(X,CG,TSet).

def_eliminate_if_element_set([],_CG,[]).
def_eliminate_if_element_set([X|Xs],CG,TSet):-
    def_eliminate_if_element(CG,X,TSet,NewTSet,NewCG),
    def_eliminate_if_element_all(NewCG,Xs,NewTSet).

def_eliminate_if_element([],Elem,[Elem|TSet],TSet,[]).
def_eliminate_if_element([G|CG],(X,Set),TSet,NewTSet,NewCG):-
    compare(Ord,G,X),
    def_eliminate_if_element(Ord,G,CG,(X,Set),TSet,NewTSet,NewCG).

def_eliminate_if_element(=,_,CG,_,TSet,TSet,CG).
def_eliminate_if_element(<,_G,CG,Elem,TSet,NewTSet,NewCG):-
    def_eliminate_if_element(CG,Elem,TSet,NewTSet,NewCG).
def_eliminate_if_element(>,G,CG,Elem,[Elem|TSet],TSet,[G|CG]).

%% collect_vars_set([],[]).
%% collect_vars_set([(X,_)|Xs],[X|VS1]):-
%%      collect_vars_set(Xs,VS1).
%% 
%% 
%% def_minimize_set([],[]).
%% def_minimize_set([(X,SS)|TempS],[(X,NewSS)|NewS]):-
%%      def_minimize_each(SS,[],NewSS),
%%      def_minimize_set(TempS,NewS).
%% 
%% %-------------------------------------------------------------------------
%% % decide_propagate(+,+,+,-)
%% % decide_propagate(Set,Ground,Lambda,NewLambda)
%% % This predicate propagates the abstract information provided by
%% % Set (the set of (X,SS) such that SS has changed) and Ground (the new set 
%% % of Ground variables) to Lambda. Note that Lambda has already all
%% % the information of Set and Ground but it has not be simplified.
%% %  - If Set = [], The only onformation that has to be propagated is the 
%% %    groundness of the variables in Ground (by calling propagate/5)
%% %  - If Ground = [], the only information that has to be propagated 
%% %    is the relationships in Set  (by calling propagate_inf/3)
%% %  - Otherwise, Let Lambda = a (G,T,S)
%% %         - It first propagates the Groundness in Ground to S until 
%% %           fixpoint, obtaining a semi-simplified TempS and the total set
%% %           of variables which have becomed ground TempG
%% %         - Then it computes Changed, the set of (X,SS) in TempS s.t.
%% %           there exists (X,SS1) in S SS1 different from SS
%% %         - It updates Set with Changed, obtaining NewSet
%% %         - propagates the information in NewSet to TempS obtaining NewS
%% %         - Obtains the final set of Ground variables NewG = TempG union G
%% %-------------------------------------------------------------------------
%% 
%% decide_propagate([],[],Lambda,Lambda):- !.
%% decide_propagate([],Ground,Lambda,NewLambda):- !,
%%      Lambda = a(G,S),
%%      propagate(Ground,S,Ground,NewS,TempG),
%%      merge(TempG,G,NewG),
%%      NewLambda = a(NewG,NewS).
%% decide_propagate(Set,[],Lambda,NewLambda):- !,
%%      Lambda = a(G,S),
%%      propagate_inf(Set,S,NewS),
%%      NewLambda = a(G,NewS).
%% decide_propagate(Set,Ground,Lambda,NewLambda):- 
%%      Lambda = a(G,S),
%%      propagate(Ground,S,Ground,TempS,TempG),
%%      def_diff(TempS,S,Changed),
%%      update_changed(Changed,Set,NewSet),
%%      propagate_inf(NewSet,TempS,NewS),
%%      merge(TempG,G,NewG),
%%      NewLambda = a(NewG,NewS).

%-------------------------------------------------------------------------
% propagate(+,+,+,-,-)
% propagate(G1,S,G,NewS,NewG)
% The first argument is the set of variables which are now ground.
% This predicate will propagate the groundness information to the set 
% component (S) of an abstract constraint, obtaining the simplified 
% abstract constraint NewS and the total set of Ground variables NewG
% This will be done iteratively, until fixpoint (no new variables have
% becomed ground) is reached.
% In each iteration, for each (Y,Ty) in S:
%       - Obtains NewTy:
%           * "g" if exists S in Ty s.t. S subseteq G1
%           * {(S minus G1) | for all S in Ty}
%       - If NewTy is "g", X is added to NewG
%       - Otherwise it (X,NewTy) is added to NewS
%-------------------------------------------------------------------------

propagate([],S,G,S,G):- !.
propagate(G1,S,G,NewS,NewG):-
    propagate_set(S,G1,TempS,NewG1),
    merge(NewG1,G,NewG2),
    propagate(NewG1,TempS,NewG2,NewS,NewG).

% propagate_set(+,+,-,-).
propagate_set([],_,[],[]).
propagate_set([(Y,Ty)|Lambda],G,Templ,NewG):- 
    eliminate_if_member(Ty,G,[],NewTy,_),
    decide_newground(NewTy,Y,Rest,G,NewG,G1,Templ,NewTempl),
    propagate_set(Lambda,G1,NewTempl,Rest).

%eliminate_if_member(+,+,+,-).
eliminate_if_member([],_G,Ty,NewTy,Flag):- !,
    sort(Ty,Ty_sorted),
    (var(Flag) ->
       NewTy = Ty_sorted
    ; def_minimize_each(Ty_sorted,[],NewTy)
    ).
eliminate_if_member([X|Xs],G,Ty,NewTy,Flag):-
    ord_subtract_flag(X,G,NonG,Flag), NonG \== [],!,
    eliminate_if_member(Xs,G,[NonG|Ty],NewTy,Flag).
eliminate_if_member(_,_G,_Ty,g,_).

% decide_newground(+,+,+,+,-,-).
decide_newground(g,Y,Rest,G,NewG,G1,Templ,Templ):- !,
        NewG = [Y|Rest],
        insert(G,Y,G1).
decide_newground(Ty,Y,Rest,G,Rest,G,[(Y,Ty)|Templ],Templ).

%% %-------------------------------------------------------------------------
%% % update_changed(+,+,-)
%% % update_changed(NonGround,Set,NewNonGround)
%% % It replaces those elements (X,Tx) in Set such that (X,Ty) in NonGround
%% % by (X,Ty), letting unchanged those for which there is no (X,_) in NonGround
%% %-------------------------------------------------------------------------
%% 
%% update_changed(NonGround,[],NonGround):- !.
%% update_changed([],Changed,Changed).
%% update_changed([(X,Tx)|Tl1],[(Y,Ty)|Tl2],New_NonGround):-
%%      compare(Ord,X,Y),
%%      update_changed(Ord,(X,Tx),Tl1,(Y,Ty),Tl2,New_NonGround).
%% 
%% %update_non_groun(+,+,+,+,+,-)
%% update_changed(<,Hd1,[],Hd2,Tl2,[Hd1,Hd2|Tl2]):- !.
%% update_changed(<,Hd1,[(X,Tx)|Tl1],(Y,Ty),Tl2,[Hd1|New_NonGround]):-
%%      compare(Ord,X,Y),
%%      update_changed(Ord,(X,Tx),Tl1,(Y,Ty),Tl2,New_NonGround).
%% update_changed(>,Hd1,Tl1,Hd2,[],[Hd2,Hd1|Tl1]):- !.
%% update_changed(>,(X,Tx),Tl1,Hd2,[(Y,Ty)|Tl2],[Hd2|New_NonGround]):-
%%      compare(Ord,X,Y),
%%      update_changed(Ord,(X,Tx),Tl1,(Y,Ty),Tl2,New_NonGround).
%% update_changed(=,_Hd1,Tl1,Hd2,Tl2,[Hd2|New_NonGround]):-
%%      update_changed(Tl1,Tl2,New_NonGround).

%-------------------------------------------------------------------------
% propagate_inf(+,+,-).
% propagate_inf(Set1,Set2,UpdatedSet).
% It propagates the information contained in each (X,Tx) in the first 
% argument to the second argument. In doing this it will traverse Set1
% propagating the information of each element, obtaining the new 
% changed elements, updating the rest of changed elements ,and so on,
% until no new elements are found. In each iteration 
% and for each (X,Tx) in Set1 and each (Y,Ty) in Set2:
%      - if X == Y, (X,Tx) is added to TempSet, and nothing is added to
%        the list of changed elements
%      - Otherwise, it collects the set of S in Ty which contain X,
%        obtaining ContainedX. If Contained X is [], (Y,Ty) is added
%        to TempSet and nothing changes. Otherwise:
%           * collects the set of S' in Tx which does not contain Y
%           * performs the pairwise union of S and S' and then
%             eliminates the supersets, obtaining NewTy, (Y,NewTy) is 
%             added to TempSet
%           * If NewTy \==  Ty (Y,NewTy) is added to the list of changed,
%-------------------------------------------------------------------------

propagate_first_to_sec(X,Tx,Y,Ty,TmpTy,Flag):-
    X == Y,!,
    compare(Order,Tx,Ty),
    def_add_element(Order,Tx,Ty,TmpTy,Flag).
propagate_first_to_sec(X,Tx,Y,Ty,TmpTy,_):-
    split_lists_without(Ty,X,ContainedX), 
    def_decide_propagate1(ContainedX,Y,Ty,Tx,TmpTy).

def_decide_propagate1([],_,Tx,_,Tx):- !.
def_decide_propagate1(ContainedY,X,Tx,Ty,NewTx):-
    split_lists(Ty,X,NotContainX),
    def_pairwise_union_no_supersets(ContainedY,NotContainX,Tx,NewTx).

%% propagate_inf([],S2,S2).
%% propagate_inf([(Y,Ty)|Xs],S2,UpdatedS2):-
%%      propagate_each(S2,Y,Ty,Temp_S2,Changed),
%%      update_changed(Xs,Changed,New_Xs),
%%      propagate_inf(New_Xs,Temp_S2,UpdatedS2).
%% 
%% propagate_each([],_Y,_Ty,[],[]).
%% propagate_each([(X,Tx)|S2],Y,Ty,[(X,Tx)|Temp_S2],Changed):-
%%      X == Y,!,
%%      propagate_each(S2,Y,Ty,Temp_S2,Changed).
%% propagate_each([(X,Tx)|S2],Y,Ty,[(X,NewTx)|Temp_S2],Changed):- 
%%      split_lists_without(Tx,Y,ContainedY), 
%%      def_decide_propagate(ContainedY,X,Tx,Ty,NewTx,Changed,Rest),
%%      propagate_each(S2,Y,Ty,Temp_S2,Rest).
%% 
%% def_decide_propagate([],_,Tx,_,Tx,Changed,Changed):- !.
%% def_decide_propagate(ContainedY,X,Tx,Ty,NewTx,Changed,Rest):-
%%      split_lists(Ty,X,NotContainX),
%%      def_pairwise_union_no_supersets(ContainedY,NotContainX,Tx,NewTx),
%%      ( NewTx == Tx ->
%%           Changed = Rest
%%      ; Changed = [(X,NewTx)|Rest]
%%         ).

%-------------------------------------------------------------------------
% def_pairwise_union_no_supersets(+,+,+,-)
% The first (Ty) and second (Tx) argument are list of lists of variables 
% (at least each element of each list is ordered). Forall Sy in Ty and 
% Sx in Tx, we will obtain the union (Merged) of them and then we will 
% call merge_no_supersets(Merged, Temp1, Temp2) which obtains in Temp2 the 
% result of adding Merged to Temp1 and eliminating supersets.
%-------------------------------------------------------------------------

def_pairwise_union_no_supersets([],_,Product,Product):- !.
def_pairwise_union_no_supersets(_,[],Product,Product):- !.
def_pairwise_union_no_supersets(Ty,Tx,Temp,New):-
    def_merge(Tx,Ty,Merged),
    sort(Merged,NewMerged),
    def_minimize_each(NewMerged,Temp,New).

def_merge([],_,[]).
def_merge([Y|Ys],X,Merged):-
    def_merge_each(X,Y,Merged,Rest),
    def_merge(Ys,X,Rest).

def_merge_each([],_Y,X,X).
def_merge_each([X|Tx],Y,[Merge|Merged],Rest):-
    merge(X,Y,Merge),
    def_merge_each(Tx,Y,Merged,Rest).

def_minimize_each([],Temp,Temp).
def_minimize_each([M|Merged],Temp,New):-
    def_no_subset(Temp,M,NewTemp,Flag),
    decide_minimized(Flag,NewTemp,M,Temp1),
    def_minimize_each(Merged,Temp1,New).

%% %-------------------------------------------------------------------------
%% % put_value(+,-,+)
%% % it transforms the ordered list of variables given as first argument into
%% % an ordered list of couples (Var, Value) in which Var is an element of 
%% % the first argument and Value is the third argument
%% %-------------------------------------------------------------------------
%% 
%% put_value([],[],_Value).
%% put_value([X|Xs],[(X,Value)|Rest],Value):-
%%      put_value(Xs,Rest,Value).
%% 
%% %-------------------------------------------------------------------------
%% % def_diff (+,+,-)
%% % It receives as input two abstract constraints (first and second arguments)
%% % and  returns in the third argument the list of elements in the second
%% % argument which have changed w.r.t. the first one
%% % We assume both abstract constraints be ordered and defined over the same 
%% % set of variables
%% %-------------------------------------------------------------------------
%% 
%% def_diff([],_,[]).
%% def_diff([(X,Vx)|Lambda],[(Y,Vy)|Temp_Lambda],Changed):-
%%      compare(Order,X,Y),
%%      def_diff(Order,(X,Vx),Lambda,(Y,Vy),Temp_Lambda,Changed).
%% 
%% def_diff(=,Elem,Lambda,_,Temp_Lambda,[Elem|Changed]):-
%%      def_diff(Lambda,Temp_Lambda,Changed).
%% def_diff(>,(X,Tx),Lambda,_,[(Y,Ty)|Temp_Lambda],Changed):-
%%      compare(Order,X,Y),
%%      def_diff(Order,(X,Tx),Lambda,(Y,Ty),Temp_Lambda,Changed).

%-------------------------------------------------------------------------
% def_project_each(+,+,-)
% It eliminates from the ordered set of sets of variables given as first 
% argument those which are not subsetseq of the ordered list of variables 
% given as second argument. Nothing (aside the order) is asumed about the 
% first and second argument.
%-------------------------------------------------------------------------

def_project_each([],_Vars,[]).
def_project_each([Set|Rest],Vars,NewSet):-
    ord_subset(Set,Vars),!,
    NewSet = [Set|RestNewSet],
    def_project_each(Rest,Vars,RestNewSet).
def_project_each([_Set|Rest],Vars,NewSet):-
    def_project_each(Rest,Vars,NewSet).
    
%-------------------------------------------------------------------------
%split_lists_without(+,+,-)
% It returns the elements of the list of lists given as second argument 
% which contain X but eliminating X from them. Note that eliminating X 
% from [[X]] will give [[]] instead of []
%-------------------------------------------------------------------------

split_lists_without([],_X,[]).
split_lists_without([L|Ls],X,ContainedX):-
    L = [Y|Ys],
    compare(Order,X,Y),
    delete_if_member1(Order,Y,Ys,X,L1,Flag),
    def_decide_split(Flag,X,L1,Ls,ContainedX).

%delete_if_member1(+,+,+,+,-,-)
delete_if_member1(<,_Y,_Ys,_X,_Ys,end).
delete_if_member1(=,_Y,Ys,_X,Ys,yes).
delete_if_member1(>,Y,Ys,X,[Y|Rest],Flag):-
    delete_if_member(Ys,X,Rest,Flag).
    
%delete_if_member(+,+,-,-)
delete_if_member([],_X,_NewYs,no).
delete_if_member([Y|Ys],X,NewYs,Flag):-
    compare(Order,X,Y),
    delete_if_member(Order,Y,Ys,X,NewYs,Flag).

%delete_if_member(+,+,+,+,-,-)
delete_if_member(<,_Y,_Ys,_X,_Ys,no).
delete_if_member(=,_Y,Ys,_X,Ys,yes).
delete_if_member(>,Y,Ys,X,[Y|Rest],Flag):-
    delete_if_member(Ys,X,Rest,Flag).
    
%def_decide_split(+,+,+,+,-)
def_decide_split(end,_X,_L1,_Ls,[]).
def_decide_split(yes,X,L1,Ls,[L1|ContainedX]):-
    split_lists_without(Ls,X,ContainedX).
def_decide_split(no,X,_L1,Ls,ContainedX):-
    split_lists_without(Ls,X,ContainedX).

%-------------------------------------------------------------------------
%split_lists(+,+,-,)
% Returns those elements in the list of lists given as first argument 
% which do not contain X (Not necessarily Ordered).
%-------------------------------------------------------------------------

%% split_lists([],_,[]).
%% split_lists([[LH|LT]|Ls],X,List2):-
%%      LH @> X,!,
%%      List2 = [[LH|LT]|Ls].
%% split_lists([L|Ls],X,List2):-
%%      myord_subset([X], L),!,
%%      split_lists(Ls,X,List2).
%% split_lists([L|Ls],X,[L|List2]):-
%%      split_lists(Ls,X,List2).

split_lists([],_,[]).
split_lists([[LH|LT]|Ls],X,List2):-
    compare(Order,LH,X),
    split_lists_each(Order,LH,LT,Ls,X,List2).

split_lists_each(=,_LH,_LT,Ls,X,List2):-
    split_lists(Ls,X,List2).
split_lists_each(>,LH,LT,Ls,_X,List2):-
    List2 = [[LH|LT]|Ls].
split_lists_each(<,_LH,LT,Ls,X,List2):-
    ord_subset([X], LT),!,
    split_lists(Ls,X,List2).
split_lists_each(<,LH,LT,Ls,X,[[LH|LT]|List2]):-
    split_lists(Ls,X,List2).

%-------------------------------------------------------------------------
% Split the list of lists in the first argument into two lists: in
% the third argument gives the lists containing X, in the fourth
% argument gives the lists which do not contain X (Ordered)

ord_disjunction_merge([],X,[],X) :- !.
ord_disjunction_merge(X,[],X,X) :- !.
ord_disjunction_merge([Hd1|Tail1],[Hd2|Tail2],Disjunct,Merge) :-
    compare(Order,Hd1,Hd2),
    ord_disjunction_merge(Order,Hd1,Tail1,Hd2,Tail2,Disjunct,Merge).

ord_disjunction_merge(<,H1,[],H2,T2,Disjunct,Merge) :- !,
    Disjunct = [H1],
    Merge = [H1,H2|T2].
ord_disjunction_merge(<,H1,[Hd1|Tail1],Hd2,Tail2,[H1|Disjunct],[H1|Merge]) :-
    compare(Order,Hd1,Hd2),
    ord_disjunction_merge(Order,Hd1,Tail1,Hd2,Tail2,Disjunct,Merge).
ord_disjunction_merge(=,Hd,Tail1,_,Tail2,Disjunct,[Hd|Merge]) :-
    ord_disjunction_merge(Tail1,Tail2,Disjunct,Merge).
ord_disjunction_merge(>,H1,T1,H2,[],Disjunct,Merge) :- !,
    Disjunct = [H1|T1],
    Merge= [H2,H1|T1].
ord_disjunction_merge(>,Hd1,Tail1,H2,[Hd2|Tail2],Disjunct,[H2|Merge]) :-
    compare(Order,Hd1,Hd2),
    ord_disjunction_merge(Order,Hd1,Tail1,Hd2,Tail2,Disjunct,Merge).

%-------------------------------------------------------------------------
% def_minimize(+,+,-)
% Identical to merge_no_supersets but simpler. Useful when Tx or Ty are 
% singletons (i.e. when it is called from def_minimize_each
%-------------------------------------------------------------------------

decide_minimized(superset,Tx,_X,Tx).
decide_minimized(nosuperset,Tx,X,Minimized):-
    insert(Tx,X,Minimized).

%-------------------------------------------------------------------------
%def_no_subset(+,+,-,-)
% def_no_subset(Ty,X,NewTy,Flag):-
% It receives a set of sets of ordered variables Ty, and a set of ordered
% variables X. 
%  * If there exists Y in Ty, s.t. X superseteq Y, then NewTy=Ty, 
%    Flag=superset
%  *If there exists Y in Ty, s.t. Y is superset X then NewTy=Ty\Y, 
%   Flag = nosuperset
%  *Otherwise NewTy=Ty,  Flag = nosuperset
%-------------------------------------------------------------------------

%% def_no_subset([],_X,[],nosuperset).
%% def_no_subset([Y|Ty],X,TY,Flag):-
%%      compare(Order,X,Y),
%%      def_no_subset(Order,Y,Ty,X,TY,Flag).
%% 
%% def_no_subset(=,_Y,_Ty,_X,_TY,superset). 
%% def_no_subset(<,Y,Ty,X,TY,Flag):-
%%      myord_intersect(Y,X,Intersect),
%%      compare(Order,Y,Intersect),
%%      def_decide_temp(Order,X,Y,Intersect,Ty,TY,Flag).
%% def_no_subset(>,Y,Ty,X,TY,Flag):-
%%      myord_intersect(Y,X,Intersect),
%%      compare(Order,Y,Intersect),
%%      def_decide_temp(Order,X,Y,Intersect,Ty,TY,Flag).
%% 
%% def_decide_temp(=,_X,_Y,_Intersect,_Ty,_TY,Flag):- 
%%      Flag = superset.
%% def_decide_temp(<,X,Y,Intersect,Ty,TY,Flag):-
%%      compare(Order,X,Intersect),
%%      def_decide_temp_x(Order,X,Y,Ty,TY,Flag).
%% def_decide_temp(>,X,Y,Intersect,Ty,TY,Flag):-
%%      compare(Order,X,Intersect),
%%      def_decide_temp_x(Order,X,Y,Ty,TY,Flag).
%% 
%% def_decide_temp_x(=, X,_Y,Ty,TY,Flag):- 
%%      def_no_subset(Ty,X,TY,Flag).
%% def_decide_temp_x(<,X,Y,Ty,[Y|TY],Flag):-
%%      def_no_subset(Ty,X,TY,Flag).
%% def_decide_temp_x(>,X,Y,Ty,[Y|TY],Flag):-
%%      def_no_subset(Ty,X,TY,Flag).


def_no_subset([],_X,[],nosuperset).
def_no_subset([Y|Ty],X,TY,Flag):-
    X == Y,!,
    TY = [Y|Ty],
    Flag = superset.
def_no_subset([Y|Ty],X,TY,Flag):-
    dmyord_superset(Y,X,Order),
    def_decide_temp(Order,X,Y,Ty,TY,Flag).

def_decide_temp(nosuperset,X,Y,Ty,[Y|TY],Flag):- 
    def_no_subset(Ty,X,TY,Flag).
def_decide_temp(superset2,_X,Y,Ty,[Y|Ty],superset).
def_decide_temp(superset1,X,_Y,Ty,TY,Flag):-
    def_no_subset(Ty,X,TY,Flag).


dmyord_superset([],_,superset2):- !.
dmyord_superset(_,[],superset1):- !.
dmyord_superset([Y|Ty],[X|Tx],Flag):-
    compare(Order,Y,X),
    dmyord_superset(Order,Y,Ty,X,Tx,Flag).

dmyord_superset(=,_Y,Ty,_X,Tx,Flag):-
    dmyord_superset(Ty,Tx,Flag).
dmyord_superset(<,_Y,Ty,X,Tx,Flag):-
    dmyord_subset_1(Ty,[X|Tx],Flag).
dmyord_superset(>,Y,Ty,_X,Tx,Flag):-
    dmyord_subset_2([Y|Ty],Tx,Flag).

dmyord_subset_1(_,[],superset1):- !.
dmyord_subset_1([],_,nosuperset):- !.
dmyord_subset_1([Y|Ty],[X|Tx],Flag):-
    compare(Order,Y,X),
    dmyord_subset_1(Order,Y,Ty,X,Tx,Flag).

dmyord_subset_1(=,_Y,Ty,_X,Tx,Flag):-
    dmyord_subset_1(Ty,Tx,Flag).
dmyord_subset_1(<,_Y,Ty,X,Tx,Flag):-
    dmyord_subset_1(Ty,[X|Tx],Flag).
dmyord_subset_1(>,_Y,_Ty,_X,_Tx,nosuperset).

dmyord_subset_2([],_,superset2):- !.
dmyord_subset_2(_,[],nosuperset):- !.
dmyord_subset_2([Y|Ty],[X|Tx],Flag):-
    compare(Order,Y,X),
    dmyord_subset_2(Order,Y,Ty,X,Tx,Flag).

dmyord_subset_2(=,_Y,Ty,_X,Tx,Flag):-
    dmyord_subset_2(Ty,Tx,Flag).
dmyord_subset_2(>,Y,Ty,_X,Tx,Flag):-
    dmyord_subset_2([Y|Ty],Tx,Flag).
dmyord_subset_2(<,_Y,_Ty,_X,_Tx,nosuperset).


%-------------------------------------------------------------------------
% def_decide_arg(+,+,+,+,+,-)
% def_decide_arg(T,Vars,Y,Z,Call,Succ)
%-------------------------------------------------------------------------

def_decide_arg([],Vars,Y,Z,Call,Succ):- !,
    def_conjunct_constr(a(Vars,[(Z,[[Y]])]),Call,Succ).
def_decide_arg([X],Vars,Y,Z,Call,Succ):-
    X == Y,!,
    merge([Z],Vars,Ground),
    def_conjunct_constr(a(Ground,[]),Call,Succ).
def_decide_arg(_,Vars,_Y,_Z,Call,Succ):- 
    def_conjunct_constr(a(Vars,[]),Call,Succ).


ord_subtract_flag([], _, [],_) :- !.
ord_subtract_flag(Set1, [], Set1,_) :- !.
ord_subtract_flag([Head1|Tail1], [Head2|Tail2], Difference,Flag) :-
    compare(Order, Head1, Head2),
    ord_subtract_flag(Order, Head1, Tail1, Head2, Tail2, Difference,Flag).

ord_subtract_flag(<, Head1, [], _, _, [Head1],_) :- !.
ord_subtract_flag(<, Head0, [Head1|Tail1], Head2, Tail2, [Head0|Difference],Flag) :-
    compare(Order, Head1, Head2),
    ord_subtract_flag(Order, Head1, Tail1, Head2, Tail2, Difference,Flag).
ord_subtract_flag(=, _, Tail1, _, Tail2, Difference,yes) :-
    ord_subtract_flag(Tail1, Tail2, Difference,_).
ord_subtract_flag(>, Head1, Tail1, _, [], [Head1|Tail1],_) :- !.
ord_subtract_flag(>, Head1, Tail1, _, [Head2|Tail2], Difference,Flag) :-
    compare(Order, Head1, Head2),
    ord_subtract_flag(Order, Head1, Tail1, Head2, Tail2, Difference,Flag).

:- pop_prolog_flag(multi_arity_warnings).
