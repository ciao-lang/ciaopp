:- module(s_simpspec,
    [ body2list/2,
      list2body/2,
      p_exp2list/2,
      next_pred/2,
%%        next_key/2,
%%        last_key/2,
      next_or_last_key/3,
      list_format/2,
      newformat/2
    ],
    [assertions,isomodes]).

:- use_module(ciaopp(p_unit/program_keys), [decode_litkey/5, make_atom/2]).

:- op( 950, xfy,[(&),(\&)]).

:- use_module(engine(messages_basic), [message/2]).

%-------------------------------------------------------------------%
% list2body(+,-)                                                    %
% list2body(List,Body)                                              %
%  Body corresponds to the list of goals List. An element of List   %
% may be in turn another list. This indicates that is a list of     %
% parallel goals.                                                   %
%-------------------------------------------------------------------%
list2body([],true).
list2body([Last],NewLast):-!,
    list2p_exp(Last,NewLast).
%list2body([First,(error:'$bottom')],NewFirst):- %this two lines avoid 
 %       list2p_exp(First,NewFirst). % displaying error literals
list2body([First|Rest],(NewFirst,More)):-
    list2p_exp(First,NewFirst),
    list2body(Rest,More).

%-------------------------------------------------------------------%
% list2p_exp(+,-)                                                   %
% list2p_exp(List,Parall_expression)                                %
%  Transforms a list of goals into a structure where goals are to   %
% be executed in parallel (separated with &)                        %
%-------------------------------------------------------------------%
list2p_exp([],(true:true)).  % dangerous. true does not have id...
list2p_exp([Last],Last):-!.
list2p_exp([First|Rest],(First & More)):-!,
    list2p_exp(Rest,More).
list2p_exp(Goal,Goal).

%-------------------------------------------------------------------%
% body2list(+,-)                                                    %
% body2list(Body,List)                                              %
%  Transform the body of a clause into a list of goals              %
%-------------------------------------------------------------------% 
body2list((First,Rest),[NewFirst|More]):-
    !,
    p_exp2list(First,NewFirst),
    body2list(Rest,More).
body2list(Last,[NewLast]):-
    p_exp2list(Last,NewLast).

%-------------------------------------------------------------------%
% p_exp2list(+,-)                                                   %
% p_exp2list(Parall_expression,List)                                %
%  Transform a set of parallel goals to a list of goals             %
%-------------------------------------------------------------------%
p_exp2list((G & Goals),[G|More]):-!,
    p_exp2listlist(Goals,More).
p_exp2list(Goal,Goal).

p_exp2listlist((G & Goals),[G|More]):-
    p_exp2listlist(Goals,More).
p_exp2listlist(Goal,[Goal]).


%-------------------------------------------------------------------%
% next_pred(+,-)                                                    %
% next_pred(Goals,Pred)                                             %
%  Pred is the functor of the first goal of the list of goals Goals %
%-------------------------------------------------------------------%
next_pred([(Goal:_)|_],N/A):-!,
    functor(Goal,N,A).
next_pred([Goal|_],N/A):-
    functor(Goal,N,A).
next_pred([],none).

%% GP: not needed any longer!
%% :- pred next_key(+atm(K),-atm(K1)) # "@tt{K1} is the key of the
%% literal following the one with key @tt{K}.".
%% 
%% next_key(K,K1):-
%%      decode_litkey(K,P,A,C,G),
%%         G1 is G+1,
%%      make_atom([P,A,C,G1],K1).
%% 
:- pred last_key(K,K1) : atm(K) => atm(K1)
    # "@tt{K1} is the key for the end of the clause to which @tt{K} belongs.".
last_key(K,K1):-
    decode_litkey(K,P,A,C,_G),
    make_atom([P,A,C],K1).

:- pred next_or_last_key(Goals,K,K1) : (list(Goals), atm(K)) => atm(K1)
    # "@tt{K1} is the key for the end of the clause to which @tt{K} belongs
     if @tt{Goals} is empty or the key for the next literal otherwise.".
next_or_last_key([],K,K1):-
    last_key(K,K1).
next_or_last_key([(_:GK)|_],_K,K1):-
    !,
    K1 = GK.
next_or_last_key([!|Body],K,K1):-
    !,
    next_or_last_key(Body,K,K1).
next_or_last_key([A|_],_,_):-
    message( error , ['INTERNAL ERROR: next_or_last_key: in ' , A] ),
    fail.

%-------------------------------------------------------------------%
% list_format(+,-)                                                  %
% this transformation in usually done by simplify_prog/5, but as we %
% do not want any simplifications in spmodes, we must do it explici-%
% tly                                                               %
%-------------------------------------------------------------------%
list_format([],[]).
list_format([directive(Dir):Id|Cs],[directive(Dir):Id|SCs]):-
    list_format(Cs,SCs).
list_format([clause(H,true):Clid|Cs],[clause(H,[]):Clid|SCs]):-
    list_format(Cs,SCs).
list_format([clause(H,Body):Clid|Cs],[clause(H,NewBody):Clid|SCs]):-
    body2list(Body,NewBody),
    list_format(Cs,SCs).

%% -----------------------------------------------------------------------


%-------------------------------------------------------------------%
% newformat(+,-)                                                    %
% newformat(Program,NewProgram)                                     %
%  NewProgram is Program but in the original format.  This is       %
% necessary because simplify_prog transforms bodys of clauses       %
% into lists of goals                                               %
%-------------------------------------------------------------------%
newformat([],[]).
newformat([directive(D):Id|Cs],[directive(D):Id|SCs]):-
    newformat(Cs,SCs).
newformat([clause(Head,Body):Clid|Cs],[clause(Head,NewBody):Clid|SCs]):-
    list2body(Body,NewBody),
    newformat(Cs,SCs).
