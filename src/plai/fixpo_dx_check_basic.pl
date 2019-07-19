:- module(fixpo_dx_check_basic, [advance_in_body/3], [assertions,isomodes,nativeprops]).

%------------------------------------------------------------------------
:- pred advance_in_body(+Ch_Key,+OldBody,-NewBody) : atm(Ch_Key) + not_fails
        #"@var{NewBody} is @var{OldBody} where the literals that do not need to
          be re-analyzed are removed. Then we can use @pred{entry_to_exit/7}
          with @var{NewBody}.".
advance_in_body(Ch_Key,g(Ch_Key,Vars,Info,SgKey,Sg),NewBody):-!,
	NewBody = g(Ch_Key,Vars,Info,SgKey,Sg).
advance_in_body(Ch_Key,(g(Ch_Key,Vars,Info,SgKey,Sg),Goals),NewBody):-!,
	NewBody = (g(Ch_Key,Vars,Info,SgKey,Sg),Goals).
advance_in_body(Ch_Key,(_,Goals),NewBody):-
	advance_in_body(Ch_Key,Goals,NewBody).
