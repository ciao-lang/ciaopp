:- module(ciaopp_log,[pplog/2],[assertions, isomodes]).

:- doc(title, "Logging of internal CiaoPP events/actions").

:- use_module(engine(messages_basic), [message/2]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).

:- pred pplog(+Group, +Message) : atm * list
   #"Prints a message if the @var{Group} is activated in the @tt{pp_flag} @tt{pplog}.".
pplog(Group, Message) :- %% flag to display the module?
    current_pp_flag(pplog, L),
    member(Group, L), !,
    message(inform, Message).
pplog(_, _).
