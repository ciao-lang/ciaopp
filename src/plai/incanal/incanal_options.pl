:- use_package(ciaopp(plai/notrace)). % inhibits the tracing

%:- compilation_fact(rtchecks_incanal). %% uncomment to activate rtchecks in incanal

:- if(defined(rtchecks_incanal)).
:- use_package(rtchecks).
:- endif.
