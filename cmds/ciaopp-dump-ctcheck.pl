:- module(_, [main/1], [assertions]).

:- doc(title, "Offline assertion checking using a dumped analysis").

:- doc(author, "Isabel Garcia-Contreras").

:- doc(summary, "This command loads one module and a dump file that contains the
                 analysis of the module and performs assertion checking.").

% TODO: dependencies may be refined but there are still strong
% dependencies among modules in ciaopp
:- use_module(ciaopp(ciaopp)).
:- use_module(ciaopp(frontend_driver), [module/1]).
:- use_module(ciaopp(ctchecks/ctchecks_pred), [simplify_assertions_all/1]).
:- use_module(ciaopp(p_unit/p_dump), [restore/1]).

main([Module,DumpFile,AbsInt]) :-
    module(Module),
    restore(DumpFile),
    assert_domain(AbsInt),
    simplify_assertions_all([AbsInt]).
