:- module(_, [], [ciaopp(ciaopp_options)]).

%! \title Optional interface to PPL
:- if(defined(has_ciao_ppl)).
:- reexport(library(ppl)).
:- else.
:- reexport(domain(ppl_dummy)).
:- endif.

