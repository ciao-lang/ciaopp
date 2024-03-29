:- module(_, [], [doccfg, ciaopp(ciaopp_options)]).

:- include(ciaopp_docsrc(docpaths)).

output_name := 'ciaopp_tutorials'.

doc_structure :=
    ciaopp_tutorials-[
        quick_start,
        tut_gentle_intro,
        tut_assrts,
        tut_advanced
    ].

% TODO: port this manual
allow_markdown := yes.
syntax_highlight := yes.
allow_runnable := yes.

% (extensions)
load_doc_module := exfilter(exfilter_lpdoc).