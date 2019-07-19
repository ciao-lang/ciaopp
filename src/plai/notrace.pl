:- package(notrace).

% TODO: uncertain priority: just disables some decls and goals
:- load_compilation_module(notrace_tr).
:- add_sentence_trans(notrace_tr:no_fixp_trace/2, 9010).
