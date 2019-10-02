:- package(aidomain).
% Helper package to write AI domains

:- load_compilation_module(library(aidomain/aidomain_tr)).
:- add_sentence_trans(aidomain_tr:dom_sent/3, 310).
