:- package(aidomain).
% Helper package to write AI domains

:- discontiguous(aidomain/1).

:- load_compilation_module(library(aidomain/aidomain_tr)).
:- add_sentence_trans(aidomain_tr:treat_sent/3, 310).
