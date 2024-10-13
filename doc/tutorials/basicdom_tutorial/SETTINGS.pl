:- module(_, [], [doccfg]).

filepath := '..'. 

doc_structure := 'tut'-
    [
        'sign',
        'polyhedra_clpq'
    ].

commonopts := no_patches|no_bugs|no_biblio.
doc_mainopts := ~commonopts.
doc_compopts := ~commonopts.

% TODO: enable by default?
syntax_highlight := yes.
