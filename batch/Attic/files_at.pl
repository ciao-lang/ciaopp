:- use_module(library(pathnames), [path_concat/3]).

main([Path]) :- store_all_ciao_files(Path).

store_all_ciao_files(Path) :-
    related_files_at(Path, Files),
    store_file_data(Files).

store_file_data([File|Files]) :-
    portray_clause(File),
    store_file_data(Files).
store_file_data([]).


related_files_at(Dir,Files) :-
    directory_files(Dir,AllFiles),
    related_files_at_aux(AllFiles,Dir,Files).

related_files_at_aux([],_,[]).
related_files_at_aux(['.'|Nf],Dir,NNf) :-
    !,
    related_files_at_aux(Nf,Dir,NNf).
related_files_at_aux(['..'|Nf],Dir,NNf) :-
    !,
    related_files_at_aux(Nf,Dir,NNf).
related_files_at_aux([File|Nf],Dir,NNf) :-
    atom_concat('.#',_,File),
    !,
    related_files_at_aux(Nf,Dir,NNf).
related_files_at_aux([File|Nf],Dir,[pl(AbsFile,Module)|NNf]) :- % A structure pl(path, modname) es created
    atom_concat(Module,'.itf',File),
    !,
    path_concat(Dir,File,AbsFile),
    related_files_at_aux(Nf,Dir,NNf).
related_files_at_aux([File|Nf],Dir,RelatedFiles) :-
    path_concat(Dir,File,AbsFile),
    is_dir_nolink(AbsFile),
%       file_property(AbsFile,type(directory)),
    !,
    related_files_at_aux(Nf,Dir,NNf),
    related_files_at(AbsFile, NewFiles),
    append(NNf,NewFiles,RelatedFiles).
related_files_at_aux([_|Nf],Dir,NNf) :-
    !,
    related_files_at_aux(Nf,Dir,NNf).

% TODO: copied from source_tree.pl, fix
% FileName is a directory that is not a symbolic link
is_dir_nolink(FileName) :-
    \+ file_property(FileName, linkto(_)),
    file_exists(FileName),
    file_property(FileName, type(directory)).

% The analysis of each module is stored in a local file
analyze_all(Path) :-
    related_files_at(Path, Files),
%       telling(File),
%       told,
%       tell('analysis.txt'),
    analyze_files(Files).
%       told,
%       tell(File) .

analyze_files([File|Files]) :-
    analyze_single_file(File),
    analyze_files(Files).
analyze_files([]).
