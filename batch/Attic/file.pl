:- use_module(ciaopp(driver)).
:- use_module(library(write)).
:- use_module('/home/isa/Desktop/pruebas_ciao/try_analyze').


main(Path):-
    display('Analyzing...'), display(Path),  nl,
    module(Path),
    analyze(eterms),
    open('analyzed.pl', append, S),
    portray_clause(S, loaded_module(Path)).

store_all_ciao_files :-
    related_files_at('/home/isa/Desktop/ciao/ciao-devel/core/lib', Files),
    open('/home/isa/Desktop/all_files.pl', append, S),
    store_file_data(Files, S),
    close(S).

store_file_data([File|Files], S) :-
    portray_clause(S, File),
    store_file_data(Files, S).
store_file_data([],_).
