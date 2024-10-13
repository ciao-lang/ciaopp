:- module(_, [], [assertions]).

%! \title Helper for creating new domains
%
% \module This module implements the utilities to generate a new
%   domain template.

:- use_module(engine(internals), [ciao_root/1]).
:- use_module(library(pathnames), [path_concat/3]).
:- use_module(engine(stream_basic), [open/3, close/1]).
:- use_module(library(stream_utils), [get_line/2, write_string/2]).
:- use_module(library(streams), [nl/1]).
:- use_module(library(write), [write/2]).
:- use_module(library(lists), [reverse/2]).
:- use_module(library(messages), [error_message/2,warning_message/2]).

:- export(new_domain/2).
new_domain(File, Kind) :-
    Kind == rel, !,
    open(File, write, Stream),
    get_plai_simpl(Kind, KindF), open(KindF, read, PlaiSimp),
    write_header(Kind, Stream),
    write_body(PlaiSimp, Stream, Kind, no),
    close(PlaiSimp),
    close(Stream).
new_domain(File, Kind) :-
    Kind == nonrel, !,
    open(File, write, Stream),
    get_plai_simpl(Kind, KindF), open(KindF, read, PlaiSimp),
    write_header(Kind, Stream),
    write_body(PlaiSimp, Stream, Kind, no),
    close(PlaiSimp),
    get_plai_simpl(rel, RelF), open(RelF, read, PlaiSimpRel),
    write_body(PlaiSimpRel, Stream, Kind, no),
    close(PlaiSimpRel), 
    close(Stream).

write_body(PlaiSimp, Stream, Kind, Flag) :-
    get_line(PlaiSimp, Line),
    ( Line = end_of_file -> true
    ; write_or_ignore(Flag, Line, Stream, Kind, NFlag),
      write_body(PlaiSimp, Stream, Kind, NFlag)        
    ).

write_or_ignore(Flag, Line, _Stream, Kind, NFlag) :-
    update_flag(Kind, Line, Flag, NFlag), !. %% If the flag is updated nothing has to be done
write_or_ignore(Flag, Line, Stream,_Kind, NFlag) :-
    Flag = yes, !,
    write_line(Line, Stream), nl(Stream), 
    NFlag = yes.
write_or_ignore(no, _Line, _Stream, _Kind, no). 
write_line(Line, Stream):-
    special_line(Line, NLine), !,
    write_string(Stream, NLine).

special_line("%&"||Xs, Xs).
special_line(Line, Line).

update_flag(rel, Line, Flag, NFlag) :-
    flag_code(Line), !,
    split_flag(Line, Point, Kind),
    ( Kind == 'rel' ; Kind == 'common' ), 
    ( Point == 'begin' ->
        NFlag = yes,
        ( Flag == yes ->
            warning_message("Open begin...", [])
        ; true
        )
    ; ( Point == 'end' ->
          NFlag = no
      ; error_message("Invalid update_flag", []),
        fail
      )
    ).      
update_flag(nonrel, Line, Flag, NFlag) :-
    flag_code(Line), !,
    split_flag(Line, Point, Kind),
    ( Kind == 'nonrel' ; Kind == 'common' ), 
    ( Point == 'begin' ->
        NFlag = yes,
        ( Flag == yes ->
            warning_message("Open begin...", [])
        ; true
        )
    ; ( Point == 'end' ->
          NFlag = no
      ; error_message("Invalid update_flag", []),
        fail 
      )
    ).      

:- use_module(engine(io_basic)).

split_flag("%#"||[_|Keep], Point, Kind) :-
    get_point(Keep, PointC, Rest),
    get_kind(Rest, KindC),
    atom_codes(Point, PointC),
    atom_codes(Kind, KindC).

get_kind([], []).
get_kind([X|_Xs], Kind) :-
    blank(X), !, Kind = [].
get_kind([X|Xs], Kind) :-
    Kind = [X|Kind_t],
    get_kind(Xs, Kind_t).

:- export(get_point/3).
get_point([X|Xs], Point, Rest) :-
    atom_codes('-', [X]), !,
    Point = [], Rest = Xs.
get_point([X|Xs], Point, Rest) :-
    Point = [X|Point_t],
    get_point(Xs, Point_t, Rest).

blank(0' ).
blank(0'\n).
blank(0'\t).

flag_code("%#"||_).

write_header(Type, Stream) :-
    write(Stream, ':- module(_, [], [assertions, regtypes, nativeprops, modes]).'), nl(Stream),   
    ( Type == rel -> 
        write(Stream, ':- include(domain(basicdom_base)).'), nl(Stream)
    ;
        write(Stream, ':- include(domain(basicdom_nonrel_base)).'), nl(Stream)
    ),
    write(Stream, ':- dom_def(_, [default]).'), nl(Stream).

:- use_module(library(bundle/bundle_paths), [bundle_path/3]).

get_plai_simpl(rel, File) :-
    bundle_path(ciaopp, 'domains/basicdom_base_doc.pl', File).
get_plai_simpl(nonrel, File) :-
    bundle_path(ciaopp, 'domains/basicdom_nonrel_base_doc.pl', File).

