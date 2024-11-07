% (Included file)

% Required: :- use_package(datafacts).

:- use_module(library(bundle/bundle_paths), [bundle_path/3]).

% % cache_persdb_dir.pl
% Define and cache persistent_dir/2 based on persdb_dir/1 and persdb_keyword/1
% persistent_dir(to_analyze_db, '../data').
persistent_dir(Keyword, Dir) :-
    persdb_keyword(Keyword),
    !,
    ensure_persistent_dir(Dir).

:- data curr_persistent_dir/1.
ensure_persistent_dir(Dir) :-
    ( curr_persistent_dir(Dir) -> true
    ; persdb_dir(Dir),
      datafacts_rt:assertz_fact(curr_persistent_dir(Dir))
    ).

update_persdb :-
    update_files.

% TODO: fix this. It is not the proper way of synchronizing (very inefficient)
update_localdb :-
    persdb_keyword(K),
    persdb_data(P),
    ensure_persistent_dir(Dir),
    datafacts_rt:asserta_fact(persistent_dir(K, Dir)), % needed for reloading
    persdb_rt:make_persistent(P, K). % reload facts from persistent db
