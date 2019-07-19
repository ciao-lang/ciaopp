:- module(itf_base_db, _, [assertions, datafacts]).

% TODO: no doc

:- data defines/3, imports/2, exports/2, multifile/2, meta/2,
	dynamic/1.
:- data curr_module/1.
:- data curr_file/2.
:- data impl_defines/2.
:- data defines_module/2, defines_module_rev_idx/2.
% IG added reverse index
