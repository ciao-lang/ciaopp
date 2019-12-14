% (included file)

:- multifile typeslib_flag/1.
% typeslib_flag(Flag) where Flag is one of:
%
%   typedefs_simp:  Perform type simplification
%   use_deftypes:   Use retricted deftypes lattice
%   output_defined: Use defined types in simplify_step2

:- multifile typeslib_is_user_type/1.
% typeslib_is_user_type(+T): T is a user type

:- multifile typeslib_interesting_type/2.
% typeslib_interesting_type(+T, +Mode): T is an "interesting" type,
%   used in build_defined_types_lattice/0 (if Mode=build) or 
%   or get_canonical_type/2 (if Mode=canonical)
