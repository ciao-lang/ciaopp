:- module(_, [
      % type symbols
        native_type_symbol/1,
      % basic types
        atom_type/1,
        bot_type/1,
        float_type/1,
        ground_type/1,
        int_type/1,
        nnegint_type/1,
        numeric_type/1,
        struct_type/1,
        ground_struct_type/1,
        top_type/1,
        var_type/1,
        set_atom_type/1,
        set_bottom_type/1,
        set_float_type/1,
        set_ground_type/1,
        set_ground_struct_type/1,
        set_int_type/1,
%%          set_nnegint_type/1,
        set_numeric_type/1,
        set_numexp_type/1,
%%          set_struct_type/1,
        set_top_type/1,
        set_var_type/1

], [assertions]).

% ========================================================================

:- pred native_type_symbol(X)
   # "@var{X} is a constant defining a @tt{native type} of the lattice
      (bottom point excluded).".

native_type_symbol(T) :- top_type(T).
native_type_symbol(T) :- var_type(T).
native_type_symbol(T) :- ground_type(T).
native_type_symbol(T) :- atom_type(T).
native_type_symbol(T) :- numeric_type(T).
native_type_symbol(T) :- int_type(T).
native_type_symbol(T) :- nnegint_type(T).
native_type_symbol(T) :- float_type(T).
native_type_symbol(T) :- struct_type(T).
native_type_symbol(T) :- ground_struct_type(T).


% ask versions for each native symbol
bot_type(X) :- X == bot.
top_type(X) :- X == term.
var_type(X) :- X == vr. % TODO:[new-resources] support for etermsvar
ground_type(X) :- X == gnd.
atom_type(X) :- X == atm.
numeric_type(X) :- X == num.
int_type(Type) :- Type == int.
nnegint_type(Type) :- Type == nnegint.
float_type(X) :- X == flt.
struct_type(X) :- X == struct.
ground_struct_type(X) :- X == gndstr.

% tell versions for each native symbol
set_bottom_type(bot).
set_top_type(term).
set_var_type(vr). % TODO:[new-resources] support for etermsvar
set_ground_type(gnd).
set_atom_type(atm).
set_numeric_type(num).
set_int_type(int).
% set_nnegint_type(nnegint).
set_float_type(flt).
% set_struct_type(struct).
set_ground_struct_type(gndstr).

% no more built-in!!!
set_numexp_type(_) :- fail.
