:- module(_,[],[noprelude]).
% (See p_unit:inject_output_package/1 for details)

%:- use_package(regtypes).
% TODO: faster than package above, no compilation module is loaded

:- new_declaration(regtype/1).
:- new_declaration(regtype/2).

:- op(1150, fx,(regtype)).      
:- op(1150,xfx,(regtype)).
