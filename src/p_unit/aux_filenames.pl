:- module(aux_filenames,[
	get_module_filename/3,
	get_loaded_module_name/3,
	just_module_name/2,
	is_library/1
   ], [assertions, isomodes]).

:- doc(title,"Auxiliary file name generation").
% TODO: Move together with compiler libs and factorize (jfmc)

:- doc(author,"Jes@'{u}s Correas").

:- doc(module,"This module provides names for auxiliary files used
   during the execution of ciaopp. Depending on the value of several
   preprocess flags (e.g. @code{tmp_dir}, @code{asr_dir}), absolute
   paths are computed in some way. If a temporary directory is
   provided in those flags, a unique file name is generated
   automatically in order to avoid name clashes.").

:- use_module(library(pathnames), [path_basename/2, path_splitext/3]).
:- use_module(ciaopp(preprocess_flags), [current_pp_flag/2]).
:- use_module(library(terms), [atom_concat/2]).
:- use_module(ciaopp(p_unit/itf_db), [current_itf/3]).
:- use_module(engine(internals), [ast_filename/2]).
:- use_module(engine(stream_basic), [absolute_file_name/7]).

:- multifile library_directory/1.
:- dynamic(library_directory/1). % (just declaration, dynamic not needed in this module)
:- multifile file_search_path/2.
:- dynamic(file_search_path/2). % (just declaration, dynamic not needed in this module)

:- doc(bug,"the get_module_filename/3 predicate name does not
   correspond to the real meaning. It needs a file name without
   extension in the second argument, whereas it seems that the module
   name is enough.").

get_module_filename(pl,Source,FileName):-
	!,
	absolute_file_name(Source,'_opt','.pl','.',FileName,_,_).
get_module_filename(Type,Source,FileName):-
	absolute_file_name(Source,'_opt','.pl','.',_,Base0,_),
	(
	    atom_concat(Base,'_opt',Base0)
	;
	    Base = Base0
	),
	get_extension_and_dir(Type,Ext,TmpDir),
	% TODO: better integration with CIAOCCACHE (jfmc)
	( TmpDir = source ->
	    ( Ext = '.ast' -> ast_filename(Base, FileName)
	    ; atom_concat(Base,Ext,FileName)
	    )
	; unique_name(Base,Name),
	  atom_concat([TmpDir,'/',Name,Ext],FileName)
	).

%% get_loaded_module_name(+Module,-AbsName,-AbsBase)
%% Given a module spec (as the one returned by current_itf(imports,_,_)),
%% returns the absolute file name and file base. The module must have
%% been read by driver:module/n, or it must be directly related to a 
%% current module already loaded.
get_loaded_module_name(Module,AbsName,AbsBase):-
	just_module_name(Module,MName),
	current_itf(defines_module,MName,Base),
	absolute_file_name(Base,'_opt','.pl','.',AbsName,AbsBase,_).
	

get_extension_and_dir(asr,'.ast',TmpDir):-
	current_pp_flag(asr_dir,TmpDir).
get_extension_and_dir(reg,'.reg',TmpDir):-
	current_pp_flag(tmp_dir,TmpDir).
get_extension_and_dir(dump,'.dmp',TmpDir):-
	current_pp_flag(tmp_dir,TmpDir).

%% --------------------------------------------------------------------

unique_name(Base,Name):-
	atom_codes(Base,[0'/|BaseS]),
	unique_name_(BaseS,NameS),
	atom_codes(Name,NameS).

unique_name_([],[]).
unique_name_([0'.|Bs],[0'.,0'.|Ns]):-
	!,
	unique_name_(Bs,Ns).
unique_name_([0'/|Bs],[0'.|Ns]):-
	!,
	unique_name_(Bs,Ns).
unique_name_([X|Bs],[X|Ns]):-
	unique_name_(Bs,Ns).

%% --------------------------------------------------------------------

%% just_module_name(+IM0,?IM)
%% given a module spec, returns the module name, without directory or 
%% search path qualifiers, nor suffixes (_opt, .pl).
just_module_name(IM0,IM):-
	nonvar(IM0),
	IM0 = user(_),
	!,
	IM = IM0.
just_module_name(IM0,IM):-
	nonvar(IM),
	IM = user(F0),
	!,
	path_splitext(IM0,Base,_),
	path_splitext(F0,Base,_).
just_module_name(IM0,IM):-
	atom(IM0),
	path_splitext(IM0,IM1,_),
	current_itf(defines_module,IM,IM1),
	!.
%% Previous clause should work in most cases.  
%% Following clauses are only applicable for special 
%% cases (non-loaded modules, etc.)
just_module_name(IM0,IM):-
	functor(IM0,_,1),  %% excluding user(F) specifications.
	!,
	arg(1,IM0,IM1),
	path_basename(IM1,IM2),
	path_splitext(IM2,IM3,_),
	( atom_concat(IM,'_opt',IM3) ->
	    true
	;
	    IM = IM3
	).
just_module_name(IM0,IM):-
	atom(IM0),
	!,
	path_basename(IM0,IM2),
	path_splitext(IM2,IM3,_),
	( atom_concat(IM,'_opt',IM3) ->
	    true
	;
	    IM = IM3
	).

%% --------------------------------------------------------------------

:- pred is_library(+Base).
% Base corresponds to a library(_) or engine(_) path (if no_engine is not set)
is_library(Base):-
	current_pp_flag(punit_boundary,no_engine),
	!,
	is_library_(Base, no).
is_library(Base):-
	is_library_(Base, yes).

is_library_(Base, AllowEngine):-
	absolute_file_name(Base,'','.pl','.',_,_,AbsPath),
	( AllowEngine = yes, % (allow engine(_) paths)
	  file_search_path(engine, Path)
	; library_directory(Path)
	),
	absolute_file_name(Path,'','.pl','.',_,_,LibPath),
	(
	    AbsPath == LibPath, !
	;
	    atom_concat(LibPath,_,AbsPath)
	).

