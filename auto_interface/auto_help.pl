:- module( auto_help , [help/0,help/1] , [assertions] ).

:- use_module(library(messages)).

:- doc(bug,"This should all really be generated automatically from 
       auto_interface.pl ... ").

% Why is this multifile here? (I do not see it used elsewhere) --MH
:- multifile program_help/2.

help :- 
	help( _ ),
	fail.

help( X ) :-
	program_help( X , T ),
	note_message( T ).


program_help( ciaopp , " 

  Note that CiaoPP can be used much more easily inside the development
  environment through the emacs menus and toolbar! 

  The following is a short description of some basic commands to use
  CiaoPP from the command line.  Note that, depending on flags,
  processing can be of one module or also all the related modules.
  
  + / - below refer to the modes of the arguments, i.e.:
  + means the argument is provided, - that the argument is returned.

a) The action-based, menu-driven interface:

   The easiest way to use CiaoPP from the command line is to call this
   interactive menu. It allows selecting a basic set of operations and
   options and then performing those operations on a given module (or
   a module and its related modules). This is done as follows:

    customize_and_preprocess( +File ) : enter a menu to select the
          preprocessing action (analysis / assertion checking /
          transformations / optimizations / ...)  to be performed on
          file F (or F and its related modules), select the different
          options, and then perform the action. 

    again : perform again the last actions selected for customize_and_preprocess
          on the same file (useful for reprocessing after changing a file). 

    customize( all ) : only select values for the different options
         (do not perform any action).

  After setting up :

    auto_check_assert( +File ) : Check assertions in F with the currently 
                                 active options.
    auto_optimize( +File ) : Optimize F with the currently active options.
    auto_analyze( +File ) : Analyze F with the currently active options.


b) Alternatively, things can be done manually. In this case the user
   typically needs to perform a sequence of commands to obtain a
   certain result (e.g., analysis first and then checking to be able
   to check assertions). At this level options are set by modifying
   manually preprocessor flags.

   These are some basic commands (the CiaoPP manual has full details):

    module( +File ) : loads a (main) module into the preprocessor.

    analyze( -A ) : enumerate the analyses available.
    analyze( +A ) : perform analysis A on the loaded module.

    acheck : check assertions (using current analysis information).

    transform( -T ) : enumerate the transformations available.
    transform( +T ) : perform transformation T on the loaded module.

    output : output a file with the current program state (i.e., the output 
             includes transformations, analysis info, assertion checking, etc.
             as controlled by the flags set and the actions performed).
    output( +File ) : same as output/0 but output to File.

  The analyses and transformations are controlled by preprocessor flags. 
  These flags can be modified or consulted with:

    current_pp_flag( +F , -V ) : return in V the value of flag F.

    set_pp_flag( +F , +V ) : change the value of flag F to V.

    pp_flag( -F ) : enumerates the available preprocessor flags.
    pp_flag( +F ) : true if F is a preprocessor flag.

    dump_flags( -R ) : enumerates set of flags by fail.
    dump_flags( +R ) : dump a set of flags related with R.

  If you are a CiaoPP developer, see also help( ciaopp( developers ) ). 
  For more info please refer to the CiaoPP manual (\"info ciaopp\").

" ).


program_help( ciaopp( developers ), "

  These commands are useful when developing or debugging CiaoPP:

    show_asr( +File ) : displays the content of a .asr file.

    show_dump( +File ) : displays the content of a .dump file.

    show_types : display all current types (inferred or read).

" ).
