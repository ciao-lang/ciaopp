:- use_package(assertions).

:- doc(filetype, part).

:- doc(title,"PART I - Using CiaoPP").

:- doc(author, "The Ciao Development Team").

% :- doc(module,"@include{AssrtLang.lpdoc}").

:- doc(module,"
This part documents several levels of interaction with CiaoPP. As
quick introduction we recommend going through the @ref{CiaoPP Quick
Tutorial} and @ref{Advanced Tutorial on Program Development and
Optimization using the Ciao Preprocessor} sections.

CiaoPP can be used from an intuitive graphical menu interface, based
on the @apl{emacs} editor, which allows the interactive selection of
configuration options. An equivalent command-line interface, described
in @ref{The CiaoPP command-line interface}, is provided for
non-interactive use.

For more advanced uses, CiaoPP can be used directly as a library from
a toplevel interface. We provide both a mostly automatic high-level
interface, described in @ref{The CiaoPP high-level interface}, and a
low-level interface intended for advanced users, detailed in @ref{The
CiaoPP low-level interface}. Both the graphical and the command-line
interfaces are based on the functionality provided by the high and
low-level interfaces.
").

% Note that if @apl{emacs} is not available, this
% menu interface can be used as a text-based menu interface. 
