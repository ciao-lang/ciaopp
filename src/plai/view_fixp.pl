:- module(view_fixp,
	[ start_view/0,
	  end_view/0,
	  clean_fixpoint_graph/0,
	  view_fixpoint/7
	],
	[assertions, datafacts, ciaopp(ciaopp_options)]).

:- if(defined(has_davinci)).

:- use_module(library(aggregates), [findall/3]).
:- use_module(library(davinci)).
:- use_module(library(format), [format/3]).
:- use_module(library(terms_vars), [varset/2]).

:- use_module(library(graphs/ugraphs), [vertices_edges_to_ugraph/3]).
:- use_module(library(write), [numbervars/3]).

:- use_module(ciaopp(p_unit/program_keys), [predkey_from_sg/2]).
:- use_module(ciaopp(plai/domains), [call_to_entry/10, project/6]).
:- use_module(ciaopp(plai/trace_fixp), [trace_fixp/1]).

:- doc(title, "Visualization of CiaoPP traces using daVinci").

:- doc(module, " This module is used to display the analysis graph
   computed during the fixpoint. It uses the daVinci product, with
   which it communicates by the standard input and ouput
   (@lib{process} library is used for system call with
   @pred{process_call/3}).

@section{Local graph representation}
The graph is incrementally mantained in the database with node/8 and
   edge/2. A node can correspond to a goal (goal-node) or a clause 
   (clause-goal), and edges are always (except with variants) between
   different classes of nodes.

@tt{node(Id,Key,Atom,ASub,A,A1,Type,Node)}

@begin{itemize}
   @item Id-Key uniquely identifies a node:
 @begin{itemize}
      @item for a goal-node which corresponds to a fixpoint node,
        Id is the fixpoint id
        Key is the functor/arity (as an atom)
      @item for a clause-node,
        Id is the fixpoint id of the closest goal-node ancestor
        Key is the clause id
      @item for a goal-node which is not yet a fixpoint node,
        Id is as in a clause-node
        Key is the program point id of the goal atom
 @end{itemize}
   @item Node=..[NKey,NId] and NKey-NId uniquely identifies a node:
 @begin{itemize}
      @item for a goal-node they are as last case above
      @item for a clause-node they are as above
 @end{itemize}
   @item Atom is:
 @begin{itemize}
      @item for a goal-node, the goal atom
      @item for a clause-node, the clause head
 @end{itemize}
   @item ASub is:
 @begin{itemize}
      @item for a goal-node, the projected call substitution
      @item for a clause-node, the entry substitution, which may contain 
            the (existential) variables of the body
 @end{itemize}
   @item A is (Ins,Outs) where:
 @begin{itemize}
      @item Ins is an open ended list of ASub's
      @item Outs is an open ended list of projected success substitutions 
            (goal-node) or exit substitutions (clause-node)
 @end{itemize}
   @item A1 is (Ins1,Outs1) where:
 @begin{itemize}
      @item Ins1 is the end of Ins
      @item Outs1 is the end of Outs
 @end{itemize}
   @item Type is:
 @begin{itemize}
      @item for a (normal) goal-node, sg
      @item for a clause-node, cl
      @item for a variant goal-node, va
 @end{itemize}
 @end{itemize}
   A variant occurs when a clause body is traversed for a second time
   and in a particular goal atom a new goal-node has to be created which
   is different from the one already associated to that body atom. The 
   former substitutes the latter, which becomes a variant of the former.
   An incoming edge to the variant exists from the new goal-node.

").

start_view:-
	davinci,
	Step=menu_entry(string(step),string('One step ahead')),
	davinci_menu(Step),
	Sync=submenu_entry(string(view),string('Mode'),
	              [menu_entry(string(sync),string('Synchronous')),
		       menu_entry(string(async),string('Asynchronous'))
		      ]   ),
	davinci_menu(Sync),
	Help=submenu_entry(string(help),string('Colors'),
             [menu_entry(string(curr),string('Current node:        orange')),
	      menu_entry(string(comp),string('Complete used:       green')),
	      menu_entry(string(fixp),string('Fixpoint used:         cyan')),
	      menu_entry(string(appr),string('Approx. used:          blue')),
	      menu_entry(string(appu),string('Approx. unchanged:   cyan')),
	      menu_entry(string(iter),string('New fixp. iteration:   red'))
	     ]            ),
	davinci_menu(Help),
	Commands=submenu_entry(string(commands),string('Commands'),
	         [menu_entry(string(hide),string('Hide/show selected node')),
		  menu_entry(string(skip),string('Skip until selected node'))
		 ]            ),
	davinci_menu(Commands),
	Trace=menu_entry(string(trace),string('Trace')),
	davinci_menu(Trace),
	End=menu_entry(string(end),string('End')),
	davinci_menu(End),
	all_menu_entries_but_step.
%	all_menu_entries.

davinci_menu(Menu):-
	davinci_put(app_menu(create_menus([Menu]))).

all_menu_entries_but_step:-
	davinci_put(app_menu(activate_menus([string(end),string(trace),
	    string(view),string(async),string(sync),
	    string(help),string(curr),string(comp),
	    string(commands),string(hide),string(skip),
            string(fixp),string(appr),string(appu),string(iter)]))
		   ).
all_menu_entries:-
	davinci_put(app_menu(activate_menus([string(end),string(trace),
	    string(view),string(async),string(sync),
	    string(step),
	    string(help),string(curr),string(comp),
	    string(commands),string(hide),string(skip),
            string(fixp),string(appr),string(appu),string(iter)]))
		   ).

end_view:- davinci_quit, !.
end_view.

:- data node/8,
	edge/2,
	current/1,
	hidden/1,
	selected_nodes/1,
	skip_node/1,
	sync/0.

clean_fixpoint_graph:-
	retractall_fact(node(_,_,_,_,_,_,_,_)),
	retractall_fact(edge(_,_)),
	retractall_fact(current(_)),
	retractall_fact(skip_node(_)),
	retractall_fact(hidden(_)).

:- doc(bug, "Create another trace event for erasing analysis info (it
is not correct to erase the local structures for representing the
analysis graph each time the fixpoint is started: event 'start fixpoint').

The problem is that if an analysis already exists, there are completes
in the analysis results but not in the structures to communicate the
visualization to daVinci in the view_fixp module because they are
created at the same time completes are added during analysis, because
they are removed by @pred{clean_fixpoint_graph/0} when the fixpoint
starts.").

% ------------------------------------------------------------------------
% view_fixpoint(State,Id,_,Key,Atom,ASub,Clauses/Body)
% ------------------------------------------------------------------------

view_fixpoint('start fixpoint',_,__,_,_,_,_):- !,
	clean_fixpoint_graph.
view_fixpoint('end fixpoint',_,_,_,_,_,_):- !,
	open_graph,
	davinci_put(show_status(string('Fixpoint computation ended'))),
	repeat,
	  davinci_get(X),
	  process(X,_),
	  X=menu_selection(end),
	!.
view_fixpoint('init fixpoint',Id,_N,SgKey,Sg,Proj,_):- !,
	Node=..[SgKey,query(Id)],
	asserta_fact(current(Node)),
	asserta_fact(node(query(Id),SgKey,Sg,Proj,([Proj|X],Y),(X,Y),sg,Node)),
	open_graph,
	focus_node(Node,orange),
	davinci_put(show_status(string(''))),
	synchro.
view_fixpoint('non-recursive initiated',Id,_PId,SgKey,Sg,Proj,_):- !,
	retract_fact(current(Node)),
	retract_fact(node(_,_,Sg,_,ASubs,ASubs1,T,Node)),
	asserta_fact(node(Id,SgKey,Sg,Proj,ASubs,ASubs1,T,Node)).
view_fixpoint('non-recursive clauses',Id,_,SgKey,_Sg,_Proj,Clauses):- !,
	node(Id,SgKey,_,_,_,_,_,Parent),
	or_successors(Clauses,Parent,Id).
view_fixpoint('fixpoint initiated',Id,_,SgKey,_Sg,_Proj,Clauses):- !,
	node(Id,SgKey,_,_,_,_,_,Parent),
	or_successors(Clauses,Parent,Id).
view_fixpoint('visit clause',Id,_,ClKey,Head,Entry,Body):- !,
	retract_fact(node(Id,ClKey,Head,Proj,ASubs,ASubs1,T,Node)),
	ASubs1=([Entry|Entries],Exits),
	asserta_fact(node(Id,ClKey,Head,Proj,ASubs,(Entries,Exits),T,Node)),
	and_successors(Body,Node,Id),
	open_graph,
	focus_node(Node,orange),
	davinci_put(show_status(string(''))),
	skipped(Node),
	synchro.
view_fixpoint('exit clause',Id,_,ClKey,Head,Exit,_):- !,
	retract_fact(node(Id,ClKey,Head,Proj,ASubs,ASubs1,T,Node)),
	ASubs1=(Entries,[Exit|Exits]),
	asserta_fact(node(Id,ClKey,Head,Proj,ASubs,(Entries,Exits),T,Node)),
	color_node(Node,white).
view_fixpoint('visit fact',Id,_,ClKey,Head,Proj,Help):- !,
	Help=(Sv,Sg,Hv,Fv,AbsInt),
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Proj,Entry,_), % TODO: add some ClauseKey? (JF)
	retract_fact(node(Id,ClKey,Head,Proj,ASubs,ASubs1,T,Node)),
	ASubs1=([Entry|Entries],Exits),
	asserta_fact(node(Id,ClKey,Head,Proj,ASubs,(Entries,Exits),T,Node)),
	open_graph,
	focus_node(Node,orange),
	davinci_put(show_status(string(''))),
	skipped(Node),
	synchro.
view_fixpoint('exit fact',Id,_,ClKey,Head,Prime,Help):- !,
	Help=(Sv,Sg,Hv,Fv,AbsInt),
	call_to_entry(AbsInt,Sv,Sg,Hv,Head,not_provided,Fv,Prime,Exit,_), % TODO: add some ClauseKey? (JF)
	retract_fact(node(Id,ClKey,Head,Proj,ASubs,ASubs1,T,Node)),
	ASubs1=(Entries,[Exit|Exits]),
	asserta_fact(node(Id,ClKey,Head,Proj,ASubs,(Entries,Exits),T,Node)),
	color_node(Node,white).
% only works in non-multivariant mode----------v
view_fixpoint('visit goal',Id0,ClKey,SgKey0,Sg,[Call],AbsInt):- !,
	varset(Sg,Sv),
	project(AbsInt,Sg,Sv,Sv,Call,Proj),
	Node=..[SgKey0,Id0],
	node_variant(Node,Sg,Proj,ASubs,ASubs1,T,Id,SgKey,Variant),
	asserta_fact(current(Node)),
	ASubs1=([Proj|Calls],Succs),
	asserta_fact(node(Id,SgKey,Sg,Proj,ASubs,(Calls,Succs),T,Node)),
	( Variant==yes -> open_graph ; true ),
	Parent=..[ClKey,Id0],
	color_node(Parent,white),
	focus_node(Node,orange),
	davinci_put(show_status(string('Entering goal'))),
	skipped(Node),
	synchro.
% only works in non-multivariant mode----------v
view_fixpoint('exit goal',NodeId,PId,(GoalKey,BodyKey),Sg,[Succ],AbsInt):- !,
	Node=..[BodyKey,PId],
	retract_fact(node(Id,SgKey,Sg,Proj,ASubs,ASubs1,T,Node)),
	varset(Sg,Sv),
	project(AbsInt,Sg,Sv,Sv,Succ,Prime),
	ASubs1=(Calls,[Prime|Succs]),
	asserta_fact(node(Id,SgKey,Sg,Proj,ASubs,(Calls,Succs),T,Node)),
	focus_node(Node,orange),
	davinci_put(show_status(string('Exiting goal'))),
	skipped(Node),
	synchro,
	color_node(Node,white),
	( node(NodeId,GoalKey,_,_,_,_,_,PNode)
	-> color_node(PNode,white)
	 ; true
	).
view_fixpoint('complete used',_Id,UsedId,SgKey,_Sg,_Prime,_):- !,
	node(UsedId,SgKey,_,_,_,_,_,Node),
	focus_node(Node,green),
	davinci_put(show_status(string('Used another node''s complete value'))),
	synchro.
view_fixpoint('fixpoint used',_Id,UsedId,SgKey,_Sg,_Prime,_):- !,
	node(UsedId,SgKey,_,_,_,_,_,Node),
	focus_node(Node,cyan),
	davinci_put(show_status(string('Used another node''s fixpoint value'))),
	synchro.
view_fixpoint('approx used',_Id,UsedId,SgKey,_Sg,_Prime,_):- !,
	node(UsedId,SgKey,_,_,_,_,_,Node),
	focus_node(Node,blue),
	davinci_put(show_status(string('Fixpoint computation may be restarted'))),
	synchro.
view_fixpoint('approx unchanged',_Id,UsedId,SgKey,_Sg,_Proj,_):- !,
	node(UsedId,SgKey,_,_,_,_,_,Node),
	focus_node(Node,cyan),
	davinci_put(show_status(string('Fixpoint computation needs not be restarted'))),
	synchro.
view_fixpoint('fixpoint iteration',Id,_,SgKey,_Sg,_Prime,_):- !,
	node(Id,SgKey,_,_,_,_,_,Node),
	focus_node(Node,red),
	davinci_put(show_status(string('Starting new fixpoint iteration'))),
	synchro.
view_fixpoint(_Mess,_Id,_F,_SgKey,_Sg,_Proj,_).

% ------------------------------------------------------------------------
% Maintenance of the database graph
% ------------------------------------------------------------------------

or_successors([clause(Head,_Vars,K,_Body)|Cls],Parent,Id):-
	Node=..[K,Id],
	successor(K,Head,Parent,Id,Node,cl),
	or_successors(Cls,Parent,Id).
or_successors([],_Parent,_Id).

and_successors((g(K,_,_,_,Sg),Body),Parent,Id):-
	Node=..[K,Id],
	successor(K,Sg,Parent,Id,Node,sg),
	and_successors(Body,Parent,Id).
and_successors(g(K,_,_,_,Sg),Parent,Id):-
	Node=..[K,Id],
	successor(K,Sg,Parent,Id,Node,sg).

successor(_K,_Sg,_Parent,_Id,Node,_T):-
	node(_,_,_,_,_,_,_,Node), !.
successor(K,Sg,Parent,Id,Node,T):-
	asserta_fact(node(Id,K,Sg,_,X,X,T,Node)),
	asserta_fact(edge(Parent,Node)).

node_variant(Node,Sg,Proj,ASubs,ASubs1,T,Id,SgKey,no):-
	retract_fact(node(Id,SgKey,Sg,Proj,ASubs,ASubs1,T,Node)), !.
node_variant(Node,_Sg,_Proj,ASubs,ASubs,T,Id0,SgKey0,yes):-
	Node=..[SgKey0,Id0],
	retract_fact(node(Id,SgKey,OldSg,OldProj,OldASubs,OldASubs1,T,Node)),
	NewNode=..[SgKey,Id],
	asserta_fact(node(Id,SgKey,OldSg,OldProj,OldASubs,OldASubs1,va,NewNode)),
	repeat,
	  ( retract_fact(edge(Node,S))
	  -> asserta_fact(edge(NewNode,S)),
	     fail
	   ; true
	  ), !,
	asserta_fact(edge(Node,NewNode)),
	asserta_fact(hidden(NewNode)).

% ------------------------------------------------------------------------
% Maintenance of the displayed graph
% ------------------------------------------------------------------------

focus_node(Node,Color):-
	color_node(Node,Color),
	davinci_put(focus_node(string(Node))).

color_node(Node,Color):-
	davinci_put(change_node_color(string(Node),string(Color))).

open_graph:-
	findall(A-B,edge_for_davinci(A,B),Edges),
	findall(N,(node(_Id,Key,Atom,_,_,_,T,Node),
	           node_for_davinci(T,Node,Key,Atom,N)),
		Nodes),
	vertices_edges_to_ugraph(Nodes,Edges,Graph),
	davinci_ugraph(Graph).

node_for_davinci(T,V,Key,Atom,node(V,[a(string('OBJECT'),string(L))|Atts])):-
	label_for_davinci(T,Atom,Key,L,Atts0),
	( hidden(V)
	-> Atts=[a(string('HIDDEN'),string(true))|Atts0]
	 ; Atts=Atts0
	).

label_for_davinci(sg,Atom,_Key,L,[]):-
	predkey_from_sg(Atom,L).
label_for_davinci(cl,_Atom,L,L,[a(string('_GO'),string(ellipse))]).
label_for_davinci(va,_Atom,_Key,'',[a(string('_GO'),string(circle))]).

edge_for_davinci(NA,NB):-
	edge(A,B),
	node(_IdA,KeyA,AtomA,_,_,_,TA,A),
	node(_IdB,KeyB,AtomB,_,_,_,TB,B),
	node_for_davinci(TA,A,KeyA,AtomA,NA),
	node_for_davinci(TB,B,KeyB,AtomB,NB).

% ------------------------------------------------------------------------
% Synchronization of the incremental display with the user 
%  and answers to the menu selections
% ------------------------------------------------------------------------

synchro:-
	davinci_get_all(List),
	process_all(List,Sync),
	( Sync==sync
	-> true
	 ; repeat,
	     ( sync
	     -> davinci_get(X),
	        process(X,_),
		X=menu_selection(step)
	      ; true
	     ),
	   !
	).

process_all([],_S).
process_all([X|Xs],S):-
	( process(X,S) -> true ; true ),
	process_all(Xs,S).
	   
process(menu_selection(async),_):-
	retractall_fact(sync),
	all_menu_entries_but_step.
process(menu_selection(sync),_):- sync, !.
process(menu_selection(sync),_):-
	asserta_fact(sync),
	all_menu_entries.
process(menu_selection(step),sync).
process(menu_selection(trace),_):- trace_fixp(trace).
process(menu_selection(end),_).
process(communication_error(X),_):-
	name(M,X),
	format(user_error,"daVinci: ~w~n",[M]).
process(communication_crash(X),_):-
	name(M,X),
	format(user_error,"daVinci: ~w~n",[M]).
process(node_selections_labels(Labels),_):-
	asserta_fact(selected_nodes(Labels)).
process(node_double_click,_):-
	retract_fact(selected_nodes([Label])),
	retractall_fact(selected_nodes(_)),
	show_label(Label).
process(menu_selection(hide),_):-
	retract_fact(selected_nodes([Label])),
	retractall_fact(selected_nodes(_)),
	( retract_fact(hidden(Label))
	-> true
	 ; asserta_fact(hidden(Label))
	),
	davinci_put(hide_or_show_subgraph).
process(menu_selection(skip),_):-
	retract_fact(selected_nodes([Label])),
	retractall_fact(selected_nodes(_)),
	( skip_node(Label)
	-> true
	 ; retractall_fact(skip_node(_)),
	   asserta_fact(skip_node(Label)),
	   retract_fact(sync)
	).

show_label(Node):-
	node(_Id,_Key,Sg,_,ASubs,ASubs1,_,Node),
	numbervars((Sg,ASubs,ASubs1),0,_),
	show_node(ASubs,ASubs1,Strings),
	davinci_put(
	   question_string(string('Abstract Substitutions'),
	                   [string(Sg)|Strings],string('') )
		   ).

show_node((Calls,Succs),(Calls1,Succs1),Strings):-
	Calls==Calls1,
	Succs==Succs1, !,
	Strings=[].
show_node((Calls,[Succ|Succs]),(Calls1,Succs1),Strings):-
	Calls==Calls1, !,
	patch(Succ,Succ0),
	S=' '-Succ0,
	Strings=[string(S)|Strings0],
	show_node((Calls,Succs),(Calls1,Succs1),Strings0).
show_node(([Call|Calls],Succs),(Calls1,Succs1),Strings):-
	Succs==Succs1, !,
	patch(Call,Call0),
	S=Call0-' ',
	Strings=[string(S)|Strings0],
	show_node((Calls,Succs),(Calls1,Succs1),Strings0).
show_node(([Call|Calls],[Succ|Succs]),ASubs1,[string(S)|Strings0]):-
	patch(Call,Call0),
	patch(Succ,Succ0),
	S=Call0-Succ0,
	show_node((Calls,Succs),ASubs1,Strings0).

patch([],{}):- !.
patch('$bottom',bottom):- !.
patch(Term,{Term0}):-
	Term=[_|_], !,
	patch_list(Term,Term0).
patch(Term,Term0):-
	functor(Term,F,A),
	functor(Term0,F,A),
	patch_args(A,0,Term,Term0).

patch_args(A,A,_Term,_Term0):- !.
patch_args(N,A,Term,Term0):-
	arg(N,Term,Arg),
	arg(N,Term0,Arg0),
	patch(Arg,Arg0),
	N1 is N-1,
	patch_args(N1,A,Term,Term0).

patch_list([Arg|Term],(Arg0,Term0)):-
	patch(Arg,Arg0),
	patch_list(Term,Term0).
patch_list([Arg],Arg0):-
	patch(Arg,Arg0).

skipped(Node):-
	retract_fact(skip_node(Node)), !,
	retractall_fact(skip_node(_)),
	asserta_fact(sync),
	all_menu_entries.
skipped(_Node).

:- else.

start_view.
end_view.
clean_fixpoint_graph.
view_fixpoint(_,_,_,_,_,_,_).

:- endif.
