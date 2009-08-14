:- use_module(library(chr)).
:- set_prolog_flag(chr_toplevel_show_store,false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interface rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cfg_to_simple_hmm(GrammarFile,SimpleHMMFile) :-
	read_store_file(GrammarFile),
	create_hidden_markov_model,
	write_simple_hmm_to_file(SimpleHMMFile).
	
cfg_to_prism_program_hmm(GrammarFile,PrismProgramFile) :-
	read_store_file(GrammarFile),
	create_hidden_markov_model,
	write_prism_program_to_file(PrismProgramFile).

create_hidden_markov_model :-
	retractall(nfa(_)),
	retractall(dfa(_)),
	retractall(prev_nfa_state(_)),
	retractall(prev_dfa_state(_)),
	mohri_nederhof_transform,
	construct_nfa,
	dfa_start(s), % FIXME: get from constraint-store
	create_hmm.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Grammar loading 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	

:- chr_constraint read_store_file/1, read_store_stream/1.

read_store_file(File) ==> open(File, read, Stream), read_store_stream(Stream).
read_store_stream(S) <=> read(S, Rule), Rule \= end_of_file | Rule, read_store_stream(S).
read_store_stream(S) <=> close(S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Mohri/Nederhof transformation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- chr_constraint 	rule/2,
					rule/3,
					prime/2,
					terminal/1,
					nonterminal/1,
					root/1,
					notroot/1,
					terminal_candidate/1,
					transform/0,
					finalize/0.
					
mohri_nederhof_transform :-	transform, finalize.					
	
new_nonterminal(N,NPrime) :-
	atom_concat(N, '_prime',NPrime).
	
rule(A,B) <=> rule(A,B,original).

rule(A,B,C) \ rule(A,B,C) <=> true.
nonterminal(N) \ nonterminal(N) <=> true.
prime(N,NP) \ prime(N,NP) <=> true.
transform \ transform <=> true.

rule(_,List,original) ==> terminal_candidate(List).

terminal_candidate([]) <=> true.
terminal_candidate([T|Rest]) <=> terminal(T), terminal_candidate(Rest).

nonterminal(X) \ terminal(X) <=> true.

rule(N,_,_) ==> nonterminal(N).

% Find the root non-terminal
nonterminal(X) ==> root(X).
%nonterminal(NPrime), prime(N, NPRime) ==> notroot(NPrime).
terminal(X) ==> notroot(X).
notroot(N) \ root(N) <=> true.

% (only) Original nonterminals are primed
nonterminal(N) ==> not(new_nonterminal(_,N)) | new_nonterminal(N,NPrime), prime(N,NPrime), notroot(NPrime).

% Add epsilon rule for each primed nonterminal
transform, prime(_,N) ==> rule(N, epsilon, transformed).

% Create initial transformed rules

% Preserve rules rewriting to just one nonterminal
transform, nonterminal(N1) \ rule(N, [N1], original) <=>
	rule(N, [N1], transformed).

% NPrime is added to original rules which are not right-recursive
transform, prime(N,NPrime) \ rule(N,[S1,S2|RestRHS], original) <=>
	append([S1,S2|RestRHS],[NPrime],RHSTransformed),
	rule(N,RHSTransformed,transformed).

transform, prime(N,NPrime), terminal(T) \ rule(N,[T], original) <=>
	rule(N,[T,NPrime],transformed).

% Recursion:
terminal(T), nonterminal(N1), prime(N1,N1Prime) \ rule(N,[T,N1,R|Rest],transformed) <=>
	rule(N,[T,N1],transformed),
	rule(N1Prime,[R|Rest],transformed).
	
terminal(T), nonterminal(N1), prime(N1,N1Prime) \ rule(N,[N1,T|Rest],transformed) <=>
	rule(N,[N1],transformed),
	rule(N1Prime, [T|Rest], transformed).
	
	
%% Finalize when all rules have been transformed
finalize \ rule(X,Y,transformed) <=> rule(X,Y,final).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Convert grammmar to NFA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- chr_constraint 
	transition/3,
	nfa_accept_state/1,
	construct_nfa/0,
	nfa_report/0.

% Mark root as accepting
mark_accepting @
construct_nfa,root(N),prime(N,NPrime) \ rule(NPrime,epsilon,final) <=> 
	nfa_accept_state(NPrime).

construct_nfa \ rule(N,epsilon,final) <=> 
	nfa_accept_state(N).

construct_nfa, nonterminal(N1), nonterminal(N2) \ rule(N1,[N2],final) <=>
	transition(epsilon,N1,N2).

construct_nfa, nonterminal(N), nonterminal(N1), terminal(T) \ rule(N, [T,N1], final) <=>
	transition(T,N,N1).

report_accepting @
nfa_report, transition(Symbol, From, To), nfa_accept_state(To) <=>
    assert(nfa(transition(Symbol,From,To))),
    assert(nfa(accept_state(To))),
    nfa_report.

report_transitions @
nfa_report, transition(Symbol, From, To) <=>
    assert(nfa(transition(Symbol,From,To))),
    nfa_report.

viewnfa :-
	findall([Symbol,To,From],nfa(transition(Symbol,To,From)),Transitions),
	findall(State,nfa(accept_state(State)),AcceptStates),
	NFA = [[s],AcceptStates,Transitions],
    fa_graphviz(NFA,'nfa.dot'),
    viewdot('nfa.dot').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert a NFA to a DFA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- chr_constraint dfa_start/1,
	      dfa_start_state/1,
		  dfa_accept_state/1,
		  epsilon_closure/2,
		  dfa_transition/3,
		  dfa_report/0,
		  open_transition/4,
		  open_state/1, 
		  marked_state/1,
		  unmarked_state/1,
		  replace_state/2.

new_dfa_state(State) :-
    catch(prev_dfa_state(Y),_,(Y is 0, assert(prev_dfa_state(Y)))),
    X is Y + 1,
    retract(prev_dfa_state(Y)),
    assert(prev_dfa_state(X)),
    atom_concat(dfa_s, X, State).		

start_dfa_generation @
dfa_start(NS1), transition(epsilon,NS1,To) <=>
    new_dfa_state(DS1),
    dfa_start_state(DS1),
    epsilon_closure(DS1,[To]),
    open_state(DS1).

%%% The epsilon-closure part
remove_dups @
epsilon_closure(A,B) \ epsilon_closure(A,B) <=> true.

add_eclosure_transition @
transition(epsilon, From, To) \ epsilon_closure(DfaState, FromStates) <=>
    member(From, FromStates),
    not(member(To,FromStates))
    |
    epsilon_closure(DfaState,[To|FromStates]).

merge_epsilon_closures @
epsilon_closure(State, NS1), epsilon_closure(State, NS2) <=>
    union(NS1, NS2, NSAll),
    epsilon_closure(State,NSAll).

%%% The move part
merge_open_transitions @
open_transition(State,Symbol,From1,To1), open_transition(State,Symbol,From2,To2) <=>
    union(From1, From2, From3), % Not really necesary
    union(To1, To2, To3),
    open_transition(State,Symbol,From3,To3).

collapse_dfa_states1 @
epsilon_closure(OtherState, ReachableSet) \
unmarked_state(SomeState), open_state(NewState), dfa_transition(Symbol,FromState,NewState), epsilon_closure(NewState, ReachableSet) <=>
    OtherState \= NewState % Obviously, or we'll have endless recursion
    |
    dfa_transition(Symbol,FromState, OtherState),
    replace_state(NewState,OtherState),	
    open_state(SomeState).

collapse_dfa_states2 @
epsilon_closure(OtherState, ReachableSet) \
open_state(NewState), dfa_transition(Symbol,FromState,NewState), epsilon_closure(NewState, ReachableSet) <=>
    OtherState \= NewState % Obviously, or we'll have endless recursion
    |
    dfa_transition(Symbol,FromState, OtherState),
    replace_state(NewState,OtherState).

replace_dangling_transitions @
replace_state(OldState,NewState) \ dfa_transition(Symbol,SomeState,OldState) <=>
    dfa_transition(Symbol,SomeState,NewState).

propagate_open_transitions @
open_state(State), epsilon_closure(State,NFromStates), transition(Symbol,NFrom,NTo) ==>
    Symbol \= epsilon,
    member(NFrom,NFromStates)
    |
    open_transition(State,Symbol,[NFrom],[NTo]).

open_dfa_state @ % When we have generated all open_transitions
open_state(State) <=> marked_state(State).

create_dfa_state @
marked_state(State), open_transition(State,Symbol,_,To) <=>
    new_dfa_state(NewState)
    |
    epsilon_closure(NewState, To),
    dfa_transition(Symbol, State, NewState),
    marked_state(State), 
    unmarked_state(NewState).

open_next_state @
dfa_transition(_,State,NewState), marked_state(State) \ unmarked_state(NewState) <=>
    open_state(NewState).

dfa_accept_states @
dfa_transition(_,_,DState), nfa_accept_state(NState), epsilon_closure(DState,NStates) ==>
    member(NState, NStates)
    |
    dfa_accept_state(DState).

%%% DFA reporting - not part of core algorithm %%%

dfa_report, epsilon_closure(X,Y) <=>
    write(' > '),
    write(epsilon_closure(X,Y)), nl,
    dfa_report.

dfa_transition(_,_,To) \ dfa_report, dfa_accept_state(To) <=>
    assert(dfa(accept_state(To))),
    dfa_report.

dfa_report, dfa_transition(X,Y,Z) <=> assert(dfa(transition(X,Y,Z))), dfa_report.

dfa_report, dfa_start_state(State) <=> assert(dfa(start_state(State))), dfa_report.

create_dfa(DFA) :-
	dfa_report,
	retractall(prev_nfa_state(_)),
	assert(prev_nfa_state(0)),
	dfa(start_state(StartState)),
    findall(State,dfa(accept_state(State)),AcceptStates),
    findall([Symbol,To,From],dfa(transition(Symbol,To,From)),Transitions),
	DFA = [[StartState],AcceptStates,Transitions].

viewdfa :-
	create_dfa(DFA),
    fa_graphviz(DFA,'dfa.dot'),
    viewdot('dfa.dot').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Create Hidden Markov Model based on DFA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- chr_constraint 
	create_hmm/0,
	write_simple_hmm_to_file/1,
	trans/3,
	emit/3.
	
trans(A,B,C) \ trans(A,B,C) <=> true.

create_hmm, dfa_transition(_,_,S) \ dfa_accept_state(S) <=>
	atom_concat('dfa_', Short, S),
	trans(Short, end, unknown).

create_hmm \ dfa_transition(Symbol, From, To) <=>
	atom_concat('dfa_', ShortFrom, From),
	atom_concat('dfa_', ShortTo, To),
	emit(ShortFrom, Symbol, unknown),
	trans(ShortFrom, ShortTo, unknown).
	
create_hmm \ dfa_start_state(S) <=>
	atom_concat('dfa_', Short, S),
	trans(start, Short, unknown).
	
write_simple_hmm_to_file(File) \ create_hmm <=>
	nl,
	write('Writing Hidden Markov Model to file:'),
	write(File),
	nl,
	tell(File).

write_simple_hmm_to_file(_) \ trans(From,To,Prob) <=>
	write_canonical(trans(From,To,Prob)), write('.'), nl.

write_simple_hmm_to_file(_) \ emit(State,Symbol,Prob) <=>
	write_canonical(emit(State,Symbol,Prob)), write('.'),nl.
	
write_simple_hmm_to_file(_) <=> told.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Create PRISM program from Hidden Markov Model
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% These two rules are only used as template for creating PRISM program
hmm(L):-msw(trans(start),S0),hmm(S0,L).
hmm(S,L):-msw(trans(S),NextS),(NextS=end->L=[];msw(emit(S),C),L=[C|Cs],hmm(NextS,Cs)).

:- chr_constraint values/2, write_prism_program_to_file/1.

values(X, A), values(X, B) <=> append(A,B,C), values(X,C).
	
create_hmm, trans(From,To,_) ==> values(trans(From), [To]).
create_hmm, emit(State,Symbol,_) ==> values(emit(State), [Symbol]).

write_prism_program_to_file(File) ==> tell(File).
write_prism_program_to_file(_) \ values(X,Y) <=> write_canonical(values(X,Y)), write('.'), nl.
write_prism_program_to_file(File) <=>
	nl,listing(hmm/1),
	nl,listing(hmm/2),
	told,
	write('Wrote PRISM program for HMM to: '),write(File),nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Convert FA to graphviz dot file
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

write_gv_edges([]).

write_gv_edges([[Symbol,From,To]|Rest]) :-
    write_gv_edge(Symbol,From,To),
    write_gv_edges(Rest).

write_gv_edge(Symbol,To,From) :-
    write('\t"'),
    write(To),
    write('" -> "'),
    write(From),
    write('" [label="'),
    write(Symbol),
    write('"]'),
    nl.

write_space_separated([]).
write_space_separated([Elem|Rest]) :-
    write(Elem),
    write(' '),
    write_space_separated(Rest).

fa_graphviz([StartStates,AcceptStates,Edges],OutputFile) :-
    tell(OutputFile),
    write('digraph FA {'),nl,
    write('\trankdir=LR'),nl,
    write('node [shape = doublecircle]; '),
    write_space_separated(AcceptStates),
    write(';'),
    nl,
    write('node [shape = box]; '),
    write_space_separated(StartStates),
    write(';'),
    nl,
    write('node [shape = circle];'),
    nl,
    write_gv_edges(Edges),
    write('}'),
    nl,
    told.

viewdot(DotFile) :-
    atom_concat('cat ', DotFile, DotCmd1),
    atom_concat(DotCmd1, ' | dot -Tpng -oviewdot.png',DotCmd),
    shell(DotCmd),
    shell('open viewdot.png').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Some stupid test rules...
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test1 :- 
	rule(t, [f]),
	rule(f, [a]),
	transform.

test2 :-
	rule(s, [e]),
	rule(e, [e,'+',t]),
	rule(e, [t]),
	rule(t, [t, '*', f]),
	rule(t, [f]),
	rule(f, ['(',e,')']),
	rule(f,[a]),
	transform,
	finalize,
	construct_nfa.

test3 :-
	retractall(nfa(_)),
	retractall(prev_nfa_state(_)),
	test2,
	nfa_report,
	viewnfa.

test4 :-
	retractall(nfa(_)),
	retractall(dfa(_)),
	retractall(prev_nfa_state(_)),
	retractall(prev_dfa_state(_)),
	test2,
	dfa_start(s),
	viewdfa.

test5 :-
	retractall(nfa(_)),
	retractall(dfa(_)),
	retractall(prev_nfa_state(_)),
	retractall(prev_dfa_state(_)),
	test2,
	dfa_start(s),
	nl,write('-----------------------------------'),nl,
	nl,write('CREATE HMM: '),nl,
	create_hmm,
	write_simple_hmm_to_file('derived.hmm'),
	nl,write('-----------------------------------'),nl.
	
test6 :-
	cfg_to_simple_hmm('sample_grammar.pl', 'generated_test_hmm.pl').

test7 :-
	cfg_to_prism_program_hmm('sample_grammar.pl', 'generated_test_hmm.pl').