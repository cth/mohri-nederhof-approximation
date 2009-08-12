:- use_module(library(chr)).

:- chr_constraint rule/2, rule/3, prime/2, terminal/1, nonterminal/1, terminal_candidate/1, transform/0.

init_grammar :-
	rule(s, [e]),
	rule(e, [e,'+',t]),
	rule(e, [t]),
	rule(t, [t, '*', f]),
	rule(t, [f]),
	rule(f, ['(',e,')']),
	rule(f,[a]).
	
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

% (only) Original nonterminals are primed
nonterminal(N) ==> not(new_nonterminal(_,N)) | new_nonterminal(N,NPrime), prime(N,NPrime).

rule(_,_,_) ==> transform.

% Add epsilon rule for each primed nonterminal
transform, prime(_,N) ==> rule(N, epsilon, transformed).

% Create initial transformed rules
transform, nonterminal(N1) \ rule(N, [N1], original) <=>
	rule(N, [N1], transformed).

transform, prime(N,NPrime) \ rule(N,RHS, original) <=>
	append(RHS,[NPrime],RHSTransformed),
	rule(N,RHSTransformed,transformed).

%% Base case:
rule(N,[N1], transformed), prime(N,NPrime), prime(_,N1) ==>
	rule(NPrime, N1, transformed).

% Recursion:
terminal(T), nonterminal(N1), prime(N1,N1Prime) \ rule(N,[T,N1,R|Rest],transformed) <=>
	rule(N,[T,N1],tranformed),
	rule(N1Prime,[R|Rest],transformed).
	
terminal(T), nonterminal(N1), prime(N1,N1Prime) \ rule(N,[N1,T|Rest],transformed) <=>
	rule(N,[N1],transformed),
	rule(N1Prime, [T|Rest], transformed).
	






















