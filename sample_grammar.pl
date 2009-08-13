rule(s, [e]).
rule(e, [e,'+',t]).
rule(e, [t]).
rule(t, [t, '*', f]).
rule(t, [f]).
rule(f, ['(',e,')']).
rule(f,[a]).
