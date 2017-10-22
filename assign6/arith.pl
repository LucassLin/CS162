% Simple arithmetic evaluator.
% Its expression language is desribed below:
%
% i \in Integer
% e \in Exp ::= i | e1 + e2 | e1 - e2

% eval: Exp, Integer
eval(int(I), I).
eval(plus(E1, E2), Result) :-
    eval(E1, E1Res),
    eval(E2, E2Res),
    Result is E1Res + E2Res.
eval(minus(E1, E2), Result) :-
    eval(E1, E1Res),
    eval(E2, E2Res),
    Result is E1Res - E2Res.
