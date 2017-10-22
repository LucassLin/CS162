% X is a logical variable
%
% b \in Boolean ::= true | false
% e \in Exp ::= true | false | variable(X)
%             | or(e1, e2)
%             | and(e1, e2)
%             | not(e)

% boolOr: InBoolean1, InBoolean2, OutBoolean

% boolAnd: InBoolean1, InBoolean2, OutBoolean

% boolNot: InBoolean, OutBoolean

% eval: Exp, Boolean
boolOr(true, true, true).
boolOr(true, false, true).
boolOr(false, true, true).
boolOr(false, false, false).
boolAnd(true, true, true).
boolAnd(true, false, false).
boolAnd(false, true, false).
boolAnd(false, false, false).
boolNot(false, true).
boolNot(true, false).

eval(true, true).
eval(false, false).
eval(variable(X), X).
eval(or(E1,E2), R) :-
    eval(E1, R1),
    eval(E2, R2),
    boolOr(R1,R2,R3),
    R = R3.
eval(and(E1,E2), R) :-
    eval(E1, R1),
    eval(E2, R2),
    boolAnd(R1,R2,R3),
    R = R3.
eval(not(E1), R) :-
    eval(E1, R1),
    boolNot(R1, R2),
    R = R2.



runTest(Test) :-
    format('Running ~w: ', [Test]),
    once(call(Test)) ->
        format('pass~n');
        format('----FAIL----').

boolOrTests :-
    runTest(boolOr(true, true, true)),
    runTest(boolOr(true, false, true)),
    runTest(boolOr(false, true, true)),
    runTest(boolOr(false, false, false)).

boolAndTests :-
    runTest(boolAnd(true, true, true)),
    runTest(boolAnd(true, false, false)),
    runTest(boolAnd(false, true, false)),
    runTest(boolAnd(false, false, false)).

evalTests :-
    runTest(eval(and(true, true), true)),
    runTest(eval(or(false, false), false)),
    runTest(eval(not(true), false)),
    runTest((eval(and(true, variable(A)), true), A == true)),
    runTest((eval(and(variable(B), variable(C)), true), B == true, C == true)),
    runTest(eval(or(variable(D), not(variable(D))), true)),
    runTest(eval(and(variable(E), not(variable(E))), false)),
    runTest((eval(or(false, variable(F)), true), F == true)),
    runTest((eval(or(false, variable(G)), false), G == false)).

runTests :-
    boolOrTests,
    boolAndTests,
    evalTests.
