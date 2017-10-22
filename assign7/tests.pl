asList(X, [X]).

unify(X, X).

myAppend([], L, L).
myAppend([H|T], L, [H|R]) :-
    myAppend(T, L, R).

myLength([], 0).
myLength([_|T], Len) :-
    myLength(T, TailLen),
    Len is TailLen + 1.

function2(1).
function2(2).

function(3).
function(4).
function(X) :-
    function2(X).

function3(X) :-
    X = 5; X = 6.

