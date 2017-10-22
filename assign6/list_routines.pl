% For this portion of the assignment, you must write code
% at the portions marked `---FILL ME IN---`.  We have provided
% example code and hints along the way.

% myAppend: Takes two input lists and a result list.
% Determines if the third list is the result of appending
% the first two lists together.
% Example:
%
% myAppend([1, 2, 3], [], L). % L = [1, 2, 3]
% myAppend([], [1, 2, 3], L). % L = [1, 2, 3]
% myAppend([1, 2], [3, 4], L). % L = [1, 2, 3, 4]
%

% BASE CASE - appending an empty list onto some other
% list results in the other list
myAppend([], L, L).

% RECURSIVE CASE - A non-empty list appended onto
% some other list.  In this case, we know the result
% list needs to begin with whatever the non-empty
% list begins with (`H` below).  We can then recursively
% process the rest of the non-empty list and the result
% list.
myAppend([H|T], L, [H|R]) :-
        myAppend(T, L, R).

% myMember: Takes an element and a list.  Determines if
% the element is in the provided list.
% Example:
%
% myMember(1, [1, 2, 3]). % true
% myMember(0, [1, 2, 3]). % false
%

% BASE CASE - A list begins with the element of interest
myMember(X, [X|_]).

% RECURSIVE CASE - The head of the list isn't interesting.
% Recursively process the tail.
myMember(X, [_|R]) :-
        myMember(X, R).

% myNextto: Takes two list elements and a list.  Determines
% if the list contains the first element followed by the second.
% Example:
%
% myNextto(1, 2, [1, 2, 3]). % true
% myNextto(1, 3, [1, 2, 3]). % false
%

% myDelete: Takes an input list, a list element, and an output list.
% Removes all occurrances of the element from the provided list.
% Example:
%
% myDelete([1, 2, 3], 2, L). % L = [1, 3]
% myDelete([1, 2, 3, 2], 2, L). % L = [1, 3]
% myDelete([1, 2, 3], 0, L). % L = [1, 2, 3]

% ---FILL ME IN---
myDelete([], _, []).
myDelete([_|T], X, R) :- 
    myDelete(T,X,R).
myDelete([H|T], X, [H|T2]) :- 
    H \= X, myDelete([H|T], X, T2).

% BASE CASE - The list begins with X and Y.
% ---FILL ME IN---
myNextto(X, Y, [X, Y|_]).

% RECURSIVE CASE - The head of the list isn't interesting.
% Recursively process the tail.
% ---FILL ME IN---
myNextto(X, Y, [_|R]) :-
        myNextto(X, Y, R).

myReverse([],[]).
myReverse([H|T],L):-
    myReverse(T,Z),append(Z,[H],L).

% myNth0: Takes an index, a list, and a result element.  Gets the
% nth element in the list, starting from 0.  For example:
%
% myNth0(0, [4, 5, 6], 4). % true
% myNth0(1, [4, 5, 6], 5). % true
% myNth0(0, [], _). % false
%

% BASE CASE - We have 0 and a non-empty list.  The result
% should simply be the head of the non-empty list.
% ---FILL ME IN---
myNth0(0, [X|_], X).

% RECURSIVE CASE - We have a number greater than 0 and a
% non-empty list.  Process the tail of the list recursively
% with the number - 1.  Keep in mind that to perform any sort
% of arithmetic, we must use `is` in Prolog.
% ---FILL ME IN---
myNth0(N, [_|R], B) :-
    not(R = []),
    N > 0, N1 is N - 1,
    myNth0(N1, R, B).

% myLast: Gets the last element of a list (the first parameter),
% returning it in the second parameter.  For example:
%
% myLast([1], 1). % true
% myLast([1, 2, 3], X). % X = 3
% myLast([], _). % false
%

% BASE CASE - A list that contains one element.  The last element
% is that element directly.
% ---FILL ME IN---
myLast([H|[]],H). 

% RECURSIVE CASE - A list that contains more than one element.
% Recursively process on the list, starting from the second element
% ---FILL ME IN---
myLast([_|T], V) :-
    not(T = []),
    myLast(T, V).

% myLength: takes an input list, and returns the length of the input
% list in the second parameter.  For example:
%
% myLength([], 0). % true
% myLength([0, 1, 2], I). % I = 3

% ---FILL ME IN---
myLength([], 0).
myLength([_|R], N) :-
    myLength(R, N1),
    N is 1 + N1.

% mySum: takes a list (presumably of integers) and returns their
% summation in the second parameter.  For example:
%
% mySum([], 0). % true
% mySum([1, 2, 3], 6). % true
%

% ---FILL ME IN---
mySum([],0).
mySum([S|R], N) :-
    mySum(R, N1),
    N is N1 + S.


runTest(Test) :-
    format('Running ~w: ', [Test]),
    once(call(Test)) ->
        format('pass~n');
        format('----FAIL----').

myAppendTests :-
    runTest(myAppend([1, 2, 3], [], [1, 2, 3])),
    runTest(myAppend([], [1, 2, 3], [1, 2, 3])),
    runTest(myAppend([1, 2], [3, 4], [1, 2, 3, 4])).

myMemberTests :-
    runTest(myMember(1, [1, 2, 3])),
    runTest(myMember(2, [1, 2, 3])),
    runTest(myMember(3, [1, 2, 3])),
    runTest(\+ myMember(4, [1, 2, 3])).

myNexttoTests :-
    runTest(myNextto(1, 2, [1, 2, 3])),
    runTest(myNextto(2, 3, [1, 2, 3])),
    runTest(\+ myNextto(1, 3, [1, 2, 3])).

myDeleteTests :-
    runTest(myDelete([1, 2, 3], 2, [1, 3])),
    runTest(myDelete([1, 2, 3, 2], 2, [1, 3])),
    runTest(myDelete([1, 2, 3], 0, [1, 2, 3])).

myNthTests :-
    runTest(myNth0(0, [4, 5, 6], 4)),
    runTest(myNth0(1, [4, 5, 6], 5)),
    runTest(\+ myNth0(0, [], _)).

myLastTests :-
    runTest(myLast([1], 1)),
    runTest(myLast([1, 2, 3], 3)),
    runTest(\+ myLast([], _)).

myReverseTests :-
    runTest(myReverse([], [])),
    runTest(myReverse([1], [1])),
    runTest(myReverse([1, 2], [2, 1])),
    runTest(myReverse([1, 2, 3], [3, 2, 1])).

myLengthTests :-
    runTest(myLength([], 0)),
    runTest(myLength([0], 1)),
    runTest(myLength([0, 0], 2)),
    runTest(myLength([0, 0, 0], 3)).

mySumTests :-
    runTest(mySum([], 0)),
    runTest(mySum([1], 1)),
    runTest(mySum([1, 2], 3)),
    runTest(mySum([1, 2, 3], 6)).

runTests :-
    myAppendTests,
    myMemberTests,
    myNexttoTests,
    myDeleteTests,
    myNthTests,
    myLastTests,
    myReverseTests,
    myLengthTests,
    mySumTests.
