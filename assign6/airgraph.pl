% flight: FlightName, Source, Destination, FlightTime
flight(tk1726, lax, ams, 40).
flight(ab1321, lax, cdg, 90).
flight(dx1764, lhr, mad, 50).
flight(lf1245, lhr, jfk, 60).
flight(tk2214, lhr, vie, 70).
flight(kk2312, ams, jfk, 30).
flight(lf3630, ams, cdg, 45).
flight(kk0017, ams, fra, 65).
flight(lf1031, ams, vie, 50).
flight(kl1727, ams, lax, 40).
flight(tk1322, cdg, lax, 90).
flight(tx1138, cdg, mad, 20).
flight(dx1765, mad, lhr, 50).
flight(dx1765, mad, cdg, 20).
flight(sr1246, jfk, lhr, 60).
flight(tk2215, vie, lhr, 70).
flight(kk2313, jfk, ams, 30).
flight(lf3632, cdg, ams, 45).
flight(kk0018, fra, ams, 65).
flight(lf1032, vie, ams, 50).

% pathMaxCost: Source, Destination, MaxCost, Flights, ActualCost
pathMaxCost(S, D, _, [N], C) :-
    flight(N, S, D, C).
pathMaxCost(S, D, M, [N|T], A) :-
    flight(N, S, I, C),
    pathMaxCost(I, D, M, T, Q),
    A is C+Q.



runTest(Test) :-
    format('Running ~w: ', [Test]),
    once(call(Test)) ->
        format('pass~n');
        format('----FAIL----').

pathMaxCostTests :-
    runTest(pathMaxCost(lax, lax, 80, [tk1726, kl1727], 80)),
    runTest(pathMaxCost(lax, lax, 140, [tk1726, kl1727], 80)),
    runTest(pathMaxCost(lax, lax, 140, [tk1726, kk2312, kk2313, kl1727], 140)),
    runTest(pathMaxCost(lax, mad, 200, [tk1726, kk2312, sr1246, dx1764], 180)),
    runTest(pathMaxCost(lax, mad, 200, [tk1726, kk2312, kk2313, lf3630, tx1138], 165)),
    runTest(pathMaxCost(lax, mad, 200, [tk1726, lf3630, tx1138], 105)),
    runTest(pathMaxCost(lax, mad, 200, [tk1726, lf3630, lf3632, lf3630, tx1138], 195)),
    runTest(pathMaxCost(lax, mad, 200, [tk1726, kl1727, tk1726, lf3630, tx1138], 185)),
    runTest(pathMaxCost(lax, mad, 200, [tk1726, kl1727, ab1321, tx1138], 190)),
    runTest(pathMaxCost(lax, mad, 200, [ab1321, tx1138], 110)),
    runTest(pathMaxCost(lax, mad, 200, [ab1321, lf3632, lf3630, tx1138], 200)).

runTests :-
    pathMaxCostTests.
