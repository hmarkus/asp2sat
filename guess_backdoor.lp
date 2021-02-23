%selection of buckets, 19 vertices
b(1000).

% guess of backdoor vars
M { abs(X) : p(X)} B :- M = #min{ 0; B}, b(B).

% limit abs costs
:~ abs(X). [1,X]

#show abs/1.
