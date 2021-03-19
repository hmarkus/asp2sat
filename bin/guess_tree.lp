% guess of backdoor vars
M { abs(X) : p(X)} B :- M = #min{ 0; B}, b(B).

% limit abs costs
:~ abs(X). [1,X]

% (non-abs) vertices are in its own bucket
bucket(X,X) :- edge(X,_), not abs(X).
bucket(X,X) :- edge(_,X), not abs(X).

% eat neighbors of eaten non-abs neighbors
bucket(B,Z) :- bucket(B,Y), not abs(Z), edge(Y,Z).
bucket(B,Z) :- bucket(B,Y), not abs(Z), edge(Z,Y).

% trees only
:- bucket(B,_), V = #count { X: bucket(B,X) }, E = #count { X,Y: edge(X,Y), X<Y, bucket(B,X), bucket(B,Y); X,Y: edge(Y,X), X<Y, bucket(B,X), bucket(B,Y) }, E > V - 1.


#show abs/1.
