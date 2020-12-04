{a(1..3)}.
{b(2..4)}.
c(X) :- a(X), b(X).
d(X) :- a(X), not b(X).
