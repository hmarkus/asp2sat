b(1..100).
a(X):-b(X), not na(X).
na(X):-b(X), not a(X).
