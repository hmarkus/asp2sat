b(1..5).
a(X):-b(X), not na(X).
na(X):-b(X), not a(X).
