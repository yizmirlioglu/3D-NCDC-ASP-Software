

% ASP subprogram for disjunctive 3D-nCDC Constraints

existrelation(K,L) :- disjrelation(K,L,I,J).

reference(L) :- disjrelation(K,L,I,J).
target(K) :- disjrelation(K,L,I,J).

disjind(K,L,I) :- disjrelation(K,L,I,J).
existdisjrel(K,L) :- disjrelation(K,L,I,J).



% Choose one basic relation from every disjunctive relation

1{chosendisj(K,L,I): disjind(K,L,I)}1 :- existdisjrel(K,L).

relation(K,L,J) :- disjrelation(K,L,I,J), chosendisj(K,L,I).




#show chosendisj/3.


