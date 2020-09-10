
% ASP program for basic 3D-nCDC networks

xcoord(0..M-1) :- hsize(M).
ycoord(0..N-1) :- vsize(N).
zcoord(0..P-1) :- zsize(P).


% This code works for both complete and incomplete networks
% Below we find, directional constraint is specified for which pair of objects

existrelation(K,L) :- relation(K,L,J).

reference(L) :- existrelation(_,L).
target(K) :- existrelation(K,_).


% Nondeterministically guess infimum and supremum of
% each spatial variable over x,y,z axes

1{infx(K,X): xcoord(X)}1 :- object(K).
1{supx(K,X): xcoord(X)}1 :- object(K).
1{infy(K,Y): ycoord(Y)}1 :- object(K).
1{supy(K,Y): ycoord(Y)}1 :- object(K).
1{infz(K,Z): zcoord(Z)}1 :- object(K).
1{supz(K,Z): zcoord(Z)}1 :- object(K).


% Constraints on inf and sup

:- X2<X1, infx(K,X1), supx(K,X2), object(K).
:- Y2<Y1, infy(K,Y1), supy(K,Y2), object(K).
:- Z2<Z1, infz(K,Z1), supz(K,Z2), object(K).


% Generate cells for all objects and take projection on each axis

1{occupy(K,X,Y,Z): xcoord(X), ycoord(Y), zcoord(Z)} :- object(K).

xoccupy(K,X) :- occupy(K,X,Y,Z).
yoccupy(K,Y) :- occupy(K,X,Y,Z).
zoccupy(K,Z) :- occupy(K,X,Y,Z).


% Ensure that every object has a cell at its borders so that infimum and supremum holds

:- not xoccupy(K,X1), infx(K,X1).
:- not xoccupy(K,X2), supx(K,X2).
:- not yoccupy(K,Y1), infy(K,Y1).
:- not yoccupy(K,Y2), supy(K,Y2).
:- not zoccupy(K,Z1), infz(K,Z1).
:- not zoccupy(K,Z2), supz(K,Z2).


% Test  bounds of objects

:- xoccupy(K,X), X<X1, infx(K,X1).
:- xoccupy(K,X), X>X2, supx(K,X2).
:- yoccupy(K,Y), Y<Y1, infy(K,Y1).
:- yoccupy(K,Y), Y>Y2, supy(K,Y2).
:- zoccupy(K,Z), Z<Z1, infz(K,Z1).
:- zoccupy(K,Z), Z>Z2, supz(K,Z2).



% Identify 27 tiles of an object based on left/right, top/bottom, above/below

hbox(K,X1..X2) :- infx(K,X1), supx(K,X2).
right(K,X2+1..M-1) :- supx(K,X2), hsize(M).
left(K,0..X1-1) :- infx(K,X1).

vbox(K,Y1..Y2) :- infy(K,Y1), supy(K,Y2).
top(K,Y2+1..N-1) :- supy(K,Y2), vsize(N).
bottom(K,0..Y1-1) :- infy(K,Y1).

zbox(K,Z1..Z2) :- infz(K,Z1), supz(K,Z2).
up(K,Z2+1..P-1) :- supz(K,Z2), zsize(P).
below(K,0..Z1-1) :- infz(K,Z1).



% Rules for condition (C1): Check whether generated objects satisfy directional constraints

violated(K,L) :- relation(K,L,nm), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,sm), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,em), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,wm), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,nwm), {occupy(K,X,Y,Z): left(L,X), top(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,swm), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,nem), {occupy(K,X,Y,Z): right(L,X), top(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,sem), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), zbox(L,Z)}0.

violated(K,L) :- relation(K,L,om), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), zbox(L,Z)}0.


violated(K,L) :- relation(K,L,na), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,sa), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,ea), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,wa), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,nwa), {occupy(K,X,Y,Z): left(L,X), top(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,swa), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,nea), {occupy(K,X,Y,Z): right(L,X), top(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,sea), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), up(L,Z)}0.

violated(K,L) :- relation(K,L,oa), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), up(L,Z)}0.


violated(K,L) :- relation(K,L,nb), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,sb), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,eb), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,wb), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,nwb), {occupy(K,X,Y,Z): left(L,X), top(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,swb), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,neb), {occupy(K,X,Y,Z): right(L,X), top(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,seb), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), below(L,Z)}0.

violated(K,L) :- relation(K,L,ob), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), below(L,Z)}0.



% Rules for condition (C2)

violated(K,L) :- not relation(K,L,nm), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,sm), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,em), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,wm), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,nwm), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,swm), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,nem), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,sem), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), zbox(L,Z)}.

violated(K,L) :- not relation(K,L,om), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), zbox(L,Z)}.


violated(K,L) :- not relation(K,L,na), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,sa), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,ea), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,wa), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,nwa), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,swa), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,nea), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,sea), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), up(L,Z)}.

violated(K,L) :- not relation(K,L,oa), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), up(L,Z)}.


violated(K,L) :- not relation(K,L,nb), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,sb), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,eb), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,wb), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,nwb), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,swb), existrelation(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,neb), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,seb), existrelation(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), below(L,Z)}.

violated(K,L) :- not relation(K,L,ob), existrelation(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), below(L,Z)}.



% No 3D-nCDC constraint must be violated:

:- violated(K,L).




#show occupy/4.



