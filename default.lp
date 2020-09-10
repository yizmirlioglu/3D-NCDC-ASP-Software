

% Default 3D-nCDC Constraints

reference(L) :- defaultrelation(K,L,J).
target(K) :- defaultrelation(K,L,J).

existdefrel(K,L) :- defaultrelation(K,L,J).

drelation(K,L) :- not -drelation(K,L), defaultrelation(K,L,J).

-drelation(K,L) :- violateddef(K,L), existdefrel(K,L).



% Minimize evidence against default

:~ -drelation(K,L), existdefrel(K,L), object(K), object(L). [1@1,K,L]




% DEFAULT CONSTRAINTS: Check condition (C1)

violateddef(K,L) :- defaultrelation(K,L,nm), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,sm), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,em), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,wm), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,nwm), {occupy(K,X,Y,Z): left(L,X), top(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,swm), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,nem), {occupy(K,X,Y,Z): right(L,X), top(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,sem), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), zbox(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,om), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), zbox(L,Z)}0.


violateddef(K,L) :- defaultrelation(K,L,na), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,sa), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,ea), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,wa), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,nwa), {occupy(K,X,Y,Z): left(L,X), top(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,swa), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,nea), {occupy(K,X,Y,Z): right(L,X), top(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,sea), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), up(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,oa), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), up(L,Z)}0.


violateddef(K,L) :- defaultrelation(K,L,nb), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,sb), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,eb), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,wb), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,nwb), {occupy(K,X,Y,Z): left(L,X), top(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,swb), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,neb), {occupy(K,X,Y,Z): right(L,X), top(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,seb), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), below(L,Z)}0.

violateddef(K,L) :- defaultrelation(K,L,ob), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), below(L,Z)}0.




% DEFAULT CONSTRAINTS: Check condition (C2)

violateddef(K,L) :- not defaultrelation(K,L,nm), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,sm), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,em), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,wm), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,nwm), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,swm), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,nem), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,sem), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), zbox(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,om), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), zbox(L,Z)}.


violateddef(K,L) :- not defaultrelation(K,L,na), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,sa), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,ea), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,wa), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,nwa), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,swa), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,nea), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,sea), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), up(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,oa), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), up(L,Z)}.


violateddef(K,L) :- not defaultrelation(K,L,nb), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,sb), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,eb), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,wb), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,nwb), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,swb), existdefrel(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,neb), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,seb), existdefrel(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), below(L,Z)}.

violateddef(K,L) :- not defaultrelation(K,L,ob), existdefrel(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), below(L,Z)}.




#show violateddef/2.
#show -drelation/2.
#show drelation/2.
