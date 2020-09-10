

% Subprogram for Inferring Unknown or Missing 3D-nCDC Relations


% Determine known relations from the given 3D-nCDC network

known(K,L)  :- existrelation(K,L).
known(K,L)  :- drelation(K,L).


% Infer unknown or missing relations

1{infer(K,L,J): alltiles(J)} :- not known(K,L), toinfer(K,L).

existinfer(K,L) :- not known(K,L), toinfer(K,L).
existinfer(K,L) :- infer(K,L,J).

reference(L) :- existinfer(K,L).
target(K) :- existinfer(K,L).



%  ASP Rules for condition (C1)

inferviolated(K,L) :- infer(K,L,nm), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,sm), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,em), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,wm), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,nwm), {occupy(K,X,Y,Z): left(L,X), top(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,swm), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,nem), {occupy(K,X,Y,Z): right(L,X), top(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,sem), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), zbox(L,Z)}0.

inferviolated(K,L) :- infer(K,L,om), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), zbox(L,Z)}0.


inferviolated(K,L) :- infer(K,L,na), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,sa), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,ea), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,wa), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,nwa), {occupy(K,X,Y,Z): left(L,X), top(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,swa), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,nea), {occupy(K,X,Y,Z): right(L,X), top(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,sea), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), up(L,Z)}0.

inferviolated(K,L) :- infer(K,L,oa), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), up(L,Z)}0.


inferviolated(K,L) :- infer(K,L,nb), {occupy(K,X,Y,Z): hbox(L,X), top(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,sb), {occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,eb), {occupy(K,X,Y,Z): right(L,X), vbox(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,wb), {occupy(K,X,Y,Z): left(L,X), vbox(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,nwb), {occupy(K,X,Y,Z): left(L,X), top(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,swb), {occupy(K,X,Y,Z): left(L,X), bottom(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,neb), {occupy(K,X,Y,Z): right(L,X), top(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,seb), {occupy(K,X,Y,Z): right(L,X), bottom(L,Y), below(L,Z)}0.

inferviolated(K,L) :- infer(K,L,ob), {occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), below(L,Z)}0.



%  ASP Rules for condition (C2)

inferviolated(K,L) :- not infer(K,L,nm), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,sm), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,em), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,wm), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,nwm), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,swm), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,nem), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,sem), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), zbox(L,Z)}.

inferviolated(K,L) :- not infer(K,L,om), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), zbox(L,Z)}.


inferviolated(K,L) :- not infer(K,L,na), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,sa), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,ea), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,wa), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,nwa), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,swa), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,nea), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,sea), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), up(L,Z)}.

inferviolated(K,L) :- not infer(K,L,oa), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), up(L,Z)}.


inferviolated(K,L) :- not infer(K,L,nb), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), top(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,sb), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), bottom(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,eb), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), vbox(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,wb), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), vbox(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,nwb), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), top(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,swb), existinfer(K,L), 1{occupy(K,X,Y,Z): left(L,X), bottom(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,neb), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), top(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,seb), existinfer(K,L), 1{occupy(K,X,Y,Z): right(L,X), bottom(L,Y), below(L,Z)}.

inferviolated(K,L) :- not infer(K,L,ob), existinfer(K,L), 1{occupy(K,X,Y,Z): hbox(L,X), vbox(L,Y), below(L,Z)}.



% Inferred 3D-nCDC relations must hold

:- inferviolated(K,L).




#show infer/3.

