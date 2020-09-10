

% Check connectedness  by connected closure  (recursively)
% First find the stem cell for each object (left-bottom-below cell of it)

leftside(K,Y,Z) :- occupy(K,X1,Y,Z), infx(K,X1), target(K).

leftborder(K,Y) :- occupy(K,X1,Y,Z), infx(K,X1), target(K).

lymin(K,Y1) :- Y1=#min{Y: leftborder(K,Y)}, target(K).

zborder(K,Z) :- leftside(K,Y1,Z), lymin(K,Y1), target(K).

zmin(K,Z1) :- Z1=#min{Z: zborder(K,Z)}, target(K).


stem(K,X1,Y1,Z1) :- lymin(K,Y1), zmin(K,Z1), infx(K,X1), target(K).



% Form a set of cells connected to the stem cell and add neighbor cells to the set

connset(K,X,Y,Z) :- stem(K,X,Y,Z), target(K).
connset(K,X-1,Y,Z) :- connset(K,X,Y,Z), occupy(K,X-1,Y,Z), target(K).
connset(K,X+1,Y,Z) :- connset(K,X,Y,Z), occupy(K,X+1,Y,Z), target(K).
connset(K,X,Y-1,Z) :- connset(K,X,Y,Z), occupy(K,X,Y-1,Z), target(K).
connset(K,X,Y+1,Z) :- connset(K,X,Y,Z), occupy(K,X,Y+1,Z), target(K).
connset(K,X,Y,Z-1) :- connset(K,X,Y,Z), occupy(K,X,Y,Z-1), target(K).
connset(K,X,Y,Z+1) :- connset(K,X,Y,Z), occupy(K,X,Y,Z+1), target(K).


% If there is a cell which is not in connected closure of the object, then it is disconnected

:- occupy(K,X,Y,Z), not connset(K,X,Y,Z), target(K).


