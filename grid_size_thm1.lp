
numobj(N) :- N=#count{K:object(K)}.


hsize(2*N-1) :- numobj(N).
vsize(2*N-1) :- numobj(N).
zsize(2*N-1) :- numobj(N).



#show hsize/1.
#show vsize/1.
#show zsize/1.

