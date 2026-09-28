import numpy as np, heapq, math
N=100000
tau=np.zeros(N+1,dtype=np.int64)
for d in range(1,N+1): tau[d::d]+=1
tauN=int(tau[1:].max())
deg=np.array([0]+[int(tau[m])-1 + N//m - 1 for m in range(1,N+1)])
eps=0.5
Kmax=int(N*eps/2/(tauN+5))
print("tau_N=",tauN," hypothesis (N/K)(eps/2)>=tau_N+5 allows K<=",Kmax)
bad=0
order=sorted(range(1,N+1),key=lambda v:-deg[v])
for K in range(1,Kmax+1):
    dK=deg[order[K-1]]
    ge=[v for v in range(1,N+1) if deg[v]>=dK]
    if max(ge)>math.floor((1+eps)*K): bad+=1; print("static upper fail",K)
    for v in range(1,math.floor((1-eps)*K)+1):
        if not (deg[v]>dK or (deg[v]==dK and len(ge)==K)): bad+=1; print("static lower fail",K,v)
print("static checked; failures",bad)
# adaptive attack with two tie-break rules, simulate once up to Kmax and check prefix sets
def adaptive(Kmax, tiebreak):
    d=deg.copy(); removed=np.zeros(N+1,bool); T=[]
    heap=[(-d[v], tiebreak*v, v) for v in range(1,N+1)]; heapq.heapify(heap)
    while len(T)<Kmax:
        nd,tb,v=heapq.heappop(heap)
        if removed[v] or -nd!=d[v]: continue
        removed[v]=True; T.append(v)
        nbrs=[u for u in range(1,int(math.isqrt(v))+1) if v%u==0 for u in {u, v//u}]
        nbrs=set(nbrs)|set(range(2*v,N+1,v)); nbrs.discard(v)
        for u in nbrs:
            if not removed[u]:
                d[u]-=1; heapq.heappush(heap,(-d[u],tiebreak*u,u))
    return T
for tb in (+1,-1):
    T=adaptive(Kmax,tb)
    for K in range(1,Kmax+1):
        S=set(T[:K])
        if max(S)>math.floor((1+eps)*K) or not set(range(1,math.floor((1-eps)*K)+1))<=S:
            bad+=1; print("adaptive fail",tb,K,sorted(S)[-3:])
    print("adaptive (tiebreak",tb,") checked; failures",bad, "; first 12 removed:",T[:12])
