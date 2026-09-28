# Exhaustive/brute-force checks of the deterministic lemmas (audit; not results).
import math, random, itertools, sys
import numpy as np

def sieve(n):
    P = list(range(n+1)); spf=[0]*(n+1)
    lp=[1]*(n+1)   # largest prime factor, lp[1]=1
    for p in range(2,n+1):
        if spf[p]==0:
            for k in range(p,n+1,p):
                if spf[k]==0: spf[k]=p
                lp[k]=p
    primes=[p for p in range(2,n+1) if spf[p]==p]
    return spf,lp,primes
NMAX=20000
spf,lp,primes=sieve(NMAX)
def factor(n):
    f={}
    while n>1:
        p=spf[n]; f[p]=f.get(p,0)+1; n//=p
    return f
def Psi(x,y): return sum(1 for n in range(1,int(x)+1) if lp[n]<=y)
def R(n,B): 
    r=1
    for p,a in factor(n).items():
        if p>B: r*=p**a
    return r
# union-find
def comps(vertices, edges):
    par={v:v for v in vertices}
    def f(a):
        while par[a]!=a: par[a]=par[par[a]]; a=par[a]
        return a
    for a,b in edges: par[f(a)]=f(b)
    return {v:f(v) for v in vertices}

bad=0
# ---- Lemma 3.1 / Prop 3.2: fibres, |V_n|<=Psi(N/n,B)<=Psi(N,B), |V_n|<=K for n>1, R_B const on components
for N in [2,3,5,10,30,100,257,1000,3000]:
    for K in sorted(set([0,1,2,3,N//10,int(N**0.5),N//3,N//2-1,N//2,N-2,N-1])):
        if not (0<=K<N): continue
        B=N//(K+1); V=range(K+1,N+1)
        E=[(d,m) for d in V for m in range(2*d,N+1,d)]
        for d,m in E:
            if m//d>B or R(d,B)!=R(m,B): bad+=1; print("L3.1a fail",N,K,d,m)
        c=comps(list(V),E); root_R={}
        for v in V:
            r=c[v]
            if r in root_R and root_R[r]!=R(v,B): bad+=1; print("L3.1b fail",N,K,v)
            root_R.setdefault(r,R(v,B))
        fib={}
        for v in V: fib.setdefault(R(v,B),[]).append(v)
        PsiNB=Psi(N,B)
        for n,Vn in fib.items():
            if len(Vn)>Psi(N/n,B) or len(Vn)>PsiNB: bad+=1; print("L3.1c fail",N,K,n)
            if n>1 and len(Vn)>K: bad+=1; print("L3.1c(K) fail",N,K,n)
        F1=[v for v in V if lp[v]<=B]
        if len(F1)!=PsiNB-Psi(K,B): bad+=1; print("|F1| fail",N,K)
print("Lemma 3.1 / Prop 3.2 checks done, failures so far:",bad)

# ---- Lemma 4.2 (doubling): for many (N,K,delta) with M>=4(K+1), S_M in one component of G_{M,K} containing 2^b
cnt=0
for N in [50,100,500,2000,10000,20000]:
    for delta in [0.01,0.05,0.1,0.125]:
        M=N**(1-2*delta)
        for K in range(0,int(M/4)):
            if not M>=4*(K+1): continue
            if K>60 and K%17: continue
            Y=M/(2*(K+1)); V=list(range(K+1,int(M)+1))
            E=[(d,m) for d in V for m in range(2*d,int(M)+1,d)]
            c=comps(V,E)
            S=[x for x in V if lp[x]<=Y]
            b=1
            while 2**(b+1)<=M: b+=1
            assert M/2<2**b<=M
            if (not S) or len({c[x] for x in S})!=1 or c[2**b]!=c[S[0]]:
                bad+=1; print("L4.2 fail",N,delta,K)
            cnt+=1
print("Lemma 4.2 checked on",cnt,"cases; failures so far:",bad)

# ---- Lemma 4.5(a)-(c): brute force for parameter sets satisfying (H1)-(H3)
def omega_z(m,z): return sum(1 for p in factor(m) if p<=z)
tested=0
for N in [2000,5000,20000]:
    for eta,delta,s0 in [(0.9,0.1125,1),(0.8,0.1,1),(0.95,0.11875,1)]:
        z=N**(delta/s0)
        if not (delta<=eta/8 and N**(eta/4)>=4 and z>=2): continue
        for K in range(0,int(N**(1-eta))+1):
            M=N**(1-2*delta); Y=M/(2*(K+1)); B=N//(K+1)
            assert M>=4*(K+1)                     # (a)
            U=[m for m in range(int(N**(1-delta))+1,N+1) if m>N**(1-delta) and lp[m]<=Y and omega_z(m,z)>=s0]
            for m in U:
                assert m>M and lp[m]<=B            # (b)
                D=[d for d in range(K+1,int(M)+1) if m%d==0 and lp[d]<=Y]
                if len(D)<s0+1: bad+=1; print("L4.5c fail",N,K,m,D)
            # (d) count vs bound (C_1-free part: exact count of the three sets)
            F1=[m for m in range(K+1,N+1) if lp[m]<=B]
            Uset=set(U); miss=[m for m in F1 if m not in Uset]
            s1=sum(1 for m in range(1,N+1) if m<=N**(1-delta))
            s2=sum(1 for m in range(1,N+1) if Y<lp[m]<=B)
            s3=sum(1 for m in range(1,N+1) if omega_z(m,z)<s0)
            if len(miss)>s1+s2+s3: bad+=1; print("L4.5d union fail",N,K)
            tested+=len(U)
print("Lemma 4.5 (c) checked on",tested,"integers m in U; failures so far:",bad)

# ---- Lemma 2.4 numerically
for N in [1000,20000]:
    for z in [2,3,10,50,200]:
        L=sum(1/p for p in primes if p<=z)
        tot=sum((omega_z(m,z)-L)**2 for m in range(1,N+1))
        if tot>3*N*L: bad+=1; print("L2.4 fail",N,z)
        for s in [x/4*L for x in range(0,3)]:
            c=sum(1 for m in range(1,N+1) if omega_z(m,z)<s)
            if c>12*N/L: bad+=1; print("L2.4 tail fail",N,z,s)
print("Lemma 2.4 checked; failures so far:",bad)

# ---- Remark 5.1 identity N - Psi(N,B) = sum_{B<p<=N} floor(N/p) for K+1<=sqrt N
for N in [16,17,100,1000,20000]:
    for K in range(0,int(math.isqrt(N))):
        if K+1>math.sqrt(N): continue
        B=N//(K+1)
        if N-Psi(N,B)!=sum(N//p for p in primes if B<p<=N): bad+=1; print("R5.1 fail",N,K)
print("Remark 5.1 identity checked; failures so far:",bad)

# ---- Lemma A.1 random test + counterexample
random.seed(0)
for t in range(20000):
    k=random.randint(1,12); x=sorted([random.random()**random.choice([1,3,6]) for _ in range(k)],reverse=True)
    s=sum(x); x=[v/s for v in x]
    th=random.uniform(0.001,1/3)
    if x[0]<1-th:
        ok=any(th-1e-12<=sum(x[i] for i in I)<=0.5+1e-12 for r in range(1,k+1) for I in itertools.combinations(range(k),r))
        if not ok: bad+=1; print("A.1 fail",x,th)
print("Lemma A.1 random tests done; failures so far:",bad)
print("TOTAL FAILURES:",bad)
