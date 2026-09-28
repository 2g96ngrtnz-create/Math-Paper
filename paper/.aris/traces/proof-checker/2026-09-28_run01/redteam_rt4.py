# RT-4 (corrected): Lemma 4.2 exactly at the boundary M = 4(K+1), with delta in (0,1/8].
import math
NMAX = 200000
lp = [1]*(NMAX+1); spf = [0]*(NMAX+1)
for p in range(2, NMAX+1):
    if spf[p] == 0:
        for k in range(p, NMAX+1, p):
            if spf[k] == 0: spf[k] = p
            lp[k] = p
tested = 0; bad = 0
for N in [5000, 20000, 200000]:
    Kmin = math.ceil(N**0.75/4) - 1
    for K in sorted(set([Kmin, Kmin+1, Kmin+7, 2*Kmin, N//40, N//16, N//8 - 1])):
        M = 4*(K+1)
        if not (N**0.75 <= M <= N): continue
        delta = (1 - math.log(M)/math.log(N))/2
        if not (0 < delta <= 1/8 + 1e-12): continue
        Y = M/(2*(K+1)); V = list(range(K+1, M+1)); par = {v: v for v in V}
        def f(a):
            while par[a] != a: par[a] = par[par[a]]; a = par[a]
            return a
        for d in V:
            for m in range(2*d, M+1, d): par[f(d)] = f(m)
        S = [x for x in V if lp[x] <= Y]
        b = max(i for i in range(40) if 2**i <= M)
        ok = len({f(x) for x in S}) == 1 and f(2**b) == f(S[0])
        tested += 1; bad += (not ok)
        print(f"  N={N:6d} K={K:6d} M={M:6d} delta={delta:.4f} Y={Y:.1f} |S_M|={len(S):3d} S_M={sorted(S)[:6]}... one component with 2^b={2**b}: {ok}")
print(f"RT-4: tested {tested} boundary cases, failures {bad}")
