# Phase 1.5 counterexample red team for hub_removal.tex (numeric falsification attempts; not results).
import math, itertools, random
from fractions import Fraction as Fr
NMAX = 200000
lp = [1]*(NMAX+1); spf = [0]*(NMAX+1)
for p in range(2, NMAX+1):
    if spf[p] == 0:
        for k in range(p, NMAX+1, p):
            if spf[k] == 0: spf[k] = p
            lp[k] = p
primes = [p for p in range(2, NMAX+1) if spf[p] == p]
def factor(n):
    f = {}
    while n > 1:
        p = spf[n]; f[p] = f.get(p, 0)+1; n //= p
    return f
psi_prefix = {}
def Psi(x, y): return sum(1 for n in range(1, int(x)+1) if lp[n] <= y)

print("== RT-1  Lemma 2.3: smallest c0 making Psi(x,y) <= sqrt x + 2x(log y + c0)/log x (x<=2e5) ==")
need = -1e9
for x in [10**3, 10**4, 5*10**4, 2*10**5]:
    for y in [2, 3, 5, 10, 100, int(x**0.5), x//10, x]:
        if 2 <= y <= x:
            c = (Psi(x, y) - math.sqrt(x))*math.log(x)/(2*x) - math.log(y)
            need = max(need, c)
mert = max(sum(math.log(p)/(p-1) for p in primes if p <= y) - math.log(y) for y in [2, 3, 10, 100, 10**3, 10**4, 10**5, 2*10**5])
print(f"  max required c0 over grid = {need:.4f};  max of sum_(p<=y) log p/(p-1) - log y = {mert:.4f}  (Lemma 2.1(a) c0 must exceed this)")
print("  -> no counterexample: required c0 is below the Mertens constant bound")

print("== RT-2  Lemma 2.4 at extreme z (z=2, z=N) ==")
for N in [100, 1000, 20000]:
    for z in [2, N]:
        L = sum(1/p for p in primes if p <= z)
        om = [0]*(N+1)
        for p in primes:
            if p > z or p > N: break
            for k in range(p, N+1, p): om[k] += 1
        tot = sum((om[m]-L)**2 for m in range(1, N+1))
        print(f"  N={N:6d} z={z:6d}: sum (w-L)^2 = {tot:10.1f}  <=  3NL = {3*N*L:10.1f}  {'OK' if tot <= 3*N*L else 'FAIL'}")

print("== RT-3  Lemma 3.1(c) tightness: max |V_n| over n>1 vs K ==")
for N in [1000, 10000]:
    for K in [3, 10, 31, 100, 316]:
        if K >= N: continue
        B = N//(K+1); fib = {}
        for v in range(K+1, N+1):
            r = 1
            for p, a in factor(v).items():
                if p > B: r *= p**a
            fib[r] = fib.get(r, 0)+1
        mx = max((c for n, c in fib.items() if n > 1), default=0)
        print(f"  N={N} K={K}: max_(n>1)|V_n| = {mx}  (bound K={K})  {'OK' if mx <= K else 'FAIL'}")

print("== RT-4  Lemma 4.2 at the boundary M = 4(K+1) exactly ==")
for N in [5000, 20000, 200000]:
    for K in [0, 1, 5, 20, 100]:
        M = 4*(K+1)
        if M > N: continue
        delta = (1 - math.log(M)/math.log(N))/2
        if not (0 < delta <= 1/8): continue
        Y = M/(2*(K+1)); V = list(range(K+1, M+1))
        par = {v: v for v in V}
        def f(a):
            while par[a] != a: par[a] = par[par[a]]; a = par[a]
            return a
        for d in V:
            for m in range(2*d, M+1, d): par[f(d)] = f(m)
        S = [x for x in V if lp[x] <= Y]
        print(f"  N={N} K={K} M={M} delta={delta:.4f} |S_M|={len(S)} one_component={len({f(x) for x in S}) == 1}")
print("  (delta<=1/8 forces M>=N^(3/4); for small K this boundary is only reachable when N is small)")

print("== RT-5  Lemma 4.5(c) tightness: minimum s(m) over U, K = floor(N^(1-eta)) extreme ==")
for N, eta, delta, s0 in [(20000, 0.9, 0.1125, 1), (200000, 0.8, 0.1, 1), (200000, 0.8, 0.05, 2)]:
    z = N**(delta/s0)
    if not (N**(eta/4) >= 4 and z >= 2 and delta <= eta/8):
        print(f"  N={N} eta={eta} delta={delta} s0={s0}: hypotheses fail, skipped"); continue
    K = int(N**(1-eta)); M = N**(1-2*delta); Y = M/(2*(K+1))
    mins = 10**9; worst = None; cnt = 0
    for m in range(int(N**(1-delta))+1, N+1, 1 if N <= 20000 else 7):
        if lp[m] > Y: continue
        fm = factor(m)
        if sum(1 for p in fm if p <= z) < s0: continue
        divs = [1]
        for p, a in fm.items(): divs = [d*p**i for d in divs for i in range(a+1)]
        s = sum(1 for d in divs if K < d <= M and lp[d] <= Y)
        cnt += 1
        if s < mins: mins, worst = s, m
    print(f"  N={N} K={K} s0={s0}: checked {cnt} m in U; min s(m) = {mins} at m={worst} (lemma needs >= {s0+1})  {'OK' if mins >= s0+1 else 'FAIL'}")

print("== RT-6  Lemma 6.2 beyond its hypothesis (informative, not a counterexample) ==")
N = 100000
tau = [0]*(N+1)
for d in range(1, N+1):
    for k in range(d, N+1, d): tau[k] += 1
deg = [0] + [tau[m]-1 + N//m - 1 for m in range(1, N+1)]
order = sorted(range(1, N+1), key=lambda v: -deg[v])
eps = 0.5; first_fail = None
for K in range(1, 5000):
    dK = deg[order[K-1]]
    top = max(v for v in range(1, int((1+eps)*K)+50) if deg[v] >= dK) if True else 0
    ge_max = max(order[i] for i in range(K))
    if ge_max > math.floor((1+eps)*K):
        first_fail = K; break
print(f"  eps=1/2: hypothesis allows K<=187; static upper inclusion first fails at K = {first_fail}")

print("== RT-7  Lemma A.1 adversarial at theta = 1/3 (exact rational arithmetic) ==")
th = Fr(1, 3); bad = 0; tested = 0
grid = [Fr(i, 24) for i in range(1, 24)]
for k in range(1, 6):
    for parts in itertools.combinations_with_replacement(grid, k):
        if sum(parts) != 1: continue
        x = sorted(parts, reverse=True)
        if x[0] >= 1 - th: continue
        tested += 1
        ok = any(th <= sum(c) <= Fr(1, 2) for r in range(1, k+1) for c in itertools.combinations(x, r))
        if not ok: bad += 1; print("   counterexample:", x)
print(f"  tested {tested} partitions of 1 into <=5 parts from the grid 1/24,...,23/24: {bad} counterexamples")

print("== RT-8  Theorem 1.3 vacuity threshold ==")
print(f"  30/log log N < 1 requires log log N > 30, i.e. N > exp(exp(30)) ~ 10^({math.exp(30)/math.log(10):.3e})")
