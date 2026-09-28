# Regression trend check for Lemma 2.7 (not a proof): Psi(N, N^(1/u))/N versus rho_Dick(u).
import numpy as np, math
NMAX = 10**7
lp = np.ones(NMAX+1, dtype=np.int64)
for p in range(2, NMAX+1):
    if lp[p] == 1:            # p is prime (not yet assigned a prime factor)
        lp[p::p] = p
lp[1] = 1
rho = {1.5: 1-math.log(1.5), 2.0: 1-math.log(2), 3.0: 0.0486083882}
for N in [10**4, 10**5, 10**6, 10**7]:
    row = []
    for u, r in rho.items():
        y = N**(1/u)
        val = np.count_nonzero(lp[1:N+1] <= y)/N
        row.append(f"u={u}: {val:.4f} (rho={r:.4f}, diff={val-r:+.4f})")
    print(f"N=1e{int(math.log10(N))}: " + "; ".join(row))
