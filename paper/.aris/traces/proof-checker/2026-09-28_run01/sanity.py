# Quick sanity test of Lemma (doubling connectivity) and Lemma (robust edges). Not a result.
import numpy as np, sys
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
N = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
rng = np.random.default_rng(1)
# largest prime factor
lpf = np.arange(N + 1)
for p in range(2, int(N**0.5) + 1):
    if lpf[p] == p:
        for k in range(p * p, N + 1, p):
            pass
spf = np.zeros(N + 1, dtype=np.int64)
P = np.ones(N + 1, dtype=np.int64)  # largest prime factor, P[1]=1
for p in range(2, N + 1):
    if spf[p] == 0:
        spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
        P[p::p] = p
# edges d | m, d<m
src, dst = [], []
for d in range(1, N // 2 + 1):
    ms = np.arange(2 * d, N + 1, d)
    src.append(np.full(ms.size, d)); dst.append(ms)
src = np.concatenate(src); dst = np.concatenate(dst)
for K, Mdiv in [(1, 40), (10, 40), (46, 40), (316, 40), (1000, 20), (2154, 10)]:
    M = N / Mdiv
    Y = M / (2 * (K + 1))
    B = N // (K + 1)
    # deterministic check: S_M in one component of G_{M,K}
    sel = (src > K) & (dst <= M)
    g = coo_matrix((np.ones(sel.sum()), (src[sel], dst[sel])), shape=(N + 1, N + 1))
    _, lab = connected_components(g, directed=False)
    S = [x for x in range(K + 1, int(M) + 1) if P[x] <= Y]
    det_ok = len(set(lab[S])) == 1
    # random orientation of G_{N,K}
    sel = src > K
    s, t = src[sel], dst[sel]
    flip = rng.random(s.size) < 0.5
    a = np.where(flip, s, t); b = np.where(flip, t, s)   # default m -> d, reversed w.p. rho
    h = coo_matrix((np.ones(a.size), (a, b)), shape=(N + 1, N + 1))
    _, lab2 = connected_components(h, directed=True, connection='strong')
    lab2 = lab2[K + 1:]
    sizes = np.bincount(lab2)
    big = sizes.argmax()
    S_in_one = len(set(lab2[np.array(S) - K - 1])) == 1
    S_in_big = S_in_one and lab2[S[0] - K - 1] == big
    F1 = np.array([x for x in range(K + 1, N + 1) if P[x] <= B])
    frac = np.mean(lab2[F1 - K - 1] == big)
    print(f"K={K:5d} M={M:8.0f} |S_M|={len(S):5d} det_connected={det_ok} S_M_in_one_SCC={S_in_one} in_giant={S_in_big} "
          f"Phi/N={sizes.max()/N:.4f} |F1|/N={F1.size/N:.4f} frac(F1 in giant)={frac:.4f}")
