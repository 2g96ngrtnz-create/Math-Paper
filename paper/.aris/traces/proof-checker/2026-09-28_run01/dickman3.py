import numpy as np
h = 1e-5; n = int(round(1/h)); U = 11
m = n * U + 1
rho = np.ones(m)
for i in range(n + 1, m):
    if (i - 1) % 20000 == 0 or i == n + 1:   # recompute window sum from scratch periodically
        S = h * (rho[i-1-n]/2 + rho[i-n:i-1].sum() + rho[i-1]*0)  # window for index i-1 is [i-1-n, i-1]
        S = h * (rho[i-n-1]/2 + rho[i-n:i-1].sum())
        # convert to window for i: h*(rho[i-n]/2 + sum_{j=i-n+1}^{i-1} rho_j)
        S = S - h*rho[i-n-1]/2 - h*rho[i-n]/2 + h*rho[i-1]
    else:
        S = S - h*(rho[i-n-1]/2) - h*(rho[i-n]/2) + h*rho[i-1]
    rho[i] = S / (i*h - h/2)
def r(u): return np.interp(u, np.arange(m)*h, rho)
for u in [2, 2.5, 3, 4, 5, 6, 7, 8, 9, 10]:
    print(u, "%.8g" % r(u))
