"""pred depends on K only through kappa = 2 pi sigma/(K-1) (and (K-1)/(K-7)); show pred(kappa) -> limit as kappa -> 0.
Both sums run over |t| <= 3000, where the t-series has converged to 1e-9."""
import math, numpy as np, sys
sys.argv = [sys.argv[0]]
import thmA_numeric as T
TM = 3000
lim = T.limit(TM)
print(f"limit = {lim:+.8f}")
for kap in (2.5, 1.58, 1.0, 0.3, 0.1, 0.03, 0.01, 0.003):
    v = sum((1 if t == 0 else 2) * T.F2[t] * T.I_K(t, kap) for t in range(0, TM + 1)) / (2 * T.zeta2 * T.H00) / T.I0
    print(f"kappa = {kap:6.3f}: finite-K main term = {v:+.8f}   (limit - main term) = {lim - v:+.3e}   / kappa^2 = {(lim - v)/kap**2:+.4f}", flush=True)
