"""Is A(K) - Pred(K) prime irregularity or a systematic error?  Compute the same average as A(K) over all integers n in the
window (weight 1 instead of log p over primes), and over primes, both against Pred(K)."""
import math, sys, numpy as np
sys.argv = [sys.argv[0]]
import thmA_numeric as T
from cypari import pari
theta = 0.9
for K in (10000, 30000, 100000, 300000, 1000000):
    sig = K ** theta; N = ((K - 1) / (4 * math.pi)) ** 2
    lo, hi = math.isqrt(int(T.a * N)), math.isqrt(int(T.b * N)) + 1
    ns = np.arange(lo, hi + 1)
    P = set(int(p) for p in pari.primes([lo, hi]))
    Tm = int(2 * hi * math.sin(200 / sig)) + 1
    ts = np.arange(0, Tm + 1); wt = np.where(ts == 0, 1.0, 2.0) * T.F2[:Tm + 1]
    An = np.empty(len(ns))
    for i, n in enumerate(ns):
        phi = np.arcsin(np.minimum(ts / (2.0 * n), 1.0))
        An[i] = (np.cos((K - 1) * phi) * T.H0h(sig * phi) * wt).sum() / (2 * T.zeta2 * T.H00) * (K - 1) / (K - 7)
    w = T.Phi(ns ** 2 / N)
    Aint = (w * An).sum() / w.sum()
    isp = np.array([int(n) in P for n in ns]); wl = w * np.log(ns) * isp
    Apr = (wl * An).sum() / wl.sum()
    pr = T.pred(K, sig, 400)
    print(f"K={K:8d}: A over integers = {Aint:+.6f}   A over primes = {Apr:+.6f}   Pred = {pr:+.6f}   ints-Pred = {Aint-pr:+.2e}   primes-Pred = {Apr-pr:+.2e}", flush=True)
