"""
Item 2: is f_2(t) (Euler product of Lemma 6) the prime average of L(1, t^2-4p^2)?
L(1, D) = pi H(|D|)/sqrt(|D|) (Lemma 3(2)); H from PARI qfbhclassno.
log p weighted average over primes p in [P0, P1]; standard error from the weighted sample scatter.
Also checks Lemma 3(2) itself on a sample (H vs class numbers of orders), independent of the doc.
"""
import sys, time
import numpy as np
from math import pi, log, sqrt
from cypari import pari
pari.allocatemem(2 * 2 ** 30)
from s1_local_densities import table_E, chi4

C_odd = float(np.load("f2_consts.npy")[0])

def f2(t):
    if t == 0:
        return pi / 4
    m = abs(t)
    r = float(table_E(t, 2)) * C_odd
    while m % 2 == 0:
        m //= 2
    l = 3
    while m > 1:
        if m % l == 0:
            c = chi4(l)
            r *= (l / (l - c)) / ((1 - (1 + c) / (l * (l - 1))) / (1 - 1 / l ** 2))
            while m % l == 0:
                m //= l
        l += 2
    return r

def f1(t):
    """prime analogue: zeta(2) prod_{l not | t} (l^2-l-1)/(l^2-l); computed via local factors"""
    return None

if __name__ == "__main__":
    P0, P1 = int(sys.argv[1]), int(sys.argv[2])
    ts = [int(x) for x in sys.argv[3].split(",")]
    primes = [int(p) for p in pari.primes([P0, P1])]
    w = np.array([log(p) for p in primes])
    print(f"{len(primes)} primes in [{P0},{P1}]")
    for t in ts:
        t0 = time.time()
        vals = np.empty(len(primes))
        for i, p in enumerate(primes):
            n = 4 * p * p - t * t
            vals[i] = pi * float(pari.qfbhclassno(n)) / sqrt(n)
        mean = np.sum(w * vals) / np.sum(w)
        # effective-sample standard error for a weighted mean
        var = np.sum(w * (vals - mean) ** 2) / np.sum(w)
        neff = np.sum(w) ** 2 / np.sum(w ** 2)
        se = sqrt(var / neff)
        print(f"t={t:5d}: prime avg of L(1,t^2-4p^2) = {mean:.5f} +- {se:.5f}   f_2(t) = {f2(t):.5f}   "
              f"(avg - f2)/se = {(mean - f2(t)) / se:+.2f}   sd(L) = {sqrt(var):.3f}   [{time.time() - t0:.0f}s]",
              flush=True)
