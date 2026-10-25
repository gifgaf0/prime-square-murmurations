"""
Normalization check against the companion doc: nu_k(E) = sum mass * y^(1/k-1) / int_E y^(1/k-1) dy,
mass (c/m^3) T_k(c) at y=(c/m)^2.  For k=2: (1/Z2) sum T_2(c)/m^2,  Z2 = 2(sqrt b - sqrt a).
c-ordered partial sums (Theorem B's ordering) and m-ordered partial sums (the companion's ordering).
"""
import sys, time
import numpy as np
from math import sqrt, floor, ceil, pi
from s5_theoremB import sieve, arith_arrays

ZETA2 = pi ** 2 / 6
companion = {(0.2, 0.3): (None, 0.700), (0.85, 1.15): (2.045, 1.980), (1.6, 1.95): (0.027, -0.779),
             (2.0, 2.5): (0.293, -0.510), (3.5, 4.5): (1.636, 1.583), (5.5, 7.0): (0.085, 0.622),
             (8.0, 10.0): (0.526, -1.063)}

def conv(R, coef, MU, C):
    out = np.zeros(C + 1)
    sq = np.nonzero(MU[1:C + 1])[0] + 1
    for d in sq:
        out[d::d] += MU[d] * coef[d] * R[1:C // d + 1]
    return out

if __name__ == "__main__":
    C = int(float(sys.argv[1])); M = int(sys.argv[2])
    t0 = time.time()
    primes = sieve(C)
    T2, T1, PHI, MU = arith_arrays(C, primes)
    d = np.arange(C + 1, dtype=float); d[0] = 1
    for (a, b), (nu1c, nu2c) in companion.items():
        top = int(C / sqrt(a)) + 2
        mm = np.arange(top + 1, dtype=float); mm[0] = np.inf
        H2 = np.cumsum(1 / mm ** 2); H3 = np.cumsum(1 / mm ** 3)
        n = np.arange(C + 1)
        hi = np.floor(n / sqrt(a)).astype(np.int64); lo = np.ceil(n / sqrt(b)).astype(np.int64) - 1
        lo[lo < 0] = 0
        R2 = H2[hi] - H2[lo]; R3 = H3[hi] - H3[lo]
        R2[0] = R3[0] = 0
        inner2 = conv(R2, 1 / d ** 2, MU, C)
        inner3 = conv(R3, 1 / d ** 3, MU, C) * np.arange(C + 1)
        Z2 = 2 * (sqrt(b) - sqrt(a))
        S2 = np.cumsum(T2 * inner2) / Z2
        S1 = np.cumsum(T1 * inner3) / (b - a)
        Spl = np.cumsum(T1 * inner2) / Z2
        line = f"E=[{a},{b}]: nu2 c-ordered C=1e4,1e5,{C:.0e}: {S2[10**4]:+.5f} {S2[10**5]:+.5f} {S2[C]:+.5f} (companion {nu2c:+.3f})"
        line += f" | nu1 {S1[C]:+.5f} (companion {nu1c})" + f" | prime-like for squares {Spl[C]:+.5f}"
        print(line, flush=True)
        if (a, b) in [(8.0, 10.0), (2.0, 2.5)]:
            acc = 0.0; rep = []
            for m in range(1, M + 1):
                c0 = int(ceil(m * sqrt(a))); c1 = int(floor(m * sqrt(b)))
                cs = np.arange(c0, c1 + 1); cs = cs[np.gcd(cs, m) == 1]
                acc += np.sum(T2[cs]) / m ** 2
                if m in (100, 1000, 5000, 10000, 20000, 50000):
                    rep.append(f"M={m}: {acc / Z2:+.5f}")
            print("    m-ordered (companion's ordering):", "  ".join(rep), flush=True)
    print(f"[{time.time() - t0:.0f}s]")
