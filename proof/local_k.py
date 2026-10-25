"""Local densities for prime powers p^k: Delta = t^2 - 4 b^k, b over units mod q.  Compare E_l with the Ramanujan-side factor
sum_j G_k(l^j) c_{l^j}(l^v), G_k(c) = A_k(c) c^-2 prod_{l|c}(1-l^-2)^-1, A_k(c) = average of S(a^k,1;c) over units a."""
from fractions import Fraction as Fr
from math import gcd
import cmath, math, sys
def sqcount(m2, m4):
    cnt = [0] * m4
    for x in range(m2): cnt[x * x % m4] += 1
    return cnt
def nu(t, q, k):
    cnt = sqcount(2 * q, 4 * q); s = nb = 0
    for b in range(q):
        if gcd(b, q) != 1: continue
        nb += 1; s += cnt[(t * t - 4 * pow(b, k, q)) % (4 * q)]
    return Fr(s, nb)
def E_local(t, l, J, k):
    nus = [Fr(1)] + [nu(t, l ** i, k) for i in range(1, J + 1)]
    d = [sum((-1) ** (j - i) * nus[i] for i in range(j + 1)) for j in range(J + 1)]
    return float(sum(d[j] / Fr(l) ** j for j in range(J + 1))), d
def kloost(m, n, c):
    return sum(cmath.exp(2j * math.pi * (m * x + n * pow(x, -1, c)) / c) for x in range(1, c) if gcd(x, c) == 1).real if c > 1 else 1.0
def A(c, k):
    us = [a for a in range(1, c) if gcd(a, c) == 1] if c > 1 else [0]
    return sum(kloost(pow(a, k, c) if c > 1 else 0, 1, c) for a in us) / len(us)
def ramanujan(c, n):
    return sum(math.cos(2 * math.pi * a * n / c) for a in range(1, c + 1) if gcd(a, c) == 1)
def F_ram(l, v, k, J=6):
    s = 0.0
    for j in range(0, J + 1):
        c = l ** j
        if c > 3000: break
        G = (A(c, k) / c ** 2 / (1 - l ** -2)) if j > 0 else 1.0
        s += G * ramanujan(c, l ** v if v < 50 else 0)
    return s
if __name__ == "__main__":
    k = int(sys.argv[1])
    for l, J in ((2, 12), (3, 7), (5, 5), (7, 4), (13, 3)):
        for v in (0, 1, 2, 3):
            t = l ** v * (1 if l != 2 else 1)
            if l != 2 and v == 0: t = 2
            E, d = E_local(t, l, J, k)
            print(f"k={k} l={l:2d} v={v} (t={t}): E_l = {E:.8f}   Ramanujan side = {F_ram(l, v, k):.8f}   delta = {[str(x) for x in d[:5]]}", flush=True)
