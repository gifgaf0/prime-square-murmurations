# Lemma 7 ingredients: sum_{b unit mod n} |a_{t^2-4b^2}(n)| <= phi(n) sum_{q|n} 2^omega(q)  (claimed << n^{1+eps}, uniform in t)
#                      nu_t(q) <= 2^omega(q);  delta_t(n) = avg_b a_{t^2-4b^2}(n) = sum_{q|n} lambda(n/q) nu_t(q), multiplicative
import math, time
from math import gcd
from fractions import Fraction as Fr
NMAX = 240
tabs = {}
def tab(q):
    if q not in tabs:
        c = [0] * (4 * q)
        for x in range(2 * q): c[x * x % (4 * q)] += 1
        tabs[q] = c
    return tabs[q]
def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def omega(n): return len(factor(n))
def bigomega(n): return sum(factor(n).values())
def phi(n):
    r = n
    for p in factor(n): r = r // p * (p - 1)
    return r
divs = {n: [q for q in range(1, n + 1) if n % q == 0] for n in range(1, NMAX + 1)}
lam = {m: (-1) ** bigomega(m) for m in range(1, NMAX + 1)}
ts = list(range(0, 41)) + [60, 64, 81, 105, 120, 210, 243, 420, 512, 840, 1155, 2520, 30030, 10 ** 6 + 3]
t0 = time.time()
worst_ratio = 0; worst_case = None; nu_viol = 0; mult_viol = 0; avg_viol = 0
delta = {}
for t in ts:
    for n in range(1, NMAX + 1):
        units = [b for b in range(n) if gcd(b, n) == 1] if n > 1 else [0]
        S = 0; tot = 0
        for b in units:
            D = t * t - 4 * b * b
            a = sum(lam[n // q] * tab(q)[D % (4 * q)] for q in divs[n])
            S += abs(a); tot += a
        bound = phi(n) * sum(2 ** omega(q) for q in divs[n])
        r = S / bound
        if r > worst_ratio: worst_ratio = r; worst_case = (t, n, S, bound)
        delta[(t, n)] = Fr(tot, len(units))
    # nu_t(q) <= 2^omega(q)
    for q in range(1, NMAX + 1):
        units = [b for b in range(q) if gcd(b, q) == 1] if q > 1 else [0]
        nu = Fr(sum(tab(q)[(t * t - 4 * b * b) % (4 * q)] for b in units), len(units))
        if nu > 2 ** omega(q): nu_viol += 1
    for n in range(1, NMAX + 1):
        # delta_t(n) = sum_{q|n} lambda(n/q) nu_t(q)
        s = Fr(0)
        for q in divs[n]:
            units = [b for b in range(q) if gcd(b, q) == 1] if q > 1 else [0]
            s += lam[n // q] * Fr(sum(tab(q)[(t * t - 4 * b * b) % (4 * q)] for b in units), len(units))
        if s != delta[(t, n)]: avg_viol += 1
    for n1 in range(1, 16):
        for n2 in range(1, 16):
            if gcd(n1, n2) == 1 and delta[(t, n1 * n2)] != delta[(t, n1)] * delta[(t, n2)]: mult_viol += 1
print(f"checked {len(ts)} values of t, n <= {NMAX} ({time.time()-t0:.0f}s)")
print(f"max of sum_b |a(n)| / [phi(n) sum_(q|n) 2^omega(q)] = {worst_ratio:.4f} at (t, n, sum, bound) = {worst_case}")
print(f"nu_t(q) > 2^omega(q): {nu_viol} cases;  delta_t != sum lambda * nu_t: {avg_viol};  delta_t multiplicativity failures: {mult_viol}")
# growth: max over t of sum_b|a| / n
for n in (16, 32, 64, 128, 81, 243, 105, 210, 225, 240):
    if n > NMAX: continue
    m = 0
    for t in ts:
        units = [b for b in range(n) if gcd(b, n) == 1]
        S = sum(abs(sum(lam[n // q] * tab(q)[(t * t - 4 * b * b) % (4 * q)] for q in divs[n])) for b in units)
        m = max(m, S)
    print(f"   n={n:4d}: max_t sum_b |a_(t^2-4b^2)(n)| = {m:6d}   phi(n) = {phi(n):4d}   ratio to n = {m/n:.3f}")
