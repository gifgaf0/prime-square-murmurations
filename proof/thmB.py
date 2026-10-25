"""Theorem B check (t-sum over |t| <= 3000, converged to ~1e-9): (1/(2 zeta 2)) sum_t f_k(t) I_k(t)/I_k(0)  vs  point masses (c/m^3) T_k(c) at y=(c/m)^2 paired with Phi
(density y^(1/k-1)), c-ordered partial sums.  k = 2 (squares) and k = 1 (primes, Bober et al.)."""
import math, numpy as np
from f2 import PR, E, vl, chi4
def E1(l, v):
    if l == 2: return 2 / 3 if v == 0 else 4 / 3
    return (1 - 1 / (l * (l - 1))) / (1 - l ** -2) if v == 0 else 1 / (1 - l ** -2)
def fk(t, k):
    Ef = E if k == 2 else E1
    if t == 0: return math.pi / 4 if k == 2 else float("nan")
    t = abs(t); r = 1.0
    for l in PR[:20000]: r *= Ef(l, 0)
    for l in PR:
        if l > t: break
        if t % l == 0: r *= Ef(l, vl(t, l)) / Ef(l, 0)
    return r
def bump(y, a, b):
    u = (2 * y - a - b) / (b - a); out = np.zeros_like(y)
    m = np.abs(u) < 1; out[m] = np.exp(-1 / (1 - u[m] ** 2)); return out
def run(a, b, k, TMAX=3000, CMAX=60000, dens=None):
    if dens is None: dens = 1 / k - 1
    # I_k(t) = int Phi(y) cos(2 pi t / sqrt y) y^(1/k - 1) dy, via x = 1/sqrt(y): dy = -2 x^-3 dx
    x = np.linspace(1 / math.sqrt(b), 1 / math.sqrt(a), 400001); y = x ** -2
    w = bump(y, a, b) * y ** dens * 2 * x ** -3
    def I(t): return np.trapezoid(w * np.cos(2 * math.pi * t * x), x)
    I0 = I(0)
    # f_k(t): only t != 0 needs the product; t = 0 term for primes: f_1(0) = sum ... handled by symmetry (f_1(0) = zeta(2)*prod... -> as t->0 all l divide)
    base = 1.0
    Ef = E if k == 2 else E1
    for l in PR[:50000]: base *= Ef(l, 0)
    tot = 0.0
    f0 = math.pi / 4 if k == 2 else math.pi ** 2 / 6   # t = 0: every l divides t -> prod E_l(inf): squares L(1,chi_-4), primes zeta(2)
    tot += f0 * I(0)
    for t in range(1, TMAX + 1):
        r = base; tt = t
        for l in PR:
            if l > tt: break
            if tt % l == 0: r *= Ef(l, vl(tt, l)) / Ef(l, 0)
        tot += 2 * r * I(t)
    lhs = tot / (2 * (math.pi ** 2 / 6)) / I0
    # RHS: point masses
    cs = np.arange(1, CMAX + 1)
    # T_k(c) = (6/pi^2) A_k(c) prod_{l|c} (1-l^-2)^-1
    spf = np.zeros(CMAX + 1, dtype=np.int64)
    for i in range(2, int(CMAX ** 0.5) + 1):
        if spf[i] == 0: spf[i * i::i][spf[i * i::i] == 0] = i
    spf[spf == 0] = np.arange(CMAX + 1)[spf == 0]
    T = np.zeros(CMAX + 1); T[1] = 6 / math.pi ** 2
    Ak = np.ones(CMAX + 1); fac = np.ones(CMAX + 1)
    for c in range(2, CMAX + 1):
        p = int(spf[c]); m = c // p; e = 1
        while m % p == 0: m //= p; e += 1
        if k == 2:
            if p == 2: loc = {1: 1.0, 2: -2.0}.get(e, 0.0)
            else: loc = (1 + chi4(p) * p) / (p - 1) if e == 1 else 0.0
        else:
            loc = 1 / (p - 1) if e == 1 else 0.0
        Ak[c] = Ak[m] * loc; fac[c] = fac[m] / (1 - float(p) ** -2)
    T = 6 / math.pi ** 2 * Ak * fac
    partial = []; s = 0.0
    for c in range(1, CMAX + 1):
        mlo = math.ceil(c / math.sqrt(b)); mhi = math.floor(c / math.sqrt(a))
        if mhi >= mlo and T[c] != 0:
            ms = np.arange(mlo, mhi + 1); ms = ms[np.gcd(ms, c) == 1]
            yy = (c / ms) ** 2
            s += T[c] * float((bump(yy, a, b) * (c / ms ** 3) * yy ** dens).sum())
        if c in (1000, 3000, 10000, 30000, CMAX): partial.append((c, s / I0))
    return lhs, partial
if __name__ == "__main__":
    # (k, density exponent): squares (A_2, y^-1/2), primes (A_1, y^0), and A_1 masses with the squares' density y^-1/2
    for k, dens, label in ((2, -0.5, "squares"), (1, 0.0, "primes"), (1, -0.5, "A_1 masses, density y^-1/2")):
        for (a, b) in ((8.0, 10.0), (1.6, 3.0), (0.6, 1.5)):
            lhs, part = run(a, b, k, dens=dens)
            print(f"{label:28s} Phi = bump on [{a}, {b}]:  t-sum = {lhs:+.8f}   point masses, c <= C: " +
                  "  ".join(f"C={c}: {v:+.6f}" for c, v in part), flush=True)
