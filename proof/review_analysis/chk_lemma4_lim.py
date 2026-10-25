import math, numpy as np
from cypari import pari
pari.allocatemem(2 * 2**30)
# ---------- Lemma 4: smoothed truncation of L(1, Delta) ----------
def coeffs(D, nmax):
    D0 = int(pari.coredisc(D)); f = math.isqrt(D // D0)
    a = np.zeros(nmax + 1); a[1] = 1.0
    spf = np.zeros(nmax + 1, dtype=np.int64)
    for i in range(2, nmax + 1):
        if spf[i] == 0: spf[i::i][spf[i::i] == 0] = i
    loc = {}
    for n in range(2, nmax + 1):
        l = int(spf[n]); m = n; j = 0
        while m % l == 0: m //= l; j += 1
        if (l, j) not in loc:
            c = int(pari.kronecker(D0, l)); e = 0; ff = f
            while ff % l == 0: ff //= l; e += 1
            Bf = [0] * (j + 1)
            for i in range(e + 1):
                if 2 * i <= j: Bf[2 * i] += l ** i
            for i in range(e):
                if 2 * i + 1 <= j: Bf[2 * i + 1] -= c * l ** i
            loc[(l, j)] = sum(Bf[i] * c ** (j - i) for i in range(j + 1))
        a[n] = a[m] * loc[(l, j)]
    return a
for (t, p) in ((0, 1999), (7, 2003), (30, 1801), (1, 1999), (12, 1993)):
    D = t * t - 4 * p * p
    L1 = math.pi * float(pari.qfbhclassno(-D)) / math.sqrt(-D)
    nmax = 400000; a = coeffs(D, nmax); n = np.arange(nmax + 1); n[0] = 1
    row = []
    for M in (10, 100, 1000, 10000):
        S = float((a[1:] / n[1:] * np.exp(-n[1:] / M)).sum())
        row.append(f"M={M}: err={S-L1:+.2e} (err*sqrt(M)={(S-L1)*math.sqrt(M):+.2f})")
    print(f"Delta={D}: L(1,Delta)={L1:.6f}; " + "; ".join(row))
# ---------- I_K(t): uniform decay in t for kappa in [0, 5] ----------
def bump(v): v = np.asarray(v, float); o = np.zeros_like(v); m = np.abs(v) < 1; o[m] = np.exp(-1 / (1 - v[m] ** 2)); return o
vg = np.linspace(0, 1, 20001); w = np.full_like(vg, vg[1] - vg[0]); w[0] /= 2; w[-1] /= 2; Hw = 2 * bump(vg) * w
def H0hat(e): e = np.atleast_1d(e); return np.array([np.cos(x * vg) @ Hw for x in e])
a_, b_ = 8.0, 10.0
xg = np.linspace(1 / math.sqrt(b_), 1 / math.sqrt(a_), 40001); yg = xg ** -2
Phi = bump((2 * yg - a_ - b_) / (b_ - a_)); wI = Phi * yg ** -0.5 * 2 * xg ** -3
etas = np.linspace(0, 6 * 120 * xg.max(), 30001); Htab = H0hat(etas)
def IK(t, kap): return np.trapezoid(wI * np.cos(2 * math.pi * t * xg) * np.interp(kap * abs(t) * xg, etas, Htab), xg)
H00 = Htab[0]; I0 = np.trapezoid(wI, xg)
print("max over kappa in {0,0.1,0.5,1,2,5} of |I_K(t)|/(Hhat0 I(0)):")
for t in (1, 2, 4, 8, 16, 32, 64, 120):
    m = max(abs(IK(t, k)) for k in (0, 0.1, 0.5, 1, 2, 5)) / (H00 * I0)
    print(f"   t={t:4d}: {m:.3e}")
# ---------- Theorem A limit with independent f2 (Lemma 6 table, verified by brute force) ----------
def chi(l): return 0 if l % 2 == 0 else (1 if l % 4 == 1 else -1)
def E(l, v):
    if l == 2: return 2 / 3 if v == 0 else (5 / 3 if v == 1 else 1.0)
    c = chi(l); return (1 - (1 + c) / (l * (l - 1))) / (1 - l ** -2) if v == 0 else l / (l - c)
ps = [int(x) for x in pari.primes(200000)]
C = 1.0
for l in ps: C *= E(l, 0)
def f2(t):
    if t == 0: return math.pi / 4
    r = C; tt = abs(t)
    for l in ps:
        if l > tt: break
        if tt % l == 0:
            v = 0; u = tt
            while u % l == 0: u //= l; v += 1
            r *= E(l, v) / E(l, 0)
    return r
tot = sum((1 if t == 0 else 2) * f2(t) * IK(t, 0.0) for t in range(0, 400)) / (H00 * I0)
print(f"Theorem A limit, Phi = bump on [8,10]: (1/(2 zeta 2)) sum_t f2(t) I(t)/I(0) = {tot / (2 * math.pi ** 2 / 6):+.5f}")
