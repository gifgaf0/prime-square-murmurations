import math, numpy as np, time
from cypari import pari
pari.allocatemem(2 * 2**30)
def H0(v):
    v = np.asarray(v, float); o = np.zeros_like(v); m = np.abs(v) < 1
    o[m] = np.exp(-1 / (1 - v[m] ** 2)); return o
vg = np.linspace(0, 1, 400001); w = np.full_like(vg, vg[1]-vg[0]); w[0] /= 2; w[-1] /= 2; Hw = 2 * H0(vg) * w
def H0hat(eta): return np.array([float(np.cos(e * vg) @ Hw) for e in np.atleast_1d(eta)])
def dimS(k): return 0 if (k % 2 or k < 4) else k // 12 - (1 if k % 12 == 2 else 0)
zeta2 = math.pi ** 2 / 6
for K, theta in ((1000, 0.9), (1002, 0.9), (3000, 0.88), (1500, 0.97)):
    sig = K ** theta; N = ((K - 1) / (4 * math.pi)) ** 2
    ks = np.arange(2, 4 * K, 2); h = H0((ks - K) / sig); sel = h > 0; ks = ks[sel]; h = h[sel]
    ik = np.where((ks // 2) % 2 == 0, 1.0, -1.0)
    DK = float(sum(hh * dimS(int(k)) for hh, k in zip(h, ks)))
    ps = [int(x) for x in pari.primes([math.isqrt(int(8 * N)), math.isqrt(int(10 * N)) + 1])][:4]
    for p in ps:
        ts = np.arange(-(2 * p - 1), 2 * p)
        Hs = np.array([float(pari.qfbhclassno(4 * p * p - int(t) ** 2)) for t in ts])
        th = np.arccos(ts / (2.0 * p))
        # exact normalized trace from Lemma 1 (verified against PARI) for each k in the window
        Tr = np.array([-(Hs * np.sin((k - 1) * th) / np.sin(th)).sum() / (2 * p) + (k - 1) / (12 * p) - 0.5 - float(p) ** (1 - k) for k in ks])
        V_exact = math.sqrt(N) * float((h * ik * Tr).sum()) / DK
        phi = np.arcsin(ts / (2.0 * p)); L = math.pi * Hs / np.sqrt(4.0 * p * p - ts ** 2)
        V_prop = (K - 1) / (K - 7) / (2 * zeta2 * H0hat(0)[0]) * float((L * np.cos((K - 1) * phi) * H0hat(sig * phi)).sum())
        print(f"K={K} theta={theta} p={p}: V exact={V_exact:+.12f}  Prop.1={V_prop:+.12f}  diff={V_exact-V_prop:+.1e}", flush=True)
# one large-weight trace against PARI's own trace form
t0 = time.time()
k, p = 202, 23
tf = pari.mftraceform([1, k]); c = pari.mfcoefs(tf, p * p)
exact = int(c[p * p])
ts = np.arange(-(2 * p - 1), 2 * p)
from fractions import Fraction as Fr
def Hq(Nn):
    if Nn == 0: return Fr(-1, 12)
    v = pari.qfbhclassno(Nn); return Fr(int(pari.numerator(v)), int(pari.denominator(v)))
def P(k, t, n):
    a, b = 1, t
    for _ in range(k - 3): a, b = b, t * b - n * a
    return b
n = p * p
s = sum(P(k, int(t), n) * Hq(4 * n - int(t) ** 2) for t in range(-2 * p, 2 * p + 1))
mine = -s / 2 - Fr(2 * 1 + p ** (k - 1), 2)
print(f"k={k}, n={p}^2: PARI mftraceform coefficient == Lemma 1 exact value: {mine == exact}  ({time.time()-t0:.0f}s)")
