"""End-to-end check of Theorem A (smooth H0 = C_c^infty bump, theta = 0.9, Phi = bump on [8, 10]).
For each K three numbers are compared:
  M(K)    the statistic itself, computed exactly through Proposition 1 (Hurwitz class numbers for every t where
          H0^(sigma phi_t) is not negligible);
  A(K)    the same prime average with every L(1, t^2 - 4p^2) replaced by its Euler-product mean f2(t) (Lemma 6);
          M - A isolates the arithmetic averaging of Steps 4-5 (Lemmas 4, 5, 7), and its standard error comes from the
          prime-to-prime scatter of the residuals;
  Pred(K) the finite-K main term of Step 5, (1/(2 zeta2 H0^(0))) sum_t f2(t) I_K(t)/I(0) (prime sum -> integral,
          phi_t -> t/(2p)); A - Pred isolates those analytic approximations.
Pred depends on K only through kappa = 2 pi sigma/(K - 1) and tends to the limit of Theorem A as kappa -> 0 (pred_kappa.py).
Usage: python3 thmA_numeric.py [K:stride ...]"""
import math, sys, json, time, numpy as np
from scipy.interpolate import CubicSpline
from cypari import pari
from f2 import f2
pari.allocatemem(2 * 2**30)
t0 = time.time()
def bump(v): v = np.asarray(v, float); o = np.zeros_like(v); m = np.abs(v) < 1; o[m] = np.exp(-1 / (1 - v[m] ** 2)); return o
# H0^(eta) = int_{-1}^{1} H0(v) cos(eta v) dv = 2 int_0^1 ...; trapezoid is spectrally accurate for this C_c^infty integrand
_v = np.linspace(0, 1, 10001); _w = np.full_like(_v, _v[1] - _v[0]); _w[0] /= 2; _w[-1] /= 2; _Hw = 2 * bump(_v) * _w
_eg = np.linspace(0, 400, 40001)
_Hg = np.concatenate([np.cos(np.outer(_eg[i:i + 2000], _v)) @ _Hw for i in range(0, len(_eg), 2000)])
_spl = CubicSpline(_eg, _Hg)
def H0h(eta):
    e = np.abs(np.asarray(eta, float)); out = np.zeros_like(e); m = e <= 400; out[m] = _spl(e[m]); return out
H00 = float(_Hg[0])
print(f"H0^ table ready ({time.time()-t0:.1f}s): H0^(0) = {H00:.10f}, H0^(50) = {float(H0h(50.0)):.3e}, H0^(200) = {float(H0h(200.0)):.3e}", flush=True)
a, b = 8.0, 10.0
def Phi(y): return bump((2 * np.asarray(y, float) - a - b) / (b - a))
xg = np.linspace(1 / math.sqrt(b), 1 / math.sqrt(a), 200001); yg = xg ** -2
wI = Phi(yg) * yg ** (-0.5) * 2 * xg ** -3
def I_K(t, kappa): return np.trapezoid(wI * np.cos(2 * math.pi * t * xg) * H0h(kappa * t * xg), xg)
I0 = np.trapezoid(wI, xg)
zeta2 = math.pi ** 2 / 6
F2 = np.array([f2(t) for t in range(0, 5001)])
def limit(TM=3000):
    return sum((1 if t == 0 else 2) * F2[t] * np.trapezoid(wI * np.cos(2 * math.pi * t * xg), xg) for t in range(0, TM + 1)) / (2 * zeta2) / I0
def pred(K, sig, TM):
    kappa = 2 * math.pi * sig / (K - 1)
    return sum((1 if t == 0 else 2) * F2[t] * I_K(t, kappa) for t in range(0, TM + 1)) / (2 * zeta2 * H00) / I0 * (K - 1) / (K - 7)
def measure(K, theta, stride=1, ETA=200.0):
    sig = K ** theta; N = ((K - 1) / (4 * math.pi)) ** 2
    plo, phi_ = math.isqrt(int(a * N)), math.isqrt(int(b * N)) + 1
    ps = [int(p) for p in pari.primes([plo, phi_])][::stride]
    W, V, A = [], [], []; nt = 0
    for p in ps:
        y = p * p / N; w = math.log(p) * float(Phi(y))
        if w == 0: continue
        T = min(2 * p - 1, int(2 * p * math.sin(min(ETA / sig, 1.5))) + 1)
        ts = np.arange(0, T + 1)
        D = 4 * p * p - ts * ts
        Hs = np.array([float(pari.qfbhclassno(int(d))) for d in D]); nt += len(ts)
        L = math.pi * Hs / np.sqrt(D.astype(float))
        phi = np.arcsin(ts / (2.0 * p))
        c = np.cos((K - 1) * phi) * H0h(sig * phi) * np.where(ts == 0, 1.0, 2.0) / (2 * zeta2 * H00) * (K - 1) / (K - 7)
        W.append(w); V.append(float(c @ L)); A.append(float(c @ F2[:T + 1]))
    W, V, A = map(np.array, (W, V, A))
    M_, A_ = W @ V / W.sum(), W @ A / W.sum()
    r = V - A; se = math.sqrt(((W * (r - (W @ r) / W.sum())) ** 2).sum()) / W.sum()
    return M_, A_, se, len(ps), nt, sig
if __name__ == "__main__":
    theta = 0.9
    lim = limit()
    print(f"limit (Theorem A) = {lim:+.6f}  ({time.time()-t0:.0f}s)", flush=True)
    runs = [tuple(int(x) for x in s.split(":")) for s in sys.argv[1:]] or [(10000, 1), (30000, 1), (100000, 1), (300000, 1), (1000000, 3)]
    out = []
    for K, stride in runs:
        m, av, se, n, nt, sig = measure(K, theta, stride)
        pr = pred(K, sig, 400)
        out.append(dict(K=K, theta=theta, sigma=sig, kappa=2 * math.pi * sig / (K - 1), stride=stride, primes=n, class_numbers=nt,
                        M=m, A=av, se_M_minus_A=se, pred=pr, limit=lim))
        print(f"K={K:8d} sigma={sig:9.0f} primes={n:5d} (class numbers {nt}):  M = {m:+.6f}   A = {av:+.6f}   M-A = {m-av:+.2e} +- {se:.1e}"
              f" (z = {(m-av)/se:+.2f})   Pred = {pr:+.6f}   A-Pred = {av-pr:+.2e}   limit {lim:+.6f}   ({time.time()-t0:.0f}s)", flush=True)
        json.dump(out, open("thmA_numeric.json", "w"), indent=1)
