"""(1) Window identity: sum_{k even} h(k) i^k U_{k-2}(cos th) = -(sigma/2) cos((K-1)phi) sum_l H0^(sigma(phi - pi l)) / cos(phi), phi = pi/2 - th.
(2) Zagier: local factors of L(s, D) = zeta(2s)/zeta(s) sum_q N_q(D) q^-s equal those of L(s, chi_D0) B_f(s);  and
    H(|D|) = sqrt|D|/pi * L(1, chi_D0) B_f(1)  (PARI class numbers and L-values).
(3) Per-prime identity at K = 2000: V(p) from the trace formula with a smooth window vs (1/(2 zeta2 H0^(0))) sum_t L(1,t^2-4p^2) cos((K-1)phi_t) H0^(sigma phi_t)."""
import math, numpy as np
from math import gcd
from cypari import pari
pari.allocatemem(2 * 2**30)
def H0(v): v = np.asarray(v, float); o = np.zeros_like(v); m = np.abs(v) < 1; o[m] = np.exp(-1 / (1 - v[m] ** 2)); return o
_vg = np.linspace(-1, 1, 200001)
def H0hat(eta):
    eta = np.atleast_1d(np.asarray(eta, float)); return np.array([np.trapezoid(H0(_vg) * np.cos(e * _vg), _vg) for e in eta])
print("(1) window identity")
K = 2000; sig = K ** 0.9
ks = np.arange(2, 4 * K, 2); h = H0((ks - K) / sig); sel = h > 0; ks, h = ks[sel], h[sel]
ik = (-1.0) ** (ks // 2)
worst = 0.0
for th in np.linspace(0.05, math.pi - 0.05, 41):
    direct = (h * ik * np.sin((ks - 1) * th)).sum() / math.sin(th)
    phi = math.pi / 2 - th
    closed = -(sig / 2) * math.cos((K - 1) * phi) * sum(H0hat(sig * (phi - math.pi * l))[0] for l in (-1, 0, 1)) / math.cos(phi)
    worst = max(worst, abs(direct - closed))
print(f"   max |direct - closed| over 41 angles = {worst:.2e}   (direct sums are up to ~{sig*H0hat(0)[0]/2/math.cos(0.3):.0f})")
ex = [(h * ik * (ks - 1)).sum(), (h * ik).sum(), (h * ((ks // 12) - (ks % 12 == 2)) ).sum()]
print(f"   extra terms: sum h(k) i^k (k-1) = {ex[0]:.2e},  sum h(k) i^k = {ex[1]:.2e};  sum h(k) dim S_k = {ex[2]:.4f} vs sigma H0^(0)(K-7)/24 = {sig*H0hat(0)[0]*(K-7)/24:.4f}")

print("(2) Zagier L-function")
def Nq(D, q):
    return sum(1 for x in range(2 * q) if (x * x - D) % (4 * q) == 0)
def kron(D, l): return int(pari.kronecker(D, l))
def core(D):   # fundamental discriminant D0 and conductor f with D = D0 f^2
    D0 = int(pari.coredisc(D)); f = int(math.isqrt(D // D0)); return D0, f
bad = 0; checked = 0
for D in range(-3, -400, -1):
    if D % 4 not in (0, 1): continue
    D0, f = core(D)
    for l in (2, 3, 5, 7):
        e = 0; ff = f
        while ff % l == 0: ff //= l; e += 1
        J = 2 * e + 5
        lhs = [0] * (J + 1); Ns = [Nq(D, l ** j) for j in range(J + 1)]
        # (1/(1+X)) sum_j N_{l^j} X^j
        for j in range(J + 1): lhs[j] = sum((-1) ** (j - i) * Ns[i] for i in range(j + 1))
        c = kron(D0, l)
        Bf = [0] * (J + 1)
        for i in range(e + 1): Bf[2 * i] += l ** i
        for i in range(e): Bf[2 * i + 1] -= c * l ** i
        rhs = [sum(Bf[i] * c ** (j - i) for i in range(j + 1)) for j in range(J + 1)]
        checked += 1
        if lhs != rhs: bad += 1
print(f"   local factors: {checked} (D, l) pairs, mismatches: {bad}")
worst = 0.0
for D in list(range(-3, -3000, -7)) + [-4 * 1009 ** 2 + 9, -4 * 997 ** 2 + 400]:
    if D % 4 not in (0, 1): continue
    D0, f = core(D)
    L1 = float(pari(f"lfun(lfuncreate({D0}), 1)"))
    B = 0.0
    for d in range(1, f + 1):
        if f % d == 0:
            mu = int(pari.moebius(d)); s1 = sum(1 / e for e in range(1, f // d + 1) if (f // d) % e == 0)
            B += mu * kron(D0, d) / d * s1
    lhsH = float(pari.qfbhclassno(-D)); rhsH = math.sqrt(-D) / math.pi * L1 * B
    worst = max(worst, abs(lhsH - rhsH) / max(1, lhsH))
print(f"   H(|D|) = sqrt|D|/pi L(1,chi_D0) B_f(1): max relative deviation {worst:.1e}")

print("(3) per-prime identity, K = 2000, smooth window H0 with sigma = K^0.9")
N = ((K - 1) / (4 * math.pi)) ** 2
dims = (ks // 12) - (ks % 12 == 2)
DK = (h * dims).sum()
for p in (467, 479, 487, 499, 1801, 2003):   # the first four have p^2/N in [8, 10]; the identity is exact for every p
    n = p * p; ts = np.arange(-(2 * p - 1), 2 * p)
    Hs = np.array([float(pari.qfbhclassno(4 * n - int(t) ** 2)) for t in range(0, 2 * p)])
    Hs = np.concatenate([Hs[:0:-1], Hs])
    th = np.arccos(ts / (2.0 * p))
    # exact: sum_k h(k) i^k Tr_k(p^2)/p^(k-1)
    U = np.sin(np.outer(ks - 1, th)) / np.sin(th)          # weights x t
    main = -(h * ik) @ (U @ Hs) / (2 * p)
    extra = (h * ik * ((ks - 1) / (12 * p) - 0.5 - 2.0 * np.exp(-(ks - 1) * math.log(p)))).sum()
    V_exact = math.sqrt(N) * (main + extra) / DK
    phi = np.arcsin(ts / (2.0 * p)); Lv = math.pi * Hs / np.sqrt(4.0 * n - ts ** 2)
    V_formula = (1 / (2 * math.pi ** 2 / 6 * H0hat(0)[0])) * (Lv * np.cos((K - 1) * phi) * H0hat(sig * phi)).sum() * (sig * H0hat(0)[0] * (K - 1) / 24) / DK
    print(f"   p={p}: y={p*p/N:.3f}  V exact = {V_exact:+.8f}   V from the L-value formula = {V_formula:+.8f}   diff {V_exact - V_formula:+.1e}", flush=True)
