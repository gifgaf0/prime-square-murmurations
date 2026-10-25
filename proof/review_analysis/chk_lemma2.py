# Lemma 2 check: sum_{k even} h(k) i^k U_{k-2}(t/2p) = -(sigma/2) cos((K-1)phi)/cos(phi) * sum_l H0^(sigma(phi - pi l))
import math, numpy as np
from scipy.integrate import quad

def H0(v):
    v = np.asarray(v, float); o = np.zeros_like(v); m = np.abs(v) < 1
    o[m] = np.exp(-1 / (1 - v[m] ** 2)); return o
def H0s(v):
    return math.exp(-1 / (1 - v * v)) if abs(v) < 1 else 0.0
def H0hat(eta):
    # real, even: 2 int_0^1 H0(v) cos(eta v) dv ; use quad with weight cos for accuracy
    val, err = quad(H0s, 0, 1, weight='cos', wvar=eta, limit=400)
    return 2 * val

def lhs(K, sig, x):           # x = t/2p = cos(theta)
    ks = np.arange(2, 4 * K, 2)
    h = H0((ks - K) / sig); sel = h > 0; ks = ks[sel]; h = h[sel]
    th = math.acos(x)
    ik = np.where((ks // 2) % 2 == 0, 1.0, -1.0)
    return float((h * ik * np.sin((ks - 1) * th)).sum() / math.sin(th))

def rhs(K, sig, x, L=3):
    phi = math.asin(x)
    S = sum(H0hat(sig * (phi - math.pi * l)) for l in range(-L, L + 1))
    S0 = H0hat(sig * phi)
    return -(sig / 2) * math.cos((K - 1) * phi) / math.cos(phi) * S, -(sig / 2) * math.cos((K - 1) * phi) / math.cos(phi) * S0

for K, theta in ((2000, 0.9), (2002, 0.9), (400, 0.6), (402, 0.5), (1000, 0.95)):
    sig = K ** theta
    worst = 0; worst0 = 0; scale = 0
    xs = list(np.linspace(-0.999, 0.999, 61)) + [0.0, 0.9999, -0.9999, 0.99999, 1 - 1e-7]
    for x in xs:
        a = lhs(K, sig, x); b, b0 = rhs(K, sig, x)
        worst = max(worst, abs(a - b)); worst0 = max(worst0, abs(a - b0)); scale = max(scale, abs(a))
    print(f"K={K} theta={theta} sigma={sig:.1f}: max|LHS-RHS(all l)|={worst:.2e}, max|LHS-RHS(l=0 only)|={worst0:.2e}, max|LHS|={scale:.2e}")

# extra terms and D_K
def dimS(k):
    if k % 2 or k < 4: return 0
    return k // 12 - (1 if k % 12 == 2 else 0)
for K, theta in ((2000, 0.9), (2002, 0.9), (400, 0.6), (10000, 0.9)):
    sig = K ** theta
    ks = np.arange(2, 4 * K, 2); h = H0((ks - K) / sig); sel = h > 0; ks = ks[sel]; h = h[sel]
    ik = np.where((ks // 2) % 2 == 0, 1.0, -1.0)
    e1 = (h * ik).sum(); e2 = (h * ik * (ks - 1)).sum()
    DK = sum(hh * dimS(int(k)) for hh, k in zip(h, ks))
    pred = sig * H0hat(0) * (K - 7) / 24
    print(f"K={K}: sum h i^k = {e1:.2e}, sum h i^k (k-1) = {e2:.2e}; D_K = {DK:.6f}, sigma H0^(0)(K-7)/24 = {pred:.6f}, rel diff {DK/pred-1:.2e}")
