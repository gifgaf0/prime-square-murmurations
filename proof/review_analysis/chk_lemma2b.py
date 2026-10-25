import math, numpy as np
def H0(v):
    v = np.asarray(v, float); o = np.zeros_like(v); m = np.abs(v) < 1
    o[m] = np.exp(-1 / (1 - v[m] ** 2)); return o
vg = np.linspace(0, 1, 400001); w = np.full_like(vg, vg[1]-vg[0]); w[0] /= 2; w[-1] /= 2; Hw = 2 * H0(vg) * w
def H0hat(eta): return float(np.cos(eta * vg) @ Hw)
def lhs(K, sig, x):
    ks = np.arange(2, 4 * K, 2); h = H0((ks - K) / sig); sel = h > 0; ks = ks[sel]; h = h[sel]
    th = math.acos(x); ik = np.where((ks // 2) % 2 == 0, 1.0, -1.0)
    return float((h * ik * np.sin((ks - 1) * th)).sum() / math.sin(th))
def rhs(K, sig, x, L=4):
    phi = math.asin(x); S = sum(H0hat(sig * (phi - math.pi * l)) for l in range(-L, L + 1))
    return -(sig / 2) * math.cos((K - 1) * phi) / math.cos(phi) * S
for K, theta in ((2000, 0.9), (2002, 0.9), (400, 0.6), (402, 0.5), (1000, 0.95)):
    sig = K ** theta; rows = []
    for x in list(np.linspace(-0.999, 0.999, 41)) + [0.9999, -0.9999, 1 - 1e-7]:
        a = lhs(K, sig, x); b = rhs(K, sig, x); rows.append((abs(a - b), abs(a), x))
    m = max(rows)
    print(f"K={K} theta={theta}: max|LHS-RHS| = {m[0]:.2e} at x={m[2]:.7f} (|LHS| there {m[1]:.2e}); max |LHS| = {max(r[1] for r in rows):.2e}")
