#!/usr/bin/env python3
"""Independent recheck of Lemma 7 (second moment) of murmurations_squares v10.

Written separately from second_moment_check.py.  Differences in construction:
  * Liouville lambda from a smallest-prime-factor sieve, not trial division per call;
  * a_Delta(n) assembled from the divisor list via the sieve; Delta reduced mod 4n first;
  * second moment vectorised over (t, b) with numpy; t runs over a full period 0..n
    (t^2 mod 4n depends on t mod 2n, and t ~ -t), i.e. EVERY t class, not 0<=t<30;
  * part (b) is tested directly: the character group of (Z/nZ)^x is built from its
    structure (primitive roots for odd prime powers; {-1} x <5> for 2^j), the
    coefficients a^(chi) are computed, and Plancherel, Cauchy-Schwarz and
    a^(chi_0) = delta_t(n) (with delta_t computed by the OTHER route,
    delta_t(n) = sum_{q|n} lambda(n/q) nu_t(q)) are checked numerically.
Also reports how sum_chi |a^(chi)| actually grows against n^{1/2}.
"""
import numpy as np
from math import gcd, isqrt
import cmath, sys

NMAX_A = int(sys.argv[1]) if len(sys.argv) > 1 else 400   # part (a), all n <= NMAX_A, all t mod period
NMAX_B = int(sys.argv[2]) if len(sys.argv) > 2 else 160   # part (b), all n <= NMAX_B, all t mod period

# ---------- arithmetic helpers (sieve-based) ----------
LIM = max(4 * NMAX_A, 5000) + 10
spf = list(range(LIM))
for i in range(2, isqrt(LIM) + 1):
    if spf[i] == i:
        for k in range(i * i, LIM, i):
            if spf[k] == k:
                spf[k] = i

def factorization(n):
    f = []
    while n > 1:
        p = spf[n]; e = 0
        while n % p == 0:
            n //= p; e += 1
        f.append((p, e))
    return f

def omega_total(n):  # Omega(n), number of prime factors with multiplicity
    return sum(e for _, e in factorization(n))

def liouville(n):
    return -1 if omega_total(n) % 2 else 1

def divisors(n):
    ds = [1]
    for p, e in factorization(n):
        ds = [d * p**k for d in ds for k in range(e + 1)]
    return sorted(ds)

def phi(n):
    r = n
    for p, _ in factorization(n):
        r -= r // p
    return r

def tau(n):
    r = 1
    for _, e in factorization(n):
        r *= e + 1
    return r

def units(n):
    return np.array([b for b in range(n) if gcd(b, n) == 1], dtype=np.int64)

# ---------- N_q(Delta) = #{x mod 2q : x^2 = Delta mod 4q}, as a lookup table over Delta mod 4q ----------
_Ntab = {}
def Ntab(q):
    if q not in _Ntab:
        x = np.arange(2 * q, dtype=np.int64)
        _Ntab[q] = np.bincount((x * x) % (4 * q), minlength=4 * q)
    return _Ntab[q]

def a_matrix(n, tvals):
    """Return array A[t_index, b_index] = a_{t^2-4b^2}(n) over units b mod n."""
    U = units(n)
    T = np.asarray(tvals, dtype=np.int64)
    D = (T[:, None] ** 2 - 4 * U[None, :] ** 2) % (4 * n)       # Delta mod 4n
    A = np.zeros(D.shape, dtype=np.int64)
    for q in divisors(n):
        A += liouville(n // q) * Ntab(q)[D % (4 * q)]
    return A, U

# ---------- part (a) ----------
def c_of(q):
    r = 1
    for _, e in factorization(q):
        r *= 128 * e
    return r

fails = 0
worst_ratio = (0.0, None, None)        # S2 / (phi tau^2), n >= 2
for n in range(1, NMAX_A + 1):
    tvals = np.arange(0, n + 1)        # full set of classes: t^2 mod 4n depends on t mod 2n, and t ~ -t
    A, U = a_matrix(n, tvals)
    S2 = (A * A).sum(axis=1)           # per t
    bound = tau(n) ** 2 * phi(n) * max(c_of(q) for q in divisors(n))
    if (S2 > bound).any():
        fails += 1
        print("FAIL (a):", n, tvals[S2 > bound][:5], S2[S2 > bound][:5], bound)
    if n >= 2:
        r = S2.max() / (phi(n) * tau(n) ** 2)
        if r > worst_ratio[0]:
            worst_ratio = (float(r), n, int(tvals[S2.argmax()]))
    # the sharper empirical claim in the numerics table: S2 <= phi(n) tau(n)^2
    if (S2 > phi(n) * tau(n) ** 2).any():
        fails += 1
        print("FAIL sharper S2 <= phi tau^2:", n, tvals[S2 > phi(n) * tau(n) ** 2][:5])
print("(a) all n <= %d, all t classes: %s; max S2/(phi tau^2) over n>=2 = %.4f at n=%d, t=%d"
      % (NMAX_A, "OK" if fails == 0 else "FAILURES", *worst_ratio))

# prime-power W bounds, from the DEFINITION of W, over every t class, at larger j than the original check
def W_of(q, tvals):
    U = units(q)
    T = np.asarray(tvals, dtype=np.int64)
    D = (T[:, None] ** 2 - 4 * U[None, :] ** 2) % (4 * q)
    return (Ntab(q)[D] ** 2).sum(axis=1)

wf = 0
for l, jmax in [(2, 12), (3, 7), (5, 5), (7, 4), (11, 3), (13, 3), (17, 3), (19, 2), (23, 2), (29, 2), (31, 2)]:
    for j in range(1, jmax + 1):
        q = l ** j
        tv = np.arange(0, q + 1)
        W = W_of(q, tv)
        if (W > 128 * j * phi(q)).any():
            wf += 1; print("FAIL W bound", l, j)
        if l == 2 and j >= 3:
            odd_t = tv % 2 == 1; four = tv % 4 == 0; two = tv % 4 == 2
            if W[odd_t].any() or W[four].any():
                wf += 1; print("FAIL W(2^j)=0 cases", j)
            if (W[two] > 128 * (j - 2) * phi(q)).any():
                wf += 1; print("FAIL sharper 2-adic", j)
        if l != 2:
            if (W[tv % l == 0] > 4 * phi(q)).any():
                wf += 1; print("FAIL l|t case", l, j)
            if (W > 4 * (2 * j + 1) * q).any():
                wf += 1; print("FAIL odd displayed bound", l, j)
print("W(l^j) bounds (every t class, 2^j<=4096, 3^j<=2187, ...): %s" % ("OK" if wf == 0 else "FAILURES"))

# ---------- part (b): explicit characters of (Z/nZ)^x ----------
def unit_group_generators(n):
    """Generators (g_i, order_i) of (Z/nZ)^x via CRT, as residues mod n."""
    gens = []
    for p, e in factorization(n):
        q = p ** e; rest = n // q
        # lift a residue r mod q to a unit mod n that is 1 mod rest
        def lift(r):
            # CRT: x = r mod q, x = 1 mod rest
            for x in range(n):
                if x % q == r % q and (rest == 1 or x % rest == 1):
                    return x
        if p == 2:
            if e == 1:
                continue
            gens.append((lift(q - 1), 2))
            if e >= 3:
                gens.append((lift(5), 2 ** (e - 2)))
        else:
            # primitive root mod p^e
            ph = phi(q)
            for g in range(2, q):
                if gcd(g, q) != 1:
                    continue
                ok = all(pow(g, ph // r, q) != 1 for r, _ in factorization(ph))
                if ok:
                    gens.append((lift(g), ph)); break
    return gens

def character_table(n):
    """Rows = characters, columns = units (in the order of units(n))."""
    U = units(n); ph = len(U)
    gens = unit_group_generators(n)
    assert np.prod([o for _, o in gens], dtype=np.int64) == ph if gens else ph == 1
    # discrete logs: enumerate all products of generator powers
    logs = {}
    def rec(i, x, vec):
        if i == len(gens):
            logs[x] = tuple(vec); return
        g, o = gens[i]
        y = x
        for k in range(o):
            rec(i + 1, y, vec + [k]); y = (y * g) % n
    rec(0, 1 % n, [])
    assert len(logs) == ph, (n, len(logs), ph)
    L = np.array([logs[int(b)] for b in U], dtype=np.int64).reshape(ph, len(gens))
    orders = np.array([o for _, o in gens], dtype=np.int64)
    # characters indexed by m in prod Z/order_i
    ms = [()]
    for o in orders:
        ms = [m + (k,) for m in ms for k in range(o)]
    X = np.zeros((ph, ph), dtype=complex)
    for i, m in enumerate(ms):
        ang = np.zeros(ph)
        for j, o in enumerate(orders):
            ang += 2 * np.pi * m[j] * L[:, j] / o
        X[i] = np.exp(1j * ang)
    return X, U

def nu_t(q, t):
    U = units(q)
    D = (t * t - 4 * U * U) % (4 * q)
    return Ntab(q)[D].sum() / len(U)

bf = 0
growth = []   # (n, max over t of sum_chi |a^(chi)| / sqrt(n))
for n in range(1, NMAX_B + 1):
    X, U = character_table(n)
    ph = len(U)
    tvals = np.arange(0, n + 1)
    A, _ = a_matrix(n, tvals)                     # (T, ph) integers
    Ahat = (A @ X.conj().T) / ph                  # (T, ph): a^(chi) = phi^{-1} sum_b a(b) conj(chi(b))
    # orthogonality sanity: X X^* = phi I
    if not np.allclose(X @ X.conj().T, ph * np.eye(ph)):
        bf += 1; print("FAIL character orthogonality", n)
    # inversion: a = sum_chi a^(chi) chi
    if not np.allclose(Ahat @ X, A):
        bf += 1; print("FAIL Fourier inversion", n)
    # Plancherel with the paper's normalisation
    lhs = (np.abs(Ahat) ** 2).sum(axis=1); rhs = (A * A).sum(axis=1) / ph
    if not np.allclose(lhs, rhs):
        bf += 1; print("FAIL Plancherel", n)
    # a^(chi_0) = delta_t(n), delta_t by the other route
    delta = np.array([sum(liouville(n // q) * nu_t(q, int(t)) for q in divisors(n)) for t in tvals])
    if not np.allclose(Ahat[:, 0].real, delta) or not np.allclose(Ahat[:, 0].imag, 0):
        bf += 1; print("FAIL a^(chi_0) = delta_t(n)", n)
    # the inequality actually used
    S1 = np.abs(Ahat).sum(axis=1)
    if (S1 > np.sqrt((A * A).sum(axis=1)) + 1e-9).any():
        bf += 1; print("FAIL sum|a^| <= S2^{1/2}", n)
    growth.append((n, float(S1.max() / np.sqrt(n)), float(S1.max())))
print("(b) all n <= %d, all t classes: %s" % (NMAX_B, "OK" if bf == 0 else "FAILURES"))
g = sorted(growth, key=lambda x: -x[1])[:8]
print("    largest max_t sum_chi|a^(chi)| / n^{1/2}:", ", ".join("n=%d: %.3f" % (n, r) for n, r, _ in g))
print("    max_t sum_chi|a^(chi)| at n=%d: %.3f  (n^{1/2}=%.2f)" % (NMAX_B, growth[-1][2], NMAX_B ** 0.5))
print("ALL OK" if fails == 0 and wf == 0 and bf == 0 else "FAILURES ABOVE")
