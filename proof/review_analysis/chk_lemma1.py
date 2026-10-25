# Lemma 1 check: Eichler-Selberg (Zagier form) vs PARI Hecke matrices on S_k(SL2(Z))
from fractions import Fraction as Fr
import math, mpmath
from cypari import pari
pari.allocatemem(2 * 2**30)
mpmath.mp.dps = 40

def H(N):
    if N == 0: return Fr(-1, 12)
    if N < 0 or N % 4 in (1, 2): return Fr(0)
    v = pari.qfbhclassno(N)
    return Fr(int(pari.numerator(v)), int(pari.denominator(v)))

def P(k, t, n):
    # coefficient of x^(k-2) in 1/(1 - t x + n x^2):  P_0 = 1, P_1 = t, P_m = t P_{m-1} - n P_{m-2}
    a, b = 1, t
    if k - 2 == 0: return 1
    for _ in range(k - 3):
        a, b = b, t * b - n * a
    return b

def trace_ES(k, n):
    s = Fr(0)
    t = 0
    while t * t <= 4 * n:
        for tt in ({t, -t}):
            s += P(k, tt, n) * H(4 * n - tt * tt)
        t += 1
    s = -s / 2
    d = 1
    dsum = 0
    while d * d <= n:
        if n % d == 0:
            dd = n // d
            dsum += min(d, dd) ** (k - 1) * (1 if d == dd else 2)
        d += 1
    return s - Fr(dsum, 2)

def trace_pari(k, n):
    mf = pari.mfinit([1, k], 1)
    if int(pari.mfdim(mf)) == 0: return 0
    return int(pari.trace(pari.mfheckemat(mf, n)))

bad = 0; cnt = 0
for k in (12, 16, 18, 20, 22, 24, 26, 28, 30, 36, 40, 48, 50, 62):
    for p in (2, 3, 5, 7, 11, 13):
        n = p * p
        a = trace_ES(k, n); b = trace_pari(k, n)
        cnt += 1
        if a != b:
            bad += 1; print("MISMATCH", k, p, a, b)
# also non-square n to confirm general validity
for k in (12, 24, 36):
    for n in (2, 3, 6, 10, 12, 30):
        a = trace_ES(k, n); b = trace_pari(k, n); cnt += 1
        if a != b: bad += 1; print("MISMATCH", k, n, a, b)
print(f"exact trace formula vs PARI mfheckemat: {cnt} cases, {bad} mismatches")

# check k = 2 and k = 4..10 (S_k = 0): formula should give 0 for k>=4, and -sigma_1(n)... for k=2
for k in (4, 6, 8, 10):
    vals = [trace_ES(k, n) for n in (4, 9, 25, 6)]
    print("k =", k, "(dim 0) formula gives", vals)
print("k = 2 formula gives", [trace_ES(2, n) for n in (4, 9, 25)], " (needs +sigma_1(n) correction, irrelevant for k>=4)")

# normalized form with U_{k-2}(t/2sqrt n), specialized p^2 form of the doc
def doc_p2(k, p):
    s = mpmath.mpf(0)
    for t in range(-(2 * p - 1), 2 * p):
        x = mpmath.mpf(t) / (2 * p)
        th = mpmath.acos(x)
        U = mpmath.sin((k - 1) * th) / mpmath.sin(th)
        s += mpmath.mpf(H(4 * p * p - t * t).numerator) / H(4 * p * p - t * t).denominator * U
    return -s / (2 * p) + mpmath.mpf(k - 1) / (12 * p) - mpmath.mpf(1) / 2 - mpmath.mpf(p) ** (1 - k)
worst = 0
for k in (12, 24, 50, 100):
    for p in (2, 3, 5, 7, 11, 13, 17):
        ex = trace_pari(k, p * p) if k <= 50 else trace_ES(k, p * p)
        ex = mpmath.mpf(ex.numerator if isinstance(ex, Fr) else ex) / (mpmath.mpf(ex.denominator) if isinstance(ex, Fr) else 1)
        norm = ex / mpmath.mpf(p) ** (k - 1)
        d = doc_p2(k, p)
        worst = max(worst, abs(norm - d))
print("normalized p^2 specialization (doc display) vs exact: max abs diff =", mpmath.nstr(worst, 5))
