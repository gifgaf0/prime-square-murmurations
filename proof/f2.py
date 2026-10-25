"""f_2(t) as an Euler product (local factors from local.py), checked against prime averages of
L(1, t^2 - 4p^2) = pi H(4p^2 - t^2)/sqrt(4p^2 - t^2) (Hurwitz class numbers from PARI)."""
import math, sys
from cypari import pari
pari.allocatemem(2 * 2**30)
def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
PR = primes_upto(10 ** 6)
def chi4(l): return 0 if l % 2 == 0 else (1 if l % 4 == 1 else -1)
def E(l, v):
    if l == 2: return 2 / 3 if v == 0 else (5 / 3 if v == 1 else 1.0)
    c = chi4(l)
    return (1 - (1 + c) / (l * (l - 1))) / (1 - l ** -2) if v == 0 else 1 / (1 - c / l)
def vl(t, l):
    v = 0
    while t % l == 0: t //= l; v += 1
    return v
C2 = 1.0
for l in PR: C2 *= E(l, 0)
def f2(t):
    if t == 0: return math.pi / 4
    t = abs(t); r = C2
    for l in PR:
        if l > t: break
        if t % l == 0: r *= E(l, vl(t, l)) / E(l, 0)
    return r
if __name__ == "__main__":
    print(f"C2 = prod_l E_l(0) = {C2:.10f}")
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    ps = [p for p in PR if lo <= p <= hi]
    print(f"prime average over {len(ps)} primes in [{lo}, {hi}] (weights log p):")
    for t in list(range(0, 13)) + [15, 20, 30, 60]:
        num = den = 0.0
        for p in ps:
            D = 4 * p * p - t * t
            num += math.log(p) * math.pi * float(pari.qfbhclassno(D)) / math.sqrt(D); den += math.log(p)
        print(f"  t={t:3d}: average L(1, t^2-4p^2) = {num/den:.5f}   f_2(t) = {f2(t):.5f}   ratio {num/den/f2(t):.4f}", flush=True)
