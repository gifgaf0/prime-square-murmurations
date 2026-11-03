#!/usr/bin/env python3
"""Brute-force check of the second-moment lemma for a_{t^2-4b^2}(n).

Everything here is computed from the definitions:
  N_q(D)  = #{x mod 2q : x^2 = D mod 4q}
  a_D(n)  = sum_{q|n} lambda(n/q) N_q(D)        (lambda = Liouville)
  W(q)    = sum_{b unit mod q} N_q(t^2-4b^2)^2
  S2(n,t) = sum_{b unit mod n} a_{t^2-4b^2}(n)^2
Checks:
  (1) W(l^j) <= 4(2j+1) l^j            for odd l        (lemma, odd case)
      W(l^j) <= 4 phi(l^j)             for odd l | t
  (2) W(2^j) <= 128 j phi(2^j)         (lemma, 2-adic case; also the exact
      values 0 / 1 for t odd / 4|t, j>=2)
  (3) W(q1 q2) = W(q1) W(q2) for coprime q1,q2
  (4) S2(n,t) <= tau(n)^2 phi(n) max_{q|n} c(q),  c(q)=prod_{l^j||q} 128 j
      and the ratio S2/(phi(n) tau(n)^2) stays small.
"""
from math import gcd
from functools import lru_cache
import sys

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def phi(n):
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r

def tau(n):
    r = 1
    for e in factor(n).values():
        r *= e + 1
    return r

def liouville(n):
    return (-1) ** sum(factor(n).values()) if n > 1 else 1

@lru_cache(maxsize=None)
def _sqtable(q):
    tab = [0] * (4 * q)
    for x in range(2 * q):
        tab[(x * x) % (4 * q)] += 1
    return tab

def Nq(q, D):
    return _sqtable(q)[D % (4 * q)]

def W(q, t):
    return sum(Nq(q, t * t - 4 * b * b) ** 2 for b in range(q) if gcd(b, q) == 1)

def a(n, D):
    return sum(liouville(n // q) * Nq(q, D) for q in range(1, n + 1) if n % q == 0)

def S2(n, t):
    return sum(a(n, t * t - 4 * b * b) ** 2 for b in range(n) if gcd(b, n) == 1)

def c_of(q):
    r = 1
    for e in factor(q).values():
        r *= 128 * e
    return r

ok = True
# (1) odd prime powers
for l in [3, 5, 7, 11, 13]:
    for j in range(1, 5):
        q = l ** j
        if q > 2500:
            continue
        for t in range(0, min(2 * q, 400) + 1):
            w = W(q, t)
            bound = 4 * (2 * j + 1) * q
            if t % l == 0:
                bound = min(bound, 4 * phi(q))
            if w > bound:
                ok = False
                print("FAIL odd", l, j, t, w, bound)
print("(1) odd prime powers checked")

# (2) powers of 2
for j in range(1, 9):
    q = 2 ** j
    for t in range(0, min(4 * q, 400) + 1):
        w = W(q, t)
        if w > 128 * j * phi(q):
            ok = False
            print("FAIL 2-adic bound", j, t, w)
        if t % 2 == 1 and w != 0:
            ok = False
            print("FAIL t odd", j, t, w)
        if t % 4 == 0 and j >= 2 and w != 0:
            ok = False
            print("FAIL 4|t", j, t, w)
        if t % 4 == 0 and j == 1 and w != 1:
            ok = False
            print("FAIL 4|t j=1", t, w)
print("(2) powers of 2 checked")

# (2') the sharper 2-adic claims actually derived in Sec. 4(c) of the note, for t = 2 mod 4:
#      W(2^j) <= 128 (j-2) phi(2^j) for j >= 3, and the exact values W(2) = 1, W(4) = 8
for j in range(1, 10):
    q = 2 ** j
    for t in range(2, min(4 * q, 400) + 1, 4):
        w = W(q, t)
        if j >= 3 and w > 128 * (j - 2) * phi(q):
            ok = False
            print("FAIL sharper 2-adic", j, t, w)
        if j == 1 and w != 1:
            ok = False
            print("FAIL W(2)", t, w)
        if j == 2 and w != 8:
            ok = False
            print("FAIL W(4)", t, w)
print("(2') sharper 2-adic bound (j>=3) and W(2)=1, W(4)=8 for 2||t checked")

# (3) multiplicativity
for q1, q2 in [(3, 4), (5, 8), (9, 4), (7, 25), (16, 9), (3, 5), (27, 8)]:
    for t in range(0, 40):
        if W(q1 * q2, t) != W(q1, t) * W(q2, t):
            ok = False
            print("FAIL mult", q1, q2, t)
print("(3) multiplicativity checked")

# (4) full second moment for composite n.  n = 1 is trivial (S2(1,t) = N_1^2 = 1, ratio 1),
#     so the ratio is reported for n >= 2.
worst = (0.0, None, None)
for n in list(range(1, 200)) + [210, 216, 240, 256, 360, 420, 480, 512, 720, 840, 900, 960, 1024]:
    for t in range(0, 30):
        s = S2(n, t)
        bound = tau(n) ** 2 * phi(n) * max(c_of(q) for q in range(1, n + 1) if n % q == 0)
        if s > bound:
            ok = False
            print("FAIL S2", n, t, s, bound)
        r = s / (phi(n) * tau(n) ** 2)
        if n >= 2 and r > worst[0]:
            worst = (r, n, t)
print("(4) composite n checked; max S2/(phi(n) tau(n)^2) over n>=2 = %.4f at n=%d, t=%d" % worst)
print("ALL OK" if ok else "FAILURES ABOVE")
