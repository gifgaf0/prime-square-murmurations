"""
Item 1: brute-force exact local densities.
nu_t(q)    = average over units b mod q of N_q(t^2 - 4 b^2),
N_q(D)     = #{x mod 2q : x^2 = D mod 4q},
delta_t(n) = average over units b mod n of a_{t^2-4b^2}(n),  a_D = lambda * N(D).
Everything in exact rationals (fractions.Fraction).
"""
from fractions import Fraction
from math import gcd
from functools import lru_cache
import itertools, sys

def chi4(l):
    return 0 if l % 2 == 0 else (1 if l % 4 == 1 else -1)

@lru_cache(maxsize=None)
def sqcount(q):
    M = 4 * q
    cnt = [0] * M
    for x in range(2 * q):
        cnt[(x * x) % M] += 1
    return cnt

def N(q, D):
    return sqcount(q)[D % (4 * q)]

def units(n):
    return [b for b in range(n) if gcd(b, n) == 1]  # n=1 -> [0]

def nu(t, q):
    U = units(q)
    return Fraction(sum(N(q, t * t - 4 * b * b) for b in U), len(U))

def liouville(n):
    k, m, p = 0, n, 2
    while p * p <= m:
        while m % p == 0:
            m //= p; k += 1
        p += 1
    if m > 1:
        k += 1
    return (-1) ** k

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def delta_direct(t, n):
    """definition: average over units b mod n of a_{t^2-4b^2}(n)"""
    U = units(n)
    divs = divisors(n)
    tot = 0
    for b in U:
        D = t * t - 4 * b * b
        tot += sum(liouville(n // q) * N(q, D) for q in divs)
    return Fraction(tot, len(U))

def delta_pp(t, l, j):
    """delta_t(l^j) = sum_{i<=j} (-1)^(j-i) nu_t(l^i)"""
    return sum(((-1) ** (j - i)) * nu(t, l ** i) for i in range(j + 1))

def vl(t, l):
    if t == 0:
        return 10 ** 9
    v = 0
    while t % l == 0:
        t //= l; v += 1
    return v

def table_delta(t, l, j):
    """Lemma 6 table, j >= 1"""
    if l % 2 == 1:
        c = chi4(l)
        if t % l != 0:
            return Fraction(1) if j % 2 == 0 else Fraction(-(1 + c), l - 1)
        return Fraction(c) ** j
    v = vl(t, 2)
    if v == 0:
        return Fraction((-1) ** j)
    if v == 1:
        return Fraction(0) if j % 2 == 1 else Fraction(2)
    return Fraction(0)

def table_E(t, l):
    if l % 2 == 1:
        c = chi4(l)
        if t % l != 0:
            return (1 - Fraction(1 + c, l * (l - 1))) / (1 - Fraction(1, l * l))
        return Fraction(l, l - c)
    v = vl(t, 2)
    return [Fraction(2, 3), Fraction(5, 3), Fraction(1)][min(v, 2)]

def nu_hand(t, l, i):
    """hand formula from the doc's proof"""
    if i == 0:
        return Fraction(1)
    if l % 2 == 1:
        c = chi4(l)
        return (1 - Fraction(1 + c, l - 1)) if t % l else Fraction(1 + c)
    v = vl(t, 2)
    if v == 0:
        return Fraction(0)
    if v == 1:
        return Fraction(1) if i == 1 else Fraction(2)
    return Fraction(1) if i == 1 else Fraction(0)

if __name__ == "__main__":
    maxpow = {2: 10, 3: 6, 5: 4, 7: 3, 11: 3, 13: 3, 17: 2, 19: 2, 23: 2, 29: 2, 31: 2}
    nchecks = 0; bad = []
    for l, J in maxpow.items():
        ts = set(range(0, 2 * l + 3))
        for v in range(0, 4):
            for u in (1, 2, 3, 5, 7):
                if u % l:
                    ts.add(u * l ** v)
        ts |= {-3, -l, 1001, 2 * 3 * 5 * 7 * 11 * 13}
        for t in sorted(ts):
            for i in range(0, J + 1):
                a = nu(t, l ** i); b = nu_hand(t, l, i)
                nchecks += 1
                if a != b:
                    bad.append(("nu", l, i, t, a, b))
            for j in range(1, J + 1):
                a = delta_pp(t, l, j); b = table_delta(t, l, j)
                nchecks += 1
                if a != b:
                    bad.append(("delta", l, j, t, a, b))
            # E_l(t): geometric tail is exact from the table pattern; check partial sums of the brute values
            # agree with the table's E up to the table-predicted tail beyond J
            partial = 1 + sum(delta_pp(t, l, j) * Fraction(1, l ** j) for j in range(1, J + 1))
            tail = sum(table_delta(t, l, j) * Fraction(1, l ** j) for j in range(J + 1, J + 60))
            err = abs(float(partial + tail - table_E(t, l)))
            nchecks += 1
            if err > 1e-15:
                bad.append(("E", l, t, float(partial + tail), float(table_E(t, l))))
    print("prime-power checks:", nchecks, "mismatches:", len(bad))
    for x in bad[:20]:
        print("  ", x)

    # multiplicativity of delta_t(n) straight from the definition (composite n)
    comp = [6, 10, 12, 14, 15, 18, 20, 21, 24, 28, 30, 36, 40, 42, 45, 60, 63, 72, 84, 90, 105, 120]
    badm = []; nm = 0
    for t in [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 21, 30, 35, 60, 105, -8]:
        for n in comp:
            direct = delta_direct(t, n)
            fac = Fraction(1); m = n; p = 2
            while m > 1:
                if m % p == 0:
                    e = 0
                    while m % p == 0:
                        m //= p; e += 1
                    fac *= (table_delta(t, p, e) if e >= 1 else 1)
                p += 1
            nm += 1
            if direct != fac:
                badm.append((t, n, direct, fac))
    print("composite-n checks (definition vs product of table values):", nm, "mismatches:", len(badm))
    for x in badm[:10]:
        print("  ", x)
    # a few explicit values for the record
    for (t, l) in [(1, 3), (3, 3), (1, 5), (5, 5), (1, 2), (2, 2), (4, 2), (0, 2), (0, 3), (0, 5)]:
        print(f"t={t:3d} l={l}: nu(l^i), i=1..4:", [str(nu(t, l ** i)) for i in range(1, 5)],
              " delta(l^j), j=1..4:", [str(delta_pp(t, l, j)) for j in range(1, 5)], " E=", table_E(t, l))
