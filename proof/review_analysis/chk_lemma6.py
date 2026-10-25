from fractions import Fraction as Fr
from math import gcd
def chi(l): return 0 if l % 2 == 0 else (1 if l % 4 == 1 else -1)
def nu(t, q):
    c = [0] * (4 * q)
    for x in range(2 * q): c[x * x % (4 * q)] += 1
    us = [b for b in range(q) if gcd(b, q) == 1]
    return Fr(sum(c[(t * t - 4 * b * b) % (4 * q)] for b in us), len(us))
def table(l, t, j):
    if l == 2:
        if t % 2: return Fr((-1) ** j)
        if t % 4 == 2: return Fr(0 if j % 2 else 2)
        return Fr(0)
    if t % l: return Fr(1) if j % 2 == 0 else Fr(-(1 + chi(l)), l - 1)
    return Fr(chi(l) ** j)
bad = 0; n = 0
for l, J in ((2, 12), (3, 7), (5, 5), (7, 4), (11, 3), (13, 3)):
    for t in [0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 21, 25, 26, 49, 50, 77, 121, 169, 338, 1001, 2 * 3 * 5 * 7 * 11 * 13]:
        nus = [Fr(1)] + [nu(t, l ** i) for i in range(1, J + 1)]
        for j in range(1, J + 1):
            d = sum((-1) ** (j - i) * nus[i] for i in range(j + 1))
            n += 1
            if d != table(l, t, j):
                bad += 1
                if bad < 6: print("mismatch l=%d t=%d j=%d brute=%s table=%s" % (l, t, j, d, table(l, t, j)))
print(f"Lemma 6 table vs brute force: {n} entries, {bad} mismatches")
