"""
Item 3b: Lemma 8 local identity E_l(t) = sum_j G(l^j) c_{l^j}(l^v), exact rationals, all cases;
Ramanujan sums from the definition; the prime analogue (A_1 = mu^2/phi) against the prime local factors
(computed by brute force from the definition of the prime-case densities: average over units b of N_q(t^2-4b));
global check sum_{c<=C} G(c) c_c(t) -> f_2(t) (Euler product); partial sums P_C(0)=sum_{c<=C} G(c) phi(c) -> pi/4.
"""
from fractions import Fraction
from math import gcd, pi
import numpy as np
import cmath
from s1_local_densities import table_E, chi4, sqcount, units, vl, liouville

def ram_def(q, n):
    s = sum(cmath.exp(2j * cmath.pi * a * n / q) for a in range(q) if gcd(a, q) == 1) if q > 1 else 1
    return round(s.real)

def mu_small(n):
    r = 1; p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r

def ram_gen(q, n):
    """c_q(n) = sum_{d | (q,n)} d mu(q/d) (small q only)"""
    g = gcd(q, n) if n != 0 else q
    return sum(d * mu_small(q // d) for d in range(1, g + 1) if g % d == 0)

def ram(q, n):
    """prime-power closed form: q = l^j. c_{l^j}(n) = phi(l^j) if l^j | n, -l^(j-1) if l^(j-1) || n, else 0."""
    if q == 1:
        return 1
    l = next(p for p in range(2, q + 1) if q % p == 0)
    j = 0; m = q
    while m % l == 0:
        m //= l; j += 1
    assert m == 1
    if n == 0 or n % (l ** j) == 0:
        return l ** j - l ** (j - 1)
    if n % (l ** (j - 1)) == 0:
        return -(l ** (j - 1))
    return 0

def A2loc(l, j):
    if j == 0: return Fraction(1)
    if l == 2: return {1: Fraction(1), 2: Fraction(-2)}.get(j, Fraction(0))
    return Fraction(1 + chi4(l) * l, l - 1) if j == 1 else Fraction(0)

def A1loc(l, j):
    if j == 0: return Fraction(1)
    return Fraction(1, l - 1) if j == 1 else Fraction(0)

def Gloc(Aloc, l, j):
    if j == 0: return Fraction(1)
    return Aloc(l, j) / Fraction(l ** (2 * j)) / (1 - Fraction(1, l * l))

def nu1(t, q):
    U = units(q)
    return Fraction(sum(sqcount(q)[(t * t - 4 * b) % (4 * q)] for b in U), len(U))

def E1_brute(t, l, J):
    """prime-case local factor from definition, J terms + exact geometric tail from period-2 pattern"""
    nus = [nu1(t, l ** i) for i in range(J + 1)]
    d = [sum(((-1) ** (j - i)) * nus[i] for i in range(j + 1)) for j in range(J + 1)]
    # pattern: d_j depends only on parity of j for j>=2 (checked below); tail from that
    assert d[J] == d[J - 2] and d[J - 1] == d[J - 3]
    s = sum(d[j] * Fraction(1, l ** j) for j in range(J + 1))
    x = Fraction(1, l)
    tail = (d[J - 1] * x ** (J + 1) + d[J] * x ** (J + 2)) / (1 - x * x)
    return s + tail

if __name__ == "__main__":
    # Ramanujan sums: formula vs definition
    badr = sum(1 for q in range(1, 130) for n in range(0, 70) if ram_gen(q, n) != ram_def(q, n))
    ppows = [p ** j for p in [2, 3, 5, 7, 11] for j in range(0, 4) if p ** j < 1400]
    badr2 = sum(1 for q in ppows for n in range(0, 300) if ram(q, n) != ram_def(q, n))
    print("Ramanujan sum: general formula vs definition (q<130, 0<=n<70) mismatches:", badr,
          "; prime-power closed form vs definition mismatches:", badr2)

    # Lemma 8 local identity
    primes = [p for p in range(2, 400) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
    bad = []; n = 0
    for l in primes:
        for v in [0, 1, 2, 3, 7, None]:  # None = v=infinity (t=0)
            t = 0 if v is None else (l ** v) * (1 if l != 3 else 2)  # t with v_l(t)=v
            if v is not None and l == 2:
                t = 2 ** v * 3
            rhs = sum(Gloc(A2loc, l, j) * ram(l ** j, l ** (v if v is not None else 12)) for j in range(0, 6))
            lhs = table_E(t, l)
            n += 1
            if lhs != rhs:
                bad.append((l, v, lhs, rhs))
    print(f"Lemma 8 local identity (squares): {n} cases, mismatches: {len(bad)}", bad[:5])

    # prime analogue: sum_j G1(l^j) c_{l^j}(l^v) vs brute-force prime local factor
    bad1 = []; n1 = 0
    for l in [2, 3, 5, 7, 11, 13]:
        J = {2: 9, 3: 6, 5: 5, 7: 4, 11: 4, 13: 4}[l]
        for t in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 25, 26, 49, 121, 169, 1001]:
            v = vl(t, l)
            rhs = sum(Gloc(A1loc, l, j) * ram(l ** j, l ** min(v, 12)) for j in range(0, 6))
            lhs = E1_brute(t, l, J)
            # Bober et al. form: (1-l^-2)^-1 * [(l^2-l-1)/(l^2-l) if l does not divide t else 1]
            bob = 1 / (1 - Fraction(1, l * l)) * (Fraction(l * l - l - 1, l * l - l) if t % l else 1)
            n1 += 1
            if not (lhs == rhs == bob):
                bad1.append((l, t, lhs, rhs, bob))
    print(f"prime analogue: {n1} cases, mismatches: {len(bad1)}", bad1[:5])

    # global: sum_{c<=C} G(c) c_c(t) vs Euler product f_2(t)
    C = 2 * 10 ** 6
    spf = np.zeros(C + 1, dtype=np.int64)
    for p in range(2, C + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    G = np.zeros(C + 1); G[1] = 1.0
    PHI = np.zeros(C + 1); PHI[1] = 1.0
    MU = np.zeros(C + 1, dtype=np.int64); MU[1] = 1
    for c in range(2, C + 1):
        p = int(spf[c]); m = c; e = 0
        while m % p == 0:
            m //= p; e += 1
        pe = p ** e
        G[c] = G[m] * float(Gloc(A2loc, p, e)) if (p == 2 and e <= 2) or e == 1 else 0.0
        PHI[c] = PHI[m] * (pe - pe // p)
        MU[c] = 0 if e > 1 else -MU[m]
    np.save("G_2e6.npy", G)

    # Euler product with primes up to C (tail ~ sum_{l>C} chi(l)/l^2: negligible)
    isp = (spf == np.arange(C + 1)); isp[:2] = False
    P = np.nonzero(isp)[0]
    Podd = P[P > 2].astype(float)
    chi = np.where(P[P > 2] % 4 == 1, 1.0, -1.0)
    E0 = (1 - (1 + chi) / (Podd * (Podd - 1))) / (1 - 1 / Podd ** 2)
    logC0 = np.sum(np.log(E0))
    def f2(t):
        if t == 0:
            return pi / 4
        tt = abs(t)
        # C_odd uses the l-not-dividing-t factor for every odd l; swap in the l | t factor for odd l | t
        r = float(table_E(t, 2)) * np.exp(logC0)
        m = tt
        while m % 2 == 0: m //= 2
        l = 3
        while m > 1:
            if m % l == 0:
                c = chi4(l)
                r *= (l / (l - c)) / ((1 - (1 + c) / (l * (l - 1))) / (1 - 1 / l ** 2))
                while m % l == 0: m //= l
            l += 2
        return r
    print("C_odd = prod_{l odd} E_l^(0) =", np.exp(logC0))
    for t in [1, 2, 3, 4, 5, 6, 7, 8, 12, 15, 30, 105, 210, 1155]:
        divs = [d for d in range(1, t + 1) if t % d == 0]
        for Cc in [10 ** 4, 10 ** 5, C]:
            s = 0.0
            for d in divs:
                k = np.arange(1, Cc // d + 1)
                s += d * np.sum(MU[k] * G[d * k])
            if Cc == C:
                print(f"t={t:5d}: sum_(c<=2e6) G(c)c_c(t) = {s:.12f}   Euler f_2(t) = {f2(t):.12f}   diff = {s - f2(t):.2e}")
    # t = 0: partial sums of G(c) phi(c)
    cs = np.cumsum(G * PHI)
    print("P_C(0) = sum_{c<=C} G(c)phi(c), target pi/4 = %.12f" % (pi / 4))
    for Cc in [10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, C]:
        d = cs[Cc] - pi / 4
        print(f"   C={Cc:8d}: P_C(0) = {cs[Cc]:.10f}, P_C - pi/4 = {d:+.3e}, (P_C-pi/4)*sqrt(C)*log(C) = {d * Cc ** 0.5 * np.log(Cc):+.3f}")
    np.save("f2_consts.npy", np.array([np.exp(logC0)]))
