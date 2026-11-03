#!/usr/bin/env python3
"""Independent check of the sharpness claim for Lemma 7(b) at prime moduli.

For p prime, p ∤ 2t, with a(b) = a_{t^2-4b^2}(p) computed from the DEFINITION
(a_D(p) = lambda(p) N_1(D) + N_p(D) = N_p(D) - 1), check:
  (1) a(b) = Legendre((t^2-4b^2)/p) for every unit b;
  (2) sum_b a(b)^2 = p - 3;
  (3) a^(chi) = 0 for odd chi;
  (4) for even chi = psi^2 != chi_0:  a^(chi) = conj(psi)(t^2/4) (J + chi2(-1) conj(J)) / (p-1),
      J = J(chi2, conj psi) = sum_x chi2(x) conj(psi)(1-x), |J| = sqrt(p);
  (5) sum_chi |a^(chi)| >= (p-3)/(2 sqrt p).
Characters are built from a primitive root; nothing is shared with the reviewer's probe.
"""
import cmath, math

def primitive_root(p):
    ph = p - 1
    fac = set()
    m = ph
    d = 2
    while d * d <= m:
        while m % d == 0:
            fac.add(d); m //= d
        d += 1
    if m > 1:
        fac.add(m)
    for g in range(2, p):
        if all(pow(g, ph // f, p) != 1 for f in fac):
            return g

def legendre(x, p):
    x %= p
    if x == 0:
        return 0
    return 1 if pow(x, (p - 1) // 2, p) == 1 else -1

def N_q(q, D):
    return sum(1 for x in range(2 * q) if (x * x - D) % (4 * q) == 0)

ok = True
for p in [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103]:
    g = primitive_root(p)
    dlog = {pow(g, k, p): k for k in range(p - 1)}
    chi2 = lambda x: legendre(x, p)
    for t in range(1, p):
        if t % p == 0:
            continue
        # a(b) from the definition
        a = {}
        for b in range(1, p):
            D = t * t - 4 * b * b
            a[b] = N_q(p, D) - N_q(1, D)          # lambda(1)=1 on N_p, lambda(p)=-1 on N_1
            if a[b] != legendre(D, p):
                ok = False; print("FAIL (1)", p, t, b)
        S2 = sum(v * v for v in a.values())
        if S2 != p - 3:
            ok = False; print("FAIL (2)", p, t, S2)
        c = (t * t * pow(4, -1, p)) % p
        total = 0.0
        for m in range(p - 1):                     # chi_m(b) = exp(2 pi i m dlog(b)/(p-1))
            chi = lambda x: cmath.exp(2j * math.pi * m * dlog[x % p] / (p - 1))
            ahat = sum(a[b] * chi(b).conjugate() for b in range(1, p)) / (p - 1)
            total += abs(ahat)
            if m % 2 == 1:
                if abs(ahat) > 1e-10:
                    ok = False; print("FAIL (3)", p, t, m)
            elif m != 0:
                k = m // 2                         # psi = chi_k, psi^2 = chi_m
                psi = lambda x: cmath.exp(2j * math.pi * k * dlog[x % p] / (p - 1))
                J = sum(chi2(x) * psi(1 - x).conjugate() for x in range(2, p))
                if abs(abs(J) - math.sqrt(p)) > 1e-8:
                    ok = False; print("FAIL |J|", p, t, m)
                pred = psi(c).conjugate() * (J + chi2(-1) * J.conjugate()) / (p - 1)
                if abs(pred - ahat) > 1e-9:
                    ok = False; print("FAIL (4)", p, t, m, pred, ahat)
        if total < (p - 3) / (2 * math.sqrt(p)) - 1e-9:
            ok = False; print("FAIL (5)", p, t, total)
    # report the ratio at one t
    print("p=%3d: max_t sum|a^| / sqrt p = %.3f   lower bound (p-3)/(2p) = %.3f" % (
        p,
        max(sum(abs(sum(a_b * cmath.exp(-2j*math.pi*m*dlog[b]/(p-1)) for b, a_b in
                ((b, legendre(t*t-4*b*b, p)) for b in range(1, p))) / (p-1))
                for m in range(p-1)) for t in range(1, p)) / math.sqrt(p),
        (p - 3) / (2 * p)))
print("ALL OK" if ok else "FAILURES ABOVE")
