import math
from fractions import Fraction as Fr
from cypari import pari
pari.allocatemem(2 * 2**30)

def Nq(D, q):
    m = 4 * q
    return sum(1 for x in range(2 * q) if (x * x - D) % m == 0)
def kron(D, l): return int(pari.kronecker(D, l))
def core(D):
    D0 = int(pari.coredisc(D)); f = math.isqrt(D // D0); assert D0 * f * f == D; return D0, f
def val(n, l):
    v = 0
    while n % l == 0: n //= l; v += 1
    return v

# (a) local factors: (1/(1+X)) sum_j N_{l^j} X^j  vs  L_l(s,chi_D0) * B_f local factor
def local_lhs(D, l, J):
    Ns = [Nq(D, l ** j) for j in range(J + 1)]
    return [sum((-1) ** (j - i) * Ns[i] for i in range(j + 1)) for j in range(J + 1)]
def local_rhs(D0, e, l, J):
    c = kron(D0, l)
    # B_f local: sum_{d | l^e} mu(d) c(d) d^-s sigma_{1-2s}(l^e/d), X = l^-s:
    #   sigma_{1-2s}(l^m) = sum_{i<=m} l^i X^{2i};  d = l contributes -c X * sigma(l^{e-1})
    Bf = [0] * (J + 1)
    for i in range(e + 1):
        if 2 * i <= J: Bf[2 * i] += l ** i
    for i in range(e):
        if 2 * i + 1 <= J: Bf[2 * i + 1] -= c * l ** i
    return [sum(Bf[i] * c ** (j - i) for i in range(j + 1)) for j in range(J + 1)]

bad = 0; cnt = 0; cnt_r1 = 0; cnt_2 = 0
Ds = [D for D in range(-3, -1500, -1) if D % 4 in (0, 1)]
Ds += [-3 * 4 ** 3 * 9, -4 * 27 * 25, -8 * 64, -7 * 121 * 9, -3 * 3 ** 6, -20 * 25 * 4, -24 * 36, -4 * 1009 ** 2 + 9 ** 2, -4 * 997 ** 2 + 400]
for D in Ds:
    D0, f = core(D)
    for l in (2, 3, 5, 7, 11):
        e = val(f, l)
        J = 2 * e + 4
        if l ** J > 2 * 10 ** 5: J = max(2 * e + 2, 1)
        a = local_lhs(D, l, J); b = local_rhs(D0, e, l, J)
        cnt += 1
        if D0 % l == 0 and e > 0: cnt_r1 += 1
        if l == 2 and e > 0: cnt_2 += 1
        if a != b:
            bad += 1
            if bad < 5: print("mismatch", D, l, a, b)
print(f"(a) Euler factor identity L(s,D) = L(s,chi_D0) B_f(s): {cnt} (D,l) pairs [{cnt_r1} with l | D0 and l | f; {cnt_2} with l = 2 | f], mismatches {bad}")

# (b) Hensel count as stated in the proof: odd l, l^e || f, D = l^(2e+r) u:
#     N_{l^j}(D) = l^floor(j/2) for j <= 2e + r and (1 + chi_D0(l)) l^e for larger j
fails = []; ok = 0
for D in Ds:
    D0, f = core(D)
    for l in (3, 5, 7):
        e = val(f, l); r = val(D, l) - 2 * e
        for j in range(1, 2 * e + r + 4):
            if l ** j > 10 ** 5: break
            stated = l ** (j // 2) if j <= 2 * e + r else (1 + kron(D0, l)) * l ** e
            true = Nq(D, l ** j)
            if stated != true: fails.append((D, l, e, r, j, stated, true))
            else: ok += 1
print(f"(b) Hensel count as stated: {ok} agree, {len(fails)} disagree; r-values among failures: {sorted(set(x[3] for x in fails))}")
for x in fails[:4]: print("    D=%d l=%d e=%d r=%d j=%d stated=%d true=%d" % x)

# (c) H(|D|) = sqrt|D|/pi * L(1,chi_D0) * B_f(1)
worst = 0; n = 0
for D in Ds[::3] + [-4 * 1009 ** 2 + 9, -4 * 997 ** 2 + 400, -3 * 49 ** 2, -4 * 30 ** 2, -3 * 2 ** 10, -4 * 3 ** 8]:
    if D % 4 not in (0, 1): continue
    D0, f = core(D)
    L1 = float(pari(f"lfun(lfuncreate({D0}), 1)"))
    B = 0.0
    for d in range(1, f + 1):
        if f % d == 0:
            mu = int(pari.moebius(d)); s1 = sum(1 / ee for ee in range(1, f // d + 1) if (f // d) % ee == 0)
            B += mu * kron(D0, d) / d * s1
    Hx = float(pari.qfbhclassno(-D)); Hy = math.sqrt(-D) / math.pi * L1 * B
    worst = max(worst, abs(Hx - Hy) / Hx); n += 1
print(f"(c) H(|D|) = sqrt|D|/pi L(1,D): {n} discriminants, max relative deviation {worst:.1e}")

# (d) a_D(n) = sum_{q|n} lambda(n/q) N_q(D): periodic mod 4n? multiplicative in n?
def liou(m): return (-1) ** int(pari.bigomega(m)) if m > 1 else 1
def aD(D, n): return sum(liou(n // q) * Nq(D, q) for q in range(1, n + 1) if n % q == 0)
per_bad = 0; per2n_bad = 0; mult_bad = 0
for n in range(1, 41):
    for D in range(-3, -200, -1):
        if D % 4 not in (0, 1): continue
        a = aD(D, n)
        if a != aD(D - 4 * n, n): per_bad += 1
        D2 = D - 2 * n
        if D2 % 4 in (0, 1) and a != aD(D2, n): per2n_bad += 1
for D in range(-3, -150, -1):
    if D % 4 not in (0, 1): continue
    for n1 in range(1, 16):
        for n2 in range(1, 16):
            if math.gcd(n1, n2) == 1 and aD(D, n1 * n2) != aD(D, n1) * aD(D, n2): mult_bad += 1
print(f"(d) a_D(n) periodic mod 4n: {per_bad} failures; (control) periodic mod 2n: {per2n_bad} failures; multiplicativity failures: {mult_bad}")
