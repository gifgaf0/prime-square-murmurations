"""Local densities for the prime average of Zagier's L(1, t^2 - 4p^2).
L(s, D) = zeta(2s)/zeta(s) * sum_q N_q(D) q^-s,  N_q(D) = #{x mod 2q : x^2 = D mod 4q};  so a_D = lambda * N(D) (Liouville lambda).
nu_t(q)  = average over units b mod q of N_q(t^2 - 4 b^2)
delta_t(l^j) = sum_{i<=j} (-1)^(j-i) nu_t(l^i)
E_l(t) = sum_j delta_t(l^j) l^-j   (local factor of f_2(t) = sum_n delta_t(n)/n)
Compare with the Ramanujan-side factors F_l(v), v = v_l(t), predicted by identity (*): f_2(t) = sum_c G(c) c_c(t), G(c) = A_2(c) c^-2 prod_{l|c}(1-l^-2)^-1."""
from fractions import Fraction as Fr
from math import gcd
import sys
def sqcount(mod2q, mod4q):
    cnt = [0] * mod4q
    for x in range(mod2q): cnt[x * x % mod4q] += 1
    return cnt
def nu(t, q):
    cnt = sqcount(2 * q, 4 * q); s = 0; nb = 0
    for b in range(q):
        if gcd(b, q) != 1: continue
        nb += 1; s += cnt[(t * t - 4 * b * b) % (4 * q)]
    return Fr(s, nb)
def E_local(t, l, J):
    nus = [Fr(1)] + [nu(t, l ** i) for i in range(1, J + 1)]
    deltas = [sum((-1) ** (j - i) * nus[i] for i in range(j + 1)) for j in range(J + 1)]
    return sum(deltas[j] / Fr(l) ** j for j in range(J + 1)), deltas
def chi4(l): return 0 if l % 2 == 0 else (1 if l % 4 == 1 else -1)
def F_ram(l, v):
    if l == 2: return [Fr(2, 3), Fr(5, 3)][v] if v < 2 else Fr(1)
    c = chi4(l)
    return 1 - Fr(1 + c * l, (l - 1) * (l * l - 1)) if v == 0 else Fr(l, l - c)
if __name__ == "__main__":
    for l, J in ((2, 14), (3, 9), (5, 6), (7, 5), (11, 4), (13, 4)):
        for v in range(0, 4):
            for u in ((1, 3, 5, 7) if l == 2 else (1, 2, 4)):
                if u % l == 0: continue
                t = l ** v * u
                E, d = E_local(t, l, J)
                print(f"l={l:2d} t={t:5d} (v={v}, u={u}):  E_l = {float(E):.10f}   F_l(v) = {float(F_ram(l, v)):.10f}   diff {float(E - F_ram(l, v)):+.2e}"
                      f"   delta_t(l^j) = {[str(x) for x in d[:5]]}", flush=True)
