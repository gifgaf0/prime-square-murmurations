"""
Item 5: numerical check of Theorem B (squares) and its prime analogue.

Squares:  LHS = (1/(2 zeta2)) sum_t f_2(t) I(t)/I(0),   I(t) = int Phi(y) cos(2 pi t/sqrt y) y^(-1/2) dy
          RHS = lim_C (1/I(0)) sum_{c<=C} sum_{(m,c)=1} T_2(c)/m^2 Phi((c/m)^2)
Primes:   LHS1 = (1/(2 zeta2)) sum_t f_1(t) I1(t)/I1(0), I1(t) = int Phi(y) cos(2 pi t/sqrt y) dy
          RHS1 = (1/I1(0)) sum_{c,m} (c/m^3) T_1(c) Phi((c/m)^2)
with T_2 = A_2 prod_{l not | c}(1-l^-2), T_1 = mu^2/phi prod_{l not | c}(1-l^-2), f_k Euler products.
Bumps: Phi(y) = exp(-1/(1-u^2)), u = (y - y0)/h, support [y0-h, y0+h].
RHS inner sums: sum_{(m,c)=1} psi(m/c) = sum_{d|c} mu(d) F(c/d), F(n) = sum_{m>=1} psi(m/n) computed
directly for n <= N0 and as n*int(psi) beyond (difference checked in the overlap).
"""
import sys, time
import numpy as np
from math import pi, sqrt, log, ceil, floor
from scipy.integrate import quad

ZETA2 = pi ** 2 / 6

def make_bump(y0, h):
    a, b = y0 - h, y0 + h
    def Phi(y):
        y = np.asarray(y, dtype=float)
        u = (y - y0) / h
        out = np.zeros_like(y)
        m = np.abs(u) < 1
        out[m] = np.exp(-1.0 / (1.0 - u[m] ** 2))
        return out
    return Phi, a, b

def sieve(C):
    spf = np.zeros(C + 1, dtype=np.int32)
    isp = np.ones(C + 1, dtype=bool); isp[:2] = False
    for p in range(2, int(C ** 0.5) + 1):
        if isp[p]:
            isp[p * p::p] = False
    primes = np.nonzero(isp)[0]
    return primes

def arith_arrays(C, primes):
    """T2, T1, phi, mu, G*phi (all exact-ish floats) up to C via multiplicative sieve"""
    T2 = np.ones(C + 1); T1 = np.ones(C + 1); PHI = np.arange(C + 1, dtype=float); MU = np.ones(C + 1)
    for l in primes:
        l = int(l)
        inv = 1.0 / (1.0 - 1.0 / (l * l))
        if l == 2:
            T2[2::2] *= 1.0 * inv          # A2(2)=1
            T2[4::4] *= -2.0               # A2(4) = -2 = A2(2) * (-2)
            T2[8::8] *= 0.0                # A2(8) = 0
        else:
            chi = 1 if l % 4 == 1 else -1
            T2[l::l] *= (1 + chi * l) / (l - 1) * inv
            if l * l <= C:
                T2[l * l::l * l] *= 0.0
        T1[l::l] *= 1.0 / (l - 1) * inv
        if l * l <= C:
            T1[l * l::l * l] *= 0.0
            MU[l * l::l * l] = 0.0
        MU[l::l] *= -1.0
        PHI[l::l] *= (1.0 - 1.0 / l)
    T2 /= ZETA2; T1 /= ZETA2     # prod_{l not| c}(1-l^-2) = (1/zeta2) prod_{l | c} (1-l^-2)^-1
    T2[0] = T1[0] = 0.0; MU[0] = 0.0
    return T2, T1, PHI, MU

def f_arrays(T, primes):
    """f_2(t), f_1(t) for 0 <= t <= T via local factors; C_odd from primes up to len(primes) range."""
    P = primes[primes > 2].astype(float)
    chi = np.where(primes[primes > 2] % 4 == 1, 1.0, -1.0)
    E0 = (1 - (1 + chi) / (P * (P - 1))) / (1 - 1 / P ** 2)
    C_odd = float(np.exp(np.sum(np.log(E0))))
    t = np.arange(T + 1)
    f2 = np.full(T + 1, C_odd)
    v2 = np.zeros(T + 1, dtype=int)
    tt = t.copy(); tt[0] = 0
    f2[1::2] *= 2.0 / 3.0
    f2[2::4] *= 5.0 / 3.0
    # 4|t : factor 1
    ARTIN = float(np.exp(np.sum(np.log(1 - 1 / (primes.astype(float) * (primes - 1))))))
    f1 = np.full(T + 1, ZETA2 * ARTIN)
    f1[2::2] *= 2.0   # l=2 divides t: replace (4-2-1)/(4-2)=1/2 by 1
    for l in primes[(primes > 2) & (primes <= T)]:
        l = int(l); c = 1 if l % 4 == 1 else -1
        f2[l::l] *= (l / (l - c)) / ((1 - (1 + c) / (l * (l - 1))) / (1 - 1 / l ** 2))
        f1[l::l] *= (l * l - l) / (l * l - l - 1)
    f2[0] = pi / 4
    f1[0] = ZETA2
    return f2, f1, C_odd, ARTIN

def I_values(psi, xa, xb, T, ngrid=2 ** 20):
    """I(t) = 2 int psi(x) cos(2 pi t x) dx for t=0..T, by FFT trapezoid on a period-L grid (spectrally accurate)."""
    L = float(ceil(xb + 0.5))
    x = np.arange(ngrid) * (L / ngrid)
    vals = np.zeros(ngrid)
    m = (x > xa) & (x < xb)
    vals[m] = psi(x[m])
    F = np.fft.fft(vals) * (L / ngrid)      # F[k] = int psi(x) e^{-2 pi i k x / L} dx
    k = (np.arange(T + 1) * L).astype(int)  # integer t <-> k = t L
    return 2 * F[k].real

def F_direct(psi, xa, xb, N0):
    """F(n) = sum_{m>=1} psi(m/n), n = 1..N0, direct summation"""
    F = np.zeros(N0 + 1)
    for n in range(1, N0 + 1):
        m0 = int(floor(xa * n)) + 1; m1 = int(ceil(xb * n)) - 1
        if m1 >= m0:
            ms = np.arange(m0, m1 + 1)
            F[n] = np.sum(psi(ms / n))
    return F

def mobius_convolve(F, MU, C):
    inner = np.zeros(C + 1)
    sq = np.nonzero(MU[1:C + 1])[0] + 1
    for d in sq:
        inner[d::d] += MU[d] * F[1:C // d + 1]
    return inner

if __name__ == "__main__":
    which = sys.argv[1]
    if which == "A":
        Phi, a, b = make_bump(9.0, 1.0)
    elif which == "B":
        Phi, a, b = make_bump(1.05, 0.45)
    else:
        y0, h = map(float, which.split(":")); Phi, a, b = make_bump(y0, h)
    Cmax = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10 ** 7
    xa, xb = 1 / sqrt(b), 1 / sqrt(a)
    psi2 = lambda x: Phi(x ** -2.0) * x ** -2.0
    psi1 = lambda x: Phi(x ** -2.0) * x ** -3.0
    t0 = time.time()
    primes = sieve(max(Cmax, 2 * 10 ** 6))
    T = 60000
    f2, f1, C_odd, ARTIN = f_arrays(T, primes)
    I2 = I_values(psi2, xa, xb, T); I1 = I_values(psi1, xa, xb, T)
    # cross-check I(t) against adaptive quadrature at a few t
    chk = []
    for tq in [0, 1, 7, 40]:
        q = 2 * quad(lambda x: float(psi2(np.array([x]))[0]) * np.cos(2 * pi * tq * x), xa, xb, limit=400, epsabs=1e-14)[0]
        chk.append(abs(q - I2[tq]))
    I0_direct = quad(lambda y: float(Phi(np.array([y]))[0]) * y ** -0.5, a, b, epsabs=1e-14)[0]
    print(f"bump on [{a},{b}]: I(0) = {I2[0]:.12f} (direct y-integral {I0_direct:.12f}); I1(0) = {I1[0]:.12f}; "
          f"max|I_fft - I_quad| at t=0,1,7,40: {max(chk):.1e}")
    print(f"  tail: max|I(t)| for t in [T/2,T] = {np.max(np.abs(I2[T // 2:])):.1e}; C_odd = {C_odd:.12f}, Artin = {ARTIN:.10f}")
    tw = np.r_[1.0, 2.0 * np.ones(T)]      # t and -t
    LHS2 = np.sum(tw * f2 * I2) / (2 * ZETA2 * I2[0])
    LHS1 = np.sum(tw * f1 * I1) / (2 * ZETA2 * I1[0])
    print(f"  LHS squares (t-series) = {LHS2:.10f}    LHS primes (t-series) = {LHS1:.10f}   [{time.time() - t0:.0f}s]")

    # RHS, c-ordered
    T2, T1, PHI, MU = arith_arrays(Cmax, primes[primes <= Cmax])
    N0 = 20000
    Fd2 = F_direct(psi2, xa, xb, N0); Fd1 = F_direct(psi1, xa, xb, N0)
    J2 = I2[0] / 2; J1 = I1[0] / 2        # int psi
    n = np.arange(N0 + 1)
    dev2 = np.max(np.abs(Fd2[N0 // 2:] - n[N0 // 2:] * J2)); dev1 = np.max(np.abs(Fd1[N0 // 2:] - n[N0 // 2:] * J1))
    print(f"  F(n) - n*int(psi) for n in [N0/2,N0]: squares {dev2:.1e}, primes {dev1:.1e}")
    F2 = np.r_[Fd2, np.arange(N0 + 1, Cmax + 1) * J2]
    F1 = np.r_[Fd1, np.arange(N0 + 1, Cmax + 1) * J1]
    inner2 = mobius_convolve(F2, MU, Cmax); inner1 = mobius_convolve(F1, MU, Cmax)
    c = np.arange(Cmax + 1, dtype=float); c[0] = 1
    blk2 = T2 * inner2 / c ** 2; blk1 = T1 * inner1 / c ** 2
    S2 = np.cumsum(blk2) / I2[0]; S1 = np.cumsum(blk1) / I1[0]
    Gphi = ZETA2 * T2 / c ** 2 * PHI; Gphi[0] = 0
    P0 = np.cumsum(Gphi)
    print(f"  RHS, c-ordered partial sums (squares: raw, and with the explicit t=0 piece P_C(0) replaced by pi/4):")
    for C in [10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7]:
        if C > Cmax: break
        corr = S2[C] + (pi / 4 - P0[C]) / (2 * ZETA2)
        print(f"    C={C:9d}: squares S_C = {S2[C]:+.10f}  corrected = {corr:+.10f}   |  primes S_C = {S1[C]:+.10f}")
    print(f"  sum_c |c-block| up to C (squares) = {np.sum(np.abs(blk2[1:Cmax + 1])) / abs(I2[0]):.3f} "
          f"(grows ~log C: up to C/10: {np.sum(np.abs(blk2[1:Cmax // 10 + 1])) / abs(I2[0]):.3f})")
    # prime-like prediction for squares (A_1 masses with the y^-1/2 density) -- the universality comparison
    S2_primelike = np.cumsum(T1 * inner2 / c ** 2) / I2[0]
    print(f"  prime-like prediction for squares (T_1 masses, y^-1/2 density): {S2_primelike[Cmax]:+.10f}")

    # m-ordered partial sums (squares and primes), direct, for the ordering question
    Mmax = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
    accum2 = 0.0; accum1 = 0.0; out = {}
    for m in range(1, Mmax + 1):
        c0 = int(floor(m / xb)) + 1; c1 = int(ceil(m / xa)) - 1
        if c1 > Cmax:
            print("  (m-ordering stopped: c exceeds Cmax)"); break
        if c1 < c0: continue
        cs = np.arange(c0, c1 + 1)
        cs = cs[np.gcd(cs, m) == 1]
        x = m / cs
        accum2 += np.sum(T2[cs] * psi2(x) / cs ** 2)
        accum1 += np.sum(T1[cs] * psi1(x) / cs ** 2)
        if m in (10, 100, 1000, 3000, 10000, 20000, 30000, 50000):
            out[m] = (accum2 / I2[0], accum1 / I1[0])
    for m, (u, v) in out.items():
        print(f"    m-ordered, M={m:6d}: squares {u:+.10f}   primes {v:+.10f}")
    print(f"  done [{time.time() - t0:.0f}s]")
