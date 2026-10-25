"""
Item 3a: A_2(c) = (1/phi(c)) sum_{a unit} S(a^2,1;c) and A_1(c) = (1/phi(c)) sum_a S(a,1;c)
from the definition S(m,n;c) = sum_{x unit} e((m x + n xbar)/c), compared with
  A_2 multiplicative, A_2(l) = (1+chi(l) l)/(l-1), A_2(l^j)=0 (j>=2, l odd), A_2(2)=1, A_2(4)=-2, A_2(2^j)=0 (j>=3)
  A_1 = mu^2/phi.
phi(c)*A_k(c) is an integer (Galois invariant algebraic integer); we compute it in floating point and round.
Two independent evaluations: (i) direct double loop for small c, (ii) FFT over the square histogram.
"""
import numpy as np
from math import gcd
from fractions import Fraction

def factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def chi4(l):
    return 0 if l % 2 == 0 else (1 if l % 4 == 1 else -1)

def A2_formula(c):
    r = Fraction(1)
    for l, e in factor(c).items():
        if l == 2:
            r *= {1: Fraction(1), 2: Fraction(-2)}.get(e, Fraction(0))
        else:
            r *= Fraction(1 + chi4(l) * l, l - 1) if e == 1 else Fraction(0)
    return r

def phi(c):
    r = c
    for l in factor(c):
        r = r // l * (l - 1)
    return r

def A1_formula(c):
    f = factor(c)
    if any(e > 1 for e in f.values()):
        return Fraction(0)
    return Fraction(1, phi(c))

def kl_sum_avg_fft(c, k):
    """returns sum_{a unit} S(a^k,1;c) as float complex via FFT"""
    U = np.array([u for u in range(c) if gcd(u, c) == 1], dtype=np.int64)
    if c == 1:
        return complex(1.0)
    inv = np.array([pow(int(u), -1, c) for u in U], dtype=np.int64)
    h = np.zeros(c)
    np.add.at(h, (U ** k) % c if k <= 2 else np.array([pow(int(u), k, c) for u in U]), 1.0)
    # w[x] = sum_s h[s] e(s x / c)
    w = np.fft.ifft(h) * c
    return complex(np.sum(np.exp(2j * np.pi * inv / c) * w[U]))

def kl_sum_avg_direct(c, k):
    U = [u for u in range(c) if gcd(u, c) == 1]
    tot = 0j
    for a in U:
        m = pow(a, k, c)
        for x in U:
            tot += np.exp(2j * np.pi * ((m * x + pow(x, -1, c) if c > 1 else 0) % c) / c)
    return tot

if __name__ == "__main__":
    # small c: direct double loop vs FFT vs formula
    worst_direct = 0.0
    for c in range(1, 61):
        d = kl_sum_avg_direct(c, 2); f = kl_sum_avg_fft(c, 2)
        worst_direct = max(worst_direct, abs(d - f))
    print("direct vs FFT, c<=60, k=2: max |diff| =", worst_direct)
    # all c up to CMAX with FFT
    CMAX = 3000
    bad2 = []; bad1 = []; worst_frac = 0.0; worst_im = 0.0
    vals = {}
    for c in range(1, CMAX + 1):
        p = phi(c)
        z2 = kl_sum_avg_fft(c, 2)
        z1 = kl_sum_avg_fft(c, 1)
        worst_im = max(worst_im, abs(z2.imag), abs(z1.imag))
        n2 = round(z2.real); n1 = round(z1.real)
        worst_frac = max(worst_frac, abs(z2.real - n2), abs(z1.real - n1))
        A2 = Fraction(n2, p); A1 = Fraction(n1, p)
        vals[c] = A2
        if A2 != A2_formula(c):
            bad2.append((c, A2, A2_formula(c)))
        if A1 != A1_formula(c):
            bad1.append((c, A1, A1_formula(c)))
    print(f"c <= {CMAX}: worst |Im| = {worst_im:.2e}, worst distance to integer = {worst_frac:.2e}")
    print("A_2 mismatches vs multiplicative formula:", len(bad2), bad2[:10])
    print("A_1 mismatches vs mu^2/phi:", len(bad1), bad1[:10])
    print("A_2 at 1,2,3,4,5,7,8,9,12,13,15,16,25,27,32,49,64,81,125,128,243,256:")
    print({c: str(vals[c]) for c in [1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 15, 16, 25, 27, 32, 49, 64, 81, 125, 128, 243, 256]})
    # a few large prime powers / composites beyond CMAX
    for c in [3 ** 8, 5 ** 5, 7 ** 4, 2 ** 13, 2 ** 2 * 3 * 5 * 7 * 13, 4 * 11 * 13 * 17, 6561 * 4]:
        z = kl_sum_avg_fft(c, 2)
        print(f"c={c}: phi*A2 = {z.real:.6f} (+{z.imag:.1e}i), formula phi*A2 = {A2_formula(c) * phi(c)}")
