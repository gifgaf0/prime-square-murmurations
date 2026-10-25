# sensitivity of the [8,10] value to the bump shape (t-series side, which equals Theorem B's RHS)
import numpy as np
from math import pi, sqrt
from s5_theoremB import sieve, f_arrays, I_values
ZETA2 = pi**2/6
primes = sieve(2*10**6)
T = 60000
f2, f1, _, _ = f_arrays(T, primes)
tw = np.r_[1.0, 2.0*np.ones(T)]
shapes = {
 "exp(-1/(1-u^2)), u=y-9 (standard)": lambda y: np.where(np.abs(y-9)<1, np.exp(-1/np.maximum(1-(y-9)**2,1e-300)), 0.0),
 "exp(-1/(1-u^2)^2)":                 lambda y: np.where(np.abs(y-9)<1, np.exp(-1/np.maximum(1-(y-9)**2,1e-300)**2), 0.0),
 "exp(-1/(1-v^2)), v=(sqrt y-3)/((sqrt10-sqrt8)/2) shifted to [sqrt8,sqrt10]":
     lambda y: (lambda v: np.where(np.abs(v)<1, np.exp(-1/np.maximum(1-v**2,1e-300)), 0.0))((np.sqrt(y)-(sqrt(8)+sqrt(10))/2)/((sqrt(10)-sqrt(8))/2)),
}
for name, Phi in shapes.items():
    psi2 = lambda x: Phi(x**-2.0)*x**-2.0
    psi1 = lambda x: Phi(x**-2.0)*x**-3.0
    xa, xb = 1/sqrt(10), 1/sqrt(8)
    I2 = I_values(psi2, xa, xb, T); I1 = I_values(psi1, xa, xb, T)
    print(f"{name:75s} squares {np.sum(tw*f2*I2)/(2*ZETA2*I2[0]):+.4f}   primes {np.sum(tw*f1*I1)/(2*ZETA2*I1[0]):+.4f}")
