from fractions import Fraction as F
# exponent of K as dict over monomials: '1', 'th', 'e', 'th*e', 'e2'
def add(*fs):
    r = {}
    for f in fs:
        for k, v in f.items(): r[k] = r.get(k, 0) + v
    return {k: v for k, v in r.items() if v != 0}
def sc(c, f): return {k: c * v for k, v in f.items()}
def mul_e(f):  # multiply a linear form (no e-terms beyond e) by e
    m = {'1': 'e', 'th': 'th*e', 'e': 'e2'}
    return {m[k]: v for k, v in f.items()}
def show(f): return " + ".join(f"{v}*{k}" for k, v in sorted(f.items()))
one = {'1': F(1)}; th = {'th': F(1)}; e = {'e': F(1)}
T1 = add(one, sc(-1, th), e)
M = add(sc(2, one), sc(-2, th), sc(8, e))
it1 = add(T1, sc(-1, one), sc(2, e))                                  # T1 K^{-1+2e}
it2 = add(T1, sc(2, e), one, sc(3, T1), sc(-3, one))                    # T1 * K^{2e} * K T1^3 / K^3
it3 = add(T1, sc(2, e), sc(F(-1, 2), M), mul_e(M))                     # T1 K^{2e} M^{-1/2+e}
it4 = add({'1': F(1, 2)}, M, mul_e(M), sc(2, T1), sc(-1, one))          # K^{1/2} M^{1+e} T1^2 / K
for name, f in (("item1 side term", it1), ("item2", it2), ("item3", it3), ("item4", it4)):
    print(f"{name}: exponent = {show(f)}")
def ev(f, t, eps): return float(sum(v * {'1': 1, 'th': t, 'e': eps, 'th*e': t * eps, 'e2': eps * eps}[k] for k, v in f.items()))
for t in (F(7, 8), F(9, 10), F(15, 16)):
    for eps in (F(1, 100), F(1, 1000)):
        print(f"theta={t}, eps={eps}: " + ", ".join(f"{n}={ev(f, t, eps):+.4f}" for n, f in (("it1", it1), ("it2", it2), ("it3", it3), ("it4", it4))) +
              f", M-exponent={ev(M, t, eps):.4f} (Lemma 7 needs <= 1/2)")
