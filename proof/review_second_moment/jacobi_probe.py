# For prime p not dividing 2t and chi = psi^2 even non-principal, claim:
#   a^(chi) = conj(psi)(t^2/4) * ( J(chi2, conj psi) + chi2(-1) conj(J(chi2, conj psi)) ) / (p-1),
# so |a^(chi)| = 2|Re J| /(p-1)  (p=1 mod 4)  or  2|Im J|/(p-1)  (p=3 mod 4), |J| = sqrt p,
# and sum_chi |a^(chi)| ~ (2/pi) sqrt p if the Jacobi angles equidistribute.
import numpy as np, cmath
from math import gcd
def prim_root(p):
    ph=p-1; fs=[q for q in range(2,ph+1) if ph%q==0 and all(q%r for r in range(2,int(q**.5)+1))]
    return next(g for g in range(2,p) if all(pow(g,ph//q,p)!=1 for q in fs))
for p,t in [(157,8),(151,11),(139,14),(131,27),(101,37),(97,23)]:
    g=prim_root(p); log={pow(g,k,p):k for k in range(p-1)}
    leg=lambda x: 0 if x%p==0 else (1 if pow(x%p,(p-1)//2,p)==1 else -1)
    a=np.array([leg(t*t-4*b*b) for b in range(1,p)])            # a(b) = N_p - N_1 = Legendre symbol
    inv4=pow(4,-1,p); c=(t*t*inv4)%p
    tot_num=0.0; tot_formula=0.0; maxdiff=0.0
    for m in range(p-1):                                            # chi_m(b) = e(m log b/(p-1))
        chi=np.exp(2j*np.pi*m*np.array([log[b] for b in range(1,p)])/(p-1))
        ah=(a*np.conj(chi)).sum()/(p-1)
        tot_num+=abs(ah)
        if m%2==1 or m==0: 
            assert abs(ah)<1e-9 if m%2==1 else True; continue
        # psi with psi^2 = chi_m : psi = chi_{m/2}
        k=m//2
        psi=lambda x: cmath.exp(2j*np.pi*k*log[x%p]/(p-1))
        J=sum(leg(1-w)*psi(w).conjugate() for w in range(2,p))     # J(chi2, conj psi) = sum_w chi2(1-w) conj psi(w)
        formula=psi(c).conjugate()*(J+leg(-1)*J.conjugate())/(p-1)
        maxdiff=max(maxdiff,abs(formula-ah)); tot_formula+=abs(formula)
        assert abs(abs(J)-p**.5)<1e-6
    print("p=%d t=%d: sum|a^| = %.4f, formula sum = %.4f, max |diff| = %.1e, (2/pi)sqrt p = %.4f" % (p,t,tot_num,tot_formula,maxdiff,2/np.pi*p**.5))

# ---- full sweep matching the paper's numerics row: the 23 primes 11 <= p <= 103, all 1 <= t < p ----
# For every even non-principal chi = psi^2: |formula - a^(chi)| < 1e-9; every odd chi: a^(chi) = 0;
# sum_b a(b)^2 = p-3; and the lower bound sum_chi |a^(chi)| >= (p-3)/(2 sqrt p).
primes=[p for p in range(11,104) if all(p%q for q in range(2,int(p**.5)+1))]
assert len(primes)==23
worst=0.0; ok=True; ratios=[]
for p in primes:
    g=prim_root(p); log={pow(g,k,p):k for k in range(p-1)}
    leg=lambda x: 0 if x%p==0 else (1 if pow(x%p,(p-1)//2,p)==1 else -1)
    L=np.array([log[b] for b in range(1,p)]); inv4=pow(4,-1,p)
    # Jacobi sums J(chi2, conj psi_k) for every k, computed once
    Jk={k: sum(leg(1-w)*cmath.exp(-2j*np.pi*k*log[w]/(p-1)) for w in range(2,p)) for k in range(p-1)}
    for t in range(1,p):
        a=np.array([leg(t*t-4*b*b) for b in range(1,p)])
        if (a*a).sum()!=p-3: ok=False; print("S2 != p-3",p,t)
        c=(t*t*inv4)%p; S1=0.0
        for m in range(p-1):
            chi=np.exp(2j*np.pi*m*L/(p-1)); ah=(a*np.conj(chi)).sum()/(p-1); S1+=abs(ah)
            if m%2==1:
                if abs(ah)>1e-9: ok=False; print("odd chi nonzero",p,t,m)
            elif m>0:
                k=m//2; J=Jk[k]; psi_c=cmath.exp(2j*np.pi*k*log[c]/(p-1))
                f=psi_c.conjugate()*(J+leg(-1)*J.conjugate())/(p-1)
                worst=max(worst,abs(f-ah))
        if S1<(p-3)/(2*p**.5)-1e-9: ok=False; print("lower bound fails",p,t)
        ratios.append(S1/p**.5)
print("sweep 23 primes 11..103, all 1<=t<p: %s; max |formula - a^(chi)| = %.1e; sum|a^|/sqrt(p) in [%.3f, %.3f]"
      % ("OK" if ok else "FAILURES", worst, min(ratios), max(ratios)))
