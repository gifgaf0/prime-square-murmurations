#!/usr/bin/env python3
"""Extra probes for the audit of second_moment_lemma.md.
Reuses the definitions from the uploaded script (imported by path, not by cwd)."""
import importlib.util, sys
from math import gcd
spec = importlib.util.spec_from_file_location("smc", "second_moment_check.py")
# the uploaded script runs its checks at import; silence that by executing only the defs
src = open("second_moment_check.py").read().split("ok = True")[0]
ns = {}
exec(compile(src, "smc_defs", "exec"), ns)
Nq, W, a, S2, phi, tau, factor, c_of = (ns[k] for k in ["Nq","W","a","S2","phi","tau","factor","c_of"])

ok = True
# (A) the bound the note actually derives in 4(c): W(2^j) <= 128 (j-2) phi(2^j) for j>=3, t = 2u, u odd
#     and the exact values W(2)=1, W(4)=8 for 2||t
for j in range(1, 10):
    q = 2**j
    for t in range(2, min(4*q, 400)+1, 4):   # t = 2 mod 4
        w = W(q, t)
        if j >= 3 and w > 128*(j-2)*phi(q):
            ok = False; print("FAIL sharper 2-adic", j, t, w, 128*(j-2)*phi(q))
        if j == 1 and w != 1: ok = False; print("FAIL W(2)", t, w)
        if j == 2 and w != 8: ok = False; print("FAIL W(4)", t, w)
print("(A) sharper 2-adic bound and W(2)=1, W(4)=8 for 2||t:", "ok" if ok else "FAIL")

# (B) actual W(2^j)/phi(2^j) for 2||t, to see how much slack 128(j-2) has
for j in range(3, 10):
    q = 2**j
    mx = max(W(q, t) for t in range(2, min(4*q, 400)+1, 4))
    print(f"   j={j}: max W(2^j)/phi(2^j) = {mx/phi(q):.3f}   (note's bound 128(j-2) = {128*(j-2)})")

# (C) the odd-l intermediate bound actually proved: W(l^j) <= 4(phi(l^j) + 2 j l^j); ratio to phi
for l in [3,5,7]:
    for j in range(1,5):
        q = l**j
        if q > 2500: continue
        mx = max(W(q,t) for t in range(0, min(2*q,400)+1) if t % l)
        print(f"   l={l} j={j}: max W/phi (l∤t) = {mx/phi(q):.3f}   bound 4(1+2j l^j/phi) = {4*(1+2*j*q/phi(q)):.2f}")

# (D) multiplicativity of N_q itself (Lemma 3(3)) with even factors, for ALL D mod 4q, not just D = t^2-4b^2
bad = 0
for q1, q2 in [(3,4),(5,8),(9,16),(7,2),(3,32)]:
    q = q1*q2
    for D in range(4*q):
        if Nq(q, D) != Nq(q1, D)*Nq(q2, D): bad += 1
print("(D) N_q multiplicative with even factor, all D mod 4q:", "ok" if bad == 0 else f"{bad} failures")

# (E) where is the max of S2/(phi tau^2) attained?  Exclude n=1, and report by omega(n)
rows = []
for n in list(range(2, 200)) + [210,216,240,256,360,420,480,512,720,840,900,960,1024]:
    for t in range(0, 30):
        rows.append((S2(n,t)/(phi(n)*tau(n)**2), n, t))
rows.sort(reverse=True)
print("(E) top S2/(phi tau^2) for n>=2:", [(round(r,3), n, t) for r,n,t in rows[:6]])
print("    S2(1,t)/(phi(1) tau(1)^2) =", S2(1,5), " <- this is the 1.0 in the log")
print("ALL EXTRA OK" if ok and bad == 0 else "EXTRA FAILURES ABOVE")
