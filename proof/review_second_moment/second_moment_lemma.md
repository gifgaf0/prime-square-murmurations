# Second-moment lemma for $a_{t^2-4b^2}(n)$ — for audit

**Status:** audited 2026-11-03 (`second_moment_audit.md`): passes; findings F1–F3, F5 of the audit are incorporated below (rev 1). Applied to the paper in `claude/murmurations/murmurations_squares_10.tex` (changelog: `v10_changelog.md`). This is the one new ingredient needed for the character-expansion revision of Lemma 7 (`lem:averaged`), which widens Theorem A to $\theta>5/6$ and Proposition `prop:zf` to $1-\theta<2a^2/(1+4a)$. Section 6 shows where it plugs in; Section 7 lists what to audit; Section 8 is the brute-force check.

Lemma numbers refer to `murmurations_squares (9).tex`: Lemma 3 = `lem:zagier`, Lemma 5 = `lem:pnt-ap`, Lemma 6 = `lem:local`, Lemma 7 = `lem:averaged`.

## 0. Notation (as in the paper)

- $N_q(\Delta)=\#\{x \bmod 2q:\ x^2\equiv\Delta \pmod{4q}\}$. Depends only on $\Delta \bmod 4q$; multiplicative in $q$ (Lemma 3(3)).
- $a_\Delta(n)=\sum_{q\mid n}\lambda(n/q)\,N_q(\Delta)$, $\lambda$ = Liouville. Depends only on $\Delta \bmod 4n$.
- Fix $n\ge1$, $t\in\mathbb Z$. For $b\in(\mathbb Z/n\mathbb Z)^\times$ put $\Delta_b=t^2-4b^2$. This is well defined mod $4n$ and $\equiv t^2\equiv 0,1 \pmod 4$, so $a(b):=a_{\Delta_b}(n)$ is a well-defined function on $(\mathbb Z/n\mathbb Z)^\times$.
- $\delta_t(n)=\varphi(n)^{-1}\sum_b a(b)$ (the paper's definition of the local density).
- $r_m(D)=\#\{x \bmod m:\ x^2\equiv D \pmod m\}$.
- $\chi=\chi_{-4}$.

## 1. Statement

**Lemma S (second moment).** Uniformly in $t\in\mathbb Z$ (including $t=0$) and $n\ge1$,
$$
S_2(n,t):=\sum_{b\in(\mathbb Z/n\mathbb Z)^\times}\big|a_{t^2-4b^2}(n)\big|^2
\;\le\;\tau(n)^2\,\varphi(n)\,\max_{q\mid n}c(q),
\qquad c(q)=\prod_{\ell^j\parallel q}128\,j\;\le\;128^{\,\omega(q)}\tau(q),
$$
so $S_2(n,t)\ll_\varepsilon n^{1+\varepsilon}$.

**Corollary (character coefficients).** For $\chi$ a Dirichlet character mod $n$ put $\hat a(\chi)=\varphi(n)^{-1}\sum_b a(b)\overline{\chi}(b)$. Then $\hat a(\chi_0)=\delta_t(n)$ and
$$
\sum_{\chi \bmod n}|\hat a(\chi)|\;\le\;S_2(n,t)^{1/2}\;\ll_\varepsilon\; n^{1/2+\varepsilon}.
$$

## 2. Reduction to prime powers

**Step 1 (Cauchy–Schwarz over divisors).** Since $|\lambda|=1$,
$|a(b)|^2\le\tau(n)\sum_{q\mid n}N_q(\Delta_b)^2$, hence
$$
S_2(n,t)\le\tau(n)\sum_{q\mid n}\ \sum_{b\in(\mathbb Z/n\mathbb Z)^\times}N_q(\Delta_b)^2 .
$$

**Step 2 (descend from $n$ to $q$).** $N_q(\Delta_b)$ depends on $\Delta_b \bmod 4q$, and $4b^2 \bmod 4q$ depends only on $b \bmod q$. The reduction $(\mathbb Z/n\mathbb Z)^\times\to(\mathbb Z/q\mathbb Z)^\times$ is surjective with every fibre of size $\varphi(n)/\varphi(q)$. So the inner sum equals $\dfrac{\varphi(n)}{\varphi(q)}\,W(q)$ with
$$
W(q)=W_t(q):=\sum_{b\in(\mathbb Z/q\mathbb Z)^\times}N_q(t^2-4b^2)^2 .
$$

**Step 3 (multiplicativity).** For coprime $q_1,q_2$, $N_{q_1q_2}=N_{q_1}N_{q_2}$ (Lemma 3(3)) and $b\mapsto(b \bmod q_1,\ b \bmod q_2)$ is a bijection of unit groups, so $W(q_1q_2)=W(q_1)W(q_2)$. Hence $W(q)=\prod_{\ell^j\parallel q}W(\ell^j)$.

**Step 4 (what remains).** It suffices to prove, for every prime $\ell$ and $j\ge1$,
$$
W(\ell^j)\le 128\,j\,\varphi(\ell^j). \tag{$\ast$}
$$
Then $W(q)\le c(q)\varphi(q)$, so $S_2\le\tau(n)\varphi(n)\sum_{q\mid n}c(q)\le\tau(n)^2\varphi(n)\max_{q\mid n}c(q)$, and $128^{\omega(q)}\tau(q)\ll_\varepsilon q^\varepsilon$.

The constant 128 is not meant to be good; see Section 8.

## 3. Odd $\ell$

**(a)** The congruence $x^2\equiv\Delta \pmod 4$ fixes $x \bmod 2$, so $N_{\ell^j}(\Delta)=r_{\ell^j}(\Delta)$ (this is the same reduction as in the proof of Lemma 6).

**(b) Pointwise bound.** Let $m=\min(v_\ell(\Delta),j)$. Then
$$ r_{\ell^j}(\Delta)^2\le 4\,\ell^{m}. $$
*Proof.* If $\ell^j\mid\Delta$: $x^2\equiv0 \pmod{\ell^j}$ iff $\ell^{\lceil j/2\rceil}\mid x$, so $r=\ell^{\lfloor j/2\rfloor}$ and $r^2\le\ell^j=\ell^m$. If $v=v_\ell(\Delta)<j$, write $\Delta=\ell^v u$ with $\ell\nmid u$. For any solution $x$, $v_\ell(x^2)=v$ (if $v_\ell(x^2)\neq v$ then $v_\ell(x^2-\Delta)=\min(v_\ell(x^2),v)\le v<j$, contradiction). So $v$ is even — if $v$ is odd, $r=0$. If $v$ is even, $x=\ell^{v/2}y$ with $y$ a unit and $y^2\equiv u \pmod{\ell^{j-v}}$. By Hensel there are $1+\big(\tfrac u\ell\big)\le2$ such $y \bmod \ell^{j-v}$, and each has $\ell^{v/2}$ lifts to $y \bmod \ell^{\,j-v/2}$ (which is what determines $x \bmod \ell^j$). So $r=\big(1+(\tfrac u\ell)\big)\ell^{v/2}\le2\ell^{v/2}$. $\square$

**(c) Counting $b$.** For $1\le m\le j$ put $B_m=\#\{b\in(\mathbb Z/\ell^j\mathbb Z)^\times:\ \ell^m\mid t^2-4b^2\}$.

*Case $\ell\nmid t$.* $\ell^m\mid(t-2b)(t+2b)$, and $\ell$ cannot divide both factors (their sum is $2t$). So $2b\equiv t$ or $2b\equiv-t \pmod{\ell^m}$: two residue classes mod $\ell^m$ (distinct, since $\ell\nmid t$), each with $\ell^{j-m}$ lifts mod $\ell^j$, all of them units. Hence $B_m=2\ell^{j-m}$.

*Case $\ell\mid t$.* $t^2-4b^2\equiv-4b^2\not\equiv0 \pmod\ell$, so $v_\ell(\Delta_b)=0$ for every $b$ and $B_m=0$ for $m\ge1$. Moreover, by (b), $r_{\ell^j}(\Delta_b)=1+\big(\tfrac{-4b^2}{\ell}\big)=1+\chi(\ell)$ for every unit $b$ — consistent with $\nu_t(\ell^i)=1+\chi(\ell)$ in Lemma 6.

**(d) Assemble.** With $m(b)=\min(v_\ell(\Delta_b),j)$ and $\#\{b: m(b)=m\}\le B_m$ for $m\ge1$,
$$
W(\ell^j)\le4\sum_b\ell^{m(b)}\le4\Big(\varphi(\ell^j)+\sum_{m=1}^{j}\ell^mB_m\Big).
$$
If $\ell\nmid t$: $\le4\big(\varphi(\ell^j)+2j\,\ell^j\big)\le4(2j+1)\ell^j\le6(2j+1)\varphi(\ell^j)\le18\,j\,\varphi(\ell^j)$, using $\ell^j\le\tfrac32\varphi(\ell^j)$ for $\ell\ge3$.
If $\ell\mid t$: $W(\ell^j)=(1+\chi(\ell))^2\varphi(\ell^j)\le4\varphi(\ell^j)$.
Both satisfy $(\ast)$.

## 4. $\ell=2$

Here $N_{2^j}(\Delta)=\#\{x \bmod 2^{j+1}:\ x^2\equiv\Delta \pmod{2^{j+2}}\}$ and $b$ is odd. Three cases by $t \bmod 4$, matching the three rows of the table in Lemma 6. They are exhaustive, and $t=0$ falls under (b).

**(a) $t$ odd.** $\Delta_b\equiv1-4\equiv5 \pmod 8$. Any solution $x$ is odd, odd squares are $\equiv1 \pmod 8$, and $j+2\ge3$, so there is no solution. $N_{2^j}(\Delta_b)=0$ for all $b$, $W(2^j)=0$.

**(b) $4\mid t$.** $\Delta_b\equiv0 \pmod 4$, so $x=2w$ with $w \bmod 2^j$ and $w^2\equiv t^2/4-b^2 \pmod{2^j}$. Since $4\mid t^2/4$ and $b^2\equiv1 \pmod 8$, the right side is $\equiv3 \pmod 4$. For $j\ge2$ this has no solution: $W(2^j)=0$. For $j=1$: $w$ odd, one solution, $N_2(\Delta_b)=1$ and $W(2)=\varphi(2)=1$.

**(c) $t=2u$, $u$ odd.** $x=2w$ and $w^2\equiv u^2-b^2 \pmod{2^j}$, so $N_{2^j}(\Delta_b)=r_{2^j}(D_b)$ with $D_b=u^2-b^2$. As $u,b$ are odd, $D_b\equiv0 \pmod 8$: $v:=v_2(D_b)\ge3$.

*Pointwise bound.* With $m=\min(v,j)$: $r_{2^j}(D)^2\le16\cdot2^{m}$.
*Proof.* If $2^j\mid D$, $r=2^{\lfloor j/2\rfloor}$ and $r^2\le2^j$. If $v<j$: as in 3(b), $v$ must be even, $w=2^{v/2}y$ with $y$ odd and $y^2\equiv d \pmod{2^{j-v}}$, where $D=2^vd$. The number of odd $y \bmod 2^{j-v}$ with $y^2\equiv d$ is at most $4$ (it is $1$ for $j-v=1$; $\le2$ for $j-v=2$; and for $j-v\ge3$ it is $4$ if $d\equiv1 \pmod 8$ and $0$ otherwise). Each has $2^{v/2}$ lifts. So $r\le4\cdot2^{v/2}$. $\square$

*Counting.* For $3\le m\le j$ let $B_m=\#\{b \text{ odd mod }2^j:\ 2^m\mid u^2-b^2\}$. Since $(u-b)+(u+b)=2u$ has 2-adic valuation exactly $1$, one of $u-b$, $u+b$ has valuation exactly $1$ and the other has valuation $v-1$. So $2^m\mid D_b$ forces $b\equiv u$ or $b\equiv-u \pmod{2^{m-1}}$: two classes mod $2^{m-1}$ (disjoint, since $u\not\equiv-u \pmod 4$), each with $2^{\,j-m+1}$ lifts mod $2^j$. Hence $B_m\le2^{\,j-m+2}$.

*Assemble.* For $j\ge3$ every $b$ has $m(b)\ge3$, so
$$
W(2^j)\le16\sum_{m=3}^{j}2^mB_m\le16\sum_{m=3}^{j}2^{\,j+2}=(j-2)\,2^{\,j+6}=128\,(j-2)\,\varphi(2^j).
$$
For $j=1,2$: $2^j\mid D_b$ for all $b$, so $N=2^{\lfloor j/2\rfloor}$ and $W(2)=1$, $W(4)=8$. In every case $W(2^j)\le128\,j\,\varphi(2^j)$, which is $(\ast)$.

This completes the proof of Lemma S.

## 5. Proof of the Corollary

Plancherel on the finite abelian group $(\mathbb Z/n\mathbb Z)^\times$, with $\hat a(\chi)=\varphi(n)^{-1}\sum_ba(b)\overline\chi(b)$:
$\sum_\chi|\hat a(\chi)|^2=\varphi(n)^{-1}\sum_b|a(b)|^2$. Cauchy–Schwarz over the $\varphi(n)$ characters:
$$
\sum_\chi|\hat a(\chi)|\le\varphi(n)^{1/2}\Big(\sum_\chi|\hat a(\chi)|^2\Big)^{1/2}=\Big(\sum_b|a(b)|^2\Big)^{1/2}=S_2(n,t)^{1/2}.
$$
And $\hat a(\chi_0)=\varphi(n)^{-1}\sum_ba(b)=\delta_t(n)$ by the paper's definition of $\delta_t$. $\square$

## 6. Where it plugs in: the revised Lemma 7

Everything in the current proof of Lemma 7 stands except the sentence that splits the $p$-sum into classes $b \bmod n$ and bounds the errors by $\sum_b|a_{t^2-4b^2}(n)|$. Replace it by:

For $n<K^{1-\varepsilon}$ no prime $p\asymp K$ divides $n$, and $a_{\Delta_p}(n)=a(p \bmod n)$ with $a$ as in Section 0. Expanding $a=\sum_\chi\hat a(\chi)\chi$ on $(\mathbb Z/n\mathbb Z)^\times$,
$$
\sum_p(\log p)\,g(p)\,a_{t^2-4p^2}(n)=\sum_{\chi \bmod n}\hat a(\chi)\sum_p(\log p)\,g(p)\,\chi(p).
$$
- $\chi=\chi_0$: $\hat a(\chi_0)=\delta_t(n)$, and $\sum_{p\nmid n}(\log p)g(p)=\int g+O(V(g)K^{1/2}\log^2K)$ by Lemma 5 with $r=1$ (the excluded $p\mid n$ do not occur in the support of $g$).
- $\chi\neq\chi_0$: under GRH, $\psi(x,\chi)\ll x^{1/2}\log^2(nx)$ uniformly in the modulus (Davenport ch. 20). For imprimitive $\chi$ induced by $\chi^*$ mod $n^*$, $\psi(x,\chi)-\psi(x,\chi^*)\ll\omega(n)\log x$; prime powers $p^k$, $k\ge2$, contribute $O(x^{1/2})$. Partial summation gives $\sum_p(\log p)g(p)\chi(p)\ll V(g)K^{1/2}\log^2K$.

So the error for this $n$ is $\ll V(g)K^{1/2}\log^2K\sum_\chi|\hat a(\chi)|\ll V(g)K^{1/2}\log^2K\cdot n^{1/2+\varepsilon}$ by the Corollary. Summing over $n$ with weight $e^{-n/M}/n$: $\sum_n n^{-1/2+\varepsilon}e^{-n/M}\ll M^{1/2+\varepsilon}$. Hence

**Lemma 7′.** Under the hypotheses of Lemma 7, the error term is $O\big(V(g)\,K^{1/2}M^{1/2+\varepsilon}\log^2K\big)$ in place of $O\big(V(g)\,K^{1/2}M^{1+\varepsilon}\log^2K\big)$.

The hypothesis $|t|\le K$ in Lemma 7 is not needed: Lemma S is uniform in $t$, and (audit F5) the current proof of Lemma 7 never used it either — the tail $n\ge K^{1-\varepsilon}$ uses only $M\le K^{1/2}$ and the polynomial bound on $|a_\Delta(n)|$. It is dropped from the statement.

**Consequences.**
- Section `sec:thmA`, item 4: error $O(K^{1/2}M^{1/2+\varepsilon}T_1^2)$, i.e. $O(K^{3(1-\theta)-1/2+O(\varepsilon)})$ relative to the denominator with $M=K^{2(1-\theta)+8\varepsilon}$. The range becomes $3(1-\theta)<1/2$: $\theta>5/6$. Items 1, 2, 3, 5 are unchanged; the condition $M\le K^{1/2}$ holds since $2(1-\theta)<1/3$.
- Proposition `prop:zf`: the same character sums are bounded by $K^{\sigma_0}\log^2K$ from the explicit formula already used there, so item 4 becomes $O(K^{-a}M^{1/2+\varepsilon}T_1^2)$. Items 3 and 4 then need $(1-\theta)/a<\mu<2a-4(1-\theta)$, which is possible iff $(1-\theta)(1+4a)<2a^2$. For $a=1/2,\ 1/8,\ 1/12$: $\theta>5/6,\ 47/48,\ 95/96$. Lemma 7 also needs $M\le K^{1/2}$, i.e. $\mu\le1/2$. The new upper endpoint $2a-4(1-\theta)$ can exceed $1/2$ (it tends to $1$ for $a=1/2$, $\theta\to1$), so — unlike in the paper's current proof, where the upper endpoint was $a-2(1-\theta)<a\le 1/2$ — this is not automatic. What holds is that the lower endpoint is below $1/2$: under the existence condition, $(1-\theta)/a<2a/(1+4a)<1/2$. So a $\mu\le1/2$ in the interval exists, and that is the $\mu$ to take. (Audit F1.)

## 7. Audit points

1. **Step 2 descent.** The claim that $N_q(\Delta_b)$ depends only on $b \bmod q$ rests on $N_q$ depending on $\Delta \bmod 4q$ and $4b^2 \bmod 4q$ depending on $b \bmod q$. Check both against the definition of $N_q$ (modulus $4q$, $x \bmod 2q$).
2. **Multiplicativity with an even factor.** Step 3 uses $N_{q_1q_2}=N_{q_1}N_{q_2}$ when one of $q_1,q_2$ is even. *Resolved (audit F4):* for odd $q_1$, CRT identifies $x \bmod 2q_1q_2$ with $(x \bmod q_1,\ x \bmod 2q_2)$, and $x^2 \bmod 4q_2$ depends only on $x \bmod 2q_2$, so $N_{q_1q_2}(\Delta)=r_{q_1}(\Delta)\,N_{q_2}(\Delta)$; and $N_{q_1}(\Delta)=r_{q_1}(\Delta)\cdot[\Delta\equiv0,1\ (4)]$, with the bracket already enforced by $N_{q_2}$. So the identity holds for every $\Delta \bmod 4q$. This two-line argument is now in the paper's proof of Lemma 3(3), which previously read "definition and CRT".
3. **3(b):** the step "$v_\ell(x^2)=v$ for any solution" needs $v<j$; the case $\ell^j\mid\Delta$ is handled separately. Check that the two cases together cover $m=\min(v,j)$ correctly and that $r^2\le4\ell^m$ holds in both (in the $\ell^j\mid\Delta$ case the bound is $\ell^j$ with no factor 4 needed).
4. **4(c) parity argument.** Uses $u,b$ both odd so that $v_2(2u)=1$. Check the inference "one factor has valuation exactly 1, the other $v-1$", and that $m-1\le j$ so the residue class mod $2^{m-1}$ makes sense.
5. **4(c) count of odd square roots mod $2^k$:** at most 4, for every $k\ge1$ and every odd $d$. This is standard; verify the $k=1,2$ edge cases.
6. **Lossy steps** ($\#\{m(b)=m\}\le B_m$; $2j+1\le3j$; $\ell^j\le\tfrac32\varphi(\ell^j)$; the uniform 128) are all upper bounds and only need $c(q)\ll q^\varepsilon$. Nothing depends on the constant.
7. **Corollary normalisation.** $\hat a$ carries $\varphi(n)^{-1}$; the Plancherel identity and the Cauchy–Schwarz are written for that normalisation. Check that $\hat a(\chi_0)$ is exactly $\delta_t(n)$ as the paper defines it (average over units of $a_{t^2-4b^2}(n)$).
8. **Section 6.** The GRH bound for $\psi(x,\chi)$ must be uniform in the modulus $n\le K$ with the stated $\log^2(nx)$; the imprimitive and prime-power corrections; and that nothing else in the proof of Lemma 7 used $|t|\le K$. *Resolved (audit F5):* nothing did. In the paper this bound now lives in Lemma 5, restated per character, so that §2's "GRH enters in exactly two places" stays true.
9. **Prop. `prop:zf`.** Under $\mathrm{ZF}(\sigma_0)$ the non-principal character sums get $x^{\sigma_0}\log^2$ from the same explicit-formula bound the paper already derives for $\theta(x;r,b)$ — confirm that derivation is per-character (it is: it bounds $\sum|x^\rho/\rho|$ for each primitive $L(s,\chi)$) and not only for the averaged progression count.

## 8. Numerical check

`second_moment_check.py` computes $N_q$, $a_\Delta(n)$, $W(q)$ and $S_2(n,t)$ directly from the definitions (no formulas from this note) and tests:

1. $W(\ell^j)\le4(2j+1)\ell^j$ for $\ell\in\{3,5,7,11,13\}$, $\ell^j\le2500$, $0\le t\le\min(2\ell^j,400)$; and $W(\ell^j)\le4\varphi(\ell^j)$ when $\ell\mid t$.
2. $W(2^j)\le128\,j\,\varphi(2^j)$ for $j\le8$, $0\le t\le\min(2^{j+2},400)$; $W(2^j)=0$ for $t$ odd; $W(2^j)=0$ for $4\mid t$, $j\ge2$; $W(2)=1$ for $4\mid t$.
   2′. (Folded in from the audit's probe A.) The claims actually displayed in §4(c), for $t\equiv2 \pmod 4$: $W(2^j)\le128(j-2)\varphi(2^j)$ for $3\le j\le9$, and $W(2)=1$, $W(4)=8$.
3. $W(q_1q_2)=W(q_1)W(q_2)$ for $(q_1,q_2)\in\{(3,4),(5,8),(9,4),(7,25),(16,9),(3,5),(27,8)\}$, $0\le t<40$.
4. $S_2(n,t)\le\tau(n)^2\varphi(n)\max_{q\mid n}c(q)$ for all $n<200$ and $n\in\{210,216,240,256,360,420,480,512,720,840,900,960,1024\}$, $0\le t<30$.

Result (`second_moment_check.log`): all pass, about 5 s. For $n\ge2$ the largest observed value of $S_2(n,t)/(\varphi(n)\tau(n)^2)$ is $4/9$, at $n=4$, $t\equiv2 \pmod 4$ ($n=1$ gives the trivial ratio $1$, since $S_2(1,t)=N_1^2=1$; audit F2). So in the tested range $S_2(n,t)\le\varphi(n)\tau(n)^2$ and the factor $128^{\omega}$ in Lemma S is pure slack. The audit's probes B–C show $\max_t W(\ell^j)/\varphi(\ell^j)$ growing linearly in $j$ at every prime ($\approx2j-1+O(1/\ell)$ for odd $\ell$; $4,8,8,16,24,32,40$ for $\ell=2$, $j=3,\dots,9$), so the $\prod j$ shape of $c(q)$ is real and only the constant is loose. If a sharper constant is ever wanted, the place to tighten is 3(d)/4(c), replacing $\#\{m(b)=m\}\le B_m$ by $B_m-B_{m+1}$ and using the odd-$v$ vanishing; it is not needed for $\theta>5/6$.
