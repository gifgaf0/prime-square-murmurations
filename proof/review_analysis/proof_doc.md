# Prime-square murmurations: a proof under GRH

Oct 23, 2026 · @Matt

## Theorem

Under GRH, the root-number-weighted average of λ\_f(p²) over level-1 eigenforms, taken with smooth weights in k and in p²/N, converges to an explicit limit that differs from the prime limit. That limit is the square measure ν₂ of the companion doc, [Prime-power murmurations in the weight aspect](https://claude.ai/artifact/YU4TbTQ65HjbaD8gU1KDA4).

Let H₀ ∈ C\_c^∞(ℝ) be real and even with ∫H₀ ≠ 0, let Φ ∈ C\_c^∞((0, ∞)), and fix θ ∈ (7/8, 1). For even K put σ = K^θ, h(k) = H₀((k − K)/σ) and N = ((K − 1)/4π)². H\_k is the Hecke eigenbasis of S\_k(SL₂(ℤ)), λ\_f(n) = a\_f(n)/n^((k−1)/2), and i^k is the root number shared by all of H\_k. The statistic is

```latex
M(K)=\sqrt{N}\;\frac{\sum_{p}\log p\;\Phi(p^2/N)\sum_{k\ \mathrm{even}}h(k)\,i^{k}\sum_{f\in H_k}\lambda_f(p^2)}{\sum_{p}\log p\;\Phi(p^2/N)\sum_{k\ \mathrm{even}}h(k)\,\dim S_k(1)}
```

**Theorem A.** Assume GRH for all Dirichlet L-functions. As K → ∞ through even integers,

```latex
M(K)\;\longrightarrow\;\frac{1}{2\zeta(2)}\sum_{t\in\mathbb{Z}}f_2(t)\,\frac{I(t)}{I(0)},\qquad I(t)=\int_0^\infty\Phi(y)\cos\!\big(2\pi t/\sqrt{y}\big)\,y^{-1/2}\,dy .
```

Here f₂(t) is the prime average of L(1, t² − 4p²), where L(s, Δ) is Zagier's L-function of the discriminant Δ. Step 4 defines it through local densities and gives it as an explicit Euler product, with f₂(0) = π/4. The series over t converges absolutely.

**Theorem B.** The limit is ν₂ paired with Φ: point masses (c/m³)·T₂(c) at y = (c/m)², summed with c in increasing order,

```latex
\frac{1}{2\zeta(2)}\sum_{t}f_2(t)\,\frac{I(t)}{I(0)}=\lim_{C\to\infty}\frac{1}{I(0)}\sum_{c\le C}\ \sum_{\substack{m\ge1\\(m,c)=1}}\frac{T_2(c)}{m^{2}}\,\Phi\big((c/m)^2\big),\qquad T_2(c)=A_2(c)\prod_{\ell\nmid c}\big(1-\ell^{-2}\big),
```

where A₂(c) is the average of the Kloosterman sum S(a², 1; c) over units a mod c.

Three remarks on the setup. Smooth Φ makes the t-series absolutely convergent, so the conditional summation in Bober et al.'s Section 5 is not needed. Weighting by i^k over all even k removes the two non-oscillating terms of the p² trace formula. The range θ > 7/8 comes from the error budget in Step 5; the companion doc's numerics also use narrower windows, outside this range.

## Setup and notation

GRH enters in exactly two places: the Lindelöf bound for quadratic Dirichlet L-functions (Step 3) and primes in progressions (Step 4). Nothing is assumed about L-functions of modular forms.

K is even and large, σ = K^θ with 7/8 < θ < 1, and h(k) = H₀((k − K)/σ) with H₀ real, even, smooth and supported in \[−1, 1\]. So h(k) ≠ 0 only for K/2 ≤ k ≤ 2K, and every weight in play has k ≥ 4.

- Ĥ₀(η) = ∫H₀(v)e^(iηv) dv is real, even and Schwartz, with Ĥ₀(0) = ∫H₀ ≠ 0.
- N = ((K − 1)/4π)². Φ is supported in \[a, b\] ⊂ (0, ∞), so only primes with √(aN) ≤ p ≤ √(bN) enter; all of them are ≍ K.
- Tr\_k(n) = Σ\_{f∈H\_k} λ\_f(n) = Tr(T\_n | S\_k)/n^((k−1)/2). Every f ∈ H\_k has root number i^k = (−1)^(k/2).
- With D\_K = Σ\_k h(k) dim S\_k and V(p) = √N · Σ\_k h(k) i^k Tr\_k(p²)/D\_K, the statistic is the prime average M(K) = Σ\_p log p Φ(p²/N) V(p) / Σ\_p log p Φ(p²/N).
- Δ < 0 is a discriminant, Δ ≡ 0 or 1 (mod 4). N\_q(Δ) = #{x mod 2q : x² ≡ Δ (mod 4q)}. Zagier's L-function is L(s, Δ) = ζ(2s)/ζ(s) · Σ\_q N\_q(Δ) q^(−s) = Σ\_n a\_Δ(n) n^(−s), so a\_Δ = λ ∗ N(Δ) with λ the Liouville function.
- H(n) is the Hurwitz class number, H(0) = −1/12. χ = χ₋₄ throughout; τ and ω count divisors and prime factors; c\_q(t) is Ramanujan's sum.
- Local densities: ν\_t(q) is the average of N\_q(t² − 4b²) over units b mod q, and δ\_t(n) is the average of a\_{t²−4b²}(n) over units b mod n, so δ\_t(n) = Σ\_{q|n} λ(n/q) ν\_t(q).
- ε > 0 is arbitrarily small and A > 0 arbitrarily large. Implied constants depend only on H₀, Φ, θ, ε and A.

## Step 1: the trace formula and the weight sum

Summing over all even k with the root-number weight turns the p² trace formula into a sum over t with a sharply localized factor, and kills its two non-oscillating terms.

**Lemma 1 (Eichler–Selberg, level 1).** For even k ≥ 4 and n ≥ 1, with U the Chebyshev polynomial of the second kind,

```latex
\mathrm{Tr}_k(n)=-\frac{1}{2\sqrt n}\sum_{t^2\le 4n}H(4n-t^2)\,U_{k-2}\!\Big(\frac{t}{2\sqrt n}\Big)-\frac12\sum_{dd'=n}\Big(\frac{\min(d,d')}{\sqrt n}\Big)^{k-1}.
```

This is Zagier's form of the trace formula (appendix to Lang, *Introduction to Modular Forms*) in unitary normalization; our implementation matches PARI's mftraceform to 12–14 digits. For n = p² the terms t = ±2p have H(0) = −1/12 and U\_{k−2}(±1) = k − 1, and the divisors are 1, p, p²:

```latex
\mathrm{Tr}_k(p^2)=-\frac{1}{2p}\sum_{|t|<2p}H(4p^2-t^2)\,U_{k-2}\!\Big(\frac{t}{2p}\Big)+\frac{k-1}{12p}-\frac12-p^{1-k}.
```

**Lemma 2 (weight sum).** For |t| < 2p put φ\_t = arcsin(t/2p) ∈ (−π/2, π/2). Then

```latex
\sum_{k\ \mathrm{even}}h(k)\,i^{k}\,U_{k-2}\!\Big(\frac{t}{2p}\Big)=-\frac{\sigma}{2}\,\frac{\cos((K-1)\varphi_t)}{\cos\varphi_t}\sum_{\ell\in\mathbb Z}\widehat H_0\big(\sigma(\varphi_t-\pi\ell)\big),
```

where the terms with ℓ ≠ 0 are O\_A(σ^(−A)) uniformly in t. Moreover Σ\_k h(k) i^k g(k) = O\_A(Kσ^(−A)) for g(k) = 1 and g(k) = k − 1, and D\_K = σĤ₀(0)(K − 7)/24 + O\_A(Kσ^(−A)).

*Proof.* Write θ = π/2 − φ\_t, so U\_{k−2}(cos θ) = sin((k − 1)θ)/sin θ, and for even k, i^k sin((k − 1)θ) = −cos((k − 1)φ). Poisson summation over k = 2j gives, for K even,

```latex
\sum_{k\ \mathrm{even}}h(k)\,e^{i(k-1)\varphi}=\frac{\sigma}{2}\,e^{i(K-1)\varphi}\sum_{\ell\in\mathbb Z}\widehat H_0\big(\sigma(\varphi-\pi\ell)\big),
```

and the real part is the identity. For |φ| < π/2 and ℓ ≠ 0, |φ − πℓ| ≥ π/2, so those terms are O(σ^(−A)). The weight i^k = e^(iπk/2) puts the frequency at φ = π/2, where every term is O(σ^(−A)); the factor k − 1 is a derivative in φ and costs a factor K. For D\_K, dim S\_k = (k − 1)/12 − 1/2 + ρ(k) with ρ periodic mod 12 and of mean zero on even k, so ρ contributes O(σ^(−A)). Finally Σ\_{k even} h(k) = σĤ₀(0)/2 + O(σ^(−A)), and Σ\_{k even} h(k)(k − K) = O(σ^(−A)) because H₀ is even. ∎

**Corollary.** For p ≍ K,

```latex
\sum_{k\ \mathrm{even}}h(k)\,i^k\,\mathrm{Tr}_k(p^2)=\frac{\sigma}{4p}\sum_{|t|<2p}\frac{H(4p^2-t^2)}{\cos\varphi_t}\,\cos((K-1)\varphi_t)\,\widehat H_0(\sigma\varphi_t)+O_A(K^{-A}).
```

The two non-oscillating terms of Lemma 1, (k − 1)/12p and −1/2, contribute O(Kσ^(−A)/p + σ^(−A)) to the root-number-weighted sum over all even k, and p^(1−k) is smaller still. In a window restricted to k ≡ 2δ (mod 4) they would survive as a smooth extra term (companion doc, Setup).

## Step 2: class numbers as L-values

Written through Zagier's L-function, each class number becomes an L-value whose Dirichlet coefficients depend only on Δ modulo 4n. That periodicity is what lets Step 4 average over primes.

**Lemma 3 (Zagier).** Let Δ < 0, Δ ≡ 0 or 1 (mod 4), and write Δ = Δ₀f² with Δ₀ fundamental.

1. L(s, Δ) = L(s, χ\_{Δ₀}) B\_f(s), where B\_f(s) = Σ\_{d|f} μ(d) χ\_{Δ₀}(d) d^(−s) σ\_{1−2s}(f/d). So L(s, Δ) is entire, and |B\_f(s)| ≤ τ(f)² for Re s ≥ 1/2.
2. H(|Δ|) = (√|Δ|/π) · L(1, Δ).
3. N\_q(Δ) depends only on Δ mod 4q and is multiplicative in q. Hence a\_Δ(n) depends only on Δ mod 4n and is multiplicative in n.

*Proof.* (1) is in Zagier, "Modular forms whose Fourier coefficients involve zeta-functions of quadratic fields" (LNM 627, 1977). Both sides are Euler products, and the local factors agree by counting square roots modulo ℓ^j. For odd ℓ with ℓ^e ∥ f and Δ = ℓ^(2e+r)u (r ∈ {0, 1}, ℓ ∤ u), Hensel's lemma gives N\_{ℓ^j}(Δ) = ℓ^⌊j/2⌋ for j ≤ 2e + r and (1 + χ\_{Δ₀}(ℓ))ℓ^e for larger j; ℓ = 2 is the same count with the modulus 4q. We checked the local factors exactly for all 796 pairs (Δ, ℓ) with −400 < Δ < 0 and ℓ ≤ 7. (2) H(|Δ|) = Σ\_{g|f} h\_w(Δ₀g²) with h\_w = h/(w/2). The class number of the order of discriminant Δ₀g² is h\_w(Δ₀)·g·Π\_{ℓ|g}(1 − χ\_{Δ₀}(ℓ)/ℓ), and Dirichlet's formula gives h\_w(Δ₀) = √|Δ₀| L(1, χ\_{Δ₀})/π. The factor (1/f)Σ\_{g|f} g Π\_{ℓ|g}(1 − χ(ℓ)/ℓ) and B\_f(1) are both multiplicative in f and agree on prime powers. Against PARI's class numbers the identity holds to 3·10⁻¹⁶. (3) follows from the definition and the Chinese remainder theorem. ∎

**Proposition 1 (per-prime identity).** For p ≍ K,

```latex
V(p)=\frac{1}{2\zeta(2)\,\widehat H_0(0)}\cdot\frac{K-1}{K-7}\sum_{|t|<2p}L(1,t^2-4p^2)\,\cos((K-1)\varphi_t)\,\widehat H_0(\sigma\varphi_t)+O_A(K^{-A}).
```

*Proof.* Since √(4p² − t²) = 2p cos φ\_t, Lemma 3(2) gives H(4p² − t²)/cos φ\_t = (2p/π) L(1, t² − 4p²) in the Corollary of Step 1. Divide by D\_K (Lemma 2) and multiply by √N = (K − 1)/4π. The constant is √N·(σ/2π)/(σĤ₀(0)(K − 7)/24) = (3/π²Ĥ₀(0))·(K − 1)/(K − 7), and 3/π² = 1/(2ζ(2)). ∎

At K = 2000 the two sides agree to 10⁻¹³ for every prime tested (Numerical checks).

## Step 3: truncating L(1, Δ) under GRH

Under GRH a smoothed series of length about M already gives L(1, Δ) up to M^(−1/2), so only short Dirichlet coefficients, hence only small moduli, are needed.

**Lemma 4.** Assume GRH. For Δ as in Lemma 3 and M ≥ 1,

```latex
L(1,\Delta)=\sum_{n\ge1}\frac{a_\Delta(n)}{n}\,e^{-n/M}+O_\varepsilon\big(|\Delta|^{\varepsilon}M^{-1/2+\varepsilon}\big).
```

*Proof.* By Mellin inversion of e^(−x), the sum equals (1/2πi)∫ over Re w = 2 of L(1 + w, Δ)Γ(w)M^w dw. L(s, Δ) is entire, because Δ₀ < 0 makes χ\_{Δ₀} non-principal. Move the contour to Re w = −1/2 + ε, passing the pole of Γ at w = 0, whose residue is L(1, Δ). On the new line GRH gives the Lindelöf bound L(1/2 + ε + iτ, χ\_{Δ₀}) ≪ (|Δ|(1 + |τ|))^ε, Lemma 3(1) gives |B\_f| ≤ τ(f)² ≪ |Δ|^ε, and Γ decays exponentially in |τ|. ∎

We also use the trivial bound L(1, Δ) ≪ |Δ|^ε.

## Step 4: primes in progressions, local densities and f₂(t)

Averaging the truncated series over primes replaces each coefficient by its local density δ\_t(n), and these densities are simple enough to compute exactly.

**Lemma 5 (GRH).** Let r ≥ 1, (b, r) = 1, and let g ∈ C¹ be supported in \[Y₁, Y₂\] with Y₂ ≪ Y₁. With V(g) = ‖g‖\_∞ + ∫|g′|,

```latex
\sum_{p\equiv b\ (r)}(\log p)\,g(p)=\frac{1}{\varphi(r)}\int g(x)\,dx+O\big(V(g)\,Y_2^{1/2}\log^2(rY_2)\big).
```

*Proof.* Under GRH, θ(x; r, b) = x/φ(r) + O(x^(1/2) log²(rx)) uniformly in r (Davenport, *Multiplicative Number Theory*, ch. 20; Montgomery–Vaughan, §13.1). Integrate by parts against g. ∎

**Lemma 6 (local densities).** δ\_t is multiplicative in n, |δ\_t(ℓ^j)| ≤ 2, and the local values are:

| Prime | Condition | δ\_t(ℓ^j) for j ≥ 1 | Local factor E\_ℓ(t) = Σ\_j δ\_t(ℓ^j)ℓ^(−j) |
| --- | --- | --- | --- |
| odd ℓ | ℓ ∤ t | 1 for even j; −(1 + χ(ℓ))/(ℓ − 1) for odd j | (1 − (1 + χ(ℓ))/(ℓ(ℓ − 1)))/(1 − ℓ⁻²) |
| odd ℓ | ℓ \| t | χ(ℓ)^j | ℓ/(ℓ − χ(ℓ)) |
| 2 | t odd | (−1)^j | 2/3 |
| 2 | 2 ∥ t | 0 for odd j; 2 for even j | 5/3 |
| 2 | 4 \| t | 0 | 1 |

For t ≠ 0 the series D\_t(s) = Σ\_n δ\_t(n) n^(−s) = Π\_ℓ Σ\_j δ\_t(ℓ^j)ℓ^(−js) converges absolutely for Re s > 1/2, and D\_t(s) ≪ |t|^ε on Re s ≥ 1/2 + ε. Define f₂(t) = D\_t(1) = Π\_ℓ E\_ℓ(t). For t = 0 the same local values give D₀(s) = L(s, χ₋₄), and f₂(0) = π/4.

*Proof.* Multiplicativity follows from Lemma 3(3) and the Chinese remainder theorem. Since δ\_t(ℓ^j) = Σ\_{i≤j} (−1)^(j−i) ν\_t(ℓ^i), it is enough to compute ν\_t(ℓ^i) for i ≥ 1.

- *Odd ℓ.* The congruence x² ≡ Δ (mod 4ℓ^i) fixes x mod 2, so N\_{ℓ^i}(Δ) counts square roots mod ℓ^i. With y = 2b, φ(ℓ^i)ν\_t(ℓ^i) counts pairs (x, y) mod ℓ^i with y a unit and x² + y² ≡ t². For fixed x there are 1 + ((t² − x²)/ℓ) unit solutions y when ℓ ∤ t² − x², and none otherwise (Hensel). Summing over x mod ℓ^i, and using Σ\_{x mod ℓ} ((t² − x²)/ℓ) = −χ(ℓ) when ℓ ∤ t, the count is ℓ^(i−1)(ℓ − 2 − χ(ℓ)) if ℓ ∤ t and ℓ^(i−1)(ℓ − 1)(1 + χ(ℓ)) if ℓ | t. So ν\_t(ℓ^i) is 1 − (1 + χ(ℓ))/(ℓ − 1) or 1 + χ(ℓ), whatever i is, and the alternating sums give the table.
- *ℓ = 2.* Units b are odd and Δ = t² − 4b². If t is odd, Δ ≡ 5 (mod 8) is not a square mod 8, so ν\_t(2^i) = 0. If t = 2u with u odd, then x = 2w and the condition is w² + b² ≡ u² (mod 2^i). After scaling by u⁻¹, exactly one of w, b is odd; for i ≥ 3 the solutions with b odd are w ≡ 0 (mod 4), with 2^(i−2) choices, each with 4 square roots b of 1 − w². That is 2^i solutions, and with the cases i = 1, 2 it gives ν\_t(2) = 1 and ν\_t(2^i) = 2 for i ≥ 2. If 4 | t, the condition w² ≡ t²/4 − b² ≡ 3 (mod 4) has no solution for i ≥ 2, while ν\_t(2) = 1.
- *Convergence.* For ℓ ∤ 2t the local factor is 1 + O(ℓ^(−2σ) + ℓ^(−1−σ)) at Re s = σ. The finitely many ℓ | t contribute Π\_{ℓ|t} (1 − ℓ^(−1/2−ε))⁻¹ ≪ |t|^ε. ∎

Brute-force exact computation of the local densities for ℓ ≤ 13 agrees with the table, and the Euler product matches prime averages of L(1, t² − 4p²) (Numerical checks).

**Lemma 7 (the averaged series).** Assume GRH. Let g ∈ C¹ be supported in \[√(aN), √(bN)\], M ≤ K^(1/2) and |t| ≤ K. Then

```latex
\sum_{p}(\log p)\,g(p)\sum_{n\ge1}\frac{a_{t^2-4p^2}(n)}{n}\,e^{-n/M}=F_M(t)\int g(x)\,dx+O\big(V(g)\,K^{1/2}M^{1+\varepsilon}\big),\qquad F_M(t)=\sum_{n\ge1}\frac{\delta_t(n)}{n}\,e^{-n/M}.
```

*Proof.* Terms with n ≥ K^(1−ε) contribute O(exp(−K^(1/2−ε))). For n < K^(1−ε) no prime p ≍ K divides n, and a\_{t²−4p²}(n) depends only on p mod n (Lemma 3(3)). Split the p-sum into classes b ∈ (ℤ/nℤ)\* and apply Lemma 5 to each. The main terms add up to δ\_t(n)∫g. The errors add up to O(V(g)K^(1/2) log²K, · Σ\_b |a\_{t²−4b²}(n)|). Since |a\_Δ(n)| ≤ Σ\_{q|n} N\_q(Δ) and ν\_t(q) ≤ 2^ω(q), we have Σ\_b |a\_{t²−4b²}(n)| ≤ φ(n)Σ\_{q|n} 2^ω(q) ≪ n^(1+ε). Summing over n with weight e^(−n/M)/n gives the error term. ∎

Finally, shifting the Mellin integral for F\_M(t) to Re w = −1/2 + ε gives F\_M(t) = f₂(t) + O(|t|^ε M^(−1/2+ε)) for t ≠ 0 (Lemma 6), and F\_M(0) = π/4 + O(M^(−1/2+ε)) by the convexity bound for L(s, χ₋₄).

## Step 5: assembling the limit

The three error terms tend to zero exactly when θ > 7/8, and the main term converges by dominated convergence. This proves Theorem A.

Fix a small ε > 0 and put T₁ = K^(1−θ+ε) and M = K^(2(1−θ)+8ε). Every error below is measured against the denominator Σ\_p log p Φ(p²/N) = (√N/2)I(0) + O(K^(1/2) log²K), which is ≍ K.

1. **Truncate t.** Since |φ\_t| ≥ |t|/2p, the factor Ĥ₀(σφ\_t) is O(K^(−A)) for |t| > T₁. With L(1, ·) ≪ K^(2ε), Proposition 1 becomes V(p) = (1/(2ζ(2)Ĥ₀(0))) Σ\_{|t|≤T₁} L(1, t² − 4p²) cos((K − 1)φ\_t) Ĥ₀(σφ\_t) + O(T₁K^(−1+ε)); the last term absorbs the factor (K − 1)/(K − 7) = 1 + O(1/K).
2. **Linearize the phase.** φ\_t = t/2p + O(|t|³/p³) and (K − 1)/2p = 2π√N/p. Replacing cos((K − 1)φ\_t)Ĥ₀(σφ\_t) by cos(2πt√N/p)Ĥ₀(σt/2p) costs O(KT₁³/K³ + σT₁³/K³) per term, so O(K^(2−4θ+6ε)) in total.
3. **Truncate L(1, Δ)** by Lemma 4. The error is O(K^(2ε) M^(−1/2+ε)) per term, so O(T₁K^(2ε)M^(−1/2+ε)) = O(K^(−ε+2ε(1−θ)+O(ε²))) = O(K^(−ε/2)) in total.
4. **Average over p** by Lemma 7, for each |t| ≤ T₁, with g\_t(x) = Φ(x²/N) cos(2πt√N/x) Ĥ₀(σt/2x), for which V(g\_t) ≪ 1 + |t|. The main term is F\_M(t)∫g\_t. The errors add up to O(K^(1/2)M^(1+ε)T₁²), which is O(K^(4(1−θ)−1/2+O(ε))) relative to the denominator.
5. **Main term.** Substituting x = √(yN) gives ∫g\_t = (√N/2) I\_K(t), where I\_K(t) = ∫Φ(y) cos(2πt/√y) Ĥ₀(κt/√y) y^(−1/2) dy and κ = 2πσ/(K − 1).

Putting these together,

```latex
M(K)=\frac{1}{2\zeta(2)\,\widehat H_0(0)}\sum_{|t|\le T_1}F_M(t)\,\frac{I_K(t)}{I(0)}+O\!\left(K^{2-4\theta+6\varepsilon}+K^{-\varepsilon/2}+K^{4(1-\theta)-1/2+O(\varepsilon)}\right).
```

All three errors tend to 0 when θ > 7/8 and ε is small. This is where the range comes from: the prime sums need T₁²M ≪ K^(1/2), and the truncation of L(1, Δ) needs M ≫ T₁².

**The limit.** As K → ∞, κ → 0, so I\_K(t) → Ĥ₀(0)I(t) for each t, and M → ∞, so F\_M(t) → f₂(t), with F\_M(0) → π/4. For domination, |F\_M(t)| ≪ 1 + |t|^ε uniformly in M. Writing x = 1/√y, I\_K(t) = 2∫ψ(x)Ĥ₀(κtx)cos(2πtx) dx with ψ ∈ C\_c^∞((0, ∞)). Every x-derivative of Ĥ₀(κtx) is bounded uniformly in κ and t, because η^j Ĥ₀^(j)(η) is bounded. So j integrations by parts give |I\_K(t)| ≪\_j (1 + |t|)^(−j) uniformly in K. Dominated convergence now gives M(K) → (1/(2ζ(2))) Σ\_t f₂(t) I(t)/I(0). ∎ (Theorem A)

## Step 6: the limit equals ν₂

The class-number densities of Step 4 are exactly the Ramanujan coefficients of the Kloosterman masses T₂(c)/c². Poisson summation then turns the t-series into the point masses of ν₂, which proves Theorem B.

**Lemma 8 (local identity).** Let A₂ be multiplicative, with A₂(ℓ) = (1 + χ(ℓ)ℓ)/(ℓ − 1) and A₂(ℓ^j) = 0 for j ≥ 2 when ℓ is odd, and A₂(2) = 1, A₂(4) = −2, A₂(2^j) = 0 for j ≥ 3. Put G(c) = A₂(c) c⁻² Π\_{ℓ|c} (1 − ℓ⁻²)⁻¹, so that T₂(c)/c² = G(c)/ζ(2). Then for every prime ℓ, with v = v\_ℓ(t) (v = ∞ allowed),

```latex
E_\ell(t)=\sum_{j\ge0}G(\ell^{j})\,c_{\ell^{j}}(\ell^{v}).
```

*Proof.* The right side has at most three nonzero terms. For odd ℓ, G(ℓ) = (1 + χ(ℓ)ℓ)/((ℓ − 1)(ℓ² − 1)), and c\_ℓ(ℓ^v) is −1 for v = 0 and ℓ − 1 for v ≥ 1. These give the two odd-ℓ entries of Lemma 6's table, using ℓ² − 1 = (ℓ − χ(ℓ))(ℓ + χ(ℓ)). For ℓ = 2, G(2) = 1/3 and G(4) = −1/6, and the Ramanujan sums c₂, c₄ at 1, 2 and 2^(≥2) give 2/3, 5/3 and 1. ∎

So the trace-formula side (class-number densities) and the Petersson side (Kloosterman averages A₂) carry the same arithmetic. The same computation with A₁ = μ²/φ in place of A₂ reproduces Bober et al.'s factors Π\_{ℓ∤t} (ℓ² − ℓ − 1)/(ℓ² − ℓ) for primes.

**Proof of Theorem B.**

1. *t ≠ 0.* The series Σ\_c G(c) c\_c(t) converges absolutely, since |c\_c(t)| ≤ (c, t) and |G(c)| ≪ c^(−2+ε). It factors over primes, so by Lemma 8 it equals f₂(t). Hence f₂(t)/ζ(2) = Σ\_c (T₂(c)/c²) c\_c(t), and every partial sum is bounded by Σ\_c |G(c)|(c, t) ≪ |t|^ε.
2. *t = 0.* Here c\_c(0) = φ(c), and Σ\_{c≤C} G(c)φ(c) → π/4. The Dirichlet series of G(c)φ(c) is L(s + 1, χ)H(s), with H absolutely convergent for Re s > −1/2. By Lemma 8 at v = ∞, Σ\_j G(ℓ^j)φ(ℓ^j) = (1 − χ(ℓ)/ℓ)⁻¹ for odd ℓ and 1 for ℓ = 2, so H(0) = 1. Writing G·φ as the convolution of χ(n)/n with the coefficients of H, the partial sums converge to L(1, χ)H(0) = π/4 because those of χ(n)/n converge.
3. *Poisson.* Put ψ(x) = Φ(x⁻²)x⁻² ∈ C\_c^∞((0, ∞)), so that I(t) = 2∫ψ(x)cos(2πtx) dx. For each c, summing Σ\_j ψ(j + a/c) over units a mod c and applying Poisson summation in j gives Σ\_{(m,c)=1} ψ(m/c) = (1/2)Σ\_{t∈ℤ} I(t) c\_c(t).
4. *Assembly.* Since T₂(c)Φ((c/m)²)/m² = T₂(c)ψ(m/c)/c², the partial sums in Theorem B are S\_C = (1/2)Σ\_t I(t) Σ\_{c≤C} (T₂(c)/c²) c\_c(t). Because I(t) is Schwartz, dominated convergence with steps 1 and 2 gives S\_C → (1/(2ζ(2))) Σ\_t f₂(t) I(t). Divide by I(0). ∎

Since T₂ and T₁ = μ²/φ · Π\_{ℓ∤c}(1 − ℓ⁻²) differ at every c ≥ 3 where either is nonzero, the square limit is not the prime limit. For example, with Φ a smooth bump on \[8, 10\] the limits are −1.708 for squares and +0.859 for primes.
