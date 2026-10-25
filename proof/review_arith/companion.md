# Prime-power murmurations in the weight aspect

Oct 22, 2026 · @Matt

In weight-aspect families, root-number-weighted averages of λ\_f(p²) do not follow the murmuration of λ\_f(p). A Petersson-formula derivation that reproduces the proven prime measure of Bober, Booker, Lee and Lowry-Duda exactly predicts both. Exact traces up to weight 38,750, and an independent computation at K = 500,000, match it at every scale tested: across 82 prime-square measurements it gives χ² = 58, against about 12,000 if squares behaved like primes. The square limit ν₂ has infinite total variation, but its interval values converge, and narrow weight windows already sit close to it.

## Result

Primes follow the Bober et al. measure ν₁; prime squares follow the same formula with a different Kloosterman average, which changes every point mass with denominator c ≥ 3. The square limit ν₂ has the opposite sign to ν₁ on \[2, 2.5\] and \[8, 10\], and is large and negative on \[1.6, 1.95\], where ν₁ nearly vanishes. The statistic is the root-number-weighted form of their Theorem 1.1 statistic (see Setup), computed exactly from the trace formula. The table uses the largest run, K = 32,000 with window half-width H = K^0.7 ≈ 1,424.

| Interval E | Point mass inside | ν₁ limit (theorem, primes) | ν₂ limit (derived, squares) | Squares measured, K = 32,000 (count) | Derived formula, same squares | Prime-like prediction, same squares |
| --- | --- | --- | --- | --- | --- | --- |
| \[0.85, 1.15\] | y = 1 (c = 1) | +2.045 | +1.980 | +1.716 ± 0.021 (50) | +1.710 | +1.702 |
| \[3.5, 4.5\] | y = 4 (c = 2) | +1.636 | +1.583 | +1.749 ± 0.036 (71) | +1.712 | +1.729 |
| \[2.0, 2.5\] | y = 9/4 (c = 3) | +0.293 | −0.510 | −0.476 ± 0.025 (53) | −0.508 | +0.271 |
| \[8, 10\] | y = 9 (c = 3) | +0.526 | −1.063 | −1.105 ± 0.022 (92) | −1.100 | +0.545 |
| \[1.6, 1.95\] | y = 16/9 (c = 4) | +0.027 | −0.779 | −0.700 ± 0.027 (42) | −0.692 | +0.046 |
| \[5.5, 7.0\] | y = 25/4 (c = 5) | +0.085 | +0.622 | +0.450 ± 0.024 (88) | +0.434 | +0.087 |

Values are √N times the root-number-weighted average, averaged with log p weights over the p with p²/N in E. ± is the scatter of the per-prime residuals about the formula; the raw scatter of the values is 2–11 times larger because it includes the residue dependence the formula accounts for. The prime-like prediction is the same formula with the primes' Kloosterman average A₁, which is what universality would give for these squares. On the c ≤ 2 intervals primes and squares share their point masses, so the two predictions agree; on the other four the measurement sits 6–19σ from the prime-like value. This window is narrower than Bober et al.'s proven range (H > K^(5/6)). Inside that range the same separation holds but is smaller, because the wider window smears the masses: on \[8, 10\] at K = 32,000 with H = K^0.85, measured −0.229 ± 0.009, formula −0.220, prime-like +0.185.

## Setup

The family is all level-1 Hecke eigenforms f of even weight w with |w − K| ≤ H, each counted once (natural weights), with H = K^θ. Bober et al. prove their theorem for 5/6 < θ < 1. Most computations use θ = 0.85; at K = 8,000–32,000 they also use θ = 0.7 and 0.55, outside that range. (Kuan and Lesesvre prove a weight-aspect murmuration for windows down to K^(1/3+ε), but with harmonic weights, so it does not cover this statistic.) Eigenvalues are unitary (λ\_f(n) = a\_f(n)/n^((w−1)/2)), and every level-1 form of weight w has root number ε\_f = i^w = (−1)^(w/2).

With conductor scale N = ((K − 1)/4π)² and y = n/N, the statistic for Hecke index pᵏ is:

```latex
M_k(E) = \sqrt{N}\;\frac{\sum_{p:\,p^k/N\in E} \log p \;\sum_{w} \varepsilon_w \sum_{f\in H_w(1)} \lambda_f(p^k)}{\sum_{p:\,p^k/N\in E} \log p \;\sum_{w} \dim S_w(1)}
```

For k = 1 this is Bober, Booker, Lee and Lowry-Duda's Theorem 1.1 (conditional on GRH). They fix w ≡ 2δ mod 4 and get (−1)^δ ν(E)/|E|. For primes, weighting by ε\_w over both residues is the same statement, and it is Hua–Mok's E\[ε(f) λ(p)\] with no selection on root numbers. For even powers it is not. The trace formula for p² has two terms that do not oscillate with w, from t = ±2p and from the divisor d = p. They cancel in the root-number-weighted sum over all even weights, but they add (−1)^δ(ln(b/a)/Z₂ − 3/(2π)) to each fixed-δ statistic, with Z₂ = 2(√b − √a): that is −0.143(−1)^δ on \[8, 10\]. This doc uses the root-number-weighted form throughout. Their measure is:

```latex
\nu(E) = \frac{1}{\zeta(2)} \sum_{\substack{(a,q)=1\\ (q/a)^2 \in E}} \frac{\mu(q)^2}{\varphi(q)^2\,\sigma(q)} \left(\frac{q}{a}\right)^3
```

The per-weight checks at level 2 use newforms of level 2, ε\_f from the Atkin–Lehner sign, and C = 2((w − 1)/4π)².

## Derivation

For each Hecke index n, the window average carries a point mass (c/m³)·S(nm², 1; c) at y = (c/m)² for every pair (c, m). Averaged over primes, this reproduces Bober et al.'s ν exactly. The steps (heuristic; see Caveats):

1. Petersson formula at level 1, with ω\_f = Γ(w−1)/((4π)^(w−1)⟨f, f⟩):

```latex
\sum_f \omega_f \lambda_f(n) = \delta_{n,1} + 2\pi i^{-w} \sum_{c\ge1} \frac{S(n,1;c)}{c}\, J_{w-1}\!\left(\frac{4\pi\sqrt{n}}{c}\right)
```

2. Natural weights. Since 1/ω\_f = (w−1) L(sym² f, 1)/(2π²) and L(sym² f, 1) = ζ(2) Σ\_m λ\_f(m²)/m, for (n, m) = 1:

```latex
\sum_f \lambda_f(n) = \frac{w-1}{12} \sum_{m\ge1} \frac{1}{m} \sum_f \omega_f\, \lambda_f(nm^2)
```

3. Root numbers. Multiplying by ε\_f = i^w cancels i^(−w), so every Kloosterman term keeps one sign across the window. The diagonal and other non-oscillating terms alternate with w and cancel.
4. The window. With the natural-weight factor (w − 1)/12, the sum needed is Σ (w − 1) J\_(w−1)(x) over even w in the window. With a and b the first and last values of w − 1 it has the exact closed form Φ(x) = (x/2)\[J\_(a−1)(x) + J\_(b+1)(x) + ∫₀ˣ (J\_a(t) − J\_b(t)) dt\]: about x/2 inside the window and negligible below it, and dividing by Σ dim gives the mass in step 5. The (c, m) term therefore survives only where 4πm√n/c falls inside the window, which is y = n/N ≈ (c/m)².
5. Per index n: √N · E\[ε\_f λ\_f(n)\] has mass (c/m³)·S(nm², 1; c) at y = (c/m)². At finite K, Φ spreads the mass over √y ∈ (c/m)(w\_lo − 1, w\_hi − 1)/(K − 1); every finite-K prediction in this doc uses Φ exactly.
6. Prime average. With p equidistributed in units mod c, collect the pairs (gc′, gm′) that land on the same reduced point c′/m′, with gcd(c′, m′) = 1. Twisted multiplicativity of Kloosterman sums gives mass (c′/m′³)·A₁(c′)·Π\_(ℓ∤c′)(1 − ℓ⁻²), with A₁(c′) = μ(c′)²/φ(c′). That equals Bober et al.'s mass at q = c′, a = m′ term by term.

Numerical check of step 6: the collected masses match their formula to within 2 × 10⁻⁴ for every squarefree c′ ≤ 30 and m′ ≤ 5 (the gap is truncation of the g-sum), and vanish for non-squarefree c′. On intervals the two measures agree to four digits: 2.0447 vs 2.0448 on \[0.85, 1.15\], 0.2927 vs 0.2926 on \[2, 2.5\], 1.6358 vs 1.6358 on \[3.5, 4.5\], 0.5261 vs 0.5261 on \[8, 10\]. No constants were fitted.

**Which steps are exact.** At finite K the measured statistic (trace formula, checked against PARI), the Petersson formula, the kernel Φ and the local Kloosterman averages are exact. Two steps are heuristic: expanding L(sym² f, 1) as a conditionally convergent m-series and swapping it with the sums over f, c and the window; and replacing each prime's own residue mod c by the average over residue classes, uniformly in c and m. Bober et al.'s proof avoids both. It starts from the Eichler–Selberg formula, expands the class-number L-values L(1, ψ\_(t²−4n)) instead (truncated under GLH), and sums primes in progressions under GRH. Adapting it to n = p² is real work, not a transcription; the independent check found four changes. First, the t = ±2p and d = p terms add a smooth term in their fixed-root-number windows (see Setup). Second, with p \~ K instead of n \~ K² the GRH saving is smaller, which by the checker's estimate needs windows wider than K^(11/12). Third, for primes ℓ dividing t the discriminant t² − 4p² gives ψ(ℓ) = χ₋₄(ℓ) for every p, so the local factors change and their Section 5 continuation must be redone. Fourth, the square masses are only conditionally summable, so the assembly must use ordered sums. That proof has not been written. Step 2 also drops the terms with p | m. Restoring them through the Hecke relations multiplies every mass at index pᵏ by 1 + 1/p − p^(−k−1) − p^(−k−2), which is negligible for primes and for the squares at large K (p ≥ 3,600 at K = 32,000), but a few percent for the small primes behind the cube test.

At level N, the Fricke-twisted Petersson formula gives S(N̄nm², 1; c) with (c, N) = 1 and C = N((w − 1)/4π)². For newforms of prime level N with natural weights, the collected mass at each point with N ∤ c′ is N/(N − 1) times the level-1 mass, and 0 at N | c′; the old forms supply the pairs with N | m. (The first version of this section said N; the independent check corrected it.) At N = 2 both give 2. On matched weights 300–820 the level-2/level-1 ratio is 2.003 ± 0.043 at y = 1/9, 1.996 ± 0.030 at 1/4, 1.982 ± 0.015 at 1, 2.01 ± 0.25 at 9/4 and 1.90 ± 0.29 at 9, and 0.003 ± 0.004 at y = 4 (c = 2). The checker measured 1.48 ± 0.10 at N = 3 and 1.22 ± 0.07 at N = 5, against 1.5 and 1.25. For squares the twist by N̄ also changes the Kloosterman average, replacing χ₋₄(ℓ) by χ₋₄(ℓ)(N/ℓ): A₂(3) = −1 at level 1 but +2 at level 2. So level-2 squares are not twice level 1; on \[8, 10\] at K = 1000 they measure +4.01 ± 0.51, against +4.09 from the twisted formula and −2.10 from doubling level 1.

## Prime powers

For Hecke index pᵏ only the Kloosterman average changes: the mass at (c′/m′)² becomes (c′/m′³)·A\_k(c′, m′)·Π\_(ℓ∤c′)(1 − ℓ⁻²), where A\_k(c′, m′) is the average of S(aᵏ m′², 1; c′) over units a mod c′. This closed form matches the collected g-sum to 5 × 10⁻⁵ for every c′ tested. With log p weights the points y = pᵏ/N have density proportional to y^(1/k − 1), so the limit on E = \[a, b\] is ν\_k(E) = Σ mass · y^(1/k−1) / ∫\_E y^(1/k−1) dy.

| c′ | A₁ (primes) | A₂ (prime squares) | A₃ (prime cubes) |
| --- | --- | --- | --- |
| 3 | +0.500 | −1.000 | +0.500 |
| 4 | 0 | −2.000 | 0 |
| 5 | +0.250 | +1.500 | +0.250 |
| 7 | +0.167 | −1.000 | +1.579 |
| 9 | 0 | 0 | +0.521 |
| 11 | +0.100 | −1.000 | +0.100 |
| 12 | 0 | +2.000 | 0 |
| 13 | +0.083 | +1.167 | −1.807 |
| 15 | +0.125 | −1.500 | +0.125 |

Values are for m′ = 1. For an odd prime ℓ, A₂(ℓ) = (1 + (−1/ℓ)ℓ)/(ℓ − 1), from the Gauss-sum identity G² = (−1/ℓ)ℓ, against A₁(ℓ) = 1/(ℓ − 1). A₂ is multiplicative, equals −2 at 4 and 0 at 8, 9, 16 and 25. So the square masses keep weight about (−1/ℓ) at large denominators instead of decaying like 1/ℓ, and their total variation diverges logarithmically: ν₂ is not a locally finite measure. Its interval values still converge when summed m first, and this needs no hypothesis:

Write T₂(c) = A₂(c)·Π\_(ℓ∤c)(1 − ℓ⁻²). The m-th block of ν₂(E) is then (1/(m²Z₂)) Σ T₂(c) over c ∈ \[m√a, m√b\] coprime to m, with Z₂ = 2(√b − √a). The Dirichlet series of T₂ is L(s, χ₋₄)·G(s) with G absolutely convergent for Re s > 1/2; that is, T₂ = χ₋₄ ∗ g with Σ |g(d)| d^(−σ) < ∞ for σ > 1/2. Partial sums of χ₋₄ are bounded by 1, so |Σ\_(c≤X, (c,m)=1) T₂(c)| ≤ 2^ω(m) Σ\_(d≤X) |g(d)| ≪ m^ε X^(1/2+ε). Each block is therefore O(m^(−3/2+ε)), and the m-series converges absolutely even though the masses do not. The same bound holds uniformly in K when the indicator of E is replaced by the finite-K window weight, so the finite-K formula tends to ν₂(E) by dominated convergence (a sketch; the window weight must have uniformly bounded variation and depend on c/m only). Ordering by c instead of m gives the same values, but arithmetic rearrangements do not: on \[8, 10\] the parts with c ≡ 1 and 3 (mod 4) drift apart by about ±0.14 per decade of m while their sum converges. So ν₂ is an interval function rather than a measure, and a proof must control the equidistribution errors in aggregate, not term by term. (The bound is not sharp: the blocks actually decay like m^(−7/4).)

Numerically, Σ\_(d≤X) |g(d)| ≈ 1.41√X, while the partial sums of T₂ stay below 0.24√X up to X = 4 × 10⁶. Summing blocks up to m = 3 × 10⁵, the interval values change by less than 6 × 10⁻⁵ beyond m = 10⁵ while the total variation keeps growing like log m; the m-th block times m^1.5 stays below 3.6 and falls slowly. With the density y^(−1/2), the seven test intervals \[0.2, 0.3\], \[0.85, 1.15\], \[1.6, 1.95\], \[2, 2.5\], \[3.5, 4.5\], \[5.5, 7\] and \[8, 10\] give ν₂ = +0.700, +1.980, −0.779, −0.510, +1.583, +0.622 and −1.063.

Cubes agree with primes wherever cubing permutes the units mod c′ (c′ = 3, 4, 5, 11, 15) and differ where 3 divides φ(c′) (c′ = 7, 9, 13, 19). Example: ν₃ = −0.244 against ν₁ = +0.027 on \[1.6, 1.95\]. Prime cubes are too sparse for the window statistic (a handful per interval even at K = 32,000), so the cube prediction is tested peak by peak below.

## The exact limit

In the statistic of Bober et al.'s Theorem 1.1, the derived formula with the exact window kernel matches every measurement: primes at K = 500–4000, and prime squares at K = 1,000–32,000 in three window widths. Its K → ∞ limit is ν₁ for primes and ν₂ for squares.

&#91;embedded content: murm\_squares\_resid.json · prime squares at K = 1,000–32,000 in three weight windows; error bars = scatter of the per-prime residuals about the formula\]

- **Measurements.** Exact traces from the Eichler–Selberg formula with Hurwitz class numbers from PARI, summed over the weight window in closed form. Windows run from weights 304–696 (K = 500) to 25,250–38,750 (K = 32,000, H = K^0.85). Samples: 81,285 primes and 143 prime squares at K = 4000; 32–92 prime squares per interval at K = 32,000.
- **Agreement for primes.** All 28 interval × K values for primes (K = 500–4000) match the finite-K formula, χ² = 5.5 with errors from the raw scatter (which overstate the noise), e.g. +0.147 ± 0.004 against +0.150 on \[8, 10\] at K = 4000.
- **Agreement for squares.** Squares follow the same formula with p² substituted. Each prime gets its own prediction (its actual Kloosterman residues for c ≤ 40, the average beyond), and the error is the scatter of the residuals. Over all 82 square measurements χ² = 57.7, with one point beyond 2σ (2.2σ); the prime-like formula gives χ² ≈ 12,000 with errors computed the same way.
- **Separation.** At K = 32,000 with H = K^0.7, squares sit 19σ from the prime-like value on \[8, 10\] (−1.105 against +0.545) and 11–12σ on \[2, 2.5\] and \[1.6, 1.95\].
- **Convergence.** The window smears each mass over a relative width of about H/K = K^(θ−1) in √y. For θ = 0.85 that is ±29% at K = 4000 and ±21% at K = 32,000, so convergence to the limits is slow. For θ = 0.7 and 0.55 at K = 32,000 it is ±4.5% and ±0.9%, and the measurements already sit near ν₂ (−1.105 and −1.145 on \[8, 10\], limit −1.063). Windows narrower than K^(5/6) are outside Bober et al.'s theorem, so there the agreement is empirical.
- **Larger K (independent).** The second-round independent check (below) computed the statistic with Gaussian windows over all even weights at much larger K: on \[8, 10\], −1.096 ± 0.038 at K = 200,000 and −1.057 ± 0.046 at K = 500,000 (ν₂ = −1.063); on \[2, 2.5\], −0.560 ± 0.036 and −0.543 ± 0.039 (ν₂ = −0.510). Each is within about 1σ of its finite-K model.

## Per-weight evidence at levels 1 and 2

Measured one weight at a time against its own conductor C(w), the data resolve each point mass separately and confirm every ingredient of the formula: where the peaks sit, which denominators the level allows, and the Kloosterman sum that weights each residue class.

&#91;image: Per-weight profiles at levels 1 and 2, the c = 3 residue split at both levels, the hidden c = 4 peak, and primes vs squares vs cubes at each peak\]

| Test | Level 1 | Level 2 |
| --- | --- | --- |
| Peak locations | y = (c/m)², all c | y = (c/m)², c odd only; all 6 even-c points flat |
| c = 2 peaks (y = 4, 4/9, 4/25) | +5.8, +1.9, +1.1 | absent |
| c = 3 peak at y = 9/4, by p mod 3 (1 / 2) | −1.66 / +3.29 | +6.41 / −3.17 |
| Kloosterman rule fitted | S(pm², 1; c): correlation +1.000 (c = 3), 0.999–1.000 (c = 5) | S(2̄pm², 1; c): 0.9999–1.000 over 8 peaks, χ² = 2 on 16 dof |
| c = 4 peak at y = 16, by p mod 4 (1 / 3) | −5.63 / +5.62, sum over all primes 0.00 | — |
| Squares at y = 9 (c = 3) | −3.20 ± 0.28 vs predicted −3.24 (primes +1.63) | — |
| Squares at y = 9/4 (c = 3) | −1.56 ± 0.39 vs predicted −1.62 (primes +0.80) | +6.18 ± 0.63 vs predicted +6.4 (primes +1.62) |
| Squares at y = 16/9 (c = 4) | −1.55 ± 0.43 vs predicted −1.93 (primes 0.00) | — |
| Squares at y = 25/4, 25/9, 25/16 (c = 5) | +1.10, +0.98, +0.65 vs predicted +1.35, +0.90, +0.67 | — |
| Squares at y = 49/4, 49/9, 49/16 (c = 7) | −0.75, −0.40, −0.34 vs predicted −0.63, −0.42, −0.33 | — |
| Per-index rule at c = 7, 9, 13 (primes split by p mod c) | correlation 0.994–1.000 with S(pm², 1; c) at all 9 peaks tested | — |
| Cubes at y = 49/4 (c = 7) and 81/4 (c = 9) | −1.21 vs predicted −1.21 and prime-like +0.09; −1.33 vs −1.32 and 0.00. The prime-like rule is off by 10.7σ and 6.1σ | — |
| Cubes at y = 81/4 split by p³ mod 9 | p³ ≡ 1: −2.40 ± 0.14 vs predicted −2.69; p³ ≡ 8 (Kloosterman sum 0): −0.32 ± 0.17 vs 0. The prime-like rule predicts 0 for both | — |
| Cubes at all 8 peaks with c = 7, 9, 13 | χ² = 13.2 for the cube rule, 172 for the prime-like rule | — |
| Cubes at the 6 reference peaks (c = 1, 3, 5) | χ² = 9.9 with the p \| m terms, 17.4 without (they add about 1/p, up to 14% for these small primes); primes at y = 1: +0.09 ± 0.14%, as 1/p predicts | — |

Peak heights use a ±4% window in y around each point, pooled over weights 200–822 at level 1 (300–822 for the residue splits) and 200–822 at level 2. "Predicted" for squares = the amplitude fitted to the primes' residue split at that peak, times A₂ instead of A₁, with no further freedom. The level-2 traces come from Hurwitz quaternion shells of norm p and 2p (Eichler–Brandt), checked against PARI to 12–14 digits. The cube rows use single weights 200–8000 from the trace formula, 13–40 primes per peak (p ≤ 199), the dominant (c, m) term with each cube's own Kloosterman residue and the p | m factor 1 + 1/p − p⁻⁴ − p⁻⁵, and errors of measured − predicted clustered by prime. Since p³ grows like w², neighbouring cubes fall at nearly disjoint weights, so clustering by prime is appropriate; for primes, where neighbours share weights, it understates the noise.

## What this means for Hua–Mok

In weight-aspect families, primes and prime squares share point masses only at denominators c ≤ 2 (and where both vanish). Every other mass changes for squares; for cubes the masses change wherever 3 divides φ(c), which the peak test confirms at c = 7, 9 and 13.

- **Conjecture 1.1 as stated.** It assumes a per-prime profile: a continuous G with √X E\[ε λ(p)\] = G(p/X) + o(1) locally uniformly along primes. Bober et al.'s limit ν is purely atomic, and a continuous G holding uniformly along primes would force an absolutely continuous limit, so no such G exists in this family. The data agree: on \[8, 10\] the scatter of √N·A(p) across primes is about 0.25√(K/H), with an O(1) floor near H ≈ K, and it tracks the class number H(4p)/√p (correlation 0.90–0.97). The per-index masses S(pm², 1; c) also depend on p mod c. So the hypothesis fails here, and 1.1 says nothing literal about this family.
- **The prime-averaged version.** This is the form that makes sense in weight aspect, and the one Bober et al. prove for k = 1. Here universality fails for k = 2: ν₂ replaces A₁ by A₂ in every mass, which changes every c′ ≥ 3 where either is nonzero, and has the opposite sign on \[2, 2.5\] and \[8, 10\]. Over 82 square measurements universality gives χ² ≈ 12,000, against 58 for the derived formula.
- **Their proven case.** Theorem 1.2 (weight 2, level aspect) is consistent with this. There the average over levels removes the residue dependence, and their formula depends on Pᵏ only through Pᵏ/X.
- **Conjecture 2.2** (the von Mangoldt average over all prime powers). The formula gives proper-power averages of size N^(−1/2) each. About √N squares fall in NE, so proper powers contribute O(1/N) to the normalized average, below the N^(−1/2) murmuration scale. That is consistent with 2.2 (heuristic, not a proof).

## Independent check

A separate agent, working from scratch with its own code, confirmed the data and the prime-case derivation, and found two overstatements; both are now corrected in this doc.

| Item checked | Method | Outcome |
| --- | --- | --- |
| Stored statistic, K = 1000 (intervals \[8, 10\] and \[2, 2.5\], primes and squares) | Brute-force PARI traces over all 355 weights, plus its own trace-formula code | Agrees to 7 × 10⁻¹⁴ per index; M = +0.128 ± 0.013 and −0.337 ± 0.029 on \[8, 10\] |
| Kloosterman averages (A₁ = μ²/φ; A₂(ℓ) closed form) | All units, c ≤ 60 and ℓ ≤ 47 | Pass, max deviation 1.3 × 10⁻¹¹ |
| Collected masses equal Bober et al.'s | g-sum up to 400, 62 reduced pairs | Pass (10⁻⁴, truncation); fails for non-reduced pairs, which the derivation does not use |
| Petersson normalization 1/ω\_f = (w − 1)L(sym² f, 1)/(2π²) | PARI at w = 12, 16 | Pass (10⁻⁹, 2 × 10⁻⁵) |
| Finite-K formula | Its own Bessel-sum version over the actual window | Reproduces 0.129 and 0.315 at K = 1000 |
| "Squares converge to a different limiting measure" | Total variation of the square masses | **Overstated.** The variation diverges logarithmically; only conditionally convergent sums exist. Corrected to "does not follow the prime curve; the limit over fixed intervals is open." |
| Argument that Conjecture 1.1's hypothesis fails | Per-prime scatter and the form of ν | **Conclusion right, argument weak.** Replaced the counting argument with: ν is atomic, so no continuous per-prime G exists; measured scatter about 0.25√(K/H), tracking H(4p)/√p |

It also flagged that the Bessel step must carry the (w − 1) weight, which the computations did but the text had glossed (fixed in Derivation, step 4), and that terms with p | m are dropped (added to Caveats). It could not open Hua–Mok's PDF; the per-prime form of Conjecture 1.1 used here was read directly from the paper's page 2.

**Second round (this revision).** Two more agents, each with its own code, checked the new numbers and the new theory claims. They confirmed every number they recomputed and found three things to correct, all now fixed: the level-N constant is N/(N − 1), not N; Bober et al.'s proof does not transfer to squares as directly as first claimed; and the cube error bars had been quoted as errors of the measured values when they were errors of measured − predicted. Their code is in prime\_experiments.zip, under independent\_check\_2/.

| Item checked | Method | Outcome |
| --- | --- | --- |
| Prime squares at K = 32,000, window K^0.7 | Own trace-formula code over all 1,425 weights, 6 primes | Agrees to 8 × 10⁻¹² |
| Prime squares at K = 200,000 and 500,000 | Own code, Gaussian windows over all even weights, 261–1,143 primes per interval | \[8, 10\]: −1.096 ± 0.038 and −1.057 ± 0.046; \[2, 2.5\]: −0.560 ± 0.036 and −0.543 ± 0.039; each within about 1σ of the finite-K model |
| Existence of ν₂ | Local factors by hand; blocks to m = 10⁵ | Pass. The bound is not sharp (blocks decay like m^(−7/4)); ordering by c agrees with ordering by m, but rearranging by c mod 4 does not |
| Cube peaks y = 49/4 and 81/4 | Own code, single weights 200–4000, split by p³ mod 7 and 9 | Values agree to 3 × 10⁻¹⁴ and the class means follow the cube rule. **Error bars mislabelled:** they were errors of measured − predicted, and the prime-like rejection was understated (7.5σ and 4.3σ, not 3.5σ and 3.1σ). Corrected |
| Level-N constant | Derivation including old forms; exact PARI newform traces at N = 2, 3, 5 | **Corrected** to N/(N − 1): 1.99 ± 0.16, 1.48 ± 0.10, 1.22 ± 0.07. On our level-2 data: 1.996 ± 0.029 at y = 1/4, 1.982 ± 0.014 at y = 1. Squares at level N carry a (N/·) twist |
| Transfer of Bober et al.'s proof to p² | Their Sections 2–5; local factors of the class-number sums measured | **Overstated.** Plausible as a heuristic, but four steps change (Derivation) |

## Caveats and open steps

The first version listed eight caveats. Five are now resolved or explained, the cube prediction has a first test, and two remain open: a rigorous proof and peer review.

| Caveat in the first version | Status | What changed |
| --- | --- | --- |
| The derivation is heuristic | Open, narrowed | Exact and heuristic steps are now separated (Derivation). Adapting Bober et al.'s proof to p² needs four concrete changes, found by the independent check: smooth extra terms, wider windows, new local factors, and ordered sums. Not done. |
| The finite-K model treats the window edges as sharp | Resolved | Exact window kernel Φ; predictions moved by at most 0.011. Small samples use each prime's own Kloosterman residues. |
| 2–14 prime squares per interval | Resolved | K = 8,000–32,000 in three windows, up to 92 squares per interval. All 82 square measurements fit (χ² = 57.7); the prime-like rule gives ≈ 12,000. |
| Slow convergence to the limits | Explained | It is the window's smearing (±21% in √y at K = 32,000 for H = K^0.85), which the finite-K formula reproduces. Narrower windows sit near ν₂, outside the proven window range. |
| ν₂ has infinite total variation, so its limit was unclear | Resolved (sketch) | Interval values converge absolutely in m with no hypothesis (the T₂ = χ₋₄ ∗ g bound), and the finite-K formula tends to them. Rearranging by c mod 4 changes the parts, so the equidistribution errors must be controlled in aggregate. That the statistic itself tends to the formula belongs to the first row. |
| The cube prediction is untested | Tested | At the 8 peaks where cube and prime residues differ: χ² = 13.2 for the cube rule, 172 for the prime-like rule. The reference peaks first sat 2–3σ high; the p \| m Hecke terms dropped in the derivation (a factor of about 1 + 1/p, large for these small primes) account for it. A windowed cube test needs K near 10⁶. |
| The level-2 normalization is not derived | Resolved (corrected) | N/(N − 1) times the level-1 mass, corrected from N by the independent check (both give 2 at N = 2). Level 2: 1.98–2.01 at the well-measured peaks, 0.003 at the forbidden c = 2 peak; N = 3 and 5: 1.48 ± 0.10 and 1.22 ± 0.07. Squares at level N carry an extra (N/·) twist. |
| Literature; no peer review | Checked; not reviewed | Kundu–Müller (p² in the level aspect, same shape as primes there), Kuan–Lesesvre (weight aspect, primes, harmonic weights) and Tomczak (depth aspect) do not treat prime powers in the weight aspect. Nothing here has been peer reviewed. |

Natural next steps: write the trace-formula proof for n = p²; a windowed cube test, which needs K near 10⁶ to put a few dozen cubes in an interval; and the same analysis at higher level and for Maass forms.

## Reproducibility and sources

Everything runs from the scripts in prime\_experiments.zip (Python with numpy, scipy and cypari).

| Script | What it does | Check passed |
| --- | --- | --- |
| murm\_level1.py | Level-1 traces per weight from the Eichler–Selberg formula | Equal to PARI mftraceform to 10–12 digits (weights 12–600, including p and p² at the peaks) |
| murm\_exact.py | Weight-window sums in closed form; the Theorem 1.1 statistic for K = 500–4000 | Equal to per-weight sums to 10⁻¹³ |
| murm\_predict.py, kloost.py | ν₁, ν₂, ν₃ and the finite-K formula; Kloosterman averages by FFT | ν₁ equal to Bober et al.'s formula to four digits |
| murm\_compare\_exact.py, murm\_converge.py | Measured against predicted; extrapolation to K = 10⁷; limit stability | Cutoff m ≤ 300 vs 600 agree to 3–4 digits |
| murm\_hurwitz.py | Level-2 traces from Hurwitz quaternion shells | Equal to PARI to 12–14 digits |
| murm\_predict2.py | Exact window kernel Φ; ν\_k with the density y^(1/k − 1); finite-K predictions | Φ equal to the direct Bessel sum (247.416 vs 247.417 at K = 500) |
| murm\_squares\_bigK.py, murm\_bigK\_resid.py | Square statistic at K = 8,000–32,000 in three windows; per-prime predictions, residual errors and χ² for the formula and the prime-like rule | Equal to the earlier K = 1000 run to 6 × 10⁻¹⁴ |
| murm\_limit\_check2.py | Partial sums of T₂, the bound Σ\|g\|, and the m-blocks of ν₂ up to m = 3 × 10⁵ | \|Σ T₂\| below the bound at every X tested |
| murm\_single\_weight.py, murm\_cubes.py | Single-weight peak test for primes and cubes, weights 200–8000 | The two implementations agree on every shared peak |
| murm\_level2\_ratio.py | Level-2 / level-1 peak ratio on matched weights | Uses the PARI-checked trace data above |

Sources:

- Bober, Booker, Lee, Lowry-Duda, [Murmurations of modular forms in the weight aspect](https://arxiv.org/html/2310.07746v2), Theorem 1.1 and the measure ν.
- Hua, Mok, [Universal murmuration and Hecke augmentation](https://arxiv.org/pdf/2609.00777), Conjectures 1.1 and 2.2, Theorem 1.2.
- Kundu, Müller, [Murmurations of modular forms and p-power coefficients](https://arxiv.org/html/2507.00738v1): level aspect, weight 2; the p² density has the same shape as the prime one there.
- Kuan, Lesesvre, [Murmurations using Petersson trace formula](https://arxiv.org/pdf/2507.11418): weight aspect, primes, harmonic weights, windows down to K^(1/3+ε).
- Tomczak, [Murmurations in the depth aspect for Maass and modular forms](https://arxiv.org/pdf/2606.08353): depth aspect, primes.
