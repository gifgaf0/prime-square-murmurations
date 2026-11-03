# murmurations_squares v10 — changelog (2026-11-03)

Base: `murmurations_squares (9).tex` (compiles, 13 pp). v10 compiles with latexmk/pdflatex, no errors or undefined references, 16 pp. Every change below was applied as a separate edit to a verbatim copy of v9; 106 lines differ.

Source of the changes: `second_moment_lemma.md` (rev 1) and its audit `second_moment_audit.md` §3. All five audit findings (F1–F5) are incorporated.

## Headline

Theorem A range **7/8 → 5/6** under GRH; Proposition `prop:zf` range **1 − a²/(1+2a) → 1 − 2a²/(1+4a)**, so 79/80 → 47/48 (ZF(7/8)) and 167/168 → 95/96 (ZF(11/12)).

## Edits, in document order

1. `\date`: October → November 2026.
2. **Abstract**: 7/8 → 5/6, 79/80 → 47/48, 167/168 → 95/96.
3. **§1 "What is new"**: the sentence "The price is the range θ>7/8, against θ>5/6 in [BBLL]" (now false) replaced by: range equals BBLL's; obtained by character expansion of a_{t²−4p²}(n) in p mod n, with the second-moment bound (new Lemma 7) as the arithmetic input; one sentence placing Kuan–Lesesvre (narrower windows, width K^{1/3+ε}, but for the harmonically weighted statistic). **A `% VERIFY` comment marks the KL exponent and weighting for checking against their Theorem 1 before submission.**
4. **§1 Statement**: θ ∈ (7/8,1) → (5/6,1).
5. **Remarks (3), (5)** after Theorem B: new range and reason (truncation of L(1,Δ) and the character sums bind jointly); 47/48, 95/96.
6. **§2**: "GRH enters in exactly two places" now names *character sums over primes* (Lemma 5, principal case r=1 for the denominator); "7/8<θ<1" → "5/6<θ<1".
7. **Lemma 3(3) proof** (audit F4): "definition and CRT" replaced by the two-line argument N_{q₁q₂} = r_{q₁}·N_{q₂} for odd q₁, and N_{q₁} = r_{q₁} on discriminants.
8. **Lemma 5** restated **per Dirichlet character** (audit §3 item 4): Σ_p (log p) χ(p) g(p) = 1_{χ=χ₀}∫g + O(V(g) Y₂^{1/2} log²(rY₂)); proof via ψ(x,χ*), with the imprimitive (≤ ω(r) log x) and prime-power (O(x^{1/2})) corrections written out. A sentence after it notes the progression form follows by orthogonality and that only r=1 and the character form are used.
9. **New Lemma 7** (`lem:secondmoment`, "second moment of the coefficients"), between Lemma 6 (local densities) and the averaged series: (a) Σ_b a(b)² ≤ τ(n)² φ(n) max c(q) ≪ n^{1+ε}, c(q)=∏128j; (b) â(χ₀)=δ_t(n) and Σ_χ|â(χ)| ≤ (Σ_b a(b)²)^{1/2} ≪ n^{1/2+ε}. Full proof: reduction to W(ℓʲ) ≤ 128 j φ(ℓʲ); odd ℓ (pointwise r² ≤ 4ℓ^m, count 2ℓ^{j−m}); ℓ=2 (three cases by t mod 4; parity argument on u±b; 128(j−2)φ(2ʲ) for j≥3, W(2)=1, W(4)=8). One line after it: the constant is far from the truth, only c(q) ≪ q^ε is used.
10. **Lemma 8** (`lem:averaged`, was Lemma 7): error M^{1+ε} → M^{1/2+ε}; hypothesis |t| ≤ K **dropped** (audit F5); "uniformly in t" added; proof rewritten via the character expansion, citing Lemma 5 and Lemma 7(b).
11. **§7 proof of Theorem A**: item 4 error K^{1/2}M^{1/2+ε}T₁², relative K^{3(1−θ)−1/2}; final display; "θ>5/6 and ε<(θ−5/6)/3"; range sentence "M^{1/2}T₁² ≪ K^{1/2} … T₁³ ≪ K^{1/2}, that is θ>5/6".
12. **Prop. `prop:zf`**: statement 1−2a²/(1+4a), values 5/6, 47/48, 95/96. Proof: the Lemma 5 paragraph now bounds ψ(x,χ*) per primitive character under ZF(σ₀); Lemma 8 error K^{σ₀}M^{1/2+ε}; inequalities (1−θ)/a < μ < 2a−4(1−θ), nonempty iff (1−θ)(1+4a) < 2a²; the M ≤ K^{1/2} requirement justified correctly (audit F1): a μ ≤ 1/2 exists because the lower endpoint (1−θ)/a < 2a/(1+4a) < 1/2. Remark after it: 47/48, 95/96.
13. **§ Lean, "Not formalized"**: hard-coded "Lemmas 1–5 and 7" replaced by `\ref`s (numbering shifted); Lemma 7 (second moment) listed as elementary, checked numerically only.
14. **§ Numerics table**: new row for Lemma 7(a) — brute-force check of W(ℓʲ) bounds, multiplicativity of W, and (a) for n<200 plus 13 further n ≤ 1024, 0 ≤ t < 30; notes Σ_b a(b)² ≤ φ(n)τ(n)² throughout.
15. **§ Scope**: θ ≤ 7/8 → θ ≤ 5/6; "primes in progressions" → "character sums over primes".
16. **Use of AI tools**: mentions the independent review of the character-expansion argument (Lemmas 7–8). Wording is the author's call.

## Unchanged, deliberately

- Everything in §§3–4, §6 (Lemma 6), §8 (Theorem B), §9 (Lean), the end-to-end numerics (θ=0.9 was already in range), the bibliography (KL entry existed).
- The remaining "7/8" occurrences are all the zero-free half-plane Re s > 7/8 (abstract, Remark 5, §7.1, Prop. statement/remark, bibliography) and are correct.
- §7.1's discussion of the OpenAI/Liu announcements and the Quanta sentence: **not** trimmed here; that is a separate, non-mathematical edit (item 4 of the earlier review) for the author to decide.

## Open items for the author

- Verify the Kuan–Lesesvre sentence (exponent 1/3+ε; "harmonic/Petersson weights") against their Theorem 1; the `% VERIFY` comment marks it.
- Decide the wording of "Use of AI tools".
- Re-run the independent-recheck convention on Lemma 7 if the ledger requires two independent codes (only `second_moment_check.py` and the audit's probe script exist so far; both derive from the same definitions file).

---

## v10 rev 2 (2026-11-03, after `v10_review_2026-11-03.md`)

The review passed v10 (hand check of Lemmas 5, 7, 8, §7 budget, Prop. `prop:zf`; Kuan–Lesesvre Theorem 1 confirmed: Petersson weights, $K^{1/3+\varepsilon}\ll M\ll K^{1-\varepsilon}$; independent recheck of Lemma 7 with separate code, including part (b) directly). Its edits, applied to the same file:

17. `% VERIFY` comment removed (KL sentence confirmed).
18. **New Remark after Lemma 7**: Lemma 7(b) is sharp. For prime $p\nmid2t$, $a(b)=(\tfrac{t^2-4b^2}{p})$, $\hat a$ vanishes on odd characters, and $\hat a(\psi^2)=\overline\psi(t^2/4)(J+\chi_2(-1)\overline J)/(p-1)$ with $J=J(\chi_2,\overline\psi)$, $|J|=\sqrt p$; hence $\sum_\chi|\hat a(\chi)|\ge(p-3)/(2\sqrt p)$ and the Lemma 8 error (absolute values over characters and moduli) is of the true order $\gg M^{1/2}/\log M$. Widening $\theta>5/6$ through Lemma 8 would need cancellation between characters or moduli. **Verified independently** (`jacobi_sharpness_check.py`, written separately from the reviewer's `jacobi_probe.py`): identity to $10^{-9}$ at every even character, 23 primes $\le103$, all $t$; odd characters vanish; $S_2=p-3$; lower bound holds; observed ratio $\approx0.62\approx2/\pi$. Hand derivation: substitute $b^2=w$, split by $\chi_2(w)$, and use $J(\chi,\psi)=\chi(-1)J(\chi,\overline{\chi\psi})$.
19. **Remark (3)** after Theorem B now says the second-moment bound is sharp and names what a wider range would need.
20. **Numerics row for Lemma 7** corrected ("$\ell\le13$, $\ell^j\le2500$, $2^j\le256$") and extended with the recheck (all $n\le400$, every $t$ class; prime powers to $2^{12},3^7,5^5,7^4$; part (b) for $n\le160$) and the Jacobi check.

Compiles (16 pp, no errors/undefined refs). Files added to the project: `second_moment_recheck.py/.log`, `jacobi_probe.py/.log` (reviewer), `jacobi_sharpness_check.py/.log` (this pass), `v10_review_2026-11-03.md`.

Still open for the author: wording of "Use of AI tools"; the §7.1 trim; adding the check scripts to the GitHub repo and bumping the Zenodo release when the PDF is re-deposited.

---

## v10 rev 3 (2026-11-03, after the final check `v10_rev2_overview_2026-11-03.md`)

Rev 2 passed (sharpness remark re-derived from scratch; cross-references after renumbering; the explicit $\varepsilon<(\theta-5/6)/3$ with the $2\varepsilon(1-\theta)+8\varepsilon^2$ terms written out; numerics counts against the scripts). Three cosmetic edits applied:

21. Sharpness Remark: added that $|\hat a(\chi)|$ is independent of $t$ and equals $2\sqrt p|\cos\phi|/(p-1)$ or $2\sqrt p|\sin\phi|/(p-1)$ with $J=\sqrt p\,e^{i\phi}$, which is why the sum is $\approx(2/\pi)\sqrt p$ when the angles equidistribute.
22. Numerics row: "the 23 primes $11\le p\le103$, all $1\le t<p$".
23. Lemma 8 proof: tail $n\ge K^{1-\varepsilon}$ now stated as $O_A(K^{-A})$ with the one-clause reason (pre-existing imprecision, harmless).

Compiles, 16 pp. Mathematics closed. Remaining items are the author's: "Use of AI tools" wording; the §7.1 OpenAI/Liu/Quanta paragraph (a two-sentence replacement is drafted in the chat of 2026-11-03); push `second_moment_check.py`, `second_moment_check_extra.py`, `second_moment_recheck.py`, `jacobi_probe.py`, `jacobi_sharpness_check.py` and logs to the repo and mint a new Zenodo version — the DOI in `\CODEURL` is the v9 deposit.

---

## v10 rev 4 (2026-11-03) — remaining changelog items applied

Base: rev 3. The project's `murmurations_squares_10.tex` was still at rev 2, so the three rev-3 edits (21–23) were first re-applied to it from the rev-3 PDF text (a sentence-level diff of the rev-3 PDF against rev 2 showed exactly those three changes, so this is faithful); the rev-4 edits were then made on top. Compiles with latexmk, no errors or undefined references, 16 pp. A sentence-level diff of the rev-4 PDF against the rev-3 PDF shows exactly the four changes below and nothing else. The project `.tex` is now rev 4.

24. **§7.1 trim.** The paragraph on the OpenAI/Liu announcements is cut from nine sentences to four: the ZF(σ₀) definition; one sentence that a claimed proof of ZF(7/8) — stated for every Dirichlet $L$-function with $\zeta$ included, with a Lean formalization — and a shorter companion argument for ZF(11/12) were released by OpenAI in October 2026 [4], and that Liu [3] refines 7/8 to about 0.874957 by the same argument, changing the range only negligibly; "At the time of writing none of these results has been refereed."; and the unchanged sentence that Theorem A uses GRH only through Lemmas 4 and 5. Dropped: the description of their Theorem 1.1, the "pole at $s=1$" clause, Liu's $\mathbb Q(\sqrt{-3})$ route, and the *Quanta* sentence about expert opinion. The clause "with $\zeta$ included" is kept because the proof of Prop. 2 uses the principal character for the main term.
25. **Remark after Prop. 2:** the parenthetical "(the version experts have mainly checked)" removed, for the same reason.
26. **Reference [4]:** the "Secondary account: *Quanta Magazine* …" sentence removed; nothing cites it any more. (Easy to restore if wanted.)
27. **Use of AI tools:** "Further independent AI-agent reviews …" → "Independent reviews by separate AI-agent sessions, of the analytic and arithmetic parts and of the character-expansion argument of Lemmas 7–8 that gives the range θ>5/6, led to corrections that are incorporated here; the review notes and check scripts are included with the code." The last clause commits the repo to carrying the review notes and scripts (item 28).

**Not done here (needs the author's accounts):**

28. Push to `gifgaf0/prime-square-murmurations`: `second_moment_check.py`, `second_moment_check_extra.py`, `second_moment_recheck.py`, `jacobi_probe.py`, `jacobi_sharpness_check.py` with their `.log`s, and the review notes (`second_moment_lemma.md`, `second_moment_audit.md`, `v10_review_2026-11-03.md`, `v10_rev2_overview_2026-11-03.md`, this changelog). Suggested layout: `checks/second_moment/`, `checks/jacobi/`, `reviews/`.
29. New Zenodo version for the rev-4 PDF; then either update `\CODEURL` to the new version DOI or switch it to the concept DOI so it resolves to the latest version.
