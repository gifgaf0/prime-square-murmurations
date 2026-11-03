# Overview of murmurations_squares v10 rev2 (PDF, 16 pp) — 2026-11-03

Third pass after `second_moment_audit.md` (Lemma S) and `v10_review_2026-11-03.md` (v10). Read the full PDF; checked the new or changed material by hand against the `.tex`; left §§3–4, Theorem B, Lean and the end-to-end numerics as they were (unchanged since v9 and audited then).

**Verdict: nothing to fix mathematically. Ready for the author's remaining non-mathematical decisions.**

## Checked on this pass

- **Lemma 7 Remark (sharpness, new in rev2).** Re-derived: for $p\nmid2t$, $a(b)=(\tfrac{t^2-4b^2}{p})$, $\sum_ba(b)^2=p-3$; odd $\chi$ vanish ($a(b)=a(-b)$); for $\chi=\psi^2\ne\chi_0$, substituting $w=b^2$ and splitting by $\chi_2(w)$ gives $\overline\psi(t^2/4)\,[J(\chi_2,\overline\psi)+J(\chi_2,\chi_2\overline\psi)]/(p-1)$, and $J(\chi,\lambda)=\chi(-1)J(\chi,\overline{\chi\lambda})$ turns the second term into $\chi_2(-1)\overline J$. Matches the display. $|\hat a(\chi_0)|=|\delta_t(p)|\le2/(p-1)$ is within the stated max, so the lower bound $(p-3)/(2\sqrt p)$ stands. The conjugates ($\overline{\chi}(b)$ in 7(b), $\overline\psi$, $\overline J$) are present in the source; they are dropped only by PDF text extraction.
- **Lemma 5 (per-character form), Lemma 8, §7 budget, Prop. 2 and its $\mu\le1/2$ sentence**: re-read in the rev2 wording; all consistent with the earlier two reviews. The explicit $\varepsilon<(\theta-5/6)/3$ suffices even with the $2\varepsilon(1-\theta)+8\varepsilon^2$ terms written out.
- **Cross-references after renumbering** (Remark (3) → "Remark after Lemma 7"; Lean "Not formalized" list; AI-tools "Lemmas 7–8"; §2 "two places"; Scope): all point where they should.
- **Numerics row for Lemma 7**: counts match the scripts ($2^j\le256$ for the original; $2^{12},3^7,5^5,7^4$, $n\le400$, (b) for $n\le160$ for the recheck).

## Cosmetic (optional) — all three applied in rev3

1. Numerics row: "23 primes $p\le103$, all $t$" → "23 primes $11\le p\le103$, all $1\le t<p$" (that is what `jacobi_sharpness_check.py` runs).
2. Remark after Lemma 7: a clause explaining the $(2/\pi)\sqrt p$ would help a reader — $|\hat a(\psi^2)|$ does not depend on $t$, and $|J+\chi_2(-1)\overline J|=2\sqrt p\,|\cos\phi_\psi|$ or $2\sqrt p\,|\sin\phi_\psi|$, whose mean over equidistributed Jacobi angles is $2/\pi$ (times the $(p-3)/2$ even non-principal characters, over $p-1$).
3. Lemma 8 proof, first sentence: the tail is $\exp(-K^{1/2-\varepsilon})$ times a power of $K$; harmless since $\varepsilon$ is arbitrary, but "$O(\exp(-K^{1/2-2\varepsilon}))$" is literally true. Pre-existing.

## rev3 (same day) — reviewed

Sentence-level diff rev2 → rev3 shows exactly three changes, the three items above:
- Remark after Lemma 7: new sentence on $t$-independence of $|\hat a(\chi)|$, the $|\cos\phi|$ / $|\sin\phi|$ split by $\chi_2(-1)$, and $(2/\pi)\sqrt p$ under equidistribution of the angles ("as they do numerically"). Checked: correct; the hedge is safe (equidistribution of Jacobi-sum angles is in fact a theorem of Katz, not needed here).
- Lemma 8 proof: tail now "$O_A(K^{-A})$, since there $e^{-n/M}\le e^{-K^{1/2-\varepsilon}}$ and everything else is polynomial in $K$." Correct ($n/M\ge K^{1-\varepsilon}/K^{1/2}$); cleaner than the suggestion.
- Numerics row: "the 23 primes $11\le p\le103$, all $1\le t<p$". Matches the script.

Nothing else changed; 16 pp. **rev3 passes.** Remaining items are the non-mathematical ones below.

## Still open for the author (unchanged from the changelog)

- §7.1: the paragraph on the OpenAI/Liu announcements and the *Quanta* sentence is the one place a referee is likely to object (secondary-source appeal, news register). Two sentences with the citations would do; Prop. 2 and its Remark carry the mathematical content.
- Wording of "Use of AI tools".
- Add `second_moment_check.py`, `second_moment_check_extra.py`, `second_moment_recheck.py`, `jacobi_probe.py`, `jacobi_sharpness_check.py` and logs to the GitHub repo; new Zenodo version when the PDF is re-deposited (the DOI in the paper is the v9 deposit).
