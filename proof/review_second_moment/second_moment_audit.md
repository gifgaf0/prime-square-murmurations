# Audit of `second_moment_lemma.md` (Lemma S) — 2026-11-03

**Scope.** The note, its check script and log, read against `murmurations_squares (9).tex` (Lemmas 3, 5, 6, 7; Section 7; Prop. `prop:zf`). Every step of Sections 2–6 of the note was re-derived by hand; the script was re-run (log reproduces, `ALL OK`), and five further probes were run (`second_moment_check_extra.py`, log attached).

**Verdict.** Lemma S, its Corollary, and Lemma 7′ are correct as written. The derivation of $\theta>5/6$ and of the $\mathrm{ZF}(\sigma_0)$ range $(1-\theta)(1+4a)<2a^2$ is correct. No mathematical error found. Four presentation/justification issues and one list of paper-wide edits follow; none affects the result.

---

## 1. Findings

### F1 (justification, Prop. `prop:zf` consequence) — "The requirement $\mu<a\le1/2$ still holds" is the wrong reason
The new upper endpoint $2a-4(1-\theta)$ is **not** $\le a$ in general (for $a=1/2$ and $\theta\to1$ it tends to $1$). The actual constraint is $M\le K^{1/2}$, i.e. $\mu\le1/2$, and what has to be checked is that the interval $\big((1-\theta)/a,\ 2a-4(1-\theta)\big)$ meets $(0,1/2]$. It does: under the existence condition, $(1-\theta)/a<2a/(1+4a)<1/2$. Replace the sentence by: *"A $\mu\le1/2$ can be chosen, since $(1-\theta)/a<2a/(1+4a)<1/2$; so $M\le K^{1/2}$ as Lemma 7 requires."*

### F2 (reporting, §8) — the "max ratio exactly 1.0" is the trivial $n=1$ case
$S_2(1,t)=N_1(\Delta)^2=1$ for every $t$, so the ratio is $1$ at $n=1$ by definition. For $n\ge2$ the maximum of $S_2/(\varphi(n)\tau(n)^2)$ over the tested range is $4/9$ (attained at $n=4$, $t\equiv2\bmod4$). The conclusion "the $128^{\omega}$ is pure slack" stands, but the number quoted should be the $n\ge2$ one, or the text should say the $1.0$ is $n=1$.

### F3 (coverage, script) — the displayed 2-adic claims are not the ones tested
The proof derives $W(2^j)\le128\,(j-2)\,\varphi(2^j)$ for $j\ge3$ and the exact values $W(2)=1$, $W(4)=8$ when $2\parallel t$; the script tests only the weaker $(\ast)$ and the $t$ odd / $4\mid t$ rows. Probe (A) tests all three: pass for $j\le9$. Suggest folding probe (A) into `second_moment_check.py` so the log covers every displayed inequality. Observed $W(2^j)/\varphi(2^j)$ for $2\parallel t$: $4,8,8,16,24,32,40$ for $j=3,\dots,9$ — linear in $j$, so the $j$-dependence of $c(q)$ is real and only the constant is loose. Same picture at odd $\ell$ (probe C): $\max W(\ell^j)/\varphi(\ell^j)\approx 2j-1+O(1/\ell)$ against the proved $4(1+2j\ell^j/\varphi(\ell^j))$.

### F4 (audit point 2) — multiplicativity of $N_q$ with an even factor: confirmed, and stronger than needed
For odd $q_1$ and any $q_2$ coprime to it, $N_{q_1}(\Delta)=r_{q_1}(\Delta)\cdot[\Delta\equiv0,1\ (4)]$ and $N_{q_1q_2}(\Delta)=r_{q_1}(\Delta)\,N_{q_2}(\Delta)$ (CRT on $x\bmod 2q_1q_2\leftrightarrow(x\bmod q_1,\ x\bmod 2q_2)$, and $x^2\bmod 4q_2$ depends on $x\bmod 2q_2$). Since $N_{q_2}(\Delta)=0$ whenever the bracket is $0$, $N_{q_1q_2}=N_{q_1}N_{q_2}$ for **every** $\Delta\bmod4q$, not only discriminants. Probe (D) checks this exhaustively over all $D\bmod 4q$ for $(3,4),(5,8),(9,16),(7,2),(3,32)$: pass. The paper's Lemma 3(3) proof is the single phrase "definition and CRT"; the two-line argument above is worth adding there, since Lemma S now leans on it.

### F5 (audit point 8) — $|t|\le K$ in Lemma 7
Confirmed that nothing in the revised argument uses it. Note also that the **current** proof of Lemma 7 never uses it either (the $n\ge K^{1-\varepsilon}$ tail uses only $M\le K^{1/2}$ and $|a_\Delta(n)|\ll n^{1/2+\varepsilon}$). It can be dropped from the statement outright.

---

## 2. Audit points 1–9, answered

| # | Point | Result |
|---|---|---|
| 1 | Step 2 descent | ✓ $N_q$ depends on $\Delta\bmod4q$ (definition); $4b^2\bmod4q$ depends on $b\bmod q$; reduction of unit groups is onto with fibres $\varphi(n)/\varphi(q)$. |
| 2 | Multiplicativity, even factor | ✓ see F4. |
| 3 | 3(b) two cases | ✓ $\ell^j\mid\Delta$: $r=\ell^{\lfloor j/2\rfloor}$, $r^2\le\ell^j=\ell^m$. $v<j$: $v_\ell(x^2)=v$ forced (else $v_\ell(x^2-\Delta)=\min\le v<j$), $v$ even, Hensel gives $1+(\tfrac u\ell)$ roots mod $\ell^{j-v}$, $\ell^{v/2}$ lifts each; $r^2\le4\ell^v=4\ell^m$. Both cases cover $m=\min(v,j)$. |
| 4 | 4(c) parity | ✓ $u\pm b$ both even, sum $2u$ has $v_2=1$, so exactly one factor has $v_2=1$; the other has $v_2=v-1\ge m-1$. Classes $\pm u\bmod2^{m-1}$ disjoint iff $m\ge3$ (given). $m-1\le j$ since $m\le j$. |
| 5 | Odd square roots mod $2^k$ | ✓ $k=1$: 1; $k=2$: 2 or 0; $k\ge3$: 4 or 0. Max 4. |
| 6 | Lossy steps | ✓ all one-directional; only $c(q)\ll q^\varepsilon$ is used downstream. |
| 7 | Corollary normalisation | ✓ with $\hat a(\chi)=\varphi(n)^{-1}\sum_b a(b)\bar\chi(b)$: $\sum_\chi|\hat a|^2=\varphi(n)^{-1}\sum_b|a|^2$, C–S over $\varphi(n)$ characters gives $\sum_\chi|\hat a|\le S_2^{1/2}$; $\hat a(\chi_0)=\delta_t(n)$ matches the paper's definition in §2. Inversion $a=\sum_\chi\hat a(\chi)\chi$ holds with this normalisation. |
| 8 | §6 analytic inputs | ✓ GRH: $\psi(x,\chi^*)\ll x^{1/2}\log^2(nx)$ for primitive $\chi^*$ (Davenport ch. 20, same citation as Lemma 5); imprimitive correction $\le\sum_{p\mid n}\log p\cdot\lfloor\log x/\log p\rfloor\le\omega(n)\log x$; prime powers $\ll x^{1/2}$; partial summation against $g$ with $\int|g'|\le V(g)$. $|t|\le K$: see F5. |
| 9 | ZF per-character | ✓ the paper's bound $\sum_{|\gamma|\le T}|x^\rho/\rho|\ll x^{\sigma_0}\log^2(qT)$ is applied to each primitive $L(s,\chi)$; the imprimitive and $\psi\to\theta$ corrections are the same as under GRH. |

Exponent bookkeeping, checked: item 4 relative error $=K^{-1/2}M^{1/2+\varepsilon}T_1^2=K^{3(1-\theta)-1/2+6\varepsilon+2\varepsilon(1-\theta)+8\varepsilon^2}$; $\varepsilon<(\theta-5/6)/3$ still suffices. $\mathrm{ZF}$: $\mu>(1-\theta)/a$ (item 3), $\mu<2a-4(1-\theta)$ (item 4); nonempty iff $(1-\theta)(1+4a)<2a^2$; $a=1/2,1/8,1/12\Rightarrow\theta>5/6,\ 47/48,\ 95/96$. ✓

---

## 3. Paper-wide edits implied by Lemma 7′ (not listed in the note's §6)

1. **Abstract:** $7/8\to5/6$, $79/80\to47/48$, $167/168\to95/96$.
2. **§1 "What is new":** the sentence "The price is the range $\theta>7/8$, against $\theta>5/6$ in [BBLL]" is now false; the range equals BBLL's. Say so plainly (same mechanism: character expansion of the class-mod-$n$ coefficients plus Plancherel), and do not phrase it as an improvement over BBLL.
3. **Remarks (3) and (5)** after Theorem B; **§2** first paragraph ("$7/8<\theta<1$"); **Scope §** ("$\theta\le7/8$").
4. **§2 "GRH enters in exactly two places"** — stays true only if the character-sum bound is housed in Lemma 5. Recommended: restate Lemma 5 as *for $\chi\neq\chi_0$ mod $r$, $\sum_p(\log p)g(p)\chi(p)\ll V(g)Y_2^{1/2}\log^2(rY_2)$, and for $\chi_0$ the main term $\int g$* — the progression form then follows by orthogonality, and Lemma 7′'s proof cites Lemma 5 rather than Davenport directly. The paper's existing proof of Lemma 5 already goes through $\psi(x,\chi)$, so this is a restatement, not new work.
5. **Lemma 7 statement:** error term $M^{1/2+\varepsilon}$; drop $|t|\le K$ (F5).
6. **§7 (`sec:thmA`):** item 4 and the final display ($K^{4(1-\theta)-1/2}\to K^{3(1-\theta)-1/2}$); "$\theta>7/8$ and $\varepsilon<(\theta-7/8)/3$" $\to$ "$\theta>5/6$ and $\varepsilon<(\theta-5/6)/3$"; "the prime sums need $MT_1^2\ll K^{1/2}$ … $T_1^4\ll K^{1/2}$" $\to$ "$M^{1/2}T_1^2\ll K^{1/2}$ … $T_1^3\ll K^{1/2}$".
7. **Prop. `prop:zf`:** statement $1-a^2/(1+2a)\to1-2a^2/(1+4a)$ with the three new values; proof: "the proof of Lemma 7 gives … $M^{1+\varepsilon}$" $\to M^{1/2+\varepsilon}$; the two inequalities; the final sentence per F1. The Remark after it: $79/80\to47/48$, $167/168\to95/96$.
8. **§ Numerics:** unaffected ($\theta=0.9>7/8$ already). **Lean section:** unaffected (Lemma 7 was never formalized). **"Use of AI tools":** unchanged.

---

## 4. Files
- `second_moment_check.py` / `.log` — re-run, reproduces (`ALL OK`, 7.9 s here).
- `second_moment_check_extra.py` / `.log` — probes A–E above, all pass.
