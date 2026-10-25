# Prime-square murmurations in the weight aspect

Code, logs and Lean formalization for

> Matthew Gifford, *Murmurations of Hecke eigenvalues at prime squares in the weight aspect* (October 2026).

The paper proves two results about the root-number-weighted average of λ_f(p²) over level-one eigenforms:

- **Theorem A** (assuming GRH for Dirichlet L-functions): the average converges to an explicit limit.
- **Theorem B** (unconditional): that limit equals an ordered sum of point masses at y = (c/m)², weighted by averages of Kloosterman sums S(a², 1; c).

This repository contains:

- the Lean 4 formalization of the unconditional part (`lean/`);
- the numerical checks of every identity in the argument, with their logs (`proof/`);
- one script that rebuilds and checks both (`check.sh`).

## Rebuild and check everything

```sh
./check.sh
```

That one command:

1. fetches the pinned Mathlib and builds the Lean project;
2. re-elaborates `LocalDensities.lean` and audits its `#print axioms` output;
3. creates a Python virtual environment from `requirements.txt`;
4. runs every numerical check and compares each output line with the committed log.

It exits non-zero if any step fails. New outputs go to `build/logs/`. The committed logs in `proof/` are never overwritten.

| Option | What runs | Time on a 2-core machine |
|---|---|---|
| `./check.sh` | everything | about 30 minutes of numerics, plus the Lean build |
| `./check.sh --quick` | everything except the three slow end-to-end runs | about 17 minutes of numerics, plus the Lean build |
| `./check.sh --lean` | the Lean part only | a few minutes with the Mathlib cache |
| `./check.sh --python` | the numerical checks only | as above |

The slow runs are `thmA_numeric`, `a_minus_pred` and `arith_s4`.

**Requirements.**
- [elan](https://github.com/leanprover/elan), which installs the pinned Lean toolchain automatically.
- Python ≥ 3.10.
- git and curl.

`lake exe cache get` downloads prebuilt Mathlib in a few minutes. If that download is unavailable, `lake build` compiles the needed part of Mathlib from source, which takes several hours.

## Lean formalization

| | |
|---|---|
| File | `lean/PrimeSquareMurmurations/LocalDensities.lean` (3,407 lines) |
| Lean | `leanprover/lean4:v4.36.0-rc1` (`lean/lean-toolchain`) |
| Mathlib | commit [`4dc43842a11f257ffba2a611c943a133a65cb4b2`](https://github.com/leanprover-community/mathlib4/commit/4dc43842a11f257ffba2a611c943a133a65cb4b2) (master, 23 October 2026), pinned in `lean/lakefile.toml` and `lean/lake-manifest.json` |

The paper says the file was checked against "Mathlib of 23 October 2026". The lockfile from that original check was not kept. The pin above is the last Mathlib master commit dated 23 October 2026 (UTC). Every master commit that day uses `v4.36.0-rc1`. `./check.sh` was run against this pin on 24 October 2026: the file compiles, and the axiom audit below passes. Lake prints warnings that the file is not in Lean's new `module` system. These are expected for a single-file project and do not affect the check.

The file contains no `sorry`, `admit` or `native_decide`. `scripts/check_lean_output.py` confirms this. It also confirms that all 26 `#print axioms` reports at the end of the file list only `propext`, `Classical.choice` and `Quot.sound`.

| Lean name | Statement (paper numbering) |
|---|---|
| `nuSum_odd`, `nuSum_two` | φ(ℓⁱ)ν_t(ℓⁱ) for every prime ℓ (including 2) and every i ≥ 1, from the definition of N_q |
| `hasSum_E_odd`, `hasSum_E_two` | the Euler factors E_ℓ(t) = Σ_j δ_t(ℓʲ)ℓ⁻ʲ of Lemma 6 |
| `KS_formula` | Lemma 8(a): Σ_a S(a², 1; c) for every c ≥ 1 and every primitive additive character mod c |
| `local_identity_odd`, `local_identity_two` | Lemma 8(b) at every prime |
| `global_identity` | for t ≠ 0, Σ_c G(c)c_c(t) converges absolutely and equals Π_p E_p(t) |
| `Gc_eq` | G(c) = A₂(c)c⁻² Π_{ℓ∣c}(1 − ℓ⁻²)⁻¹, with A₂ defined through Kloosterman sums |
| `sum_norm_gc_le` | Σ_c \|G(c)c_c(t)\| ≤ 2\|t\|e^{C₀} for t ≠ 0 |
| `tendsto_sum_wA` | Σ_{c≤C} G(c)φ(c) → π/4 |
| `poisson_coprime` | Σ_{m∈ℤ, (m,c)=1} f(m/c) = Σ_{t∈ℤ} f̂(t)c_c(t) for Schwartz f |
| `theoremB` | Theorem B |

Not formalized: Theorem A, Lemmas 1–5 and 7, and Proposition 1. These need the Eichler–Selberg trace formula, class-number L-values and GRH, which are not in Mathlib.

`LocalCounts.lean` is the earlier set of finite `native_decide` checks of the Lemma 6 point counts (ℓ ≤ 13). The general proofs in `LocalDensities.lean` supersede it. It is kept for the record and is not part of the default build or the audit. It imports all of Mathlib. To build it:

```sh
cd lean && lake build PrimeSquareMurmurations.LocalCounts
```

## Numerical checks

Each check is listed in `scripts/checks.tsv` with its exact command line. Each one runs in a scratch copy of `proof/`.

**How outputs are compared.** Where a reference log exists, every printed number must match it.
- Numbers must agree to a relative 1e-6.
- Round-off-sized residuals (both below 1e-9) count as agreeing.
- Timing fields are ignored.

Checks without a reference log must run without error. Their output is kept in `build/logs/`.

PARI/GP (through `cypari`) supplies traces, class numbers and L-values. The local densities are computed in exact rational arithmetic.

| Check (`proof/…`) | What it tests | Paper |
|---|---|---|
| `exact_checks.py` → `exact_checks.log` | Poisson closed form of the weight sum; extra terms and D_K; Zagier's local factors (796 pairs); H(\|Δ\|) = √\|Δ\|/π · L(1,Δ); per-prime identity at K = 2000 | Lemmas 2, 3, Prop. 1 |
| `local.py` → `local.log` | local densities by brute force against the table and the Ramanujan side (ℓ ≤ 13) | Lemmas 6, 8 |
| `local_k.py 1`, `local_k.py 2` | the same for Δ = t² − 4bᵏ; k = 1 reproduces Bober–Booker–Lee–Lowry-Duda | Lemma 6 |
| `f2.py 20000 24000` → `f2.log` | Euler product f₂(t) against prime averages of L(1, t² − 4p²), 406 primes | Lemma 6 |
| `thmB.py` → `thmB.log` | t-series against point masses, c ≤ 60000; squares, primes, A₁ masses | Theorem B, §1.2 |
| `limit_tm.py` → `limit_tm.log` | convergence of the t-series; limit −1.7077790 for the bump on [8, 10] | Theorem A |
| `pred_kappa.py` → `pred_kappa.log` | finite-K main term → limit, error ≈ 0.79κ² | Theorem A |
| `thmA_numeric.py` → `thmA_numeric.log` | end to end, K = 10⁴ … 10⁶: M(K) from class numbers vs A(K) vs the main term | §10 table |
| `a_minus_pred.py` | the same average over all integers matches the main term to 1e-8 | §10 |
| `review_arith/s1`–`s7` | independent recheck of Lemmas 6, 8 and Theorem B (own code) | §10 "recheck" |
| `review_analysis/chk_*.py` | independent recheck of Lemmas 1–4, 6, 7, Prop. 1 and the error exponents (own code) | §10 "recheck" |

**One documented difference from a committed log.** In `thmA_numeric.log` the printed limit is −1.707745, but a rerun prints −1.707779.
- The log was written when `limit()` summed the t-series to |t| ≤ 600. The script now sums to |t| ≤ 3000.
- `limit_tm.log` shows both values: −1.7077455 at t ≤ 600 and −1.7077790 at t ≤ 3000. The paper uses −1.7077790.
- Every M(K), A(K) and main-term value in the log reproduces exactly.
- The log is kept as it was. `checks.tsv` declares this one substitution, and the runner reports it each time.

**The review scripts test the drafts they were given.** The reviews found errors that were then corrected in the paper, so a few of these scripts still print the discrepancies they found. For example, `chk_lemma3.py` (b) flags the r = 1 Hensel count, which the paper now states correctly. `chk_lemma2.py` also tests small θ on purpose, outside the range of the theorem. These scripts have no committed logs. The runner only requires that they run; their output in `build/logs/` is meant to be read.

The two `review_*` folders also contain the version of the proof each independent review was given (`proof_doc.md`, `doc.md`, `companion.md`).

`arith_s4` reads `f2_consts.npy`, which `arith_s3` writes, so run them in that order. `run_checks.py` already does.

## Layout

```
check.sh                    one command: build + check everything
requirements.txt            Python packages (pinned)
lean/
  lean-toolchain            leanprover/lean4:v4.36.0-rc1
  lakefile.toml             Mathlib pinned by commit
  lake-manifest.json        exact revisions of Mathlib and its dependencies
  PrimeSquareMurmurations.lean
  PrimeSquareMurmurations/LocalDensities.lean   the formalization
  PrimeSquareMurmurations/LocalCounts.lean      earlier finite checks (not built by default)
proof/                      numerical scripts and their logs
  review_analysis/          independent recheck: analytic lemmas
  review_arith/             independent recheck: arithmetic lemmas and Theorem B
scripts/
  checks.tsv                list of numerical checks and their reference logs
  run_checks.py             runs them and compares with the logs
  check_lean_output.py      axiom / sorry audit of the Lean output
```

## Use of AI tools

As stated in the paper, this work was carried out by the author with an AI assistant (Claude, Anthropic). The assistant drafted the proofs and wrote the numerical code and the Lean formalization, under the author's direction. The author takes responsibility for the content.
