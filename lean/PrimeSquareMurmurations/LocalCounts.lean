import Mathlib

/-!
# Lemma 6 point counts: exact machine checks

First file of the Lean formalization of "Prime-square murmurations: a proof under GRH".

Definitions:
* `Nq q D`   = #{x mod 2q : x² ≡ D (mod 4q)}            (Zagier's N_q(Δ))
* `nuSum t q` = Σ over units b mod q of N_q(t² − 4b²)     (= φ(q) · ν_t(q))

The point counts in the proof of Lemma 6 say
* odd ℓ, ℓ ∤ t : φ(ℓ^i) ν_t(ℓ^i) = ℓ^(i−1) (ℓ − 2 − χ(ℓ))
* odd ℓ, ℓ | t : φ(ℓ^i) ν_t(ℓ^i) = ℓ^(i−1) (ℓ − 1)(1 + χ(ℓ))
* ℓ = 2        : 0 for t odd; 1 or 2^i for 2 ∥ t (i = 1 or i ≥ 2); 1 or 0 for 4 | t.

Here they are checked exactly for every residue t, for ℓ ≤ 13 and small i. These are
finite checks (`native_decide`), not yet the general proofs, which come in the next file.
-/

namespace Murmurations

/-- `Nq q D = #{x mod 2q : x² ≡ D (mod 4q)}` (Zagier's `N_q(Δ)`). -/
def Nq (q : ℕ) (D : ℤ) : ℕ :=
  ((Finset.range (2 * q)).filter (fun x : ℕ => ((x : ℤ) ^ 2 - D) % (4 * (q : ℤ)) = 0)).card

/-- `nuSum t q = Σ_{b mod q, gcd(b, q) = 1} N_q(t² − 4b²)`, i.e. `φ(q) · ν_t(q)`. -/
def nuSum (t : ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter (fun b => Nat.Coprime b q)).sum
    (fun b => Nq q (t ^ 2 - 4 * (b : ℤ) ^ 2))

/-- The character χ₋₄ on natural numbers. -/
def chi4 (l : ℕ) : ℤ := if l % 4 = 1 then 1 else if l % 4 = 3 then -1 else 0

/-- Odd primes ℓ ≤ 13, exponents i = 1, 2, every residue t mod 2ℓ^i. -/
theorem nuSum_odd_check :
    ∀ l ∈ ({3, 5, 7, 11, 13} : Finset ℕ), ∀ i ∈ Finset.Icc 1 2,
      ∀ t ∈ Finset.range (2 * l ^ i),
        (nuSum (t : ℤ) (l ^ i) : ℤ) =
          if t % l = 0 then (l : ℤ) ^ (i - 1) * ((l : ℤ) - 1) * (1 + chi4 l)
          else (l : ℤ) ^ (i - 1) * ((l : ℤ) - 2 - chi4 l) := by
  native_decide

/-- The same for ℓ = 3 and 5 with i = 3 (moduli 27 and 125). -/
theorem nuSum_odd_check_cube :
    ∀ l ∈ ({3, 5} : Finset ℕ), ∀ t ∈ Finset.range (2 * l ^ 3),
        (nuSum (t : ℤ) (l ^ 3) : ℤ) =
          if t % l = 0 then (l : ℤ) ^ 2 * ((l : ℤ) - 1) * (1 + chi4 l)
          else (l : ℤ) ^ 2 * ((l : ℤ) - 2 - chi4 l) := by
  native_decide

/-- ℓ = 2, exponents i = 1 … 6, every residue t mod 2^(i+1). -/
theorem nuSum_two_check :
    ∀ i ∈ Finset.Icc 1 6, ∀ t ∈ Finset.range (2 * 2 ^ i),
      nuSum (t : ℤ) (2 ^ i) =
        if t % 2 = 1 then 0
        else if t % 4 = 2 then (if i = 1 then 1 else 2 ^ i)
        else (if i = 1 then 1 else 0) := by
  native_decide

end Murmurations
