import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral

open Finset

namespace Murmurations

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lemma 6: the local point counts, general proof (odd primes and ℓ = 2)

For an odd prime p, i ≥ 1 and t mod p^i:
  Σₓ #{y unit mod p^i : y² = t² − x²}
    = p^(i−1) (p − 2 − χ(−1))        if p ∤ t,
    = p^(i−1) (p − 1)(1 + χ(−1))     if p ∣ t,
where χ is the quadratic character mod p (so χ(−1) = χ₋₄(p)).  Main theorems:
* `count_odd`: the count above, for t mod p^i;
* `nuSum_odd`: the same statement for `nuSum`, the original counting of `LocalCounts.lean`
  (Σ over units b mod q of #{x mod 2q : x² ≡ t² − 4b² (mod 4q)}), for every integer t.
* `nuSum_two`: the case ℓ = 2: for i ≥ 1 and every integer t, `nuSum t (2^i)` is
  0 if t is odd; 1 (i = 1) or 2^i (i ≥ 2) if t ≡ 2 (mod 4); 1 (i = 1) or 0 (i ≥ 2) if 4 ∣ t.
  The main case (t ≡ 2 mod 4, i ≥ 3) uses that y² = 1 has exactly four solutions mod 2^i
  and that a unit c mod 2^i has 4 or 0 unit square roots according as c ≡ 1 (mod 8) or not.
Lemma 8(a), local values (for any primitive additive character ψ with values in a domain of
characteristic 0, e.g. x ↦ e(x/c) in ℂ), for the sum Σ_{a unit} S(a², 1; c) with
S(m, 1; c) = Σ_{x unit} ψ(m x + x⁻¹):
* `kloosterman_sum_odd_prime`: c = p odd prime: χ(−1) p + 1, i.e. A₂(p) = (1 + χ₋₄(p) p)/(p − 1);
* `kloosterman_sum_odd_prime_pow`: c = ℓ^j, ℓ odd, j ≥ 2: 0;
* `kloosterman_sum_two`, `_four`, `_eight`, `kloosterman_sum_two_pow`: c = 2, 4, 8, 2^j (j ≥ 4):
  1, −4, 0, 0, i.e. A₂(2) = 1, A₂(4) = −2, A₂(2^j) = 0 for j ≥ 3.
Lemma 6 Euler factors and Lemma 8(b), with ν_t(q) = nuSum t q / φ(q) (`nuQ`, ν_t(1) = 1 by
`nuQ_one`), δ_t(ℓ^j) = Σ_{i ≤ j} (−1)^(j−i) ν_t(ℓ^i) (`deltaQ`) and E_ℓ(t) = Σ_j δ_t(ℓ^j) ℓ^(−j):
* `hasSum_E_odd`: E_p(t) = (1 + (ν − 1)/p)/(1 − p⁻²), with ν = 1 + χ₋₄(p) if p ∣ t and
  (p − 2 − χ₋₄(p))/(p − 1) otherwise — the odd rows of the table in Lemma 6;
* `hasSum_E_two`: E_2(t) = 2/3, 5/3, 1 for t odd, 2 ∥ t, 4 ∣ t;
* `local_identity_odd`: E_p(t) = 1 + G(p) c_p(t) with G(p) = A₂(p)/(p² − 1), A₂ the Kloosterman
  average and c_p the Ramanujan sum (both written with an arbitrary primitive additive character);
* `local_identity_two`: E_2(t) = 1 + G(2) c_2(t) + G(4) c_4(t), G(2) = A₂(2)/3, G(4) = A₂(4)/12.
The higher terms G(ℓ^j) vanish by the Lemma 8(a) theorems above.
Multiplicativity of Lemma 8(a):
* `KS_mul`: by the Chinese remainder theorem, for coprime m, n the sum mod mn is the product of
  the sums mod m and mod n (for suitable primitive characters on the factors);
* `KS_formula`: for every c ≥ 1 and every primitive ψ mod c,
  Σ_{a unit} S(a², 1; c) = Π_{p^k ∥ c} localK p k, i.e. A₂ = KS/φ is multiplicative with the
  local values of the doc.
This file is self-contained: it repeats the definitions `Nq`, `nuSum`, `chi4` of `LocalCounts.lean`.
-/

/-- Number of square roots of `a`, as a filtered `Finset`. -/
lemma card_sq_eq (hF : ringChar F ≠ 2) (a : F) :
    ((#{x : F | x ^ 2 = a} : ℕ) : ℤ) = quadraticChar F a + 1 := by
  simpa [Set.toFinset_ofPred] using quadraticChar_card_sqrts hF a

/-- Summing a function of `x²` over `x`. -/
lemma sum_sq (hF : ringChar F ≠ 2) (f : F → ℤ) :
    ∑ x : F, f (x ^ 2) = ∑ u : F, (quadraticChar F u + 1) * f u := by
  have h := Finset.sum_fiberwise' (univ : Finset F) (fun x : F => x ^ 2) f
  rw [← h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_sq_eq hF u]

/-- `∑ₓ χ(a − x²) = −χ(−1)` for `a ≠ 0` (a Jacobi sum). -/
lemma sum_chi_sub_sq (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ x : F, quadraticChar F (a - x ^ 2) = -quadraticChar F (-1) := by
  set χ := quadraticChar F with hχdef
  have h1 := sum_sq hF (fun u => χ (a - u))
  rw [h1]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  have h2 : ∑ u : F, χ (a - u) = 0 := by
    rw [← quadraticChar_sum_zero hF]
    exact Fintype.sum_equiv (Equiv.subLeft a) _ _ (fun u => rfl)
  rw [h2, add_zero]
  have h3 : ∑ u : F, χ u * χ (a - u) = jacobiSum χ χ := by
    rw [jacobiSum]
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun w => ?_)
    show χ w * χ (1 - w) = χ (a * w) * χ (a - a * w)
    rw [show a - a * w = a * (1 - w) by ring, map_mul, map_mul]
    have hsq : χ a ^ 2 = 1 := quadraticChar_sq_one ha
    linear_combination (-(χ w * χ (1 - w))) * hsq
  rw [h3]
  have hinv : χ⁻¹ = χ := (quadraticChar_isQuadratic F).inv
  calc jacobiSum χ χ = jacobiSum χ χ⁻¹ := by rw [hinv]
    _ = -χ (-1) := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)

/-- The weight `G(u)`: the number of nonzero square roots of `u`. -/
def G (u : F) : ℤ := if u = 0 then 0 else quadraticChar F u + 1

lemma G_eq (u : F) : G u = quadraticChar F u + 1 - (if u = 0 then 1 else 0) := by
  unfold G; split_ifs with h <;> simp [h]

/-- The base count over the field: `∑ₓ G(t² − x²)`. -/
theorem base_sum (hF : ringChar F ≠ 2) (t : F) :
    ∑ x : F, G (t ^ 2 - x ^ 2) =
      if t = 0 then ((Fintype.card F : ℤ) - 1) * (quadraticChar F (-1) + 1)
      else (Fintype.card F : ℤ) - 2 - quadraticChar F (-1) := by
  simp only [G_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcnt : ∑ x : F, (if t ^ 2 - x ^ 2 = 0 then (1 : ℤ) else 0) = quadraticChar F (t ^ 2) + 1 := by
    rw [Finset.sum_boole, ← card_sq_eq hF (t ^ 2)]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> linear_combination -h
  rw [hcnt]
  split_ifs with ht
  · subst ht
    have hs : ∑ x : F, quadraticChar F (0 ^ 2 - x ^ 2) =
        ∑ x : F, (if x = 0 then 0 else quadraticChar F (-1)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · simp [hx]
      · rw [show (0 : F) ^ 2 - x ^ 2 = -1 * x ^ 2 by ring, map_mul, quadraticChar_sq_one' hx,
          mul_one]
    rw [hs, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have hc : (#{x : F | ¬x = 0} : ℤ) = (Fintype.card F : ℤ) - 1 := by
      rw [Finset.filter_ne' univ (0 : F), Finset.card_erase_of_mem (mem_univ _), Finset.card_univ]
      have : 1 ≤ Fintype.card F := Fintype.card_pos
      push_cast [this]
      ring
    rw [hc]
    simp
    ring
  · rw [sum_chi_sub_sq hF (pow_ne_zero 2 ht), quadraticChar_sq_one' ht]
    ring

end FiniteField

section PrimePower

variable (p : ℕ) [hp : Fact p.Prime] (i : ℕ) [NeZero (p ^ i)]

/-- Reduction `ZMod (p ^ i) → ZMod p`. -/
abbrev red (hi : i ≠ 0) : ZMod (p ^ i) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hi) (ZMod p)

omit [NeZero (p ^ i)] in
lemma isUnit_iff_red_ne_zero (hi : i ≠ 0) (c : ZMod (p ^ i)) :
    IsUnit c ↔ red p i hi c ≠ 0 := by
  constructor
  · intro h
    exact (h.map (red p i hi)).ne_zero
  · intro h
    have : NeZero p := ⟨hp.out.ne_zero⟩
    have := ZMod.isLocalHom_castHom_pow (n := p) hi
    exact isUnit_of_map_unit (red p i hi) c (isUnit_iff_ne_zero.mpr h)

lemma red_two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

/-- Unit square roots of `c`: `#{y | y unit, y² = c}`. -/
def Nu (hi : i ≠ 0) (c : ZMod (p ^ i)) : ℕ :=
  #{y ∈ ({y : ZMod (p ^ i) | red p i hi y ≠ 0} : Finset _) | y ^ 2 = c}

lemma G_nonneg (u : ZMod p) : 0 ≤ G u := by
  unfold G
  split_ifs with h
  · exact le_rfl
  · rcases quadraticChar_dichotomy h with h1 | h1 <;> rw [h1] <;> norm_num

omit [NeZero (p ^ i)] in
/-- Two unit square roots differ by a sign. -/
lemma sq_eq_sq_unit (hp2 : p ≠ 2) (hi : i ≠ 0) {y y₀ : ZMod (p ^ i)}
    (hy₀ : red p i hi y₀ ≠ 0) (h : y ^ 2 = y₀ ^ 2) : y = y₀ ∨ y = -y₀ := by
  have hprod : (y - y₀) * (y + y₀) = 0 := by linear_combination h
  by_cases h1 : red p i hi (y - y₀) = 0
  · by_cases h2 : red p i hi (y + y₀) = 0
    · exfalso
      have : red p i hi (2 * y₀) = 0 := by
        rw [show (2 : ZMod (p ^ i)) * y₀ = (y + y₀) - (y - y₀) by ring, map_sub, h1, h2, sub_zero]
      rw [map_mul, map_ofNat] at this
      exact mul_ne_zero (red_two_ne_zero p hp2) hy₀ this
    · have hu : IsUnit (y + y₀) := (isUnit_iff_red_ne_zero p i hi _).mpr h2
      left
      have : y - y₀ = 0 := by
        have := congrArg (· * hu.unit⁻¹.val) hprod
        simpa [mul_assoc] using this
      exact sub_eq_zero.mp this
  · have hu : IsUnit (y - y₀) := (isUnit_iff_red_ne_zero p i hi _).mpr h1
    right
    have : y + y₀ = 0 := by
      have := congrArg (hu.unit⁻¹.val * ·) hprod
      simpa [← mul_assoc] using this
    exact eq_neg_of_add_eq_zero_left this

lemma Nu_le (hp2 : p ≠ 2) (hi : i ≠ 0) (c : ZMod (p ^ i)) :
    (Nu p i hi c : ℤ) ≤ G (red p i hi c) := by
  by_cases hne : (({y : ZMod (p ^ i) | red p i hi y ≠ 0} : Finset _).filter (fun y => y ^ 2 = c)).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₀
    obtain ⟨hy₀r, hy₀c⟩ := hy₀
    have hsub : (({y : ZMod (p ^ i) | red p i hi y ≠ 0} : Finset _).filter (fun y => y ^ 2 = c)) ⊆
        {y₀, -y₀} := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rcases sq_eq_sq_unit p i hp2 hi hy₀r (hy.2.trans hy₀c.symm) with h | h <;> simp [h]
    have hcard : Nu p i hi c ≤ 2 := by
      unfold Nu
      refine (Finset.card_le_card hsub).trans ?_
      exact (Finset.card_insert_le _ _).trans (by simp)
    have hG : G (red p i hi c) = 2 := by
      rw [← hy₀c, map_pow]
      unfold G
      simp only [pow_ne_zero 2 hy₀r, ite_false, quadraticChar_sq_one' hy₀r]
      norm_num
    rw [hG]
    exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : Nu p i hi c = 0 := by
      unfold Nu
      rw [hne, Finset.card_empty]
    rw [this]
    exact_mod_cast G_nonneg p _

/-- Every fiber of the reduction has the same size as the fiber over `0`. -/
lemma card_fiber (hi : i ≠ 0) (v : ZMod p) :
    #{x : ZMod (p ^ i) | red p i hi x = v} = #{x : ZMod (p ^ i) | red p i hi x = 0} := by
  have hs : Function.Surjective (red p i hi) := ZMod.castHom_surjective _
  exact AddMonoidHom.card_fiber_eq_of_mem_range (red p i hi).toAddMonoidHom (hs v) (hs 0)

lemma sum_red (hi : i ≠ 0) (H : ZMod p → ℤ) :
    ∑ c : ZMod (p ^ i), H (red p i hi c) =
      (#{x : ZMod (p ^ i) | red p i hi x = 0} : ℤ) * ∑ v : ZMod p, H v := by
  rw [← Finset.sum_fiberwise' univ (red p i hi) H, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_fiber p i hi v]

lemma fiber_card_eq (hi : i ≠ 0) :
    #{x : ZMod (p ^ i) | red p i hi x = 0} = p ^ (i - 1) := by
  have h := sum_red p i hi (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  have hp0 : 0 < p := hp.out.pos
  have h2 : (p : ℤ) ^ i = (#{x : ZMod (p ^ i) | red p i hi x = 0} : ℤ) * p := by
    exact_mod_cast h
  have h3 : (p : ℤ) ^ i = (p : ℤ) ^ (i - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)]
  have h4 : ((#{x : ZMod (p ^ i) | red p i hi x = 0} : ℕ) : ℤ) = (p : ℤ) ^ (i - 1) := by
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact mul_right_cancel₀ hpz (h2.symm.trans h3)
  exact_mod_cast h4

lemma sum_G (hp2 : p ≠ 2) : ∑ v : ZMod p, G v = (p : ℤ) - 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  simp only [G_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib, quadraticChar_sum_zero hF,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, zero_add]

lemma sum_Nu (hi : i ≠ 0) :
    ∑ c : ZMod (p ^ i), (Nu p i hi c : ℤ) = (p : ℤ) ^ (i - 1) * ((p : ℤ) - 1) := by
  have h1 : #({y : ZMod (p ^ i) | red p i hi y ≠ 0} : Finset _) =
      ∑ c : ZMod (p ^ i), Nu p i hi c :=
    Finset.card_eq_sum_card_fiberwise (f := fun y => y ^ 2) (t := univ) (fun _ _ => mem_univ _)
  have h2 := sum_red p i hi (fun v => if v ≠ 0 then (1 : ℤ) else 0)
  rw [Finset.sum_boole, Finset.sum_boole, fiber_card_eq p i hi] at h2
  have h3 : (#({v : ZMod p | v ≠ 0} : Finset _) : ℤ) = (p : ℤ) - 1 := by
    rw [Finset.filter_ne' univ (0 : ZMod p), Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ, ZMod.card]
    have : 1 ≤ p := hp.out.one_lt.le
    push_cast [this]
    ring
  rw [h3] at h2
  push_cast at h2
  rw [← h2]
  exact_mod_cast h1.symm

/-- The number of unit square roots of `c` is `G(c mod p)`. -/
theorem Nu_eq (hp2 : p ≠ 2) (hi : i ≠ 0) (c : ZMod (p ^ i)) :
    (Nu p i hi c : ℤ) = G (red p i hi c) := by
  have hle : ∀ c ∈ (univ : Finset (ZMod (p ^ i))), (Nu p i hi c : ℤ) ≤ G (red p i hi c) :=
    fun c _ => Nu_le p i hp2 hi c
  have hsum : ∑ c : ZMod (p ^ i), (Nu p i hi c : ℤ) = ∑ c : ZMod (p ^ i), G (red p i hi c) := by
    rw [sum_Nu p i hi, sum_red p i hi G, fiber_card_eq p i hi, sum_G p hp2]
    push_cast
    ring
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum c (mem_univ c)

/-- **Lemma 6, odd primes.** The number of pairs `(x, y)` mod `p^i` with `y` a unit and
`x² + y² = t²`, counted as `∑ₓ #{y unit | y² = t² − x²}`. -/
theorem count_odd (hp2 : p ≠ 2) (hi : i ≠ 0) (t : ZMod (p ^ i)) :
    ∑ x : ZMod (p ^ i), (Nu p i hi (t ^ 2 - x ^ 2) : ℤ) =
      (p : ℤ) ^ (i - 1) *
        (if red p i hi t = 0 then ((p : ℤ) - 1) * (quadraticChar (ZMod p) (-1) + 1)
         else (p : ℤ) - 2 - quadraticChar (ZMod p) (-1)) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  simp_rw [Nu_eq p i hp2 hi, map_sub, map_pow]
  rw [sum_red p i hi (fun v => G (red p i hi t ^ 2 - v ^ 2)), fiber_card_eq p i hi,
    base_sum hF, ZMod.card]
  push_cast
  rfl

end PrimePower

/-- `Nq q D = #{x mod 2q : x² ≡ D (mod 4q)}` (Zagier's `N_q(Δ)`). -/
def Nq (q : ℕ) (D : ℤ) : ℕ :=
  ((Finset.range (2 * q)).filter (fun x : ℕ => ((x : ℤ) ^ 2 - D) % (4 * (q : ℤ)) = 0)).card

/-- `4 ∣ x² − t²` iff `x ≡ t (mod 2)`. -/
lemma four_dvd_sq_sub_sq_iff (x t : ℤ) :
    (4 : ℤ) ∣ x ^ 2 - t ^ 2 ↔ (x : ZMod 2) = (t : ZMod 2) := by
  have key : ∀ r s : ZMod 4, (r ^ 2 - s ^ 2 = 0 ↔
      ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) r =
        ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) s) := by decide
  have h1 := key (x : ZMod 4) (t : ZMod 4)
  rw [map_intCast, map_intCast] at h1
  rw [← h1, show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

section Bridge

variable (q : ℕ) [NeZero q]

omit [NeZero q] in
/-- Membership in the set counted by `Nq`. -/
lemma mem_Nq_iff (hq : Odd q) (t b : ℤ) (x : ℕ) :
    ((x : ℤ) ^ 2 - (t ^ 2 - 4 * b ^ 2)) % (4 * (q : ℤ)) = 0 ↔
      ((x : ℤ) : ZMod 2) = (t : ZMod 2) ∧
        ((x : ZMod q)) ^ 2 = (((t ^ 2 - 4 * b ^ 2 : ℤ)) : ZMod q) := by
  rw [← Int.dvd_iff_emod_eq_zero]
  have hcop : IsCoprime (4 : ℤ) (q : ℤ) := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_two_left.mpr hq).pow_left 2
  have hq' : (q : ℤ) ∣ (x : ℤ) ^ 2 - (t ^ 2 - 4 * b ^ 2) ↔
      ((x : ZMod q)) ^ 2 = (((t ^ 2 - 4 * b ^ 2 : ℤ)) : ZMod q) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero
  have h4 : (4 : ℤ) ∣ (x : ℤ) ^ 2 - (t ^ 2 - 4 * b ^ 2) ↔ (4 : ℤ) ∣ (x : ℤ) ^ 2 - t ^ 2 := by
    rw [show (x : ℤ) ^ 2 - (t ^ 2 - 4 * b ^ 2) = ((x : ℤ) ^ 2 - t ^ 2) + 4 * b ^ 2 by ring]
    exact (dvd_add_left (dvd_mul_right 4 _))
  rw [← hq', ← four_dvd_sq_sub_sq_iff, ← h4]
  constructor
  · intro h
    exact ⟨dvd_trans (dvd_mul_right 4 (q : ℤ)) h, dvd_trans (dvd_mul_left (q : ℤ) 4) h⟩
  · rintro ⟨h1, h2⟩
    exact hcop.mul_dvd h1 h2

/-- For odd `q`, `Nq q (t² − 4b²)` is the number of square roots of `t² − 4b²` mod `q`. -/
lemma Nq_eq (hq : Odd q) (t b : ℤ) :
    Nq q (t ^ 2 - 4 * b ^ 2) = #{y : ZMod q | y ^ 2 = (((t ^ 2 - 4 * b ^ 2 : ℤ)) : ZMod q)} := by
  have hq1 : q % 2 = 1 := Nat.odd_iff.mp hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : ((q : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_iff]
    exact ⟨q / 2, by simp [ZMod.val_one]; omega⟩
  have flip : ∀ a b : ZMod 2, a ≠ b → a + 1 = b := by decide
  unfold Nq
  simp_rw [mem_Nq_iff q hq t b]
  refine Finset.card_nbij' (fun x => (x : ZMod q))
    (fun y => if ((y.val : ℤ) : ZMod 2) = (t : ZMod 2) then y.val else y.val + q) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hx.2.2
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    have hv := ZMod.val_lt y
    split_ifs with h
    · refine ⟨by omega, h, ?_⟩
      rw [ZMod.natCast_zmod_val]; push_cast at hy ⊢; exact hy
    · refine ⟨by omega, ?_, ?_⟩
      · push_cast
        rw [hq2]
        exact flip _ _ h
      · push_cast
        rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]; push_cast at hy ⊢; exact hy
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    obtain ⟨hx2q, hxt, -⟩ := hx
    simp only [ZMod.val_natCast]
    by_cases hlt : x < q
    · rw [Nat.mod_eq_of_lt hlt]
      simp only [hxt, ite_true]
    · have hm : x % q = x - q := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      have hne : (((x - q : ℕ) : ℤ) : ZMod 2) ≠ (t : ZMod 2) := by
        intro h
        rw [← hxt] at h
        have : (((x - q : ℕ) : ℤ) : ZMod 2) + 1 = ((x : ℤ) : ZMod 2) := by
          rw [← hq2]
          push_cast [show q ≤ x by omega]
          ring
        rw [h] at this
        simp at this
      simp only [hne, ite_false]
      omega
  · intro y _
    simp only
    split_ifs
    · exact ZMod.natCast_zmod_val y
    · push_cast
      rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]


end Bridge

/-- `nuSum t q = Σ_{b mod q, gcd(b, q) = 1} N_q(t² − 4b²)`, i.e. `φ(q) · ν_t(q)`
(the same definition as in `LocalCounts.lean`). -/
def nuSum (t : ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter (fun b => Nat.Coprime b q)).sum
    (fun b => Nq q (t ^ 2 - 4 * (b : ℤ) ^ 2))

/-- The character χ₋₄ on natural numbers (as in `LocalCounts.lean`). -/
def chi4 (l : ℕ) : ℤ := if l % 4 = 1 then 1 else if l % 4 = 3 then -1 else 0

section Final

variable (p : ℕ) [hp : Fact p.Prime] (i : ℕ) [NeZero (p ^ i)]

lemma nuSum_eq_sum_Nu (hp2 : p ≠ 2) (hi : i ≠ 0) (t : ℤ) :
    (nuSum t (p ^ i) : ℤ) =
      ∑ x : ZMod (p ^ i), (Nu p i hi (((t : ZMod (p ^ i))) ^ 2 - x ^ 2) : ℤ) := by
  have hodd : Odd (p ^ i) := (hp.out.odd_of_ne_two hp2).pow
  set q := p ^ i with hqdef
  -- Step 1: Nq as square-root counts mod q.
  have h1 : nuSum t q = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - 4 * ((b : ℕ) : ZMod q) ^ 2} := by
    unfold nuSum
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nq_eq q hodd t b]
    push_cast
    rfl
  -- Step 2: residues coprime to q are the units, i.e. `red ≠ 0`.
  have h2 : ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
      #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - 4 * ((b : ℕ) : ZMod q) ^ 2} =
      ∑ v ∈ ({v : ZMod q | red p i hi v ≠ 0} : Finset _),
        #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - 4 * v ^ 2} := by
    refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun v => v.val) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hb ⊢
      rw [← isUnit_iff_red_ne_zero p i hi, ZMod.isUnit_iff_coprime]
      exact hb.2
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hv ⊢
      refine ⟨ZMod.val_lt v, ?_⟩
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val, isUnit_iff_red_ne_zero p i hi]
      exact hv
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hb.1]
    · intro v _
      simp only [ZMod.natCast_zmod_val]
    · intro b _
      rfl
  -- Step 3: substitute u = 2v.
  have hred2 : red p i hi (2 : ZMod q) ≠ 0 := by
    rw [map_ofNat]; exact red_two_ne_zero p hp2
  have hu2 : IsUnit (2 : ZMod q) := (isUnit_iff_red_ne_zero p i hi _).mpr hred2
  have h3 : ∑ v ∈ ({v : ZMod q | red p i hi v ≠ 0} : Finset _),
      #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - 4 * v ^ 2} =
      ∑ u ∈ ({u : ZMod q | red p i hi u ≠ 0} : Finset _),
        #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - u ^ 2} := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Fintype.sum_equiv (Units.mulLeft hu2.unit) _ _ (fun v => ?_)
    have e : (Units.mulLeft hu2.unit) v = 2 * v := rfl
    rw [e, map_mul, show (2 * v) ^ 2 = 4 * v ^ 2 by ring]
    simp only [ne_eq, mul_eq_zero, hred2, false_or]
  -- Step 4: swap the order of counting.
  have h4 : ∑ u ∈ ({u : ZMod q | red p i hi u ≠ 0} : Finset _),
      #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - u ^ 2} =
      ∑ x : ZMod q, Nu p i hi ((t : ZMod q) ^ 2 - x ^ 2) := by
    calc ∑ u ∈ ({u : ZMod q | red p i hi u ≠ 0} : Finset _),
          #{y : ZMod q | y ^ 2 = (t : ZMod q) ^ 2 - u ^ 2}
        = ∑ u ∈ ({u : ZMod q | red p i hi u ≠ 0} : Finset _),
            ∑ y : ZMod q, (if y ^ 2 = (t : ZMod q) ^ 2 - u ^ 2 then 1 else 0) :=
          Finset.sum_congr rfl (fun u _ => Finset.card_filter _ _)
      _ = ∑ y : ZMod q, ∑ u ∈ ({u : ZMod q | red p i hi u ≠ 0} : Finset _),
            (if y ^ 2 = (t : ZMod q) ^ 2 - u ^ 2 then 1 else 0) := Finset.sum_comm
      _ = ∑ x : ZMod q, Nu p i hi ((t : ZMod q) ^ 2 - x ^ 2) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          unfold Nu
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun u _ => ?_
          by_cases hy : y ^ 2 = (t : ZMod q) ^ 2 - u ^ 2
          · have h' : u ^ 2 = (t : ZMod q) ^ 2 - y ^ 2 := by linear_combination hy
            split_ifs; rfl
          · have h' : ¬ u ^ 2 = (t : ZMod q) ^ 2 - y ^ 2 := fun h => hy (by linear_combination h)
            split_ifs; rfl
  rw [h1, h2, h3, h4]
  push_cast
  rfl

lemma quadraticChar_neg_one_eq_chi4 (hp2 : p ≠ 2) :
    quadraticChar (ZMod p) (-1) = chi4 p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [quadraticChar_neg_one hF, ZMod.card, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  unfold chi4
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h <;> simp [h, hodd]

/-- **Lemma 6 for odd primes, in the original counting.** For an odd prime `p`, `i ≥ 1` and any
integer `t`, `Σ_{b mod p^i, (b,p)=1} N_{p^i}(t² − 4b²)` equals `p^(i−1)(p − 1)(1 + χ₋₄(p))` if
`p ∣ t` and `p^(i−1)(p − 2 − χ₋₄(p))` otherwise. -/
theorem nuSum_odd (hp2 : p ≠ 2) (hi : i ≠ 0) (t : ℤ) :
    (nuSum t (p ^ i) : ℤ) =
      (p : ℤ) ^ (i - 1) *
        (if (p : ℤ) ∣ t then ((p : ℤ) - 1) * (1 + chi4 p) else (p : ℤ) - 2 - chi4 p) := by
  rw [nuSum_eq_sum_Nu p i hp2 hi t, count_odd p i hp2 hi, quadraticChar_neg_one_eq_chi4 p hp2]
  simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs <;> ring

end Final

section TwoAdic

variable (k : ℕ)

/-- The element `2^(k−1)` of `ZMod (2^k)`. -/
abbrev half (k : ℕ) : ZMod (2 ^ k) := ((2 ^ (k - 1) : ℕ) : ZMod (2 ^ k))

lemma two_mul_half (hk : 1 ≤ k) : 2 * half k = 0 := by
  unfold half
  rw [show (2 : ZMod (2 ^ k)) = ((2 : ℕ) : ZMod (2 ^ k)) by norm_cast, ← Nat.cast_mul,
    ← pow_succ', Nat.sub_add_cancel hk, ZMod.natCast_self]

lemma natCast_ne_zero_of_lt {n m : ℕ} (h0 : 0 < m) (h : m < n) : ((m : ℕ) : ZMod n) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

/-- In `ZMod (2^k)`, `k ≥ 3`, the solutions of `y² = 1` are `±1` and `±1 + 2^(k−1)`. -/
lemma sq_eq_one_two_pow (hk : 3 ≤ k) (y : ZMod (2 ^ k)) (hy : y ^ 2 = 1) :
    y = 1 ∨ y = -1 ∨ y = 1 + half k ∨ y = -1 + half k := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ZMod (2 ^ k)) = y :=
    ⟨(y.val : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val]⟩
  have hdvd : (2 : ℤ) ^ k ∣ n ^ 2 - 1 := by
    have h0 : ((n ^ 2 - 1 : ℤ) : ZMod (2 ^ k)) = 0 := by push_cast; rw [hy, sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    exact_mod_cast h0
  -- n is odd
  have hodd : n % 2 = 1 := by
    have h2 : (2 : ℤ) ∣ n ^ 2 - 1 := dvd_trans (dvd_pow_self 2 (by omega)) hdvd
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · exfalso
      obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      subst hm
      obtain ⟨c, hc⟩ := h2
      have : (2 : ℤ) * (2 * m ^ 2 - c) = 1 := by linear_combination hc
      omega
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  subst hm
  have hk2 : (2 : ℤ) ^ k = 4 * 2 ^ (k - 2) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hmm : (2 : ℤ) ^ (k - 2) ∣ m * (m + 1) := by
    rw [hk2, show (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) by ring] at hdvd
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hdvd
  -- integer `2^(k-1) j` in ZMod (2^k): 0 or half
  have hcast : ∀ j : ℤ, (((2 : ℤ) ^ (k - 1) * j : ℤ) : ZMod (2 ^ k)) = 0 ∨
      (((2 : ℤ) ^ (k - 1) * j : ℤ) : ZMod (2 ^ k)) = half k := by
    intro j
    obtain ⟨r, hr | hr⟩ : ∃ r, j = 2 * r ∨ j = 2 * r + 1 := ⟨j / 2, by omega⟩
    · left
      subst hr
      have : ((2 : ℤ) ^ (k - 1) * (2 * r) : ℤ) = ((2 ^ k : ℕ) : ℤ) * r := by
        push_cast
        rw [show k = (k - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [this]; push_cast; rw [show ((2 : ZMod (2 ^ k)) ^ k) = ((2 ^ k : ℕ) : ZMod (2 ^ k)) by
        push_cast; rfl, ZMod.natCast_self, zero_mul]
    · right
      subst hr
      have : ((2 : ℤ) ^ (k - 1) * (2 * r + 1) : ℤ) = ((2 ^ k : ℕ) : ℤ) * r + ((2 ^ (k - 1) : ℕ) : ℤ) := by
        push_cast
        rw [show k = (k - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [this]
      push_cast
      rw [show ((2 : ZMod (2 ^ k)) ^ k) = ((2 ^ k : ℕ) : ZMod (2 ^ k)) by push_cast; rfl,
        ZMod.natCast_self, zero_mul, zero_add]
  rcases Int.emod_two_eq_zero_or_one m with hm2 | hm2
  · -- m even: m + 1 odd, so 2^(k-2) ∣ m
    have hco : IsCoprime ((2 : ℤ) ^ (k - 2)) (m + 1) :=
      (Int.isCoprime_two_left.mpr (by rw [Int.odd_iff]; omega)).pow_left
    obtain ⟨j, hj⟩ := hco.dvd_of_dvd_mul_right hmm
    have hn : 2 * m + 1 = 1 + 2 ^ (k - 1) * j := by
      rw [hj, show k - 1 = (k - 2) + 1 by omega, pow_succ]; ring
    rw [hn]
    push_cast
    rcases hcast j with h | h <;> push_cast at h <;> rw [h]
    · left; simp
    · right; right; left; rfl
  · -- m odd: 2^(k-2) ∣ m + 1
    have hco : IsCoprime ((2 : ℤ) ^ (k - 2)) m :=
      (Int.isCoprime_two_left.mpr (by rw [Int.odd_iff]; omega)).pow_left
    obtain ⟨j, hj⟩ := hco.dvd_of_dvd_mul_left hmm
    have hn : 2 * m + 1 = -1 + 2 ^ (k - 1) * j := by
      have : m = 2 ^ (k - 2) * j - 1 := by linear_combination hj
      rw [this, show k - 1 = (k - 2) + 1 by omega, pow_succ]; ring
    rw [hn]
    push_cast
    rcases hcast j with h | h <;> push_cast at h <;> rw [h]
    · right; left; simp
    · right; right; right; rfl

/-- `#{y | y² = 1} = 4` in `ZMod (2^k)`, `k ≥ 3`. -/
lemma card_sq_eq_one_two_pow (hk : 3 ≤ k) :
    #{y : ZMod (2 ^ k) | y ^ 2 = 1} = 4 := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  have hh : (half k) ^ 2 = 0 := by
    unfold half
    rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow 2 (by omega)
  have h2h := two_mul_half k (by omega)
  have hset : ({y : ZMod (2 ^ k) | y ^ 2 = 1} : Finset _) = {1, -1, 1 + half k, -1 + half k} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · exact sq_eq_one_two_pow k hk y
    · rintro (h | h | h | h) <;> subst h
      · ring
      · ring
      · linear_combination hh + h2h
      · linear_combination hh - h2h
  rw [hset]
  -- distinctness
  have h2 : (2 : ZMod (2 ^ k)) ≠ 0 := by
    have := natCast_ne_zero_of_lt (n := 2 ^ k) (m := 2) (by norm_num)
      (by calc 2 < 2 ^ 3 := by norm_num
               _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)
    exact_mod_cast this
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  have hlt : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have ha : half k ≠ 0 := natCast_ne_zero_of_lt hpos hlt
  have hk4 : 4 ≤ 2 ^ (k - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have ham2 : half k - 2 ≠ 0 := by
    have := natCast_ne_zero_of_lt (n := 2 ^ k) (m := 2 ^ (k - 1) - 2) (by omega) (by omega)
    unfold half
    rwa [Nat.cast_sub (by omega), Nat.cast_ofNat] at this
  have hap2 : half k + 2 ≠ 0 := by
    have := natCast_ne_zero_of_lt (n := 2 ^ k) (m := 2 ^ (k - 1) + 2) (by omega) (by omega)
    unfold half
    rwa [Nat.cast_add, Nat.cast_ofNat] at this
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · intro h; apply h2; linear_combination h
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hap2 ?_, fun h => ha ?_⟩ <;> linear_combination -h
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => h2 ?_, fun h => ha ?_, fun h => ham2 ?_⟩
    · linear_combination h
    · linear_combination -h
    · linear_combination -h

end TwoAdic


section TwoMain

/-- Sums over residues coprime to `p^i` are sums over units (`red ≠ 0`). -/
lemma sum_coprime_eq (p : ℕ) [Fact p.Prime] (i : ℕ) [NeZero (p ^ i)] (hi : i ≠ 0)
    (F : ZMod (p ^ i) → ℕ) :
    ∑ b ∈ (Finset.range (p ^ i)).filter (fun b => Nat.Coprime b (p ^ i)), F (b : ZMod (p ^ i)) =
      ∑ v ∈ ({v : ZMod (p ^ i) | red p i hi v ≠ 0} : Finset _), F v := by
  refine Finset.sum_nbij' (fun b => (b : ZMod (p ^ i))) (fun v => v.val) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hb ⊢
    rw [← isUnit_iff_red_ne_zero p i hi, ZMod.isUnit_iff_coprime]
    exact hb.2
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hv ⊢
    refine ⟨ZMod.val_lt v, ?_⟩
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val, isUnit_iff_red_ne_zero p i hi]
    exact hv
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hb.1]
  · intro v _
    simp only [ZMod.natCast_zmod_val]
  · intro b _
    rfl

/-- Swapping the order of counting. -/
lemma sum_swap (p : ℕ) [Fact p.Prime] (i : ℕ) [NeZero (p ^ i)] (hi : i ≠ 0) (c : ZMod (p ^ i)) :
    ∑ u ∈ ({u : ZMod (p ^ i) | red p i hi u ≠ 0} : Finset _), #{y : ZMod (p ^ i) | y ^ 2 = c - u ^ 2} =
      ∑ x : ZMod (p ^ i), Nu p i hi (c - x ^ 2) := by
  calc ∑ u ∈ ({u : ZMod (p ^ i) | red p i hi u ≠ 0} : Finset _),
        #{y : ZMod (p ^ i) | y ^ 2 = c - u ^ 2}
      = ∑ u ∈ ({u : ZMod (p ^ i) | red p i hi u ≠ 0} : Finset _),
          ∑ y : ZMod (p ^ i), (if y ^ 2 = c - u ^ 2 then 1 else 0) :=
        Finset.sum_congr rfl (fun u _ => Finset.card_filter _ _)
    _ = ∑ y : ZMod (p ^ i), ∑ u ∈ ({u : ZMod (p ^ i) | red p i hi u ≠ 0} : Finset _),
          (if y ^ 2 = c - u ^ 2 then 1 else 0) := Finset.sum_comm
    _ = ∑ x : ZMod (p ^ i), Nu p i hi (c - x ^ 2) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        unfold Nu
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hy : y ^ 2 = c - u ^ 2
        · have h' : u ^ 2 = c - y ^ 2 := by linear_combination hy
          split_ifs; rfl
        · have h' : ¬ u ^ 2 = c - y ^ 2 := fun h => hy (by linear_combination h)
          split_ifs; rfl

/-- `Nq` only depends on `D` modulo `4q`. -/
lemma Nq_congr (q : ℕ) {D D' : ℤ} (h : (4 * (q : ℤ)) ∣ D - D') : Nq q D = Nq q D' := by
  unfold Nq
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  rw [← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_emod_eq_zero,
    show (x : ℤ) ^ 2 - D = ((x : ℤ) ^ 2 - D') - (D - D') by ring]
  exact dvd_sub_left h

variable (k : ℕ) [NeZero (2 ^ k)]

omit [NeZero (2 ^ k)] in
lemma eight_dvd (hk : 3 ≤ k) : 8 ∣ 2 ^ k := by
  rw [show 8 = 2 ^ 3 by norm_num]; exact pow_dvd_pow 2 hk

/-- Reduction `ZMod (2^k) → ZMod 8`. -/
abbrev r8 (hk : 3 ≤ k) : ZMod (2 ^ k) →+* ZMod 8 := ZMod.castHom (eight_dvd k hk) (ZMod 8)

omit [NeZero (2 ^ k)] in
lemma red_two_eq (hk : 3 ≤ k) (y : ZMod (2 ^ k)) :
    red 2 k (by omega) y = ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2) (r8 k hk y) :=
  RingHom.congr_fun (RingHom.ext_zmod (red 2 k (by omega))
    ((ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2)).comp (r8 k hk))) y

lemma odd_sq_eight : ∀ v : ZMod 8, ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2) v ≠ 0 →
    v ^ 2 = 1 := by decide

/-- A unit square in `ZMod (2^k)` has exactly four unit square roots. -/
lemma Nu_sq_unit (hk : 3 ≤ k) (y₀ : ZMod (2 ^ k)) (hy₀ : red 2 k (by omega) y₀ ≠ 0) :
    Nu 2 k (by omega) (y₀ ^ 2) = 4 := by
  have hk0 : k ≠ 0 := by omega
  have hu : IsUnit y₀ := (isUnit_iff_red_ne_zero 2 k hk0 y₀).mpr hy₀
  unfold Nu
  rw [← card_sq_eq_one_two_pow k hk]
  symm
  refine Finset.card_nbij' (fun y => y₀ * y) (fun y => hu.unit⁻¹.val * y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hy ⊢
    have hyu : IsUnit y := ⟨⟨y, y, by rw [← sq]; exact hy, by rw [← sq]; exact hy⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hy₀ ((isUnit_iff_red_ne_zero 2 k hk0 y).mp hyu)
    · rw [mul_pow, hy, mul_one]
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hy ⊢
    have h1 : hu.unit⁻¹.val * y₀ = 1 := hu.val_inv_mul
    calc (hu.unit⁻¹.val * y) ^ 2 = hu.unit⁻¹.val ^ 2 * y ^ 2 := by ring
      _ = hu.unit⁻¹.val ^ 2 * y₀ ^ 2 := by rw [hy.2]
      _ = (hu.unit⁻¹.val * y₀) ^ 2 := by ring
      _ = 1 := by rw [h1, one_pow]
  · intro y _
    simp only [← mul_assoc, hu.val_inv_mul, one_mul]
  · intro y _
    simp only [← mul_assoc, hu.mul_val_inv, one_mul]

lemma Nu_le_four (hk : 3 ≤ k) (c : ZMod (2 ^ k)) :
    (Nu 2 k (by omega) c : ℤ) ≤ if r8 k hk c = 1 then 4 else 0 := by
  have hk0 : k ≠ 0 := by omega
  by_cases hne : (({y : ZMod (2 ^ k) | red 2 k hk0 y ≠ 0} : Finset _).filter
      (fun y => y ^ 2 = c)).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₀
    obtain ⟨hy₀r, rfl⟩ := hy₀
    have h8 : r8 k hk (y₀ ^ 2) = 1 := by
      rw [map_pow]
      apply odd_sq_eight
      rw [← red_two_eq k hk]
      exact hy₀r
    rw [Nu_sq_unit k hk y₀ hy₀r]
    simp only [h8, ite_true]
    norm_num
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : Nu 2 k hk0 c = 0 := by
      unfold Nu
      rw [hne, Finset.card_empty]
    rw [this]
    split_ifs <;> norm_num

lemma card_fiber8 (hk : 3 ≤ k) (v : ZMod 8) :
    #{x : ZMod (2 ^ k) | r8 k hk x = v} = #{x : ZMod (2 ^ k) | r8 k hk x = 0} := by
  have hs : Function.Surjective (r8 k hk) := ZMod.castHom_surjective _
  exact AddMonoidHom.card_fiber_eq_of_mem_range (r8 k hk).toAddMonoidHom (hs v) (hs 0)

lemma sum_r8 (hk : 3 ≤ k) (H : ZMod 8 → ℤ) :
    ∑ c : ZMod (2 ^ k), H (r8 k hk c) =
      (#{x : ZMod (2 ^ k) | r8 k hk x = 0} : ℤ) * ∑ v : ZMod 8, H v := by
  rw [← Finset.sum_fiberwise' univ (r8 k hk) H, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, card_fiber8 k hk v]

lemma fiber8_card (hk : 3 ≤ k) : (#{x : ZMod (2 ^ k) | r8 k hk x = 0} : ℤ) = 2 ^ (k - 3) := by
  have h := sum_r8 k hk (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  have h3 : ((2 ^ k : ℕ) : ℤ) = 2 ^ (k - 3) * 8 := by
    push_cast
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, Nat.sub_add_cancel hk]
  exact mul_right_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) (h.symm.trans h3)

/-- The number of unit square roots in `ZMod (2^k)`, `k ≥ 3`: 4 if `c ≡ 1 (mod 8)`, else 0. -/
theorem Nu_eq_two (hk : 3 ≤ k) (c : ZMod (2 ^ k)) :
    (Nu 2 k (by omega) c : ℤ) = if r8 k hk c = 1 then 4 else 0 := by
  have hk0 : k ≠ 0 := by omega
  have hle : ∀ c ∈ (univ : Finset (ZMod (2 ^ k))),
      (Nu 2 k hk0 c : ℤ) ≤ if r8 k hk c = 1 then 4 else 0 := fun c _ => Nu_le_four k hk c
  have hsum : ∑ c : ZMod (2 ^ k), (Nu 2 k hk0 c : ℤ) =
      ∑ c : ZMod (2 ^ k), (if r8 k hk c = 1 then (4 : ℤ) else 0) := by
    rw [sum_Nu 2 k hk0, sum_r8 k hk (fun v => if v = 1 then (4 : ℤ) else 0), fiber8_card k hk,
      Finset.sum_ite_eq' univ (1 : ZMod 8) (fun _ => (4 : ℤ))]
    simp only [Finset.mem_univ, ite_true, Nat.cast_ofNat]
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]
    norm_num
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum c (mem_univ c)

lemma sum_Nu_one_sub_sq (hk : 3 ≤ k) :
    ∑ w : ZMod (2 ^ k), (Nu 2 k (by omega) (1 - w ^ 2) : ℤ) = 2 ^ k := by
  simp_rw [Nu_eq_two k hk, map_sub, map_one, map_pow]
  rw [sum_r8 k hk (fun v => if 1 - v ^ 2 = 1 then (4 : ℤ) else 0), fiber8_card k hk]
  have : ∑ v : ZMod 8, (if 1 - v ^ 2 = 1 then (4 : ℤ) else 0) = 8 := by decide
  rw [this, show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add, Nat.sub_add_cancel hk]

lemma Nu_mul_sq (hk : 3 ≤ k) {u : ZMod (2 ^ k)} (hu : IsUnit u) (c : ZMod (2 ^ k)) :
    Nu 2 k (by omega) (u ^ 2 * c) = Nu 2 k (by omega) c := by
  have hk0 : k ≠ 0 := by omega
  unfold Nu
  have hur : red 2 k hk0 u ≠ 0 := (isUnit_iff_red_ne_zero 2 k hk0 u).mp hu
  refine Finset.card_nbij' (fun y => hu.unit⁻¹.val * y) (fun y => u * y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hy ⊢
    have hinv : red 2 k hk0 hu.unit⁻¹.val ≠ 0 :=
      (isUnit_iff_red_ne_zero 2 k hk0 _).mp (Units.isUnit _)
    refine ⟨by rw [map_mul]; exact mul_ne_zero hinv hy.1, ?_⟩
    have h1 : hu.unit⁻¹.val * u = 1 := hu.val_inv_mul
    calc (hu.unit⁻¹.val * y) ^ 2 = hu.unit⁻¹.val ^ 2 * y ^ 2 := by ring
      _ = hu.unit⁻¹.val ^ 2 * (u ^ 2 * c) := by rw [hy.2]
      _ = (hu.unit⁻¹.val * u) ^ 2 * c := by ring
      _ = c := by rw [h1, one_pow, one_mul]
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hy ⊢
    refine ⟨by rw [map_mul]; exact mul_ne_zero hur hy.1, ?_⟩
    rw [mul_pow, hy.2]
  · intro y _
    simp only [← mul_assoc, hu.mul_val_inv, one_mul]
  · intro y _
    simp only [← mul_assoc, hu.val_inv_mul, one_mul]

lemma sum_scale (hk : 3 ≤ k) {u : ZMod (2 ^ k)} (hu : IsUnit u) :
    ∑ w : ZMod (2 ^ k), Nu 2 k (by omega) (u ^ 2 - w ^ 2) =
      ∑ w : ZMod (2 ^ k), Nu 2 k (by omega) (1 - w ^ 2) := by
  symm
  refine Fintype.sum_equiv (Units.mulLeft hu.unit) _ _ (fun w => ?_)
  have e : (Units.mulLeft hu.unit) w = u * w := rfl
  rw [e, show u ^ 2 - (u * w) ^ 2 = u ^ 2 * (1 - w ^ 2) by ring, Nu_mul_sq k hk hu]

/-- For `t = 2u`, `Nq (2^k) (t² − 4b²)` counts square roots of `u² − b²` mod `2^k`. -/
lemma Nq_two_even (u b : ℤ) :
    Nq (2 ^ k) ((2 * u) ^ 2 - 4 * b ^ 2) =
      #{w : ZMod (2 ^ k) | w ^ 2 = (u : ZMod (2 ^ k)) ^ 2 - (b : ZMod (2 ^ k)) ^ 2} := by
  set q := 2 ^ k with hq
  unfold Nq
  have key : ∀ m : ℕ, ((((2 * m : ℕ) : ℤ) ^ 2 - ((2 * u) ^ 2 - 4 * b ^ 2)) % (4 * (q : ℤ)) = 0 ↔
      (m : ZMod q) ^ 2 = (u : ZMod q) ^ 2 - (b : ZMod q) ^ 2) := by
    intro m
    rw [← Int.dvd_iff_emod_eq_zero,
      show (((2 * m : ℕ) : ℤ) ^ 2 - ((2 * u) ^ 2 - 4 * b ^ 2)) = 4 * ((m : ℤ) ^ 2 - (u ^ 2 - b ^ 2))
        by push_cast; ring,
      mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0), ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero
  have heven : ∀ x : ℕ, (((x : ℤ) ^ 2 - ((2 * u) ^ 2 - 4 * b ^ 2)) % (4 * (q : ℤ)) = 0) →
      x = 2 * (x / 2) := by
    intro x hx
    rw [← Int.dvd_iff_emod_eq_zero] at hx
    obtain ⟨d, hd⟩ := hx
    have h2 : Even ((x : ℤ) ^ 2) := ⟨2 * u ^ 2 - 2 * b ^ 2 + 2 * q * d, by linear_combination hd⟩
    have : Even x := by exact_mod_cast (Int.even_pow.mp h2).1
    exact (Nat.two_mul_div_two_of_even this).symm
  refine Finset.card_nbij' (fun x => ((x / 2 : ℕ) : ZMod q)) (fun y => 2 * y.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hx ⊢
    have hx2 := heven x hx.2
    rw [← key]
    rw [← hx2]
    exact hx.2
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_range, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hy ⊢
    refine ⟨by have := ZMod.val_lt y; omega, ?_⟩
    rw [key, ZMod.natCast_zmod_val]
    exact hy
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    have hlt : x < 2 * q := hx.1
    have hx2 := heven x hx.2
    simp only [ZMod.val_natCast]
    rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hlt)]
    exact hx2.symm
  · intro y _
    simp only
    rw [Nat.mul_div_cancel_left _ (by norm_num), ZMod.natCast_zmod_val]

/-- **Main 2-adic case**: for `u` odd and `k ≥ 3`, `nuSum (2u) (2^k) = 2^k`. -/
theorem nuSum_two_main (hk : 3 ≤ k) (u : ℤ) (hu : u % 2 = 1) :
    (nuSum (2 * u) (2 ^ k) : ℤ) = 2 ^ k := by
  have hk0 : k ≠ 0 := by omega
  have h1 : nuSum (2 * u) (2 ^ k) = ∑ b ∈ (Finset.range (2 ^ k)).filter
      (fun b => Nat.Coprime b (2 ^ k)),
      #{w : ZMod (2 ^ k) | w ^ 2 = (u : ZMod (2 ^ k)) ^ 2 - ((b : ℕ) : ZMod (2 ^ k)) ^ 2} := by
    unfold nuSum
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Nq_two_even k u b]
    push_cast
    rfl
  have huu : IsUnit (u : ZMod (2 ^ k)) := by
    rw [isUnit_iff_red_ne_zero 2 k hk0, map_intCast]
    have h2 : (u : ZMod 2) = 1 := by
      rw [← ZMod.intCast_mod u 2]
      push_cast
      rw [hu]
      rfl
    rw [h2]
    decide
  rw [h1, sum_coprime_eq 2 k hk0
      (fun v => #{w : ZMod (2 ^ k) | w ^ 2 = (u : ZMod (2 ^ k)) ^ 2 - v ^ 2}),
    sum_swap 2 k hk0, sum_scale k hk huu]
  exact_mod_cast sum_Nu_one_sub_sq k hk

end TwoMain

section TwoFinal

lemma b_odd_of_coprime {i : ℕ} (hi : 1 ≤ i) {b : ℕ} (hb : Nat.Coprime b (2 ^ i)) :
    (b : ZMod 2) = 1 := by
  have h2 : Nat.Coprime b 2 := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (by omega)) hb
  have hodd : b % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp h2)
  rw [← ZMod.natCast_mod, hodd]
  rfl

lemma intCast_two_of_odd {t : ℤ} (ht : t % 2 = 1) : (t : ZMod 2) = 1 := by
  rw [← ZMod.intCast_mod t 2]
  push_cast
  rw [ht]
  rfl

lemma intCast_four_of_dvd {t : ℤ} (ht : t % 4 = 0) : (t : ZMod 4) = 0 := by
  rw [← ZMod.intCast_mod t 4]
  push_cast
  rw [ht]
  rfl

/-- `t` odd: no solutions at all (`t² − 4b² ≡ 5 (mod 8)` is not a square). -/
lemma nuSum_two_odd (i : ℕ) (hi : 1 ≤ i) (t : ℤ) (ht : t % 2 = 1) : nuSum t (2 ^ i) = 0 := by
  unfold nuSum
  refine Finset.sum_eq_zero fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hb
  have hb2 := b_odd_of_coprime hi hb.2
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  unfold Nq
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  rw [← Int.dvd_iff_emod_eq_zero] at hx
  have h8 : ((8 : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - (t ^ 2 - 4 * (b : ℤ) ^ 2) :=
    dvd_trans ⟨2 ^ j, by push_cast; ring⟩ hx
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h8
  push_cast at h0
  have key : ∀ x t b : ZMod 8, ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2) t = 1 →
      ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2) b = 1 → x ^ 2 - (t ^ 2 - 4 * b ^ 2) ≠ 0 := by
    decide
  refine key _ _ _ ?_ ?_ h0
  · rw [map_intCast]; exact intCast_two_of_odd ht
  · rw [map_natCast]; exact hb2

/-- `4 ∣ t`, `i ≥ 2`: no solutions (`t² − 4b² ≡ 12 (mod 16)` is not a square). -/
lemma nuSum_two_four (i : ℕ) (hi : 2 ≤ i) (t : ℤ) (ht : t % 4 = 0) : nuSum t (2 ^ i) = 0 := by
  unfold nuSum
  refine Finset.sum_eq_zero fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hb
  have hb2 := b_odd_of_coprime (by omega : 1 ≤ i) hb.2
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  unfold Nq
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  rw [← Int.dvd_iff_emod_eq_zero] at hx
  have h16 : ((16 : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - (t ^ 2 - 4 * (b : ℤ) ^ 2) :=
    dvd_trans ⟨2 ^ j, by push_cast; ring⟩ hx
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mpr h16
  push_cast at h0
  have key : ∀ x t b : ZMod 16, ZMod.castHom (show 4 ∣ 16 by norm_num) (ZMod 4) t = 0 →
      ZMod.castHom (show 2 ∣ 16 by norm_num) (ZMod 2) b = 1 → x ^ 2 - (t ^ 2 - 4 * b ^ 2) ≠ 0 := by
    decide
  refine key _ _ _ ?_ ?_ h0
  · rw [map_intCast]; exact intCast_four_of_dvd ht
  · rw [map_natCast]; exact hb2

/-- `i = 1`, `t` even: exactly one solution. -/
lemma nuSum_two_one (t : ℤ) (ht : t % 2 = 0) : nuSum t (2 ^ 1) = 1 := by
  unfold nuSum
  have hf : (Finset.range (2 ^ 1)).filter (fun b => Nat.Coprime b (2 ^ 1)) = {1} := by decide
  rw [hf, Finset.sum_singleton]
  obtain ⟨s, hs | hs⟩ : ∃ s, t = 4 * s ∨ t = 4 * s + 2 := ⟨t / 4, by omega⟩
  · rw [Nq_congr (2 ^ 1) (D' := -4) ⟨2 * s ^ 2, by rw [hs]; push_cast; ring⟩]
    decide
  · rw [Nq_congr (2 ^ 1) (D' := 0) ⟨2 * s ^ 2 + 2 * s, by rw [hs]; push_cast; ring⟩]
    decide

/-- `i = 2`, `t ≡ 2 (mod 4)`: four solutions. -/
lemma nuSum_two_two (t : ℤ) (ht : t % 4 = 2) : nuSum t (2 ^ 2) = 4 := by
  unfold nuSum
  have hf : (Finset.range (2 ^ 2)).filter (fun b => Nat.Coprime b (2 ^ 2)) = {1, 3} := by decide
  rw [hf, Finset.sum_pair (by norm_num)]
  obtain ⟨s, hs⟩ : ∃ s, t = 4 * s + 2 := ⟨t / 4, by omega⟩
  have e1 : Nq (2 ^ 2) (t ^ 2 - 4 * ((1 : ℕ) : ℤ) ^ 2) = Nq (2 ^ 2) 0 :=
    Nq_congr _ ⟨s ^ 2 + s, by rw [hs]; push_cast; ring⟩
  have e3 : Nq (2 ^ 2) (t ^ 2 - 4 * ((3 : ℕ) : ℤ) ^ 2) = Nq (2 ^ 2) 0 :=
    Nq_congr _ ⟨s ^ 2 + s - 2, by rw [hs]; push_cast; ring⟩
  rw [e1, e3]
  decide

/-- **Lemma 6 for ℓ = 2, in the original counting.** -/
theorem nuSum_two (i : ℕ) (hi : 1 ≤ i) (t : ℤ) :
    nuSum t (2 ^ i) =
      if t % 2 = 1 then 0
      else if t % 4 = 2 then (if i = 1 then 1 else 2 ^ i)
      else (if i = 1 then 1 else 0) := by
  by_cases h1 : t % 2 = 1
  · simp only [h1, ite_true]; exact nuSum_two_odd i hi t h1
  simp only [h1, ite_false]
  by_cases h2 : t % 4 = 2
  · simp only [h2, ite_true]
    by_cases hi1 : i = 1
    · subst hi1; simp only [ite_true]; exact nuSum_two_one t (by omega)
    simp only [hi1, ite_false]
    by_cases hi2 : i = 2
    · subst hi2; exact nuSum_two_two t h2
    have : NeZero (2 ^ i) := ⟨by positivity⟩
    obtain ⟨u, rfl⟩ : ∃ u, t = 2 * u := ⟨t / 2, by omega⟩
    have := nuSum_two_main i (by omega) u (by omega)
    exact_mod_cast this
  · simp only [h2, ite_false]
    by_cases hi1 : i = 1
    · subst hi1; simp only [ite_true]; exact nuSum_two_one t (by omega)
    simp only [hi1, ite_false]
    exact nuSum_two_four i (by omega) t (by omega)

end TwoFinal

/-!
## Lemma 8(a): Kloosterman averages at primes

For a finite ring `R` and an additive character `ψ`, the sum of the Kloosterman sums
`S(a², 1; c) = Σ_{x unit} ψ(a² x + x⁻¹)` over units `a`. Everything here holds for any primitive
additive character with values in a domain of characteristic zero (for `ℂ`, `e(x/c)`).
-/

section KloostermanPrime

variable {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']

omit [IsDomain R'] [CharZero R'] in
/-- Sum over the units of a finite field. -/
lemma sum_units_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F] (f : F → R') :
    ∑ x : Fˣ, f x = ∑ x : F, f x - f 0 := by
  rw [← Finset.sum_erase_add _ _ (mem_univ (0 : F)), add_sub_cancel_right]
  refine Finset.sum_nbij' (fun u => (u : F))
    (fun x => if h : x = 0 then 1 else Units.mk0 x h) ?_ ?_ ?_ ?_ ?_
  · intro u _; simp [u.ne_zero]
  · intro x _; simp
  · intro u _; simp [u.ne_zero]
  · intro x hx
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hx
    simp [hx]
  · intro u _; rfl

omit [IsDomain R'] [CharZero R'] in
/-- `Σ_a f(a²) = Σ_u (χ(u) + 1) f(u)`, with values in `R'`. -/
lemma sum_sq' {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : F → R') :
    ∑ x : F, f (x ^ 2) = ∑ u : F, (((quadraticChar F u : ℤ) : R') + 1) * f u := by
  have h := Finset.sum_fiberwise' (univ : Finset F) (fun x : F => x ^ 2) f
  rw [← h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := congrArg (Int.cast : ℤ → R') (card_sq_eq hF u)
  push_cast at this
  exact this

/-- **Lemma 8(a) at an odd prime**: `Σ_{a unit} S(a², 1; p) = χ(−1) p + 1`. -/
theorem kloosterman_sum_odd_prime (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ψ : AddChar (ZMod p) R') (hψ : ψ.IsPrimitive) :
    ∑ a : (ZMod p)ˣ, ∑ x : (ZMod p)ˣ, ψ ((a : ZMod p) ^ 2 * x + ((x⁻¹ : (ZMod p)ˣ) : ZMod p)) =
      ((quadraticChar (ZMod p) (-1) : ℤ) : R') * p + 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set χ : MulChar (ZMod p) R' := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R') with hχ
  have hχapp : ∀ u, χ u = ((quadraticChar (ZMod p) u : ℤ) : R') := fun u => rfl
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic _).comp _
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hF)
  set g := gaussSum χ ψ with hg
  have hψ1 : ψ ≠ 1 := by
    have := hψ (one_ne_zero : (1 : ZMod p) ≠ 0)
    intro h; apply this; rw [h]; ext x; simp
  -- inner sum over a
  have hA : ∀ x : (ZMod p)ˣ, ∑ a : (ZMod p)ˣ, ψ ((a : ZMod p) ^ 2 * x) = χ x * g - 1 := by
    intro x
    rw [sum_units_eq (fun a => ψ (a ^ 2 * x))]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      AddChar.map_zero_eq_one]
    rw [sum_sq' hF (fun u => ψ (u * x))]
    simp only [add_mul, one_mul, Finset.sum_add_distrib]
    rw [AddChar.sum_mulShift (x : ZMod p) hψ]
    simp only [x.ne_zero, ite_false, Nat.cast_zero, add_zero]
    have h1 : ∑ u : ZMod p, ((quadraticChar (ZMod p) u : ℤ) : R') * ψ (u * x) =
        gaussSum χ (ψ.mulShift x) := by
      rw [gaussSum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [hχapp, AddChar.mulShift_apply, mul_comm (x : ZMod p)]
    rw [h1, gaussSum_mulShift_eq, hχq.inv]
  -- reindex and finish
  have hB : ∑ a : (ZMod p)ˣ, ∑ x : (ZMod p)ˣ,
      ψ ((a : ZMod p) ^ 2 * x + ((x⁻¹ : (ZMod p)ˣ) : ZMod p)) =
      ∑ x : (ZMod p)ˣ, ψ ((x⁻¹ : (ZMod p)ˣ) : ZMod p) * (χ x * g - 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hA x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.map_add_eq_mul, mul_comm]
  rw [hB]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hC : ∑ x : (ZMod p)ˣ, ψ ((x⁻¹ : (ZMod p)ˣ) : ZMod p) * (χ x * g) = g * g := by
    rw [show g * g = (∑ y : (ZMod p)ˣ, χ y * ψ y) * g by
      rw [sum_units_eq (fun y => χ y * ψ y), MulChar.map_zero, zero_mul, sub_zero]; rfl]
    rw [Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun x => ?_)
    simp only [Equiv.inv_apply]
    have : χ ((x⁻¹ : (ZMod p)ˣ) : ZMod p) = χ x := by
      rw [Units.val_inv_eq_inv_val, ← MulChar.inv_apply', hχq.inv]
    rw [this]
    ring
  have hD : ∑ x : (ZMod p)ˣ, ψ ((x⁻¹ : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [show ∑ x : (ZMod p)ˣ, ψ ((x⁻¹ : (ZMod p)ˣ) : ZMod p) = ∑ x : (ZMod p)ˣ, ψ x from
      Fintype.sum_equiv (Equiv.inv _) _ _ (fun x => rfl)]
    rw [sum_units_eq (fun y => ψ y), AddChar.sum_eq_zero_of_ne_one hψ1, AddChar.map_zero_eq_one]
    ring
  rw [hC, hD, ← sq, hg, gaussSum_sq hχ1 hχq hψ, hχapp, ZMod.card]
  ring

end KloostermanPrime

section KloostermanPowers

variable {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']

/-- If `h² = 0` and `2hu ≠ 0` for every unit `u`, then `Σ_{a unit} ψ(a² x) = 0` for every
unit `x`: the substitution `a ↦ a(1 + hy)` multiplies each term by `ψ(y · 2h a² x)`, and
averaging over `y` kills the sum. -/
lemma inner_vanish (c : ℕ) [NeZero c] (ψ : AddChar (ZMod c) R') (hψ : ψ.IsPrimitive)
    (h : ZMod c) (hh : h ^ 2 = 0) (hne : ∀ u : (ZMod c)ˣ, 2 * h * (u : ZMod c) ≠ 0)
    (x : (ZMod c)ˣ) : ∑ a : (ZMod c)ˣ, ψ ((a : ZMod c) ^ 2 * x) = 0 := by
  set S := ∑ a : (ZMod c)ˣ, ψ ((a : ZMod c) ^ 2 * x) with hS
  have hunit : ∀ y : ZMod c, IsUnit (1 + h * y) := fun y =>
    ⟨⟨1 + h * y, 1 - h * y, by linear_combination (-y ^ 2) * hh,
      by linear_combination (-y ^ 2) * hh⟩, rfl⟩
  have hshift : ∀ y : ZMod c, S = ∑ a : (ZMod c)ˣ,
      ψ ((a : ZMod c) ^ 2 * x) * ψ (y * (2 * h * ((a : ZMod c) ^ 2 * x))) := by
    intro y
    have e1 : S = ∑ a : (ZMod c)ˣ, ψ (((a * (hunit y).unit : (ZMod c)ˣ) : ZMod c) ^ 2 * x) :=
      (Fintype.sum_equiv (Equiv.mulRight (hunit y).unit) _ _ (fun a => rfl)).symm
    rw [e1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Units.val_mul, IsUnit.unit_spec]
    linear_combination ((a : ZMod c) ^ 2 * x * y ^ 2) * hh
  have hsum : (Fintype.card (ZMod c) : R') * S = 0 := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    rw [Finset.sum_congr rfl (fun y _ => hshift y), Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hb : 2 * h * ((a : ZMod c) ^ 2 * x) ≠ 0 := by
      have := hne (a ^ 2 * x)
      simpa [mul_assoc] using this
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
    simp only [hb, ite_false, Nat.cast_zero, mul_zero]
  have hc : (Fintype.card (ZMod c) : R') ≠ 0 := by
    rw [ZMod.card]; exact_mod_cast NeZero.ne c
  exact (mul_eq_zero.mp hsum).resolve_left hc

/-- Under the same hypotheses the whole Kloosterman average vanishes. -/
lemma kloosterman_sum_vanish (c : ℕ) [NeZero c] (ψ : AddChar (ZMod c) R') (hψ : ψ.IsPrimitive)
    (h : ZMod c) (hh : h ^ 2 = 0) (hne : ∀ u : (ZMod c)ˣ, 2 * h * (u : ZMod c) ≠ 0) :
    ∑ a : (ZMod c)ˣ, ∑ x : (ZMod c)ˣ, ψ ((a : ZMod c) ^ 2 * x + ((x⁻¹ : (ZMod c)ˣ) : ZMod c)) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun x _ => ?_
  simp_rw [AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul, inner_vanish c ψ hψ h hh hne x, zero_mul]

lemma two_h_ne_zero {c : ℕ} [NeZero c] (h : ZMod c) (h2 : 2 * h ≠ 0) (u : (ZMod c)ˣ) :
    2 * h * (u : ZMod c) ≠ 0 := by
  intro H
  apply h2
  have := congrArg (· * ((u⁻¹ : (ZMod c)ˣ) : ZMod c)) H
  simpa [mul_assoc] using this

/-- **Lemma 8(a) at odd prime powers**: `Σ_{a unit} S(a², 1; ℓ^j) = 0` for `j ≥ 2`. -/
theorem kloosterman_sum_odd_prime_pow (l : ℕ) [hl : Fact l.Prime] (hl2 : l ≠ 2) (j : ℕ)
    (hj : 2 ≤ j) [NeZero (l ^ j)] (ψ : AddChar (ZMod (l ^ j)) R') (hψ : ψ.IsPrimitive) :
    ∑ a : (ZMod (l ^ j))ˣ, ∑ x : (ZMod (l ^ j))ˣ,
      ψ ((a : ZMod (l ^ j)) ^ 2 * x + ((x⁻¹ : (ZMod (l ^ j))ˣ) : ZMod (l ^ j))) = 0 := by
  refine kloosterman_sum_vanish _ ψ hψ ((l ^ (j - 1) : ℕ) : ZMod (l ^ j)) ?_ ?_
  · rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow l (by omega)
  · apply two_h_ne_zero
    rw [show (2 : ZMod (l ^ j)) = ((2 : ℕ) : ZMod (l ^ j)) by norm_cast, ← Nat.cast_mul, Ne,
      ZMod.natCast_eq_zero_iff]
    intro hd
    rw [show l ^ j = l ^ (j - 1) * l by rw [← pow_succ]; congr 1; omega, mul_comm 2] at hd
    have h2 : l ∣ 2 := (Nat.mul_dvd_mul_iff_left (pow_pos hl.out.pos _)).mp hd
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).mp h2)

/-- **Lemma 8(a) at `2^j`, `j ≥ 4`**: `Σ_{a unit} S(a², 1; 2^j) = 0`. -/
theorem kloosterman_sum_two_pow (j : ℕ) (hj : 4 ≤ j) [NeZero (2 ^ j)]
    (ψ : AddChar (ZMod (2 ^ j)) R') (hψ : ψ.IsPrimitive) :
    ∑ a : (ZMod (2 ^ j))ˣ, ∑ x : (ZMod (2 ^ j))ˣ,
      ψ ((a : ZMod (2 ^ j)) ^ 2 * x + ((x⁻¹ : (ZMod (2 ^ j))ˣ) : ZMod (2 ^ j))) = 0 := by
  refine kloosterman_sum_vanish _ ψ hψ ((2 ^ (j - 2) : ℕ) : ZMod (2 ^ j)) ?_ ?_
  · rw [← Nat.cast_pow, ← pow_mul, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow 2 (by omega)
  · apply two_h_ne_zero
    rw [show (2 : ZMod (2 ^ j)) = ((2 : ℕ) : ZMod (2 ^ j)) by norm_cast, ← Nat.cast_mul, Ne,
      ZMod.natCast_eq_zero_iff, ← pow_succ']
    intro hd
    have := Nat.le_of_dvd (by positivity) hd
    have h' : 2 ^ (j - 2 + 1) < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end KloostermanPowers

section KloostermanSmall

variable {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']

lemma units_inv_of_sq_one {c : ℕ} (a : (ZMod c)ˣ) (h : (a : ZMod c) ^ 2 = 1) :
    ((a⁻¹ : (ZMod c)ˣ) : ZMod c) = a := by
  calc ((a⁻¹ : (ZMod c)ˣ) : ZMod c) = ((a⁻¹ : (ZMod c)ˣ) : ZMod c) * ((a : ZMod c) * a) := by
        rw [← sq, h, mul_one]
    _ = (((a⁻¹ : (ZMod c)ˣ) : ZMod c) * a) * a := by ring
    _ = a := by rw [Units.inv_mul, one_mul]

omit [IsDomain R'] [CharZero R'] in
/-- When every unit squares to 1, the average is `φ(c) · Σ_x ψ(2x)`. -/
lemma kloosterman_sum_sq_one (c : ℕ) [NeZero c] (hsq : ∀ a : (ZMod c)ˣ, (a : ZMod c) ^ 2 = 1)
    (ψ : AddChar (ZMod c) R') :
    ∑ a : (ZMod c)ˣ, ∑ x : (ZMod c)ˣ, ψ ((a : ZMod c) ^ 2 * x + ((x⁻¹ : (ZMod c)ˣ) : ZMod c)) =
      (Fintype.card (ZMod c)ˣ : R') * ∑ x : (ZMod c)ˣ, ψ (2 * x) := by
  have : ∀ a : (ZMod c)ˣ, ∑ x : (ZMod c)ˣ,
      ψ ((a : ZMod c) ^ 2 * x + ((x⁻¹ : (ZMod c)ˣ) : ZMod c)) = ∑ x : (ZMod c)ˣ, ψ (2 * x) := by
    intro a
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsq a, one_mul, units_inv_of_sq_one x (hsq x), two_mul]
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [CharZero R'] in
/-- A primitive additive character takes the value `−1` at an element of order two. -/
lemma addChar_order_two (n : ℕ) [NeZero n] (ψ : AddChar (ZMod n) R') (hψ : ψ.IsPrimitive)
    (b : ZMod n) (hb : b ≠ 0) (hb2 : 2 * b = 0) : ψ b = -1 := by
  have hsq : ψ b * ψ b = 1 := by rw [← AddChar.map_add_eq_mul, ← two_mul, hb2, AddChar.map_zero_eq_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exfalso
    apply hψ hb
    ext z
    rw [AddChar.mulShift_apply, AddChar.one_apply]
    have : b * z = z.val • b := by
      rw [nsmul_eq_mul, mul_comm]
      congr 1
      exact (ZMod.natCast_zmod_val z).symm
    rw [this, AddChar.map_nsmul_eq_pow, h, one_pow]
  · exact h

omit [IsDomain R'] [CharZero R'] in
/-- **Lemma 8(a) at `c = 2`**: the sum is `1`. -/
theorem kloosterman_sum_two (ψ : AddChar (ZMod 2) R') :
    ∑ a : (ZMod 2)ˣ, ∑ x : (ZMod 2)ˣ, ψ ((a : ZMod 2) ^ 2 * x + ((x⁻¹ : (ZMod 2)ˣ) : ZMod 2)) = 1 := by
  rw [kloosterman_sum_sq_one 2 (by decide) ψ]
  have h2 : ∀ x : (ZMod 2)ˣ, (2 : ZMod 2) * x = 0 := by decide
  simp only [h2, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  rw [ZMod.card_units_eq_totient]
  norm_num [Nat.totient_two]

omit [CharZero R'] in
/-- **Lemma 8(a) at `c = 4`**: the sum is `−4`. -/
theorem kloosterman_sum_four (ψ : AddChar (ZMod 4) R') (hψ : ψ.IsPrimitive) :
    ∑ a : (ZMod 4)ˣ, ∑ x : (ZMod 4)ˣ, ψ ((a : ZMod 4) ^ 2 * x + ((x⁻¹ : (ZMod 4)ˣ) : ZMod 4)) = -4 := by
  rw [kloosterman_sum_sq_one 4 (by decide) ψ]
  have h2 : ∀ x : (ZMod 4)ˣ, (2 : ZMod 4) * x = 2 := by decide
  simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [addChar_order_two 4 ψ hψ 2 (by decide) (by decide)]
  have hc : Fintype.card (ZMod 4)ˣ = 2 := by rw [ZMod.card_units_eq_totient]; decide
  rw [hc]
  norm_num

/-- **Lemma 8(a) at `c = 8`**: the sum is `0`. -/
theorem kloosterman_sum_eight (ψ : AddChar (ZMod 8) R') (hψ : ψ.IsPrimitive) :
    ∑ a : (ZMod 8)ˣ, ∑ x : (ZMod 8)ˣ, ψ ((a : ZMod 8) ^ 2 * x + ((x⁻¹ : (ZMod 8)ˣ) : ZMod 8)) = 0 := by
  rw [kloosterman_sum_sq_one 8 (by decide) ψ]
  set T := ∑ x : (ZMod 8)ˣ, ψ (2 * x) with hT
  have h4 : ψ 4 = -1 := addChar_order_two 8 ψ hψ 4 (by decide) (by decide)
  have hx4 : ∀ x : (ZMod 8)ˣ, (4 : ZMod 8) * x = 4 := by decide
  let u3 : (ZMod 8)ˣ := ZMod.unitOfCoprime 3 (by norm_num)
  have hneg : T = -T := by
    have e : T = ∑ x : (ZMod 8)ˣ, ψ (2 * ((u3 * x : (ZMod 8)ˣ) : ZMod 8)) :=
      (Fintype.sum_equiv (Equiv.mulLeft u3) _ _ (fun x => rfl)).symm
    refine e.trans ?_
    calc ∑ x : (ZMod 8)ˣ, ψ (2 * ((u3 * x : (ZMod 8)ˣ) : ZMod 8))
        = ∑ x : (ZMod 8)ˣ, -ψ (2 * x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have hu3 : ((u3 : (ZMod 8)ˣ) : ZMod 8) = 3 := rfl
          rw [Units.val_mul, hu3, show (2 : ZMod 8) * (3 * x) = 2 * x + 4 * x by ring,
            AddChar.map_add_eq_mul, hx4, h4]
          ring
      _ = -T := by rw [Finset.sum_neg_distrib, hT]
  have hT0 : T = 0 := by
    have : (2 : R') * T = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  rw [hT0, mul_zero]

end KloostermanSmall

/-!
## Lemma 8(b): the local identity

`ν_t(q) = nuSum t q / φ(q)`, `δ_t(ℓ^j) = Σ_{i ≤ j} (−1)^(j−i) ν_t(ℓ^i)` (recursively
`δ_{j+1} = ν_{j+1} − δ_j`, `δ_0 = ν_t(1) = 1`), and `E_ℓ(t) = Σ_j δ_t(ℓ^j) ℓ^(−j)`.
-/

section LocalIdentity

/-- `ν_t(q)`. -/
noncomputable def nuQ (t : ℤ) (q : ℕ) : ℚ := (nuSum t q : ℚ) / Nat.totient q

/-- `δ_t(ℓ^j)`. -/
noncomputable def deltaQ (t : ℤ) (l : ℕ) : ℕ → ℚ
  | 0 => 1
  | (j + 1) => nuQ t (l ^ (j + 1)) - deltaQ t l j

lemma nuQ_one (t : ℤ) : nuQ t 1 = 1 := by
  unfold nuQ nuSum
  have hf : (Finset.range 1).filter (fun b => Nat.Coprime b 1) = {0} := by decide
  rw [hf, Finset.sum_singleton]
  obtain ⟨s, hs | hs⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
  · rw [Nq_congr 1 (D' := 0) ⟨s ^ 2, by rw [hs]; push_cast; ring⟩]
    norm_num [show Nq 1 0 = 1 by decide]
  · rw [Nq_congr 1 (D' := 1) ⟨s ^ 2 + s, by rw [hs]; push_cast; ring⟩]
    norm_num [show Nq 1 1 = 1 by decide]

section Odd

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ν_t(p^i)` for an odd prime `p` and `i ≥ 1`. -/
noncomputable def nuOdd (t : ℤ) : ℚ :=
  if (p : ℤ) ∣ t then 1 + chi4 p else ((p : ℚ) - 2 - chi4 p) / ((p : ℚ) - 1)

lemma nuQ_odd_eq (hp2 : p ≠ 2) {i : ℕ} (hi : 1 ≤ i) (t : ℤ) : nuQ t (p ^ i) = nuOdd p t := by
  have : NeZero (p ^ i) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  unfold nuQ nuOdd
  have h := nuSum_odd p i hp2 (by omega) t
  rw [Nat.totient_prime_pow hp.out (by omega)]
  have hp1 : (p : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  have hpi : ((p : ℚ) ^ (i - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hq : ((nuSum t (p ^ i) : ℕ) : ℚ) = ((nuSum t (p ^ i) : ℤ) : ℚ) := by norm_cast
  rw [hq, h]
  push_cast [Nat.sub_le, hp.out.one_lt.le]
  split_ifs
  · field_simp
  · field_simp

lemma deltaQ_odd (hp2 : p ≠ 2) (t : ℤ) (j : ℕ) :
    deltaQ t p j = if Even j then 1 else nuOdd p t - 1 := by
  induction j with
  | zero => simp [deltaQ]
  | succ j ih =>
    rw [deltaQ, ih, nuQ_odd_eq p hp2 (by omega) t]
    rcases Nat.even_or_odd j with he | ho
    · have : ¬ Even (j + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
      simp only [he, this, ite_true, ite_false]
    · have : Even (j + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr ho
      have hne : ¬ Even j := Nat.not_even_iff_odd.mpr ho
      simp only [hne, this, ite_true, ite_false]
      ring

/-- **Lemma 6, Euler factor at an odd prime**: `E_p(t) = (1 + (ν − 1)/p)/(1 − 1/p²)`. -/
theorem hasSum_E_odd (hp2 : p ≠ 2) (t : ℤ) :
    HasSum (fun j => (deltaQ t p j : ℝ) / (p : ℝ) ^ j)
      ((1 + ((nuOdd p t : ℝ) - 1) / p) / (1 - 1 / (p : ℝ) ^ 2)) := by
  set x : ℝ := 1 / p with hx
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hx0 : 0 ≤ x ^ 2 := sq_nonneg _
  have hx1 : x ^ 2 < 1 := by
    rw [hx, div_pow, one_pow]
    exact (div_lt_one (by positivity)).mpr (by nlinarith)
  have hg := hasSum_geometric_of_lt_one hx0 hx1
  have heq : ∀ j, (deltaQ t p j : ℝ) / (p : ℝ) ^ j =
      x ^ j * (if Even j then 1 else ((nuOdd p t : ℝ) - 1)) := by
    intro j
    rw [deltaQ_odd p hp2 t j, hx, div_pow, one_pow]
    split_ifs <;> push_cast <;> ring
  simp_rw [heq]
  have he : HasSum (fun k => x ^ (2 * k) * (if Even (2 * k) then 1 else ((nuOdd p t : ℝ) - 1)))
      (1 - x ^ 2)⁻¹ := by
    simp only [even_two_mul, ite_true, mul_one, pow_mul]
    exact hg
  have ho : HasSum (fun k => x ^ (2 * k + 1) *
      (if Even (2 * k + 1) then 1 else ((nuOdd p t : ℝ) - 1)))
      (((nuOdd p t : ℝ) - 1) * x * (1 - x ^ 2)⁻¹) := by
    have hodd : ∀ k : ℕ, ¬ Even (2 * k + 1) := fun k => by
      rw [Nat.even_add_one]; exact not_not.mpr (even_two_mul k)
    simp only [hodd, ite_false]
    have := hg.mul_left (((nuOdd p t : ℝ) - 1) * x)
    convert this using 1
    funext k
    rw [pow_succ, pow_mul]
    ring
  have hv : (1 + ((nuOdd p t : ℝ) - 1) / p) / (1 - 1 / (p : ℝ) ^ 2) =
      (1 - x ^ 2)⁻¹ + ((nuOdd p t : ℝ) - 1) * x * (1 - x ^ 2)⁻¹ := by
    rw [hx]; ring
  rw [hv]
  exact he.even_add_odd ho

/-- Ramanujan sum `c_p(t) = Σ_{a unit} ψ(a t)`. -/
lemma ramanujan_prime {R' : Type*} [CommRing R'] [IsDomain R'] (ψ : AddChar (ZMod p) R')
    (hψ : ψ.IsPrimitive) (t : ZMod p) :
    ∑ a : (ZMod p)ˣ, ψ (a * t) = if t = 0 then (p : R') - 1 else -1 := by
  rw [sum_units_eq (fun a => ψ (a * t)), AddChar.sum_mulShift t hψ, zero_mul,
    AddChar.map_zero_eq_one, ZMod.card]
  split_ifs <;> ring

/-- **Lemma 8(b) at an odd prime.** `E_p(t) = G(1) c_1 + G(p) c_p(t)` with
`G(p) = A₂(p)/(p² − 1)`, `A₂(p) = (Σ_{a unit} S(a², 1; p))/(p − 1)`; the terms `j ≥ 2` vanish
because `A₂(p^j) = 0` (`kloosterman_sum_odd_prime_pow`). -/
theorem local_identity_odd (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (t : ℤ) :
    (((1 + ((nuOdd p t : ℝ) - 1) / p) / (1 - 1 / (p : ℝ) ^ 2) : ℝ) : ℂ) =
      1 + ((∑ a : (ZMod p)ˣ, ∑ x : (ZMod p)ˣ,
          ψ ((a : ZMod p) ^ 2 * x + ((x⁻¹ : (ZMod p)ˣ) : ZMod p))) / ((p : ℂ) - 1)) /
        ((p : ℂ) ^ 2 - 1) * ∑ a : (ZMod p)ˣ, ψ (a * (t : ZMod p)) := by
  rw [kloosterman_sum_odd_prime p hp2 ψ hψ, ramanujan_prime p ψ hψ,
    quadraticChar_neg_one_eq_chi4 p hp2]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hc : chi4 p = 1 ∨ chi4 p = -1 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    unfold chi4
    have : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases this with h | h <;> simp [h]
  have hpc : (p : ℂ) - 1 ≠ 0 := by
    have : (p : ℂ) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
    exact sub_ne_zero.mpr this
  have hpc2 : (p : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (p : ℂ) ^ 2 ≠ 1 := by
      have : (1 : ℕ) < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
      exact_mod_cast this.ne'
    exact sub_ne_zero.mpr this
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold nuOdd
  split_ifs with h
  · push_cast
    rcases hc with hc | hc <;> rw [hc] <;> field_simp <;> ring
  · push_cast
    rcases hc with hc | hc <;> rw [hc] <;> field_simp <;> ring

end Odd

section Two

lemma nuQ_two (i : ℕ) (hi : 1 ≤ i) (t : ℤ) :
    nuQ t (2 ^ i) = if t % 2 = 1 then 0 else if t % 4 = 2 then (if i = 1 then 1 else 2)
      else (if i = 1 then 1 else 0) := by
  unfold nuQ
  rw [nuSum_two i hi t, Nat.totient_prime_pow Nat.prime_two (by omega)]
  by_cases h1 : t % 2 = 1
  · simp [h1]
  · by_cases h2 : t % 4 = 2
    · by_cases hi1 : i = 1
      · subst hi1; simp [h1, h2]
      · simp only [h1, h2, hi1, ite_false, ite_true]
        have hpow : (2 : ℚ) ^ i = 2 ^ (i - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel hi]
        push_cast
        rw [hpow]
        field_simp
    · by_cases hi1 : i = 1
      · subst hi1; simp [h1, h2]
      · simp [h1, h2, hi1]

/-- The value of `E_2(t)`. -/
noncomputable def E2 (t : ℤ) : ℝ := if t % 2 = 1 then 2 / 3 else if t % 4 = 2 then 5 / 3 else 1

/-- **Lemma 6, Euler factor at 2**: `E_2(t) = 2/3, 5/3, 1` for `t` odd, `2 ∥ t`, `4 ∣ t`. -/
theorem hasSum_E_two (t : ℤ) :
    HasSum (fun j => (deltaQ t 2 j : ℝ) / (2 : ℝ) ^ j) (E2 t) := by
  unfold E2
  by_cases h1 : t % 2 = 1
  · have hd : ∀ j, deltaQ t 2 j = (-1) ^ j := by
      intro j
      induction j with
      | zero => simp [deltaQ]
      | succ j ih =>
        rw [deltaQ, ih, nuQ_two (j + 1) (by omega) t]
        simp only [h1, ite_true]
        ring
    have hf : (fun j => (deltaQ t 2 j : ℝ) / (2 : ℝ) ^ j) = fun j => (-1 / 2 : ℝ) ^ j := by
      funext j; rw [hd j, div_pow]; push_cast; ring
    rw [hf]
    simp only [h1, ite_true]
    have hg := hasSum_geometric_of_abs_lt_one (r := (-1 / 2 : ℝ)) (by norm_num [abs_div])
    have hv : (1 - (-1 / 2 : ℝ))⁻¹ = 2 / 3 := by norm_num
    rw [← hv]; exact hg
  · simp only [h1, ite_false]
    by_cases h2 : t % 4 = 2
    · simp only [h2, ite_true]
      have hd : ∀ j, deltaQ t 2 j = if j = 0 then 1 else if Even j then 2 else 0 := by
        intro j
        induction j with
        | zero => simp [deltaQ]
        | succ j ih =>
          rw [deltaQ, ih, nuQ_two (j + 1) (by omega) t]
          simp only [h1, h2, ite_true, ite_false]
          rcases Nat.even_or_odd j with he | ho
          · by_cases hj : j = 0
            · subst hj; norm_num
            · have h1' : j + 1 ≠ 1 := by omega
              have hne : ¬ Even (j + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
              simp [hj, he, hne]
          · have hno : ¬ Even j := Nat.not_even_iff_odd.mpr ho
            have hj : j ≠ 0 := by rintro rfl; exact hno ⟨0, rfl⟩
            have h1' : j + 1 ≠ 1 := by omega
            have hev : Even (j + 1) := by rw [Nat.even_add_one]; exact hno
            simp [hj, hev, hno]
      have hf : (fun j => (deltaQ t 2 j : ℝ) / (2 : ℝ) ^ j) =
          fun j => if j = 0 then (1 : ℝ) else if Even j then 2 / 2 ^ j else 0 := by
        funext j; rw [hd j]; split_ifs with hj <;> push_cast <;> simp [hj]
      rw [hf]
      have he : HasSum (fun k : ℕ => if 2 * k = 0 then (1 : ℝ) else
          if Even (2 * k) then 2 / 2 ^ (2 * k) else 0) (5 / 3) := by
        have hg := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
          (by norm_num)).mul_left 2
        have hs := hg.sub (hasSum_ite_eq 0 (1 : ℝ))
        have hv : 2 * (1 - 1 / 4 : ℝ)⁻¹ - 1 = 5 / 3 := by norm_num
        rw [hv] at hs
        convert hs using 1
        funext k
        by_cases hk : k = 0
        · subst hk; norm_num
        · have hk2 : 2 * k ≠ 0 := by omega
          simp only [hk2, hk, even_two_mul, ite_true, ite_false, sub_zero]
          rw [pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num, div_pow, one_pow]
          ring
      have ho : HasSum (fun k : ℕ => if 2 * k + 1 = 0 then (1 : ℝ) else
          if Even (2 * k + 1) then 2 / 2 ^ (2 * k + 1) else 0) 0 := by
        have hodd : ∀ k : ℕ, ¬ Even (2 * k + 1) := fun k => by
          rw [Nat.even_add_one]; exact not_not.mpr (even_two_mul k)
        have hz : (fun k : ℕ => if 2 * k + 1 = 0 then (1 : ℝ) else
            if Even (2 * k + 1) then 2 / 2 ^ (2 * k + 1) else 0) = fun _ => 0 := by
          funext k; simp [hodd k]
        rw [hz]; exact hasSum_zero
      have := HasSum.even_add_odd
        (f := fun j => if j = 0 then (1 : ℝ) else if Even j then 2 / 2 ^ j else 0) he ho
      rwa [add_zero] at this
    · simp only [h2, ite_false]
      have hd : ∀ j, deltaQ t 2 j = if j = 0 then 1 else 0 := by
        intro j
        induction j with
        | zero => simp [deltaQ]
        | succ j ih =>
          rw [deltaQ, ih, nuQ_two (j + 1) (by omega) t]
          simp only [h1, h2, ite_false]
          by_cases hj : j = 0
          · subst hj; norm_num
          · simp [hj]
      have hf : (fun j => (deltaQ t 2 j : ℝ) / (2 : ℝ) ^ j) = fun j => if j = 0 then (1 : ℝ) else 0 := by
        funext j; rw [hd j]; split_ifs with hj <;> simp [hj]
      rw [hf]
      exact hasSum_ite_eq 0 1

/-- Ramanujan sum mod 2. -/
lemma ramanujan_two {R' : Type*} [CommRing R'] [IsDomain R'] (ψ : AddChar (ZMod 2) R')
    (hψ : ψ.IsPrimitive) (t : ℤ) :
    ∑ a : (ZMod 2)ˣ, ψ (a * (t : ZMod 2)) = if t % 2 = 1 then -1 else 1 := by
  have hu : (univ : Finset (ZMod 2)ˣ) = {1} := by decide
  rw [hu, Finset.sum_singleton, Units.val_one, one_mul]
  obtain h | h : t % 2 = 0 ∨ t % 2 = 1 := by omega
  · have ht : (t : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; omega
    rw [ht, AddChar.map_zero_eq_one]; simp [h]
  · have ht : (t : ZMod 2) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff' t 1 2).mpr (by push_cast; omega)
      simpa using this
    rw [ht, addChar_order_two 2 ψ hψ 1 (by decide) (by decide)]; simp [h]

/-- Ramanujan sum mod 4. -/
lemma ramanujan_four {R' : Type*} [CommRing R'] [IsDomain R'] (ψ : AddChar (ZMod 4) R')
    (hψ : ψ.IsPrimitive) (t : ℤ) :
    ∑ a : (ZMod 4)ˣ, ψ (a * (t : ZMod 4)) =
      if t % 2 = 1 then 0 else if t % 4 = 2 then -2 else 2 := by
  have hu : (univ : Finset (ZMod 4)ˣ) = {1, -1} := by decide
  rw [hu, Finset.sum_pair (by decide), Units.val_one, one_mul, Units.val_neg, Units.val_one,
    neg_one_mul]
  have h2 : ψ 2 = -1 := addChar_order_two 4 ψ hψ 2 (by decide) (by decide)
  have hcast : ∀ r : ℤ, t % 4 = r → (t : ZMod 4) = (r : ZMod 4) := fun r hr =>
    (ZMod.intCast_eq_intCast_iff' t r 4).mpr (by push_cast; omega)
  obtain h | h | h | h : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  · rw [hcast 0 h]
    simp only [show ¬ t % 2 = 1 by omega, show ¬ t % 4 = 2 by omega, ite_false]
    push_cast
    rw [neg_zero, AddChar.map_zero_eq_one]; norm_num
  · rw [hcast 1 h]
    simp only [show t % 2 = 1 by omega, ite_true]
    push_cast
    rw [show (-1 : ZMod 4) = 1 + 2 by decide, AddChar.map_add_eq_mul, h2]; ring
  · rw [hcast 2 h]
    simp only [show ¬ t % 2 = 1 by omega, h, ite_true, ite_false]
    push_cast
    rw [show (-2 : ZMod 4) = 2 by decide, h2]; ring
  · rw [hcast 3 h]
    simp only [show t % 2 = 1 by omega, ite_true]
    push_cast
    rw [show (-3 : ZMod 4) = 1 by decide, show (3 : ZMod 4) = 1 + 2 by decide,
      AddChar.map_add_eq_mul, h2]; ring

/-- **Lemma 8(b) at 2.** `E_2(t) = G(1) + G(2) c_2(t) + G(4) c_4(t)` with `G(2) = A₂(2)/3`,
`G(4) = A₂(4)/12`, `A₂(c) = (Σ_{a unit} S(a², 1; c))/φ(c)`; the terms `2^j`, `j ≥ 3`, vanish
because `A₂(2^j) = 0` (`kloosterman_sum_eight`, `kloosterman_sum_two_pow`). -/
theorem local_identity_two (ψ₂ : AddChar (ZMod 2) ℂ) (hψ₂ : ψ₂.IsPrimitive)
    (ψ₄ : AddChar (ZMod 4) ℂ) (hψ₄ : ψ₄.IsPrimitive) (t : ℤ) :
    ((E2 t : ℝ) : ℂ) =
      1 + ((∑ a : (ZMod 2)ˣ, ∑ x : (ZMod 2)ˣ,
          ψ₂ ((a : ZMod 2) ^ 2 * x + ((x⁻¹ : (ZMod 2)ˣ) : ZMod 2))) / 1) / 3 *
          ∑ a : (ZMod 2)ˣ, ψ₂ (a * (t : ZMod 2)) +
        ((∑ a : (ZMod 4)ˣ, ∑ x : (ZMod 4)ˣ,
          ψ₄ ((a : ZMod 4) ^ 2 * x + ((x⁻¹ : (ZMod 4)ˣ) : ZMod 4))) / 2) / 12 *
          ∑ a : (ZMod 4)ˣ, ψ₄ (a * (t : ZMod 4)) := by
  rw [kloosterman_sum_two ψ₂, kloosterman_sum_four ψ₄ hψ₄, ramanujan_two ψ₂ hψ₂,
    ramanujan_four ψ₄ hψ₄]
  unfold E2
  split_ifs <;> push_cast <;> norm_num

end Two

end LocalIdentity

/-!
## Lemma 8(a): multiplicativity

`KS ψ = Σ_{a, x units} ψ(a² x + x⁻¹)` over a finite commutative ring. By the Chinese remainder
theorem it factors over coprime moduli, with primitive characters on the factors; combined with
the prime-power values this gives `KS` for every modulus.
-/

section KSMult

variable {R' : Type*} [CommRing R']

/-- The Kloosterman average `Σ_{a unit} S(a², 1)` (times `φ`) for a finite commutative ring. -/
def KS {R : Type*} [CommRing R] [Fintype Rˣ] (ψ : AddChar R R') : R' :=
  ∑ a : Rˣ, ∑ x : Rˣ, ψ ((a : R) ^ 2 * x + ((x⁻¹ : Rˣ) : R))

/-- `KS` is invariant under ring isomorphisms. -/
lemma KS_equiv {S T : Type*} [CommRing S] [CommRing T] [Fintype Sˣ] [Fintype Tˣ]
    (e : S ≃+* T) (ψ : AddChar S R') :
    KS ψ = KS (ψ.compAddMonoidHom e.symm.toAddMonoidHom) := by
  unfold KS
  refine Fintype.sum_equiv (Units.mapEquiv e.toMulEquiv) _ _ (fun a => ?_)
  refine Fintype.sum_equiv (Units.mapEquiv e.toMulEquiv) _ _ (fun x => ?_)
  have hinv : ((Units.mapEquiv e.toMulEquiv x)⁻¹ : Tˣ) = Units.mapEquiv e.toMulEquiv x⁻¹ :=
    (map_inv _ x).symm
  show ψ ((a : S) ^ 2 * x + ((x⁻¹ : Sˣ) : S)) =
    ψ (e.symm (e (a : S) ^ 2 * e (x : S) + e ((x⁻¹ : Sˣ) : S)))
  rw [← map_pow, ← map_mul, ← map_add, RingEquiv.symm_apply_apply]

/-- The character `(y₁, y₂) ↦ ψ₁(y₁) ψ₂(y₂)` on a product ring. -/
def prodChar {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (ψ₁ : AddChar R₁ R') (ψ₂ : AddChar R₂ R') :
    AddChar (R₁ × R₂) R' :=
  ψ₁.compAddMonoidHom (AddMonoidHom.fst R₁ R₂) * ψ₂.compAddMonoidHom (AddMonoidHom.snd R₁ R₂)

lemma KS_prod {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [Fintype R₁ˣ] [Fintype R₂ˣ]
    [Fintype (R₁ × R₂)ˣ] (ψ₁ : AddChar R₁ R') (ψ₂ : AddChar R₂ R') :
    KS (prodChar ψ₁ ψ₂) = KS ψ₁ * KS ψ₂ := by
  calc KS (prodChar ψ₁ ψ₂) = ∑ p : R₁ˣ × R₂ˣ, ∑ q : R₁ˣ × R₂ˣ,
        ψ₁ ((p.1 : R₁) ^ 2 * q.1 + ((q.1⁻¹ : R₁ˣ) : R₁)) *
          ψ₂ ((p.2 : R₂) ^ 2 * q.2 + ((q.2⁻¹ : R₂ˣ) : R₂)) := by
        unfold KS
        refine Fintype.sum_equiv (MulEquiv.prodUnits).toEquiv _ _ (fun u => ?_)
        refine Fintype.sum_equiv (MulEquiv.prodUnits).toEquiv _ _ (fun v => ?_)
        rfl
    _ = KS ψ₁ * KS ψ₂ := by
        unfold KS
        simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Every character of a product ring is a `prodChar`. -/
lemma eq_prodChar {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (ψ : AddChar (R₁ × R₂) R') :
    ψ = prodChar (ψ.compAddMonoidHom (AddMonoidHom.inl R₁ R₂))
      (ψ.compAddMonoidHom (AddMonoidHom.inr R₁ R₂)) := by
  ext y
  simp only [prodChar, AddChar.mul_apply, AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.coe_snd, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
    ← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp

lemma isPrimitive_inl {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] {ψ : AddChar (R₁ × R₂) R'}
    (hψ : ψ.IsPrimitive) : (ψ.compAddMonoidHom (AddMonoidHom.inl R₁ R₂)).IsPrimitive := by
  intro z hz h
  apply hψ (a := (z, 0)) (by simp [hz])
  ext y
  have := congrArg (· y.1) h
  simp only [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, AddMonoidHom.inl_apply,
    AddChar.one_apply] at this ⊢
  rw [← this]
  congr 1
  ext <;> simp

lemma isPrimitive_inr {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] {ψ : AddChar (R₁ × R₂) R'}
    (hψ : ψ.IsPrimitive) : (ψ.compAddMonoidHom (AddMonoidHom.inr R₁ R₂)).IsPrimitive := by
  intro z hz h
  apply hψ (a := (0, z)) (by simp [hz])
  ext y
  have := congrArg (· y.2) h
  simp only [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, AddMonoidHom.inr_apply,
    AddChar.one_apply] at this ⊢
  rw [← this]
  congr 1
  ext <;> simp

lemma isPrimitive_equiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T)
    {ψ : AddChar S R'} (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.symm.toAddMonoidHom).IsPrimitive := by
  intro t ht h
  apply hψ (a := e.symm t) (by simpa using ht)
  ext y
  have := congrArg (· (e y)) h
  change ψ (e.symm (t * e y)) = 1 at this
  rw [map_mul, RingEquiv.symm_apply_apply] at this
  simpa using this

/-- **Multiplicativity**: for coprime `m, n` and a primitive `ψ` mod `mn`, `KS ψ` is a product of
`KS` of primitive characters mod `m` and mod `n`. -/
theorem KS_mul (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) R') (hψ : ψ.IsPrimitive) :
    ∃ (ψ₁ : AddChar (ZMod m) R') (ψ₂ : AddChar (ZMod n) R'), ψ₁.IsPrimitive ∧ ψ₂.IsPrimitive ∧
      KS ψ = KS ψ₁ * KS ψ₂ := by
  set e := ZMod.chineseRemainder h
  set ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hψ' : ψ'.IsPrimitive := isPrimitive_equiv e hψ
  refine ⟨ψ'.compAddMonoidHom (AddMonoidHom.inl _ _), ψ'.compAddMonoidHom (AddMonoidHom.inr _ _),
    isPrimitive_inl hψ', isPrimitive_inr hψ', ?_⟩
  rw [KS_equiv e ψ, ← KS_prod, ← eq_prodChar]

end KSMult

section KSFormula

variable {R' : Type*} [CommRing R'] [IsDomain R'] [CharZero R']

/-- The local value of `KS` at `p^k` (`k ≥ 1`), from Lemma 8(a). -/
def localK (p k : ℕ) : ℤ :=
  if k = 0 then 1
  else if p = 2 then (if k = 1 then 1 else if k = 2 then -4 else 0)
  else (if k = 1 then chi4 p * p + 1 else 0)

omit [IsDomain R'] [CharZero R'] in
lemma KS_one (ψ : AddChar (ZMod 1) R') : KS ψ = 1 := by
  unfold KS
  have h : ∀ y : ZMod 1, y = 0 := fun y => Subsingleton.elim _ _
  have hu : (univ : Finset (ZMod 1)ˣ) = {1} := by decide
  simp only [hu, Finset.sum_singleton]
  rw [h (((1 : (ZMod 1)ˣ) : ZMod 1) ^ 2 * ((1 : (ZMod 1)ˣ) : ZMod 1) +
    (((1 : (ZMod 1)ˣ)⁻¹ : (ZMod 1)ˣ) : ZMod 1)), AddChar.map_zero_eq_one]

lemma KS_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) [NeZero (p ^ k)]
    (ψ : AddChar (ZMod (p ^ k)) R') (hψ : ψ.IsPrimitive) : KS ψ = (localK p k : R') := by
  have : Fact p.Prime := ⟨hp⟩
  unfold localK
  simp only [hk.ne', ite_false]
  by_cases hp2 : p = 2
  · subst hp2
    simp only [ite_true]
    obtain hk1 | hk2 | hk3 | hk4 : k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k := by omega
    · subst hk1
      simp only [ite_true, Int.cast_one]
      revert ψ hψ
      generalize hc : (2 : ℕ) ^ 1 = c at *
      norm_num at hc; subst hc
      intro ψ _
      exact kloosterman_sum_two ψ
    · subst hk2
      simp only [show (2 : ℕ) ≠ 1 by norm_num, ite_false, ite_true, Int.cast_neg, Int.cast_ofNat]
      revert ψ hψ
      generalize hc : (2 : ℕ) ^ 2 = c at *
      norm_num at hc; subst hc
      intro ψ hψ
      exact kloosterman_sum_four ψ hψ
    · subst hk3
      simp only [show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num, ite_false,
        Int.cast_zero]
      revert ψ hψ
      generalize hc : (2 : ℕ) ^ 3 = c at *
      norm_num at hc; subst hc
      intro ψ hψ
      exact kloosterman_sum_eight ψ hψ
    · simp only [show k ≠ 1 by omega, show k ≠ 2 by omega, ite_false, Int.cast_zero]
      exact kloosterman_sum_two_pow k hk4 ψ hψ
  · simp only [hp2, ite_false]
    by_cases hk1 : k = 1
    · subst hk1
      simp only [ite_true]
      revert ψ hψ
      generalize hc : p ^ 1 = c at *
      rw [pow_one] at hc; subst hc
      intro ψ hψ
      unfold KS
      rw [kloosterman_sum_odd_prime p hp2 ψ hψ, quadraticChar_neg_one_eq_chi4 p hp2]
      push_cast
      ring
    · simp only [hk1, ite_false, Int.cast_zero]
      exact kloosterman_sum_odd_prime_pow p hp2 k (by omega) ψ hψ

/-- **Lemma 8(a), all moduli**: for every `c ≥ 1` and every primitive additive character `ψ`
mod `c`, `Σ_{a unit} S(a², 1; c) = Π_{p^k ∥ c} localK p k`. Equivalently `A₂ = KS/φ` is
multiplicative with the local values of the doc. -/
theorem KS_formula : ∀ (c : ℕ) [NeZero c] (ψ : AddChar (ZMod c) R'), ψ.IsPrimitive →
    KS ψ = ((c.factorization.prod fun p k => localK p k : ℤ) : R') := by
  intro c
  induction c using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ ψ hψ
    rw [Nat.Prime.factorization_pow hp, Finsupp.prod_single_index (by simp [localK])]
    exact KS_prime_pow p k hp hk ψ hψ
  | zero => intro h; exact absurd rfl h.out
  | one =>
    intro _ ψ _
    rw [KS_one, Nat.factorization_one, Finsupp.prod_zero_index, Int.cast_one]
  | coprime a b ha hb hab iha ihb =>
    intro _ ψ hψ
    have : NeZero a := ⟨by omega⟩
    have : NeZero b := ⟨by omega⟩
    obtain ⟨ψ₁, ψ₂, h1, h2, hKS⟩ := KS_mul a b hab ψ hψ
    rw [hKS, iha ψ₁ h1, ihb ψ₂ h2, Nat.factorization_mul_of_coprime hab,
      Finsupp.prod_add_index_of_disjoint hab.disjoint_primeFactors, Int.cast_mul]

end KSFormula


/-!
## The global identity (Lemma 8 ⇒ Theorem B input)

For `t ≠ 0`,
`Σ_{c ≥ 1} G(c) c_c(t) = Π_p E_p(t)`,
where `c_c(t) = Σ_{a ∈ (ℤ/c)ˣ} e(a t / c)` is the Ramanujan sum,
`G(c) = A₂(c) / (c² Π_{p | c} (1 − p⁻²))`, `A₂(c) = KS(c)/φ(c)` and `E_p(t)` is the Euler factor
of Lemma 6 (`hasSum_E_odd`, `hasSum_E_two`). The series converges absolutely.
-/

section Global

variable {R' : Type*} [CommRing R']

/-- The Ramanujan sum `Σ_{a unit} ψ(a t)` over a finite commutative ring. -/
def RS {R : Type*} [CommRing R] [Fintype Rˣ] (ψ : AddChar R R') (t : R) : R' :=
  ∑ a : Rˣ, ψ ((a : R) * t)

lemma RS_equiv {S T : Type*} [CommRing S] [CommRing T] [Fintype Sˣ] [Fintype Tˣ]
    (e : S ≃+* T) (ψ : AddChar S R') (t : S) :
    RS ψ t = RS (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (e t) := by
  unfold RS
  refine Fintype.sum_equiv (Units.mapEquiv e.toMulEquiv) _ _ (fun a => ?_)
  show ψ ((a : S) * t) = ψ (e.symm (e (a : S) * e t))
  rw [← map_mul, RingEquiv.symm_apply_apply]

lemma RS_prod {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] [Fintype R₁ˣ] [Fintype R₂ˣ]
    [Fintype (R₁ × R₂)ˣ] (ψ₁ : AddChar R₁ R') (ψ₂ : AddChar R₂ R') (t₁ : R₁) (t₂ : R₂) :
    RS (prodChar ψ₁ ψ₂) (t₁, t₂) = RS ψ₁ t₁ * RS ψ₂ t₂ := by
  calc RS (prodChar ψ₁ ψ₂) (t₁, t₂) =
        ∑ p : R₁ˣ × R₂ˣ, ψ₁ ((p.1 : R₁) * t₁) * ψ₂ ((p.2 : R₂) * t₂) := by
        unfold RS
        exact Fintype.sum_equiv (MulEquiv.prodUnits).toEquiv _ _ (fun u => rfl)
    _ = RS ψ₁ t₁ * RS ψ₂ t₂ := by
        unfold RS
        simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **Multiplicativity of Ramanujan sums** (CRT). -/
theorem RS_mul (m n : ℕ) [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) R') (hψ : ψ.IsPrimitive) (t : ℤ) :
    ∃ (ψ₁ : AddChar (ZMod m) R') (ψ₂ : AddChar (ZMod n) R'), ψ₁.IsPrimitive ∧ ψ₂.IsPrimitive ∧
      RS ψ (t : ZMod (m * n)) = RS ψ₁ (t : ZMod m) * RS ψ₂ (t : ZMod n) := by
  set e := ZMod.chineseRemainder h
  set ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hψ' : ψ'.IsPrimitive := isPrimitive_equiv e hψ
  refine ⟨ψ'.compAddMonoidHom (AddMonoidHom.inl _ _), ψ'.compAddMonoidHom (AddMonoidHom.inr _ _),
    isPrimitive_inl hψ', isPrimitive_inr hψ', ?_⟩
  have ht : ((t : ZMod m × ZMod n)) = ((t : ZMod m), (t : ZMod n)) := Prod.ext (by simp) (by simp)
  rw [RS_equiv e ψ, map_intCast, ht, ← RS_prod, ← eq_prodChar]

lemma RS_mulShift {R : Type*} [CommRing R] [Fintype Rˣ] (ψ : AddChar R R') (u : Rˣ) (t : R) :
    RS (ψ.mulShift u) t = RS ψ t := by
  unfold RS
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun a => ?_)
  simp only [AddChar.mulShift_apply, Equiv.coe_mulLeft, Units.val_mul, mul_assoc]

lemma addChar_zmod_natCast (c : ℕ) (ψ : AddChar (ZMod c) R') (n : ℕ) :
    ψ (n : ZMod c) = ψ 1 ^ n := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one]

/-- A primitive character of `ℤ/c` sends `1` to a primitive `c`-th root of unity. -/
lemma isPrimitiveRoot_of_isPrimitive [IsDomain R'] (c : ℕ) [NeZero c] (ψ : AddChar (ZMod c) R')
    (hψ : ψ.IsPrimitive) : IsPrimitiveRoot (ψ 1) c := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← addChar_zmod_natCast c ψ c, ZMod.natCast_self, AddChar.map_zero_eq_one]
  · rw [← addChar_zmod_natCast c ψ l] at hl
    by_contra hne
    apply hψ (a := (l : ZMod c)) (fun h => hne ((ZMod.natCast_eq_zero_iff _ _).mp h))
    ext x
    rw [AddChar.mulShift_apply, AddChar.one_apply, ← ZMod.natCast_zmod_val x, ← Nat.cast_mul,
      addChar_zmod_natCast c ψ, pow_mul, ← addChar_zmod_natCast c ψ l, hl, one_pow]

/-- Every primitive character of `ℤ/c` is `ψ(u ·)` for a fixed primitive `ψ` and a unit `u`. -/
lemma eq_mulShift_unit [IsDomain R'] (c : ℕ) [NeZero c] {ψ φ : AddChar (ZMod c) R'}
    (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) : ∃ u : (ZMod c)ˣ, φ = ψ.mulShift u := by
  have hζ := isPrimitiveRoot_of_isPrimitive c ψ hψ
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := φ 1)
    (by rw [← addChar_zmod_natCast c φ c, ZMod.natCast_self, AddChar.map_zero_eq_one])
  have hφi : φ = ψ.mulShift (i : ZMod c) := by
    ext x
    rw [AddChar.mulShift_apply, ← ZMod.natCast_zmod_val x, ← Nat.cast_mul,
      addChar_zmod_natCast c φ, addChar_zmod_natCast c ψ, ← hi, pow_mul]
  have hu : IsUnit (i : ZMod c) := by
    by_contra h
    apply AddChar.not_isPrimitive_mulShift ψ h
    rw [← hφi]; exact hφ
  exact ⟨hu.unit, by rw [hφi, IsUnit.unit_spec]⟩

/-- The Ramanujan sum does not depend on the primitive character. -/
lemma RS_indep [IsDomain R'] (c : ℕ) [NeZero c] {ψ φ : AddChar (ZMod c) R'}
    (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) (t : ZMod c) : RS φ t = RS ψ t := by
  obtain ⟨u, rfl⟩ := eq_mulShift_unit c hψ hφ
  exact RS_mulShift ψ u t

/-- Local factor of `G` at `p^k`: `localK p k / (φ(p^k) p^{2k} (1 − p⁻²))`. -/
noncomputable def localG (p k : ℕ) : ℝ :=
  if k = 0 then 1 else (localK p k : ℝ) /
    ((p : ℝ) ^ (k - 1) * ((p : ℝ) - 1) * (p : ℝ) ^ (2 * k) * (1 - 1 / (p : ℝ) ^ 2))

/-- `G(c) = A₂(c) / (c² Π_{p | c}(1 − p⁻²))`, as a product of local factors (see `Gc_eq`). -/
noncomputable def Gc (c : ℕ) : ℝ := c.factorization.prod localG

/-- The Ramanujan sum `c_c(t) = Σ_{a unit mod c} e(a t / c)` (and `0` for `c = 0`). -/
noncomputable def RSc (t : ℤ) (c : ℕ) : ℂ :=
  if h : c = 0 then 0 else haveI : NeZero c := ⟨h⟩; RS (ZMod.stdAddChar (N := c)) (t : ZMod c)

/-- The summand `G(c) c_c(t)`. -/
noncomputable def gc (t : ℤ) (c : ℕ) : ℂ := (Gc c : ℂ) * RSc t c

lemma RSc_eq (t : ℤ) (c : ℕ) [NeZero c] :
    RSc t c = RS (ZMod.stdAddChar (N := c)) (t : ZMod c) := by
  unfold RSc
  split_ifs with h
  · exact absurd h (NeZero.ne c)
  · rfl

lemma RSc_one (t : ℤ) : RSc t 1 = 1 := by
  rw [RSc_eq]
  unfold RS
  have hu : (univ : Finset (ZMod 1)ˣ) = {1} := by decide
  simp only [hu, Finset.sum_singleton]
  rw [Subsingleton.elim (((1 : (ZMod 1)ˣ) : ZMod 1) * (t : ZMod 1)) 0, AddChar.map_zero_eq_one]

lemma RSc_mul (t : ℤ) {m n : ℕ} (h : m.Coprime n) : RSc t (m * n) = RSc t m * RSc t n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp [RSc]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp [RSc]
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  obtain ⟨ψ₁, ψ₂, h1, h2, hRS⟩ :=
    RS_mul m n h (ZMod.stdAddChar (N := m * n)) (ZMod.isPrimitive_stdAddChar _) t
  rw [RSc_eq, RSc_eq, RSc_eq, hRS, RS_indep m (ZMod.isPrimitive_stdAddChar m) h1,
    RS_indep n (ZMod.isPrimitive_stdAddChar n) h2]

lemma Gc_one : Gc 1 = 1 := by
  simp [Gc]

lemma Gc_mul {m n : ℕ} (h : m.Coprime n) : Gc (m * n) = Gc m * Gc n := by
  unfold Gc
  rw [Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors]

lemma Gc_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : Gc (p ^ k) = localG p k := by
  unfold Gc
  rw [hp.factorization_pow, Finsupp.prod_single_index (by simp [localG])]

lemma Gc_prime {p : ℕ} (hp : p.Prime) : Gc p = localG p 1 := by
  simpa using Gc_prime_pow hp 1

lemma gc_zero (t : ℤ) : gc t 0 = 0 := by simp [gc, RSc]

lemma gc_one (t : ℤ) : gc t 1 = 1 := by simp [gc, Gc_one, RSc_one]

lemma gc_mul (t : ℤ) {m n : ℕ} (h : m.Coprime n) : gc t (m * n) = gc t m * gc t n := by
  unfold gc
  rw [Gc_mul h, RSc_mul t h]
  push_cast
  ring

/-- `G(p^k) = 0` for `k ≥ 3`, and for `k ≥ 2` when `p` is odd (Lemma 8(a)). -/
lemma gc_prime_pow_eq_zero (t : ℤ) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 3 ≤ k ∨ (p ≠ 2 ∧ 2 ≤ k)) :
    gc t (p ^ k) = 0 := by
  have hK : localK p k = 0 := by
    unfold localK
    rcases hk with hk | ⟨hp2, hk⟩
    · by_cases hp2 : p = 2
      · simp [hp2, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
      · simp [hp2, show k ≠ 0 by omega, show k ≠ 1 by omega]
    · simp [hp2, show k ≠ 0 by omega, show k ≠ 1 by omega]
  unfold gc
  simp [Gc_prime_pow hp, localG, show k ≠ 0 by omega, hK]

lemma tsum_gc (t : ℤ) {p : ℕ} (hp : p.Prime) :
    ∑' e, gc t (p ^ e) = 1 + gc t p + gc t (p ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun e he => gc_prime_pow_eq_zero t hp
    (Or.inl (by simp at he; omega)))]
  simp [Finset.sum_range_succ, gc_one]

/-- The Euler factor `E_p(t)` of Lemma 6. -/
noncomputable def Eloc (t : ℤ) (p : ℕ) : ℝ :=
  if p = 2 then E2 t else
    (1 + (((if (p : ℤ) ∣ t then 1 + chi4 p else ((p : ℚ) - 2 - chi4 p) / ((p : ℚ) - 1) : ℚ) : ℝ)
      - 1) / p) / (1 - 1 / (p : ℝ) ^ 2)

lemma Eloc_odd (t : ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Eloc t p = (1 + ((nuOdd p t : ℝ) - 1) / p) / (1 - 1 / (p : ℝ) ^ 2) := by
  simp only [Eloc, hp2, ite_false]
  rfl

lemma KS_std_prime (p : ℕ) [hp : Fact p.Prime] :
    KS (ZMod.stdAddChar (N := p)) = ((localK p 1 : ℤ) : ℂ) := by
  rw [KS_formula p _ (ZMod.isPrimitive_stdAddChar p), hp.out.factorization,
    Finsupp.prod_single_index (by simp [localK])]

/-- **Euler factor, odd `p`**: `Σ_e G(p^e) c_{p^e}(t) = E_p(t)`. -/
lemma tsum_gc_odd (t : ℤ) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∑' e, gc t (p ^ e) = (Eloc t p : ℂ) := by
  rw [tsum_gc t hp.out, gc_prime_pow_eq_zero t hp.out (Or.inr ⟨hp2, le_rfl⟩), add_zero,
    Eloc_odd t p hp2]
  have h := local_identity_odd p hp2 (ZMod.stdAddChar (N := p)) (ZMod.isPrimitive_stdAddChar p) t
  change _ = 1 + (KS (ZMod.stdAddChar (N := p)) / ((p : ℂ) - 1)) / ((p : ℂ) ^ 2 - 1) *
    RS (ZMod.stdAddChar (N := p)) (t : ZMod p) at h
  rw [h, KS_std_prime, gc, RSc_eq, Gc_prime hp.out]
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    have : (p : ℂ) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
    exact sub_ne_zero.mpr this
  have hpc2 : (p : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (p : ℂ) ^ 2 ≠ 1 := by
      have : (1 : ℕ) < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
      exact_mod_cast this.ne'
    exact sub_ne_zero.mpr this
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold localG
  simp only [one_ne_zero, ite_false]
  push_cast
  congr 2
  field_simp

/-- **Euler factor at 2**: `Σ_e G(2^e) c_{2^e}(t) = E_2(t)`. -/
lemma tsum_gc_two (t : ℤ) : ∑' e, gc t (2 ^ e) = (Eloc t 2 : ℂ) := by
  rw [tsum_gc t Nat.prime_two]
  have h := local_identity_two (ZMod.stdAddChar (N := 2)) (ZMod.isPrimitive_stdAddChar 2)
    (ZMod.stdAddChar (N := 4)) (ZMod.isPrimitive_stdAddChar 4) t
  rw [kloosterman_sum_two, kloosterman_sum_four _ (ZMod.isPrimitive_stdAddChar 4)] at h
  have hG4 : Gc 4 = localG 2 2 := by simpa using Gc_prime_pow Nat.prime_two 2
  simp only [Eloc, ite_true]
  rw [h]
  norm_num only [gc]
  rw [RSc_eq, RSc_eq, Gc_prime Nat.prime_two, hG4]
  unfold RS localG localK
  norm_num

/-- `|G(p)| ≤ 1/(p−1)²` and `|c_p(t)| ≤ |t|` give `|G(p) c_p(t)| ≤ |t|/(p−1)²` for odd `p`. -/
lemma norm_gc_prime_le (t : ℤ) (ht : t ≠ 0) (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ‖gc t p‖ ≤ |(t : ℝ)| / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp3 : (3 : ℝ) ≤ p := by
    have := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hc : chi4 p = 1 ∨ chi4 p = -1 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    unfold chi4
    have : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases this with h | h <;> simp [h]
  have hG : |localG p 1| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
    unfold localG localK
    simp only [one_ne_zero, ite_false, hp2, ite_true, Nat.sub_self, pow_zero, one_mul, mul_one]
    have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hq2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    have hden : ((p : ℝ) - 1) * (p : ℝ) ^ 2 * (1 - 1 / (p : ℝ) ^ 2) =
        ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 1) := by
      field_simp
    rw [hden]
    rcases hc with hc | hc <;> rw [hc] <;> push_cast
    · rw [abs_of_pos (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 1)),
        div_le_div_iff₀ (by positivity) (by positivity)]
      rw [abs_of_nonpos (by linarith)]
      nlinarith
  have hR : ‖RSc t p‖ ≤ |(t : ℝ)| := by
    rw [RSc_eq]
    unfold RS
    rw [ramanujan_prime p _ (ZMod.isPrimitive_stdAddChar p)]
    have ht1 : (1 : ℝ) ≤ |(t : ℝ)| := by
      have : (1 : ℤ) ≤ |t| := Int.one_le_abs ht
      exact_mod_cast this
    split_ifs with h
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      have hle : (p : ℤ) ≤ |t| := Int.le_of_dvd (abs_pos.mpr ht) ((dvd_abs _ _).mpr h)
      have hle' : (p : ℝ) ≤ |(t : ℝ)| := by exact_mod_cast hle
      rw [show (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      linarith
    · simpa using ht1
  calc ‖gc t p‖ = |localG p 1| * ‖RSc t p‖ := by
        rw [gc, Gc_prime hp.out, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 / ((p : ℝ) - 1) ^ 2 * |(t : ℝ)| :=
        mul_le_mul hG hR (norm_nonneg _) (by positivity)
    _ = |(t : ℝ)| / ((p : ℝ) - 1) ^ 2 := by ring

/-- **Absolute convergence** of `Σ_c G(c) c_c(t)` for `t ≠ 0`. -/
theorem summable_gc (t : ℤ) (ht : t ≠ 0) : Summable (fun c => ‖gc t c‖) := by
  set F : ℕ → ℝ := fun c => ‖gc t c‖ with hFdef
  have hF0 : 0 ≤ F := fun c => norm_nonneg _
  have hF1 : F 1 = 1 := by simp [hFdef, gc_one]
  have hFmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := fun h => by
    simp only [hFdef, gc_mul t h, norm_mul]
  have hFp : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖F (p ^ e)‖) := fun hp =>
    summable_of_ne_finset_zero (s := Finset.range 3) (fun e he => by
      simp only [hFdef, gc_prime_pow_eq_zero t hp (Or.inl (by simp at he; omega)), norm_zero])
  -- the comparison series `Σ 1/(n+1)²`
  set h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2 with hhdef
  have hh : Summable h := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [hhdef] using this
  have hh0 : ∀ n, 0 ≤ h n := fun n => by positivity
  set A : ℝ := F 2 + F 4 + |(t : ℝ)| * ∑' n, h n
  -- local bound: the Euler factor of `F` at `p` is `1 + a p`
  set a : ℕ → ℝ := fun p => F p + F (p ^ 2) with hadef
  have ha0 : ∀ p, 0 ≤ a p := fun p => add_nonneg (hF0 _) (hF0 _)
  have hEul : ∀ {p : ℕ}, p.Prime → ∑' e, F (p ^ e) = 1 + a p := fun {p} hp => by
    rw [tsum_eq_sum (s := Finset.range 3) (fun e he => by
      simp only [hFdef, gc_prime_pow_eq_zero t hp (Or.inl (by simp at he; omega)), norm_zero])]
    simp [Finset.sum_range_succ, hF1, hadef]
    ring
  have hab : ∀ {p : ℕ}, p.Prime →
      a p ≤ (if p = 2 then F 2 + F 4 else 0) + |(t : ℝ)| * h (p - 2) := fun {p} hp => by
    by_cases hp2 : p = 2
    · subst hp2
      simp only [hadef, ite_true]
      norm_num
    · have : Fact p.Prime := ⟨hp⟩
      simp only [hadef, hp2, ite_false, zero_add]
      rw [show F (p ^ 2) = 0 by simp [hFdef, gc_prime_pow_eq_zero t hp (Or.inr ⟨hp2, le_rfl⟩)],
        add_zero]
      have h2 : 2 ≤ p := hp.two_le
      have hcast : ((p - 2 : ℕ) : ℝ) + 1 = (p : ℝ) - 1 := by
        rw [Nat.cast_sub h2]; push_cast; ring
      simp only [hhdef, hcast]
      have := norm_gc_prime_le t ht p hp2
      calc F p ≤ |(t : ℝ)| / ((p : ℝ) - 1) ^ 2 := this
        _ = |(t : ℝ)| * (1 / ((p : ℝ) - 1) ^ 2) := by ring
  -- bound for the products over primes below `N`
  have hprod : ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e, F (p ^ e) ≤ Real.exp A := fun N => by
    calc ∏ p ∈ N.primesBelow, ∑' e, F (p ^ e) = ∏ p ∈ N.primesBelow, (1 + a p) :=
          Finset.prod_congr rfl (fun p hp => hEul (Nat.prime_of_mem_primesBelow hp))
      _ ≤ ∏ p ∈ N.primesBelow, Real.exp (a p) :=
          Finset.prod_le_prod₀ (fun p _ => by linarith [ha0 p])
            (fun p _ => by linarith [Real.add_one_le_exp (a p)])
      _ = Real.exp (∑ p ∈ N.primesBelow, a p) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp A := by
          apply Real.exp_le_exp.mpr
          calc ∑ p ∈ N.primesBelow, a p ≤ ∑ p ∈ N.primesBelow,
                ((if p = 2 then F 2 + F 4 else 0) + |(t : ℝ)| * h (p - 2)) :=
                Finset.sum_le_sum (fun p hp => hab (Nat.prime_of_mem_primesBelow hp))
            _ = (∑ p ∈ N.primesBelow, if p = 2 then F 2 + F 4 else 0) +
                |(t : ℝ)| * ∑ p ∈ N.primesBelow, h (p - 2) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
            _ ≤ (F 2 + F 4) + |(t : ℝ)| * ∑' n, h n := by
                gcongr
                · rw [Finset.sum_ite_eq']
                  split_ifs
                  · exact le_rfl
                  · exact add_nonneg (hF0 _) (hF0 _)
                · rw [← Finset.sum_image (g := fun p => p - 2) (f := h) (fun x hx y hy hxy => by
                    have := (Nat.prime_of_mem_primesBelow hx).two_le
                    have := (Nat.prime_of_mem_primesBelow hy).two_le
                    simp only at hxy
                    omega)]
                  exact hh.sum_le_tsum _ (fun n _ => hh0 n)
  refine summable_of_sum_le hF0 (c := Real.exp A) (fun u => ?_)
  set N := u.sup id + 1
  obtain ⟨-, hsum⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hF1 hFmul hFp N
  have hmem : ∀ c ∈ u, F c ≠ 0 → c ∈ N.smoothNumbers := fun c hc hFc => by
    have hc0 : c ≠ 0 := by rintro rfl; exact hFc (by simp [hFdef, gc_zero])
    refine Nat.mem_smoothNumbers.mpr ⟨hc0, fun p hp => ?_⟩
    have h1 := Nat.le_of_mem_primeFactorsList hp
    have h2 : c ≤ u.sup id := Finset.le_sup (f := id) hc
    omega
  calc ∑ c ∈ u, F c = ∑ c ∈ u with c ∈ N.smoothNumbers, F c := (Finset.sum_filter_of_ne hmem).symm
    _ = ∑ c ∈ u.subtype (· ∈ N.smoothNumbers), F c := (Finset.sum_subtype_eq_sum_filter _).symm
    _ ≤ ∏ p ∈ N.primesBelow, ∑' e, F (p ^ e) :=
        sum_le_hasSum _ (fun _ _ => hF0 _) hsum
    _ ≤ Real.exp A := hprod N

/-- The Euler factor as a function of a prime. -/
lemma tsum_gc_prime (t : ℤ) (p : Nat.Primes) : ∑' e, gc t ((p : ℕ) ^ e) = (Eloc t p : ℂ) := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2]; exact tsum_gc_two t
  · exact tsum_gc_odd t p hp2

/-- **The global identity.** For `t ≠ 0`, `Σ_c G(c) c_c(t)` converges absolutely and equals the
Euler product `Π_p E_p(t)` of Lemma 6. -/
theorem global_identity (t : ℤ) (ht : t ≠ 0) :
    Summable (fun c => ‖gc t c‖) ∧
      HasProd (fun p : Nat.Primes => (Eloc t p : ℂ)) (∑' c, gc t c) := by
  refine ⟨summable_gc t ht, ?_⟩
  have h := EulerProduct.eulerProduct_hasProd (f := gc t) (gc_one t) (fun h => gc_mul t h)
    (summable_gc t ht) (gc_zero t)
  simpa only [tsum_gc_prime] using h

/-- `G(c)` is the doc's `A₂(c)/(c² Π_{p | c}(1 − p⁻²))`, with `A₂(c) = KS(c)/φ(c)`. -/
theorem Gc_eq (c : ℕ) [NeZero c] :
    (Gc c : ℂ) = KS (ZMod.stdAddChar (N := c)) /
      ((Nat.totient c : ℂ) * (c : ℂ) ^ 2 * ∏ p ∈ c.primeFactors, (1 - 1 / (p : ℂ) ^ 2)) := by
  have hc := NeZero.ne c
  rw [KS_formula c _ (ZMod.isPrimitive_stdAddChar c), Nat.totient_eq_prod_factorization hc]
  have hcC : (c : ℂ) = ∏ p ∈ c.primeFactors, (p : ℂ) ^ c.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hc]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    rfl
  rw [hcC]
  unfold Gc Finsupp.prod
  rw [Nat.support_factorization]
  push_cast
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hk : c.factorization p ≠ 0 := (Nat.Prime.factorization_pos_of_dvd hpp hc
    (Nat.dvd_of_mem_primeFactors hp)).ne'
  unfold localG
  simp only [hk, ite_false]
  push_cast [Nat.cast_sub hpp.one_le]
  congr 1
  ring

end Global


/-!
## The Poisson step (Theorem B)

For a Schwartz function `f` and a modulus `c ≥ 1`,
`Σ_{m ∈ ℤ, (m, c) = 1} f(m/c) = Σ_{t ∈ ℤ} 𝓕f(t) c_c(t)`,
where `c_c(t)` is the Ramanujan sum `RSc t c`. In the doc `f = ψ`, `ψ(x) = Φ(x⁻²) x⁻²`.
-/

section Poisson

open scoped SchwartzMap FourierTransform

/-- `ℤ/c × ℤ ≃ ℤ`, `(r, n) ↦ r + c n` with `0 ≤ r < c`. -/
def resEquiv (c : ℕ) [NeZero c] : ZMod c × ℤ ≃ ℤ where
  toFun p := (p.1.val : ℤ) + c * p.2
  invFun m := ((m : ZMod c), m / c)
  left_inv p := by
    obtain ⟨r, n⟩ := p
    have hc : (0 : ℤ) < c := by exact_mod_cast NeZero.pos c
    have hr : (r.val : ℤ) < c := by exact_mod_cast r.val_lt
    ext
    · push_cast; simp
    · simp only
      rw [Int.add_mul_ediv_left _ _ hc.ne', Int.ediv_eq_zero_of_lt (by positivity) hr, zero_add]
  right_inv m := by
    simp only
    rw [ZMod.val_intCast]
    linarith [Int.emod_add_ediv_mul m (c : ℤ)]

/-- Scaling by `1/c` as a continuous linear equivalence of `ℝ`. -/
noncomputable def scaleCLE (c : ℕ) [NeZero c] : ℝ ≃L[ℝ] ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ ((c : ℝ)⁻¹)
    (inv_ne_zero (by exact_mod_cast NeZero.ne c))).toContinuousLinearEquiv

lemma summable_norm_int (g : 𝓢(ℝ, ℂ)) : Summable (fun m : ℤ => ‖g m‖) := by
  have h := (g.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite
  refine summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) ?_
  simpa [Function.comp_def, Real.norm_eq_abs] using h

lemma summable_norm_div (f : 𝓢(ℝ, ℂ)) (c : ℕ) [NeZero c] :
    Summable (fun m : ℤ => ‖f ((m : ℝ) / c)‖) := by
  have := summable_norm_int (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleCLE c) f)
  simpa [scaleCLE, div_eq_inv_mul] using this

lemma isUnit_intCast_iff (c : ℕ) (m : ℤ) : IsUnit (m : ZMod c) ↔ Nat.Coprime m.natAbs c := by
  rcases Int.natAbs_eq m with h | h
  · rw [h]; simp only [Int.cast_natCast, Int.natAbs_natCast]
    exact ZMod.isUnit_iff_coprime _ _
  · rw [h]; simp only [Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff, Int.natAbs_neg,
      Int.natAbs_natCast]
    exact ZMod.isUnit_iff_coprime _ _

lemma sum_isUnit {R : Type*} [CommRing R] [Fintype R] [Fintype Rˣ]
    [DecidablePred (IsUnit : R → Prop)] (F : R → ℂ) :
    ∑ r, (if IsUnit r then F r else 0) = ∑ a : Rˣ, F a := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => (a : R)) (fun a _ => by simp) (fun a _ b _ h => Units.ext h)
    (fun r hr => ⟨(Finset.mem_filter.mp hr).2.unit, Finset.mem_univ _, by simp⟩) (fun a _ => rfl)

lemma fourier_eq_std (c : ℕ) [NeZero c] (a : (ZMod c)ˣ) (t : ℤ) :
    fourier t ((((a : ZMod c).val : ℝ) / c : ℝ) : UnitAddCircle) =
      ZMod.stdAddChar ((a : ZMod c) * (t : ZMod c)) := by
  have h : (a : ZMod c) * (t : ZMod c) = ((((a : ZMod c).val : ℤ) * t : ℤ) : ZMod c) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.stdAddChar_coe, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **Poisson summation over reduced residues.** For a Schwartz function `f` and `c ≥ 1`,
`Σ_{(m, c) = 1} f(m/c) = Σ_t 𝓕f(t) c_c(t)`. -/
theorem poisson_coprime (f : 𝓢(ℝ, ℂ)) (c : ℕ) [NeZero c] :
    ∑' m : ℤ, (if Nat.Coprime m.natAbs c then f ((m : ℝ) / c) else 0) =
      ∑' t : ℤ, 𝓕 f t * RSc t c := by
  classical
  set G : ℤ → ℂ := fun m => if Nat.Coprime m.natAbs c then f ((m : ℝ) / c) else 0 with hGdef
  have hG : Summable G := by
    refine Summable.of_norm_bounded (summable_norm_div f c) (fun m => ?_)
    simp only [hGdef]; split_ifs <;> simp
  have hc : (c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have he : ∀ p : ZMod c × ℤ, G (resEquiv c p) =
      if IsUnit p.1 then f (((p.1.val : ℝ) / c) + p.2) else 0 := by
    rintro ⟨r, n⟩
    have h1 : (((r.val : ℤ) + c * n : ℤ) : ZMod c) = r := by push_cast; simp
    simp only [hGdef, resEquiv, Equiv.coe_fn_mk, ← isUnit_intCast_iff, h1]
    split_ifs
    · congr 1
      push_cast
      field_simp
    · rfl
  show ∑' m : ℤ, G m = _
  rw [← (resEquiv c).tsum_eq, Summable.tsum_prod (f := fun p => G (resEquiv c p))
    ((resEquiv c).summable_iff.mpr hG)]
  simp_rw [he]
  rw [tsum_fintype]
  have hite : ∀ r : ZMod c, (∑' n : ℤ, if IsUnit r then f (((r.val : ℝ) / c) + n) else 0) =
      if IsUnit r then ∑' n : ℤ, f (((r.val : ℝ) / c) + n) else 0 := by
    intro r; split_ifs <;> simp
  simp_rw [hite]
  rw [sum_isUnit (fun r : ZMod c => ∑' n : ℤ, f (((r.val : ℝ) / c) + n))]
  simp_rw [SchwartzMap.tsum_eq_tsum_fourier f, fourier_eq_std]
  have hsum : Summable (fun t : ℤ => ‖𝓕 f t‖) := summable_norm_int (𝓕 f)
  rw [← Summable.tsum_finsetSum (fun a _ => ?_)]
  · congr 1
    funext t
    rw [RSc_eq, RS, Finset.mul_sum]
  · refine Summable.of_norm_bounded hsum (fun t => ?_)
    rw [norm_mul]
    have : ‖ZMod.stdAddChar ((a : ZMod c) * (t : ZMod c))‖ = 1 := by
      rw [ZMod.stdAddChar_apply]; simp
    rw [this, mul_one]

end Poisson

/-!
### Bounds for multiplicative functions

A finite sum of a nonnegative multiplicative `F` is bounded by a product of local factors.
-/

section MultBound

lemma sum_le_of_multiplicative {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n) (hFz : F 0 = 0) (hF1 : F 1 = 1)
    (hFmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n)
    (hfin : ∀ {p : ℕ}, p.Prime → ∀ e, 4 ≤ e → F (p ^ e) = 0) {B : ℝ}
    (hB : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∏ p ∈ S, ∑ e ∈ Finset.range 4, F (p ^ e) ≤ B)
    (u : Finset ℕ) : ∑ c ∈ u, F c ≤ B := by
  have hFp : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖F (p ^ e)‖) := fun hp =>
    summable_of_ne_finset_zero (s := Finset.range 4) (fun e he => by
      rw [hfin hp e (by simp at he; omega), norm_zero])
  set N := u.sup id + 1
  obtain ⟨-, hsum⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hF1 hFmul hFp N
  have hmem : ∀ c ∈ u, F c ≠ 0 → c ∈ N.smoothNumbers := fun c hc hFc => by
    have hc0 : c ≠ 0 := by rintro rfl; exact hFc hFz
    refine Nat.mem_smoothNumbers.mpr ⟨hc0, fun p hp => ?_⟩
    have h1 := Nat.le_of_mem_primeFactorsList hp
    have h2 : c ≤ u.sup id := Finset.le_sup (f := id) hc
    omega
  have hfac : ∀ p ∈ N.primesBelow, ∑' e, F (p ^ e) = ∑ e ∈ Finset.range 4, F (p ^ e) :=
    fun p hp => tsum_eq_sum (fun e he =>
      hfin (Nat.prime_of_mem_primesBelow hp) e (by simp at he; omega))
  calc ∑ c ∈ u, F c = ∑ c ∈ u with c ∈ N.smoothNumbers, F c :=
        (Finset.sum_filter_of_ne hmem).symm
    _ = ∑ c ∈ u.subtype (· ∈ N.smoothNumbers), F c := (Finset.sum_subtype_eq_sum_filter _).symm
    _ ≤ ∏ p ∈ N.primesBelow, ∑' e, F (p ^ e) := sum_le_hasSum _ (fun _ _ => hF0 _) hsum
    _ = ∏ p ∈ N.primesBelow, ∑ e ∈ Finset.range 4, F (p ^ e) := Finset.prod_congr rfl hfac
    _ ≤ B := hB _ (fun p hp => Nat.prime_of_mem_primesBelow hp)

/-- The comparison constant `Σ_{n ≥ 0} 1/(n+1)²`. -/
noncomputable def Cser : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

lemma summable_Cser : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

lemma sum_primes_le_Cser {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, 1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2 ≤ Cser := by
  rw [← Finset.sum_image (g := fun p => p - 2) (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2)
    (fun x hx y hy hxy => by
      have := (hS x hx).two_le
      have := (hS y hy).two_le
      simp only at hxy
      omega)]
  exact summable_Cser.sum_le_tsum _ (fun n _ => by positivity)

/-- Product bound: if `x p ≤ (if p = 2 then x₂ else 1) · d p · (1 + K/(p−1)²)` on a set of
primes, then `Π x ≤ x₂ · Π d · exp(K · Cser)`. -/
lemma prod_le_of_local {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (x d : ℕ → ℝ) {x₂ K : ℝ}
    (hx₂ : 1 ≤ x₂) (hK : 0 ≤ K) (hx0 : ∀ p ∈ S, 0 ≤ x p) (hd : ∀ p ∈ S, 0 ≤ d p)
    (hx : ∀ p ∈ S, x p ≤ (if p = 2 then x₂ else 1) * d p *
      (1 + K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2))) :
    ∏ p ∈ S, x p ≤ x₂ * (∏ p ∈ S, d p) * Real.exp (K * Cser) := by
  have hh0 : ∀ p : ℕ, 0 ≤ 1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2 := fun p => by positivity
  calc ∏ p ∈ S, x p ≤ ∏ p ∈ S, ((if p = 2 then x₂ else 1) * d p *
        (1 + K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2))) := Finset.prod_le_prod₀ hx0 hx
    _ = (∏ p ∈ S, (if p = 2 then x₂ else 1)) * (∏ p ∈ S, d p) *
        ∏ p ∈ S, (1 + K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ x₂ * (∏ p ∈ S, d p) * Real.exp (K * Cser) := by
        have h1 : ∏ p ∈ S, (if p = 2 then x₂ else 1) ≤ x₂ := by
          rw [Finset.prod_ite_eq']
          split_ifs
          · exact le_rfl
          · exact hx₂
        have h2 : ∏ p ∈ S, (1 + K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2)) ≤ Real.exp (K * Cser) := by
          calc ∏ p ∈ S, (1 + K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2))
              ≤ ∏ p ∈ S, Real.exp (K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2)) :=
                Finset.prod_le_prod₀ (fun p _ => by have := hh0 p; positivity)
                  (fun p _ => by
                    linarith [Real.add_one_le_exp (K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2))])
            _ = Real.exp (K * ∑ p ∈ S, 1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2) := by
                rw [Finset.mul_sum, Real.exp_sum]
            _ ≤ Real.exp (K * Cser) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sum_primes_le_Cser hS) hK)
        have hd0 : 0 ≤ ∏ p ∈ S, d p := Finset.prod_nonneg hd
        have h10 : 0 ≤ ∏ p ∈ S, (if p = 2 then x₂ else 1) :=
          Finset.prod_nonneg (fun p _ => by split_ifs <;> linarith)
        have h20 : 0 ≤ ∏ p ∈ S, (1 + K * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2)) :=
          Finset.prod_nonneg (fun p _ => by have := hh0 p; positivity)
        gcongr

end MultBound

/-!
### A polynomial bound for `Σ_c |G(c) c_c(t)|`
-/

section GcBound

/-- `|G(p)| ≤ 1/(p−1)²` for odd `p`. -/
lemma abs_localG_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    |localG p 1| ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp3 : (3 : ℝ) ≤ p := by
    have := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hc : chi4 p = 1 ∨ chi4 p = -1 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    unfold chi4
    have : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases this with h | h <;> simp [h]
  unfold localG localK
  simp only [one_ne_zero, ite_false, hp2, ite_true, Nat.sub_self, pow_zero, one_mul, mul_one]
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hden : ((p : ℝ) - 1) * (p : ℝ) ^ 2 * (1 - 1 / (p : ℝ) ^ 2) =
      ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 1) := by
    field_simp
  rw [hden]
  rcases hc with hc | hc <;> rw [hc] <;> push_cast
  · rw [abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 1)),
      div_le_div_iff₀ (by positivity) (by positivity)]
    rw [abs_of_nonpos (by linarith)]
    nlinarith

lemma norm_RS_prime (t : ℤ) (p : ℕ) [hp : Fact p.Prime] :
    ‖RSc t p‖ = if (p : ℤ) ∣ t then (p : ℝ) - 1 else 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [RSc_eq]
  unfold RS
  rw [ramanujan_prime p _ (ZMod.isPrimitive_stdAddChar p)]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs
  · rw [show (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  · simp

/-- At `p = 2`: `|G(2) c_2(t)| + |G(4) c_4(t)| ≤ 1`. -/
lemma norm_gc_two_four (t : ℤ) : ‖gc t 2‖ + ‖gc t 4‖ ≤ 1 := by
  have hG4 : Gc 4 = localG 2 2 := by simpa using Gc_prime_pow Nat.prime_two 2
  have h2 : ‖RSc t 2‖ ≤ 1 := by
    rw [RSc_eq]; unfold RS
    rw [ramanujan_two _ (ZMod.isPrimitive_stdAddChar 2)]
    split_ifs <;> simp
  have h4 : ‖RSc t 4‖ ≤ 2 := by
    rw [RSc_eq]; unfold RS
    rw [ramanujan_four _ (ZMod.isPrimitive_stdAddChar 4)]
    split_ifs <;> simp
  have hl2 : localG 2 1 = 1 / 3 := by norm_num [localG, localK]
  have hl4 : localG 2 2 = -1 / 6 := by norm_num [localG, localK]
  unfold gc
  rw [Gc_prime Nat.prime_two, hG4, hl2, hl4, norm_mul, norm_mul]
  have e1 : ‖(((1 / 3 : ℝ)) : ℂ)‖ = 1 / 3 := by rw [Complex.norm_real]; norm_num
  have e2 : ‖(((-1 / 6 : ℝ)) : ℂ)‖ = 1 / 6 := by rw [Complex.norm_real]; norm_num
  rw [e1, e2]
  linarith

/-- **Polynomial bound**: `Σ_{c ∈ u} |G(c) c_c(t)| ≤ 2 |t| e^{Cser}` for `t ≠ 0`. -/
theorem sum_norm_gc_le (t : ℤ) (ht : t ≠ 0) (u : Finset ℕ) :
    ∑ c ∈ u, ‖gc t c‖ ≤ 2 * (t.natAbs : ℝ) * Real.exp (1 * Cser) := by
  refine sum_le_of_multiplicative (F := fun c => ‖gc t c‖) (fun _ => norm_nonneg _)
    (by simp [gc_zero]) (by simp [gc_one]) (fun h => by simp only [gc_mul t h, norm_mul])
    (fun {p} hp e he => by
      show ‖gc t (p ^ e)‖ = 0
      rw [gc_prime_pow_eq_zero t hp (k := e) (Or.inl (by omega)), norm_zero]) (fun S hS => ?_) u
  have hloc : ∀ p ∈ S, ∑ e ∈ Finset.range 4, ‖gc t (p ^ e)‖ = 1 + ‖gc t p‖ + ‖gc t (p ^ 2)‖ :=
    fun p hp => by
      simp [Finset.sum_range_succ, gc_one, gc_prime_pow_eq_zero t (hS p hp) (Or.inl le_rfl)]
  rw [Finset.prod_congr rfl hloc]
  set d : ℕ → ℝ := fun p => if p ∣ t.natAbs then (p : ℝ) else 1 with hddef
  have hdprod : ∏ p ∈ S, d p ≤ (t.natAbs : ℝ) := by
    have : ∏ p ∈ S, d p = ((∏ p ∈ S with p ∣ t.natAbs, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, Finset.prod_filter]
    rw [this]
    have hdvd : ∏ p ∈ S with p ∣ t.natAbs, p ∣ t.natAbs :=
      Finset.prod_primes_dvd _ (fun p hp => (hS p (Finset.mem_filter.mp hp).1).prime)
        (fun p hp => (Finset.mem_filter.mp hp).2)
    exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr ht) hdvd
  have hb := prod_le_of_local hS (fun p => 1 + ‖gc t p‖ + ‖gc t (p ^ 2)‖) d (x₂ := 2) (K := 1)
    (by norm_num) (by norm_num) (fun p _ => by positivity)
    (fun p _ => by simp only [hddef]; split_ifs <;> positivity) (fun p hp => ?_)
  · calc ∏ p ∈ S, (1 + ‖gc t p‖ + ‖gc t (p ^ 2)‖) ≤ 2 * (∏ p ∈ S, d p) * Real.exp (1 * Cser) := hb
      _ ≤ 2 * (t.natAbs : ℝ) * Real.exp (1 * Cser) := by gcongr
  · have hpp := hS p hp
    have hh0 : 0 ≤ 1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2 := by positivity
    have hd1 : 1 ≤ d p := by
      simp only [hddef]; split_ifs
      · exact_mod_cast hpp.one_lt.le
      · exact le_rfl
    by_cases hp2 : p = 2
    · subst hp2
      simp only [ite_true]
      have := norm_gc_two_four t
      norm_num at this ⊢
      nlinarith
    · have : Fact p.Prime := ⟨hpp⟩
      simp only [hp2, ite_false, one_mul]
      rw [gc_prime_pow_eq_zero t hpp (Or.inr ⟨hp2, le_rfl⟩), norm_zero, add_zero]
      have h2 : 2 ≤ p := hpp.two_le
      have hp3 : (3 : ℝ) ≤ p := by
        have : 3 ≤ p := by omega
        exact_mod_cast this
      have hcast : ((p - 2 : ℕ) : ℝ) + 1 = (p : ℝ) - 1 := by
        rw [Nat.cast_sub h2]; push_cast; ring
      rw [hcast]
      have hG := abs_localG_le p hp2
      have hgc : ‖gc t p‖ = |localG p 1| * ‖RSc t p‖ := by
        rw [gc, Gc_prime hpp, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hgc, norm_RS_prime]
      have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      by_cases hdvd : (p : ℤ) ∣ t
      · -- `p ∣ t`: the factor is at most `p`
        have hdp : d p = p := by
          simp only [hddef, Int.natCast_dvd.mp hdvd, ite_true]
        simp only [hdvd, ite_true]
        rw [hdp]
        have : |localG p 1| * ((p : ℝ) - 1) ≤ 1 / ((p : ℝ) - 1) := by
          calc |localG p 1| * ((p : ℝ) - 1) ≤ 1 / ((p : ℝ) - 1) ^ 2 * ((p : ℝ) - 1) :=
                mul_le_mul_of_nonneg_right hG hq.le
            _ = 1 / ((p : ℝ) - 1) := by field_simp
        have h1 : 1 / ((p : ℝ) - 1) ≤ 1 := by
          rw [div_le_one hq]; linarith
        have h3 : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
        nlinarith
      · have hdp : d p = 1 := by
          have : ¬ p ∣ t.natAbs := fun h => hdvd (Int.natCast_dvd.mpr h)
          simp only [hddef, this, ite_false]
        simp only [hdvd, ite_false]
        rw [hdp, one_mul, mul_one]
        linarith

end GcBound

/-!
### The term `t = 0`: `Σ_{c ≤ C} G(c) φ(c) → π/4`

`G·φ = (χ(n)/n) ∗ h` with `h` multiplicative, absolutely summable and `Σ h = 1` (all Euler
factors equal `1`, Lemma 8 at `v = ∞`); the partial sums of `χ(n)/n` converge to `L(1, χ) = π/4`
(Leibniz).
-/

section TermZero

open ArithmeticFunction

lemma chi4_mul (m n : ℕ) : chi4 (m * n) = chi4 m * chi4 n := by
  unfold chi4
  have hm := Nat.mod_lt m (show 4 > 0 by norm_num)
  have hn := Nat.mod_lt n (show 4 > 0 by norm_num)
  rw [Nat.mul_mod]
  interval_cases h1 : m % 4 <;> interval_cases h2 : n % 4 <;> simp

/-- `χ(n)/n` as an arithmetic function. -/
noncomputable def chiA : ArithmeticFunction ℝ := ⟨fun n => (chi4 n : ℝ) / n, by simp⟩

lemma chiA_apply (n : ℕ) : chiA n = (chi4 n : ℝ) / n := rfl

lemma chiA_mul (m n : ℕ) : chiA (m * n) = chiA m * chiA n := by
  rw [chiA_apply, chiA_apply, chiA_apply, chi4_mul]
  push_cast
  rw [div_mul_div_comm]

lemma chiA_one : chiA 1 = 1 := by
  rw [chiA_apply]; norm_num [chi4]

lemma isMultiplicative_chiA : chiA.IsMultiplicative := ⟨chiA_one, fun _ => chiA_mul _ _⟩

/-- `μ(n)χ(n)/n`, the Dirichlet inverse of `chiA`. -/
noncomputable def chiInv : ArithmeticFunction ℝ :=
  (moebius : ArithmeticFunction ℝ).pmul chiA

lemma chiInv_apply (n : ℕ) : chiInv n = ((moebius n : ℤ) : ℝ) * chiA n := by
  rw [chiInv, pmul_apply, intCoe_apply]

lemma chiA_mul_chiInv : chiA * chiInv = 1 := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  have h1 : ∀ x ∈ n.divisorsAntidiagonal, chiA x.1 * chiInv x.2 =
      chiA n * ((zeta : ArithmeticFunction ℤ) x.1 * moebius x.2 : ℤ) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hx1 : x.1 ≠ 0 := by
      rintro h; rw [h, zero_mul] at hx; exact hx.2 hx.1.symm
    rw [chiInv_apply, ← hx.1, chiA_mul, natCoe_apply, zeta_apply]
    simp only [hx1, ite_false]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h2 : ∑ x ∈ n.divisorsAntidiagonal, (((zeta : ArithmeticFunction ℤ) x.1 * moebius x.2 : ℤ) : ℝ)
      = (((zeta : ArithmeticFunction ℤ) * moebius) n : ℝ) := by
    rw [ArithmeticFunction.mul_apply]; push_cast; rfl
  rw [h2, coe_zeta_mul_moebius, ArithmeticFunction.one_apply, ArithmeticFunction.one_apply]
  split_ifs with h
  · subst h; rw [chiA_one]; norm_num
  · simp

/-- `w(n) = G(n) φ(n)`. -/
noncomputable def wA : ArithmeticFunction ℝ := ⟨fun n => Gc n * (Nat.totient n : ℝ), by simp⟩

lemma wA_apply (n : ℕ) : wA n = Gc n * (Nat.totient n : ℝ) := rfl

lemma isMultiplicative_wA : wA.IsMultiplicative := by
  refine ⟨by simp [wA_apply, Gc_one], fun {m n} h => ?_⟩
  rw [wA_apply, wA_apply, wA_apply, Gc_mul h, Nat.totient_mul h]
  push_cast
  ring

/-- `h = (μχ/n) ∗ w`, so that `w = (χ/n) ∗ h`. -/
noncomputable def hA : ArithmeticFunction ℝ := chiInv * wA

lemma isMultiplicative_chiInv : chiInv.IsMultiplicative :=
  isMultiplicative_moebius.intCast.pmul isMultiplicative_chiA

lemma isMultiplicative_hA : hA.IsMultiplicative :=
  isMultiplicative_chiInv.mul isMultiplicative_wA

lemma wA_eq : wA = hA * chiA := by
  rw [hA, mul_comm chiInv wA, mul_assoc, mul_comm chiInv chiA, chiA_mul_chiInv, mul_one]

lemma conv_prime_pow (f g : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simp at hi; omega) hp.pos]

lemma localG_eq_zero {p k : ℕ} (hk : 3 ≤ k ∨ (p ≠ 2 ∧ 2 ≤ k)) : localG p k = 0 := by
  have hK : localK p k = 0 := by
    unfold localK
    rcases hk with hk | ⟨hp2, hk⟩
    · by_cases hp2 : p = 2
      · simp [hp2, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
      · simp [hp2, show k ≠ 0 by omega, show k ≠ 1 by omega]
    · simp [hp2, show k ≠ 0 by omega, show k ≠ 1 by omega]
  simp [localG, show k ≠ 0 by omega, hK]

lemma wA_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    wA (p ^ k) = localG p k * (Nat.totient (p ^ k) : ℝ) := by
  rw [wA_apply, Gc_prime_pow hp]

lemma chiInv_prime_pow_zero {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 2 ≤ i) : chiInv (p ^ i) = 0 := by
  rw [chiInv_apply, moebius_apply_prime_pow hp (by omega)]
  simp [show i ≠ 1 by omega]

lemma hA_prime_pow_zero {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 4 ≤ e) : hA (p ^ e) = 0 := by
  rw [hA, conv_prime_pow _ _ hp]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  by_cases h : 2 ≤ i
  · rw [chiInv_prime_pow_zero hp h, zero_mul]
  · rw [wA_prime_pow hp, localG_eq_zero (Or.inl (by simp at hi; omega)), zero_mul, mul_zero]

/-- Values of the local factors of `h`. -/
lemma hA_local (p : ℕ) (hp : p.Prime) :
    hA (p ^ 1) = wA (p ^ 1) - chi4 p / p ∧
    hA (p ^ 2) = wA (p ^ 2) - chi4 p / p * wA (p ^ 1) ∧
    hA (p ^ 3) = - (chi4 p / p * wA (p ^ 2)) := by
  have c0 : chiInv (p ^ 0) = 1 := by rw [pow_zero, chiInv_apply, moebius_apply_one, chiA_one]; simp
  have c1 : chiInv (p ^ 1) = - (chi4 p / p) := by
    rw [pow_one, chiInv_apply, moebius_apply_prime hp, chiA_apply]; push_cast; ring
  have c2 := chiInv_prime_pow_zero hp (le_refl 2)
  have c3 := chiInv_prime_pow_zero hp (show 2 ≤ 3 by norm_num)
  have w0 : wA (p ^ 0) = 1 := by rw [pow_zero, wA_apply, Gc_one]; simp
  have w3 : wA (p ^ 3) = 0 := by rw [wA_prime_pow hp, localG_eq_zero (Or.inl le_rfl), zero_mul]
  simp only [hA, conv_prime_pow _ _ hp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceSub, Nat.sub_zero, Nat.sub_self, c0, c1, c2, c3, w0, w3]
  refine ⟨by ring, by ring, by ring⟩

lemma chi4_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : chi4 p = 1 ∨ chi4 p = -1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  unfold chi4
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h <;> simp [h]

lemma wA_one_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    wA (p ^ 1) = ((chi4 p : ℝ) * p + 1) / ((p : ℝ) ^ 2 - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [wA_prime_pow hp, Nat.totient_prime_pow hp (by norm_num)]
  unfold localG localK
  simp only [one_ne_zero, ite_false, hp2, ite_true, Nat.sub_self, pow_zero, one_mul, mul_one]
  rw [Nat.cast_sub hp.one_le]
  push_cast
  have hq : (p : ℝ) - 1 ≠ 0 := by linarith
  have hq2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  field_simp

/-- **Every Euler factor of `h` is `1`.** -/
lemma hA_euler (p : ℕ) (hp : p.Prime) : ∑ e ∈ Finset.range 4, hA (p ^ e) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hA_local p hp
  have hz : hA (p ^ 0) = 1 := by rw [pow_zero]; exact isMultiplicative_hA.map_one
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hz, h1, h2, h3]
  by_cases hp2 : p = 2
  · subst hp2
    have e1 : wA (2 ^ 1) = 1 / 3 := by
      rw [wA_prime_pow Nat.prime_two]; norm_num [localG, localK]
    have e2 : wA (2 ^ 2) = -1 / 3 := by
      rw [wA_prime_pow Nat.prime_two, Nat.totient_prime_pow Nat.prime_two (by norm_num)]
      norm_num [localG, localK]
    rw [e1, e2]; norm_num [chi4]
  · have e2 : wA (p ^ 2) = 0 := by
      rw [wA_prime_pow hp, localG_eq_zero (Or.inr ⟨hp2, le_rfl⟩), zero_mul]
    rw [e2, wA_one_odd p hp hp2]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hq2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    rcases chi4_odd p hp hp2 with hc | hc <;> rw [hc] <;> push_cast <;> field_simp <;> ring

/-- Local bound for `|h|` at an odd prime. -/
lemma hA_local_bound (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ e ∈ Finset.range 4, |hA (p ^ e)| ≤ 1 + 2 * (1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := hA_local p hp
  have hz : hA (p ^ 0) = 1 := by rw [pow_zero]; exact isMultiplicative_hA.map_one
  have e2 : wA (p ^ 2) = 0 := by
    rw [wA_prime_pow hp, localG_eq_zero (Or.inr ⟨hp2, le_rfl⟩), zero_mul]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hz, h1, h2, h3, e2,
    wA_one_odd p hp hp2]
  have h2' : 2 ≤ p := hp.two_le
  have hp3 : (3 : ℝ) ≤ p := by
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hcast : ((p - 2 : ℕ) : ℝ) + 1 = (p : ℝ) - 1 := by
    rw [Nat.cast_sub h2']; push_cast; ring
  rw [hcast]
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0 : (0 : ℝ) < p := by linarith
  rcases chi4_odd p hp hp2 with hc | hc <;> rw [hc] <;> push_cast
  · -- χ = 1: `h(p) = 1/(p(p−1))`, `h(p²) = −1/(p(p−1))`
    have ea : (1 * (p : ℝ) + 1) / ((p : ℝ) ^ 2 - 1) - 1 / p = 1 / (p * ((p : ℝ) - 1)) := by
      field_simp; ring
    have eb : (0 : ℝ) - 1 / p * ((1 * (p : ℝ) + 1) / ((p : ℝ) ^ 2 - 1)) =
        -(1 / (p * ((p : ℝ) - 1))) := by
      field_simp; ring
    rw [ea, eb, abs_neg, mul_zero, neg_zero, abs_zero, abs_one,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (p * ((p : ℝ) - 1)))]
    have : 1 / (p * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith
  · -- χ = −1: `h(p) = 1/(p(p+1))`, `h(p²) = −1/(p(p+1))`
    have ea : (-1 * (p : ℝ) + 1) / ((p : ℝ) ^ 2 - 1) - -1 / p = 1 / (p * ((p : ℝ) + 1)) := by
      field_simp; ring
    have eb : (0 : ℝ) - -1 / p * ((-1 * (p : ℝ) + 1) / ((p : ℝ) ^ 2 - 1)) =
        -(1 / (p * ((p : ℝ) + 1))) := by
      field_simp; ring
    rw [ea, eb, abs_neg, mul_zero, neg_zero, abs_zero, abs_one,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (p * ((p : ℝ) + 1)))]
    have : 1 / (p * ((p : ℝ) + 1)) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    linarith

lemma sum_abs_hA_le (u : Finset ℕ) :
    ∑ c ∈ u, |hA c| ≤ (∑ e ∈ Finset.range 4, |hA (2 ^ e)| + 1) * 1 * Real.exp (2 * Cser) := by
  refine sum_le_of_multiplicative (F := fun c => |hA c|) (fun _ => abs_nonneg _)
    (by simp) (by simp [isMultiplicative_hA.map_one])
    (fun h => by simp only [isMultiplicative_hA.map_mul_of_coprime h, abs_mul])
    (fun hp e he => by simp [hA_prime_pow_zero hp he]) (fun S hS => ?_) u
  have hb := prod_le_of_local hS (fun p => ∑ e ∈ Finset.range 4, |hA (p ^ e)|) (fun _ => 1)
    (x₂ := ∑ e ∈ Finset.range 4, |hA (2 ^ e)| + 1) (K := 2)
    (by have : 0 ≤ ∑ e ∈ Finset.range 4, |hA (2 ^ e)| :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        linarith) (by norm_num)
    (fun p _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (fun _ _ => zero_le_one)
    (fun p hp => ?_)
  · simpa using hb
  · have hh0 : 0 ≤ 1 / (((p - 2 : ℕ) : ℝ) + 1) ^ 2 := by positivity
    by_cases hp2 : p = 2
    · subst hp2
      simp only [ite_true, mul_one]
      set y := 1 / (((2 - 2 : ℕ) : ℝ) + 1) ^ 2
      have hx : 0 ≤ ∑ e ∈ Finset.range 4, |hA (2 ^ e)| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have : (∑ e ∈ Finset.range 4, |hA (2 ^ e)| + 1) * 1 ≤
          (∑ e ∈ Finset.range 4, |hA (2 ^ e)| + 1) * (1 + 2 * y) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    · simp only [hp2, ite_false, one_mul]
      exact hA_local_bound p (hS p hp) hp2

lemma summable_abs_hA : Summable (fun n => |hA n|) :=
  summable_of_sum_le (fun _ => abs_nonneg _) sum_abs_hA_le

/-- `Σ h = 1`. -/
lemma tsum_hA : ∑' n, hA n = 1 := by
  have h := EulerProduct.eulerProduct_tprod (f := fun n => hA n) isMultiplicative_hA.map_one
    (fun h => isMultiplicative_hA.map_mul_of_coprime h)
    (by simpa [Real.norm_eq_abs] using summable_abs_hA) (by simp)
  rw [← h]
  have : ∀ p : Nat.Primes, ∑' e, hA ((p : ℕ) ^ e) = 1 := fun p => by
    rw [tsum_eq_sum (s := Finset.range 4) (fun e he =>
      hA_prime_pow_zero p.2 (by simp at he; omega))]
    exact hA_euler p p.2
  simp only [this, tprod_one]

/-- Partial sums of `χ(n)/n`. -/
noncomputable def Achi (X : ℕ) : ℝ := ∑ m ∈ Finset.Ioc 0 X, chiA m

lemma Achi_eq (X : ℕ) :
    Achi X = ∑ i ∈ Finset.range ((X + 1) / 2), (-1 : ℝ) ^ i / (2 * i + 1) := by
  induction X with
  | zero => simp [Achi]
  | succ X ih =>
    rw [Achi, Finset.sum_Ioc_succ_top (Nat.zero_le X), ← Achi, ih]
    obtain ⟨j, rfl | rfl⟩ : ∃ j, X = 2 * j ∨ X = 2 * j + 1 := ⟨X / 2, by omega⟩
    · rw [show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
        Finset.sum_range_succ, chiA_apply]
      congr 1
      have hc : (chi4 (2 * j + 1) : ℝ) = (-1) ^ j := by
        rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
        · subst hr
          rw [Even.neg_one_pow ⟨r, rfl⟩]
          norm_num [chi4, show (2 * (r + r) + 1) % 4 = 1 by omega]
        · subst hr
          rw [Odd.neg_one_pow ⟨r, rfl⟩]
          norm_num [chi4, show (2 * (2 * r + 1) + 1) % 4 = 3 by omega]
      rw [hc]
      push_cast
      ring
    · rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1 + 1 + 1) / 2 = j + 1 by omega,
        chiA_apply]
      have hc : chi4 (2 * j + 1 + 1) = 0 := by
        unfold chi4
        simp only [show ¬ ((2 * j + 1 + 1) % 4 = 1) by omega,
          show ¬ ((2 * j + 1 + 1) % 4 = 3) by omega, ite_false]
      rw [hc]
      simp

lemma tendsto_Achi : Filter.Tendsto Achi Filter.atTop (nhds (Real.pi / 4)) := by
  rw [show Achi = fun X => ∑ i ∈ Finset.range ((X + 1) / 2), (-1 : ℝ) ^ i / (2 * i + 1) from
    funext Achi_eq]
  exact Real.tendsto_sum_pi_div_four.comp
    (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨2 * b, fun a ha => by omega⟩))

/-- **The term `t = 0`**: `Σ_{c ≤ C} G(c) φ(c) → π/4`. -/
theorem tendsto_sum_wA :
    Filter.Tendsto (fun C => ∑ c ∈ Finset.Ioc 0 C, wA c) Filter.atTop (nhds (Real.pi / 4)) := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto Achi tendsto_Achi).exists_norm_le
  have hM' : ∀ X, |Achi X| ≤ M := fun X => by
    simpa [Real.norm_eq_abs] using hM (Achi X) ⟨X, rfl⟩
  have hsplit : ∀ C, ∑ c ∈ Finset.Ioc 0 C, wA c = ∑' n, hA n * Achi (C / n) := by
    intro C
    rw [wA_eq, sum_Ioc_mul_eq_sum_sum]
    rw [tsum_eq_sum (s := Finset.Ioc 0 C) (fun n hn => ?_)]
    · rfl
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · have : C < n := by simp at hn; omega
        rw [Nat.div_eq_of_lt this]
        simp [Achi]
  simp_rw [hsplit]
  have hlim : Real.pi / 4 = ∑' n, hA n * (Real.pi / 4) := by
    rw [tsum_mul_right, tsum_hA, one_mul]
  rw [hlim]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => |hA n| * M)
    (summable_abs_hA.mul_right M) (fun n => ?_) (Filter.Eventually.of_forall (fun C n => ?_))
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · exact (tendsto_Achi.comp (Nat.tendsto_div_const_atTop hn0.ne')).const_mul (hA n)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM' _) (abs_nonneg _)

end TermZero

/-!
### Assembly: Theorem B for a Schwartz test function
-/

section Assembly

open scoped SchwartzMap FourierTransform

lemma sum_Ioc_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (h0 : f 0 = 0) (C : ℕ) :
    ∑ c ∈ Finset.Ioc 0 C, f c = ∑ c ∈ Finset.range (C + 1), f c := by
  induction C with
  | zero => simp [h0]
  | succ C ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le C), ih, Finset.sum_range_succ _ (C + 1)]

lemma RSc_zero (c : ℕ) : RSc 0 c = (Nat.totient c : ℂ) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [RSc]
  · have : NeZero c := ⟨hc.ne'⟩
    rw [RSc_eq]
    unfold RS
    simp [ZMod.card_units_eq_totient]

lemma gc_zero_eq (c : ℕ) : gc 0 c = (wA c : ℂ) := by
  rw [gc, RSc_zero, wA_apply]; push_cast; ring

lemma norm_RSc_le (t : ℤ) (c : ℕ) : ‖RSc t c‖ ≤ Nat.totient c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [RSc]
  · have : NeZero c := ⟨hc.ne'⟩
    rw [RSc_eq]
    unfold RS
    calc ‖∑ a : (ZMod c)ˣ, ZMod.stdAddChar ((a : ZMod c) * (t : ZMod c))‖
        ≤ ∑ a : (ZMod c)ˣ, ‖ZMod.stdAddChar ((a : ZMod c) * (t : ZMod c))‖ := norm_sum_le _ _
      _ = Nat.totient c := by
          simp [ZMod.stdAddChar_apply, ZMod.card_units_eq_totient]

lemma summable_abs_mul_norm (g : 𝓢(ℝ, ℂ)) : Summable (fun t : ℤ => |(t : ℝ)| * ‖g t‖) := by
  have h := (g.isBigO_cocompact_rpow (-3)).norm_left
  have h2 : (fun x : ℝ => |x| * ‖g x‖) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    have h3 := (Asymptotics.isBigO_refl (fun x : ℝ => |x|) (Filter.cocompact ℝ)).mul h
    refine h3.trans_eventuallyEq ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with x hx
    have hx0 : 0 < |x| := abs_pos.mpr hx
    simp only [Real.norm_eq_abs]
    rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have h4 := h2.comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) h4

/-- The limit function: `F(t) = Σ_c G(c) c_c(t)` (`= Π_p E_p(t)`) for `t ≠ 0`, `F(0) = π/4`. -/
noncomputable def Flim (t : ℤ) : ℂ := if t = 0 then ((Real.pi / 4 : ℝ) : ℂ) else ∑' c, gc t c

/-- **Theorem B (Poisson form).** For every Schwartz function `f`, the `c`-ordered partial sums
`Σ_{c ≤ C} G(c) Σ_{(m, c) = 1} f(m/c)` converge to `Σ_t 𝓕f(t) F(t)`. -/
theorem theoremB_schwartz (f : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto (fun C : ℕ => ∑ c ∈ Finset.Ioc 0 C, (Gc c : ℂ) *
        ∑' m : ℤ, (if Nat.Coprime m.natAbs c then f ((m : ℝ) / c) else 0))
      Filter.atTop (nhds (∑' t : ℤ, 𝓕 f t * Flim t)) := by
  have hF := summable_norm_int (𝓕 f)
  -- step 1: Poisson in each modulus, then swap the finite `c`-sum with the `t`-series
  have hrw : ∀ C : ℕ, (∑ c ∈ Finset.Ioc 0 C, (Gc c : ℂ) *
      ∑' m : ℤ, (if Nat.Coprime m.natAbs c then f ((m : ℝ) / c) else 0)) =
      ∑' t : ℤ, 𝓕 f t * ∑ c ∈ Finset.Ioc 0 C, gc t c := by
    intro C
    have h1 : ∀ c ∈ Finset.Ioc 0 C, (Gc c : ℂ) *
        ∑' m : ℤ, (if Nat.Coprime m.natAbs c then f ((m : ℝ) / c) else 0) =
        ∑' t : ℤ, 𝓕 f t * gc t c := by
      intro c hc
      have : NeZero c := ⟨by simp at hc; omega⟩
      rw [poisson_coprime f c, ← tsum_mul_left]
      congr 1; funext t; rw [gc]; ring
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun c _ => ?_)]
    · congr 1; funext t; rw [Finset.mul_sum]
    · refine Summable.of_norm_bounded (hF.mul_right (|Gc c| * Nat.totient c)) (fun t => ?_)
      rw [norm_mul, gc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_RSc_le t c) (abs_nonneg _))
        (norm_nonneg _)
  simp_rw [hrw]
  -- step 2: bounds on the partial sums
  obtain ⟨M₀, hM₀⟩ := (Metric.isBounded_range_of_tendsto _ tendsto_sum_wA).exists_norm_le
  have hM₀' : ∀ C, |∑ c ∈ Finset.Ioc 0 C, wA c| ≤ M₀ := fun C => by
    simpa [Real.norm_eq_abs] using hM₀ _ ⟨C, rfl⟩
  have hM₀0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀' 0)
  set B : ℝ := 2 * Real.exp (1 * Cser)
  have hB0 : 0 ≤ B := by positivity
  have hP : ∀ (C : ℕ) (t : ℤ), ‖∑ c ∈ Finset.Ioc 0 C, gc t c‖ ≤ M₀ + B * |(t : ℝ)| := by
    intro C t
    by_cases ht : t = 0
    · subst ht
      simp_rw [gc_zero_eq]
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
      simp only [Int.cast_zero, abs_zero, mul_zero, add_zero]
      exact hM₀' C
    · have hnat : (t.natAbs : ℝ) = |(t : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      calc ‖∑ c ∈ Finset.Ioc 0 C, gc t c‖ ≤ ∑ c ∈ Finset.Ioc 0 C, ‖gc t c‖ := norm_sum_le _ _
        _ ≤ 2 * (t.natAbs : ℝ) * Real.exp (1 * Cser) := sum_norm_gc_le t ht _
        _ = B * |(t : ℝ)| := by rw [hnat]; ring
        _ ≤ M₀ + B * |(t : ℝ)| := by linarith
  -- step 3: dominated convergence over `t`
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun t : ℤ => M₀ * ‖𝓕 f t‖ + B * (|(t : ℝ)| * ‖𝓕 f t‖))
    ((hF.mul_left M₀).add ((summable_abs_mul_norm (𝓕 f)).mul_left B)) (fun t => ?_)
    (Filter.Eventually.of_forall (fun C t => ?_))
  · refine Filter.Tendsto.const_mul (𝓕 f t) ?_
    by_cases ht : t = 0
    · subst ht
      simp only [Flim, ite_true]
      simp_rw [gc_zero_eq, ← Complex.ofReal_sum]
      exact (Complex.continuous_ofReal.tendsto _).comp tendsto_sum_wA
    · simp only [Flim, ht, ite_false]
      simp_rw [sum_Ioc_eq_sum_range (fun c => gc t c) (gc_zero t)]
      have hs : Summable (fun c => gc t c) := (summable_gc t ht).of_norm
      exact (Filter.tendsto_add_atTop_iff_nat 1).mpr hs.hasSum.tendsto_sum_nat
  · rw [norm_mul]
    calc ‖𝓕 f t‖ * ‖∑ c ∈ Finset.Ioc 0 C, gc t c‖ ≤ ‖𝓕 f t‖ * (M₀ + B * |(t : ℝ)|) :=
          mul_le_mul_of_nonneg_left (hP C t) (norm_nonneg _)
      _ = M₀ * ‖𝓕 f t‖ + B * (|(t : ℝ)| * ‖𝓕 f t‖) := by ring

/-- For `t ≠ 0` the limit function is the Euler product of Lemma 6. -/
theorem Flim_hasProd (t : ℤ) (ht : t ≠ 0) :
    HasProd (fun p : Nat.Primes => (Eloc t p : ℂ)) (Flim t) := by
  simp only [Flim, ht, ite_false]
  exact (global_identity t ht).2

end Assembly

/-!
### Theorem B in the doc's form

`Φ` is smooth with `Φ(y) ≠ 0 ⇒ a ≤ y ≤ b`, `a > 0`. With `ψ(x) = Φ(x⁻²) x⁻²` (extended evenly
to `ℝ`), the masses of `ν₂` paired with `Φ` are `T₂(c) Φ((c/m)²)/m² = T₂(c) ψ(m/c)/c²`, where
`T₂(c) = c² G(c)/ζ(2)` and `ζ(2) = π²/6`, and `I(t) = ∫ Φ(y) cos(2πt/√y) y^(−1/2) dy = 𝓕ψ(t)`.
-/

section TheoremB

open scoped SchwartzMap FourierTransform
open MeasureTheory
open scoped ContDiff

/-- `ψ(x) = Φ(x⁻²) x⁻²`. -/
noncomputable def psiFun (Φ : ℝ → ℝ) (x : ℝ) : ℝ := Φ ((x ^ 2)⁻¹) * (x ^ 2)⁻¹

/-- The doc's `I(t) = ∫_0^∞ Φ(y) cos(2πt/√y) y^(−1/2) dy`. -/
noncomputable def Iphi (Φ : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ y in Set.Ioi 0, Φ y * Real.cos (2 * Real.pi * w / Real.sqrt y) * y ^ (-1 / 2 : ℝ)

/-- `T₂(c) = c² G(c)/ζ(2)`, with `ζ(2) = π²/6`. -/
noncomputable def T2 (c : ℕ) : ℝ := (c : ℝ) ^ 2 * Gc c / (Real.pi ^ 2 / 6)

variable {Φ : ℝ → ℝ} {a b : ℝ}

lemma psiFun_neg (Φ : ℝ → ℝ) (x : ℝ) : psiFun Φ (-x) = psiFun Φ x := by
  simp [psiFun]

lemma psiFun_eq_zero_near (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b) {x : ℝ} (hx : x ^ 2 * b < 1) :
    psiFun Φ x = 0 := by
  by_cases hx0 : x = 0
  · simp [psiFun, hx0]
  · have hpos : 0 < x ^ 2 := by positivity
    have : Φ ((x ^ 2)⁻¹) = 0 := by
      by_contra h
      have h2 := (hsupp _ h).2
      have h3 : (x ^ 2)⁻¹ * x ^ 2 ≤ b * x ^ 2 := mul_le_mul_of_nonneg_right h2 hpos.le
      rw [inv_mul_cancel₀ hpos.ne'] at h3
      linarith
    simp [psiFun, this]

lemma psiFun_eq_zero_far (ha : 0 < a) (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b) {x : ℝ}
    (hx : 1 + 1 / a < |x|) : psiFun Φ x = 0 := by
  have h1 : 1 < |x| := by
    have : 0 < 1 / a := div_pos one_pos ha
    linarith
  have hx2 : 1 / a < x ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have hlt : (x ^ 2)⁻¹ < a := by
    rw [inv_lt_comm₀ (lt_trans (div_pos one_pos ha) hx2) ha]
    simpa using hx2
  have : Φ ((x ^ 2)⁻¹) = 0 := by
    by_contra h
    linarith [(hsupp _ h).1]
  simp [psiFun, this]

lemma psiFun_contDiff (hΦ : ContDiff ℝ ∞ Φ) (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b) :
    ContDiff ℝ ∞ (psiFun Φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hopen : IsOpen {y : ℝ | y ^ 2 * b < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have : psiFun Φ =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds (by simp)] with y hy using psiFun_eq_zero_near hsupp hy
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have h2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hinv : ContDiffAt ℝ ∞ (fun y : ℝ => (y ^ 2)⁻¹) x :=
      (contDiffAt_id.pow 2).inv h2
    exact (hΦ.contDiffAt.comp x hinv).mul hinv

lemma psiFun_hasCompactSupport (ha : 0 < a) (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b) :
    HasCompactSupport (fun x => (psiFun Φ x : ℂ)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(1 + 1 / a)) (b := 1 + 1 / a))
    (fun x hx => ?_)
  have : 1 + 1 / a < |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; exact hx
  simp [psiFun_eq_zero_far ha hsupp this]

/-- `ψ` as a Schwartz function. -/
noncomputable def psiS (hΦ : ContDiff ℝ ∞ Φ) (ha : 0 < a)
    (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b) : 𝓢(ℝ, ℂ) :=
  (psiFun_hasCompactSupport ha hsupp).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (psiFun_contDiff hΦ hsupp))

lemma psiS_apply (hΦ : ContDiff ℝ ∞ Φ) (ha : 0 < a) (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b)
    (x : ℝ) : psiS hΦ ha hsupp x = (psiFun Φ x : ℂ) := rfl

lemma rpow_aux {x : ℝ} (hx : 0 < x) :
    x ^ (-2 : ℝ) = (x ^ 2)⁻¹ ∧ x ^ ((-2 : ℝ) - 1) = (x ^ 3)⁻¹ ∧
      Real.sqrt (x ^ (-2 : ℝ)) = x⁻¹ ∧ (x ^ (-2 : ℝ)) ^ (-1 / 2 : ℝ) = x := by
  have h1 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [show (-2 : ℝ) - 1 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]
  · rw [h1, Real.sqrt_inv, Real.sqrt_sq hx.le]
  · rw [← Real.rpow_mul hx.le]; norm_num

/-- The change of variables `y = x⁻²`: `I(w) = 2 ∫_0^∞ ψ(x) cos(2πxw) dx`. -/
lemma Iphi_eq (Φ : ℝ → ℝ) (w : ℝ) :
    Iphi Φ w = 2 * ∫ x in Set.Ioi 0, psiFun Φ x * Real.cos (2 * Real.pi * x * w) := by
  unfold Iphi
  rw [← integral_comp_rpow_Ioi
    (fun y => Φ y * Real.cos (2 * Real.pi * w / Real.sqrt y) * y ^ (-1 / 2 : ℝ))
    (show (-2 : ℝ) ≠ 0 by norm_num), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx' : 0 < x := hx
  obtain ⟨h1, h2, h3, h4⟩ := rpow_aux hx'
  simp only [smul_eq_mul]
  rw [h3, h4, h1, h2, div_inv_eq_mul]
  unfold psiFun
  have hx0 : x ≠ 0 := hx'.ne'
  norm_num
  field_simp

/-- `𝓕ψ(w) = I(w)`. -/
lemma fourier_psiS (hΦ : ContDiff ℝ ∞ Φ) (ha : 0 < a) (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b)
    (w : ℝ) : 𝓕 (psiS hΦ ha hsupp) w = (Iphi Φ w : ℂ) := by
  set ψS := psiS hΦ ha hsupp
  set g := psiFun Φ
  have hE : 𝓕 ψS w = ∫ v, Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • (g v : ℂ) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    rfl
  have hint : ∀ s : ℝ, Integrable (fun v : ℝ => Complex.exp (↑(s * v * w) * Complex.I) • (g v : ℂ)) := by
    intro s
    refine (ψS.integrable).norm.mono' ?_ (Filter.Eventually.of_forall (fun v => ?_))
    · exact (Continuous.smul (f := fun v : ℝ => Complex.exp (↑(s * v * w) * Complex.I))
        (by fun_prop) ψS.continuous).aestronglyMeasurable
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rfl
  have hsym : ∫ v, Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • (g v : ℂ) =
      ∫ v, Complex.exp (↑(2 * Real.pi * v * w) * Complex.I) • (g v : ℂ) := by
    rw [← integral_neg_eq_self]
    congr 1
    funext v
    have hg : g (-v) = g v := psiFun_neg Φ v
    rw [hg]
    congr 3
    push_cast
    ring
  have key : ∀ X : ℂ, Complex.exp (-X * Complex.I) + Complex.exp (X * Complex.I) =
      2 * Complex.cos X := fun X => by rw [Complex.two_cos]; ring
  have h2 : 2 * ∫ v, Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • (g v : ℂ) =
      ∫ v, ((2 * (g v * Real.cos (2 * Real.pi * v * w)) : ℝ) : ℂ) := by
    rw [two_mul]
    nth_rewrite 2 [hsym]
    rw [← integral_add (hint _) (hint _)]
    congr 1
    funext v
    rw [smul_eq_mul, smul_eq_mul, ← add_mul]
    have e : ((-2 * Real.pi * v * w : ℝ) : ℂ) = -((2 * Real.pi * v * w : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, key, ← Complex.ofReal_cos]
    push_cast
    ring
  have h3 : ∫ v, ((2 * (g v * Real.cos (2 * Real.pi * v * w)) : ℝ) : ℂ) =
      ((2 * (2 * ∫ x in Set.Ioi 0, g x * Real.cos (2 * Real.pi * x * w)) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_const_mul]
    congr 2
    have habs := integral_comp_abs (f := fun y => g y * Real.cos (2 * Real.pi * y * w))
    rw [← habs]
    congr 1
    funext v
    rcases abs_cases v with ⟨hv, -⟩ | ⟨hv, -⟩
    · rw [hv]
    · simp only [hv, g, psiFun_neg]
      rw [show 2 * Real.pi * -v * w = -(2 * Real.pi * v * w) by ring, Real.cos_neg]
  rw [hE]
  have : ∫ v, Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • (g v : ℂ) =
      ((2 * ∫ x in Set.Ioi 0, g x * Real.cos (2 * Real.pi * x * w) : ℝ) : ℂ) := by
    have := h2.trans h3
    push_cast at this ⊢
    linear_combination this / 2
  rw [this, Iphi_eq]

/-- The masses: `Σ_{m ≥ 1, (m, c) = 1} T₂(c) Φ((c/m)²)/m² = (3/π²) G(c) Σ_{m ∈ ℤ, (m,c)=1} ψ(m/c)`. -/
lemma masses_eq (hΦ : ContDiff ℝ ∞ Φ) (ha : 0 < a) (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b)
    (c : ℕ) [NeZero c] :
    ∑' m : ℕ, ((if Nat.Coprime m c then T2 c * Φ (((c : ℝ) / m) ^ 2) / (m : ℝ) ^ 2 else 0 : ℝ) : ℂ)
      = (3 / Real.pi ^ 2 : ℂ) * ((Gc c : ℂ) *
        ∑' m : ℤ, (if Nat.Coprime m.natAbs c then psiS hΦ ha hsupp ((m : ℝ) / c) else 0)) := by
  set ψS := psiS hΦ ha hsupp
  set F : ℤ → ℂ := fun m => if Nat.Coprime m.natAbs c then ψS ((m : ℝ) / c) else 0 with hFdef
  have hterm : ∀ m : ℕ,
      ((if Nat.Coprime m c then T2 c * Φ (((c : ℝ) / m) ^ 2) / (m : ℝ) ^ 2 else 0 : ℝ) : ℂ) =
        (6 / Real.pi ^ 2 : ℂ) * (Gc c : ℂ) * F m := by
    intro m
    simp only [hFdef, Int.natAbs_natCast, Int.cast_natCast]
    split_ifs
    · rw [psiS_apply]
      have hr : T2 c * Φ (((c : ℝ) / m) ^ 2) / (m : ℝ) ^ 2 =
          6 / Real.pi ^ 2 * Gc c * psiFun Φ ((m : ℝ) / c) := by
        unfold T2 psiFun
        rw [show (((m : ℝ) / c) ^ 2)⁻¹ = ((c : ℝ) / m) ^ 2 by rw [← inv_pow, inv_div]]
        ring
      rw [hr]
      push_cast
      ring
    · simp
  have hF : Summable F := by
    refine Summable.of_norm_bounded (summable_norm_div ψS c) (fun m => ?_)
    simp only [hFdef]; split_ifs <;> simp
  have hF0 : F 0 = 0 := by
    simp only [hFdef]; split_ifs
    · rw [psiS_apply]; simp [psiFun]
    · rfl
  have hFeven : ∀ n : ℕ, F (-((n : ℤ) + 1)) = F ((n + 1 : ℕ) : ℤ) := by
    intro n
    have hn : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [hFdef, Int.natAbs_neg, hn, Int.natAbs_natCast]
    split_ifs
    · rw [psiS_apply, psiS_apply]
      have : (((-((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ) / c = -((((n + 1 : ℕ) : ℤ) : ℝ) / c) := by
        push_cast; ring
      rw [this, psiFun_neg]
    · rfl
  have hs1 : Summable (fun n : ℕ => F n) := hF.comp_injective Nat.cast_injective
  have hs2 : Summable (fun n : ℕ => F ((n + 1 : ℕ) : ℤ)) :=
    hF.comp_injective (fun x y h => by simpa using h)
  have hhalf : ∑' n : ℕ, F n = (1 / 2 : ℂ) * ∑' m : ℤ, F m := by
    rw [← tsum_nat_add_neg_add_one hF]
    simp_rw [hFeven]
    rw [Summable.tsum_add hs1 hs2]
    have hz := hs1.tsum_eq_zero_add
    simp only [Nat.cast_zero, hF0, zero_add] at hz
    rw [← hz]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, hhalf]
  ring

/-- **Theorem B.** The `c`-ordered partial sums of `ν₂` paired with `Φ`,
`Σ_{c ≤ C} Σ_{m ≥ 1, (m, c) = 1} T₂(c) Φ((c/m)²)/m²`, converge to
`(1/(2ζ(2))) Σ_t f₂(t) I(t)`, where `f₂ = Flim` (`f₂(t) = Π_p E_p(t)` for `t ≠ 0`,
`f₂(0) = π/4`) and `ζ(2) = π²/6`. Dividing by `I(0)` gives the doc's normalization. -/
theorem theoremB (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ y, Φ y ≠ 0 → a ≤ y ∧ y ≤ b) :
    Filter.Tendsto (fun C : ℕ => ∑ c ∈ Finset.Ioc 0 C, ∑' m : ℕ,
        ((if Nat.Coprime m c then T2 c * Φ (((c : ℝ) / m) ^ 2) / (m : ℝ) ^ 2 else 0 : ℝ) : ℂ))
      Filter.atTop
      (nhds (1 / (2 * (Real.pi ^ 2 / 6)) * ∑' t : ℤ, Flim t * (Iphi Φ t : ℂ))) := by
  set ψS := psiS hΦ ha hsupp
  have hB := (theoremB_schwartz ψS).const_mul (3 / Real.pi ^ 2 : ℂ)
  have hL : (1 / (2 * (Real.pi ^ 2 / 6)) : ℂ) * ∑' t : ℤ, Flim t * (Iphi Φ t : ℂ) =
      (3 / Real.pi ^ 2 : ℂ) * ∑' t : ℤ, 𝓕 ψS t * Flim t := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    congr 1
    · field_simp; ring
    · congr 1; funext t; rw [fourier_psiS hΦ ha hsupp]; ring
  have hS : ∀ C : ℕ, (∑ c ∈ Finset.Ioc 0 C, ∑' m : ℕ,
      ((if Nat.Coprime m c then T2 c * Φ (((c : ℝ) / m) ^ 2) / (m : ℝ) ^ 2 else 0 : ℝ) : ℂ)) =
      (3 / Real.pi ^ 2 : ℂ) * ∑ c ∈ Finset.Ioc 0 C, (Gc c : ℂ) *
        ∑' m : ℤ, (if Nat.Coprime m.natAbs c then ψS ((m : ℝ) / c) else 0) := by
    intro C
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    have : NeZero c := ⟨by simp at hc; omega⟩
    exact masses_eq hΦ ha hsupp c
  rw [hL]
  simp_rw [hS]
  exact hB

end TheoremB

end Murmurations

#print axioms Murmurations.nuSum_odd
#print axioms Murmurations.nuSum_two
#print axioms Murmurations.kloosterman_sum_odd_prime
#print axioms Murmurations.kloosterman_sum_odd_prime_pow
#print axioms Murmurations.kloosterman_sum_two_pow
#print axioms Murmurations.kloosterman_sum_two
#print axioms Murmurations.kloosterman_sum_four
#print axioms Murmurations.kloosterman_sum_eight
#print axioms Murmurations.hasSum_E_odd
#print axioms Murmurations.local_identity_odd
#print axioms Murmurations.hasSum_E_two
#print axioms Murmurations.local_identity_two
#print axioms Murmurations.KS_mul
#print axioms Murmurations.KS_formula

#print axioms Murmurations.RS_indep
#print axioms Murmurations.summable_gc
#print axioms Murmurations.Gc_eq
#print axioms Murmurations.global_identity
#print axioms Murmurations.poisson_coprime
#print axioms Murmurations.sum_norm_gc_le
#print axioms Murmurations.tendsto_sum_wA
#print axioms Murmurations.theoremB_schwartz
#print axioms Murmurations.Flim_hasProd
#print axioms Murmurations.Iphi_eq
#print axioms Murmurations.fourier_psiS
#print axioms Murmurations.theoremB
