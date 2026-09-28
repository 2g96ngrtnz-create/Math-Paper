import HubRemoval.FibreCount
import HubRemoval.Turan

/-!
# The elementary smooth-number bound (paper, Lemma 2.3)

**Lemma 2.3.** For `x ≥ 2` and `2 ≤ y ≤ x`, `Ψ(x, y) ≤ √x + 2x(log y + c₀)/log x`.

The input is Mertens' estimate, the paper's Lemma 2.1(a):
`∑_{p ≤ y} log p/(p − 1) ≤ log y + c₀`. Mertens' theorem is not in Mathlib, so the estimate for
this `y` is an explicit hypothesis `hM`. Everything else is proved.

The proof is the paper's.
* For `y`-smooth `n`, `log n = ∑_{p ≤ y} v_p(n) log p`. Summing over `n ≤ x`,
  `∑_{n ≤ x, P⁺(n) ≤ y} log n ≤ ∑_{p ≤ y} log p · v_p(x!) ≤ x ∑_{p ≤ y} log p/(p − 1)`.
  The last step is Legendre's theorem, `(p − 1) v_p(x!) ≤ x`, from Mathlib.
* At most `√x` of the counted `n` are `≤ √x`, and each of the others has `log n ≥ ½ log x`.

The paper's consequence `ρ(u) ≤ 2/u` also needs Dickman's theorem, and is not formalised.
-/

namespace HubRemoval

open Finset
open scoped Nat

/-- For `y`-smooth `n`, `log n = ∑_{p ≤ y} v_p(n) log p`. -/
theorem log_eq_sum_primesUpTo {n y : ℕ} (hn : n ∈ Nat.smoothNumbers (y + 1)) :
    Real.log n = ∑ p ∈ primesUpTo y, (n.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  apply sum_subset
  · intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have := (Nat.mem_smoothNumbers'.mp hn) p hp'.1 hp'.2.1
    exact mem_primesUpTo.mpr ⟨hp'.1, by omega⟩
  · intro p _ hp
    have : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    simp [this]

/-- Legendre: `∑_{1 ≤ n ≤ x} v_p(n) = v_p(x!)`, and `(p − 1) v_p(x!) ≤ x`. So the sum of
`v_p(n)` over any set of integers in `[1, x]` is at most `x/(p − 1)`. -/
theorem sum_factorization_le {x p : ℕ} (hp : p.Prime) {S : Finset ℕ} (hS : S ⊆ Ico 1 (x + 1)) :
    (∑ n ∈ S, (n.factorization p : ℝ)) ≤ (x : ℝ) / ((p : ℝ) - 1) := by
  have hfact : (x !).factorization p = ∑ n ∈ Ico 1 (x + 1), n.factorization p := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.factorization_prod fun n hn => by
      have := (mem_Ico.mp hn).1
      omega]
    simp
  have hleg : (p - 1) * (x !).factorization p ≤ x := by
    have := Fact.mk hp
    rw [Nat.factorization_def _ hp, sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hsub : ∑ n ∈ S, n.factorization p ≤ (x !).factorization p := by
    rw [hfact]
    exact sum_le_sum_of_subset hS
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcast : ((p : ℝ) - 1) * ((x !).factorization p : ℝ) ≤ x := by
    have : (((p - 1 : ℕ) : ℝ)) * ((x !).factorization p : ℝ) ≤ x := by exact_mod_cast hleg
    rwa [Nat.cast_sub hp.one_lt.le, Nat.cast_one] at this
  rw [le_div_iff₀ (by linarith)]
  have : (∑ n ∈ S, (n.factorization p : ℝ)) ≤ ((x !).factorization p : ℝ) := by
    exact_mod_cast hsub
  nlinarith

/-- `∑_{n ≤ x, P⁺(n) ≤ y} log n ≤ x ∑_{p ≤ y} log p/(p − 1)`. -/
theorem sum_log_smooth_le (x y : ℕ) :
    ∑ n ∈ Nat.smoothNumbersUpTo x (y + 1), Real.log n ≤
      x * ∑ p ∈ primesUpTo y, Real.log p / ((p : ℝ) - 1) := by
  set S := Nat.smoothNumbersUpTo x (y + 1)
  have hS : S ⊆ Ico 1 (x + 1) := fun n hn => by
    obtain ⟨hnx, hns⟩ := Nat.mem_smoothNumbersUpTo.mp hn
    have := (Nat.mem_smoothNumbers.mp hns).1
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  calc ∑ n ∈ S, Real.log n
      = ∑ n ∈ S, ∑ p ∈ primesUpTo y, (n.factorization p : ℝ) * Real.log p :=
        sum_congr rfl fun n hn => log_eq_sum_primesUpTo (Nat.mem_smoothNumbersUpTo.mp hn).2
    _ = ∑ p ∈ primesUpTo y, Real.log p * ∑ n ∈ S, (n.factorization p : ℝ) := by
        rw [sum_comm]
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun n _ => mul_comm _ _
    _ ≤ ∑ p ∈ primesUpTo y, Real.log p * ((x : ℝ) / ((p : ℝ) - 1)) := by
        refine sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)
        exact sum_factorization_le (mem_primesUpTo.mp hp).1 hS
    _ = x * ∑ p ∈ primesUpTo y, Real.log p / ((p : ℝ) - 1) := by
        rw [mul_sum]
        exact sum_congr rfl fun p _ => by ring

/-- **Lemma 2.3.** Assuming Mertens' estimate `∑_{p ≤ y} log p/(p − 1) ≤ log y + c₀`,
`Ψ(x, y) ≤ √x + 2x(log y + c₀)/log x` for `x ≥ 2`. -/
theorem psi_upper {x y : ℕ} (hx : 2 ≤ x) {c₀ : ℝ}
    (hM : ∑ p ∈ primesUpTo y, Real.log p / ((p : ℝ) - 1) ≤ Real.log y + c₀) :
    (psi x y : ℝ) ≤ Real.sqrt x + 2 * x * (Real.log y + c₀) / Real.log x := by
  set S := Nat.smoothNumbersUpTo x (y + 1)
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlogx : 0 < Real.log x := Real.log_pos hxR
  have hsqrt0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  set Sbig := S.filter fun n : ℕ => Real.sqrt x < n
  -- At most `√x` elements are `≤ √x`.
  have hsmall : ((S.filter fun n : ℕ => ¬ Real.sqrt x < n).card : ℝ) ≤ Real.sqrt x := by
    have hsub : S.filter (fun n : ℕ => ¬ Real.sqrt x < n) ⊆ Icc 1 ⌊Real.sqrt x⌋₊ := by
      intro n hn
      obtain ⟨hnS, hnle⟩ := mem_filter.mp hn
      have hn0 := (Nat.mem_smoothNumbers.mp (Nat.mem_smoothNumbersUpTo.mp hnS).2).1
      push Not at hnle
      exact mem_Icc.mpr ⟨by omega, Nat.le_floor hnle⟩
    have h1 := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hsqrt0.le)
  have hsplit : (S.card : ℝ) = Sbig.card + (S.filter fun n : ℕ => ¬ Real.sqrt x < n).card := by
    exact_mod_cast (card_filter_add_card_filter_not (s := S) (fun n : ℕ => Real.sqrt x < n)).symm
  -- Each `n > √x` has `log n ≥ ½ log x`.
  have hbig : (Sbig.card : ℝ) * (Real.log x / 2) ≤ ∑ n ∈ S, Real.log n := by
    calc (Sbig.card : ℝ) * (Real.log x / 2) = ∑ _n ∈ Sbig, Real.log x / 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Sbig, Real.log n := by
          refine sum_le_sum fun n hn => ?_
          have hn := (mem_filter.mp hn).2
          rw [← Real.log_sqrt (by linarith)]
          exact Real.log_le_log hsqrt0 hn.le
      _ ≤ ∑ n ∈ S, Real.log n :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n _ _ =>
            Real.log_natCast_nonneg n
  have hA := sum_log_smooth_le x y
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hkey : (Sbig.card : ℝ) * Real.log x ≤ 2 * x * (Real.log y + c₀) := by
    have := mul_le_mul_of_nonneg_left hM hx0
    linarith
  have hSbig : (Sbig.card : ℝ) ≤ 2 * x * (Real.log y + c₀) / Real.log x := by
    rw [le_div_iff₀ hlogx]
    exact hkey
  show (S.card : ℝ) ≤ _
  linarith

end HubRemoval
