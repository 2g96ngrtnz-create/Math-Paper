import Mathlib

/-!
# The divisor bound (paper, Lemma 2.6)

**Lemma 2.6.** For every `ε > 0` there is `C_ε` with `τ(n) ≤ C_ε n^ε` for all `n ≥ 1`.

The proof is the paper's. Write `τ(n)/n^ε = ∏_{p^a ∥ n} (a+1) p^{−aε}`.

* If `p ≥ 2^{1/ε}`, then `p^{aε} ≥ 2^a ≥ a + 1`, so the factor is `≤ 1`.
* For every prime `p`, the factor is `≤ c := max(1, 1/(ε log 2))`, because
  `p^{aε} ≥ 2^{aε} = e^{aε log 2} ≥ 1 + aε log 2`.

At most `⌈2^{1/ε}⌉` primes are `< 2^{1/ε}`, so `τ(n) ≤ c^{⌈2^{1/ε}⌉} n^ε`. The paper uses
`c_ε = sup_a (a+1) 2^{−aε}`; the explicit `c` above is an upper bound for it.
-/

namespace HubRemoval

open Finset

/-- `a + 1 ≤ c · 2^{aε}` with `c = max(1, 1/(ε log 2))`. -/
theorem succ_le_const_mul_two_rpow {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    (a : ℝ) + 1 ≤ max 1 (1 / (ε * Real.log 2)) * (2 : ℝ) ^ ((a : ℝ) * ε) := by
  have ht : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hexp : 1 + a * (ε * Real.log 2) ≤ (2 : ℝ) ^ ((a : ℝ) * ε) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 2 * (a * ε))
    have e : Real.log 2 * (a * ε) = a * (ε * Real.log 2) := by ring
    linarith
  have hpow : 0 ≤ (2 : ℝ) ^ ((a : ℝ) * ε) := by positivity
  rcases le_or_gt 1 (ε * Real.log 2) with h1 | h1
  · have hm : 1 ≤ max 1 (1 / (ε * Real.log 2)) := le_max_left _ _
    have h2 : (a : ℝ) + 1 ≤ 1 + a * (ε * Real.log 2) := by nlinarith
    nlinarith
  · have hm : 1 / (ε * Real.log 2) ≤ max 1 (1 / (ε * Real.log 2)) := le_max_right _ _
    have hinv : 1 ≤ 1 / (ε * Real.log 2) := by rw [le_div_iff₀ ht]; linarith
    have h2 : (a : ℝ) + 1 ≤ 1 / (ε * Real.log 2) * (1 + a * (ε * Real.log 2)) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm (1 / (ε * Real.log 2)) (a : ℝ), mul_assoc,
        one_div_mul_cancel ht.ne', mul_one]
      linarith
    calc (a : ℝ) + 1 ≤ 1 / (ε * Real.log 2) * (1 + a * (ε * Real.log 2)) := h2
      _ ≤ max 1 (1 / (ε * Real.log 2)) * (1 + a * (ε * Real.log 2)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
      _ ≤ max 1 (1 / (ε * Real.log 2)) * (2 : ℝ) ^ ((a : ℝ) * ε) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)

/-- For a large prime, `p ≥ 2^{1/ε}`, the factor is `≤ 1`: `a + 1 ≤ 2^a ≤ p^{aε}`. -/
theorem succ_le_rpow_of_large {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : (2 : ℝ) ^ (1 / ε) ≤ p)
    (a : ℕ) : (a : ℝ) + 1 ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
  have h1 : (2 : ℝ) ^ (a : ℝ) ≤ (p : ℝ) ^ ((a : ℝ) * ε) :=
    calc (2 : ℝ) ^ (a : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ((a : ℝ) * ε) := by
          rw [← Real.rpow_mul (by norm_num)]
          congr 1
          field_simp
      _ ≤ (p : ℝ) ^ ((a : ℝ) * ε) := Real.rpow_le_rpow (by positivity) hp (by positivity)
  have h2 : (a : ℝ) + 1 ≤ (2 : ℝ) ^ (a : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self : a < 2 ^ a)
  linarith

/-- `n^ε = ∏_{p^a ∥ n} p^{aε}`. -/
theorem rpow_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) (ε : ℝ) :
    (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  push_cast
  rw [← Real.finsetProd_rpow _ _ fun p _ => by positivity]
  refine prod_congr rfl fun p _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

/-- **Lemma 2.6, with the explicit constant.** For `ε > 0` and `n ≥ 1`,
`τ(n) ≤ C_ε n^ε` with `C_ε = max(1, 1/(ε log 2))^{⌈2^{1/ε}⌉}`. -/
theorem divisor_bound_explicit {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ≤
      max 1 (1 / (ε * Real.log 2)) ^ ⌈(2 : ℝ) ^ (1 / ε)⌉₊ * (n : ℝ) ^ ε := by
  classical
  set c := max 1 (1 / (ε * Real.log 2)) with hcdef
  set B := (2 : ℝ) ^ (1 / ε) with hBdef
  have hc1 : 1 ≤ c := le_max_left _ _
  have hc0 : 0 < c := by linarith
  rw [Nat.card_divisors hn, rpow_eq_prod_primeFactors hn]
  push_cast
  have hper : ∀ p ∈ n.primeFactors, (n.factorization p : ℝ) + 1 ≤
      (if (p : ℝ) < B then c else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hpB
    · calc (n.factorization p : ℝ) + 1
          ≤ c * (2 : ℝ) ^ ((n.factorization p : ℝ) * ε) := succ_le_const_mul_two_rpow hε _
        _ ≤ c * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) hp2 (by positivity))
              hc0.le
    · push Not at hpB
      rw [one_mul]
      exact succ_le_rpow_of_large hε hpB _
  have hweights : ∏ p ∈ n.primeFactors, (if (p : ℝ) < B then c else 1) ≤ c ^ ⌈B⌉₊ := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
    apply pow_le_pow_right₀ hc1
    have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) < B) ⊆ range ⌈B⌉₊ := by
      intro p hp
      have h1 := (mem_filter.mp hp).2
      have h2 : (p : ℝ) < ⌈B⌉₊ := lt_of_lt_of_le h1 (Nat.le_ceil B)
      exact mem_range.mpr (by exact_mod_cast h2)
    simpa using card_le_card hsub
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if (p : ℝ) < B then c else 1) * (p : ℝ) ^ ((n.factorization p : ℝ) * ε)) :=
        prod_le_prod₀ (fun p _ => by positivity) hper
    _ = (∏ p ∈ n.primeFactors, (if (p : ℝ) < B then c else 1)) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := prod_mul_distrib
    _ ≤ c ^ ⌈B⌉₊ * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right hweights (prod_nonneg fun p _ => by positivity)

/-- **Lemma 2.6.** `τ(n) ≤ C_ε n^ε` for all `n ≥ 1`, for some `C_ε > 0`
(`divisor_bound_explicit` gives `C_ε = max(1, 1/(ε log 2))^⌈2^{1/ε}⌉`). -/
theorem divisor_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε :=
  ⟨_, pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _,
    fun _ hn => divisor_bound_explicit hε hn⟩

end HubRemoval
