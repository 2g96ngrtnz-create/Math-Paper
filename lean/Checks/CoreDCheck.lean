import HubRemoval.CoreD
open HubRemoval Finset

/-! ### Lemma 4.5(d): axioms -/

#print axioms coreY_pos
#print axioms CoreHyp.log_Y_ge
#print axioms CoreHyp.log_B_sub_log_Y
#print axioms core_d

/-! ### Non-vacuity: the Mertens hypothesis `hMb` holds in a concrete case

`N = 2¹⁶`, `K = 10`, `η = 1/2`, `δ = 1/16`, `s₀ = 1` (as in `Checks/CoreParamsCheck.lean`). Then
`Y = 2¹⁴/22 = 8192/11 ≈ 744.7` and `B = ⌊65536/11⌋ = 5957`. Every prime in `(Y, B]` has
`1/p < 11/8192`, and there are fewer than `5957` of them, so the sum is `< 8`. Since
`log Y < 13 log 2 < 9.1`, the hypothesis holds with `C₁ = 100`. -/

theorem N_rpow (a : ℝ) : (65536 : ℝ) ^ a = (2 : ℝ) ^ (16 * a) := by
  rw [Real.rpow_mul (by norm_num), show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  norm_num

theorem two_rpow_nat (n : ℕ) : (2 : ℝ) ^ (n : ℝ) = 2 ^ n := Real.rpow_natCast 2 n

theorem hyp : CoreHyp 65536 10 1 (1 / 2) (1 / 16) where
  η_pos := by norm_num
  η_lt_one := by norm_num
  s₀_pos := le_rfl
  δ_pos := by norm_num
  δ_le := by norm_num
  H1 := by
    push_cast
    rw [N_rpow, show 16 * (1 - 1 / 2 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  H2 := by
    push_cast
    rw [N_rpow, show 16 * (1 / 2 / 4 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num
  H3 := by
    push_cast
    rw [N_rpow, show 16 * (1 / 16 / 1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, two_rpow_nat]
    norm_num

theorem Y_eq : coreY 65536 10 (1 / 16) = 8192 / 11 := by
  unfold coreY
  push_cast
  rw [N_rpow, show 16 * (1 - 2 * (1 / 16) : ℝ) = ((14 : ℕ) : ℝ) by norm_num, two_rpow_nat]
  norm_num

#guard 65536 / (10 + 1) = 5957

theorem hMb_example : coreY 65536 10 (1 / 16) < ((65536 / (10 + 1) : ℕ) : ℝ) →
    ∑ p ∈ (primesUpTo (65536 / (10 + 1))).filter (fun p : ℕ => coreY 65536 10 (1 / 16) < p),
      (1 : ℝ) / p ≤
      Real.log (Real.log ((65536 / (10 + 1) : ℕ) : ℝ) / Real.log (coreY 65536 10 (1 / 16))) +
        100 / Real.log (coreY 65536 10 (1 / 16)) := by
  intro hYB
  rw [Y_eq] at hYB ⊢
  rw [show 65536 / (10 + 1) = 5957 by norm_num] at hYB ⊢
  set P := (primesUpTo 5957).filter (fun p : ℕ => (8192 / 11 : ℝ) < p)
  -- The sum is at most `5957 · 11/8192 < 8`.
  have hterm : ∀ p ∈ P, (1 : ℝ) / p ≤ 11 / 8192 := fun p hp => by
    have h := (mem_filter.mp hp).2
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hcard : (P.card : ℝ) ≤ 5957 := by
    have h1 : P.card ≤ (primesUpTo 5957).card := card_le_card (filter_subset _ _)
    exact_mod_cast h1.trans (card_primesUpTo_le 5957)
  have hsum : ∑ p ∈ P, (1 : ℝ) / p ≤ 8 :=
    calc ∑ p ∈ P, (1 : ℝ) / p ≤ ∑ _p ∈ P, (11 / 8192 : ℝ) := sum_le_sum hterm
      _ = P.card * (11 / 8192) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 5957 * (11 / 8192) := by nlinarith
      _ ≤ 8 := by norm_num
  -- `0 < log Y < 9.1`, and `log B ≥ log Y`.
  have hlogY : 0 < Real.log (8192 / 11 : ℝ) := Real.log_pos (by norm_num)
  have hlogY9 : Real.log (8192 / 11 : ℝ) ≤ 9.1 := by
    have h1 : Real.log (8192 / 11 : ℝ) ≤ Real.log 8192 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
      rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
      norm_num
    have h3 := Real.log_two_lt_d9
    linarith
  have hratio : 0 ≤ Real.log (Real.log ((5957 : ℕ) : ℝ) / Real.log (8192 / 11 : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hlogY, one_mul]
    exact Real.log_le_log (by norm_num) hYB.le
  have hC : (8 : ℝ) ≤ 100 / Real.log (8192 / 11 : ℝ) := by
    rw [le_div_iff₀ hlogY]
    linarith
  linarith

open Classical in
/-- Lemma 4.5(d), applied: the exceptional set of `F₁` for `N = 2¹⁶`, `K = 10`. -/
example : (((smoothFibre 65536 10).filter (fun m => ¬ InU 65536 10 1 (1 / 16) m)).card : ℝ) ≤
    ((65536 : ℕ) : ℝ) ^ (1 - 1 / 16 : ℝ) +
      (65536 : ℕ) * (4 * (1 / 16) / (1 / 2) + 2 * (1 + 100) / (1 / 2 * Real.log (65536 : ℕ))) +
      ((Ioc 0 65536).filter
        (fun m => omegaZ ⌊((65536 : ℕ) : ℝ) ^ ((1 / 16 : ℝ) / ((1 : ℕ) : ℝ))⌋₊ m < 1)).card :=
  core_d hyp (by norm_num) hMb_example
