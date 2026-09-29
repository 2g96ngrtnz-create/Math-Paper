import HubRemoval.LowerBound
open HubRemoval Finset

/-! ### Proposition 4.6: axioms -/

#print axioms card_attached_le_PhiK
#print axioms card_coreU_ge
#print axioms card_coreU_le
#print axioms lower_bound
#print axioms lower_bound_err
#print axioms expect_PhiK_le_psi
#print axioms CoreHyp.N_div_M
#print axioms fixedN_sandwich

/-! ### Applied: `𝒟_{1/2}(2¹⁶, 10)`

`N = 2¹⁶`, `K = 10`, `η = 1/2`, `δ = 1/16`, `s₀ = 1`, `ρ = 1/2`. The instance of Mertens' theorem
holds with `C₁ = 100` (proved below, as in `Checks/CoreDCheck.lean`). Proposition 4.6 and
Lemma 4.1 then give a two-sided bound on `E[Φ₁₀]`. The helper lemmas are repeated from
`Checks/CoreDCheck.lean`, because check files are not importable modules. -/

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

/-- Proposition 4.6, eq. (2), in `𝒟_{1/2}(2¹⁶, 10)` (no Mertens input needed). -/
example := lower_bound hyp (ρ := 1 / 2) (by norm_num) (by norm_num)

/-- The paper's form of Proposition 4.6, with the Mertens instance proved above. -/
example := lower_bound_err hyp (ρ := 1 / 2) (by norm_num) (by norm_num) (C₁ := 100) (by norm_num)
  hMb_example

/-- The two-sided bound for `N = 2¹⁶`, `K = 10`. -/
example := fixedN_sandwich hyp (ρ := 1 / 2) (by norm_num) (by norm_num) (C₁ := 100) (by norm_num)
  hMb_example

/-- The upper half, stated explicitly: `E[Φ₁₀] ≤ Ψ(2¹⁶, ⌊2¹⁶/11⌋)`. -/
example : expectP (1 / 2) (fun ω : Edge 65536 10 → Bool => (PhiK 65536 10 ω : ℝ)) ≤
    psi 65536 (65536 / (10 + 1)) :=
  expect_PhiK_le_psi (by norm_num) (by norm_num)
