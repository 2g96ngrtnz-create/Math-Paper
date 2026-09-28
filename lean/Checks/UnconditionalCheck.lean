import HubRemoval.Unconditional
open HubRemoval Finset

/-! ### Unconditional Lemma 4.5(d) and Proposition 4.6: axioms -/

#print axioms CoreHyp.two_le_Y
#print axioms CoreHyp.mertens_instance
#print axioms core_d'
#print axioms lower_bound_err'
#print axioms fixedN_sandwich'

/-! ### Applied: `𝒟_{1/2}(2¹⁶, 10)`, with no Mertens input

`N = 2¹⁶`, `K = 10`, `η = 1/2`, `δ = 1/16`, `s₀ = 1`, `ρ = 1/2`. The helper lemmas are repeated
from `Checks/CoreDCheck.lean`. -/

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

/-- `Y = 8192/11 ≥ 2`. -/
example : 2 ≤ coreY 65536 10 (1 / 16) := hyp.two_le_Y

/-- Lemma 4.5(d), unconditional. -/
example := core_d' hyp

/-- Proposition 4.6 with Lemma 4.1, unconditional. -/
example := fixedN_sandwich' hyp (ρ := 1 / 2) (by norm_num) (by norm_num)
