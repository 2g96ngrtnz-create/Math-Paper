import HubRemoval.Divisor
open HubRemoval

/-! ### Lemma 2.5: axioms -/

#print axioms succ_le_const_mul_two_rpow
#print axioms succ_le_rpow_of_large
#print axioms rpow_eq_prod_primeFactors
#print axioms divisor_bound

/-! ### Concrete values -/

#guard (Nat.divisors 12).card = 6
#guard (Nat.divisors 720720).card = 240   -- 720720 = 2⁴·3²·5·7·11·13, τ = 5·3·2·2·2·2

/-- Lemma 2.5 with `ε = 1/2`: `τ(n) ≤ C √n`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) :=
  divisor_bound (by norm_num)

/-- A constant is needed: `τ(12) = 6 > √12`, so `C = 1` fails for `ε = 1/2`. -/
example : (12 : ℝ) ^ (1 / 2 : ℝ) < (Nat.divisors 12).card := by
  rw [show (Nat.divisors 12).card = 6 by decide, ← Real.sqrt_eq_rpow]
  have : Real.sqrt 12 < 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  push_cast
  linarith

/-- The large-prime case with `ε = 1` and `p = 2 ≥ 2^{1/1}`: `a + 1 ≤ 2^a`. -/
example (a : ℕ) : (a : ℝ) + 1 ≤ ((2 : ℕ) : ℝ) ^ ((a : ℝ) * 1) :=
  succ_le_rpow_of_large (ε := 1) (by norm_num) (by norm_num) a
