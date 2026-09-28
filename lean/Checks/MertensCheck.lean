import HubRemoval.Mertens
open HubRemoval Finset

/-! ### Lemma 2.1(a): axioms -/

#print axioms theta_le
#print axioms div_le_factorization_factorial
#print axioms factorial_mem_smoothNumbers
#print axioms sum_log_div_le
#print axioms log_div_le_tel
#print axioms sum_tel_le
#print axioms sum_log_div_mul_le
#print axioms mertens_a
#print axioms psi_upper'

/-! ### Legendre, evaluated

`v₂(10!) = 5 + 2 + 1 = 8 ≥ ⌊10/2⌋ = 5`, and `v₇(10!) = 1 = ⌊10/7⌋`. -/

#guard (Nat.factorial 10).factorization 2 = 8
#guard (Nat.factorial 10).factorization 7 = 1
example : 10 / 7 ≤ (Nat.factorial 10).factorization 7 :=
  div_le_factorization_factorial (by norm_num) (by norm_num)

/-! ### Chebyshev, applied: `θ(10) = log(2·3·5·7) = log 210 ≤ 10 log 4`. -/

#guard primesUpTo 10 = {2, 3, 5, 7}
example : ∑ p ∈ primesUpTo 10, Real.log p ≤ 10 * Real.log 4 := by
  simpa using theta_le 10

/-! ### Mertens (a) and the unconditional Lemma 2.3, applied -/

example : ∑ p ∈ primesUpTo 100, Real.log p / ((p : ℝ) - 1) ≤
    Real.log 100 + (Real.log 4 + 2) := by
  simpa using mertens_a 100 (by norm_num)

/-- `Ψ(100, 10) ≤ 10 + 200 (log 10 + log 4 + 2)/log 100` (about 76.7). The true value is 46. -/
example : (psi 100 10 : ℝ) ≤
    Real.sqrt 100 + 2 * 100 * (Real.log 10 + (Real.log 4 + 2)) / Real.log 100 := by
  simpa using psi_upper' (x := 100) (y := 10) (by norm_num) (by norm_num)

#guard psi 100 10 = 46
