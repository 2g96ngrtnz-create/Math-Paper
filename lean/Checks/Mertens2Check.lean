import HubRemoval.Mertens2
open HubRemoval Finset

/-! ### Lemma 2.1(b)–(d): axioms -/

#print axioms sub_one_mul_factorization_factorial_le
#print axioms log_factorial_ge
#print axioms Smert_ge
#print axioms abs_Smert_sub_log_le
#print axioms Smert_succ
#print axioms abel_sum
#print axioms sum_Ioc_tel
#print axioms abel_err_le
#print axioms sum_inv_primes_eq
#print axioms main_term_bounds
#print axioms sum_inv_sq_le
#print axioms mertens_b_nat
#print axioms loglog_floor
#print axioms mertens_b
#print axioms mertens_c
#print axioms mertens_d
#print axioms mertens_a_real
#print axioms lemma_2_1

/-! ### The lemmas, applied -/

/-- (b) on `(10, 1000]`. -/
example : |∑ p ∈ (primesUpTo ⌊(1000 : ℝ)⌋₊).filter (fun p : ℕ => (10 : ℝ) < p), (1 : ℝ) / p -
    Real.log (Real.log 1000 / Real.log 10)| ≤ 18 / Real.log 10 :=
  mertens_b (by norm_num) (by norm_num)

/-- (c) at `z = 100`. -/
example : Real.log (Real.log 100) - 13 ≤ ∑ p ∈ primesUpTo ⌊(100 : ℝ)⌋₊, (1 : ℝ) / p :=
  mertens_c (by norm_num)

/-- (d) at `x = 100`: `π(100) = 25 ≤ 500/log 100 ≈ 108.6`. -/
example : ((primesUpTo ⌊(100 : ℝ)⌋₊).card : ℝ) ≤ 5 * 100 / Real.log 100 :=
  mertens_d (by norm_num)

#guard (primesUpTo 100).card = 25

/-- Mertens' first theorem at `n = 1000`. -/
example : |Smert 1000 - Real.log 1000| ≤ 3 := by
  simpa using abs_Smert_sub_log_le 1000 (by norm_num)

/-- The Abel identity on a toy example: `E k = k`, `f k = 1`, `y = 0`, `w = 3`. -/
example : ∑ k ∈ Ioc (0 : ℕ) 3, ((k : ℝ) - ((k - 1 : ℕ) : ℝ)) * 1 =
    3 * 1 - 0 * 1 + ∑ k ∈ Ioc (0 : ℕ) 3, ((k - 1 : ℕ) : ℝ) * (1 - 1) := by
  simpa using abel_sum (fun k => (k : ℝ)) (fun _ => (1 : ℝ)) (Nat.zero_le 3)

/-! ### Floating-point sanity check of the constants (numerics, not a proof)

At `n = 10⁴`, `S(n) − log n ≈ −1.32` (the limit is `−1.33`), well inside `[−3, 3]`. The error
in (b) on `(10, 10⁴]` is about `−0.08`, far inside `±8/log 10 ≈ ±3.5`. -/

def primesF (n : ℕ) : List ℕ := (List.range (n + 1)).filter Nat.Prime

#eval
  let n := 10000
  let S := ((primesF n).map fun p => Float.log p.toFloat / p.toFloat).foldl (· + ·) 0
  S - Float.log n.toFloat                         -- ≈ -1.32

#eval
  let y := 10
  let w := 10000
  let s := (((primesF w).filter (y < ·)).map fun p => 1 / p.toFloat).foldl (· + ·) 0
  s - Float.log (Float.log w.toFloat / Float.log y.toFloat)   -- ≈ -0.08
