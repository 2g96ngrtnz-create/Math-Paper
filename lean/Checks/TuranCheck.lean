import HubRemoval.Turan
open HubRemoval Finset

/-! ### Lemma 2.4: axioms -/

#print axioms sum_omegaZ
#print axioms sum_omegaZ_ge
#print axioms count_two_dvd_le
#print axioms sum_omegaZ_sq_le
#print axioms turan_variance
#print axioms turan_count

/-! ### Exact evaluation over `ℚ` (same definitions)

`N = 100`, `z = 7`: the primes are `2, 3, 5, 7` and `L = 1/2 + 1/3 + 1/5 + 1/7 = 247/210`. -/

#guard primesUpTo 7 = {2, 3, 5, 7}
#guard omegaZ 7 210 = 4
#guard omegaZ 7 11 = 0
#guard omegaZ 7 60 = 3
#guard (Lz 7 : ℚ) = 247 / 210

/-- The variance sum `∑_{m ≤ 100} (ω₇(m) − L)²`, computed exactly. -/
def varSum (z N : ℕ) : ℚ := ∑ m ∈ Ioc 0 N, ((omegaZ z m : ℚ) - Lz z) ^ 2

#eval varSum 7 100                 -- 154601/2205 ≈ 70.1
#eval (3 * 100 * Lz 7 : ℚ)         -- the bound 3NL = 2470/7 ≈ 352.9
#guard varSum 7 100 ≤ 3 * 100 * Lz 7

/-! `S₁ = ∑ ω_z(m) = ∑_p ⌊N/p⌋ = 50 + 33 + 20 + 14 = 117`. -/
#guard (∑ m ∈ Ioc 0 100, omegaZ 7 m) = 117

/-! The numbers `≤ 100` with `ω₇(m) = 0` are `1` and the primes from `11` to `97`: `22` of them.
`s = 1/2 ≤ L/2`, and the bound is `12 · 100 / L ≈ 1020`. -/
#guard ((Ioc 0 100).filter (fun m => omegaZ 7 m = 0)).card = 22

/-! ### The theorems, applied -/

example : ∑ m ∈ Ioc 0 100, ((omegaZ 7 m : ℝ) - Lz 7) ^ 2 ≤ 3 * (100 : ℝ) * Lz 7 :=
  turan_variance (by norm_num)

example : (((Ioc 0 100).filter (fun m => (omegaZ 7 m : ℝ) < 1 / 2)).card : ℝ) ≤
    12 * (100 : ℝ) / Lz 7 := by
  refine turan_count (by norm_num) (by norm_num) ?_
  have h : (Lz 7 : ℝ) = 247 / 210 := by
    rw [Lz, show primesUpTo 7 = {2, 3, 5, 7} by decide]
    norm_num
  rw [h]
  norm_num
