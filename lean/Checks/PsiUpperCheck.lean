import HubRemoval.PsiUpper
open HubRemoval Finset

/-! ### Lemma 2.3: axioms -/

#print axioms log_eq_sum_primesUpTo
#print axioms sum_factorization_le
#print axioms sum_log_smooth_le
#print axioms psi_upper

/-! ### Legendre's theorem, evaluated

`∑_{n ≤ 100} v_2(n) = v_2(100!) = 50 + 25 + 12 + 6 + 3 + 1 = 97 ≤ 100/(2 − 1)`, and
`∑_{n ≤ 100} v_3(n) = 33 + 11 + 3 + 1 = 48 ≤ 100/2`. -/

#guard (∑ n ∈ Ico 1 101, n.factorization 2) = 97
#guard (Nat.factorial 100).factorization 2 = 97
#guard (∑ n ∈ Ico 1 101, n.factorization 3) = 48
#guard 2 * 48 ≤ 100

/-! ### Applying the lemma (non-vacuity)

For `y = 2` the Mertens sum is `log 2 / (2 − 1) = log 2`, so the hypothesis holds with
`c₀ = 0`. Then `Ψ(100, 2) ≤ 10 + 200 log 2 / log 100 ≈ 40.1`. The true value is `Ψ(100, 2) = 7`,
counting `1, 2, 4, …, 64`. -/

#guard psi 100 2 = 7

example : (psi 100 2 : ℝ) ≤ Real.sqrt 100 + 2 * 100 * (Real.log 2 + 0) / Real.log 100 := by
  have h := psi_upper (x := 100) (y := 2) (c₀ := 0) (by norm_num) (by
    rw [show primesUpTo 2 = {2} by decide, sum_singleton]
    norm_num)
  push_cast at h
  exact h
