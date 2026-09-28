import HubRemoval.Attach
open HubRemoval Finset

/-! ### Lemma 4.4: axioms -/

#print axioms attach_mutual
#print axioms sum_weight
#print axioms not_attachEvent_iff
#print axioms prob_attach
#print axioms prob_attach_ge

/-! ### Brute force over `ℚ` (the same definitions)

For `s = 3` and `ρ = 1/3`, enumerate all `2³ = 8` orientations. The weights sum to `1`, the six
non-constant orientations form `A_m`, and their weight is `1 − 1/27 − 8/27 = 2/3`. -/

#eval (univ.filter (attachEvent (s := 3))).card                          -- 6
#eval ∑ ω : Fin 3 → Bool, weight (1 / 3 : ℚ) ω                           -- 1
#eval ∑ ω ∈ univ.filter (attachEvent (s := 3)), weight (1 / 3 : ℚ) ω    -- 2/3

#guard (univ.filter (attachEvent (s := 3))).card = 6
#guard ∑ ω ∈ univ.filter (attachEvent (s := 3)), weight (1 / 3 : ℚ) ω =
  1 - (1 / 3) ^ 3 - (2 / 3) ^ 3
#guard ∑ ω ∈ univ.filter (attachEvent (s := 5)), weight (1 / 4 : ℚ) ω =
  1 - (1 / 4) ^ 5 - (3 / 4) ^ 5

/-- `s = 1` is the edge case: one edge can never point both ways, so `P(A_m) = 0`. -/
example (ρ : ℝ) : ∑ ω ∈ univ.filter (attachEvent (s := 1)), weight ρ ω = 0 := by
  rw [prob_attach ρ le_rfl]
  ring

/-! For `s = 0` the hypothesis `s ≥ 1` is needed: `A_m` is empty, while the formula gives `−1`. -/

#guard ∑ ω ∈ univ.filter (attachEvent (s := 0)), weight (1 / 2 : ℚ) ω = 0
#guard (1 - (1 / 2) ^ 0 - (1 / 2) ^ 0 : ℚ) = -1

/-- The bound, applied: for `ρ = 1/3` and `s = 3`, `P(A_m) ≥ 1 − 2(2/3)³ = 11/27`. -/
example : 1 - 2 * (2 / 3 : ℝ) ^ 3 ≤
    ∑ ω ∈ univ.filter (attachEvent (s := 3)), weight (1 / 3 : ℝ) ω := by
  have h := prob_attach_ge (ρ := 1 / 3) (by norm_num) (by norm_num) (s := 3) (by norm_num)
  rwa [show max (1 / 3 : ℝ) (1 - 1 / 3) = 2 / 3 by norm_num] at h

/-! ### The deterministic part, applied

`N = 48`, `K = 1`, `M = 24`, `D = Adj` of `G_{48,1}` (symmetric, so `𝓡` holds; see
`Checks/SigmaCheck.lean`). Take `m = 30` and `d = 3`, `d' = 5`, both in `S_M` and both dividing
`30`. Then `m` joins the SCC of `3`. -/

theorem robust_adj48 : RobustEvent (divGraph 48 1).Adj 48 1 24 := by
  intro x x' hKx hxx' hx'M hdvd
  have h2 : 2 * x' ≤ 48 := by
    have : (x' : ℝ) ≤ 24 := hx'M
    exact_mod_cast (show (2 * x' : ℝ) ≤ 48 by linarith)
  have hy : x' ∣ 2 * x' := Dvd.intro_left 2 rfl
  have e1 : (divGraph 48 1).Adj x (2 * x') :=
    ⟨by omega, hKx, by omega, by omega, h2, Or.inl (hdvd.trans hy)⟩
  have e2 : (divGraph 48 1).Adj (2 * x') x' :=
    ⟨by omega, by omega, h2, by omega, by omega, Or.inr hy⟩
  exact ⟨⟨2 * x', by omega, h2, hy, e1, e2⟩, ⟨2 * x', by omega, h2, hy, e2.symm, e1.symm⟩⟩

theorem goodSet24_3 : goodSet 24 1 3 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd]
  norm_num

theorem goodSet24_5 : goodSet 24 1 5 := by
  refine ⟨by norm_num, by norm_num, fun p hp hpd => ?_⟩
  rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpd]
  norm_num

example : MutuallyReachable (divGraph 48 1).Adj 30 3 :=
  attach_mutual (by norm_num) robust_adj48 goodSet24_3 goodSet24_5
    (by unfold divGraph; decide) (by unfold divGraph; decide)
