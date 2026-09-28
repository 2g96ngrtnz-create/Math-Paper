import HubRemoval.RobustProb
open HubRemoval Finset

/-! ### Lemma 4.1, probability bound: axioms -/

#print axioms prob_pat
#print axioms prob_no_pat
#print axioms two_mul_card_edges_le
#print axioms exists_bad_pair
#print axioms prob_not_robust
#print axioms prob_not_robust_exp

/-! ### The pair count

`G_{12,1}` has 12 edges, and `2 · 12 = 24 ≤ 12² = 144`. `G_{100,0}` has 382 edges. -/

#guard (edges 12 1).card = 12
#guard 2 * (edges 100 0).card ≤ 100 ^ 2
#eval (edges 100 0).card   -- 382

/-! ### A two-edge cylinder

In `G_{12,1}`, `P(2 → 6 → 3) = P((2,6) reversed, (3,6) not) = ρ(1 − ρ)`. -/

example (ρ : ℝ) : prob ρ (pat (N := 12) (K := 1) 2 3 6) = ρ * (1 - ρ) :=
  prob_pat ρ (by decide) (by decide) (by decide)

/-- For the pair `(2, 4)` in `G_{12,1}` the witnesses `y ∈ {8, 12}` are independent:
`P(no 2 → y → 4) = (1 − ρ(1 − ρ))²`. -/
example (ρ : ℝ) : prob ρ (fun ω : Edge 12 1 → Bool => ∀ y ∈ ({8, 12} : Finset ℕ), ¬ pat 2 4 y ω) =
    (1 - ρ * (1 - ρ)) ^ 2 :=
  prob_no_pat ρ (by decide) {8, 12} (by decide)

/-! ### Lemma 4.1, applied

In `𝒟_{1/2}(400, 1)` with `M = 4`: `q = 1/4`, `N/M − 2 = 98`, and
`P(𝓡ᶜ) ≤ 16 · (3/4)^98 < 10⁻¹⁰`. -/

example : prob (1 / 2) (fun ω : Edge 400 1 → Bool => ¬ RobustEvent (arc ω) 400 1 4) <
    1 / 10 ^ 10 := by
  refine lt_of_le_of_lt (prob_not_robust (by norm_num) (by norm_num) (by norm_num)) ?_
  rw [show ((400 : ℕ) : ℝ) / 4 - 2 = ((98 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num
