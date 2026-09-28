import HubRemoval.Robust
open HubRemoval

/-! ### Lemma 4.1: axioms -/

#print axioms robust_pair
#print axioms robust_adj
#print axioms robust_reachable
#print axioms card_multiples_Ioc
#print axioms card_multiples_Ioc_ge

/-! ### The witness count

For `x' = 3` and `N = 12`, `𝒴 = {6, 9, 12}` has `⌊12/3⌋ − 1 = 3` elements. -/

#guard ((Finset.Ioc 3 12).filter (3 ∣ ·)) = {6, 9, 12}
example : ((Finset.Ioc 3 12).filter (3 ∣ ·)).card = 12 / 3 - 1 := card_multiples_Ioc 12 (by norm_num)

/-! ### A genuine orientation on which `𝓡` holds (non-vacuity)

`N = 12`, `K = 1`, `M = 4`. Every edge of `G_{12,1}` has its default orientation, from the larger
end to the smaller, except the two edges `{2, 8}` and `{4, 12}`, which are reversed. The only
divisibility pair `1 < x < x' ≤ 4` is `(2, 4)`, with witnesses `2 → 8 → 4` and `4 → 12 → 2`. So
`𝓡` holds, and Lemma 4.1 puts `2` and `4` in one SCC. -/

/-- The reversed edges, written as `(smaller, larger)`. -/
def rev (a b : ℕ) : Prop := (a = 2 ∧ b = 8) ∨ (a = 4 ∧ b = 12)

/-- The orientation: exactly one direction of every edge of `G_{12,1}`. -/
def D (a b : ℕ) : Prop := (divGraph 12 1).Adj a b ∧ (if a < b then rev a b else ¬ rev b a)

/-- `D` is an orientation: each edge gets exactly one direction. -/
example (a b : ℕ) (h : (divGraph 12 1).Adj a b) : D a b ↔ ¬ D b a := by
  have hab : a ≠ b := h.1
  unfold D
  simp only [h, h.symm, true_and]
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · simp [hlt, Nat.lt_asymm hlt]
  · simp [hlt, Nat.lt_asymm hlt]

theorem D_2_8 : D 2 8 := ⟨by unfold divGraph; decide, by unfold rev; decide⟩
theorem D_8_4 : D 8 4 := ⟨by unfold divGraph; decide, by unfold rev; decide⟩
theorem D_4_12 : D 4 12 := ⟨by unfold divGraph; decide, by unfold rev; decide⟩
theorem D_12_2 : D 12 2 := ⟨by unfold divGraph; decide, by unfold rev; decide⟩

/-- Without the reversals the default orientation has no arc from `2` to `8`. -/
example : ¬ D 8 2 := fun h => by
  have := h.2
  unfold rev at this
  simp at this

theorem robust_example : RobustEvent D 12 1 4 := by
  intro x x' hx hxx' hx'M hdvd
  have hx'4 : x' ≤ 4 := by exact_mod_cast hx'M
  interval_cases x' <;> interval_cases x <;> norm_num at hdvd
  exact ⟨⟨8, by norm_num, by norm_num, by norm_num, D_2_8, D_8_4⟩,
    ⟨12, by norm_num, by norm_num, by norm_num, D_4_12, D_12_2⟩⟩

example : MutuallyReachable D 2 4 := by
  have hadj : (divGraph ⌊(4 : ℝ)⌋₊ 1).Adj 2 4 := by
    rw [show ⌊(4 : ℝ)⌋₊ = 4 by norm_num]
    unfold divGraph
    decide
  exact robust_adj robust_example hadj
