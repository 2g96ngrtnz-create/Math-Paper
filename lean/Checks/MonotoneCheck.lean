import HubRemoval.Monotone
open HubRemoval

/-! ### Lemma 6.1: axioms -/

#print axioms StronglyConnectedIn.mono
#print axioms card_le_maxSCC
#print axioms exists_card_eq_maxSCC
#print axioms maxSCC_mono
#print axioms maxSCC_Ioc_antitone

/-! ### A concrete example (non-vacuity)

`D` is the directed 3-cycle `1 → 2 → 3 → 1`. On `V = {1, 2, 3}` the whole cycle is strongly
connected, so `#Φ(D[V]) ≥ 3`. On `U = {1, 2}` only the arc `1 → 2` survives, so `{1, 2}` is **not**
strongly connected in `D[U]`. Paths must stay inside the induced subgraph, and the inequality of
Lemma 6.1 can be strict. -/

def cyc (a b : ℕ) : Prop := (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 1)

theorem cyc_full : StronglyConnectedIn cyc {1, 2, 3} {1, 2, 3} := by
  have e12 : inducedArc cyc {1, 2, 3} 1 2 := ⟨by simp, by simp, Or.inl ⟨rfl, rfl⟩⟩
  have e23 : inducedArc cyc {1, 2, 3} 2 3 := ⟨by simp, by simp, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have e31 : inducedArc cyc {1, 2, 3} 3 1 := ⟨by simp, by simp, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have r12 := Relation.ReflTransGen.single e12
  have r23 := Relation.ReflTransGen.single e23
  have r31 := Relation.ReflTransGen.single e31
  refine ⟨subset_rfl, fun a ha b hb => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact Relation.ReflTransGen.refl
    | exact r12 | exact r23 | exact r31
    | exact r12.trans r23 | exact r23.trans r31 | exact r31.trans r12

example : 3 ≤ maxSCC cyc {1, 2, 3} := card_le_maxSCC cyc_full

/-- In `D[{1, 2}]` nothing leaves `2`, so every path from `2` ends at `2`. -/
theorem cyc_sub_stuck {b : ℕ} (h : Relation.ReflTransGen (inducedArc cyc {1, 2}) 2 b) : b = 2 := by
  induction h with
  | refl => rfl
  | tail _ hcd ih =>
    obtain ⟨_, hd, hcd⟩ := hcd
    subst ih
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hcd with ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ <;> omega

example : ¬ StronglyConnectedIn cyc {1, 2} {1, 2} := fun h =>
  absurd (cyc_sub_stuck (h.2 2 (by simp) 1 (by simp))) (by decide)

example : maxSCC cyc {1, 2} ≤ maxSCC cyc {1, 2, 3} := maxSCC_mono cyc (by decide)

/-- Hub removal with `N = 3`: `Φ_1 ≤ Φ_0` for the 3-cycle. -/
example : maxSCC cyc (Finset.Ioc 1 3) ≤ maxSCC cyc (Finset.Ioc 0 3) :=
  maxSCC_Ioc_antitone cyc 3 (by norm_num)
