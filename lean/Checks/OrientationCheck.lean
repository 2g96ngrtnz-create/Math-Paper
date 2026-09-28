import HubRemoval.Orientation
open HubRemoval Finset

/-! ### The orientation model: axioms -/

#print axioms mem_edges
#print axioms arc_adj
#print axioms arc_of_edge
#print axioms bit_congr
#print axioms PhiK_le_psi
#print axioms PhiK_le_max
#print axioms card_le_PhiK

/-! ### `G_{4,0}`: four edges, sixteen outcomes -/

#guard edges 4 0 = {(1, 2), (1, 3), (1, 4), (2, 4)}
#guard edges 12 1 = {(2, 4), (2, 6), (2, 8), (2, 10), (2, 12), (3, 6), (3, 9), (3, 12),
  (4, 8), (4, 12), (5, 10), (6, 12)}
#guard Fintype.card (Edge 4 0 → Bool) = 16

/-- Reverse `(1, 2)` and `(2, 4)`; `(1, 3)` and `(1, 4)` keep the default orientation. -/
def ω₀ : Edge 4 0 → Bool := fun e => decide (e.val = (1, 2) ∨ e.val = (2, 4))

/-- The directed cycle `1 → 2 → 4 → 1`. -/
theorem cyc12 : arc ω₀ 1 2 := by unfold arc bit ω₀; decide
theorem cyc24 : arc ω₀ 2 4 := by unfold arc bit ω₀; decide
theorem cyc41 : arc ω₀ 4 1 := by unfold arc bit ω₀; decide

/-- `3` is a sink: the edge `(1, 3)` points `3 → 1`, and there is no arc into `3`. -/
example : arc ω₀ 3 1 ∧ ¬ arc ω₀ 1 3 := by unfold arc bit ω₀; decide

/-- So `Φ₀(ω₀) ≥ 3`, and Proposition 3.2 gives `Φ₀(ω₀) ≤ Ψ(4, 4) ≤ 4`. -/
example : 3 ≤ PhiK 4 0 ω₀ ∧ PhiK 4 0 ω₀ ≤ 4 := by
  refine ⟨?_, ?_⟩
  · have h := card_le_PhiK (ω := ω₀) (S := {1, 2, 4}) (by decide) ?_
    · simpa using h
    have r12 := Relation.ReflTransGen.single cyc12
    have r24 := Relation.ReflTransGen.single cyc24
    have r41 := Relation.ReflTransGen.single cyc41
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact Relation.ReflTransGen.refl
      | exact r12 | exact r24 | exact r41
      | exact r12.trans r24 | exact r24.trans r41 | exact r41.trans r12
  · have h := PhiK_le_psi (N := 4) (K := 0) ω₀
    have hpsi := psi_le_self 4 (4 / (0 + 1))
    omega
