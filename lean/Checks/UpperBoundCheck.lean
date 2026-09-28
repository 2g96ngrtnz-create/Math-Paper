import HubRemoval.UpperBound
open HubRemoval

/-! ### Proposition 3.2: axioms -/

#print axioms reachable_of_reflTransGen
#print axioms stronglyConnected_subset_fibre
#print axioms stronglyConnected_card_le_psi
#print axioms stronglyConnected_card_le_max

/-! ### A concrete application (non-vacuity)

`N = 12`, `K = 1`, so `B = 12 / 2 = 6`. Take the digraph with both arc directions on every edge,
`D = Adj`. The set `{2, 4}` is strongly connected, since `2 ∣ 4` is an edge. The proposition then
bounds it by `Ψ(12, 6)`. -/

#eval psi 12 6   -- 10: the 6-smooth numbers up to 12 are 1,2,3,4,5,6,8,9,10,12

example : ({2, 4} : Finset ℕ).card ≤ psi 12 (12 / (1 + 1)) := by
  have hadj : (divGraph 12 1).Adj 2 4 :=
    ⟨by decide, by decide, by decide, by decide, by decide, Or.inl ⟨2, rfl⟩⟩
  refine stronglyConnected_card_le_psi (D := (divGraph 12 1).Adj) (fun _ _ h => h) ?_ ?_
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [vertices, Finset.mem_Ioc]
    omega
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single hadj
    · exact Relation.ReflTransGen.single hadj.symm
    · exact Relation.ReflTransGen.refl
