import HubRemoval.FibreCount

/-!
# The upper bound (paper, Proposition 3.2)

For **every** orientation of `G_{N,K}`, every strongly connected set of vertices lies in a single
fibre `V_n`. Hence it has at most `Ψ(N, B)` elements and at most `max(|F₁|, K)` elements. In
particular the largest SCC satisfies `Φ_K ≤ Ψ(N, B)` and `Φ_K ≤ max(|F₁|, K)`.

An orientation is modelled as a relation `D` on `ℕ` whose arcs are edges of `G_{N,K}`. A set `S`
is strongly connected in `D` if any two of its elements are joined by a directed path. This is a
path in the whole digraph, exactly as in the definition of an SCC.
-/

namespace HubRemoval

/-- A directed path along arcs of an orientation of `G_{N,K}` is an undirected path in
`G_{N,K}`. -/
theorem reachable_of_reflTransGen {N K : ℕ} {D : ℕ → ℕ → Prop}
    (hD : ∀ a b, D a b → (divGraph N K).Adj a b) {a b : ℕ}
    (h : Relation.ReflTransGen D a b) : (divGraph N K).Reachable a b := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans (hD _ _ hbc).reachable

/-- **Proposition 3.2, first part.** A strongly connected set of an orientation of `G_{N,K}`
lies in one fibre. -/
theorem stronglyConnected_subset_fibre {N K : ℕ} {D : ℕ → ℕ → Prop}
    (hD : ∀ a b, D a b → (divGraph N K).Adj a b) {S : Finset ℕ} (hS : S ⊆ vertices N K)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen D a b) {a : ℕ} (ha : a ∈ S) :
    S ⊆ fibre N K (roughPart (N / (K + 1)) a) := by
  intro b hb
  refine Finset.mem_filter.mpr ⟨hS hb, ?_⟩
  exact (roughPart_eq_of_reachable (reachable_of_reflTransGen hD (hconn a ha b hb))).symm

/-- **Proposition 3.2.** A strongly connected set of any orientation of `G_{N,K}` has at most
`Ψ(N, B)` elements, `B = ⌊N/(K+1)⌋`. -/
theorem stronglyConnected_card_le_psi {N K : ℕ} {D : ℕ → ℕ → Prop}
    (hD : ∀ a b, D a b → (divGraph N K).Adj a b) {S : Finset ℕ} (hS : S ⊆ vertices N K)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen D a b) :
    S.card ≤ psi N (N / (K + 1)) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  exact (Finset.card_le_card (stronglyConnected_subset_fibre hD hS hconn ha)).trans
    (card_fibre_le_psi _ _ _)

/-- **Proposition 3.2.** A strongly connected set of any orientation of `G_{N,K}` has at most
`max(|F₁|, K)` elements. -/
theorem stronglyConnected_card_le_max {N K : ℕ} {D : ℕ → ℕ → Prop}
    (hD : ∀ a b, D a b → (divGraph N K).Adj a b) {S : Finset ℕ} (hS : S ⊆ vertices N K)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen D a b) :
    S.card ≤ max (smoothFibre N K).card K := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have hsub := stronglyConnected_subset_fibre hD hS hconn ha
  rcases Nat.lt_or_ge 1 (roughPart (N / (K + 1)) a) with h1 | h1
  · exact ((Finset.card_le_card hsub).trans (card_fibre_le_K h1)).trans (le_max_right _ _)
  · have hone : roughPart (N / (K + 1)) a = 1 := le_antisymm h1 (roughPart_pos _ _)
    rw [hone, fibre_one] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_left _ _)

end HubRemoval
