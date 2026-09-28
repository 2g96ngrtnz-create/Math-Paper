import Mathlib

/-!
# Monotonicity of the largest SCC (paper, Lemma 6.1)

`D` is a digraph on a type `α`, given as a relation, and `V` is a finite vertex set. The induced
digraph `D[V]` keeps the arcs of `D` with both ends in `V`. A set `S ⊆ V` is strongly connected in
`D[V]` if any two of its elements are joined by a directed path inside `D[V]`.

`maxSCC D V` is the largest size of a strongly connected set of `D[V]`. Every strongly connected
set lies in an SCC, and every SCC is strongly connected, so this is the size of the largest SCC,
the paper's `#Φ(D[V])`.

**Lemma 6.1.** If `U ⊆ V`, then `#Φ(D[U]) ≤ #Φ(D[V])`.
-/

namespace HubRemoval

variable {α : Type*}

/-- The arcs of the induced digraph `D[V]`. -/
def inducedArc (D : α → α → Prop) (V : Finset α) (a b : α) : Prop :=
  a ∈ V ∧ b ∈ V ∧ D a b

/-- `S` is strongly connected in `D[V]`: `S ⊆ V`, and any two elements of `S` are joined by a
directed path in `D[V]`. -/
def StronglyConnectedIn (D : α → α → Prop) (V S : Finset α) : Prop :=
  S ⊆ V ∧ ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen (inducedArc D V) a b

open Classical in
/-- `#Φ(D[V])`: the largest size of a strongly connected set of `D[V]`. -/
noncomputable def maxSCC (D : α → α → Prop) (V : Finset α) : ℕ :=
  ((V.powerset).filter (StronglyConnectedIn D V)).sup Finset.card

/-- A strongly connected set of `D[U]` is strongly connected in `D[V]` when `U ⊆ V`: a path
inside `D[U]` is a path inside `D[V]`. -/
theorem StronglyConnectedIn.mono {D : α → α → Prop} {U V S : Finset α} (hUV : U ⊆ V)
    (h : StronglyConnectedIn D U S) : StronglyConnectedIn D V S :=
  ⟨h.1.trans hUV, fun a ha b hb =>
    Relation.ReflTransGen.mono (fun _ _ ⟨hx, hy, hxy⟩ => ⟨hUV hx, hUV hy, hxy⟩) _ _
      (h.2 a ha b hb)⟩

/-- Every strongly connected set of `D[V]` has at most `#Φ(D[V])` elements. -/
theorem card_le_maxSCC {D : α → α → Prop} {V S : Finset α} (h : StronglyConnectedIn D V S) :
    S.card ≤ maxSCC D V := by
  classical
  unfold maxSCC
  convert Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h⟩)

/-- `#Φ(D[V])` is attained: some strongly connected set has exactly that many elements. -/
theorem exists_card_eq_maxSCC (D : α → α → Prop) (V : Finset α) :
    ∃ S, StronglyConnectedIn D V S ∧ S.card = maxSCC D V := by
  classical
  have hne : ((V.powerset).filter (StronglyConnectedIn D V)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset V,
      ⟨Finset.empty_subset V, fun a ha => absurd ha (Finset.notMem_empty a)⟩⟩⟩
  obtain ⟨S, hS, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  unfold maxSCC
  convert hcard.symm

/-- **Lemma 6.1.** If `U ⊆ V`, then `#Φ(D[U]) ≤ #Φ(D[V])`. -/
theorem maxSCC_mono (D : α → α → Prop) {U V : Finset α} (hUV : U ⊆ V) :
    maxSCC D U ≤ maxSCC D V := by
  obtain ⟨S, hS, hcard⟩ := exists_card_eq_maxSCC D U
  exact hcard ▸ card_le_maxSCC (hS.mono hUV)

/-- **Lemma 6.1, as used for hub removal.** Fix one orientation `D` of `G_N`. Removing more hubs
cannot enlarge the largest SCC: if `K ≤ K'`, then `Φ_{K'} ≤ Φ_K`, where `Φ_K` is the largest
SCC of `D` restricted to `V_{N,K} = (K, N]`. -/
theorem maxSCC_Ioc_antitone (D : ℕ → ℕ → Prop) (N : ℕ) {K K' : ℕ} (hK : K ≤ K') :
    maxSCC D (Finset.Ioc K' N) ≤ maxSCC D (Finset.Ioc K N) :=
  maxSCC_mono D (Finset.Ioc_subset_Ioc_left hK)

end HubRemoval
