import HubRemoval.FiniteProb
import HubRemoval.Monotone
import HubRemoval.UpperBound

/-!
# The random orientation `𝒟_ρ(N, K)`

The edges of `G_{N,K}` are the pairs `(a, b)` with `K < a < b ≤ N` and `a ∣ b`. By default an
edge points from the larger end to the smaller, `b → a`. Independently for each edge, it is
reversed to `a → b` with probability `ρ`.

An outcome is `ω : Edge N K → Bool`, where `ω e = true` means that `e` is reversed. With the
weights of `HubRemoval/FiniteProb.lean` this is exactly the paper's `𝒟_ρ(N, K)`.

* `bit ω a b` reads the coordinate of the edge `(a, b)`, and is `false` if there is no such edge.
* `arc ω a b` says that `a → b` in the digraph of `ω`.
* `PhiK N K ω` is `Φ_K`, the size of the largest SCC.

**Proposition 3.2 in the model** (`PhiK_le_psi`): `Φ_K(ω) ≤ Ψ(N, B)` for every outcome.
-/

namespace HubRemoval

open Finset

/-- The edges of `G_{N,K}`: pairs `(a, b)` with `K < a < b ≤ N` and `a ∣ b`. -/
def edges (N K : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc K N ×ˢ Ioc K N).filter fun e => e.1 < e.2 ∧ e.1 ∣ e.2

/-- The edge type. -/
abbrev Edge (N K : ℕ) := {e : ℕ × ℕ // e ∈ edges N K}

theorem mem_edges {N K a b : ℕ} :
    (a, b) ∈ edges N K ↔ K < a ∧ a < b ∧ b ≤ N ∧ a ∣ b := by
  simp only [edges, mem_filter, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _, h4⟩, h5, h6⟩
    exact ⟨h1, h5, h4, h6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, by omega⟩, by omega, h3⟩, h2, h4⟩

variable {N K : ℕ}

/-- The coordinate of the edge `(a, b)`, or `false` if `(a, b)` is not an edge. -/
def bit (ω : Edge N K → Bool) (a b : ℕ) : Bool :=
  if h : (a, b) ∈ edges N K then ω ⟨(a, b), h⟩ else false

/-- `a → b` in the digraph of `ω`: either `(a, b)` is an edge that is reversed, or `(b, a)` is an
edge in its default orientation. -/
def arc (ω : Edge N K → Bool) (a b : ℕ) : Prop :=
  ((a, b) ∈ edges N K ∧ bit ω a b = true) ∨ ((b, a) ∈ edges N K ∧ bit ω b a = false)

/-- Every arc is an edge of `G_{N,K}`. -/
theorem arc_adj {ω : Edge N K → Bool} {a b : ℕ} (h : arc ω a b) : (divGraph N K).Adj a b := by
  rcases h with ⟨he, -⟩ | ⟨he, -⟩
  · obtain ⟨h1, h2, h3, h4⟩ := mem_edges.mp he
    exact ⟨by omega, h1, by omega, by omega, h3, Or.inl h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := mem_edges.mp he
    exact ⟨by omega, by omega, h3, h1, by omega, Or.inr h4⟩

/-- Both ends of an arc are vertices of `G_{N,K}`. -/
theorem arc_mem {ω : Edge N K → Bool} {a b : ℕ} (h : arc ω a b) :
    a ∈ Ioc K N ∧ b ∈ Ioc K N := by
  obtain ⟨-, ha, haN, hb, hbN, -⟩ := arc_adj h
  exact ⟨mem_Ioc.mpr ⟨ha, haN⟩, mem_Ioc.mpr ⟨hb, hbN⟩⟩

/-- An edge `(a, b)`, `a < b`, points `a → b` exactly when reversed and `b → a` otherwise. -/
theorem arc_of_edge {ω : Edge N K → Bool} {a b : ℕ} (he : (a, b) ∈ edges N K) :
    (arc ω a b ↔ bit ω a b = true) ∧ (arc ω b a ↔ bit ω a b = false) := by
  have hlt := (mem_edges.mp he).2.1
  have hba : (b, a) ∉ edges N K := fun h => by have := (mem_edges.mp h).2.1; omega
  refine ⟨⟨fun h => ?_, fun h => Or.inl ⟨he, h⟩⟩, ⟨fun h => ?_, fun h => Or.inr ⟨he, h⟩⟩⟩
  · rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hba
  · rcases h with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hba
    · exact h

/-- `bit` depends only on the coordinate of the edge `(a, b)`. -/
theorem bit_congr {ω ω' : Edge N K → Bool} {a b : ℕ}
    (h : ∀ e : Edge N K, e.val = (a, b) → ω e = ω' e) : bit ω a b = bit ω' a b := by
  unfold bit
  split_ifs with he
  · exact h _ rfl
  · rfl

/-- `Φ_K(ω)`: the size of the largest SCC of the digraph of `ω`. -/
noncomputable def PhiK (N K : ℕ) (ω : Edge N K → Bool) : ℕ := maxSCC (arc ω) (Ioc K N)

/-- A directed path in the digraph of `ω` stays inside `V_{N,K}`, so it is a path of the induced
digraph on `V_{N,K}`. -/
theorem reflTransGen_induced {ω : Edge N K → Bool} {a b : ℕ}
    (h : Relation.ReflTransGen (arc ω) a b) :
    Relation.ReflTransGen (inducedArc (arc ω) (Ioc K N)) a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy => ⟨(arc_mem hxy).1, (arc_mem hxy).2, hxy⟩) _ _ h

/-- **Proposition 3.2, in the model.** For every outcome, `Φ_K ≤ Ψ(N, B)`. -/
theorem PhiK_le_psi (ω : Edge N K → Bool) : PhiK N K ω ≤ psi N (N / (K + 1)) := by
  obtain ⟨S, hS, hcard⟩ := exists_card_eq_maxSCC (arc ω) (Ioc K N)
  rw [PhiK, ← hcard]
  refine stronglyConnected_card_le_psi (D := arc ω) (fun a b h => arc_adj h) hS.1 ?_
  intro a ha b hb
  exact Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _ (hS.2 a ha b hb)

/-- **Proposition 3.2, in the model.** For every outcome, `Φ_K ≤ max(|F₁|, K)`. -/
theorem PhiK_le_max (ω : Edge N K → Bool) : PhiK N K ω ≤ max (smoothFibre N K).card K := by
  obtain ⟨S, hS, hcard⟩ := exists_card_eq_maxSCC (arc ω) (Ioc K N)
  rw [PhiK, ← hcard]
  refine stronglyConnected_card_le_max (D := arc ω) (fun a b h => arc_adj h) hS.1 ?_
  intro a ha b hb
  exact Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _ (hS.2 a ha b hb)

/-- A set of vertices whose elements are pairwise mutually reachable in the digraph of `ω` has at
most `Φ_K(ω)` elements. -/
theorem card_le_PhiK {ω : Edge N K → Bool} {S : Finset ℕ} (hS : S ⊆ Ioc K N)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen (arc ω) a b) : S.card ≤ PhiK N K ω :=
  card_le_maxSCC ⟨hS, fun a ha b hb => reflTransGen_induced (hconn a ha b hb)⟩

end HubRemoval
