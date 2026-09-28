import HubRemoval.RobustProb
import HubRemoval.Core

/-!
# Attachment in the random orientation (paper, Lemma 4.4)

For `m ∈ V_{N,K}` with `m > M`, let `D(m) = {d ∈ S_M : d ∣ m}` (`lowerDivisors M K m`) and
`s = |D(m)|`. `A_m` is the event that some `d ∈ D(m)` has `m → d` and some `d' ∈ D(m)` has
`d' → m`.

**Lemma 4.4.** `P(A_m) ≥ 1 − ρ^s − (1 − ρ)^s ≥ 1 − 2λ^s`, where `λ = max(ρ, 1 − ρ)`.

The paper computes this with equality for `s ≥ 1`. The inequality below holds for every `s`.
Every `d ∈ D(m)` has `d ≤ M < m`, so `{d, m}` is an edge `(d, m)` of `G_{N,K}`. It points
`d → m` when reversed and `m → d` otherwise. If `A_m` fails, then all these edges are reversed or
none is. Each of these is a cylinder on the `s` edges, with probability `ρ^s` or `(1 − ρ)^s`.

The deterministic half (on `A_m ∩ 𝓡`, `m ∈ Σ`) is `attach_mutual` in `HubRemoval/Attach.lean`.
-/

namespace HubRemoval

open Finset

variable {N K : ℕ}

/-- The event `A_m`. -/
def attachEv (M : ℝ) (m : ℕ) (ω : Edge N K → Bool) : Prop :=
  (∃ d ∈ lowerDivisors M K m, arc ω m d) ∧ (∃ d ∈ lowerDivisors M K m, arc ω d m)

/-- For `d ∈ D(m)` with `M < m ≤ N`, `(d, m)` is an edge of `G_{N,K}`. -/
theorem edge_of_lowerDivisor {M : ℝ} {m d : ℕ} (hmN : m ≤ N) (hMm : M < m)
    (hd : d ∈ lowerDivisors M K m) : (d, m) ∈ edges N K := by
  obtain ⟨⟨hdm, -⟩, hKd, hdM, -⟩ := mem_lowerDivisors.mp hd
  have : (d : ℝ) < m := lt_of_le_of_lt hdM hMm
  exact mem_edges.mpr ⟨hKd, by exact_mod_cast this, hmN, hdm⟩

/-- The edges `(d, m)`, `d ∈ D(m)`. -/
noncomputable def starEdges (N K : ℕ) (M : ℝ) (m : ℕ) : Finset (Edge N K) :=
  univ.filter fun e => e.val.2 = m ∧ e.val.1 ∈ lowerDivisors M K m

theorem card_starEdges {M : ℝ} {m : ℕ} (hmN : m ≤ N) (hMm : M < m) :
    (starEdges N K M m).card = (lowerDivisors M K m).card := by
  refine card_bij (fun e _ => e.val.1) (fun e he => (mem_filter.mp he).2.2) ?_ ?_
  · intro e₁ he₁ e₂ he₂ h
    have h₁ := (mem_filter.mp he₁).2.1
    have h₂ := (mem_filter.mp he₂).2.1
    exact Subtype.ext (Prod.ext h (h₁.trans h₂.symm))
  · intro d hd
    exact ⟨⟨(d, m), edge_of_lowerDivisor hmN hMm hd⟩,
      mem_filter.mpr ⟨mem_univ _, rfl, hd⟩, rfl⟩

/-- `P(every edge (d, m), d ∈ D(m), has coordinate b) = P(one coordinate is b)^s`. -/
theorem prob_all_bit (ρ : ℝ) (b : Bool) {M : ℝ} {m : ℕ} (hmN : m ≤ N) (hMm : M < m) :
    prob ρ (fun ω : Edge N K → Bool => ∀ d ∈ lowerDivisors M K m, bit ω d m = b) =
      pb ρ b ^ (lowerDivisors M K m).card := by
  have hiff : ∀ ω : Edge N K → Bool, (∀ d ∈ lowerDivisors M K m, bit ω d m = b) ↔
      ∀ e ∈ starEdges N K M m, ω e = (fun _ => b) e := by
    intro ω
    constructor
    · intro h e he
      obtain ⟨-, he2, he1⟩ := mem_filter.mp he
      have := h e.val.1 he1
      unfold bit at this
      rw [dite_eq_left (by rw [← he2]; exact e.2)] at this
      convert this using 2
      exact Subtype.ext (Prod.ext rfl he2)
    · intro h d hd
      have hdm := edge_of_lowerDivisor hmN hMm hd
      rw [bit, dite_eq_left hdm]
      exact h ⟨(d, m), hdm⟩ (mem_filter.mpr ⟨mem_univ _, rfl, hd⟩)
  rw [prob_congr hiff, prob_cylinder, prod_const, card_starEdges hmN hMm]

/-- **Lemma 4.4, in the model.** `P(A_m) ≥ 1 − ρ^s − (1 − ρ)^s`. -/
theorem prob_attachEv {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {M : ℝ} {m : ℕ} (hmN : m ≤ N)
    (hMm : M < m) :
    1 - ρ ^ (lowerDivisors M K m).card - (1 - ρ) ^ (lowerDivisors M K m).card ≤
      prob ρ (attachEv (N := N) (K := K) M m) := by
  have hnot : ∀ ω : Edge N K → Bool, ¬ attachEv M m ω →
      (∀ d ∈ lowerDivisors M K m, bit ω d m = true) ∨
        (∀ d ∈ lowerDivisors M K m, bit ω d m = false) := by
    intro ω h
    by_contra hc
    push Not at hc
    obtain ⟨⟨d, hd, hdt⟩, ⟨d', hd', hd'f⟩⟩ := hc
    apply h
    have e := edge_of_lowerDivisor hmN hMm hd
    have e' := edge_of_lowerDivisor hmN hMm hd'
    refine ⟨⟨d, hd, (arc_of_edge e).2.mpr ?_⟩, ⟨d', hd', (arc_of_edge e').1.mpr ?_⟩⟩
    · simpa using hdt
    · simpa using hd'f
  have h1 := prob_mono hρ0 hρ1 hnot
  have h2 := prob_or_le hρ0 hρ1
    (fun ω : Edge N K → Bool => ∀ d ∈ lowerDivisors M K m, bit ω d m = true)
    (fun ω => ∀ d ∈ lowerDivisors M K m, bit ω d m = false)
  rw [prob_all_bit ρ true hmN hMm, prob_all_bit ρ false hmN hMm] at h2
  have h3 := prob_not ρ (attachEv (N := N) (K := K) M m)
  simp only [pb] at h2
  simp only [Bool.false_eq_true, ↓reduceIte] at h2
  linarith

/-- **Lemma 4.4, the bound.** `P(A_m) ≥ 1 − 2λ^s` with `λ = max(ρ, 1 − ρ)`. -/
theorem prob_attachEv_ge {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {M : ℝ} {m : ℕ} (hmN : m ≤ N)
    (hMm : M < m) :
    1 - 2 * (max ρ (1 - ρ)) ^ (lowerDivisors M K m).card ≤
      prob ρ (attachEv (N := N) (K := K) M m) := by
  refine le_trans ?_ (prob_attachEv hρ0 hρ1 hmN hMm)
  have h1 := pow_le_pow_left₀ hρ0 (le_max_left ρ (1 - ρ)) (lowerDivisors M K m).card
  have h2 := pow_le_pow_left₀ (by linarith) (le_max_right ρ (1 - ρ)) (lowerDivisors M K m).card
  linarith

end HubRemoval
