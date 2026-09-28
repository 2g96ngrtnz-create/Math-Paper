import HubRemoval.Sigma

/-!
# Attachment (paper, Lemma 4.4)

Let `m ∈ V_{N,K}` with `m > M`, let `D(m) = {d ∈ S_M : d ∣ m}` and `s = |D(m)|`. `A_m` is the
event that there are `d, d' ∈ D(m)` with `m → d` and `d' → m`.

**Lemma 4.4.** If `s ≥ 1`, then `P(A_m) = 1 − ρ^s − (1 − ρ)^s ≥ 1 − 2λ^s`, where
`λ = max(ρ, 1 − ρ)`. On `A_m ∩ 𝓡` the vertex `m` lies in `Σ`.

What is formalised:

* **The deterministic part** (`attach_mutual`). If `M ≥ 4(K+1)`, `𝓡` holds, `d, d' ∈ S_M`,
  `m → d` and `d' → m`, then `m` and `d` lie in the same SCC. So `m` lies in `Σ`.
* **The probability, on the `s` edges.** Each edge `{dᵢ, m}` has `dᵢ < m`, so its default
  orientation is `m → dᵢ`. It is reversed to `dᵢ → m` with probability `ρ`, independently. An outcome
  is `ω : Fin s → Bool`, with `ω i = true` meaning reversed, and it has weight
  `∏ᵢ (ρ if ω i else 1 − ρ)`. The weights sum to `1` (`sum_weight`). The event `A_m` says that
  `ω` takes both values. Its weight is exactly `1 − ρ^s − (1 − ρ)^s` (`prob_attach`), which is
  `≥ 1 − 2λ^s` (`prob_attach_ge`).

This is the marginal computation on the `s` edges `{d, m}`. `A_m` depends only on these edges,
so it gives `P(A_m)`. The product measure on all orientations of `G_{N,K}`, and the
marginalisation step, are not formalised.
-/

namespace HubRemoval

open Finset

/-- **Lemma 4.4, deterministic part.** Assume `M ≥ 4(K+1)` and `𝓡`. If `d, d' ∈ S_M`, `m → d` and
`d' → m`, then `m` and `d` lie in the same SCC: `m → d ⇝ d' → m`. -/
theorem attach_mutual {D : ℕ → ℕ → Prop} {N K : ℕ} {M : ℝ} (hM : 4 * ((K : ℝ) + 1) ≤ M)
    (hR : RobustEvent D N K M) {d d' m : ℕ} (hd : goodSet M K d) (hd' : goodSet M K d')
    (hmd : D m d) (hd'm : D d' m) : MutuallyReachable D m d :=
  ⟨Relation.ReflTransGen.single hmd, (sigma_mutual hM hR hd hd').1.tail hd'm⟩

/-- The weight of an orientation `ω` of `s` independent edges, each reversed with
probability `ρ`. It is defined over any commutative ring, so that it can be evaluated exactly over
`ℚ`. -/
def weight {R : Type*} [CommRing R] (ρ : R) {s : ℕ} (ω : Fin s → Bool) : R :=
  ∏ i, if ω i then ρ else 1 - ρ

/-- The event `A_m`: some edge points `m → d` (`ω i = false`), and some edge points
`d' → m` (`ω j = true`). -/
def attachEvent {s : ℕ} (ω : Fin s → Bool) : Prop :=
  (∃ i, ω i = true) ∧ ∃ j, ω j = false

instance {s : ℕ} : DecidablePred (attachEvent (s := s)) := fun _ => by
  unfold attachEvent; infer_instance

/-- The weights form a probability distribution. -/
theorem sum_weight {R : Type*} [CommRing R] (ρ : R) (s : ℕ) : ∑ ω : Fin s → Bool, weight ρ ω = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun (_ : Fin s) (b : Bool) => if b then ρ else 1 - ρ)]
  simp

/-- The complement of `A_m`: all edges point the same way. -/
theorem not_attachEvent_iff {s : ℕ} (ω : Fin s → Bool) :
    ¬ attachEvent ω ↔ ω = (fun _ => true) ∨ ω = (fun _ => false) := by
  unfold attachEvent
  constructor
  · intro h
    by_cases hi : ∃ i, ω i = true
    · left
      funext j
      by_contra hj
      exact h ⟨hi, j, by simpa using hj⟩
    · right
      push Not at hi
      funext j
      by_contra hj
      exact hi j (by simpa using hj)
  · rintro (rfl | rfl) ⟨⟨i, hi⟩, j, hj⟩
    · exact Bool.noConfusion hj
    · exact Bool.noConfusion hi

/-- **Lemma 4.4, the probability.** For `s ≥ 1` independent edges,
`P(A_m) = 1 − ρ^s − (1 − ρ)^s`. -/
theorem prob_attach {R : Type*} [CommRing R] (ρ : R) {s : ℕ} (hs : 1 ≤ s) :
    ∑ ω ∈ univ.filter (attachEvent (s := s)), weight ρ ω = 1 - ρ ^ s - (1 - ρ) ^ s := by
  have hne : (fun _ : Fin s => true) ≠ (fun _ => false) := fun h =>
    Bool.noConfusion (congrFun h ⟨0, hs⟩)
  have hcompl : univ.filter (fun ω : Fin s → Bool => ¬ attachEvent ω) =
      {fun _ => true, fun _ => false} := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact not_attachEvent_iff ω
  have htotal := Finset.sum_filter_add_sum_filter_not univ (attachEvent (s := s)) (weight ρ)
  rw [hcompl, Finset.sum_pair hne, sum_weight] at htotal
  have h1 : weight ρ (fun _ : Fin s => true) = ρ ^ s := by simp [weight]
  have h0 : weight ρ (fun _ : Fin s => false) = (1 - ρ) ^ s := by simp [weight]
  rw [h1, h0] at htotal
  linear_combination htotal

/-- **Lemma 4.4, the bound.** For `0 ≤ ρ ≤ 1` and `λ = max(ρ, 1 − ρ)`,
`P(A_m) ≥ 1 − 2λ^s`. -/
theorem prob_attach_ge {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {s : ℕ} (hs : 1 ≤ s) :
    1 - 2 * (max ρ (1 - ρ)) ^ s ≤ ∑ ω ∈ univ.filter (attachEvent (s := s)), weight ρ ω := by
  rw [prob_attach ρ hs]
  have h1 : ρ ^ s ≤ (max ρ (1 - ρ)) ^ s := pow_le_pow_left₀ hρ0 (le_max_left _ _) s
  have h2 : (1 - ρ) ^ s ≤ (max ρ (1 - ρ)) ^ s :=
    pow_le_pow_left₀ (by linarith) (le_max_right _ _) s
  linarith

end HubRemoval
