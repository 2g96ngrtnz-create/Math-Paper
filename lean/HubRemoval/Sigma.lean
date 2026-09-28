import HubRemoval.Doubling
import HubRemoval.Robust
import HubRemoval.UpperBound

/-!
# The giant's seed `Σ` (paper, Corollary 4.3)

**Corollary 4.3.** Assume `M ≥ 4(K+1)`. On `𝓡`, the set `S_M` lies in a single SCC `Σ` of the
orientation `D`. If `M ≤ N`, then `Σ ⊆ F₁`.

The first claim is Lemma 4.2 (`S_M` lies in one component of `G_{M,K}`) combined with
Lemma 4.1 (on `𝓡`, each component of `G_{M,K}` lies in one SCC). For the second, every
element of `S_M` is `B`-smooth, so `S_M ⊆ F₁`. By Proposition 3.2 a strongly connected set lies in
one fibre, and a strongly connected set that meets `S_M` must therefore lie in `V₁ = F₁`.
-/

namespace HubRemoval

/-- **Corollary 4.3, first part.** On `𝓡`, any two elements of `S_M` lie in the same SCC. -/
theorem sigma_mutual {D : ℕ → ℕ → Prop} {N K : ℕ} {M : ℝ} (hM : 4 * ((K : ℝ) + 1) ≤ M)
    (hR : RobustEvent D N K M) {x x' : ℕ} (hx : goodSet M K x) (hx' : goodSet M K x') :
    MutuallyReachable D x x' :=
  robust_reachable hR (doubling_connected hM hx hx')

/-- `S_M ⊆ F₁` when `M ≤ N`: an element of `S_M` has every prime factor `p` with
`2(K+1)p ≤ M ≤ N`, so `p ≤ ⌊N/(K+1)⌋ = B`. -/
theorem goodSet_mem_smoothFibre {N K : ℕ} {M : ℝ} (hMN : M ≤ N) {x : ℕ} (hx : goodSet M K x) :
    x ∈ smoothFibre N K := by
  obtain ⟨hKx, hxM, hprimes⟩ := hx
  have hxN : x ≤ N := by exact_mod_cast hxM.trans hMN
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hKx, hxN⟩, ?_⟩
  refine Nat.mem_smoothNumbers'.mpr fun p hp hpx => ?_
  have h1 : 2 * ((K : ℝ) + 1) * p ≤ N := (hprimes p hp hpx).trans hMN
  have h2 : (K + 1) * p ≤ N := by
    have : ((K : ℝ) + 1) * p ≤ 2 * ((K : ℝ) + 1) * p := by
      have : (0 : ℝ) ≤ ((K : ℝ) + 1) * p := by positivity
      linarith
    exact_mod_cast this.trans h1
  have h3 : p ≤ N / (K + 1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [h2])
  omega

/-- **Corollary 4.3, second part.** If `M ≤ N`, a strongly connected set of an orientation of
`G_{N,K}` that contains an element of `S_M` lies in `F₁`. In particular `Σ ⊆ F₁`. -/
theorem sigma_subset_smoothFibre {D : ℕ → ℕ → Prop} {N K : ℕ} {M : ℝ} (hMN : M ≤ N)
    (hD : ∀ a b, D a b → (divGraph N K).Adj a b) {S : Finset ℕ} (hS : S ⊆ vertices N K)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, Relation.ReflTransGen D a b) {a : ℕ} (ha : a ∈ S)
    (haM : goodSet M K a) : S ⊆ smoothFibre N K := by
  have hsub := stronglyConnected_subset_fibre hD hS hconn ha
  have hsmooth := goodSet_mem_smoothFibre hMN haM
  have ha0 : a ≠ 0 := by have := haM.1; omega
  have hone : roughPart (N / (K + 1)) a = 1 :=
    (roughPart_eq_one_iff ha0).mpr (Finset.mem_filter.mp hsmooth).2
  rwa [hone, fibre_one] at hsub

end HubRemoval
