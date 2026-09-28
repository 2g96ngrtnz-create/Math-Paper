import HubRemoval.LowerBound
import HubRemoval.Mertens2

/-!
# Lemma 4.5(d) and Proposition 4.6 without the Mertens hypothesis

`core_d`, `lower_bound_err` and `fixedN_sandwich` take the one instance of Mertens' second theorem
used in Lemma 4.5(d) as a hypothesis `hMb`, at `y = Y` and `w = B`. Lemma 2.1(b) is now proved
(`mertens_b`, with `C₁ = 18`). Under the hypotheses of Lemma 4.5, `Y ≥ N^{η/2} = (N^{η/4})² ≥ 16`,
so that instance holds (`CoreHyp.mertens_instance`). This file restates the three results with no
hypothesis beyond those of the paper.
-/

namespace HubRemoval

open Finset

variable {N K s₀ : ℕ} {η δ : ℝ}

/-- `Y ≥ 2` (in fact `Y ≥ 16`) under the hypotheses of Lemma 4.5. -/
theorem CoreHyp.two_le_Y (h : CoreHyp N K s₀ η δ) : 2 ≤ coreY N K δ := by
  have h1 : (N : ℝ) ^ (η / 2) = ((N : ℝ) ^ (η / 4)) ^ 2 := by
    rw [h.rpow_pow]
    congr 1
    push_cast
    ring
  have h2 : (16 : ℝ) ≤ ((N : ℝ) ^ (η / 4)) ^ 2 := by nlinarith [h.H2]
  linarith [h.rpow_le_Y]

/-- **The Mertens instance of Lemma 4.5(d) holds**, with `C₁ = 18`, by Lemma 2.1(b). -/
theorem CoreHyp.mertens_instance (h : CoreHyp N K s₀ η δ) :
    coreY N K δ < ((N / (K + 1) : ℕ) : ℝ) →
      ∑ p ∈ (primesUpTo (N / (K + 1))).filter (fun p : ℕ => coreY N K δ < p), (1 : ℝ) / p ≤
        Real.log (Real.log ((N / (K + 1) : ℕ) : ℝ) / Real.log (coreY N K δ)) +
          18 / Real.log (coreY N K δ) := by
  intro hYB
  have hb := mertens_b (y := coreY N K δ) (w := ((N / (K + 1) : ℕ) : ℝ)) h.two_le_Y hYB.le
  rw [Nat.floor_natCast] at hb
  linarith [(abs_le.mp hb).2]

open Classical in
/-- **Lemma 4.5(d), unconditional.**
`|F₁ \ 𝒰| ≤ N^{1−δ} + N(4δ/η + 38/(η log N)) + #{m ≤ N : ω_z(m) < s₀}`. -/
theorem core_d' (h : CoreHyp N K s₀ η δ) :
    (((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card : ℝ) ≤
      (N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) +
        ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card :=
  core_d h (by norm_num) h.mertens_instance

open Classical in
/-- **Proposition 4.6, unconditional (paper's form).** In `𝒟_ρ(N, K)`,
`E[Φ_K] ≥ Ψ(N, B) − K − Err − N · P(𝓡ᶜ)` with `C₁ = 18` in `Err`. -/
theorem lower_bound_err' (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (psi N (N / (K + 1)) : ℝ) - K -
        ((N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) +
          ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card +
          2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N) -
        N * prob ρ (fun ω : Edge N K → Bool =>
          ¬ RobustEvent (arc ω) N K ((N : ℝ) ^ (1 - 2 * δ))) ≤
      expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) :=
  lower_bound_err h hρ0 hρ1 (by norm_num) h.mertens_instance

open Classical in
/-- **Proposition 4.6 with Lemma 4.1, unconditional.** For each `N`, in `𝒟_ρ(N, K)`,
`Ψ(N, B) − K − Err − N³ exp(−q (N^{2δ} − 2)) ≤ E[Φ_K] ≤ Ψ(N, B)`, with `q = ρ(1 − ρ)` and
`C₁ = 18` in `Err`. -/
theorem fixedN_sandwich' (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (psi N (N / (K + 1)) : ℝ) - K -
        ((N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + 18) / (η * Real.log N)) +
          ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card +
          2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N) -
        (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2)) ≤
      expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) ∧
    expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) ≤ psi N (N / (K + 1)) :=
  fixedN_sandwich h hρ0 hρ1 (by norm_num) h.mertens_instance

end HubRemoval
