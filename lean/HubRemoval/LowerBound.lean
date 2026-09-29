import HubRemoval.AttachProb
import HubRemoval.CoreD
import HubRemoval.Sigma
import HubRemoval.Attach

/-!
# The lower bound (paper, Proposition 4.6)

Assume the hypotheses of Lemma 4.5 (`CoreHyp N K s₀ η δ`), put `M = N^{1−2δ}`, and let
`0 ≤ ρ ≤ 1`, `λ = max(ρ, 1 − ρ)`. `𝒰 ⊆ F₁` is the set of Lemma 4.5.

**Proposition 4.6, eq. (2).** In `𝒟_ρ(N, K)`,
`E[Φ_K] ≥ Ψ(N, B) − K − |F₁ \ 𝒰| − 2λ^{s₀+1} N − N · P(𝓡ᶜ)` (`lower_bound`).

With Lemma 4.5(d) this becomes the paper's form
`E[Φ_K] ≥ Ψ(N, B) − K − Err − N · P(𝓡ᶜ)`, where
`Err = N^{1−δ} + N(4δ/η + 2(1+C₁)/(η log N)) + #{m ≤ N : ω_z(m) < s₀} + 2λ^{s₀+1} N`
(`lower_bound_err`). This needs the one instance of Mertens' theorem used in Lemma 4.5(d).
Lemma 4.1 bounds `P(𝓡ᶜ)` (`prob_not_robust`).

The proof is the paper's. Let `X = 1_𝓡 · #{m ∈ 𝒰 : A_m}`.
* **Pointwise**, `X ≤ Φ_K`: on `𝓡`, every `m ∈ 𝒰` with `A_m` joins the SCC of `S_M`
  (Lemmas 4.4, 4.2, 4.1), so these `m` form a strongly connected set.
* `E[X] = ∑_{m ∈ 𝒰} P(A_m ∩ 𝓡) ≥ ∑_{m ∈ 𝒰} (P(A_m) − P(𝓡ᶜ))`, and
  `P(A_m) ≥ 1 − 2λ^{s(m)} ≥ 1 − 2λ^{s₀+1}` (Lemmas 4.4 and 4.5(c)).
* `|𝒰| = |F₁| − |F₁ \ 𝒰|` and `|F₁| = Ψ(N, B) − Ψ(K, B) ≥ Ψ(N, B) − K`.
-/

namespace HubRemoval

open Finset

variable {N K s₀ : ℕ} {η δ : ℝ}

open Classical in
/-- `𝒰` as a finite set. -/
noncomputable def coreU (N K s₀ : ℕ) (δ : ℝ) : Finset ℕ := (smoothFibre N K).filter (InU N K s₀ δ)

open Classical in
/-- **Pointwise, `X ≤ Φ_K`.** On `𝓡`, the `m ∈ 𝒰` for which `A_m` occurs form a strongly
connected set. -/
theorem card_attached_le_PhiK (h : CoreHyp N K s₀ η δ) (ω : Edge N K → Bool)
    (hR : RobustEvent (arc ω) N K ((N : ℝ) ^ (1 - 2 * δ))) :
    ((coreU N K s₀ δ).filter (fun m => attachEv ((N : ℝ) ^ (1 - 2 * δ)) m ω)).card ≤
      PhiK N K ω := by
  classical
  set M := (N : ℝ) ^ (1 - 2 * δ)
  have hM := core_a h
  apply card_le_PhiK
  · intro m hm
    have hmU := (mem_filter.mp hm).1
    have hmF := (mem_filter.mp hmU).1
    simpa [smoothFibre, vertices] using (mem_filter.mp hmF).1
  · -- Each attached `m` is mutually reachable with some `d ∈ S_M`.
    have hjoin : ∀ m ∈ (coreU N K s₀ δ).filter (fun m => attachEv M m ω),
        ∃ d, goodSet M K d ∧ MutuallyReachable (arc ω) m d := by
      intro m hm
      obtain ⟨⟨d, hd, hmd⟩, ⟨d', hd', hd'm⟩⟩ := (mem_filter.mp hm).2
      have hgd := (mem_lowerDivisors.mp hd).2
      have hgd' := (mem_lowerDivisors.mp hd').2
      exact ⟨d, hgd, attach_mutual hM hR hgd hgd' hmd hd'm⟩
    intro a ha b hb
    obtain ⟨d, hd, had⟩ := hjoin a ha
    obtain ⟨d', hd', hbd'⟩ := hjoin b hb
    exact ((had.trans (sigma_mutual hM hR hd hd')).trans hbd'.symm).1

open Classical in
/-- `|𝒰| ≥ Ψ(N, B) − K − |F₁ \ 𝒰|`. -/
theorem card_coreU_ge (h : CoreHyp N K s₀ η δ) :
    (psi N (N / (K + 1)) : ℝ) - K -
        ((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card ≤ (coreU N K s₀ δ).card := by
  classical
  have hKN : K ≤ N := by
    have h1 : (K : ℝ) ≤ N := h.H1.trans ((h.rpow_le (by linarith [h.η_pos])).trans
      (Real.rpow_one (N : ℝ)).le)
    exact_mod_cast h1
  have hsplit := card_filter_add_card_filter_not (s := smoothFibre N K) (InU N K s₀ δ)
  have hF := card_smoothFibre hKN
  have hpsiK := psi_le_self K (N / (K + 1))
  have hpsi : psi K (N / (K + 1)) ≤ psi N (N / (K + 1)) := by
    have : (smoothFibre N K).card + psi K (N / (K + 1)) = psi N (N / (K + 1)) := by
      rw [hF]
      exact Nat.sub_add_cancel (psi_mono hKN _)
    omega
  unfold coreU
  have e : ((smoothFibre N K).filter (InU N K s₀ δ)).card =
      (smoothFibre N K).card - ((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card := by
    omega
  have hle : ((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card ≤
      (smoothFibre N K).card := by omega
  rw [e, Nat.cast_sub hle, hF, Nat.cast_sub hpsi]
  have : (psi K (N / (K + 1)) : ℝ) ≤ K := by exact_mod_cast hpsiK
  linarith

/-- `|𝒰| ≤ N`. -/
theorem card_coreU_le : (coreU N K s₀ δ).card ≤ N := by
  classical
  have hsub : coreU N K s₀ δ ⊆ Ioc 0 N := fun m hm => by
    have hmF := (mem_filter.mp hm).1
    have := (mem_filter.mp hmF).1
    simp only [vertices, mem_Ioc] at this
    exact mem_Ioc.mpr ⟨by omega, this.2⟩
  simpa using card_le_card hsub

open Classical in
/-- **Proposition 4.6, eq. (2).**
`E[Φ_K] ≥ Ψ(N, B) − K − |F₁ \ 𝒰| − 2λ^{s₀+1} N − N · P(𝓡ᶜ)`. -/
theorem lower_bound (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (psi N (N / (K + 1)) : ℝ) - K -
        ((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card -
        2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N -
        N * prob ρ (fun ω : Edge N K → Bool =>
          ¬ RobustEvent (arc ω) N K ((N : ℝ) ^ (1 - 2 * δ))) ≤
      expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) := by
  classical
  set M := (N : ℝ) ^ (1 - 2 * δ) with hMdef
  set U := coreU N K s₀ δ with hUdef
  set lam := max ρ (1 - ρ) with hlam
  set pR := prob ρ (fun ω : Edge N K → Bool => ¬ RobustEvent (arc ω) N K M) with hpR
  have hlam0 : 0 ≤ lam := le_trans hρ0 (le_max_left _ _)
  have hlam1 : lam ≤ 1 := max_le hρ1 (by linarith)
  have hpR0 : 0 ≤ pR := prob_nonneg hρ0 hρ1 _
  -- The indicator sum `X`.
  set X : (Edge N K → Bool) → ℝ := fun ω =>
    ∑ m ∈ U, (if attachEv M m ω ∧ RobustEvent (arc ω) N K M then (1 : ℝ) else 0) with hXdef
  -- Pointwise `X ≤ Φ_K`.
  have hXle : ∀ ω, X ω ≤ PhiK N K ω := by
    intro ω
    by_cases hR : RobustEvent (arc ω) N K M
    · have h1 : X ω = ((U.filter (fun m => attachEv M m ω)).card : ℝ) := by
        simp only [hXdef, hR, and_true]
        rw [← natCast_card_filter]
      rw [h1]
      exact_mod_cast card_attached_le_PhiK h ω hR
    · have h1 : X ω = 0 := by
        simp only [hXdef, hR, and_false, ↓reduceIte, sum_const_zero]
      rw [h1]
      exact Nat.cast_nonneg _
  -- `E[X] = ∑_{m ∈ 𝒰} P(A_m ∩ 𝓡)`.
  have hEX : expectP ρ X = ∑ m ∈ U,
      prob ρ (fun ω : Edge N K → Bool => attachEv M m ω ∧ RobustEvent (arc ω) N K M) := by
    rw [hXdef, expectP_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [prob_eq]
    rfl
  -- Each term is `≥ 1 − 2λ^{s₀+1} − P(𝓡ᶜ)`.
  have hterm : ∀ m ∈ U, 1 - 2 * lam ^ (s₀ + 1) - pR ≤
      prob ρ (fun ω : Edge N K → Bool => attachEv M m ω ∧ RobustEvent (arc ω) N K M) := by
    intro m hm
    have hmU : InU N K s₀ δ m := (mem_filter.mp hm).2
    obtain ⟨hmF, hMm⟩ := core_b h hmU
    have hmN : m ≤ N := by
      have := (mem_filter.mp hmF).1
      simp only [vertices, mem_Ioc] at this
      exact this.2
    have hs := core_c h hmU
    have hA := prob_attachEv_ge (N := N) (K := K) hρ0 hρ1 hmN hMm
    have hpow : lam ^ (lowerDivisors M K m).card ≤ lam ^ (s₀ + 1) :=
      pow_le_pow_of_le_one hlam0 hlam1 hs
    have hand := prob_and_ge hρ0 hρ1 (attachEv (N := N) (K := K) M m)
      (fun ω => RobustEvent (arc ω) N K M)
    linarith
  have hsum : (U.card : ℝ) * (1 - 2 * lam ^ (s₀ + 1) - pR) ≤ expectP ρ X := by
    rw [hEX]
    calc (U.card : ℝ) * (1 - 2 * lam ^ (s₀ + 1) - pR)
        = ∑ _m ∈ U, (1 - 2 * lam ^ (s₀ + 1) - pR) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hterm
  have hU := card_coreU_ge h
  have hUN : (U.card : ℝ) ≤ N := by exact_mod_cast card_coreU_le
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have ha : 0 ≤ 2 * lam ^ (s₀ + 1) := by positivity
  have hEmono : expectP ρ X ≤ expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) :=
    expectP_mono hρ0 hρ1 hXle
  -- `|𝒰|(1 − a − p) ≥ |𝒰| − N a − N p`.
  have h1 : (U.card : ℝ) * (2 * lam ^ (s₀ + 1)) ≤ N * (2 * lam ^ (s₀ + 1)) :=
    mul_le_mul_of_nonneg_right hUN ha
  have h2 : (U.card : ℝ) * pR ≤ N * pR := mul_le_mul_of_nonneg_right hUN hpR0
  nlinarith

open Classical in
/-- **Proposition 4.6, the paper's form.** Assuming the instance of Mertens' second theorem used
in Lemma 4.5(d), `E[Φ_K] ≥ Ψ(N, B) − K − Err − N · P(𝓡ᶜ)`. -/
theorem lower_bound_err (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hMb : coreY N K δ < ((N / (K + 1) : ℕ) : ℝ) →
      ∑ p ∈ (primesUpTo (N / (K + 1))).filter (fun p : ℕ => coreY N K δ < p), (1 : ℝ) / p ≤
        Real.log (Real.log ((N / (K + 1) : ℕ) : ℝ) / Real.log (coreY N K δ)) +
          C₁ / Real.log (coreY N K δ)) :
    (psi N (N / (K + 1)) : ℝ) - K -
        ((N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + C₁) / (η * Real.log N)) +
          ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card +
          2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N) -
        N * prob ρ (fun ω : Edge N K → Bool =>
          ¬ RobustEvent (arc ω) N K ((N : ℝ) ^ (1 - 2 * δ))) ≤
      expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) := by
  classical
  have h1 := lower_bound h hρ0 hρ1
  have h2 := core_d h hC₁ hMb
  linarith

/-- **The upper bound in expectation.** `E[Φ_K] ≤ Ψ(N, B)`, from Proposition 3.2. -/
theorem expect_PhiK_le_psi {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) ≤ psi N (N / (K + 1)) :=
  calc expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ))
      ≤ expectP ρ (fun _ : Edge N K → Bool => (psi N (N / (K + 1)) : ℝ)) :=
        expectP_mono hρ0 hρ1 fun ω => by exact_mod_cast PhiK_le_psi ω
    _ = psi N (N / (K + 1)) := expectP_const ρ _

/-- `N / N^{1−2δ} = N^{2δ}`. -/
theorem CoreHyp.N_div_M (h : CoreHyp N K s₀ η δ) :
    (N : ℝ) / (N : ℝ) ^ (1 - 2 * δ) = (N : ℝ) ^ (2 * δ) := by
  have hpos : 0 < (N : ℝ) ^ (1 - 2 * δ) := Real.rpow_pos_of_pos h.N_pos _
  rw [div_eq_iff hpos.ne', ← h.rpow_add, show 2 * δ + (1 - 2 * δ) = (1 : ℝ) by ring,
    Real.rpow_one]

open Classical in
/-- **Proposition 4.6 with Lemma 4.1: the two-sided bound for each fixed `N`.** Assuming the
instance of Mertens' second theorem used in Lemma 4.5(d), in `𝒟_ρ(N, K)`,
`Ψ(N, B) − K − Err − N³ exp(−q (N^{2δ} − 2)) ≤ E[Φ_K] ≤ Ψ(N, B)`, with `q = ρ(1 − ρ)`. -/
theorem fixedN_sandwich (h : CoreHyp N K s₀ η δ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hMb : coreY N K δ < ((N / (K + 1) : ℕ) : ℝ) →
      ∑ p ∈ (primesUpTo (N / (K + 1))).filter (fun p : ℕ => coreY N K δ < p), (1 : ℝ) / p ≤
        Real.log (Real.log ((N / (K + 1) : ℕ) : ℝ) / Real.log (coreY N K δ)) +
          C₁ / Real.log (coreY N K δ)) :
    (psi N (N / (K + 1)) : ℝ) - K -
        ((N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + C₁) / (η * Real.log N)) +
          ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card +
          2 * (max ρ (1 - ρ)) ^ (s₀ + 1) * N) -
        (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2)) ≤
      expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) ∧
    expectP ρ (fun ω : Edge N K → Bool => (PhiK N K ω : ℝ)) ≤ psi N (N / (K + 1)) := by
  refine ⟨?_, expect_PhiK_le_psi hρ0 hρ1⟩
  have h1 := lower_bound_err h hρ0 hρ1 hC₁ hMb
  have hM0 : 0 < (N : ℝ) ^ (1 - 2 * δ) := Real.rpow_pos_of_pos h.N_pos _
  have hMN : (N : ℝ) ^ (1 - 2 * δ) ≤ N :=
    (h.rpow_le (by linarith [h.δ_pos])).trans (Real.rpow_one (N : ℝ)).le
  have h2 := prob_not_robust_exp (N := N) (K := K) hρ0 hρ1 hM0 hMN
  rw [h.N_div_M] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N)
  have e : (N : ℝ) * ((N : ℝ) ^ 2 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2))) =
      (N : ℝ) ^ 3 * Real.exp (-(ρ * (1 - ρ)) * ((N : ℝ) ^ (2 * δ) - 2)) := by ring
  linarith

end HubRemoval
