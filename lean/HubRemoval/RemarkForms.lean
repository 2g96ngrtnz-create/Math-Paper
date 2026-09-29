import HubRemoval.Giant

/-!
# Remark 3.4 (Equivalent forms)

Suppose `K = o(N)`. Since `0 ≤ Ψ(N, B) − |F₁| ≤ K`, Proposition 3.2 shows that the following are
equivalent (`remark_3_4`):
* (i) `E[Φ_K] = Ψ(N, B) + o(N)`;
* (ii) `E ||F₁| − Φ_K| = o(N)`;
* (iii) for every `ε > 0`, w.h.p. the largest SCC has at least `|F₁| − εN` vertices.

Theorem 1.2 gives (i), hence all three, for `ρ ∈ (0, 1)` (`remark_3_4_holds`).

The pointwise facts are `|F₁| ≤ Ψ(N, B) ≤ |F₁| + K`, `Φ_K ≤ Ψ(N, B)` and `Φ_K ≤ max(|F₁|, K)`, which
give `||F₁| − Φ_K| ≤ (Ψ(N, B) − Φ_K) + K`. Then (i) ⇒ (ii) by taking expectations, (ii) ⇒ (iii)
by Markov's inequality, and (iii) ⇒ (i) because `Ψ(N, B) − Φ_K ≤ K + εN + N·1[Φ_K < |F₁| − εN]`.
-/

namespace HubRemoval

open Finset Filter Topology

section Pointwise

variable {N K : ℕ}

/-- `|F₁| ≤ Ψ(N, B) ≤ |F₁| + K`. -/
theorem card_smoothFibre_bounds (hKN : K ≤ N) :
    ((smoothFibre N K).card : ℝ) ≤ psi N (N / (K + 1)) ∧
      (psi N (N / (K + 1)) : ℝ) ≤ (smoothFibre N K).card + K := by
  have hF := card_smoothFibre hKN
  have h1 := psi_le_self K (N / (K + 1))
  have h2 := psi_mono hKN (N / (K + 1))
  have e : (smoothFibre N K).card + psi K (N / (K + 1)) = psi N (N / (K + 1)) := by omega
  have e' : ((smoothFibre N K).card : ℝ) + psi K (N / (K + 1)) = psi N (N / (K + 1)) := by
    exact_mod_cast e
  have h1' : (psi K (N / (K + 1)) : ℝ) ≤ K := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ psi K (N / (K + 1)) := Nat.cast_nonneg _
  constructor <;> linarith

/-- `||F₁| − Φ_K| ≤ (Ψ(N, B) − Φ_K) + K`, for every outcome. -/
theorem abs_card_sub_PhiK_le (hKN : K ≤ N) (ω : Edge N K → Bool) :
    |((smoothFibre N K).card : ℝ) - PhiK N K ω| ≤ ((psi N (N / (K + 1)) : ℝ) - PhiK N K ω) + K := by
  have h1 : (PhiK N K ω : ℝ) ≤ psi N (N / (K + 1)) := by exact_mod_cast PhiK_le_psi ω
  obtain ⟨h3, -⟩ := card_smoothFibre_bounds hKN
  have h4 : (PhiK N K ω : ℝ) - (smoothFibre N K).card ≤ K := by
    rcases le_max_iff.mp (PhiK_le_max ω) with h | h
    · have : (PhiK N K ω : ℝ) ≤ (smoothFibre N K).card := by exact_mod_cast h
      linarith [Nat.cast_nonneg (α := ℝ) K]
    · have : (PhiK N K ω : ℝ) ≤ K := by exact_mod_cast h
      linarith [Nat.cast_nonneg (α := ℝ) (smoothFibre N K).card]
  rw [abs_le]
  constructor <;> linarith

end Pointwise

section Forms

variable {ρ : ℝ} {K : ℕ → ℕ}

/-- (i): `E[Φ_K] = Ψ(N, B) + o(N)`. -/
def FormI (ρ : ℝ) (K : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ => gap ρ N (K N) / N) atTop (𝓝 0)

/-- (ii): `E ||F₁| − Φ_K| = o(N)`. -/
def FormII (ρ : ℝ) (K : ℕ → ℕ) : Prop :=
  Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N (K N) → Bool =>
    |((smoothFibre N (K N)).card : ℝ) - PhiK N (K N) ω|) / N) atTop (𝓝 0)

/-- (iii): for every `ε > 0`, w.h.p. `Φ_K ≥ |F₁| − εN`. -/
def FormIII (ρ : ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ ε > 0, Tendsto (fun N : ℕ => prob ρ (fun ω : Edge N (K N) → Bool =>
    (PhiK N (K N) ω : ℝ) < (smoothFibre N (K N)).card - ε * N)) atTop (𝓝 0)

variable (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hKN : ∀ᶠ N in atTop, K N ≤ N)
  (hK : Tendsto (fun N : ℕ => (K N : ℝ) / N) atTop (𝓝 0))
include hρ0 hρ1 hKN

omit hρ0 hρ1 hKN in
/-- `E[Ψ − Φ_K + K] = gap + K`. -/
theorem expect_psi_sub_add (N k : ℕ) :
    expectP ρ (fun ω : Edge N k → Bool => ((psi N (N / (k + 1)) : ℝ) - PhiK N k ω) + k) =
      gap ρ N k + k := by
  rw [expectP_add, expectP_sub, expectP_const, expectP_const]
  rfl

include hK in
/-- (i) ⇒ (ii). -/
theorem formI_to_formII (h : FormI ρ K) : FormII ρ K := by
  have hsum := h.add hK
  rw [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun N => div_nonneg
    ((expectP_const (ι := Edge N (K N)) ρ (0 : ℝ)).symm.le.trans
      (expectP_mono hρ0 hρ1 fun ω => abs_nonneg _)) (Nat.cast_nonneg N)) ?_ hsum
  filter_upwards [hKN] with N hN
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
  rw [← expect_psi_sub_add (ρ := ρ) N (K N)]
  exact expectP_mono hρ0 hρ1 fun ω => abs_card_sub_PhiK_le hN ω

omit hKN in
/-- (ii) ⇒ (iii), by Markov's inequality. -/
theorem formII_to_formIII (h : FormII ρ K) : FormIII ρ K := by
  intro ε hε
  have hlim : Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N (K N) → Bool =>
      |((smoothFibre N (K N)).card : ℝ) - PhiK N (K N) ω|) / N / ε) atTop (𝓝 0) := by
    simpa using h.div_const ε
  refine squeeze_zero' (Eventually.of_forall fun N => prob_nonneg hρ0 hρ1 _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hεN : 0 < ε * N := mul_pos hε hN0
  have h1 := prob_mono hρ0 hρ1 (A := fun ω : Edge N (K N) → Bool =>
      (PhiK N (K N) ω : ℝ) < (smoothFibre N (K N)).card - ε * N)
    (B := fun ω => ε * N ≤ |((smoothFibre N (K N)).card : ℝ) - PhiK N (K N) ω|)
    fun ω hω => le_trans (by linarith) (le_abs_self _)
  have h2 := prob_ge_le hρ0 hρ1 (f := fun ω : Edge N (K N) → Bool =>
    |((smoothFibre N (K N)).card : ℝ) - PhiK N (K N) ω|) (fun ω => abs_nonneg _) hεN
  refine h1.trans (h2.trans (le_of_eq ?_))
  rw [div_div, mul_comm (N : ℝ) ε]

include hK in
/-- (iii) ⇒ (i). -/
theorem formIII_to_formI (h : FormIII ρ K) : FormI ρ K := by
  classical
  rw [FormI, Metric.tendsto_nhds]
  intro δ hδ
  have hε : 0 < δ / 3 := by positivity
  filter_upwards [hKN, h (δ / 3) hε |>.eventually (gt_mem_nhds hε),
    hK.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with N hN hP hKsmall hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set k := K N with hk
  set Ψ : ℝ := ((psi N (N / (k + 1)) : ℕ) : ℝ) with hΨ
  set F : ℝ := (((smoothFibre N k).card : ℕ) : ℝ) with hF
  set A : (Edge N k → Bool) → Prop := fun ω => (PhiK N k ω : ℝ) < F - δ / 3 * N with hA
  obtain ⟨-, hΨF⟩ := card_smoothFibre_bounds hN
  have hΨN : Ψ ≤ N := by rw [hΨ]; exact_mod_cast psi_le_self N (N / (k + 1))
  -- Pointwise: `Ψ − Φ ≤ K + (δ/3) N + N · 1_A`.
  have hpt : ∀ ω : Edge N k → Bool, Ψ - PhiK N k ω ≤
      ((k : ℝ) + δ / 3 * N) + N * (if A ω then (1 : ℝ) else 0) := by
    intro ω
    have hΦ0 : (0 : ℝ) ≤ PhiK N k ω := Nat.cast_nonneg _
    by_cases hω : A ω
    · simp only [hω, ↓reduceIte, mul_one]
      have : (0 : ℝ) ≤ k + δ / 3 * N := by positivity
      linarith
    · simp only [hω, ↓reduceIte, mul_zero, add_zero]
      simp only [hA, not_lt] at hω
      linarith
  have hE := expectP_mono hρ0 hρ1 hpt
  rw [expectP_sub, expectP_const, expectP_add, expectP_const, expectP_const_mul] at hE
  have hprob : expectP ρ (fun ω : Edge N k → Bool => if A ω then (1 : ℝ) else 0) = prob ρ A := by
    rw [prob_eq]
    rfl
  rw [hprob] at hE
  have hgap : gap ρ N k = Ψ - expectP ρ (fun ω : Edge N k → Bool => (PhiK N k ω : ℝ)) := rfl
  have hg0 := gap_nonneg hρ0 hρ1 N k
  have hPr : prob ρ A < δ / 3 := by
    have := hP
    simpa [hA, hF, hk] using this
  have hKs : (k : ℝ) / N < δ / 3 := by
    have := hKsmall
    simpa [hk] using this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hg0 hN0.le), div_lt_iff₀ hN0]
  rw [div_lt_iff₀ hN0] at hKs
  have : (N : ℝ) * prob ρ A ≤ N * (δ / 3) := mul_le_mul_of_nonneg_left hPr.le hN0.le
  rw [hgap]
  nlinarith

include hK in
/-- **Remark 3.4.** For `K = o(N)`, (i) ⇔ (ii) ⇔ (iii). -/
theorem remark_3_4 : (FormI ρ K ↔ FormII ρ K) ∧ (FormII ρ K ↔ FormIII ρ K) :=
  ⟨⟨formI_to_formII hρ0 hρ1 hKN hK, fun h =>
      formIII_to_formI hρ0 hρ1 hKN hK (formII_to_formIII hρ0 hρ1 h)⟩,
    ⟨formII_to_formIII hρ0 hρ1, fun h =>
      formI_to_formII hρ0 hρ1 hKN hK (formIII_to_formI hρ0 hρ1 hKN hK h)⟩⟩

end Forms

/-- **Remark 3.4, last sentence.** For `ρ ∈ (0, 1)` and `K(N) < N` for large `N`, Theorem 1.2 gives
(i), hence (ii) and (iii) when `K = o(N)`. -/
theorem remark_3_4_holds {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ}
    (hKN : ∀ᶠ N in atTop, K N < N) : FormI ρ K := by
  have hlim : Tendsto (fun N : ℕ => 30 / Real.log (Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_log_nat)
  refine squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (gap_nonneg hρ0.le hρ1.le N (K N)) (Nat.cast_nonneg N)) ?_ hlim
  filter_upwards [hKN, eventually_goodN hρ0 hρ1, eventually_ge_atTop 1] with N hK hG hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [div_le_iff₀ hN0]
  calc gap ρ N (K N) ≤ 30 * N / Real.log (Real.log N) := gap_le_of_good hρ0 hρ1 hK hG
    _ = 30 / Real.log (Real.log N) * N := by ring

end HubRemoval
