import HubRemoval.CoreParams

/-!
# The exceptional set (paper, Lemma 4.5(d))

Under the hypotheses of Lemma 4.5 (`CoreHyp`), with `Y = N^{1−2δ}/(2(K+1))` and `B = ⌊N/(K+1)⌋`:

**Lemma 4.5(d).**
`|F₁ \ 𝒰| ≤ N^{1−δ} + N(4δ/η + 2(1 + C₁)/(η log N)) + #{m ≤ N : ω_z(m) < s₀}`.

The input is the paper's Lemma 2.1(b), Mertens' second theorem, used once, at `y = Y` and
`w = B`: `∑_{Y < p ≤ B} 1/p ≤ log(log B / log Y) + C₁/log Y`. Mertens' theorem is not in Mathlib,
so this instance is an explicit hypothesis `hMb`. It is needed only when `Y < B`; otherwise the
sum is empty.

The proof is the paper's. If `m ∈ F₁ \ 𝒰`, then `m ≤ N^{1−δ}`, or `Y < P⁺(m) ≤ B`, or
`ω_z(m) < s₀`. The middle set has at most `∑_{Y<p≤B} ⌊N/p⌋ ≤ N ∑_{Y<p≤B} 1/p` elements. The
estimates `log B − log Y ≤ 2δ log N + log 2` and `log Y ≥ ½η log N`, together with
`log t ≤ t − 1`, finish the proof.
-/

namespace HubRemoval

open Finset

variable {N K s₀ : ℕ} {η δ : ℝ}

/-- `Y = M/(2(K+1)) = N^{1−2δ}/(2(K+1))`. -/
noncomputable def coreY (N K : ℕ) (δ : ℝ) : ℝ := (N : ℝ) ^ (1 - 2 * δ) / (2 * ((K : ℝ) + 1))

theorem coreY_pos (N K : ℕ) (δ : ℝ) (hN : (0 : ℝ) < N) : 0 < coreY N K δ := by
  unfold coreY
  positivity

/-- `log Y ≥ ½ η log N`, because `Y ≥ N^{η/2}`. -/
theorem CoreHyp.log_Y_ge (h : CoreHyp N K s₀ η δ) :
    η / 2 * Real.log N ≤ Real.log (coreY N K δ) := by
  have hY : (N : ℝ) ^ (η / 2) ≤ coreY N K δ := by
    unfold coreY
    rw [le_div_iff₀ (by positivity)]
    have h1 : 2 * ((K : ℝ) + 1) ≤ 4 * (N : ℝ) ^ (1 - η) := by linarith [h.K1_le]
    have hs : (N : ℝ) ^ (1 - 2 * δ) =
        (N : ℝ) ^ (η / 2) * (N : ℝ) ^ (1 - η) * (N : ℝ) ^ (η / 2 - 2 * δ) := by
      rw [← h.rpow_add, ← h.rpow_add]
      congr 1
      ring
    have h4 : 4 ≤ (N : ℝ) ^ (η / 2 - 2 * δ) := h.H2.trans (h.rpow_le (by linarith [h.δ_le]))
    have h3 : 0 ≤ (N : ℝ) ^ (η / 2) := by positivity
    have h5 : 0 ≤ (N : ℝ) ^ (η / 2) * (N : ℝ) ^ (1 - η) := by positivity
    calc (N : ℝ) ^ (η / 2) * (2 * ((K : ℝ) + 1))
        ≤ (N : ℝ) ^ (η / 2) * (4 * (N : ℝ) ^ (1 - η)) := mul_le_mul_of_nonneg_left h1 h3
      _ ≤ (N : ℝ) ^ (1 - 2 * δ) := by rw [hs]; nlinarith
  calc η / 2 * Real.log N = Real.log ((N : ℝ) ^ (η / 2)) := by rw [Real.log_rpow h.N_pos]
    _ ≤ Real.log (coreY N K δ) := Real.log_le_log (Real.rpow_pos_of_pos h.N_pos _) hY

/-- `log B − log Y ≤ 2δ log N + log 2`, because `B/Y ≤ 2N^{2δ}`. -/
theorem CoreHyp.log_B_sub_log_Y (h : CoreHyp N K s₀ η δ) (hB : 0 < N / (K + 1)) :
    Real.log ((N / (K + 1) : ℕ) : ℝ) - Real.log (coreY N K δ) ≤
      2 * δ * Real.log N + Real.log 2 := by
  have hYpos := coreY_pos N K δ h.N_pos
  have hBR : (0 : ℝ) < ((N / (K + 1) : ℕ) : ℝ) := by exact_mod_cast hB
  rw [← Real.log_div hBR.ne' hYpos.ne']
  have hBle : ((N / (K + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((K : ℝ) + 1) := by
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := K + 1)
    push_cast at this
    exact this
  have h2 : (N : ℝ) ^ (2 * δ) * (N : ℝ) ^ (1 - 2 * δ) = N := by
    rw [← h.rpow_add, show 2 * δ + (1 - 2 * δ) = (1 : ℝ) by ring, Real.rpow_one]
  have hratio : ((N / (K + 1) : ℕ) : ℝ) / coreY N K δ ≤ 2 * (N : ℝ) ^ (2 * δ) := by
    rw [div_le_iff₀ hYpos]
    have e : 2 * (N : ℝ) ^ (2 * δ) * coreY N K δ =
        ((N : ℝ) ^ (2 * δ) * (N : ℝ) ^ (1 - 2 * δ)) / ((K : ℝ) + 1) := by
      unfold coreY
      field_simp
    rw [e, h2]
    exact hBle
  calc Real.log (((N / (K + 1) : ℕ) : ℝ) / coreY N K δ)
      ≤ Real.log (2 * (N : ℝ) ^ (2 * δ)) := Real.log_le_log (div_pos hBR hYpos) hratio
    _ = 2 * δ * Real.log N + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos h.N_pos _).ne', Real.log_rpow h.N_pos]
        ring

open Classical in
/-- **Lemma 4.5(d).** Assuming the instance `hMb` of Mertens' second theorem at `y = Y`,
`w = B`, `|F₁ \ 𝒰| ≤ N^{1−δ} + N(4δ/η + 2(1+C₁)/(η log N)) + #{m ≤ N : ω_z(m) < s₀}`. -/
theorem core_d (h : CoreHyp N K s₀ η δ) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hMb : coreY N K δ < ((N / (K + 1) : ℕ) : ℝ) →
      ∑ p ∈ (primesUpTo (N / (K + 1))).filter (fun p : ℕ => coreY N K δ < p), (1 : ℝ) / p ≤
        Real.log (Real.log ((N / (K + 1) : ℕ) : ℝ) / Real.log (coreY N K δ)) +
          C₁ / Real.log (coreY N K δ)) :
    (((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card : ℝ) ≤
      (N : ℝ) ^ (1 - δ) + N * (4 * δ / η + 2 * (1 + C₁) / (η * Real.log N)) +
        ((Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀)).card := by
  set B := N / (K + 1) with hBdef
  set Y := coreY N K δ with hYdef
  set P := (primesUpTo B).filter (fun p : ℕ => Y < p) with hPdef
  set A1 := (Ioc 0 N).filter (fun m : ℕ => (m : ℝ) ≤ (N : ℝ) ^ (1 - δ)) with hA1def
  set A2 := P.biUnion (fun p : ℕ => (Ioc 0 N).filter (p ∣ ·)) with hA2def
  set A3 := (Ioc 0 N).filter (fun m => omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m < s₀) with hA3def
  -- Every `m ∈ F₁ \ 𝒰` lies in `A1 ∪ A2 ∪ A3`.
  have hsub : (smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m) ⊆ A1 ∪ A2 ∪ A3 := by
    intro m hm
    obtain ⟨hmF, hmU⟩ := mem_filter.mp hm
    simp only [smoothFibre, vertices, mem_filter, mem_Ioc] at hmF
    obtain ⟨⟨hKm, hmN⟩, hsm⟩ := hmF
    have hm0 : 0 < m := by omega
    unfold InU at hmU
    by_cases h1 : (N : ℝ) ^ (1 - δ) < m
    · by_cases h3 : s₀ ≤ omegaZ ⌊(N : ℝ) ^ (δ / s₀)⌋₊ m
      · have h2 : ¬ ∀ p, p.Prime → p ∣ m → 2 * ((K : ℝ) + 1) * p ≤ (N : ℝ) ^ (1 - 2 * δ) :=
          fun h2 => hmU ⟨h1, hmN, h2, h3⟩
        push Not at h2
        obtain ⟨p, hp, hpm, hpY⟩ := h2
        refine mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨p, ?_,
          mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm0, hmN⟩, hpm⟩⟩))
        refine mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨hp, ?_⟩, ?_⟩
        · have := (Nat.mem_smoothNumbers'.mp hsm) p hp hpm
          omega
        · show coreY N K δ < p
          unfold coreY
          rw [div_lt_iff₀ (by positivity)]
          linarith
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm0, hmN⟩, by omega⟩)
    · exact mem_union_left _ (mem_union_left _
        (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm0, hmN⟩, not_lt.mp h1⟩))
  -- `|A1| ≤ N^{1−δ}`.
  have hA1 : (A1.card : ℝ) ≤ (N : ℝ) ^ (1 - δ) := by
    have hs : A1 ⊆ Icc 1 ⌊(N : ℝ) ^ (1 - δ)⌋₊ := fun m hm => by
      obtain ⟨hmI, hle⟩ := mem_filter.mp hm
      exact mem_Icc.mpr ⟨(mem_Ioc.mp hmI).1, Nat.le_floor hle⟩
    have h1 := card_le_card hs
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
  -- `|A2| ≤ N ∑_{Y<p≤B} 1/p`.
  have hA2 : (A2.card : ℝ) ≤ N * ∑ p ∈ P, (1 : ℝ) / p := by
    have h1 : (A2.card : ℝ) ≤ ∑ p ∈ P, (((Ioc 0 N).filter (p ∣ ·)).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    rw [mul_sum]
    refine h1.trans (sum_le_sum fun p _ => ?_)
    rw [Nat.Ioc_filter_dvd_card_eq_div, mul_one_div]
    exact Nat.cast_div_le
  -- `∑_{Y<p≤B} 1/p ≤ 4δ/η + 2(1+C₁)/(η log N)`.
  have hlogN : 0 < Real.log N := Real.log_pos h.one_lt_N
  have hη := h.η_pos
  have hδ := h.δ_pos
  have hsumP : ∑ p ∈ P, (1 : ℝ) / p ≤ 4 * δ / η + 2 * (1 + C₁) / (η * Real.log N) := by
    by_cases hYB : Y < B
    · have hM := hMb hYB
      have hYlog := h.log_Y_ge
      have hlogY : 0 < Real.log Y := lt_of_lt_of_le (by positivity) hYlog
      have hYpos : 0 < Y := coreY_pos N K δ h.N_pos
      have hBpos : 0 < B := by
        have : (0 : ℝ) < B := lt_trans hYpos hYB
        exact_mod_cast this
      have hBlog := h.log_B_sub_log_Y hBpos
      have hlogB : 0 < Real.log B := lt_trans hlogY (Real.log_lt_log hYpos hYB)
      have ht : Real.log (Real.log B / Real.log Y) ≤ Real.log B / Real.log Y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hlogB hlogY)
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      have hnum : 0 ≤ 2 * δ * Real.log N + 1 + C₁ := by positivity
      have e : Real.log B / Real.log Y - 1 + C₁ / Real.log Y =
          (Real.log B - Real.log Y + C₁) / Real.log Y := by
        field_simp
      calc ∑ p ∈ P, (1 : ℝ) / p
          ≤ Real.log (Real.log B / Real.log Y) + C₁ / Real.log Y := hM
        _ ≤ Real.log B / Real.log Y - 1 + C₁ / Real.log Y := by linarith
        _ = (Real.log B - Real.log Y + C₁) / Real.log Y := e
        _ ≤ (2 * δ * Real.log N + 1 + C₁) / Real.log Y :=
            div_le_div_of_nonneg_right (by linarith) hlogY.le
        _ ≤ (2 * δ * Real.log N + 1 + C₁) / (η / 2 * Real.log N) :=
            div_le_div_of_nonneg_left hnum (by positivity) hYlog
        _ = 4 * δ / η + 2 * (1 + C₁) / (η * Real.log N) := by
            field_simp
            ring
    · have hP : P = ∅ := by
        refine filter_eq_empty_iff.mpr fun p hp hYp => ?_
        have hpB : (p : ℝ) ≤ B := by exact_mod_cast (mem_primesUpTo.mp hp).2
        push Not at hYB
        linarith
      rw [hP, sum_empty]
      positivity
  have hunion : ((A1 ∪ A2 ∪ A3).card : ℝ) ≤ A1.card + A2.card + A3.card := by
    have h1 := card_union_le (A1 ∪ A2) A3
    have h2 := card_union_le A1 A2
    exact_mod_cast (show (A1 ∪ A2 ∪ A3).card ≤ A1.card + A2.card + A3.card by omega)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsumP hN0
  calc (((smoothFibre N K).filter (fun m => ¬ InU N K s₀ δ m)).card : ℝ)
      ≤ ((A1 ∪ A2 ∪ A3).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ A1.card + A2.card + A3.card := hunion
    _ ≤ _ := by linarith

end HubRemoval
