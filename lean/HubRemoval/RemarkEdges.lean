import HubRemoval.Profile
import HubRemoval.Sandwich

/-!
# Remarks 7.1 and 7.3

**Remark 7.1 (Edge share of the hubs).** An edge of `G_N` meets `{1, …, K}` exactly when its
smaller end `d` is at most `K`. So `{1, …, K}` meets exactly `∑_{d ≤ K} (⌊N/d⌋ − 1)` edges
(`card_hubEdges`), which is `N log K + O(N)` (`abs_card_hubEdges_sub_le`, with `|O(N)| ≤ 2N`),
out of `|E(G_N)| = ∑_{d ≤ N} (⌊N/d⌋ − 1) = N log N + O(N)` edges (`card_edges_zero`,
`abs_card_edges_sub_le`). Hence, if `log(K + 1)/log N → θ`, the hubs carry a `θ`-fraction of
the edges (`hub_edge_share`).

**Remark 7.3 (Relation to Kim–Phillips).** The case `K = 0` of Corollary 1.4 is
`E[#Φ(𝒟_ρ(N))]/N → 1`, Kim and Phillips' Corollary 2 (`kp_corollary_2`).
-/

namespace HubRemoval

open Finset Filter Topology

/-- The edges of `G_N` meeting `{1, …, K}`: those whose smaller end is at most `K`. -/
def hubEdges (N K : ℕ) : Finset (ℕ × ℕ) := (edges N 0).filter (fun e => e.1 ≤ K)

/-- An edge meets `{1, …, K}` if and only if its smaller end is `≤ K` (the ends are `a < b`). -/
theorem mem_hubEdges_iff {N K a b : ℕ} :
    (a, b) ∈ hubEdges N K ↔ (a, b) ∈ edges N 0 ∧ (a ≤ K ∨ b ≤ K) := by
  unfold hubEdges
  rw [mem_filter]
  constructor
  · rintro ⟨h, hK⟩
    exact ⟨h, Or.inl hK⟩
  · rintro ⟨h, hK | hK⟩
    · exact ⟨h, hK⟩
    · exact ⟨h, (le_of_lt (mem_edges.mp h).2.1).trans hK⟩

/-- **Remark 7.1, the count.** For `K ≤ N`, `{1, …, K}` meets `∑_{d ≤ K} (⌊N/d⌋ − 1)` edges. -/
theorem card_hubEdges {N K : ℕ} (hKN : K ≤ N) :
    (hubEdges N K).card = ∑ d ∈ Icc 1 K, (N / d - 1) := by
  have hmaps : Set.MapsTo Prod.fst (hubEdges N K : Set (ℕ × ℕ)) (Icc 1 K : Set ℕ) := by
    rintro ⟨a, b⟩ he
    obtain ⟨hmem, hK⟩ := mem_filter.mp (mem_coe.mp he)
    obtain ⟨h1, -, -, -⟩ := mem_edges.mp hmem
    exact mem_coe.mpr (mem_Icc.mpr ⟨h1, hK⟩)
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun d hd => ?_
  obtain ⟨hd1, hdK⟩ := mem_Icc.mp hd
  have hfib : (hubEdges N K).filter (fun e => e.1 = d) =
      ((Ioc d N).filter (d ∣ ·)).image (fun b => (d, b)) := by
    ext ⟨a, b⟩
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨he, hed⟩
      simp only at hed
      subst hed
      obtain ⟨hmem, -⟩ := mem_filter.mp he
      obtain ⟨-, h2, h3, h4⟩ := mem_edges.mp hmem
      exact ⟨b, mem_filter.mpr ⟨mem_Ioc.mpr ⟨h2, h3⟩, h4⟩, rfl⟩
    · rintro ⟨b', hb', hbb⟩
      obtain ⟨hIoc, h4⟩ := mem_filter.mp hb'
      obtain ⟨h2, h3⟩ := mem_Ioc.mp hIoc
      simp only [Prod.mk.injEq] at hbb
      obtain ⟨rfl, rfl⟩ := hbb
      exact ⟨mem_filter.mpr ⟨mem_edges.mpr ⟨by omega, h2, h3, h4⟩, hdK⟩, rfl⟩
  rw [hfib, card_image_of_injective _ fun b b' h => (Prod.mk.inj h).2,
    card_Ioc_filter_dvd (by omega) d, Nat.div_self (by omega)]

/-- Every edge meets `{1, …, N}`, so `|E(G_N)| = ∑_{d ≤ N} (⌊N/d⌋ − 1)`. -/
theorem card_edges_zero (N : ℕ) : (edges N 0).card = ∑ d ∈ Icc 1 N, (N / d - 1) := by
  rw [← card_hubEdges le_rfl]
  congr 1
  refine (filter_true_of_mem fun e he => ?_).symm
  obtain ⟨a, b⟩ := e
  obtain ⟨-, h2, h3, -⟩ := mem_edges.mp he
  exact (le_of_lt h2).trans h3

/-- `N H_K − 2K ≤ ∑_{d ≤ K} (⌊N/d⌋ − 1) ≤ N H_K` for `K ≤ N`, with `H_K = ∑_{d ≤ K} 1/d`. -/
theorem sum_div_sub_one_bounds {N K : ℕ} (hKN : K ≤ N) :
    (N : ℝ) * (harmonic K : ℝ) - 2 * K ≤ ((∑ d ∈ Icc 1 K, (N / d - 1) : ℕ) : ℝ) ∧
      ((∑ d ∈ Icc 1 K, (N / d - 1) : ℕ) : ℝ) ≤ (N : ℝ) * (harmonic K : ℝ) := by
  have hH : (N : ℝ) * (harmonic K : ℝ) = ∑ d ∈ Icc 1 K, (N : ℝ) / d := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [mul_sum]
    exact sum_congr rfl fun d _ => by rw [div_eq_mul_inv]
  have hterm : ∀ d ∈ Icc 1 K, (N : ℝ) / d - 2 ≤ ((N / d - 1 : ℕ) : ℝ) ∧
      ((N / d - 1 : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    intro d hd
    obtain ⟨hd1, hdK⟩ := mem_Icc.mp hd
    have h1 : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr (by omega)
    rw [Nat.cast_sub h1, Nat.cast_one]
    have h2 := Nat.cast_div_le (α := ℝ) (m := N) (n := d)
    have h3 : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor ((N : ℝ) / d)
      rwa [Nat.floor_div_eq_div] at this
    constructor <;> linarith
  push_cast
  rw [hH]
  constructor
  · have := sum_le_sum fun d hd => (hterm d hd).1
    rw [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
    linarith
  · have := sum_le_sum fun d hd => (hterm d hd).2
    linarith

/-- **Remark 7.1, the size.** For `1 ≤ K ≤ N`,
`|#{edges meeting {1, …, K}} − N log K| ≤ 2N`. -/
theorem abs_card_hubEdges_sub_le {N K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) :
    |((hubEdges N K).card : ℝ) - N * Real.log K| ≤ 2 * N := by
  rw [card_hubEdges hKN]
  obtain ⟨h1, h2⟩ := sum_div_sub_one_bounds (N := N) (K := K) hKN
  have hlow : Real.log K ≤ (harmonic K : ℝ) := by
    have := log_add_one_le_harmonic K
    have h : Real.log K ≤ Real.log ((K + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hK) (by push_cast; linarith)
    linarith
  have hup := harmonic_le_one_add_log K
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have p1 : (N : ℝ) * Real.log K ≤ N * (harmonic K : ℝ) := mul_le_mul_of_nonneg_left hlow hN0
  have p2 : (N : ℝ) * (harmonic K : ℝ) ≤ N * (1 + Real.log K) := mul_le_mul_of_nonneg_left hup hN0
  rw [abs_le]
  constructor <;> nlinarith

/-- **Remark 7.1, all edges.** `||E(G_N)| − N log N| ≤ 2N` for `N ≥ 1`. -/
theorem abs_card_edges_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |((edges N 0).card : ℝ) - N * Real.log N| ≤ 2 * N := by
  have h := abs_card_hubEdges_sub_le hN le_rfl
  rwa [card_hubEdges le_rfl, ← card_edges_zero] at h

/-- `|#{edges meeting {1, …, K}}/N − log(K + 1)| ≤ 2 + log 2`, for every `K ≤ N`. -/
theorem abs_card_hubEdges_div_sub_le {N K : ℕ} (hN : 1 ≤ N) (hKN : K ≤ N) :
    |((hubEdges N K).card : ℝ) / N - Real.log ((K : ℝ) + 1)| ≤ 2 + Real.log 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    have : hubEdges N 0 = ∅ := filter_false_of_mem fun e he => by
      obtain ⟨a, b⟩ := e
      have := (mem_edges.mp he).1
      simp only
      omega
    rw [this]
    simp only [card_empty, Nat.cast_zero, zero_div, zero_add, Real.log_one, sub_zero, abs_zero]
    linarith
  · have h := abs_card_hubEdges_sub_le hK1 hKN
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have e : ((hubEdges N K).card : ℝ) / N - Real.log K =
        (((hubEdges N K).card : ℝ) - N * Real.log K) / N := by field_simp
    have h' : |((hubEdges N K).card : ℝ) / N - Real.log K| ≤ 2 := by
      rw [e, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
      linarith
    have hlog : |Real.log K - Real.log ((K : ℝ) + 1)| ≤ Real.log 2 := by
      have l1 : Real.log K ≤ Real.log ((K : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
      have l2 : Real.log ((K : ℝ) + 1) ≤ Real.log (2 * K) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at l2
      rw [abs_le]
      constructor <;> linarith
    calc |((hubEdges N K).card : ℝ) / N - Real.log ((K : ℝ) + 1)|
        ≤ |((hubEdges N K).card : ℝ) / N - Real.log K| + |Real.log K - Real.log ((K : ℝ) + 1)| :=
          abs_sub_le _ _ _
      _ ≤ 2 + Real.log 2 := add_le_add h' hlog

/-- **Remark 7.1, the share.** If `K(N) ≤ N` for large `N` and `log(K + 1)/log N → θ`, the hubs
`{1, …, K}` meet a fraction `→ θ` of the edges of `G_N`. -/
theorem hub_edge_share {K : ℕ → ℕ} (hK : ∀ᶠ N in atTop, K N ≤ N) {θ : ℝ}
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => ((hubEdges N (K N)).card : ℝ) / (edges N 0).card) atTop (𝓝 θ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop := tendsto_log_nat
  set c := 2 + Real.log 2 with hc
  -- `a_N = #hub/(N log N) → θ` and `b_N = #edges/(N log N) → 1`.
  have hsq : ∀ (x y : ℕ → ℝ) (L : ℝ), Tendsto y atTop (𝓝 L) →
      (∀ᶠ N : ℕ in atTop, |x N - y N| ≤ c / Real.log N) → Tendsto x atTop (𝓝 L) := by
    intro x y L hy hxy
    have h0 : Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have hd : Tendsto (fun N => x N - y N) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [hxy] with N hN
      rw [Real.norm_eq_abs]
      exact hN
    have := hd.add hy
    rw [zero_add] at this
    exact this.congr fun N => by ring
  have ha : Tendsto (fun N : ℕ => ((hubEdges N (K N)).card : ℝ) / N / Real.log N) atTop (𝓝 θ) := by
    refine hsq _ _ θ hθ ?_
    filter_upwards [hK, eventually_ge_atTop 2] with N hKN hN2
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [← sub_div, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (abs_card_hubEdges_div_sub_le (by omega) hKN) hL.le
  have hb : Tendsto (fun N : ℕ => ((edges N 0).card : ℝ) / N / Real.log N) atTop (𝓝 1) := by
    refine hsq _ (fun _ => 1) 1 tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hN0 : (0 : ℝ) < N := by positivity
    have h := abs_card_edges_sub_le (N := N) (by omega)
    have e : ((edges N 0).card : ℝ) / N / Real.log N - 1 =
        (((edges N 0).card : ℝ) - N * Real.log N) / N / Real.log N := by field_simp
    rw [e, abs_div, abs_div, abs_of_pos hN0, abs_of_pos hL]
    refine div_le_div_of_nonneg_right ?_ hL.le
    rw [div_le_iff₀ hN0]
    have : c * N ≥ 2 * N := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      nlinarith
    linarith
  have := ha.div hb one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp

/-- **Remark 7.3.** Kim and Phillips' Corollary 2: `E[#Φ(𝒟_ρ(N))]/N → 1` for `ρ ∈ (0, 1)`. This is
the case `K = 0` of Corollary 1.4. -/
theorem kp_corollary_2 {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N 0 → Bool => (PhiK N 0 ω : ℝ)) / N) atTop
      (𝓝 1) := by
  have h := cor_profile (ρ := ρ) (K := fun _ => 0) (θ := 0) hρ0 hρ1 (eventually_gt_atTop 0)
    (by simp)
  rwa [dickLim_zero] at h

end HubRemoval
