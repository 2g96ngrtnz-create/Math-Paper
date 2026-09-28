import HubRemoval.Rate
import HubRemoval.PsiLimit

/-!
# The limit profile (paper, Corollary 1.3; also Corollary 3.3)

**Corollary 1.3.** Fix `ρ ∈ (0, 1)`, and let `K = K(N) ∈ [0, N)` satisfy
`log(K + 1)/log N → θ`. Then `E[Φ_K]/N → ρ(1/(1 − θ))`, with `ρ(∞) = 0` (`cor_profile`).
The profile `θ ↦ ρ(1/(1 − θ))` (`dickLim`) is continuous and strictly decreasing on `[0, 1]`
(`dickLim_continuous`, `dickLim_strictAntiOn`). It equals `1 − log(1/(1 − θ))` for
`0 ≤ θ ≤ 1/2` (`dickLim_of_le_half`).

*Proof.* `E[Φ_K]/N = Ψ(N, N/(K + 1))/N − gap/N`. The first term tends to `ρ(1/(1 − θ))` by
Lemma 2.7. By Theorem 1.2, `0 ≤ gap/N ≤ 30/log log N` for large `N`. Continuity at `θ = 1`
comes from `0 ≤ ρ(1/(1 − θ)) ≤ 2(1 − θ)` (Lemma 2.3, `dickman_le_two_div`).

**Corollary 3.3.** For any `ρ ∈ [0, 1]`, `limsup E[Φ_K]/N ≤ ρ(1/(1 − θ))`
(`cor_upper_profile`). It needs only Proposition 3.2 and Lemma 2.7.

As in Lemma 2.7, `θ ∈ [0, 1]` is not assumed, since it follows from `K < N`.
-/

namespace HubRemoval

open Filter Topology

/-! ### The profile `θ ↦ ρ(1/(1 − θ))` -/

theorem dickLim_of_lt {θ : ℝ} (h : θ < 1) : dickLim θ = dickman (1 / (1 - θ)) := by
  rw [dickLim, ite_eq_left h]

theorem dickLim_of_ge {θ : ℝ} (h : 1 ≤ θ) : dickLim θ = 0 := by
  rw [dickLim, ite_eq_right (not_lt.mpr h)]

theorem dickLim_zero : dickLim 0 = 1 := by
  rw [dickLim_of_lt one_pos, sub_zero, div_one, dickman_eq_one le_rfl]

theorem dickLim_one : dickLim 1 = 0 := dickLim_of_ge le_rfl

theorem dickLim_nonneg (θ : ℝ) : 0 ≤ dickLim θ := by
  unfold dickLim
  split_ifs
  · exact (dickman_pos _).le
  · exact le_rfl

/-- For `θ ∈ [0, 1)`, `u = 1/(1 − θ) ≥ 1`. -/
theorem one_le_one_div_one_sub {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : 1 ≤ 1 / (1 - θ) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `ρ(1/(1 − θ)) ≤ 2(1 − θ)` for `θ ≥ 0`, from `ρ(u) ≤ 2/u`. -/
theorem dickLim_le {θ : ℝ} (h0 : 0 ≤ θ) : dickLim θ ≤ 2 * |1 - θ| := by
  rcases lt_or_ge θ 1 with h | h
  · rw [dickLim_of_lt h, abs_of_pos (by linarith)]
    calc dickman (1 / (1 - θ)) ≤ 2 / (1 / (1 - θ)) :=
          dickman_le_two_div (one_le_one_div_one_sub h0 h)
      _ = 2 * (1 - θ) := by rw [div_div_eq_mul_div, div_one]
  · rw [dickLim_of_ge h]
    positivity

/-- **The profile is continuous** (on all of `ℝ`, so in particular on `[0, 1]`). -/
theorem dickLim_continuous : Continuous dickLim := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  rcases lt_trichotomy θ₀ 1 with h | h | h
  · have hc : ContinuousAt (fun θ : ℝ => dickman (1 / (1 - θ))) θ₀ :=
      dickman_continuous.continuousAt.comp (f := fun θ : ℝ => 1 / (1 - θ))
        (continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by linarith))
    refine hc.congr ?_
    filter_upwards [Iio_mem_nhds h] with θ hθ
    exact (dickLim_of_lt hθ).symm
  · subst h
    rw [ContinuousAt, dickLim_one]
    have h2 : Tendsto (fun θ : ℝ => 2 * |1 - θ|) (𝓝 1) (𝓝 0) := by
      have : Tendsto (fun θ : ℝ => 2 * |1 - θ|) (𝓝 1) (𝓝 (2 * |1 - 1|)) :=
        (continuous_const.mul (continuous_const.sub continuous_id).abs).tendsto 1
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall dickLim_nonneg) ?_
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with θ hθ
    exact dickLim_le (le_of_lt hθ)
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with θ hθ
    exact (dickLim_of_ge (le_of_lt hθ)).symm

/-- **The profile is strictly decreasing on `[0, 1]`.** -/
theorem dickLim_strictAntiOn : StrictAntiOn dickLim (Set.Icc 0 1) := by
  intro a ha b hb hab
  have ha1 : a < 1 := hab.trans_le hb.2
  have hua := one_le_one_div_one_sub ha.1 ha1
  rw [dickLim_of_lt ha1]
  rcases lt_or_eq_of_le hb.2 with hb1 | hb1
  · rw [dickLim_of_lt hb1]
    have hub : 1 / (1 - a) < 1 / (1 - b) :=
      one_div_lt_one_div_of_lt (by linarith) (by linarith)
    exact dickman_strictAntiOn (Set.mem_Ici.mpr hua) (Set.mem_Ici.mpr (hua.trans hub.le)) hub
  · rw [hb1, dickLim_one]
    exact dickman_pos _

/-- **For `0 ≤ θ ≤ 1/2`, the profile is `1 − log(1/(1 − θ))`.** -/
theorem dickLim_of_le_half {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    dickLim θ = 1 - Real.log (1 / (1 - θ)) := by
  have hθ1 : θ < 1 := by linarith
  rw [dickLim_of_lt hθ1]
  refine dickman_eq_one_sub_log (one_le_one_div_one_sub h0 hθ1) ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

/-! ### Corollaries 1.3 and 3.3 -/

/-- **Corollary 1.3 (Limit profile).** For `ρ ∈ (0, 1)`, if `K(N) < N` eventually and
`log(K + 1)/log N → θ`, then `E[Φ_K]/N → ρ(1/(1 − θ))`, with `ρ(∞) = 0`. -/
theorem cor_profile {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {K : ℕ → ℕ}
    (hK : ∀ᶠ N in atTop, K N < N) {θ : ℝ}
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    Tendsto (fun N : ℕ => expectP ρ (fun ω : Edge N (K N) → Bool => (PhiK N (K N) ω : ℝ)) / N)
      atTop (𝓝 (dickLim θ)) := by
  have hgap : Tendsto (fun N : ℕ => gap ρ N (K N) / N) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => 30 / Real.log (Real.log N)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_log_nat)
    obtain ⟨N₀, hN₀⟩ := thm_rate hρ0 hρ1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N =>
        div_nonneg (gap_nonneg hρ0.le hρ1.le N (K N)) (Nat.cast_nonneg N)) ?_
    filter_upwards [hK, eventually_ge_atTop N₀, eventually_gt_atTop 0] with N hKN hN hN0
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [div_le_iff₀ hNpos]
    calc gap ρ N (K N) ≤ 30 * N / Real.log (Real.log N) := (hN₀ N hN (K N) hKN).2
      _ = 30 / Real.log (Real.log N) * N := by ring
  have h := (psi_limit hK hθ).sub hgap
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  simp only [gap]
  ring

/-- **Corollary 3.3, ε-form.** For any `ρ ∈ [0, 1]` and `ε > 0`, eventually
`E[Φ_K]/N ≤ ρ(1/(1 − θ)) + ε`. -/
theorem cor_upper_profile_eventually {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {K : ℕ → ℕ}
    (hK : ∀ᶠ N in atTop, K N < N) {θ : ℝ}
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      expectP ρ (fun ω : Edge N (K N) → Bool => (PhiK N (K N) ω : ℝ)) / N ≤ dickLim θ + ε := by
  filter_upwards [(psi_limit hK hθ).eventually_lt_const (lt_add_of_pos_right _ hε)] with N hN
  exact (div_le_div_of_nonneg_right (expect_PhiK_le_psi hρ0 hρ1) (Nat.cast_nonneg N)).trans hN.le

/-- **Corollary 3.3.** For any `ρ ∈ [0, 1]`, `limsup E[Φ_K]/N ≤ ρ(1/(1 − θ))`. -/
theorem cor_upper_profile {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {K : ℕ → ℕ}
    (hK : ∀ᶠ N in atTop, K N < N) {θ : ℝ}
    (hθ : Tendsto (fun N : ℕ => Real.log ((K N : ℝ) + 1) / Real.log N) atTop (𝓝 θ)) :
    limsup (fun N : ℕ => expectP ρ (fun ω : Edge N (K N) → Bool => (PhiK N (K N) ω : ℝ)) / N)
      atTop ≤ dickLim θ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine limsup_le_of_le ?_ (cor_upper_profile_eventually hρ0 hρ1 hK hθ hε)
  exact isCoboundedUnder_le_of_le atTop fun N =>
    div_nonneg (expect_PhiK_nonneg hρ0 hρ1 N (K N)) (Nat.cast_nonneg N)

/-! ### An instance with `θ = 1/2` -/

/-- For `K = ⌊√N⌋`, `log(K + 1)/log N → 1/2`. -/
theorem tendsto_log_sqrt_succ :
    Tendsto (fun N : ℕ => Real.log ((Nat.sqrt N : ℝ) + 1) / Real.log N) atTop (𝓝 (1 / 2)) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => 1 / 2 + Real.log 2 / Real.log N) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hN))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [le_div_iff₀ hL]
    have h1 : Real.log (Real.sqrt N) ≤ Real.log ((Nat.sqrt N : ℝ) + 1) :=
      Real.log_le_log (Real.sqrt_pos.mpr hN0) Real.real_sqrt_lt_nat_sqrt_succ.le
    rw [Real.log_sqrt hN0.le] at h1
    linarith
  · filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N by omega))
    have h1 : Real.log ((Nat.sqrt N : ℝ) + 1) ≤ Real.log (2 * Real.sqrt N) :=
      Real.log_le_log (by positivity) (by linarith [Real.nat_sqrt_le_real_sqrt (a := N)])
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hN0.le] at h1
    rw [div_le_iff₀ hL, add_mul, div_mul_cancel₀ _ hL.ne']
    linarith

end HubRemoval
